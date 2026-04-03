use std::collections::HashMap;
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use krypton_diagnostics::{AriadneRenderer, DiagnosticRenderer};
use krypton_ir::Type;
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::ast::CompileTarget;
pub use krypton_parser::repl::{classify_input, build_synthetic_source, ReplInputKind};
use krypton_typechecker::types::{format_type_with_var_names, TypeScheme, TypeVarId};

/// Information about a prior REPL binding (session-level, holds IR type for codegen).
#[derive(Clone, Debug)]
pub struct BindingInfo {
    pub type_str: String,
    pub ir_type: Type,
}

/// Persistent state across REPL inputs.
pub struct ReplSession {
    pub bindings: Vec<(String, BindingInfo)>,
    /// Function definitions stored as (name, source, type_display_str).
    /// Re-emitted in each synthetic module so they're available as top-level functions.
    pub fun_defs: Vec<(String, String, String)>,
    input_counter: u32,
    jvm: Option<JvmProcess>,
}

impl ReplSession {
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
            fun_defs: Vec::new(),
            input_counter: 0,
            jvm: None,
        }
    }

    fn next_class_name(&mut self) -> String {
        self.input_counter += 1;
        format!("Repl${}", self.input_counter)
    }

    fn ensure_jvm(&mut self) -> Result<&mut JvmProcess, String> {
        if self.jvm.is_none() {
            self.jvm = Some(JvmProcess::spawn()?);
        }
        Ok(self.jvm.as_mut().unwrap())
    }

    pub fn eval_input(&mut self, input: &str) -> Result<String, String> {
        let kind = classify_input(input);
        let class_name = self.next_class_name();
        let binding_strs: Vec<(String, String)> = self
            .bindings
            .iter()
            .map(|(n, info)| (n.clone(), info.type_str.clone()))
            .collect();
        let synthetic = build_synthetic_source(&kind, &binding_strs, &self.fun_defs);

        // Parse
        let (module, parse_errors) = krypton_parser::parser::parse(&synthetic);
        if !parse_errors.is_empty() {
            let (diags, srcs) = krypton_parser::diagnostics::lower_parse_errors(
                "<repl>", &synthetic, &parse_errors,
            );
            let mut msg = String::new();
            for d in &diags {
                msg.push_str(&AriadneRenderer.render(d, &srcs));
            }
            return Err(msg);
        }

        // Typecheck
        let resolver = CompositeResolver::stdlib_only();
        let (typed_modules, interfaces) = krypton_typechecker::infer::infer_module(
            &module,
            &resolver,
            "repl".to_string(),
            CompileTarget::Jvm,
        )
        .map_err(|errors| {
            let (diags, srcs) = krypton_typechecker::diagnostics::lower_infer_errors(
                "<repl>", &synthetic, &errors,
            );
            let mut msg = String::new();
            for d in &diags {
                msg.push_str(&AriadneRenderer.render(d, &srcs));
            }
            msg
        })?;

        // Infer the return type of __eval for binding tracking
        let root_typed = &typed_modules[0];
        let _eval_type_entry = root_typed
            .fn_types
            .iter()
            .find(|e| e.name == "__eval")
            .ok_or_else(|| "ICE: __eval not found in typed module".to_string())?;

        // Build LinkContext
        let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);

        // Lower to IR
        let (ir_modules, module_sources) =
            krypton_ir::lower::lower_all(&typed_modules, &class_name, &link_ctx).map_err(|e| {
                format!("IR lowering error: {}", e)
            })?;

        // Find __eval's return type from IR
        let root_ir = &ir_modules[0];
        let eval_fn = root_ir
            .functions
            .iter()
            .find(|f| f.name == "__eval")
            .ok_or_else(|| "ICE: __eval not found in IR module".to_string())?;
        let eval_return_type = eval_fn.return_type.clone();

        // For FunDef, extract the function's type scheme for display
        let fun_def_type_display = if let ReplInputKind::FunDef { ref name, .. } = kind {
            root_typed
                .fn_types_by_name
                .get(name.as_str())
                .and_then(|&idx| root_typed.fn_types.get(idx))
                .map(|entry| format_scheme_for_repl(&entry.scheme))
        } else {
            None
        };

        // Determine store_var and the type string for the binding
        let (store_var, binding_name, binding_type_str) = match &kind {
            ReplInputKind::LetBinding { name, .. } => {
                let type_str = eval_return_type.to_string();
                (Some(name.clone()), Some(name.clone()), Some(type_str))
            }
            ReplInputKind::FunDef { .. } => {
                // Function defs are re-emitted as source; don't store in JVM Registry
                (None, None, None)
            }
            ReplInputKind::BareExpr { .. } => (None, None, None),
        };

        // Gather repl_vars for codegen
        let repl_vars: Vec<(String, Type)> = self
            .bindings
            .iter()
            .map(|(n, info)| (n.clone(), info.ir_type.clone()))
            .collect();

        // REPL codegen
        let classes = krypton_codegen::emit::repl::compile_repl_input(
            &ir_modules,
            &class_name,
            &link_ctx,
            &module_sources,
            &repl_vars,
            store_var.as_deref(),
        )
        .map_err(|e| format!("codegen error: {}", e))?;

        // Send to JVM
        let jvm = self.ensure_jvm()?;
        let result = jvm.load_and_eval(&class_name, &classes, store_var.as_deref())?;

        // Update bindings (let-bindings only)
        if let (Some(name), Some(type_str)) = (binding_name, binding_type_str) {
            self.bindings.retain(|(n, _)| n != &name);
            self.bindings.push((
                name,
                BindingInfo {
                    type_str,
                    ir_type: eval_return_type,
                },
            ));
        }

        // Update fun_defs for function definitions
        if let ReplInputKind::FunDef { ref name, ref source } = kind {
            let type_display = fun_def_type_display
                .clone()
                .unwrap_or_else(|| "?".to_string());
            self.fun_defs.retain(|(n, _, _)| n != name);
            self.fun_defs
                .push((name.clone(), source.clone(), type_display));
        }

        // Return appropriate result
        match &kind {
            ReplInputKind::FunDef { ref name, .. } => {
                let type_display = fun_def_type_display.unwrap_or_else(|| "?".to_string());
                Ok(format!("{}: {}", name, type_display))
            }
            _ => Ok(result),
        }
    }

    pub fn reset(&mut self) {
        self.bindings.clear();
        self.fun_defs.clear();
        if let Some(ref mut jvm) = self.jvm {
            let _ = jvm.reset();
        }
    }

    pub fn format_env(&self) -> String {
        if self.bindings.is_empty() && self.fun_defs.is_empty() {
            return "(no bindings)".to_string();
        }
        let mut lines: Vec<String> = self
            .bindings
            .iter()
            .map(|(name, info)| format!("{} : {}", name, info.type_str))
            .collect();
        for (name, _, type_display) in &self.fun_defs {
            lines.push(format!("{} : {}", name, type_display));
        }
        lines.join("\n")
    }
}

impl Drop for ReplSession {
    fn drop(&mut self) {
        if let Some(ref mut jvm) = self.jvm {
            let _ = jvm.quit();
        }
    }
}

/// Format a `TypeScheme` for REPL display: `(params) -> ret where constraints`.
/// Unlike `TypeScheme::Display`, this omits the `forall vars.` prefix.
fn format_scheme_for_repl(scheme: &TypeScheme) -> String {
    if scheme.vars.is_empty() {
        return format!("{}", scheme.ty);
    }
    let (renamed_ty, names) = scheme.display_var_names();
    let type_part = format_type_with_var_names(&renamed_ty, &names);

    if scheme.constraints.is_empty() {
        return type_part;
    }

    let id_mapping: HashMap<TypeVarId, usize> = scheme
        .vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, i))
        .collect();
    let mut where_parts: Vec<String> = Vec::new();
    for (trait_name, var) in &scheme.constraints {
        let var_name = id_mapping
            .get(var)
            .map(|&i| names[i].clone())
            .unwrap_or_else(|| var.display_name());
        where_parts.push(format!("{}: {}", var_name, trait_name.local_name));
    }
    format!("{} where {}", type_part, where_parts.join(", "))
}


// --- JVM Process Management ---

struct JvmProcess {
    child: Child,
    writer: BufWriter<ChildStdin>,
    reader: BufReader<ChildStdout>,
}

impl JvmProcess {
    fn spawn() -> Result<Self, String> {
        let runtime_jar = find_runtime_jar()
            .ok_or_else(|| "Cannot find krypton-runtime.jar. Build with: ./extern/jvm/gradlew :runtime:build".to_string())?;
        let repl_jar = find_repl_jar()
            .ok_or_else(|| "Cannot find krypton-repl.jar. Build with: ./extern/jvm/gradlew :repl:build".to_string())?;

        let sep = if cfg!(windows) { ";" } else { ":" };
        let classpath = format!("{}{}{}", repl_jar.display(), sep, runtime_jar.display());

        let mut child = Command::new("java")
            .arg("-cp")
            .arg(&classpath)
            .arg("krypton.repl.ReplHost")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("Failed to spawn JVM: {}", e))?;

        let stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();

        Ok(Self {
            child,
            writer: BufWriter::new(stdin),
            reader: BufReader::new(stdout),
        })
    }

    fn load_and_eval(
        &mut self,
        _class_name: &str,
        classes: &[(String, Vec<u8>)],
        store_var: Option<&str>,
    ) -> Result<String, String> {
        // CMD_LOAD = 1
        write_byte(&mut self.writer, 1)?;

        // Number of classes
        write_int(&mut self.writer, classes.len() as i32)?;

        for (name, bytes) in classes {
            write_utf(&mut self.writer, name)?;
            write_int(&mut self.writer, bytes.len() as i32)?;
            self.writer
                .write_all(bytes)
                .map_err(|e| format!("write error: {}", e))?;
        }

        // store_var
        match store_var {
            Some(name) => {
                write_bool(&mut self.writer, true)?;
                write_utf(&mut self.writer, name)?;
            }
            None => {
                write_bool(&mut self.writer, false)?;
            }
        }

        self.writer.flush().map_err(|e| format!("flush error: {}", e))?;

        // Read response
        let resp = read_byte(&mut self.reader)?;
        let msg = read_utf(&mut self.reader)?;

        if resp == 0 {
            Ok(msg)
        } else {
            Err(msg)
        }
    }

    fn reset(&mut self) -> Result<(), String> {
        write_byte(&mut self.writer, 2)?; // CMD_RESET
        self.writer.flush().map_err(|e| format!("flush error: {}", e))?;

        let resp = read_byte(&mut self.reader)?;
        let _msg = read_utf(&mut self.reader)?;

        if resp == 0 {
            Ok(())
        } else {
            Err("reset failed".to_string())
        }
    }

    fn quit(&mut self) -> Result<(), String> {
        write_byte(&mut self.writer, 3)?; // CMD_QUIT
        self.writer.flush().map_err(|e| format!("flush error: {}", e))?;
        let _ = self.child.wait();
        Ok(())
    }
}

// --- Binary protocol helpers (Java DataInputStream/DataOutputStream format) ---

fn write_byte(w: &mut impl Write, b: u8) -> Result<(), String> {
    w.write_all(&[b]).map_err(|e| format!("write error: {}", e))
}

fn write_bool(w: &mut impl Write, b: bool) -> Result<(), String> {
    write_byte(w, if b { 1 } else { 0 })
}

fn write_int(w: &mut impl Write, n: i32) -> Result<(), String> {
    w.write_all(&n.to_be_bytes())
        .map_err(|e| format!("write error: {}", e))
}

fn write_utf(w: &mut impl Write, s: &str) -> Result<(), String> {
    let bytes = s.as_bytes();
    let len = bytes.len() as u16;
    w.write_all(&len.to_be_bytes())
        .map_err(|e| format!("write error: {}", e))?;
    w.write_all(bytes)
        .map_err(|e| format!("write error: {}", e))
}

fn read_byte(r: &mut impl Read) -> Result<u8, String> {
    let mut buf = [0u8; 1];
    r.read_exact(&mut buf)
        .map_err(|e| format!("read error: {}", e))?;
    Ok(buf[0])
}

fn read_utf(r: &mut impl Read) -> Result<String, String> {
    let mut len_buf = [0u8; 2];
    r.read_exact(&mut len_buf)
        .map_err(|e| format!("read error: {}", e))?;
    let len = u16::from_be_bytes(len_buf) as usize;
    let mut buf = vec![0u8; len];
    r.read_exact(&mut buf)
        .map_err(|e| format!("read error: {}", e))?;
    String::from_utf8(buf).map_err(|e| format!("utf8 error: {}", e))
}

// --- JAR discovery ---

pub fn find_runtime_jar() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("KRYPTON_RUNTIME") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../extern/jvm/runtime/build/libs/krypton-runtime.jar");
    if workspace_root.exists() {
        return Some(workspace_root);
    }
    None
}

fn find_repl_jar() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("KRYPTON_REPL_RUNTIME") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../extern/jvm/repl/build/libs/krypton-repl.jar");
    if workspace_root.exists() {
        return Some(workspace_root);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_let_binding() {
        assert_eq!(
            classify_input("let x = 42"),
            ReplInputKind::LetBinding {
                name: "x".to_string(),
                rhs: "42".to_string(),
            }
        );
    }

    #[test]
    fn classify_fun_def() {
        assert_eq!(
            classify_input("fun f(x) = x + 1"),
            ReplInputKind::FunDef {
                name: "f".to_string(),
                source: "fun f(x) = x + 1".to_string(),
            }
        );
    }

    #[test]
    fn classify_bare_expr() {
        assert_eq!(
            classify_input("1 + 2"),
            ReplInputKind::BareExpr {
                source: "1 + 2".to_string(),
            }
        );
    }

    #[test]
    fn wrap_bare_expr_parses() {
        let kind = ReplInputKind::BareExpr {
            source: "1 + 2".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        let (_, errors) = krypton_parser::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_let_parses() {
        let kind = ReplInputKind::LetBinding {
            name: "x".to_string(),
            rhs: "42".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        let (_, errors) = krypton_parser::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_fun_def_parses() {
        let kind = ReplInputKind::FunDef {
            name: "f".to_string(),
            source: "fun f(x: Int) -> Int = x + 1".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = krypton_parser::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_with_prior_bindings() {
        let kind = ReplInputKind::BareExpr {
            source: "x + 1".to_string(),
        };
        let bindings = vec![("x".to_string(), "Int".to_string())];
        let source = build_synthetic_source(&kind, &bindings, &[]);
        assert!(source.contains("fun __eval(x: Int) = x + 1"));
        let (_, errors) = krypton_parser::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_bare_expr_with_prior_fun_defs() {
        let kind = ReplInputKind::BareExpr {
            source: "add(1, 2)".to_string(),
        };
        let fun_defs = vec![(
            "add".to_string(),
            "fun add(a: Int, b: Int) -> Int = a + b".to_string(),
            "(Int, Int) -> Int".to_string(),
        )];
        let source = build_synthetic_source(&kind, &[], &fun_defs);
        assert!(source.contains("fun add(a: Int, b: Int) -> Int = a + b"));
        assert!(source.contains("fun __eval() = add(1, 2)"));
        let (_, errors) = krypton_parser::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_fun_def_does_not_return_function_name() {
        let kind = ReplInputKind::FunDef {
            name: "a".to_string(),
            source: "fun a(x: Int, y: Int) -> Int = x + y".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        // Should NOT try to return `a` as a value
        assert!(!source.contains("= a\n"));
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = krypton_parser::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }
}
