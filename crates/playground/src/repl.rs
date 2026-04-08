//! Browser REPL API: WASM-exported functions for creating and driving REPL sessions.

use std::cell::RefCell;
use std::collections::HashMap;

use krypton_codegen_js::compile_repl_js;
use krypton_diagnostics::Diagnostic;
use krypton_modules::{module_resolver::ModuleResolver, stdlib_loader::StdlibLoader};
use krypton_parser::repl::{build_synthetic_source, classify_input, ReplDeclarations, ReplInputKind};
use krypton_typechecker::types::{format_type_with_var_names, TypeScheme};
use serde::Serialize;
use wasm_bindgen::prelude::*;

use crate::{package_runtime_files, CompiledJsFile};

// ---------------------------------------------------------------------------
// Session state
// ---------------------------------------------------------------------------

struct WasmReplSession {
    /// Prior let-bindings: (name, type_annotation_str).
    bindings: Vec<(String, String)>,
    fun_defs: Vec<(String, String, String)>,
    type_defs: Vec<(String, String)>,
    trait_defs: Vec<(String, String)>,
    impl_defs: Vec<(String, String)>,
    imports: Vec<String>,
    extern_defs: Vec<String>,
    input_counter: u32,
    runtime_sent: bool,
    pending: Option<PendingUpdate>,
}

enum PendingUpdate {
    None,
    LetBinding {
        name: String,
        type_str: String,
    },
    FunDef {
        name: String,
        source: String,
        type_display: String,
    },
    TypeDef {
        name: String,
        source: String,
    },
    TraitDef {
        name: String,
        source: String,
    },
    ImplDef {
        key: String,
        source: String,
    },
    Import {
        source: String,
    },
    ExternDef {
        source: String,
    },
}

impl WasmReplSession {
    fn new() -> Self {
        Self {
            bindings: Vec::new(),
            fun_defs: Vec::new(),
            type_defs: Vec::new(),
            trait_defs: Vec::new(),
            impl_defs: Vec::new(),
            imports: Vec::new(),
            extern_defs: Vec::new(),
            input_counter: 0,
            runtime_sent: false,
            pending: None,
        }
    }

    fn next_module_name(&mut self) -> String {
        self.input_counter += 1;
        format!("repl_{}", self.input_counter)
    }

    fn build_decls(&self) -> ReplDeclarations {
        ReplDeclarations {
            imports: self.imports.clone(),
            type_defs: self.type_defs.clone(),
            trait_defs: self.trait_defs.clone(),
            impl_defs: self.impl_defs.clone(),
            extern_defs: self.extern_defs.clone(),
            fun_defs: self.fun_defs.clone(),
            bindings: self.bindings.clone(),
        }
    }
}

thread_local! {
    static SESSIONS: RefCell<HashMap<u32, WasmReplSession>> = RefCell::new(HashMap::new());
    static NEXT_ID: RefCell<u32> = const { RefCell::new(1) };
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Serialize)]
pub struct ReplEvalResult {
    pub success: bool,
    pub files: Vec<CompiledJsFile>,
    pub entry_module: String,
    pub store_binding: Option<String>,
    pub display: String,
    pub diagnostics: Vec<Diagnostic>,
    pub include_runtime: bool,
    pub runtime_files: Vec<CompiledJsFile>,
}

impl ReplEvalResult {
    fn failure(diagnostics: Vec<Diagnostic>) -> Self {
        Self {
            success: false,
            files: Vec::new(),
            entry_module: String::new(),
            store_binding: None,
            display: String::new(),
            diagnostics,
            include_runtime: false,
            runtime_files: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Module resolver for REPL synthetic source
// ---------------------------------------------------------------------------

struct ReplResolver {
    module_name: String,
    source: String,
}

impl ModuleResolver for ReplResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        if module_path == self.module_name {
            return Some(self.source.clone());
        }
        StdlibLoader::get_source(module_path).map(str::to_owned)
    }
}

// ---------------------------------------------------------------------------
// WASM exports
// ---------------------------------------------------------------------------

#[wasm_bindgen]
pub fn repl_create() -> u32 {
    let id = NEXT_ID.with(|cell| {
        let mut next = cell.borrow_mut();
        let id = *next;
        *next += 1;
        id
    });
    SESSIONS.with(|cell| {
        cell.borrow_mut().insert(id, WasmReplSession::new());
    });
    id
}

#[wasm_bindgen]
pub fn repl_eval(session_id: u32, input: &str) -> Result<JsValue, JsValue> {
    let result = SESSIONS.with(|cell| {
        let mut sessions = cell.borrow_mut();
        let session = sessions
            .get_mut(&session_id)
            .ok_or_else(|| format!("Invalid REPL session ID: {}", session_id))?;
        eval_impl(session, input)
    });
    match result {
        Ok(r) => serde_wasm_bindgen::to_value(&r)
            .map_err(|e| JsValue::from_str(&e.to_string())),
        Err(e) => Err(JsValue::from_str(&e)),
    }
}

#[wasm_bindgen]
pub fn repl_commit(session_id: u32) -> Result<(), JsValue> {
    SESSIONS.with(|cell| {
        let mut sessions = cell.borrow_mut();
        let session = sessions
            .get_mut(&session_id)
            .ok_or_else(|| JsValue::from_str(&format!("Invalid REPL session ID: {}", session_id)))?;

        if let Some(update) = session.pending.take() {
            match update {
                PendingUpdate::None => {}
                PendingUpdate::LetBinding { name, type_str } => {
                    session.bindings.retain(|(n, _)| n != &name);
                    session.bindings.push((name, type_str));
                }
                PendingUpdate::FunDef {
                    name,
                    source,
                    type_display,
                } => {
                    session.fun_defs.retain(|(n, _, _)| n != &name);
                    session.fun_defs.push((name, source, type_display));
                }
                PendingUpdate::TypeDef { name, source } => {
                    session.type_defs.retain(|(n, _)| n != &name);
                    session.type_defs.push((name, source));
                }
                PendingUpdate::TraitDef { name, source } => {
                    session.trait_defs.retain(|(n, _)| n != &name);
                    session.trait_defs.push((name, source));
                }
                PendingUpdate::ImplDef { key, source } => {
                    session.impl_defs.retain(|(k, _)| k != &key);
                    session.impl_defs.push((key, source));
                }
                PendingUpdate::Import { source } => {
                    if !session.imports.contains(&source) {
                        session.imports.push(source);
                    }
                }
                PendingUpdate::ExternDef { source } => {
                    session.extern_defs.push(source);
                }
            }
        }
        Ok(())
    })
}

#[wasm_bindgen]
pub fn repl_reset(session_id: u32) -> Result<(), JsValue> {
    SESSIONS.with(|cell| {
        let mut sessions = cell.borrow_mut();
        let session = sessions
            .get_mut(&session_id)
            .ok_or_else(|| JsValue::from_str(&format!("Invalid REPL session ID: {}", session_id)))?;
        session.bindings.clear();
        session.fun_defs.clear();
        session.type_defs.clear();
        session.trait_defs.clear();
        session.impl_defs.clear();
        session.imports.clear();
        session.extern_defs.clear();
        session.pending = None;
        session.input_counter = 0;
        session.runtime_sent = false;
        Ok(())
    })
}

#[wasm_bindgen]
pub fn repl_destroy(session_id: u32) {
    SESSIONS.with(|cell| {
        cell.borrow_mut().remove(&session_id);
    });
}

// ---------------------------------------------------------------------------
// Core eval pipeline
// ---------------------------------------------------------------------------

fn eval_impl(session: &mut WasmReplSession, input: &str) -> Result<ReplEvalResult, String> {
    let kind = classify_input(input);
    let module_name = session.next_module_name();
    let repl_filename = format!("{}.kr", module_name);
    let include_runtime = !session.runtime_sent;
    let decls = session.build_decls();

    // For bare expressions, try show-wrapping first, fall back if typecheck fails
    let is_bare_expr = matches!(kind, ReplInputKind::BareExpr { .. });
    let (synthetic, show_wrapped) = if is_bare_expr {
        let show_source = build_synthetic_source(&kind, &decls, true);
        let (show_module, show_parse_errors) = krypton_parser::parser::parse(&show_source);
        if show_parse_errors.is_empty() {
            let show_resolver = ReplResolver {
                module_name: module_name.clone(),
                source: show_source.clone(),
            };
            match krypton_typechecker::infer::infer_module(
                &show_module,
                &show_resolver,
                module_name.clone(),
                krypton_parser::ast::CompileTarget::Js,
            ) {
                Ok(_) => (show_source, true),
                Err(_) => {
                    // Show wrapping failed (e.g. no Show instance), fall back
                    (build_synthetic_source(&kind, &decls, false), false)
                }
            }
        } else {
            (build_synthetic_source(&kind, &decls, false), false)
        }
    } else {
        (build_synthetic_source(&kind, &decls, false), false)
    };

    // Parse
    let (module, parse_errors) = krypton_parser::parser::parse(&synthetic);
    if !parse_errors.is_empty() {
        let (diags, _srcs) = krypton_parser::diagnostics::lower_parse_errors(
            &repl_filename,
            &synthetic,
            &parse_errors,
        );
        return Ok(ReplEvalResult::failure(diags));
    }

    // Typecheck
    let resolver = ReplResolver {
        module_name: module_name.clone(),
        source: synthetic.clone(),
    };
    let (typed_modules, interfaces) = match krypton_typechecker::infer::infer_module(
        &module,
        &resolver,
        module_name.clone(),
        krypton_parser::ast::CompileTarget::Js,
    ) {
        Ok(result) => result,
        Err(errors) => {
            let (diags, _srcs) = krypton_typechecker::diagnostics::lower_infer_errors(
                &repl_filename,
                &synthetic,
                &errors,
            );
            return Ok(ReplEvalResult::failure(diags));
        }
    };

    let root_typed = &typed_modules[0];

    // Extract __eval's type entry
    let _eval_type_entry = root_typed
        .fn_types
        .iter()
        .find(|e| e.name == "__eval")
        .ok_or_else(|| "ICE: __eval not found in typed module".to_string())?;

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

    // Build LinkContext + lower to IR
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        krypton_ir::lower::lower_all(&typed_modules, &module_name, &link_ctx)
            .map_err(|e| format!("IR lowering error: {}", e))?;

    // Find __eval's return type from IR
    let root_ir = &ir_modules[0];
    let eval_fn = root_ir
        .functions
        .iter()
        .find(|f| f.name == "__eval")
        .ok_or_else(|| "ICE: __eval not found in IR module".to_string())?;
    let eval_return_type = eval_fn.return_type.clone();

    // Determine store_var and display string
    let (store_var, display, pending_update) = match &kind {
        ReplInputKind::LetBinding { name, .. } => {
            let type_str = eval_return_type.to_string();
            let display = format!("{}: {}", name, type_str);
            let pending = PendingUpdate::LetBinding {
                name: name.clone(),
                type_str,
            };
            (Some(name.clone()), display, pending)
        }
        ReplInputKind::BareExpr { .. } => {
            (None, String::new(), PendingUpdate::None)
        }
        ReplInputKind::FunDef { name, source } => {
            let type_display = fun_def_type_display
                .clone()
                .unwrap_or_else(|| "?".to_string());
            let display = format!("{}: {}", name, type_display);
            let pending = PendingUpdate::FunDef {
                name: name.clone(),
                source: source.clone(),
                type_display,
            };
            (None, display, pending)
        }
        ReplInputKind::TypeDef { name, source } => {
            let display = format!("type {}", name);
            let pending = PendingUpdate::TypeDef {
                name: name.clone(),
                source: source.clone(),
            };
            (None, display, pending)
        }
        ReplInputKind::TraitDef { name, source } => {
            let display = format!("trait {}", name);
            let pending = PendingUpdate::TraitDef {
                name: name.clone(),
                source: source.clone(),
            };
            (None, display, pending)
        }
        ReplInputKind::ImplDef { key, source } => {
            let display = format!("impl {}", key);
            let pending = PendingUpdate::ImplDef {
                key: key.clone(),
                source: source.clone(),
            };
            (None, display, pending)
        }
        ReplInputKind::Import { source } => {
            let display = source.clone();
            let pending = PendingUpdate::Import {
                source: source.clone(),
            };
            (None, display, pending)
        }
        ReplInputKind::ExternDef { source } => {
            let display = "extern defined".to_string();
            let pending = PendingUpdate::ExternDef {
                source: source.clone(),
            };
            (None, display, pending)
        }
    };

    // Build repl_vars: (name, registry_key) from existing bindings
    let repl_vars: Vec<(String, String)> = session
        .bindings
        .iter()
        .map(|(n, _)| (n.clone(), n.clone()))
        .collect();

    // JS codegen with REPL wrapper
    let js_module_sources: HashMap<String, Option<String>> =
        module_sources.into_iter().map(|(k, v)| (k, Some(v))).collect();
    let js_files = compile_repl_js(
        &ir_modules,
        &module_name,
        &link_ctx,
        &js_module_sources,
        &repl_vars,
        store_var.as_deref(),
        show_wrapped,
    )
    .map_err(|e| format!("JS codegen error: {}", e))?;

    let files: Vec<CompiledJsFile> = js_files
        .into_iter()
        .map(|(path, source)| CompiledJsFile { path, source })
        .collect();

    // Package runtime files if not yet sent
    let mut runtime_files = Vec::new();
    if include_runtime {
        package_runtime_files(&mut runtime_files);
        session.runtime_sent = true;
    }

    // Store pending update (do NOT apply yet — wait for repl_commit)
    session.pending = Some(pending_update);

    Ok(ReplEvalResult {
        success: true,
        files,
        entry_module: format!("{}.mjs", module_name),
        store_binding: store_var,
        display,
        diagnostics: Vec::new(),
        include_runtime,
        runtime_files,
    })
}

/// Format a `TypeScheme` for REPL display.
fn format_scheme_for_repl(scheme: &TypeScheme) -> String {
    if scheme.vars.is_empty() {
        return format!("{}", scheme.ty);
    }
    let (renamed_ty, names) = scheme.display_var_names();
    let type_part = format_type_with_var_names(&renamed_ty, &names);

    if scheme.constraints.is_empty() {
        return type_part;
    }

    let id_mapping: HashMap<krypton_typechecker::types::TypeVarId, usize> = scheme
        .vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, i))
        .collect();
    let mut where_parts: Vec<String> = Vec::new();
    for (trait_name, vars) in &scheme.constraints {
        let var_names: Vec<String> = vars
            .iter()
            .map(|var| {
                id_mapping
                    .get(var)
                    .map(|&i| names[i].clone())
                    .unwrap_or_else(|| var.display_name())
            })
            .collect();
        if var_names.len() == 1 {
            where_parts.push(format!("{}: {}", var_names[0], trait_name.local_name));
        } else {
            where_parts.push(format!("{}[{}]", trait_name.local_name, var_names.join(", ")));
        }
    }
    format!("{} where {}", type_part, where_parts.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repl_session_lifecycle() {
        let id = repl_create();

        // Eval a bare expr — value shown but not stored as binding
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "1 + 2")
        });
        let result = result.unwrap();
        assert!(result.success, "eval failed: {:?}", result.diagnostics);
        assert_eq!(result.store_binding, None);
        assert!(result.include_runtime);

        repl_commit(id).unwrap();

        // Eval a let binding
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "let x = 10")
        });
        let result = result.unwrap();
        assert!(result.success, "eval failed: {:?}", result.diagnostics);
        assert_eq!(result.display, "x: Int");
        assert!(!result.include_runtime);

        repl_commit(id).unwrap();

        // Eval using prior binding
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "x * 2")
        });
        let result = result.unwrap();
        assert!(result.success, "eval failed: {:?}", result.diagnostics);

        // Verify the entry module has the repl wrapper with prior let binding
        let entry = result
            .files
            .iter()
            .find(|f| f.path == result.entry_module)
            .unwrap();
        assert!(entry.source.contains("__repl_eval"));
        assert!(entry.source.contains("__repl_lookup(\"x\")"));

        repl_commit(id).unwrap();

        // Fun def
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "fun f(n: Int) -> Int = n + 1")
        });
        let result = result.unwrap();
        assert!(result.success, "eval failed: {:?}", result.diagnostics);
        assert!(result.display.starts_with("f:"));
        assert_eq!(result.store_binding, None);

        repl_destroy(id);
    }

    #[test]
    fn repl_reset_clears_state() {
        let id = repl_create();

        // Add a binding
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "let x = 5")
        });
        assert!(result.unwrap().success);
        repl_commit(id).unwrap();

        // Reset
        repl_reset(id).unwrap();

        // Bare expr after reset
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "42")
        });
        let result = result.unwrap();
        assert!(result.success);

        repl_destroy(id);
    }

    #[test]
    fn repl_parse_error_does_not_commit() {
        let id = repl_create();

        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "let = ")
        });
        let result = result.unwrap();
        assert!(!result.success);
        assert!(!result.diagnostics.is_empty());

        repl_destroy(id);
    }

    #[test]
    fn repl_runtime_sent_after_failed_first_eval() {
        let id = repl_create();

        // First eval fails (type error)
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "hi")
        });
        let result = result.unwrap();
        assert!(!result.success);

        // Second eval succeeds — should still include runtime
        let result = SESSIONS.with(|cell| {
            let mut sessions = cell.borrow_mut();
            let session = sessions.get_mut(&id).unwrap();
            eval_impl(session, "42")
        });
        let result = result.unwrap();
        assert!(result.success, "eval failed: {:?}", result.diagnostics);
        assert!(result.include_runtime, "runtime should be included after failed first eval");
        assert!(!result.runtime_files.is_empty());

        repl_destroy(id);
    }
}
