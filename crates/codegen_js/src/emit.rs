use std::collections::HashMap;
use std::fmt;

use krypton_ir::{
    Atom, Expr, ExprKind, FnId, Literal, Module, PrimOp, SimpleExpr, StructDef, SumTypeDef,
    VarId,
};
use krypton_typechecker::typed_ast::TypedModule;

/// Errors that can occur during JS code generation.
#[derive(Debug, Clone)]
pub enum JsCodegenError {
    LowerError(String),
    UnsupportedFeature(String),
}

impl fmt::Display for JsCodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JsCodegenError::LowerError(msg) => write!(f, "IR lowering error: {msg}"),
            JsCodegenError::UnsupportedFeature(msg) => {
                write!(f, "unsupported JS feature: {msg}")
            }
        }
    }
}

impl std::error::Error for JsCodegenError {}

/// Compile all typed modules to JavaScript ESM (.mjs) files.
///
/// Returns `Vec<(filename, js_source)>` where filename uses `.mjs` extension.
pub fn compile_modules_js(
    typed_modules: &[TypedModule],
    main_module_name: &str,
) -> Result<Vec<(String, String)>, JsCodegenError> {
    let root_module_path = typed_modules
        .first()
        .map(|tm| tm.module_path.as_str())
        .unwrap_or("");

    let mut ir_modules: Vec<Module> = Vec::new();
    for tm in typed_modules {
        let is_root = tm.module_path == root_module_path;
        let mod_name = if is_root {
            main_module_name
        } else {
            &tm.module_path
        };
        let ir = krypton_ir::lower::lower_module(tm, mod_name).map_err(|e| {
            JsCodegenError::LowerError(format!("module {mod_name}: {e}"))
        })?;
        ir_modules.push(ir);
    }

    let mut results = Vec::new();
    for ir_module in &ir_modules {
        let mut emitter = JsEmitter::new(ir_module);
        let js_source = emitter.emit();
        let filename = format!("{}.mjs", ir_module.name);
        results.push((filename, js_source));
    }

    Ok(results)
}

/// Accumulates JavaScript source for a single IR module.
pub(crate) struct JsEmitter<'a> {
    output: String,
    indent: usize,
    module: &'a Module,
    /// Maps VarId → JS variable name for the current function scope.
    var_names: HashMap<VarId, String>,
    /// Counter for generating unique variable names.
    var_counter: usize,
}

impl<'a> JsEmitter<'a> {
    pub(crate) fn new(module: &'a Module) -> Self {
        JsEmitter {
            output: String::new(),
            indent: 0,
            module,
            var_names: HashMap::new(),
            var_counter: 0,
        }
    }

    pub(crate) fn emit(&mut self) -> String {
        self.emit_imports();
        self.emit_structs();
        self.emit_sum_types();
        self.emit_functions();
        self.output.clone()
    }

    // ── Helpers ──────────────────────────────────────────────

    fn write(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn writeln(&mut self, s: &str) {
        self.write_indent();
        self.output.push_str(s);
        self.output.push('\n');
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.output.push_str("  ");
        }
    }

    fn fresh_var(&mut self, hint: &str) -> String {
        let name = format!("{}${}", hint, self.var_counter);
        self.var_counter += 1;
        name
    }

    fn bind_var(&mut self, var: VarId) -> String {
        let name = self.fresh_var("v");
        self.var_names.insert(var, name.clone());
        name
    }

    fn var_name(&self, var: VarId) -> String {
        self.var_names
            .get(&var)
            .cloned()
            .unwrap_or_else(|| format!("v_{}", var.0))
    }

    /// Compute a relative import path from the current module to `target_module`.
    /// E.g. from `core/io` to `core/result` → `./result.mjs`,
    /// from `test` to `core/list` → `./core/list.mjs`,
    /// from `core/io` to `util` → `../util.mjs`.
    fn relative_import_path(&self, target_module: &str) -> String {
        let from_dir: Vec<&str> = {
            let parts: Vec<&str> = self.module.module_path.split('/').collect();
            // Directory is everything except the last component (the filename stem).
            if parts.len() > 1 {
                parts[..parts.len() - 1].to_vec()
            } else {
                vec![]
            }
        };
        let to_parts: Vec<&str> = target_module.split('/').collect();
        let to_dir = if to_parts.len() > 1 {
            &to_parts[..to_parts.len() - 1]
        } else {
            &[]
        };
        let to_file = to_parts.last().unwrap();

        // Find common prefix length.
        let common = from_dir
            .iter()
            .zip(to_dir.iter())
            .take_while(|(a, b)| a == b)
            .count();

        let ups = from_dir.len() - common;
        let mut path = String::new();
        if ups == 0 && to_dir.len() == common {
            path.push_str("./");
        } else {
            for _ in 0..ups {
                path.push_str("../");
            }
            if ups == 0 {
                path.push_str("./");
            }
        }
        for &segment in &to_dir[common..] {
            path.push_str(segment);
            path.push('/');
        }
        path.push_str(to_file);
        path.push_str(".mjs");
        path
    }

    fn fn_name(&self, id: FnId) -> String {
        self.module
            .fn_names
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("fn_{}", id.0))
    }

    // ── Imports ──────────────────────────────────────────────

    fn emit_imports(&mut self) {
        use std::collections::HashSet;

        // Collect locally-defined names to detect shadowing.
        let mut local_names: HashSet<&str> = HashSet::new();
        for f in &self.module.functions {
            local_names.insert(&f.name);
        }
        for s in &self.module.structs {
            local_names.insert(&s.name);
        }
        for st in &self.module.sum_types {
            local_names.insert(&st.name);
            for v in &st.variants {
                local_names.insert(&v.name);
            }
        }

        // Group imported functions by source module.
        // Each import tracks (original_name, local_name) so we can emit
        // `import { original as local }` when they differ or when `original`
        // would shadow a local definition.
        let mut by_module: HashMap<&str, Vec<(&str, &str)>> = HashMap::new();
        for imp in &self.module.imported_fns {
            by_module
                .entry(&imp.source_module)
                .or_default()
                .push((&imp.original_name, &imp.name));
        }

        let mut modules: Vec<&&str> = by_module.keys().collect();
        modules.sort();
        let mut emitted_any = false;
        for module_path in modules {
            let entries = by_module.get(*module_path).unwrap();
            let mut seen = HashSet::new();
            let mut specifiers: Vec<String> = Vec::new();
            for &(original, local) in entries {
                if !seen.insert((original, local)) {
                    continue;
                }
                // When the local name shadows a local definition, the IR
                // lowerer reuses the local FnId, so call sites already
                // resolve to the local function — skip the import entirely.
                if local_names.contains(local) {
                    continue;
                }
                if original == local {
                    specifiers.push(original.to_string());
                } else {
                    specifiers.push(format!("{original} as {local}"));
                }
            }
            specifiers.sort();
            specifiers.dedup();
            if !specifiers.is_empty() {
                let rel_path = self.relative_import_path(module_path);
                self.writeln(&format!(
                    "import {{ {} }} from '{}';",
                    specifiers.join(", "),
                    rel_path
                ));
                emitted_any = true;
            }
        }

        if emitted_any {
            self.write("\n");
        }
    }

    // ── Structs ──────────────────────────────────────────────

    fn emit_structs(&mut self) {
        for s in &self.module.structs {
            self.emit_struct(s);
            self.write("\n");
        }
    }

    fn emit_struct(&mut self, s: &StructDef) {
        self.writeln(&format!("export class {} {{", s.name));
        self.indent += 1;

        // Constructor
        let field_names: Vec<&str> = s.fields.iter().map(|(name, _)| name.as_str()).collect();
        self.writeln(&format!("constructor({}) {{", field_names.join(", ")));
        self.indent += 1;
        for name in &field_names {
            self.writeln(&format!("this.{name} = {name};"));
        }
        self.indent -= 1;
        self.writeln("}");

        self.indent -= 1;
        self.writeln("}");
    }

    // ── Sum Types ────────────────────────────────────────────

    fn emit_sum_types(&mut self) {
        for st in &self.module.sum_types {
            self.emit_sum_type(st);
            self.write("\n");
        }
    }

    fn emit_sum_type(&mut self, st: &SumTypeDef) {
        // Base class
        self.writeln(&format!("export class {} {{", st.name));
        self.writeln("}");
        self.write("\n");

        // Variant subclasses
        for variant in &st.variants {
            self.writeln(&format!(
                "export class {} extends {} {{",
                variant.name, st.name
            ));
            self.indent += 1;

            // Tag getter for switch dispatch
            self.writeln(&format!("get $tag() {{ return {}; }}", variant.tag));

            if variant.fields.is_empty() {
                // Zero-arg variant: singleton
                self.writeln(&format!(
                    "static INSTANCE = new {}();",
                    variant.name
                ));
            } else {
                // Constructor with positional fields _0, _1, ...
                let params: Vec<String> =
                    (0..variant.fields.len()).map(|i| format!("_{i}")).collect();
                self.writeln(&format!("constructor({}) {{", params.join(", ")));
                self.indent += 1;
                self.writeln("super();");
                for p in &params {
                    self.writeln(&format!("this.{p} = {p};"));
                }
                self.indent -= 1;
                self.writeln("}");
            }

            self.indent -= 1;
            self.writeln("}");
            self.write("\n");
        }
    }

    // ── Functions ────────────────────────────────────────────

    fn emit_functions(&mut self) {
        for func in &self.module.functions {
            self.emit_function(func);
            self.write("\n");
        }
    }

    fn emit_function(&mut self, func: &krypton_ir::FnDef) {
        // Reset variable state for each function
        self.var_names.clear();
        self.var_counter = 0;

        // Bind parameter names
        let param_names: Vec<String> = func
            .params
            .iter()
            .map(|(var, _)| self.bind_var(*var))
            .collect();

        self.writeln(&format!(
            "export function {}({}) {{",
            func.name,
            param_names.join(", ")
        ));
        self.indent += 1;
        self.emit_expr(&func.body, true);
        self.indent -= 1;
        self.writeln("}");
    }

    // ── Expressions ──────────────────────────────────────────

    fn emit_expr(&mut self, expr: &Expr, tail: bool) {
        match &expr.kind {
            ExprKind::Atom(atom) => {
                if tail {
                    self.write_indent();
                    self.write("return ");
                    self.write(&self.emit_atom(atom));
                    self.write(";\n");
                } else {
                    self.write(&self.emit_atom(atom));
                }
            }
            ExprKind::Let {
                bind,
                value,
                body,
                ..
            } => {
                let var_name = self.bind_var(*bind);
                self.write_indent();
                self.write(&format!("const {var_name} = "));
                self.emit_simple_expr(value);
                self.write(";\n");
                self.emit_expr(body, tail);
            }
            ExprKind::LetRec {
                bindings, body, ..
            } => {
                for (var, _, fn_id, captures) in bindings {
                    let var_name = self.bind_var(*var);
                    let fn_name = self.fn_name(*fn_id);
                    if captures.is_empty() {
                        self.writeln(&format!("const {var_name} = {fn_name};"));
                    } else {
                        let caps: Vec<String> =
                            captures.iter().map(|a| self.emit_atom(a)).collect();
                        self.writeln(&format!(
                            "const {var_name} = (...args) => {fn_name}({}, ...args);",
                            caps.join(", ")
                        ));
                    }
                }
                self.emit_expr(body, tail);
            }
            ExprKind::LetJoin {
                name,
                params,
                join_body,
                body,
                is_recur,
            } => {
                let join_name = self.bind_var(*name);
                let param_names: Vec<String> =
                    params.iter().map(|(v, _)| self.bind_var(*v)).collect();

                if *is_recur {
                    // Recursive join point → while(true) loop
                    self.writeln(&format!(
                        "function {join_name}({}) {{",
                        param_names.join(", ")
                    ));
                    self.indent += 1;
                    self.writeln("while (true) {");
                    self.indent += 1;
                    self.emit_expr(join_body, true);
                    self.indent -= 1;
                    self.writeln("}");
                    self.indent -= 1;
                    self.writeln("}");
                } else {
                    self.writeln(&format!(
                        "function {join_name}({}) {{",
                        param_names.join(", ")
                    ));
                    self.indent += 1;
                    self.emit_expr(join_body, true);
                    self.indent -= 1;
                    self.writeln("}");
                }
                self.emit_expr(body, tail);
            }
            ExprKind::Jump { target, args } => {
                let target_name = self.var_name(*target);
                let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                if tail {
                    self.writeln(&format!(
                        "return {target_name}({});",
                        arg_strs.join(", ")
                    ));
                } else {
                    self.writeln(&format!(
                        "{target_name}({});",
                        arg_strs.join(", ")
                    ));
                }
            }
            ExprKind::BoolSwitch {
                scrutinee,
                true_body,
                false_body,
            } => {
                let scrut = self.emit_atom(scrutinee);
                self.writeln(&format!("if ({scrut}) {{"));
                self.indent += 1;
                self.emit_expr(true_body, tail);
                self.indent -= 1;
                self.writeln("} else {");
                self.indent += 1;
                self.emit_expr(false_body, tail);
                self.indent -= 1;
                self.writeln("}");
            }
            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                let scrut = self.emit_atom(scrutinee);
                self.writeln(&format!("switch ({scrut}.$tag) {{"));
                self.indent += 1;
                for branch in branches {
                    self.writeln(&format!("case {}: {{", branch.tag));
                    self.indent += 1;
                    // Bind variant fields
                    for (i, (var, _)) in branch.bindings.iter().enumerate() {
                        let var_name = self.bind_var(*var);
                        self.writeln(&format!("const {var_name} = {scrut}._{i};"));
                    }
                    self.emit_expr(&branch.body, tail);
                    if !tail {
                        self.writeln("break;");
                    }
                    self.indent -= 1;
                    self.writeln("}");
                }
                if let Some(default_body) = default {
                    self.writeln("default: {");
                    self.indent += 1;
                    self.emit_expr(default_body, tail);
                    if !tail {
                        self.writeln("break;");
                    }
                    self.indent -= 1;
                    self.writeln("}");
                }
                self.indent -= 1;
                self.writeln("}");
            }
        }
    }

    fn emit_simple_expr(&mut self, expr: &SimpleExpr) {
        match expr {
            SimpleExpr::Atom(atom) => {
                self.write(&self.emit_atom(atom));
            }
            SimpleExpr::PrimOp { op, args } => {
                self.emit_prim_op(*op, args);
            }
            SimpleExpr::Call { func, args } => {
                let fn_name = self.fn_name(*func);
                let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                self.write(&format!("{fn_name}({})", arg_strs.join(", ")));
            }
            SimpleExpr::CallClosure { closure, args } => {
                let closure_str = self.emit_atom(closure);
                let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                self.write(&format!("{closure_str}({})", arg_strs.join(", ")));
            }
            SimpleExpr::MakeClosure { func, captures } => {
                let fn_name = self.fn_name(*func);
                if captures.is_empty() {
                    self.write(&fn_name);
                } else {
                    let caps: Vec<String> = captures.iter().map(|a| self.emit_atom(a)).collect();
                    self.write(&format!(
                        "(...args) => {fn_name}({}, ...args)",
                        caps.join(", ")
                    ));
                }
            }
            SimpleExpr::Construct { type_name, fields } => {
                let arg_strs: Vec<String> = fields.iter().map(|a| self.emit_atom(a)).collect();
                // Use the bare type name (strip module path prefix)
                let bare_name = type_name.rsplit('/').next().unwrap_or(type_name);
                self.write(&format!("new {bare_name}({})", arg_strs.join(", ")));
            }
            SimpleExpr::ConstructVariant {
                variant,
                fields,
                ..
            } => {
                if fields.is_empty() {
                    self.write(&format!("{variant}.INSTANCE"));
                } else {
                    let arg_strs: Vec<String> =
                        fields.iter().map(|a| self.emit_atom(a)).collect();
                    self.write(&format!("new {variant}({})", arg_strs.join(", ")));
                }
            }
            SimpleExpr::Project { value, field_index } => {
                let val = self.emit_atom(value);
                // Look up the struct to get the field name
                let field_name = self.resolve_field_name(&val, *field_index);
                self.write(&format!("{val}.{field_name}"));
            }
            SimpleExpr::Tag { value } => {
                let val = self.emit_atom(value);
                self.write(&format!("{val}.$tag"));
            }
            SimpleExpr::MakeTuple { elements } => {
                let elems: Vec<String> = elements.iter().map(|a| self.emit_atom(a)).collect();
                self.write(&format!("[{}]", elems.join(", ")));
            }
            SimpleExpr::TupleProject { value, index } => {
                let val = self.emit_atom(value);
                self.write(&format!("{val}[{index}]"));
            }
            SimpleExpr::TraitCall { method_name, args, .. } => {
                // args[0] is the dict, args[1..] are user args
                let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                if arg_strs.is_empty() {
                    self.write(&format!("/* trait call {method_name} */ undefined"));
                } else {
                    let dict = &arg_strs[0];
                    let user_args = &arg_strs[1..];
                    self.write(&format!(
                        "{dict}.{method_name}({})",
                        user_args.join(", ")
                    ));
                }
            }
            SimpleExpr::GetDict { .. } => {
                // Placeholder — dict resolution deferred to M23-T5/T6
                self.write("/* TODO: GetDict */ {}");
            }
            SimpleExpr::MakeDict { .. } => {
                self.write("/* TODO: MakeDict */ {}");
            }
            SimpleExpr::MakeVec { elements, .. } => {
                let elems: Vec<String> = elements.iter().map(|a| self.emit_atom(a)).collect();
                self.write(&format!("[{}]", elems.join(", ")));
            }
        }
    }

    fn emit_atom(&self, atom: &Atom) -> String {
        match atom {
            Atom::Var(var) => self.var_name(*var),
            Atom::Lit(lit) => self.emit_literal(lit),
        }
    }

    fn emit_literal(&self, lit: &Literal) -> String {
        match lit {
            Literal::Int(n) => format!("{n}n"),
            Literal::Float(f) => {
                if f.fract() == 0.0 && f.is_finite() {
                    format!("{f:.1}")
                } else {
                    format!("{f}")
                }
            }
            Literal::Bool(b) => format!("{b}"),
            Literal::String(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
            Literal::Unit => "undefined".to_string(),
        }
    }

    fn emit_prim_op(&mut self, op: PrimOp, args: &[Atom]) {
        let a = || self.emit_atom(&args[0]);
        let b = || self.emit_atom(&args[1]);

        match op {
            // Integer arithmetic — BigInt
            PrimOp::AddInt => self.write(&format!("({} + {})", a(), b())),
            PrimOp::SubInt => self.write(&format!("({} - {})", a(), b())),
            PrimOp::MulInt => self.write(&format!("({} * {})", a(), b())),
            PrimOp::DivInt => self.write(&format!("({} / {})", a(), b())),
            PrimOp::ModInt => self.write(&format!("({} % {})", a(), b())),
            PrimOp::NegInt => self.write(&format!("(-{})", a())),

            // Float arithmetic
            PrimOp::AddFloat => self.write(&format!("({} + {})", a(), b())),
            PrimOp::SubFloat => self.write(&format!("({} - {})", a(), b())),
            PrimOp::MulFloat => self.write(&format!("({} * {})", a(), b())),
            PrimOp::DivFloat => self.write(&format!("({} / {})", a(), b())),
            PrimOp::NegFloat => self.write(&format!("(-{})", a())),

            // Integer comparison
            PrimOp::EqInt => self.write(&format!("({} === {})", a(), b())),
            PrimOp::NeqInt => self.write(&format!("({} !== {})", a(), b())),
            PrimOp::LtInt => self.write(&format!("({} < {})", a(), b())),
            PrimOp::LeInt => self.write(&format!("({} <= {})", a(), b())),
            PrimOp::GtInt => self.write(&format!("({} > {})", a(), b())),
            PrimOp::GeInt => self.write(&format!("({} >= {})", a(), b())),

            // Float comparison
            PrimOp::EqFloat => self.write(&format!("({} === {})", a(), b())),
            PrimOp::NeqFloat => self.write(&format!("({} !== {})", a(), b())),
            PrimOp::LtFloat => self.write(&format!("({} < {})", a(), b())),
            PrimOp::LeFloat => self.write(&format!("({} <= {})", a(), b())),
            PrimOp::GtFloat => self.write(&format!("({} > {})", a(), b())),
            PrimOp::GeFloat => self.write(&format!("({} >= {})", a(), b())),

            // Boolean
            PrimOp::Not => self.write(&format!("(!{})", a())),
            PrimOp::And => self.write(&format!("({} && {})", a(), b())),
            PrimOp::Or => self.write(&format!("({} || {})", a(), b())),

            // String
            PrimOp::EqString => self.write(&format!("({} === {})", a(), b())),
            PrimOp::NeqString => self.write(&format!("({} !== {})", a(), b())),
            PrimOp::ConcatString => self.write(&format!("({} + {})", a(), b())),

            // Conversions
            PrimOp::IntToFloat => self.write(&format!("Number({})", a())),
            PrimOp::FloatToInt => self.write(&format!("BigInt(Math.trunc({}))", a())),
            PrimOp::IntToString => self.write(&format!("String({})", a())),
            PrimOp::FloatToString => self.write(&format!("String({})", a())),
            PrimOp::BoolToString => self.write(&format!("String({})", a())),
        }
    }

    /// Resolve a field name for a Project operation.
    /// Tries to find a struct with a matching field index; falls back to `_N`.
    fn resolve_field_name(&self, _value: &str, field_index: usize) -> String {
        // For structs, look up the field name from struct definitions.
        // Since we don't have type info on the value at this point, we search
        // all structs for one that has enough fields. This works because in
        // practice the field_index is used with the correct type.
        // TODO: In M23-T5, carry type info to disambiguate.
        for s in &self.module.structs {
            if field_index < s.fields.len() {
                return s.fields[field_index].0.clone();
            }
        }
        // Fallback to positional for variant fields
        format!("_{field_index}")
    }
}
