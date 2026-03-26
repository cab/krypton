use std::collections::HashMap;
use std::fmt;

use krypton_ir::{
    head_type_name, Atom, Expr, ExprKind, FnId, Literal, Module, PrimOp, SimpleExpr, StructDef,
    SumTypeDef, Type, VarId,
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

    // Build variant lookup from all modules: (type_name, tag) → variant_name
    let mut variant_lookup: HashMap<(String, u32), String> = HashMap::new();
    for ir_module in &ir_modules {
        for st in &ir_module.sum_types {
            for v in &st.variants {
                variant_lookup.insert((st.name.clone(), v.tag), v.name.clone());
            }
        }
    }

    // Build instance → source module map: (trait_local_name, target_type_name) → module_name
    let mut instance_source_modules: HashMap<(String, String), String> = HashMap::new();
    for ir_module in &ir_modules {
        for inst in &ir_module.instances {
            if !inst.is_imported && !inst.is_intrinsic {
                instance_source_modules.insert(
                    (inst.trait_name.local_name.clone(), inst.target_type_name.clone()),
                    ir_module.name.clone(),
                );
            }
        }
    }

    let mut results = Vec::new();
    for (i, ir_module) in ir_modules.iter().enumerate() {
        let is_main = i == 0;
        let mut emitter =
            JsEmitter::new(ir_module, is_main, &variant_lookup, &instance_source_modules);
        let js_source = emitter.emit();
        let filename = format!("{}.mjs", ir_module.name);
        results.push((filename, js_source));
    }

    Ok(results)
}

/// Tracks info about a recur join point for while(true) + continue emission.
struct RecurJoinInfo {
    param_names: Vec<String>,
    phase: RecurPhase,
}

#[derive(PartialEq)]
enum RecurPhase {
    Init,
    Loop,
}

/// Accumulates JavaScript source for a single IR module.
pub(crate) struct JsEmitter<'a> {
    output: String,
    indent: usize,
    module: &'a Module,
    is_main: bool,
    /// Maps VarId → JS variable name for the current function scope.
    var_names: HashMap<VarId, String>,
    /// Maps VarId → IR Type for type-directed emission (instanceof, field names).
    var_types: HashMap<VarId, &'a krypton_ir::Type>,
    /// Counter for generating unique variable names.
    var_counter: usize,
    /// Maps (sum_type_name, tag) → variant_class_name for instanceof emission.
    variant_lookup: &'a HashMap<(String, u32), String>,
    /// Active recur join points for while(true) + continue emission.
    recur_joins: HashMap<VarId, RecurJoinInfo>,
    /// Maps (trait_local_name, target_type_name) → source module name for cross-module dict imports.
    instance_source_modules: &'a HashMap<(String, String), String>,
}

impl<'a> JsEmitter<'a> {
    pub(crate) fn new(
        module: &'a Module,
        is_main: bool,
        variant_lookup: &'a HashMap<(String, u32), String>,
        instance_source_modules: &'a HashMap<(String, String), String>,
    ) -> Self {
        JsEmitter {
            output: String::new(),
            indent: 0,
            module,
            is_main,
            var_names: HashMap::new(),
            var_types: HashMap::new(),
            var_counter: 0,
            variant_lookup,
            recur_joins: HashMap::new(),
            instance_source_modules,
        }
    }

    pub(crate) fn emit(&mut self) -> String {
        self.emit_imports();
        self.emit_structs();
        self.emit_sum_types();
        self.emit_dict_instances();
        self.emit_functions();
        if self.is_main && self.module.functions.iter().any(|f| f.name == "main") {
            self.writeln("main();");
        }
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
    fn relative_import_path(&self, target_module: &str) -> String {
        let from_dir: Vec<&str> = {
            let parts: Vec<&str> = self.module.module_path.split('/').collect();
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

    /// Extract the sum type name from an IR type, if it names a known sum type.
    fn sum_type_name_from_type(&self, ty: &krypton_ir::Type) -> Option<String> {
        match ty {
            krypton_ir::Type::Named(name, _) => {
                let bare = name.rsplit('/').next().unwrap_or(name);
                if self.variant_lookup.keys().any(|(tn, _)| tn == bare) {
                    Some(bare.to_string())
                } else {
                    None
                }
            }
            krypton_ir::Type::Own(inner) => self.sum_type_name_from_type(inner),
            _ => None,
        }
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

        let mut emitted_any = false;

        // ── Krypton-to-Krypton imports ──
        let mut by_module: HashMap<&str, Vec<(&str, &str)>> = HashMap::new();
        for imp in &self.module.imported_fns {
            by_module
                .entry(&imp.source_module)
                .or_default()
                .push((&imp.original_name, &imp.name));
        }

        let mut modules: Vec<&&str> = by_module.keys().collect();
        modules.sort();
        for module_path in modules {
            let entries = by_module.get(*module_path).unwrap();
            let mut seen = HashSet::new();
            let mut specifiers: Vec<String> = Vec::new();
            for &(original, local) in entries {
                if !seen.insert((original, local)) {
                    continue;
                }
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

        // ── Extern JS imports ──
        let mut extern_by_module: HashMap<&str, Vec<&str>> = HashMap::new();
        for ext in &self.module.extern_fns {
            if let krypton_ir::ExternTarget::Js { module } = &ext.target {
                extern_by_module
                    .entry(module.as_str())
                    .or_default()
                    .push(&ext.name);
            }
        }
        let mut extern_modules: Vec<&&str> = extern_by_module.keys().collect();
        extern_modules.sort();
        for module_path in extern_modules {
            let mut names: Vec<&str> = extern_by_module[*module_path].clone();
            names.sort();
            names.dedup();
            self.writeln(&format!(
                "import {{ {} }} from '{}';",
                names.join(", "),
                module_path
            ));
            emitted_any = true;
        }

        // ── Cross-module dict imports ──
        {
            let mut dict_by_module: HashMap<String, Vec<String>> = HashMap::new();
            for inst in &self.module.instances {
                if inst.is_imported && !inst.is_intrinsic {
                    let dict_name = format!(
                        "{}$${}",
                        inst.trait_name.local_name, inst.target_type_name
                    );
                    let key = (
                        inst.trait_name.local_name.clone(),
                        inst.target_type_name.clone(),
                    );
                    if let Some(source_module) = self.instance_source_modules.get(&key) {
                        dict_by_module
                            .entry(source_module.clone())
                            .or_default()
                            .push(dict_name);
                    }
                }
            }
            let mut modules: Vec<&String> = dict_by_module.keys().collect();
            modules.sort();
            for module_path in modules {
                let mut names = dict_by_module[module_path].clone();
                names.sort();
                names.dedup();
                let rel_path = self.relative_import_path(module_path);
                self.writeln(&format!(
                    "import {{ {} }} from '{}';",
                    names.join(", "),
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
        let has_same_name_variant = st.variants.iter().any(|v| v.name == st.name);
        let single_variant_same_name = st.variants.len() == 1 && has_same_name_variant;

        if single_variant_same_name {
            // Single variant with same name as type — emit just one class.
            let variant = &st.variants[0];
            self.writeln(&format!("export class {} {{", st.name));
            self.indent += 1;
            self.writeln(&format!("get $tag() {{ return {}; }}", variant.tag));
            if variant.fields.is_empty() {
                self.writeln(&format!(
                    "static INSTANCE = new {}();",
                    variant.name
                ));
            } else {
                let params: Vec<String> =
                    (0..variant.fields.len()).map(|i| format!("_{i}")).collect();
                self.writeln(&format!("constructor({}) {{", params.join(", ")));
                self.indent += 1;
                for p in &params {
                    self.writeln(&format!("this.{p} = {p};"));
                }
                self.indent -= 1;
                self.writeln("}");
            }
            self.indent -= 1;
            self.writeln("}");
            return;
        }

        // Multi-variant: rename base if any variant shares the type name.
        let base_name = if has_same_name_variant {
            format!("{}$Base", st.name)
        } else {
            st.name.clone()
        };

        self.writeln(&format!("export class {} {{", base_name));
        self.writeln("}");
        self.write("\n");

        for variant in &st.variants {
            self.writeln(&format!(
                "export class {} extends {} {{",
                variant.name, base_name
            ));
            self.indent += 1;
            self.writeln(&format!("get $tag() {{ return {}; }}", variant.tag));
            if variant.fields.is_empty() {
                self.writeln(&format!(
                    "static INSTANCE = new {}();",
                    variant.name
                ));
            } else {
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

    // ── Dict Instances ───────────────────────────────────────

    fn dict_constant_name(
        &self,
        trait_name: &krypton_typechecker::typed_ast::TraitName,
        ty: &Type,
    ) -> String {
        let trait_local = &trait_name.local_name;
        let type_base = head_type_name(ty);
        format!("{trait_local}$${type_base}")
    }

    fn emit_dict_instances(&mut self) {
        // Emit all intrinsic dicts unconditionally (they're tiny inline constants).
        // This mirrors the JVM backend which registers all intrinsics in every module.
        for (trait_name, type_name, entries) in js_intrinsic_dicts() {
            let dict_name = format!("{trait_name}$${type_name}");
            let methods: Vec<String> = entries
                .iter()
                .map(|(method_name, body)| format!("{method_name}: {body}"))
                .collect();
            self.writeln(&format!(
                "const {dict_name} = {{ {} }};",
                methods.join(", ")
            ));
        }
        if !JS_INTRINSICS.is_empty() {
            self.write("\n");
        }

        // Emit local (non-imported, non-intrinsic) instances
        for inst in &self.module.instances {
            if inst.is_imported || inst.is_intrinsic {
                continue;
            }
            let dict_name = format!("{}$${}", inst.trait_name.local_name, inst.target_type_name);

            if inst.sub_dict_requirements.is_empty() {
                // Concrete instance — dict constant object
                let methods: Vec<String> = inst
                    .method_fn_ids
                    .iter()
                    .map(|(method_name, fn_id)| {
                        let fn_name = self.fn_name(*fn_id);
                        format!("{method_name}: {fn_name}")
                    })
                    .collect();
                self.writeln(&format!(
                    "export const {dict_name} = {{ {} }};",
                    methods.join(", ")
                ));
            } else {
                // Parameterized instance — factory function
                let dict_params: Vec<String> = inst
                    .sub_dict_requirements
                    .iter()
                    .map(|(tn, tv)| format!("dict$${}$${}", tn.local_name, tv.display_name()))
                    .collect();
                let methods: Vec<String> = inst
                    .method_fn_ids
                    .iter()
                    .map(|(method_name, fn_id)| {
                        let fn_name = self.fn_name(*fn_id);
                        format!(
                            "{method_name}: (...args) => {fn_name}({}, ...args)",
                            dict_params.join(", ")
                        )
                    })
                    .collect();
                self.writeln(&format!(
                    "export function {dict_name}({}) {{",
                    dict_params.join(", ")
                ));
                self.indent += 1;
                self.writeln(&format!("return {{ {} }};", methods.join(", ")));
                self.indent -= 1;
                self.writeln("}");
            }
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

    fn emit_function(&mut self, func: &'a krypton_ir::FnDef) {
        self.var_names.clear();
        self.var_types.clear();
        self.var_counter = 0;
        self.recur_joins.clear();

        let param_names: Vec<String> = func
            .params
            .iter()
            .map(|(var, ty)| {
                self.var_types.insert(*var, ty);
                self.bind_var(*var)
            })
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

    fn emit_expr(&mut self, expr: &'a Expr, tail: bool) {
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
                ty,
                value,
                body,
            } => {
                self.var_types.insert(*bind, ty);
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
                // Declare all variables first with `let` (enables mutual recursion).
                let mut binding_info: Vec<(String, FnId, Vec<Atom>)> = Vec::new();
                for (var, ty, fn_id, captures) in bindings {
                    self.var_types.insert(*var, ty);
                    let var_name = self.bind_var(*var);
                    self.writeln(&format!("let {var_name};"));
                    binding_info.push((var_name, *fn_id, captures.clone()));
                }
                // Then assign values.
                for (var_name, fn_id, captures) in &binding_info {
                    let fn_name = self.fn_name(*fn_id);
                    if captures.is_empty() {
                        self.writeln(&format!("{var_name} = {fn_name};"));
                    } else {
                        let caps: Vec<String> =
                            captures.iter().map(|a| self.emit_atom(a)).collect();
                        let free_count =
                            self.module.closure_free_params(*fn_id, captures.len());
                        let free_params: Vec<String> =
                            (0..free_count).map(|i| format!("a${i}")).collect();
                        self.writeln(&format!(
                            "{var_name} = ({}) => {fn_name}({}, {});",
                            free_params.join(", "),
                            caps.join(", "),
                            free_params.join(", ")
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
                if *is_recur {
                    // Recur join → while(true) + reassignment + continue.
                    let param_names: Vec<String> = params
                        .iter()
                        .map(|(v, ty)| {
                            self.var_types.insert(*v, ty);
                            let pname = self.bind_var(*v);
                            self.writeln(&format!("let {pname};"));
                            pname
                        })
                        .collect();

                    // Register join in Init phase.
                    self.recur_joins.insert(
                        *name,
                        RecurJoinInfo {
                            param_names: param_names.clone(),
                            phase: RecurPhase::Init,
                        },
                    );

                    // Emit body — the initial Jump assigns starting values.
                    self.emit_expr(body, false);

                    // Switch to Loop phase.
                    self.recur_joins.get_mut(name).unwrap().phase = RecurPhase::Loop;

                    // Emit the loop.
                    self.writeln("while (true) {");
                    self.indent += 1;
                    self.emit_expr(join_body, tail);
                    self.indent -= 1;
                    self.writeln("}");

                    self.recur_joins.remove(name);
                } else {
                    // Non-recur join → helper function.
                    let join_name = self.bind_var(*name);
                    let param_names: Vec<String> = params
                        .iter()
                        .map(|(v, ty)| {
                            self.var_types.insert(*v, ty);
                            self.bind_var(*v)
                        })
                        .collect();

                    self.writeln(&format!(
                        "function {join_name}({}) {{",
                        param_names.join(", ")
                    ));
                    self.indent += 1;
                    self.emit_expr(join_body, true);
                    self.indent -= 1;
                    self.writeln("}");
                    self.emit_expr(body, tail);
                }
            }
            ExprKind::Jump { target, args } => {
                if let Some(info) = self.recur_joins.get(target) {
                    let is_loop = info.phase == RecurPhase::Loop;
                    let param_names = info.param_names.clone();

                    // Use temp vars to avoid order-dependent overwrites.
                    let arg_strs: Vec<String> =
                        args.iter().map(|a| self.emit_atom(a)).collect();
                    let tmp_names: Vec<String> = arg_strs
                        .iter()
                        .map(|arg_str| {
                            let tmp = self.fresh_var("tmp");
                            self.writeln(&format!("const {tmp} = {arg_str};"));
                            tmp
                        })
                        .collect();
                    for (i, param_name) in param_names.iter().enumerate() {
                        self.writeln(&format!("{param_name} = {};", tmp_names[i]));
                    }
                    if is_loop {
                        self.writeln("continue;");
                    }
                } else {
                    let target_name = self.var_name(*target);
                    let arg_strs: Vec<String> =
                        args.iter().map(|a| self.emit_atom(a)).collect();
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

                // Try to resolve the sum type for instanceof emission.
                let sum_type_name = if let Atom::Var(id) = scrutinee {
                    self.var_types
                        .get(id)
                        .and_then(|ty| self.sum_type_name_from_type(ty))
                } else {
                    None
                };

                if let Some(type_name) = sum_type_name {
                    // instanceof chain
                    for (i, branch) in branches.iter().enumerate() {
                        let variant_name = self
                            .variant_lookup
                            .get(&(type_name.clone(), branch.tag))
                            .cloned()
                            .unwrap_or_else(|| format!("Tag{}", branch.tag));

                        if i == 0 {
                            self.writeln(&format!(
                                "if ({scrut} instanceof {variant_name}) {{"
                            ));
                        } else {
                            self.writeln(&format!(
                                "}} else if ({scrut} instanceof {variant_name}) {{"
                            ));
                        }
                        self.indent += 1;
                        for (j, (var, ty)) in branch.bindings.iter().enumerate() {
                            self.var_types.insert(*var, ty);
                            let var_name = self.bind_var(*var);
                            self.writeln(&format!("const {var_name} = {scrut}._{j};"));
                        }
                        self.emit_expr(&branch.body, tail);
                        self.indent -= 1;
                    }
                    if let Some(default_body) = default {
                        self.writeln("} else {");
                        self.indent += 1;
                        self.emit_expr(default_body, tail);
                        self.indent -= 1;
                    }
                    self.writeln("}");
                } else {
                    // Fallback: tag-based switch
                    self.writeln(&format!("switch ({scrut}.$tag) {{"));
                    self.indent += 1;
                    for branch in branches {
                        self.writeln(&format!("case {}: {{", branch.tag));
                        self.indent += 1;
                        for (i, (var, ty)) in branch.bindings.iter().enumerate() {
                            self.var_types.insert(*var, ty);
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
    }

    fn emit_simple_expr(&mut self, expr: &'a SimpleExpr) {
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
                    let free_count = self.module.closure_free_params(*func, captures.len());
                    let free_params: Vec<String> =
                        (0..free_count).map(|i| format!("a${i}")).collect();
                    self.write(&format!(
                        "({}) => {fn_name}({}, {})",
                        free_params.join(", "),
                        caps.join(", "),
                        free_params.join(", ")
                    ));
                }
            }
            SimpleExpr::Construct { type_name, fields } => {
                let arg_strs: Vec<String> = fields.iter().map(|a| self.emit_atom(a)).collect();
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
                let field_name = self.resolve_field_name(value, *field_index);
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
            SimpleExpr::GetDict { trait_name, ty } => {
                let dict_name = self.dict_constant_name(trait_name, ty);
                self.write(&dict_name);
            }
            SimpleExpr::MakeDict {
                trait_name,
                ty,
                sub_dicts,
            } => {
                let factory_name = self.dict_constant_name(trait_name, ty);
                let args: Vec<String> = sub_dicts.iter().map(|a| self.emit_atom(a)).collect();
                self.write(&format!("{factory_name}({})", args.join(", ")));
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
            Literal::Int(n) => format!("{n}"),
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
            // Integer arithmetic
            PrimOp::AddInt => self.write(&format!("({} + {})", a(), b())),
            PrimOp::SubInt => self.write(&format!("({} - {})", a(), b())),
            PrimOp::MulInt => self.write(&format!("({} * {})", a(), b())),
            PrimOp::DivInt => self.write(&format!("Math.trunc({} / {})", a(), b())),
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
            PrimOp::FloatToInt => self.write(&format!("Math.trunc({})", a())),
            PrimOp::IntToString => self.write(&format!("String({})", a())),
            PrimOp::FloatToString => self.write(&format!("String({})", a())),
            PrimOp::BoolToString => self.write(&format!("String({})", a())),
        }
    }

    /// Resolve a field name for a Project operation using type information.
    fn resolve_field_name(&self, value: &Atom, field_index: usize) -> String {
        // Try to look up the type from var_types.
        if let Atom::Var(id) = value {
            if let Some(ty) = self.var_types.get(id) {
                let type_name = match ty {
                    krypton_ir::Type::Named(name, _) => {
                        Some(name.rsplit('/').next().unwrap_or(name))
                    }
                    krypton_ir::Type::Own(inner) => {
                        if let krypton_ir::Type::Named(name, _) = inner.as_ref() {
                            Some(name.rsplit('/').next().unwrap_or(name))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(type_name) = type_name {
                    for s in &self.module.structs {
                        if s.name == type_name && field_index < s.fields.len() {
                            return s.fields[field_index].0.clone();
                        }
                    }
                }
            }
        }
        // Fallback: search all structs for one with enough fields.
        for s in &self.module.structs {
            if field_index < s.fields.len() {
                return s.fields[field_index].0.clone();
            }
        }
        format!("_{field_index}")
    }
}

/// Static table of intrinsic JS implementations: (trait, type, method, js_body).
/// Used by both dict emission (T7) and will be reused by inline TraitCall optimization (T6).
const JS_INTRINSICS: &[(&str, &str, &str, &str)] = &[
    // Semigroup
    ("Semigroup", "Int", "combine", "(a, b) => (a + b)"),
    ("Semigroup", "Float", "combine", "(a, b) => (a + b)"),
    ("Semigroup", "String", "combine", "(a, b) => (a + b)"),
    // Sub
    ("Sub", "Int", "sub", "(a, b) => (a - b)"),
    ("Sub", "Float", "sub", "(a, b) => (a - b)"),
    // Mul
    ("Mul", "Int", "mul", "(a, b) => (a * b)"),
    ("Mul", "Float", "mul", "(a, b) => (a * b)"),
    // Div
    ("Div", "Int", "div", "(a, b) => Math.trunc(a / b)"),
    ("Div", "Float", "div", "(a, b) => (a / b)"),
    // Neg
    ("Neg", "Int", "neg", "(a) => (-a)"),
    ("Neg", "Float", "neg", "(a) => (-a)"),
    // Eq
    ("Eq", "Int", "eq", "(a, b) => a === b"),
    ("Eq", "Float", "eq", "(a, b) => a === b"),
    ("Eq", "String", "eq", "(a, b) => a === b"),
    ("Eq", "Bool", "eq", "(a, b) => a === b"),
    // Ord
    ("Ord", "Int", "lt", "(a, b) => a < b"),
    ("Ord", "Float", "lt", "(a, b) => a < b"),
    // Show
    ("Show", "Int", "show", "(x) => String(x)"),
    ("Show", "Float", "show", "(x) => { let s = String(x); return s.includes('.') ? s : s + '.0'; }"),
    ("Show", "String", "show", "(x) => x"),
    ("Show", "Bool", "show", "(x) => String(x)"),
    // Hash
    ("Hash", "Int", "hash", "(x) => x"),
    ("Hash", "Bool", "hash", "(x) => x ? 1 : 0"),
    ("Hash", "Float", "hash", "(x) => { const buf = new ArrayBuffer(8); new Float64Array(buf)[0] = x; const view = new Int32Array(buf); return view[0] ^ view[1]; }"),
    ("Hash", "String", "hash", "(x) => { let h = 0; for (let i = 0; i < x.length; i++) { h = (Math.imul(31, h) + x.charCodeAt(i)) | 0; } return h; }"),
];

/// Lookup a single intrinsic body. Used by M23-T6 for inline TraitCall optimization.
pub fn js_intrinsic_body(trait_name: &str, type_name: &str, method_name: &str) -> Option<&'static str> {
    JS_INTRINSICS
        .iter()
        .find(|(t, ty, m, _)| *t == trait_name && *ty == type_name && *m == method_name)
        .map(|(_, _, _, body)| *body)
}

/// Group intrinsics by (trait, type) for dict emission. Returns (trait, type, [(method, body)]).
fn js_intrinsic_dicts() -> Vec<(&'static str, &'static str, Vec<(&'static str, &'static str)>)> {
    let mut map: Vec<(&str, &str, Vec<(&str, &str)>)> = Vec::new();
    for &(trait_name, type_name, method_name, body) in JS_INTRINSICS {
        if let Some(entry) = map.iter_mut().find(|(t, ty, _)| *t == trait_name && *ty == type_name) {
            entry.2.push((method_name, body));
        } else {
            map.push((trait_name, type_name, vec![(method_name, body)]));
        }
    }
    map
}
