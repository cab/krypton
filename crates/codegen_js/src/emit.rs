use std::collections::{HashMap, HashSet};
use std::fmt;

use krypton_ir::{
    bind_type_vars_many, canonical_type_name, has_type_vars, head_type_name, Atom, CanonicalRef,
    Expr, ExprKind, FnId, FnIdentity, Literal, Module, PrimOp, SimpleExpr, SimpleExprKind,
    StructDef, SumTypeDef, Type, VarId,
};
use krypton_parser::ast::Span;
use krypton_typechecker::link_context::ModuleLinkView;
use krypton_typechecker::module_interface::{ModulePath as LinkModulePath, TypeSummaryKind};
use krypton_typechecker::typed_ast::TraitName;

use crate::suspend::{analyze_suspend, SuspendSummary};

/// Concrete singleton dict: exact type lookup.
struct SingletonInstance {
    js_name: String,
    source_module: Option<String>,
}

/// Parametric dict: needs structural type matching.
struct ParametricInstance {
    js_name: String,
    /// Instance type arguments. Length 1 for single-parameter traits.
    target_types: Vec<Type>,
    /// Head key of the first position (used as a rough bucket filter).
    head_key: Option<String>,
    source_module: Option<String>,
}

struct ParametricBucket {
    wildcard: Vec<ParametricInstance>,
    by_head: HashMap<String, Vec<ParametricInstance>>,
}

/// Registry of all trait instances for dispatch resolution.
pub(crate) struct InstanceRegistry {
    /// Exact (TraitName, Vec<Type>) lookup for fully concrete instances.
    singletons: HashMap<(TraitName, Vec<Type>), SingletonInstance>,
    /// Structural matching for instances with type vars, grouped by trait.
    parametric: HashMap<TraitName, ParametricBucket>,
    /// Intrinsic dicts keyed by (trait_local_name, type_name).
    intrinsic_dict_names: HashMap<(String, String), String>,
}

impl InstanceRegistry {
    fn parametric_candidates<'a>(
        &'a self,
        trait_name: &TraitName,
        tys: &[Type],
    ) -> impl Iterator<Item = &'a ParametricInstance> {
        let head_key = tys
            .first()
            .map(|ty| head_type_name(&ty.strip_own()))
            .unwrap_or_default();
        self.parametric
            .get(trait_name)
            .into_iter()
            .flat_map(move |bucket| {
                bucket
                    .by_head
                    .get(&head_key)
                    .into_iter()
                    .flat_map(|items| items.iter())
                    .chain(bucket.wildcard.iter())
            })
    }

    /// Resolve a dict JS name for GetDict/MakeDict.
    fn resolve_js_name(&self, trait_name: &TraitName, tys: &[Type]) -> Option<&str> {
        // 1. Exact singleton lookup
        if let Some(info) = self.singletons.get(&(trait_name.clone(), tys.to_vec())) {
            return Some(&info.js_name);
        }
        // Also try with Own stripped
        let stripped: Vec<Type> = tys.iter().map(|t| t.strip_own()).collect();
        if stripped != tys {
            if let Some(info) = self.singletons.get(&(trait_name.clone(), stripped.clone())) {
                return Some(&info.js_name);
            }
        }
        // 2. Parametric structural match
        for inst in self.parametric_candidates(trait_name, tys) {
            let mut bindings = HashMap::new();
            if bind_type_vars_many(&inst.target_types, tys, &mut bindings) {
                return Some(&inst.js_name);
            }
        }
        // 3. Intrinsic fallback (single-parameter only)
        if tys.len() == 1 {
            let type_name = head_type_name(&tys[0]);
            let key = (trait_name.local_name.clone(), type_name);
            if let Some(name) = self.intrinsic_dict_names.get(&key) {
                return Some(name);
            }
        }
        None
    }

    /// Find source module for a given trait+type (for imports and reachability).
    fn find_source_module(&self, trait_name: &TraitName, tys: &[Type]) -> Option<&str> {
        if let Some(info) = self.singletons.get(&(trait_name.clone(), tys.to_vec())) {
            return info.source_module.as_deref();
        }
        let stripped: Vec<Type> = tys.iter().map(|t| t.strip_own()).collect();
        if stripped != tys {
            if let Some(info) = self.singletons.get(&(trait_name.clone(), stripped.clone())) {
                return info.source_module.as_deref();
            }
        }
        for inst in self.parametric_candidates(trait_name, tys) {
            let mut bindings = HashMap::new();
            if bind_type_vars_many(&inst.target_types, tys, &mut bindings) {
                return inst.source_module.as_deref();
            }
        }
        None
    }
}

fn parametric_head_key(ty: &Type) -> Option<String> {
    match ty {
        Type::Var(_) => None,
        Type::App(ctor, _) if matches!(ctor.as_ref(), Type::Var(_)) => None,
        _ => Some(head_type_name(ty)),
    }
}

/// Compute the JS name for a dict instance.
fn compute_dict_js_name(inst: &krypton_ir::InstanceDef) -> String {
    let any_vars = inst.target_types.iter().any(has_type_vars);
    let type_key = if any_vars {
        inst.target_types
            .iter()
            .map(canonical_type_name)
            .collect::<Vec<_>>()
            .join("$$")
    } else {
        inst.target_type_name.clone()
    };
    format!("{}$${}", inst.trait_name.local_name, type_key)
}

/// Compute the JS name for a dict instance from an `InstanceSummary`.
fn compute_dict_js_name_from_summary(
    inst: &krypton_typechecker::module_interface::InstanceSummary,
) -> String {
    let ir_types: Vec<Type> = inst.target_types.iter().cloned().map(Into::into).collect();
    let any_vars = ir_types.iter().any(has_type_vars);
    let type_key = if any_vars {
        ir_types
            .iter()
            .map(canonical_type_name)
            .collect::<Vec<_>>()
            .join("$$")
    } else {
        inst.target_type_name.clone()
    };
    format!("{}$${}", inst.trait_name.local_name, type_key)
}

/// Strip Own wrappers from a type for registry key normalization.
fn strip_own_type(ty: &Type) -> Type {
    ty.strip_own()
}

/// Convert a module path to a JS-safe slug by replacing `/` with `$`.
fn module_slug(path: &str) -> String {
    path.replace('/', "$")
}

/// Tracks allocated JS binding names across all import categories to prevent
/// duplicate bindings. When two imports want the same bare name, the second
/// gets a module-qualified mangled name.
struct BindingAllocator {
    /// All allocated JS binding names (prevents duplicates).
    allocated: HashSet<String>,
    /// (source_module, exported_name) → JS binding name.
    bindings: HashMap<(String, String), String>,
}

impl BindingAllocator {
    /// Create an allocator pre-seeded with local names that imports must not shadow.
    fn new(local_names: HashSet<String>) -> Self {
        BindingAllocator {
            allocated: local_names,
            bindings: HashMap::new(),
        }
    }

    /// Allocate a JS binding name for an imported symbol. Returns the bare name
    /// if available, otherwise a module-qualified mangled name.
    fn allocate(&mut self, source_module: &str, exported_name: &str) -> String {
        self.allocate_preferred(source_module, exported_name, &js_safe_name(exported_name))
    }

    /// Allocate a JS binding name with a preferred name (e.g. user alias).
    /// Falls back to module-qualified mangling if the preferred name collides.
    fn allocate_preferred(
        &mut self,
        source_module: &str,
        exported_name: &str,
        preferred: &str,
    ) -> String {
        if self.allocated.insert(preferred.to_string()) {
            self.bindings.insert(
                (source_module.into(), exported_name.into()),
                preferred.to_string(),
            );
            return preferred.to_string();
        }
        // preferred collides — mangle with module path
        let bare = js_safe_name(exported_name);
        let mangled = format!("{}${}", module_slug(source_module), bare);
        let final_name = if self.allocated.insert(mangled.clone()) {
            mangled
        } else {
            let mut counter = 2;
            loop {
                let candidate = format!("{}${}", mangled, counter);
                if self.allocated.insert(candidate.clone()) {
                    break candidate;
                }
                counter += 1;
            }
        };
        self.bindings.insert(
            (source_module.into(), exported_name.into()),
            final_name.clone(),
        );
        final_name
    }

    /// Look up the allocated JS binding name for a previously allocated import.
    fn resolve(&self, source_module: &str, exported_name: &str) -> &str {
        self.bindings
            .get(&(source_module.to_string(), exported_name.to_string()))
            .map(|s| s.as_str())
            .unwrap_or_else(|| {
                panic!(
                    "ICE: no binding allocated for ({}, {})",
                    source_module, exported_name
                )
            })
    }
}

/// Build an InstanceRegistry from a set of IR modules (for unit tests).
#[cfg(test)]
pub(crate) fn build_registry_for_modules(modules: &[&Module]) -> InstanceRegistry {
    let mut registry = InstanceRegistry {
        singletons: HashMap::new(),
        parametric: HashMap::new(),
        intrinsic_dict_names: HashMap::new(),
    };

    for (trait_name, type_name, _) in js_intrinsic_dicts() {
        let js_name = format!("{trait_name}$${type_name}");
        registry
            .intrinsic_dict_names
            .insert((trait_name.to_string(), type_name.to_string()), js_name);
    }

    for module in modules {
        for inst in &module.instances {
            if inst.is_intrinsic {
                continue;
            }
            let js_name = compute_dict_js_name(inst);
            let source_module = Some(module.name.clone());
            register_instance(
                &mut registry,
                js_name,
                inst.target_types.clone(),
                &inst.trait_name,
                source_module,
            );
        }
    }

    registry
}

/// Build an InstanceRegistry using the root module's `ModuleLinkView` for imported
/// instances and local IR modules for locally-defined instances.
fn build_registry_from_link_view(
    root_view: &ModuleLinkView<'_>,
    ir_modules: &[Module],
) -> InstanceRegistry {
    let mut registry = InstanceRegistry {
        singletons: HashMap::new(),
        parametric: HashMap::new(),
        intrinsic_dict_names: HashMap::new(),
    };

    // Register intrinsic dicts
    for (trait_name, type_name, _) in js_intrinsic_dicts() {
        let js_name = format!("{trait_name}$${type_name}");
        registry
            .intrinsic_dict_names
            .insert((trait_name.to_string(), type_name.to_string()), js_name);
    }

    // Local instances from IR modules
    for ir_module in ir_modules {
        for inst in &ir_module.instances {
            if inst.is_intrinsic {
                continue;
            }
            let js_name = compute_dict_js_name(inst);
            let source_module = Some(ir_module.name.clone());
            register_instance(
                &mut registry,
                js_name,
                inst.target_types.clone(),
                &inst.trait_name,
                source_module,
            );
        }
    }

    // Imported instances from link view
    let local_module_paths: HashSet<&str> =
        ir_modules.iter().map(|m| m.module_path.as_str()).collect();
    for (path, inst) in root_view.all_instances() {
        if local_module_paths.contains(path.as_str()) {
            continue;
        }
        if inst.is_intrinsic {
            continue;
        }
        let js_name = compute_dict_js_name_from_summary(inst);
        let source_module = Some(path.as_str().to_string());
        let ir_types: Vec<Type> = inst.target_types.iter().cloned().map(Into::into).collect();
        register_instance(
            &mut registry,
            js_name,
            ir_types,
            &inst.trait_name,
            source_module,
        );
    }

    registry
}

/// Register a single instance into the registry (shared helper for both IR and summary paths).
fn register_instance(
    registry: &mut InstanceRegistry,
    js_name: String,
    target_types: Vec<Type>,
    trait_name: &TraitName,
    source_module: Option<String>,
) {
    let any_vars = target_types.iter().any(has_type_vars);
    if any_vars {
        let head_key = target_types.first().and_then(parametric_head_key);
        let param_inst = ParametricInstance {
            js_name,
            head_key,
            target_types,
            source_module,
        };
        let bucket = registry
            .parametric
            .entry(trait_name.clone())
            .or_insert_with(|| ParametricBucket {
                wildcard: Vec::new(),
                by_head: HashMap::new(),
            });
        if let Some(head_key) = &param_inst.head_key {
            bucket
                .by_head
                .entry(head_key.clone())
                .or_default()
                .push(param_inst);
        } else {
            bucket.wildcard.push(param_inst);
        }
    } else {
        let stripped: Vec<Type> = target_types.iter().map(strip_own_type).collect();
        registry.singletons.insert(
            (trait_name.clone(), stripped),
            SingletonInstance {
                js_name,
                source_module,
            },
        );
    }
}

/// JS reserved words that cannot be used as identifiers.
pub(crate) const JS_RESERVED: &[&str] = &[
    "break",
    "case",
    "catch",
    "class",
    "const",
    "continue",
    "debugger",
    "default",
    "delete",
    "do",
    "else",
    "enum",
    "export",
    "extends",
    "false",
    "finally",
    "for",
    "function",
    "if",
    "import",
    "in",
    "instanceof",
    "new",
    "null",
    "return",
    "super",
    "switch",
    "this",
    "throw",
    "true",
    "try",
    "typeof",
    "var",
    "void",
    "while",
    "with",
    "yield",
    // strict mode
    "implements",
    "interface",
    "let",
    "package",
    "private",
    "protected",
    "public",
    "static",
    // other
    "await",
    "async",
];

/// Return a JS-safe version of a Krypton name: prefix with `$` if it's a reserved word.
pub(crate) fn js_safe_name(name: &str) -> String {
    if JS_RESERVED.contains(&name) {
        format!("${name}")
    } else {
        name.to_string()
    }
}

/// Errors that can occur during JS code generation.
#[derive(Debug, Clone)]
pub enum JsCodegenError {
    LowerError(String),
    UnsupportedFeature(String),
    MissingExternTarget(Vec<MissingExternTarget>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingExternTarget {
    pub function_name: String,
    pub referencing_module: String,
    pub available_targets: Vec<String>,
    pub referencing_module_source: Option<String>,
    pub is_root_module: bool,
    pub use_span: Span,
    pub declaring_module: String,
    pub declaring_module_source: Option<String>,
    pub declaration_span: Span,
}

impl fmt::Display for JsCodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            JsCodegenError::LowerError(msg) => write!(f, "IR lowering error: {msg}"),
            JsCodegenError::UnsupportedFeature(msg) => {
                write!(f, "unsupported JS feature: {msg}")
            }
            JsCodegenError::MissingExternTarget(items) => {
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(
                        f,
                        "JS codegen error: extern function `{}` referenced from module `{}` has no JS target declaration (available targets: {})",
                        item.function_name,
                        item.referencing_module,
                        item.available_targets.join(", ")
                    )?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for JsCodegenError {}

/// Compile all typed modules to JavaScript ESM (.mjs) files.
///
/// Returns `Vec<(filename, js_source)>` where filename uses `.mjs` extension.
/// Compile pre-lowered IR modules to JS. The first module is the main module;
/// the rest are library modules.
///
/// Callers must lower `TypedModule`s to IR before calling this function (e.g. via
/// `krypton_ir::lower::lower_all`). This ensures codegen never touches `TypedModule`.
pub fn compile_modules_js(
    ir_modules: &[Module],
    main_module_name: &str,
    emit_main_call: bool,
    link_ctx: &krypton_typechecker::link_context::LinkContext,
    module_sources: &HashMap<String, Option<String>>,
) -> Result<Vec<(String, String)>, JsCodegenError> {
    let root_module_path = ir_modules
        .first()
        .map(|m| m.module_path.as_str())
        .unwrap_or("");

    // Use root module's link view for global variant lookup and instance registry.
    let root_view = link_ctx
        .view_for(&LinkModulePath::new(root_module_path))
        .unwrap_or_else(|| {
            panic!(
                "ICE: no LinkContext view for root module '{}'",
                root_module_path
            )
        });

    // Build variant lookup: (type_name, tag) → variant_name
    // Local sum types come from ir_modules, imported from link view.
    let mut variant_lookup: HashMap<(String, u32), String> = HashMap::new();
    let mut qualified_sum_type_names: HashSet<String> = HashSet::new();

    // Local sum types from IR modules
    for ir_module in ir_modules {
        for st in &ir_module.sum_types {
            let qualified = format!("{}/{}", ir_module.name, st.name);
            qualified_sum_type_names.insert(qualified.clone());
            for v in &st.variants {
                let qkey = (qualified.clone(), v.tag);
                variant_lookup.insert(qkey, v.name.clone());
            }
        }
    }

    // Imported sum types from link view
    let local_module_paths: HashSet<&str> =
        ir_modules.iter().map(|m| m.module_path.as_str()).collect();
    for (path, ts) in root_view.all_exported_types() {
        if local_module_paths.contains(path.as_str()) {
            continue;
        }
        let TypeSummaryKind::Sum { variants } = &ts.kind else {
            continue;
        };
        let qualified = format!("{}/{}", path.as_str(), ts.name);
        qualified_sum_type_names.insert(qualified.clone());
        for (tag, v) in variants.iter().enumerate() {
            let tag = tag as u32;
            let qkey = (qualified.clone(), tag);
            variant_lookup.insert(qkey, v.name.clone());
        }
    }

    // Build instance registry for dict dispatch resolution.
    let registry = build_registry_from_link_view(&root_view, ir_modules);

    validate_js_extern_targets(ir_modules, &root_view, module_sources)?;

    let suspend = analyze_suspend(ir_modules);

    let mut results = Vec::new();
    for (module_index, ir_module) in ir_modules.iter().enumerate() {
        let is_main = ir_module.name == main_module_name;
        let view = link_ctx
            .view_for(&LinkModulePath::new(ir_module.module_path.as_str()))
            .unwrap_or_else(|| {
                panic!(
                    "ICE: no LinkContext view for module '{}'",
                    ir_module.module_path
                )
            });
        let mut emitter = JsEmitter::new(
            ir_module,
            is_main && emit_main_call,
            &variant_lookup,
            &qualified_sum_type_names,
            &registry,
            &view,
            module_index,
            &suspend,
        );
        let js_source = emitter.emit();
        let filename = format!("{}.mjs", ir_module.name);
        results.push((filename, js_source));
    }

    Ok(results)
}

fn validate_js_extern_targets(
    ir_modules: &[Module],
    root_view: &ModuleLinkView<'_>,
    module_sources: &HashMap<String, Option<String>>,
) -> Result<(), JsCodegenError> {
    let mut missing = Vec::new();

    for ir_module in ir_modules {
        if !root_view.is_reachable(&LinkModulePath::new(ir_module.module_path.as_str())) {
            continue;
        }
        let referenced = collect_referenced_fns(ir_module);

        // Index local extern fns by FnId.
        let local_externs_by_id: HashMap<FnId, &krypton_ir::ExternFnDef> = ir_module
            .extern_fns
            .iter()
            .filter(|ext| referenced.contains_key(&ext.id))
            .map(|ext| (ext.id, ext))
            .collect();

        for (fn_id, use_span) in &referenced {
            // Only local externs need validation — imported externs are now
            // accessed through the defining module's wrapper, not directly.
            if let Some(ext) = local_externs_by_id.get(fn_id) {
                if matches!(ext.target, krypton_ir::ExternTarget::Js { .. }) {
                    continue;
                }
                let fn_name = ir_module
                    .fn_name(*fn_id)
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| ext.name.clone());
                missing.push(MissingExternTarget {
                    function_name: fn_name,
                    referencing_module: ir_module.module_path.as_str().to_string(),
                    referencing_module_source: module_sources
                        .get(ir_module.module_path.as_str())
                        .cloned()
                        .flatten()
                        .or_else(|| module_sources.get(&ir_module.name).cloned().flatten()),
                    available_targets: vec![format_extern_target(&ext.target)],
                    is_root_module: ir_module.name == ir_modules[0].name,
                    use_span: *use_span,
                    declaring_module: ext.declaring_module_path.clone(),
                    declaring_module_source: module_sources
                        .get(&ext.declaring_module_path)
                        .cloned()
                        .flatten(),
                    declaration_span: ext.span,
                });
            }
        }
    }

    if missing.is_empty() {
        Ok(())
    } else {
        missing.sort_by(|a, b| {
            a.referencing_module
                .cmp(&b.referencing_module)
                .then(a.function_name.cmp(&b.function_name))
        });
        missing.dedup();
        Err(JsCodegenError::MissingExternTarget(missing))
    }
}

fn format_extern_target(target: &krypton_ir::ExternTarget) -> String {
    match target {
        krypton_ir::ExternTarget::Java { class } => format!("java:{class}"),
        krypton_ir::ExternTarget::Js { module } => format!("js:{module}"),
    }
}

fn collect_referenced_fns(module: &Module) -> HashMap<FnId, Span> {
    let mut ids = HashMap::new();
    for func in &module.functions {
        collect_referenced_fns_expr(&func.body, &mut ids);
    }
    ids
}

fn collect_referenced_fns_expr(expr: &Expr, ids: &mut HashMap<FnId, Span>) {
    match &expr.kind {
        ExprKind::Let { value, body, .. } => {
            collect_referenced_fns_simple(value, ids);
            collect_referenced_fns_expr(body, ids);
        }
        ExprKind::LetRec { bindings, body } => {
            for (_, _, fn_id, _) in bindings {
                ids.entry(*fn_id).or_insert(expr.span);
            }
            collect_referenced_fns_expr(body, ids);
        }
        ExprKind::LetJoin {
            join_body, body, ..
        } => {
            collect_referenced_fns_expr(join_body, ids);
            collect_referenced_fns_expr(body, ids);
        }
        ExprKind::BoolSwitch {
            true_body,
            false_body,
            ..
        } => {
            collect_referenced_fns_expr(true_body, ids);
            collect_referenced_fns_expr(false_body, ids);
        }
        ExprKind::Switch {
            branches, default, ..
        } => {
            for branch in branches {
                collect_referenced_fns_expr(&branch.body, ids);
            }
            if let Some(default) = default {
                collect_referenced_fns_expr(default, ids);
            }
        }
        ExprKind::AutoClose { body, .. } => collect_referenced_fns_expr(body, ids),
        ExprKind::Jump { .. } | ExprKind::Atom(_) => {}
    }
}

fn collect_referenced_fns_simple(expr: &SimpleExpr, ids: &mut HashMap<FnId, Span>) {
    match &expr.kind {
        SimpleExprKind::Call { func, .. } | SimpleExprKind::MakeClosure { func, .. } => {
            ids.entry(*func).or_insert(expr.span);
        }
        _ => {}
    }
}

/// Collect all `(TraitName, Type)` pairs referenced by GetDict/MakeDict in a module's functions.
/// Collects `(source_module, import_name)` pairs for all imported constructors
/// by querying the `ModuleLinkView` for exported types. This covers struct
/// names and all sum type variant names (both nullary and non-nullary),
/// ensuring they're available for construction (`new Foo(...)`,
/// `Nil.INSTANCE`) and pattern matching (`instanceof Nil`).
fn collect_constructor_imports<'a>(
    link_view: &'a ModuleLinkView<'a>,
    local_module: &str,
) -> Vec<(String, String)> {
    let mut refs = Vec::new();
    let mut seen = HashSet::new();
    for (mod_path, ts) in link_view.all_exported_types() {
        if mod_path.as_str() == local_module {
            continue;
        }
        match &ts.kind {
            TypeSummaryKind::Record { .. } => {
                let key = (mod_path.as_str().to_string(), ts.name.clone());
                if seen.insert(key.clone()) {
                    refs.push(key);
                }
            }
            TypeSummaryKind::Sum { variants } => {
                for v in variants {
                    let key = (mod_path.as_str().to_string(), v.name.clone());
                    if seen.insert(key.clone()) {
                        refs.push(key);
                    }
                }
            }
            TypeSummaryKind::Opaque => {}
        }
    }
    refs
}

fn collect_dict_refs(module: &Module) -> Vec<(TraitName, Vec<Type>)> {
    let mut refs = Vec::new();
    let mut seen = HashSet::new();
    for func in &module.functions {
        collect_dict_refs_expr(&func.body, &mut refs, &mut seen);
    }
    refs
}

fn collect_dict_refs_expr(
    expr: &Expr,
    refs: &mut Vec<(TraitName, Vec<Type>)>,
    seen: &mut HashSet<(TraitName, Vec<Type>)>,
) {
    match &expr.kind {
        ExprKind::Let { value, body, .. } => {
            collect_dict_refs_simple(value, refs, seen);
            collect_dict_refs_expr(body, refs, seen);
        }
        ExprKind::LetRec { body, .. } => {
            collect_dict_refs_expr(body, refs, seen);
        }
        ExprKind::LetJoin {
            join_body, body, ..
        } => {
            collect_dict_refs_expr(join_body, refs, seen);
            collect_dict_refs_expr(body, refs, seen);
        }
        ExprKind::BoolSwitch {
            true_body,
            false_body,
            ..
        } => {
            collect_dict_refs_expr(true_body, refs, seen);
            collect_dict_refs_expr(false_body, refs, seen);
        }
        ExprKind::Switch {
            branches, default, ..
        } => {
            for branch in branches {
                collect_dict_refs_expr(&branch.body, refs, seen);
            }
            if let Some(default) = default {
                collect_dict_refs_expr(default, refs, seen);
            }
        }
        ExprKind::AutoClose { body, .. } => collect_dict_refs_expr(body, refs, seen),
        ExprKind::Jump { .. } | ExprKind::Atom(_) => {}
    }
}

fn collect_dict_refs_simple(
    expr: &SimpleExpr,
    refs: &mut Vec<(TraitName, Vec<Type>)>,
    seen: &mut HashSet<(TraitName, Vec<Type>)>,
) {
    match &expr.kind {
        SimpleExprKind::GetDict {
            trait_name,
            target_types,
            ..
        }
        | SimpleExprKind::MakeDict {
            trait_name,
            target_types,
            ..
        } => {
            let key = (trait_name.clone(), target_types.clone());
            if seen.insert(key.clone()) {
                refs.push(key);
            }
        }
        _ => {}
    }
}

/// Tracks info about a recur join point for while(true) + continue emission.
struct RecurJoinInfo {
    param_names: Vec<String>,
    phase: RecurPhase,
}

/// Tracks a non-recur join that should be inlined (to avoid `continue` inside a nested function).
struct InlineJoinInfo<'a> {
    param_names: Vec<String>,
    join_body: &'a Expr,
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
    qualified_sum_type_names: &'a HashSet<String>,
    /// Binding allocator for collision-free JS import names.
    binding_alloc: BindingAllocator,
    /// Active recur join points for while(true) + continue emission.
    recur_joins: HashMap<VarId, RecurJoinInfo>,
    /// Non-recur joins inside a recur context that must be inlined to avoid `continue` in nested functions.
    inline_joins: HashMap<VarId, InlineJoinInfo<'a>>,
    /// Instance registry for dict dispatch resolution.
    registry: &'a InstanceRegistry,
    /// Link view for cross-module metadata lookups.
    link_view: &'a ModuleLinkView<'a>,
    /// Index of the current module in the IR module list.
    module_index: usize,
    /// Suspend analysis summary for async/await emission.
    suspend: &'a SuspendSummary,
    /// Whether the function currently being emitted is async.
    current_fn_is_async: bool,
}

impl<'a> JsEmitter<'a> {
    const NULLABLE_SOME_ALIAS: &'static str = "__krypton_nullable_Some";
    const NULLABLE_NONE_ALIAS: &'static str = "__krypton_nullable_None";

    // Emitter constructor: each arg is a borrowed input held for the lifetime
    // of emission. A builder would just forward each field, so the wide arg
    // list is intentional.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        module: &'a Module,
        is_main: bool,
        variant_lookup: &'a HashMap<(String, u32), String>,
        qualified_sum_type_names: &'a HashSet<String>,
        registry: &'a InstanceRegistry,
        link_view: &'a ModuleLinkView<'a>,
        module_index: usize,
        suspend: &'a SuspendSummary,
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
            qualified_sum_type_names,
            binding_alloc: BindingAllocator::new(HashSet::new()),
            recur_joins: HashMap::new(),
            inline_joins: HashMap::new(),
            registry,
            link_view,
            module_index,
            suspend,
            current_fn_is_async: false,
        }
    }

    /// Check if a function in the current module suspends.
    fn fn_suspends(&self, id: FnId) -> bool {
        self.suspend.fn_suspends(self.module_index, id)
    }

    pub(crate) fn emit(&mut self) -> String {
        self.emit_imports();
        self.emit_structs();
        self.emit_sum_types();
        self.emit_dict_instances();
        self.emit_nullable_extern_wrappers();
        self.emit_nonnullable_extern_wrappers();
        self.emit_functions();
        if self.is_main && self.module.functions.iter().any(|f| f.name == "main") {
            self.writeln("await runMain(main);");
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
            let parts: Vec<&str> = self.module.module_path.as_str().split('/').collect();
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

    /// Resolve an extern JS import path that is relative to the declaring module
    /// into a path relative to the current (emitting) module.
    ///
    /// For example, `core/io` declares `extern js "../extern/js/io.mjs"`.
    /// If the emitting module is `test` (at root), the resolved path is
    /// `./extern/js/io.mjs`. If the emitting module is `core/show`, the
    /// resolved path remains `../extern/js/io.mjs`.
    fn resolve_extern_js_path(&self, raw_path: &str, declaring_module: &str) -> String {
        // 1. Get the declaring module's directory segments
        let decl_parts: Vec<&str> = declaring_module.split('/').collect();
        let decl_dir = if decl_parts.len() > 1 {
            &decl_parts[..decl_parts.len() - 1]
        } else {
            &[]
        };

        // 2. Resolve the raw path (which is relative to decl_dir) into segments
        //    relative to the output root.
        let mut resolved: Vec<&str> = decl_dir.to_vec();
        for segment in raw_path.split('/') {
            match segment {
                ".." => {
                    resolved.pop();
                }
                "." | "" => {}
                s => resolved.push(s),
            }
        }
        // `resolved` is now segments relative to the output root, e.g. ["runtime", "js", "io.mjs"]

        // 3. Compute relative path from the emitting module to the resolved path.
        let emit_parts: Vec<&str> = self.module.module_path.as_str().split('/').collect();
        let emit_dir = if emit_parts.len() > 1 {
            &emit_parts[..emit_parts.len() - 1]
        } else {
            &[][..]
        };

        // Find common prefix between emit_dir and resolved directory (all but last segment)
        let resolved_dir = if resolved.len() > 1 {
            &resolved[..resolved.len() - 1]
        } else {
            &[]
        };
        let resolved_file = resolved.last().unwrap_or(&"");

        let common = emit_dir
            .iter()
            .zip(resolved_dir.iter())
            .take_while(|(a, b)| a == b)
            .count();

        let ups = emit_dir.len() - common;
        let mut path = String::new();
        if ups == 0 && resolved_dir.len() == common {
            path.push_str("./");
        } else {
            for _ in 0..ups {
                path.push_str("../");
            }
            if ups == 0 {
                path.push_str("./");
            }
        }
        for &segment in &resolved_dir[common..] {
            path.push_str(segment);
            path.push('/');
        }
        path.push_str(resolved_file);
        path
    }

    fn fn_name(&self, id: FnId) -> String {
        match self.module.fn_identities.get(&id) {
            Some(FnIdentity::Imported {
                canonical,
                local_alias: _,
            }) => {
                let source_module = canonical.module.as_str();
                let original = canonical.symbol.local_name();
                // Look up the binding allocated during import emission.
                self.binding_alloc
                    .bindings
                    .get(&(source_module.to_string(), original.clone()))
                    .cloned()
                    .unwrap_or_else(|| js_safe_name(&original))
            }
            Some(identity) => js_safe_name(identity.name()),
            None => format!("fn_{}", id.0),
        }
    }

    /// Resolve the JS binding for a type/variant reference. For imported types,
    /// consults the binding allocator; for local types, uses bare name.
    fn resolve_type_binding(&self, type_ref: &CanonicalRef, name: &str) -> String {
        let source_module = type_ref.module.as_str();
        if source_module == self.module.module_path.as_str() {
            js_safe_name(name)
        } else {
            self.binding_alloc
                .bindings
                .get(&(source_module.to_string(), name.to_string()))
                .cloned()
                .unwrap_or_else(|| js_safe_name(name))
        }
    }

    fn raw_nullable_extern_alias(name: &str) -> String {
        format!("__krypton_nullable_raw${}", js_safe_name(name))
    }

    fn raw_extern_alias(name: &str) -> String {
        format!("__krypton_raw${}", js_safe_name(name))
    }

    /// Extract the sum type name from an IR type, if it names a known sum type.
    /// Returns the qualified key used in variant_lookup (e.g. "core/option/Option").
    fn sum_type_name_from_type(&self, ty: &krypton_ir::Type) -> Option<String> {
        match ty {
            krypton_ir::Type::Named(name, _) => {
                if self.qualified_sum_type_names.contains(name) {
                    Some(name.clone())
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
        // ── 1. Collect locally-defined names to seed the allocator ──
        let mut local_names: HashSet<String> = HashSet::new();
        for f in &self.module.functions {
            local_names.insert(f.name.clone());
        }
        for ext in &self.module.extern_fns {
            if matches!(ext.target, krypton_ir::ExternTarget::Js { .. }) {
                local_names.insert(ext.name.clone());
            }
        }
        for s in &self.module.structs {
            local_names.insert(s.name.clone());
        }
        for st in &self.module.sum_types {
            local_names.insert(st.name.clone());
            for v in &st.variants {
                local_names.insert(v.name.clone());
            }
        }
        // Reserve fixed runtime names
        local_names.insert("KryptonPanic".to_string());
        local_names.insert("runMain".to_string());
        local_names.insert(Self::NULLABLE_SOME_ALIAS.to_string());
        local_names.insert(Self::NULLABLE_NONE_ALIAS.to_string());

        self.binding_alloc = BindingAllocator::new(local_names);

        // ── 2. Gather all import entries for allocation ──

        // 2a. Krypton function imports (sorted by source_module, then original_name)
        let mut fn_imports: Vec<(&str, &str, &str)> = Vec::new(); // (source_module, original, local_alias)
        for imp in &self.module.imported_fns {
            fn_imports.push((&imp.source_module, &imp.original_name, &imp.name));
        }
        fn_imports.sort_by(|a, b| a.0.cmp(b.0).then(a.1.cmp(b.1)));
        fn_imports.dedup();

        // 2b. Constructor imports (sorted by source_module, then name)
        let ctor_refs =
            collect_constructor_imports(self.link_view, self.module.module_path.as_str());
        let mut ctor_imports: Vec<(&str, &str)> = ctor_refs
            .iter()
            .map(|(m, n)| (m.as_str(), n.as_str()))
            .collect();
        ctor_imports.sort();
        ctor_imports.dedup();

        // 2c. Dict imports (sorted by source_module, then dict_name)
        let dict_refs = collect_dict_refs(self.module);
        let mut dict_imports: Vec<(String, String)> = Vec::new(); // (source_module, dict_js_name)
        for (trait_name, target_types) in &dict_refs {
            let js_name = self.resolve_dict_js_name(trait_name, target_types);
            if let Some(source) = self.registry.find_source_module(trait_name, target_types) {
                if source == self.module.name || source == self.module.module_path.as_str() {
                    continue;
                }
                let is_local = self.module.instances.iter().any(|inst| {
                    self.resolve_dict_js_name(&inst.trait_name, &inst.target_types) == js_name
                });
                if is_local {
                    continue;
                }
                dict_imports.push((source.to_string(), js_name));
            }
        }
        dict_imports.sort();
        dict_imports.dedup();

        // ── 3. Allocate bindings in deterministic order ──

        // 3a. Function imports — use user alias as preferred name when present
        for &(source_module, original, local_alias) in &fn_imports {
            let preferred = js_safe_name(local_alias);
            self.binding_alloc
                .allocate_preferred(source_module, original, &preferred);
        }

        // 3b. Constructor imports
        for &(source_module, name) in &ctor_imports {
            // Skip if already allocated by fn imports
            if self
                .binding_alloc
                .bindings
                .contains_key(&(source_module.to_string(), name.to_string()))
            {
                continue;
            }
            self.binding_alloc.allocate(source_module, name);
        }

        // 3c. Dict imports
        for (source_module, dict_name) in &dict_imports {
            self.binding_alloc.allocate(source_module, dict_name);
        }

        // ── 4. Emit import statements ──

        // 4a. Krypton function + constructor imports grouped by module
        {
            let mut by_module: HashMap<&str, Vec<(String, String)>> = HashMap::new(); // module → [(original, binding)]
            for &(source_module, original, _) in &fn_imports {
                let binding = self
                    .binding_alloc
                    .resolve(source_module, original)
                    .to_string();
                by_module
                    .entry(source_module)
                    .or_default()
                    .push((js_safe_name(original), binding));
            }
            for &(source_module, name) in &ctor_imports {
                let binding = self.binding_alloc.resolve(source_module, name).to_string();
                by_module
                    .entry(source_module)
                    .or_default()
                    .push((js_safe_name(name), binding));
            }

            let mut modules: Vec<&&str> = by_module.keys().collect();
            modules.sort();
            for module_path in modules {
                let entries = by_module.get(*module_path).unwrap();
                let mut specifiers: Vec<String> = Vec::new();
                let mut seen = HashSet::new();
                for (original, binding) in entries {
                    if !seen.insert((original.clone(), binding.clone())) {
                        continue;
                    }
                    if original == binding {
                        specifiers.push(original.clone());
                    } else {
                        specifiers.push(format!("{original} as {binding}"));
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
                }
            }
        }

        // 4b. Extern JS imports (keep existing __krypton_raw$ scheme — already namespaced)
        let mut extern_by_resolved: HashMap<String, Vec<String>> = HashMap::new();
        for ext in &self.module.extern_fns {
            if let krypton_ir::ExternTarget::Js { module } = &ext.target {
                let resolved = self.resolve_extern_js_path(module, &ext.declaring_module_path);
                let specifier = if ext.nullable {
                    format!(
                        "{} as {}",
                        js_safe_name(&ext.name),
                        Self::raw_nullable_extern_alias(&ext.name)
                    )
                } else {
                    format!(
                        "{} as {}",
                        js_safe_name(&ext.name),
                        Self::raw_extern_alias(&ext.name)
                    )
                };
                extern_by_resolved
                    .entry(resolved)
                    .or_default()
                    .push(specifier);
            }
        }
        let mut extern_modules: Vec<&String> = extern_by_resolved.keys().collect();
        extern_modules.sort();
        for resolved_path in extern_modules {
            let mut names = extern_by_resolved[resolved_path].clone();
            names.sort();
            names.dedup();
            self.writeln(&format!(
                "import {{ {} }} from '{}';",
                names.join(", "),
                resolved_path
            ));
        }

        // 4c. Nullable extern Option imports
        if self
            .module
            .extern_fns
            .iter()
            .any(|ext| ext.nullable && matches!(ext.target, krypton_ir::ExternTarget::Js { .. }))
        {
            let rel_path = self.relative_import_path("core/option");
            self.writeln(&format!(
                "import {{ Some as {}, None as {} }} from '{}';",
                Self::NULLABLE_SOME_ALIAS,
                Self::NULLABLE_NONE_ALIAS,
                rel_path
            ));
        }

        // 4d. Cross-module dict imports
        {
            let mut dict_by_module: HashMap<&str, Vec<String>> = HashMap::new();
            for (source_module, dict_name) in &dict_imports {
                let binding = self
                    .binding_alloc
                    .resolve(source_module, dict_name)
                    .to_string();
                let original = js_safe_name(dict_name);
                let specifier = if original == binding {
                    original
                } else {
                    format!("{original} as {binding}")
                };
                dict_by_module
                    .entry(source_module.as_str())
                    .or_default()
                    .push(specifier);
            }
            let mut modules: Vec<&&str> = dict_by_module.keys().collect();
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
            }
        }

        // 4e. Runtime imports
        {
            let runtime_path = self.runtime_import_path("panic.mjs");
            self.writeln(&format!(
                "import {{ KryptonPanic }} from '{}';",
                runtime_path
            ));
        }

        if self.is_main && self.module.functions.iter().any(|f| f.name == "main") {
            let runtime_path = self.runtime_import_path("actor.mjs");
            self.writeln(&format!("import {{ runMain }} from '{}';", runtime_path));
        }

        self.write("\n");
    }

    /// Compute the relative path from this module to a runtime JS file.
    fn runtime_import_path(&self, filename: &str) -> String {
        let parts: Vec<&str> = self.module.module_path.as_str().split('/').collect();
        let depth = if parts.len() > 1 { parts.len() - 1 } else { 0 };
        let mut path = String::new();
        if depth == 0 {
            path.push_str("./");
        } else {
            for _ in 0..depth {
                path.push_str("../");
            }
        }
        path.push_str("extern/js/");
        path.push_str(filename);
        path
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
                self.writeln(&format!("static INSTANCE = new {}();", variant.name));
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
                self.writeln(&format!("static INSTANCE = new {}();", variant.name));
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

    fn resolve_dict_js_name(&self, trait_name: &TraitName, tys: &[Type]) -> String {
        if let Some(name) = self.registry.resolve_js_name(trait_name, tys) {
            return name.to_string();
        }
        let tys_fmt = tys
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        panic!(
            "ICE: unresolved JS dict lookup for trait `{}` and types `[{}]` in module `{}`",
            trait_name, tys_fmt, self.module.name
        )
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

            let dict_name = self.resolve_dict_js_name(&inst.trait_name, &inst.target_types);

            if inst.sub_dict_requirements.is_empty() {
                // Constant dict object (singleton or parametric without sub-dicts).
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
                    .map(|(tn, tvs)| {
                        let joined = tvs
                            .iter()
                            .map(|v| v.display_name())
                            .collect::<Vec<_>>()
                            .join("$");
                        format!("dict$${}$${}", tn.local_name, joined)
                    })
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

    fn emit_nullable_extern_wrappers(&mut self) {
        for ext in &self.module.extern_fns {
            if ext.nullable && matches!(ext.target, krypton_ir::ExternTarget::Js { .. }) {
                self.emit_nullable_extern_wrapper(ext);
                self.write("\n");
            }
        }
    }

    fn emit_nonnullable_extern_wrappers(&mut self) {
        for ext in &self.module.extern_fns {
            if !ext.nullable && matches!(ext.target, krypton_ir::ExternTarget::Js { .. }) {
                self.emit_nonnullable_extern_wrapper(ext);
                self.write("\n");
            }
        }
    }

    fn emit_nonnullable_extern_wrapper(&mut self, ext: &krypton_ir::ExternFnDef) {
        let dict_count = self
            .module
            .fn_dict_requirements
            .get(&ext.name)
            .map(|r| r.len())
            .unwrap_or(0);
        let dict_params: Vec<String> = (0..dict_count).map(|i| format!("dict{i}")).collect();
        let user_params: Vec<String> = (0..ext.param_types.len())
            .map(|i| format!("arg{i}"))
            .collect();
        let all_params: Vec<String> = dict_params
            .iter()
            .chain(user_params.iter())
            .cloned()
            .collect();
        let wrapper_args = all_params.join(", ");
        // Raw call: user params first, dicts appended
        let raw_args: Vec<String> = user_params
            .iter()
            .chain(dict_params.iter())
            .cloned()
            .collect();
        let raw_call_args = raw_args.join(", ");
        let is_async = self.fn_suspends(ext.id);
        let async_prefix = if is_async { "async " } else { "" };
        let await_prefix = if is_async { "await " } else { "" };

        self.writeln(&format!(
            "export {async_prefix}function {}({}) {{",
            js_safe_name(&ext.name),
            wrapper_args
        ));
        self.indent += 1;
        self.writeln(&format!(
            "return {await_prefix}{}({});",
            Self::raw_extern_alias(&ext.name),
            raw_call_args
        ));
        self.indent -= 1;
        self.writeln("}");
    }

    fn emit_nullable_extern_wrapper(&mut self, ext: &krypton_ir::ExternFnDef) {
        let dict_count = self
            .module
            .fn_dict_requirements
            .get(&ext.name)
            .map(|r| r.len())
            .unwrap_or(0);
        let dict_params: Vec<String> = (0..dict_count).map(|i| format!("dict{i}")).collect();
        let user_params: Vec<String> = (0..ext.param_types.len())
            .map(|i| format!("arg{i}"))
            .collect();
        let all_params: Vec<String> = dict_params
            .iter()
            .chain(user_params.iter())
            .cloned()
            .collect();
        let wrapper_args = all_params.join(", ");
        // Raw call: user params first, dicts appended
        let raw_args: Vec<String> = user_params
            .iter()
            .chain(dict_params.iter())
            .cloned()
            .collect();
        let raw_call_args = raw_args.join(", ");
        let is_async = self.fn_suspends(ext.id);
        let async_prefix = if is_async { "async " } else { "" };
        let await_prefix = if is_async { "await " } else { "" };

        self.writeln(&format!(
            "export {async_prefix}function {}({}) {{",
            js_safe_name(&ext.name),
            wrapper_args
        ));
        self.indent += 1;
        self.writeln(&format!(
            "const value = {await_prefix}{}({});",
            Self::raw_nullable_extern_alias(&ext.name),
            raw_call_args
        ));
        self.writeln(&format!(
            "return value == null ? {}.INSTANCE : new {}(value);",
            Self::NULLABLE_NONE_ALIAS,
            Self::NULLABLE_SOME_ALIAS
        ));
        self.indent -= 1;
        self.writeln("}");
    }

    fn emit_function(&mut self, func: &'a krypton_ir::FnDef) {
        self.var_names.clear();
        self.var_types.clear();
        self.var_counter = 0;
        self.recur_joins.clear();
        self.inline_joins.clear();

        let is_async = self.fn_suspends(func.id);
        self.current_fn_is_async = is_async;

        let param_names: Vec<String> = func
            .params
            .iter()
            .map(|(var, ty)| {
                self.var_types.insert(*var, ty);
                self.bind_var(*var)
            })
            .collect();

        let async_prefix = if is_async { "async " } else { "" };
        self.writeln(&format!(
            "export {async_prefix}function {}({}) {{",
            js_safe_name(&func.name),
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
            ExprKind::LetRec { bindings, body, .. } => {
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
                        let free_count = self.module.closure_free_params(*fn_id, captures.len());
                        let free_params: Vec<String> =
                            (0..free_count).map(|i| format!("a${i}")).collect();
                        if self.fn_suspends(*fn_id) {
                            self.writeln(&format!(
                                "{var_name} = async ({}) => await {fn_name}({}, {});",
                                free_params.join(", "),
                                caps.join(", "),
                                free_params.join(", ")
                            ));
                        } else {
                            self.writeln(&format!(
                                "{var_name} = ({}) => {fn_name}({}, {});",
                                free_params.join(", "),
                                caps.join(", "),
                                free_params.join(", ")
                            ));
                        }
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
                } else if !self.recur_joins.is_empty() {
                    // Non-recur join inside a recur context — inline to avoid
                    // `continue` landing inside a nested function.
                    let param_names: Vec<String> = params
                        .iter()
                        .map(|(v, ty)| {
                            self.var_types.insert(*v, ty);
                            let pname = self.bind_var(*v);
                            self.writeln(&format!("let {pname};"));
                            pname
                        })
                        .collect();

                    self.inline_joins.insert(
                        *name,
                        InlineJoinInfo {
                            param_names,
                            join_body,
                        },
                    );
                    self.emit_expr(body, tail);
                    self.inline_joins.remove(name);
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

                    let async_prefix = if self.current_fn_is_async {
                        "async "
                    } else {
                        ""
                    };
                    self.writeln(&format!(
                        "{async_prefix}function {join_name}({}) {{",
                        param_names.join(", ")
                    ));
                    self.indent += 1;
                    self.emit_expr(join_body, true);
                    self.indent -= 1;
                    self.writeln("}");
                    self.emit_expr(body, tail);
                }
            }
            ExprKind::AutoClose {
                resource,
                dict,
                type_name: _,
                null_slot: _,
                body,
            } => {
                // JS has no fn-wide exception handler so `null_slot` is meaningless.
                // Emit the Disposable.dispose trait call directly, then fall through
                // to `body`. Dict resolution has been pre-inlined as outer Lets.
                let dict_str = self.emit_atom(dict);
                let res_str = self.var_name(*resource);
                self.write_indent();
                self.write(&format!("{dict_str}.dispose({res_str});\n"));
                self.emit_expr(body, tail);
            }
            ExprKind::Jump { target, args } => {
                if let Some(info) = self.recur_joins.get(target) {
                    let is_loop = info.phase == RecurPhase::Loop;
                    let param_names = info.param_names.clone();

                    // Use temp vars to avoid order-dependent overwrites.
                    let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
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
                } else if let Some(info) = self.inline_joins.remove(target) {
                    // Inline join: assign params and emit body directly.
                    let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                    for (i, param_name) in info.param_names.iter().enumerate() {
                        self.writeln(&format!("{param_name} = {};", arg_strs[i]));
                    }
                    // Re-insert before emitting body (body may contain further jumps to same join).
                    let join_body = info.join_body;
                    self.inline_joins.insert(
                        *target,
                        InlineJoinInfo {
                            param_names: info.param_names,
                            join_body,
                        },
                    );
                    self.emit_expr(join_body, tail);
                } else {
                    let target_name = self.var_name(*target);
                    let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                    let await_prefix = if self.current_fn_is_async {
                        "await "
                    } else {
                        ""
                    };
                    if tail {
                        self.writeln(&format!(
                            "return {await_prefix}{target_name}({});",
                            arg_strs.join(", ")
                        ));
                    } else {
                        self.writeln(&format!(
                            "{await_prefix}{target_name}({});",
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
                    // Derive source module from qualified type name (e.g. "core/option/Option" → "core/option")
                    let source_module = type_name.rsplit_once('/').map(|(m, _)| m);

                    for (i, branch) in branches.iter().enumerate() {
                        let bare_variant_name = self
                            .variant_lookup
                            .get(&(type_name.clone(), branch.tag))
                            .cloned()
                            .unwrap_or_else(|| {
                                panic!(
                                    "ICE: variant name not found for ({}, tag={})",
                                    type_name, branch.tag
                                )
                            });

                        // Resolve through binding allocator for imported variants
                        let variant_name = if let Some(src_mod) = source_module {
                            if src_mod == self.module.module_path.as_str() {
                                bare_variant_name.clone()
                            } else {
                                self.binding_alloc
                                    .bindings
                                    .get(&(src_mod.to_string(), bare_variant_name.clone()))
                                    .cloned()
                                    .unwrap_or(bare_variant_name)
                            }
                        } else {
                            bare_variant_name
                        };

                        if i == 0 {
                            self.writeln(&format!("if ({scrut} instanceof {variant_name}) {{"));
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
                    // Fallback: $tag-based switching when the concrete sum type
                    // name is unavailable (e.g. generic type variables in nested
                    // pattern matches). Semantically equivalent to instanceof.
                    for (i, branch) in branches.iter().enumerate() {
                        if i == 0 {
                            self.writeln(&format!("if ({scrut}.$tag === {}) {{", branch.tag));
                        } else {
                            self.writeln(&format!(
                                "}} else if ({scrut}.$tag === {}) {{",
                                branch.tag
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
                }
            }
        }
    }

    fn emit_simple_expr(&mut self, expr: &'a SimpleExpr) {
        match &expr.kind {
            SimpleExprKind::Atom(atom) => {
                self.write(&self.emit_atom(atom));
            }
            SimpleExprKind::PrimOp { op, args } => {
                self.emit_prim_op(*op, args);
            }
            SimpleExprKind::Call { func, args } => {
                let fn_name = self.fn_name(*func);
                let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                if fn_name == "panic" || fn_name == "todo" || fn_name == "unreachable" {
                    self.write(&format!(
                        "(() => {{ throw new KryptonPanic({}); }})()",
                        arg_strs.join(", ")
                    ));
                } else {
                    let await_prefix = if self.current_fn_is_async && self.fn_suspends(*func) {
                        "await "
                    } else {
                        ""
                    };
                    self.write(&format!("{await_prefix}{fn_name}({})", arg_strs.join(", ")));
                }
            }
            SimpleExprKind::CallClosure { closure, args } => {
                let closure_str = self.emit_atom(closure);
                let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                let await_prefix = if self.current_fn_is_async {
                    "await "
                } else {
                    ""
                };
                self.write(&format!(
                    "{await_prefix}{closure_str}({})",
                    arg_strs.join(", ")
                ));
            }
            SimpleExprKind::MakeClosure { func, captures } => {
                let fn_name = self.fn_name(*func);
                if captures.is_empty() {
                    self.write(&fn_name);
                } else {
                    let caps: Vec<String> = captures.iter().map(|a| self.emit_atom(a)).collect();
                    let free_count = self.module.closure_free_params(*func, captures.len());
                    let free_params: Vec<String> =
                        (0..free_count).map(|i| format!("a${i}")).collect();
                    if self.fn_suspends(*func) {
                        self.write(&format!(
                            "async ({}) => await {fn_name}({}, {})",
                            free_params.join(", "),
                            caps.join(", "),
                            free_params.join(", ")
                        ));
                    } else {
                        self.write(&format!(
                            "({}) => {fn_name}({}, {})",
                            free_params.join(", "),
                            caps.join(", "),
                            free_params.join(", ")
                        ));
                    }
                }
            }
            SimpleExprKind::Construct { type_ref, fields } => {
                let arg_strs: Vec<String> = fields.iter().map(|a| self.emit_atom(a)).collect();
                let name = self.resolve_type_binding(type_ref, &type_ref.symbol.local_name());
                self.write(&format!("new {name}({})", arg_strs.join(", ")));
            }
            SimpleExprKind::ConstructVariant {
                type_ref,
                variant,
                fields,
                ..
            } => {
                let name = self.resolve_type_binding(type_ref, variant);
                if fields.is_empty() {
                    self.write(&format!("{name}.INSTANCE"));
                } else {
                    let arg_strs: Vec<String> = fields.iter().map(|a| self.emit_atom(a)).collect();
                    self.write(&format!("new {name}({})", arg_strs.join(", ")));
                }
            }
            SimpleExprKind::Project { value, field_index } => {
                let val = self.emit_atom(value);
                let field_name = self.resolve_field_name(value, *field_index);
                self.write(&format!("{val}.{field_name}"));
            }
            SimpleExprKind::Tag { value } => {
                let val = self.emit_atom(value);
                self.write(&format!("{val}.$tag"));
            }
            SimpleExprKind::MakeTuple { elements } => {
                let elems: Vec<String> = elements.iter().map(|a| self.emit_atom(a)).collect();
                self.write(&format!("[{}]", elems.join(", ")));
            }
            SimpleExprKind::TupleProject { value, index } => {
                let val = self.emit_atom(value);
                self.write(&format!("{val}[{index}]"));
            }
            SimpleExprKind::TraitCall {
                trait_name,
                method_name,
                args,
            } => {
                let arg_strs: Vec<String> = args.iter().map(|a| self.emit_atom(a)).collect();
                if arg_strs.is_empty() {
                    self.write(&format!("/* trait call {method_name} */ undefined"));
                } else {
                    // Try intrinsic inline: look up concrete type from dict var
                    let inlined = if let Some(Atom::Var(dict_var)) = args.first() {
                        if let Some(Type::Dict { target_types, .. }) = self.var_types.get(dict_var)
                        {
                            // Intrinsic lookup uses the first dispatch position's
                            // head type as the key; this matches the single-arg
                            // intrinsic table (e.g. `Show$Int`). Multi-arg
                            // intrinsics are not currently expressible.
                            target_types.first().and_then(|t| {
                                js_intrinsic_body(
                                    &trait_name.local_name,
                                    &head_type_name(t),
                                    method_name,
                                )
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    if let Some(body) = inlined {
                        let user_args = &arg_strs[1..];
                        self.write(&format!("({body})({})", user_args.join(", ")));
                    } else {
                        let dict = &arg_strs[0];
                        let user_args = &arg_strs[1..];
                        let await_prefix = if self.current_fn_is_async {
                            "await "
                        } else {
                            ""
                        };
                        self.write(&format!(
                            "{await_prefix}{dict}.{method_name}({})",
                            user_args.join(", ")
                        ));
                    }
                }
            }
            SimpleExprKind::GetDict {
                trait_name,
                target_types,
                ..
            } => {
                let dict_name = self.resolve_dict_js_name(trait_name, target_types);
                self.write(&dict_name);
            }
            SimpleExprKind::MakeDict {
                trait_name,
                target_types,
                sub_dicts,
                ..
            } => {
                let factory_name = self.resolve_dict_js_name(trait_name, target_types);
                let args: Vec<String> = sub_dicts.iter().map(|a| self.emit_atom(a)).collect();
                self.write(&format!("{factory_name}({})", args.join(", ")));
            }
            SimpleExprKind::MakeVec { elements, .. } => {
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
            Literal::Int(n) => {
                if *n > 9007199254740991 || *n < -9007199254740991 {
                    panic!(
                        "integer literal {} exceeds JavaScript safe integer range (±2^53-1)",
                        n
                    );
                }
                format!("{n}")
            }
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
                let named = match ty {
                    krypton_ir::Type::Named(name, _) => Some(name.as_str()),
                    krypton_ir::Type::Own(inner) => match inner.as_ref() {
                        krypton_ir::Type::Named(name, _) => Some(name.as_str()),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(named) = named {
                    if let Some((module_path, type_name)) = named.rsplit_once('/') {
                        // Qualified name: look up from link view
                        let link_path = LinkModulePath::new(module_path);
                        if let Some(ts) = self.link_view.lookup_type_summary(&link_path, type_name)
                        {
                            if let TypeSummaryKind::Record { fields } = &ts.kind {
                                if field_index < fields.len() {
                                    return fields[field_index].0.clone();
                                }
                            }
                        }
                    } else {
                        // Bare name: try local structs first
                        for s in &self.module.structs {
                            if s.name == named && field_index < s.fields.len() {
                                return s.fields[field_index].0.clone();
                            }
                        }
                        // Then try imported types from link view
                        let matches: Vec<_> = self
                            .link_view
                            .all_exported_types()
                            .into_iter()
                            .filter(|(path, ts)| {
                                path.as_str() != self.module.module_path.as_str()
                                    && ts.name == named
                                    && matches!(ts.kind, TypeSummaryKind::Record { .. })
                            })
                            .collect();
                        if matches.len() == 1 {
                            if let TypeSummaryKind::Record { fields } = &matches[0].1.kind {
                                if field_index < fields.len() {
                                    return fields[field_index].0.clone();
                                }
                            }
                        }
                    }
                }
            }
        }
        panic!(
            "ICE: resolve_field_name: no type info for {:?} (field index {}) in module '{}'",
            value, field_index, self.module.name
        )
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

/// Lookup a single intrinsic body. Used for inline TraitCall optimization.
pub fn js_intrinsic_body(
    trait_name: &str,
    type_name: &str,
    method_name: &str,
) -> Option<&'static str> {
    JS_INTRINSICS
        .iter()
        .find(|(t, ty, m, _)| *t == trait_name && *ty == type_name && *m == method_name)
        .map(|(_, _, _, body)| *body)
}

/// (trait_name, type_name, methods) entry from `js_intrinsic_dicts`, where each
/// method is `(method_name, js_body)`.
type JsIntrinsicDict = (
    &'static str,
    &'static str,
    Vec<(&'static str, &'static str)>,
);

/// Group intrinsics by (trait, type) for dict emission. Returns (trait, type, [(method, body)]).
fn js_intrinsic_dicts() -> Vec<JsIntrinsicDict> {
    let mut map: Vec<JsIntrinsicDict> = Vec::new();
    for &(trait_name, type_name, method_name, body) in JS_INTRINSICS {
        if let Some(entry) = map
            .iter_mut()
            .find(|(t, ty, _)| *t == trait_name && *ty == type_name)
        {
            entry.2.push((method_name, body));
        } else {
            map.push((trait_name, type_name, vec![(method_name, body)]));
        }
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use krypton_ir::lower::lower_all;
    use krypton_ir::{
        ExternCallKind, ExternFnDef, ExternTarget, FnDef, ImportedFnDef, Module, ModulePath,
    };
    use krypton_modules::module_resolver::CompositeResolver;
    use krypton_parser::parser::parse;
    use krypton_typechecker::infer::infer_module;
    use krypton_typechecker::link_context::LinkContext;
    use krypton_typechecker::module_interface::ModuleInterface;
    use std::collections::{BTreeSet, HashMap, HashSet};

    fn expr(ty: Type, kind: ExprKind) -> Expr {
        Expr::new((0, 0), ty, kind)
    }

    fn simple(kind: SimpleExprKind) -> SimpleExpr {
        SimpleExpr::new((0, 0), kind)
    }

    fn test_module(name: &str) -> Module {
        Module {
            name: name.to_string(),
            structs: vec![],
            sum_types: vec![],
            functions: vec![],
            fn_identities: HashMap::new(),
            extern_fns: vec![],
            extern_types: vec![],
            extern_traits: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: BTreeSet::new(),
            module_path: ModulePath::new(name),
            fn_dict_requirements: HashMap::new(),
            fn_exit_closes: HashMap::new(),
        }
    }

    fn test_link_ctx(module_path: &str) -> LinkContext {
        let iface = ModuleInterface {
            module_path: LinkModulePath::new(module_path),
            direct_deps: vec![],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        };
        LinkContext::build(vec![iface])
    }

    fn emit_test_module(module: &Module) -> String {
        let registry = build_registry_for_modules(&[module]);
        let variant_lookup = HashMap::new();
        let qualified_sum_type_names = HashSet::new();
        let suspend = SuspendSummary::empty();
        let link_ctx = test_link_ctx(module.module_path.as_str());
        let view = link_ctx
            .view_for(&LinkModulePath::new(module.module_path.as_str()))
            .unwrap();
        let mut emitter = JsEmitter::new(
            module,
            false,
            &variant_lookup,
            &qualified_sum_type_names,
            &registry,
            &view,
            0,
            &suspend,
        );
        emitter.emit()
    }

    fn emit_lowered_source_module(source: &str, module_name: &str) -> String {
        let (parsed, errors) = parse(source);
        assert!(errors.is_empty(), "parse errors: {errors:?}");

        let (typed_modules, interfaces) = infer_module(
            &parsed,
            &CompositeResolver::stdlib_only(),
            module_name.to_string(),
            krypton_parser::ast::CompileTarget::Js,
        )
        .expect("type check should succeed");
        let link_ctx = LinkContext::build(interfaces);
        let (ir_modules, _) =
            lower_all(&typed_modules, module_name, &link_ctx).expect("lowering should succeed");
        let module = ir_modules
            .into_iter()
            .find(|m| m.name == module_name)
            .expect("root IR module should exist");

        let registry = build_registry_for_modules(&[&module]);
        let variant_lookup = HashMap::new();
        let qualified_sum_type_names = HashSet::new();
        let suspend = SuspendSummary::empty();
        let view = link_ctx
            .view_for(&LinkModulePath::new(module_name))
            .unwrap();
        let mut emitter = JsEmitter::new(
            &module,
            false,
            &variant_lookup,
            &qualified_sum_type_names,
            &registry,
            &view,
            0,
            &suspend,
        );
        emitter.emit()
    }

    #[test]
    fn local_nullable_js_extern_emits_wrapper_and_raw_alias_import() {
        let mut module = test_module("test");
        module.extern_fns.push(ExternFnDef {
            id: FnId(1),
            name: "parse_int".to_string(),
            declaring_module_path: "test".to_string(),
            span: (0, 0),
            target: ExternTarget::Js {
                module: "./extern/js/string.mjs".to_string(),
            },
            nullable: true,
            throws: false,
            call_kind: ExternCallKind::Static,
            param_types: vec![Type::String],
            return_type: Type::Named("Option".to_string(), vec![Type::Int]),
            bridge_params: vec![],
        });

        let output = emit_test_module(&module);
        assert!(output.contains(
            "import { parse_int as __krypton_nullable_raw$parse_int } from './extern/js/string.mjs';"
        ));
        assert!(output.contains(
            "import { Some as __krypton_nullable_Some, None as __krypton_nullable_None } from './core/option.mjs';"
        ));
        assert!(output.contains("export function parse_int(arg0) {"));
        assert!(output.contains(
            "return value == null ? __krypton_nullable_None.INSTANCE : new __krypton_nullable_Some(value);"
        ));
    }

    #[test]
    fn imported_nullable_js_extern_uses_module_import_not_raw_extern_import() {
        let mut module = test_module("app/main");
        module.imported_fns.push(ImportedFnDef {
            id: FnId(2),
            name: "parse_int".to_string(),
            source_module: "stringlib".to_string(),
            original_name: "parse_int".to_string(),
            param_types: vec![Type::String],
            return_type: Type::Named("Option".to_string(), vec![Type::Int]),
        });

        // Build a LinkContext — the defining module wraps its externs,
        // so the consumer just imports via normal Krypton module path.
        let stringlib_iface = ModuleInterface {
            module_path: LinkModulePath::new("stringlib"),
            direct_deps: vec![],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        };
        let main_iface = ModuleInterface {
            module_path: LinkModulePath::new("app/main"),
            direct_deps: vec![LinkModulePath::new("stringlib")],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        };
        let link_ctx = LinkContext::build(vec![main_iface, stringlib_iface]);
        let view = link_ctx.view_for(&LinkModulePath::new("app/main")).unwrap();

        let registry = build_registry_for_modules(&[&module]);
        let variant_lookup = HashMap::new();
        let qualified_sum_type_names = HashSet::new();
        let suspend = SuspendSummary::empty();
        let mut emitter = JsEmitter::new(
            &module,
            false,
            &variant_lookup,
            &qualified_sum_type_names,
            &registry,
            &view,
            0,
            &suspend,
        );
        let output = emitter.emit();
        assert!(output.contains("import { parse_int } from '../stringlib.mjs';"));
        assert!(!output.contains("extern/js/string.mjs"));
    }

    #[test]
    fn non_nullable_js_extern_gets_raw_alias_and_wrapper() {
        let mut module = test_module("test");
        module.extern_fns.push(ExternFnDef {
            id: FnId(1),
            name: "length".to_string(),
            declaring_module_path: "test".to_string(),
            span: (0, 0),
            target: ExternTarget::Js {
                module: "./extern/js/string.mjs".to_string(),
            },
            nullable: false,
            throws: false,
            call_kind: ExternCallKind::Static,
            param_types: vec![Type::String],
            return_type: Type::Int,
            bridge_params: vec![],
        });

        let output = emit_test_module(&module);
        assert!(output
            .contains("import { length as __krypton_raw$length } from './extern/js/string.mjs';"));
        assert!(output.contains("export function length(arg0) {"));
        assert!(output.contains("return __krypton_raw$length(arg0);"));
        assert!(!output.contains("__krypton_nullable_Some"));
    }

    #[test]
    fn constrained_nonnullable_js_extern_forwards_user_args_before_dicts() {
        let output = emit_lowered_source_module(
            r#"
extern js "./extern/js/host.mjs" {
    fun render_key[a](x: String) -> String where a: Eq + Hash
}

fun main() = render_key[String]("hi")
"#,
            "test",
        );

        assert!(output.contains("export function render_key(dict0, dict1, arg0) {"));
        assert!(output.contains("return __krypton_raw$render_key(arg0, dict0, dict1);"));
    }

    #[test]
    fn referenced_java_only_extern_fails_validation() {
        let mut module = test_module("test");
        let bind = VarId(0);
        let extern_fn = FnId(1);
        module.fn_identities.insert(
            extern_fn,
            krypton_ir::FnIdentity::Local {
                name: "println".to_string(),
            },
        );
        module.extern_fns.push(ExternFnDef {
            id: extern_fn,
            name: "println".to_string(),
            declaring_module_path: "test".to_string(),
            span: (0, 0),
            target: ExternTarget::Java {
                class: "krypton.runtime.KryptonIO".to_string(),
            },
            nullable: false,
            throws: false,
            call_kind: ExternCallKind::Static,
            param_types: vec![Type::Int],
            return_type: Type::Unit,
            bridge_params: vec![],
        });
        module.functions.push(FnDef {
            id: FnId(0),
            name: "main".to_string(),
            params: vec![],
            return_type: Type::Unit,
            body: expr(
                Type::Unit,
                ExprKind::Let {
                    bind,
                    ty: Type::Unit,
                    value: simple(SimpleExprKind::Call {
                        func: extern_fn,
                        args: vec![Atom::Lit(Literal::Int(42))],
                    }),
                    body: Box::new(expr(Type::Unit, ExprKind::Atom(Atom::Var(bind)))),
                },
            ),
        });

        let link_ctx = test_link_ctx("test");
        let view = link_ctx.view_for(&LinkModulePath::new("test")).unwrap();
        let module_sources = HashMap::from([("test".to_string(), None)]);
        let err = validate_js_extern_targets(&[module], &view, &module_sources)
            .expect_err("referenced Java-only extern should fail");
        assert!(err.to_string().contains("println"));
    }

    #[test]
    fn unreferenced_java_only_extern_passes_validation() {
        let mut module = test_module("test");
        let extern_fn = FnId(1);
        module.fn_identities.insert(
            extern_fn,
            krypton_ir::FnIdentity::Local {
                name: "println".to_string(),
            },
        );
        module.extern_fns.push(ExternFnDef {
            id: extern_fn,
            name: "println".to_string(),
            declaring_module_path: "test".to_string(),
            span: (0, 0),
            target: ExternTarget::Java {
                class: "krypton.runtime.KryptonIO".to_string(),
            },
            nullable: false,
            throws: false,
            call_kind: ExternCallKind::Static,
            param_types: vec![Type::Int],
            return_type: Type::Unit,
            bridge_params: vec![],
        });
        module.functions.push(FnDef {
            id: FnId(0),
            name: "main".to_string(),
            params: vec![],
            return_type: Type::Int,
            body: expr(Type::Int, ExprKind::Atom(Atom::Lit(Literal::Int(42)))),
        });

        let link_ctx = test_link_ctx("test");
        let view = link_ctx.view_for(&LinkModulePath::new("test")).unwrap();
        let module_sources = HashMap::from([("test".to_string(), None)]);
        validate_js_extern_targets(&[module], &view, &module_sources)
            .expect("unreferenced Java-only extern should pass");
    }

    // ── BindingAllocator unit tests ──

    #[test]
    fn binding_allocator_bare_name_when_no_collision() {
        let mut alloc = BindingAllocator::new(HashSet::new());
        assert_eq!(alloc.allocate("mod_a", "foo"), "foo");
        assert_eq!(alloc.resolve("mod_a", "foo"), "foo");
    }

    #[test]
    fn binding_allocator_mangles_on_collision() {
        let mut alloc = BindingAllocator::new(HashSet::new());
        assert_eq!(alloc.allocate("mod_a", "compute"), "compute");
        assert_eq!(alloc.allocate("mod_b", "compute"), "mod_b$compute");
        assert_eq!(alloc.resolve("mod_a", "compute"), "compute");
        assert_eq!(alloc.resolve("mod_b", "compute"), "mod_b$compute");
    }

    #[test]
    fn binding_allocator_local_names_block_bare() {
        let locals = HashSet::from(["filter".to_string()]);
        let mut alloc = BindingAllocator::new(locals);
        // "filter" is taken by local, so imported filter must be mangled
        assert_eq!(alloc.allocate("core/list", "filter"), "core$list$filter");
    }

    #[test]
    fn binding_allocator_preferred_name_used_when_available() {
        let mut alloc = BindingAllocator::new(HashSet::new());
        assert_eq!(
            alloc.allocate_preferred("core/list", "filter", "list_filter"),
            "list_filter"
        );
        assert_eq!(alloc.resolve("core/list", "filter"), "list_filter");
    }

    #[test]
    fn same_name_imports_get_module_qualified_alias() {
        // Two ImportedFnDefs with same original_name from different modules
        let mut module = test_module("app/main");
        module.module_path = ModulePath::new("app/main");
        module.imported_fns.push(ImportedFnDef {
            id: FnId(1),
            name: "compute".to_string(),
            source_module: "helpers_a".to_string(),
            original_name: "compute".to_string(),
            param_types: vec![],
            return_type: Type::Int,
        });
        module.imported_fns.push(ImportedFnDef {
            id: FnId(2),
            name: "compute_2".to_string(),
            source_module: "helpers_b".to_string(),
            original_name: "compute".to_string(),
            param_types: vec![],
            return_type: Type::Int,
        });

        let helpers_a_iface = ModuleInterface {
            module_path: LinkModulePath::new("helpers_a"),
            direct_deps: vec![],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        };
        let helpers_b_iface = ModuleInterface {
            module_path: LinkModulePath::new("helpers_b"),
            direct_deps: vec![],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        };
        let main_iface = ModuleInterface {
            module_path: LinkModulePath::new("app/main"),
            direct_deps: vec![
                LinkModulePath::new("helpers_a"),
                LinkModulePath::new("helpers_b"),
            ],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        };
        let link_ctx = LinkContext::build(vec![main_iface, helpers_a_iface, helpers_b_iface]);
        let view = link_ctx.view_for(&LinkModulePath::new("app/main")).unwrap();

        let registry = build_registry_for_modules(&[&module]);
        let variant_lookup = HashMap::new();
        let qualified_sum_type_names = HashSet::new();
        let suspend = SuspendSummary::empty();
        let mut emitter = JsEmitter::new(
            &module,
            false,
            &variant_lookup,
            &qualified_sum_type_names,
            &registry,
            &view,
            0,
            &suspend,
        );
        let output = emitter.emit();

        // First import gets bare name, second gets alias
        assert!(
            output.contains("import { compute } from '../helpers_a.mjs';"),
            "first compute should be bare, got: {output}"
        );
        assert!(
            output.contains("import { compute as compute_2 } from '../helpers_b.mjs';"),
            "second compute should use user alias, got: {output}"
        );
    }

    #[test]
    fn constructor_import_does_not_collide_with_fn_import() {
        // Test at the allocator level: a function import "Foo" from one module
        // should not collide with constructor import "Foo" from another.
        let mut alloc = BindingAllocator::new(HashSet::new());
        // Function import allocated first
        let fn_binding = alloc.allocate("fn_mod", "Foo");
        assert_eq!(fn_binding, "Foo");
        // Constructor import of same name from different module gets mangled
        let ctor_binding = alloc.allocate("ctor_mod", "Foo");
        assert_eq!(ctor_binding, "ctor_mod$Foo");
        // Both resolve correctly
        assert_eq!(alloc.resolve("fn_mod", "Foo"), "Foo");
        assert_eq!(alloc.resolve("ctor_mod", "Foo"), "ctor_mod$Foo");
    }

    #[test]
    fn variant_lookup_uses_qualified_keys_only() {
        // variant_lookup only has qualified keys; there are no bare fallback entries
        let mut variant_lookup: HashMap<(String, u32), String> = HashMap::new();
        let mut qualified_sum_type_names: HashSet<String> = HashSet::new();

        // Insert only qualified key
        qualified_sum_type_names.insert("core/option/Option".to_string());
        variant_lookup.insert(("core/option/Option".to_string(), 0), "Some".to_string());
        variant_lookup.insert(("core/option/Option".to_string(), 1), "None".to_string());

        // Ensure there is no bare "Option" key
        assert!(!variant_lookup.contains_key(&("Option".to_string(), 0)));
        assert!(!variant_lookup.contains_key(&("Option".to_string(), 1)));

        // Qualified keys work
        assert_eq!(
            variant_lookup.get(&("core/option/Option".to_string(), 0)),
            Some(&"Some".to_string())
        );
        assert_eq!(
            variant_lookup.get(&("core/option/Option".to_string(), 1)),
            Some(&"None".to_string())
        );
    }

    #[test]
    fn module_slug_replaces_slashes() {
        assert_eq!(module_slug("core/option"), "core$option");
        assert_eq!(module_slug("helpers_a"), "helpers_a");
        assert_eq!(module_slug("a/b/c"), "a$b$c");
    }
}
