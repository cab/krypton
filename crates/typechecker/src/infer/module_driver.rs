use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Decl, Module, TypeDeclKind, Visibility};

use crate::trait_registry::TraitRegistry;
use crate::typed_ast::{
    self, ExportedTraitDef, ExternFnInfo, ExternTraitInfo, ExternTypeInfo, InstanceDefInfo,
    StructDecl, SumDecl, TraitDefInfo, TraitName, TypedExpr, TypedFnDecl, TypedModule,
};
use crate::types::{Type, TypeScheme, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::bodies::infer_function_bodies;
use super::checks;
use super::extern_decl::ExternBindingInfo;
use super::helpers::{constructor_names, free_vars, reserve_gen_for_env_schemes, spanned};
use super::impls::typecheck_impl_methods;
use super::state::ModuleInferenceState;
use super::traits_register::process_traits_and_deriving;
use super::InferError;

/// Infer types for all top-level definitions in a module.
///
/// Returns a `Vec<TypedModule>` containing the main module (first)
/// followed by any imported modules discovered during inference.
///
/// `root_module_path` is the module path for the root file (e.g., `Some("hello")` for `hello.kr`).
///
/// Uses SCC (strongly connected component) analysis to process definitions
/// in dependency order. Functions within the same SCC are inferred together
/// as a mutually recursive group, then generalized before later SCCs see them.
#[tracing::instrument(skip(module, resolver), fields(decls = module.decls.len()))]
pub fn infer_module(
    module: &Module,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
    root_module_path: String,
    target: krypton_parser::ast::CompileTarget,
) -> Result<
    (
        Vec<TypedModule>,
        Vec<crate::module_interface::ModuleInterface>,
    ),
    Vec<InferError>,
> {
    use krypton_modules::module_graph;
    use krypton_modules::stdlib_loader::StdlibLoader;

    // Filter root module by platform before anything else
    let mut module = module.clone();
    krypton_parser::platform::filter_by_platform(&mut module, target);
    let module = &module;

    // Build the module graph (resolves, parses, toposorts all imports + prelude)
    let graph = module_graph::build_module_graph(module, resolver, target).map_err(|e| {
        vec![match e {
            module_graph::ModuleGraphError::ParseError {
                path,
                source,
                errors,
            } => InferError::ModuleParseError {
                path,
                source,
                errors,
            },
            other => InferError::TypeError {
                error: map_graph_error(other),
                error_source: None,
            },
        }]
    })?;

    let mut cache: FxHashMap<String, TypedModule> = FxHashMap::default();
    let mut interface_cache: FxHashMap<String, crate::module_interface::ModuleInterface> =
        FxHashMap::default();

    // Type-check each dependency in topological order
    for resolved in &graph.modules {
        if !cache.contains_key(&resolved.path) {
            let mut dep_paths: Vec<String> =
                crate::module_interface::collect_direct_deps(&resolved.module)
                    .iter()
                    .map(|p| p.0.clone())
                    .collect();
            if !graph.prelude_tree_paths.contains(&resolved.path) {
                dep_paths.push("prelude".to_string());
            }
            let typed = infer_module_inner(
                &resolved.module,
                &interface_cache,
                resolved.path.clone(),
                &graph.prelude_tree_paths,
            )
            .map_err(|errors| {
                // Re-resolve source for the failing module (error path only)
                let source_text = StdlibLoader::get_source(&resolved.path)
                    .map(|s| s.to_string())
                    .or_else(|| resolver.resolve(&resolved.path));
                let error_source = source_text.map(|s| (resolved.path.clone(), s));
                errors
                    .into_iter()
                    .map(|mut e| {
                        if e.source_file.is_none() {
                            e.source_file = Some(resolved.path.clone());
                        }
                        InferError::TypeError {
                            error: e,
                            error_source: error_source.clone(),
                        }
                    })
                    .collect::<Vec<_>>()
            })?;
            let mut typed = typed;
            // Attach source text for diagnostic rendering of downstream codegen errors
            typed.module_source = StdlibLoader::get_source(&resolved.path)
                .map(|s| s.to_string())
                .or_else(|| resolver.resolve(&resolved.path));
            // Extract interface for downstream modules
            let iface = crate::module_interface::extract_interface(&typed, &dep_paths);
            interface_cache.insert(resolved.path.clone(), iface);
            cache.insert(resolved.path.clone(), typed);
        }
    }

    // Compute root direct deps before root_module_path is moved.
    let mut root_dep_paths: Vec<String> = crate::module_interface::collect_direct_deps(module)
        .iter()
        .map(|p| p.0.clone())
        .collect();
    if !graph.prelude_tree_paths.contains(&root_module_path) {
        root_dep_paths.push("prelude".to_string());
    }

    // Type-check the root module
    let main = infer_module_inner(
        module,
        &interface_cache,
        root_module_path,
        &graph.prelude_tree_paths,
    )
    .map_err(|errors| {
        errors
            .into_iter()
            .map(|e| InferError::TypeError {
                error: e,
                error_source: None,
            })
            .collect::<Vec<_>>()
    })?;

    // Validate main function signature (root module only)
    if let Some(&idx) = main.fn_types_by_name.get("main") {
        let main_span = module
            .decls
            .iter()
            .find_map(|d| {
                if let Decl::DefFn(f) = d {
                    if f.name == "main" {
                        return Some(f.span);
                    }
                }
                None
            })
            .unwrap_or((0, 0));

        let scheme = &main.fn_types[idx].scheme;
        if let Type::Fn(params, ret) = &scheme.ty {
            if !params.is_empty() {
                return Err(vec![InferError::TypeError {
                    error: spanned(
                        TypeError::InvalidMainSignature {
                            reason: "main must take no parameters".to_string(),
                        },
                        main_span,
                    ),
                    error_source: None,
                }]);
            }
            if !matches!(ret.as_ref(), Type::Unit) && !ret.is_never() {
                return Err(vec![InferError::TypeError {
                    error: spanned(
                        TypeError::InvalidMainSignature {
                            reason: format!("main must return Unit, found {ret}"),
                        },
                        main_span,
                    ),
                    error_source: None,
                }]);
            }
        }
    }

    let root_iface = crate::module_interface::extract_interface(&main, &root_dep_paths);

    let mut result = vec![main];
    // Collect cached imported modules in topological order (dependencies first)
    for resolved in &graph.modules {
        if let Some(typed) = cache.remove(&resolved.path) {
            result.push(typed);
        }
    }

    // Collect all interfaces: root first, then deps in topological order
    let mut interfaces = vec![root_iface];
    for resolved in &graph.modules {
        if let Some(iface) = interface_cache.remove(&resolved.path) {
            interfaces.push(iface);
        }
    }

    Ok((result, interfaces))
}

/// Convert a non-parse `ModuleGraphError` into a `SpannedTypeError`.
/// ParseError is handled separately as `InferError::ModuleParseError`.
pub(super) fn map_graph_error(e: krypton_modules::module_graph::ModuleGraphError) -> SpannedTypeError {
    use krypton_modules::module_graph::ModuleGraphError;
    match e {
        ModuleGraphError::CircularImport { cycle, span } => {
            spanned(TypeError::CircularImport { cycle }, span)
        }
        ModuleGraphError::UnknownModule { path, span } => {
            spanned(TypeError::UnknownModule { path }, span)
        }
        ModuleGraphError::BareImport { path, span } => {
            spanned(TypeError::BareImport { path }, span)
        }
        ModuleGraphError::ParseError { .. } => {
            unreachable!("ParseError is handled directly as InferError::ModuleParseError")
        }
    }
}

/// Return the main `TypedModule` from `infer_module` result (for backward compatibility).
pub fn infer_module_single(
    module: &Module,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<TypedModule, Vec<InferError>> {
    let (mut modules, _) = infer_module(
        module,
        resolver,
        "main".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )?;
    Ok(modules.remove(0))
}


/// Phase: Register traits (imported + local), process deriving, register impl instances.
/// Returns (trait_registry, exported_trait_defs, derived_instance_defs, imported_instance_defs, trait_method_map).
///
/// Extracted from `infer_module_inner` so its locals are deallocated before the
/// SCC function inference phase, reducing peak stack usage.

/// Phase 1: Import instances from cached modules via orphan-rule lookup.

/// Phase 2: Register trait definitions imported from other modules.

/// Phase 2c: Register extern traits (Java interfaces exposed as Krypton traits).
///
/// Each `extern java "..." as trait Name[a] { ... }` is registered as a real trait
/// in the TraitRegistry. Methods are bound into the environment via `bind_trait_method`,
/// making them callable like any other trait method.

/// Phase 3: Process local DefTrait declarations.

/// Phase 4: Process deriving declarations.

/// Phase 5: Process DefImpl declarations (register instances).


/// Phase: SCC-based function body inference.
/// Returns (fn_decls, result_schemes, fn_bodies, fn_constraint_requirements).
///
/// Extracted from `infer_module_inner` so that earlier phase locals are deallocated
/// before the deep `infer_expr_inner` recursion.

/// Phase: Type-check impl method bodies and produce InstanceDefInfo.
///
/// Extracted from `infer_module_inner` to reduce stack frame size.


/// Internal per-module inference with pre-resolved module cache.
///
/// The module graph has already been resolved and toposorted by `infer_module`.
/// Import declarations look up module interfaces from `interface_cache` and typed
/// results from `cache` — no recursive resolution or cycle detection needed.
///
/// Pipeline phases:
///  1. Initialize state (env, registry, intrinsics)
///  2. Build synthetic prelude import
///  3. Process imports (types, fns, traits, re-exports)
///  4. Reserve type var generator past imported schemes
///  5. Process local extern declarations
///  6. Clean up prelude shadows
///  7. Pre-register local type names
///  8. Process local type declarations
///  9. Register traits (imported + local)
/// 10. Process deriving declarations
/// 11. Process impl blocks
/// 12. SCC-based function inference
/// 13. Post-inference instance resolution
/// 14. Impl method type-checking
/// 15. Assemble TypedModule
pub(crate) fn infer_module_inner(
    module: &Module,
    interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
    module_path: String,
    prelude_tree_paths: &FxHashSet<String>,
) -> Result<TypedModule, Vec<SpannedTypeError>> {
    let is_core_module = module_path.starts_with("core/");
    let is_prelude_tree = prelude_tree_paths.contains(&module_path);

    let mut state = ModuleInferenceState::new(is_core_module);

    let synthetic_prelude_import =
        state.build_synthetic_prelude_import(is_prelude_tree, interface_cache);

    state
        .process_imports(module, interface_cache, synthetic_prelude_import.as_ref())
        .map_err(|e| vec![e])?;
    reserve_gen_for_env_schemes(&state.env, &mut state.gen);
    let (extern_fns, extern_types, extern_bindings, extern_fn_constraints, pending_extern_traits) =
        state
            .process_local_externs(module, &module_path)
            .map_err(|e| vec![e])?;
    state.cleanup_prelude_shadows(module);
    state
        .check_explicit_import_shadows(module)
        .map_err(|e| vec![e])?;
    state
        .check_duplicate_function_names(module)
        .map_err(|e| vec![e])?;
    state.preregister_type_names(module);
    let constructor_schemes = state
        .process_local_type_decls(module, &module_path)
        .map_err(|e| vec![e])?;

    // Phase: trait registration, deriving, impl registration
    let (
        trait_registry,
        exported_trait_defs,
        extern_traits,
        derived_instance_defs,
        imported_instance_defs,
        trait_method_map,
    ) = process_traits_and_deriving(
        &mut state,
        module,
        interface_cache,
        &module_path,
        is_core_module,
        pending_extern_traits,
    )
    .map_err(|e| vec![e])?;

    // Phase: SCC-based function inference. Returns a vec of errors so every
    // unresolved/ambiguous/no-match overload site is reported in one pass
    // rather than collapsed into a single diagnostic with a byte-offset note.
    let (fn_decls, result_schemes, fn_bodies, mut fn_constraint_requirements) =
        infer_function_bodies(
            &mut state,
            module,
            &extern_fns,
            &trait_registry,
            &trait_method_map,
            &module_path,
        )?;

    // Merge extern function where-clause dict requirements
    for (name, reqs) in extern_fn_constraints {
        fn_constraint_requirements.entry(name).or_insert(reqs);
    }

    // Phase: impl method type-checking
    let instance_defs = typecheck_impl_methods(
        &mut state,
        module,
        &module_path,
        &trait_registry,
        &trait_method_map,
        &extern_fns,
    )
    .map_err(|e| vec![e])?;

    state.assemble_typed_module(
        module,
        module_path,
        &fn_decls,
        result_schemes,
        fn_bodies,
        instance_defs,
        derived_instance_defs,
        imported_instance_defs,
        &mut fn_constraint_requirements,
        &trait_method_map,
        &trait_registry,
        exported_trait_defs,
        extern_fns,
        extern_types,
        extern_traits,
        extern_bindings,
        constructor_schemes,
        interface_cache,
    )
}

impl ModuleInferenceState {
    /// Assemble the final TypedModule from accumulated state and inference-phase outputs.
    ///
    /// Extracted from `infer_module_inner` specifically to reduce that function's
    /// stack frame size — bundling the args into a struct here would risk pushing
    /// the inputs back onto the caller's frame and undoing that optimization, so
    /// the wide signature is intentional.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn assemble_typed_module(
        self,
        module: &Module,
        module_path: String,
        fn_decls: &[&krypton_parser::ast::FnDecl],
        result_schemes: Vec<Option<TypeScheme>>,
        fn_bodies: Vec<Option<TypedExpr>>,
        instance_defs: Vec<InstanceDefInfo>,
        derived_instance_defs: Vec<InstanceDefInfo>,
        _imported_instance_defs: Vec<InstanceDefInfo>,
        fn_constraint_requirements: &mut FxHashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
        _trait_method_map: &FxHashMap<String, TraitName>,
        trait_registry: &TraitRegistry,
        exported_trait_defs: Vec<ExportedTraitDef>,
        extern_fns: Vec<ExternFnInfo>,
        extern_types: Vec<ExternTypeInfo>,
        extern_traits: Vec<ExternTraitInfo>,
        extern_bindings: Vec<ExternBindingInfo>,
        constructor_schemes: Vec<(String, TypeScheme)>,
        interface_cache: &FxHashMap<String, crate::module_interface::ModuleInterface>,
    ) -> Result<TypedModule, Vec<SpannedTypeError>> {
        let mut instance_defs = instance_defs;
        instance_defs.extend(derived_instance_defs);

        let mut results: Vec<typed_ast::FnTypeEntry> = self
            .imports
            .imported_fn_types
            .into_iter()
            .map(|f| typed_ast::FnTypeEntry {
                name: f.name,
                scheme: f.scheme,
                origin: f.origin,
                qualified_name: f.qualified_name,
            })
            .collect();
        results.extend(
            constructor_schemes
                .iter()
                .map(|(n, s)| typed_ast::FnTypeEntry {
                    name: n.clone(),
                    scheme: s.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        n.clone(),
                    ),
                }),
        );
        results.extend(
            extern_bindings
                .iter()
                .map(|binding| typed_ast::FnTypeEntry {
                    name: binding.name.clone(),
                    scheme: binding.scheme.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        binding.name.clone(),
                    ),
                }),
        );
        results.extend(
            fn_decls
                .iter()
                .enumerate()
                .map(|(i, d)| typed_ast::FnTypeEntry {
                    name: d.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        d.name.clone(),
                    ),
                }),
        );
        // Add instance method types to the flat list for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(
                    &inst.trait_name.local_name,
                    &inst.target_type_name,
                    &m.name,
                );
                results.push(typed_ast::FnTypeEntry {
                    name: qualified.clone(),
                    scheme: m.scheme.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        qualified,
                    ),
                });
            }
        }

        // Build exported_fn_types: the public API surface for downstream importers.
        // Includes pub (transparent) constructors, pub local functions, pub extern methods,
        // and instance methods.
        // Does NOT include imported functions.
        let mut exported_fn_types: Vec<typed_ast::ExportedFn> = Vec::new();

        // 1. Constructors for pub (transparent) types only
        for (cname, scheme) in &constructor_schemes {
            let is_pub_open = module.decls.iter().any(|d| {
                if let Decl::DefType(td) = d {
                    matches!(td.visibility, Visibility::Pub)
                        && constructor_names(td).contains(cname)
                } else {
                    false
                }
            });
            if is_pub_open {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: cname.clone(),
                    scheme: scheme.clone(),
                    origin: None,
                    def_span: None,
                    qualified_name: None,
                });
            }
        }

        // 2. Local pub function declarations
        for (i, decl) in fn_decls.iter().enumerate() {
            if matches!(decl.visibility, Visibility::Pub) {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: decl.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    def_span: Some(decl.span),
                    qualified_name: None,
                });
            }
        }

        // 3. Local pub extern methods
        for binding in &extern_bindings {
            if matches!(binding.visibility, Visibility::Pub) {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: binding.name.clone(),
                    scheme: binding.scheme.clone(),
                    origin: None,
                    def_span: Some(binding.def_span),
                    qualified_name: None,
                });
            }
        }

        let mut functions: Vec<TypedFnDecl> = Vec::new();
        // Parallel: params_per_decl[i] == parameter types for functions[i],
        // for the shared overload mangler at end-of-typechecking.
        let mut params_per_decl: Vec<Vec<Type>> = Vec::new();
        let mut fn_bodies = fn_bodies;
        for (i, decl) in fn_decls.iter().enumerate() {
            let mut body = fn_bodies[i].take().unwrap();
            typed_ast::apply_subst(&mut body, &self.subst);
            let scheme = result_schemes[i].clone().unwrap();
            let params_for_mangle: Vec<Type> = match &scheme.ty {
                Type::Fn(ps, _) => ps.iter().map(|(_, t)| t.clone()).collect(),
                _ => vec![],
            };
            functions.push(TypedFnDecl {
                name: decl.name.clone(),
                visibility: decl.visibility,
                params: decl
                    .params
                    .iter()
                    .map(|p| crate::typed_ast::TypedParam {
                        name: p.name.clone(),
                        mode: p.mode,
                    })
                    .collect(),
                body,
                close_self_type: None,
                fn_scope_id: crate::typed_ast::ScopeId(u32::MAX),
                def_span: decl.span,
                exported_symbol: String::new(),
            });
            params_per_decl.push(params_for_mangle);
        }
        // Build temporary flat list of instance method bodies for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(
                    &inst.trait_name.local_name,
                    &inst.target_type_name,
                    &m.name,
                );
                let close_self_type =
                    if inst.trait_name.local_name == "Disposable" && m.name == "dispose" {
                        Some(inst.target_type_name.clone())
                    } else {
                        None
                    };
                let method_span = m.body.span;
                let params_for_mangle: Vec<Type> = match &m.scheme.ty {
                    Type::Fn(ps, _) => ps.iter().map(|(_, t)| t.clone()).collect(),
                    _ => vec![],
                };
                functions.push(TypedFnDecl {
                    name: qualified,
                    visibility: Visibility::Pub,
                    params: m.params.clone(),
                    body: m.body.clone(),
                    close_self_type,
                    fn_scope_id: crate::typed_ast::ScopeId(u32::MAX),
                    def_span: method_span,
                    exported_symbol: String::new(),
                });
                params_per_decl.push(params_for_mangle);
            }
        }

        // Name-keyed: two local overloads share a name, so a later entry will
        // overwrite an earlier one here. The consumers (constraint-propagation
        // checks below and in `checks.rs`) only use this to look up "a scheme
        // for this name" — no overload-specific disambiguation. Overload
        // disambiguation is carried separately on resolved_ref.
        let fn_schemes: FxHashMap<String, TypeScheme> = results
            .iter()
            .map(|e| (e.name.clone(), e.scheme.clone()))
            .collect();
        let mut validation_errors: Vec<SpannedTypeError> = Vec::new();
        for func in &functions {
            let current_requirements = fn_schemes
                .get(&func.name)
                .map(|s| s.constraints.as_slice())
                .unwrap_or(&[]);
            // Monomorphic functions have no type variables
            let func_var_names = fn_schemes
                .get(&func.name)
                .map(|s| &s.var_names)
                .cloned()
                .unwrap_or_default();
            if let Err(e) = checks::check_constrained_function_refs(
                &func.body,
                current_requirements,
                &fn_schemes,
                trait_registry,
                &func_var_names,
            ) {
                validation_errors.push(e);
            }
        }

        // fn_schemes already includes imported function schemes with constraints embedded

        // Detect implicit trait constraints from body and merge into fn_constraint_requirements
        for func in &functions {
            let mut fn_type_param_vars: FxHashSet<TypeVarId> = FxHashSet::default();
            if let Some(scheme) = fn_schemes.get(&func.name) {
                if let Type::Fn(param_types, ret_ty) = &scheme.ty {
                    for (_, pty) in param_types.iter() {
                        for v in free_vars(pty) {
                            fn_type_param_vars.insert(v);
                        }
                    }
                    for v in free_vars(ret_ty) {
                        fn_type_param_vars.insert(v);
                    }
                }
            }
            let mut constraints = Vec::new();
            checks::detect_trait_constraints(
                &func.body,
                trait_registry,
                &self.subst,
                &fn_type_param_vars,
                &fn_schemes,
                &mut constraints,
            );
            if !constraints.is_empty() {
                constraints.sort();
                constraints.dedup();
                // Merge into fn_constraint_requirements (dedup by trait+var)
                let existing = fn_constraint_requirements
                    .entry(func.name.clone())
                    .or_default();
                for (trait_name, type_vars) in constraints {
                    if !existing
                        .iter()
                        .any(|(t, v)| t == &trait_name && *v == type_vars)
                    {
                        existing.push((trait_name, type_vars));
                    }
                }
            }
        }

        // Fold final constraints into TypeSchemes in fn_types (results) so they
        // propagate to importers via exported_fn_types without a side-channel map.
        for entry in &mut results {
            if let Some(reqs) = fn_constraint_requirements.get(&entry.name) {
                if entry.scheme.constraints.is_empty() && !reqs.is_empty() {
                    entry.scheme.constraints = reqs.clone();
                }
            }
        }
        // Also update exported_fn_types (built earlier from result_schemes)
        for ef in &mut exported_fn_types {
            if let Some(reqs) = fn_constraint_requirements.get(&ef.name) {
                if ef.scheme.constraints.is_empty() && !reqs.is_empty() {
                    ef.scheme.constraints = reqs.clone();
                }
            }
        }

        let mut trait_defs = Vec::new();
        for info in trait_registry.traits().values() {
            let is_imported = self.imported_trait_names.contains(&info.name);
            let method_info: Vec<(String, usize)> = info
                .methods
                .iter()
                .map(|m| (m.name.clone(), m.param_types.len()))
                .collect();
            let method_tc_types: FxHashMap<String, (Vec<(crate::types::ParamMode, Type)>, Type)> =
                info.methods
                    .iter()
                    .map(|m| {
                        (
                            m.name.clone(),
                            (m.param_types.clone(), m.return_type.clone()),
                        )
                    })
                    .collect();
            let method_constraints: FxHashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> = info
                .methods
                .iter()
                .filter(|m| !m.constraints.is_empty())
                .map(|m| (m.name.clone(), m.constraints.clone()))
                .collect();
            trait_defs.push(TraitDefInfo {
                name: info.name.clone(),
                trait_id: TraitName::new(info.module_path.clone(), info.name.clone()),
                methods: method_info,
                is_imported,
                type_var_id: info.type_var_id,
                type_var_ids: info.type_var_ids.clone(),
                method_tc_types,
                method_constraints,
            });
        }

        // Convert FnTypeEntry to tuple format for ownership/auto_close APIs
        let results_tuples: Vec<(String, TypeScheme, Option<TraitName>)> = results
            .iter()
            .map(|e| (e.name.clone(), e.scheme.clone(), e.origin.clone()))
            .collect();

        let (ownership_result, ownership_errors) = crate::ownership::check_ownership(
            module,
            &functions,
            &results_tuples,
            &self.registry,
            &self.let_own_spans,
            &self.lambda_own_captures,
            &self.imports.imported_fn_qualifiers,
        );
        let has_ownership_errors = !ownership_errors.is_empty();
        validation_errors.extend(ownership_errors);

        // Filter to exported functions only for cross-module propagation
        let exported_names: FxHashSet<&str> = exported_fn_types
            .iter()
            .map(|ef| ef.name.as_str())
            .collect();
        let exported_fn_qualifiers: FxHashMap<_, _> = ownership_result
            .fn_qualifiers
            .into_iter()
            .filter(|(name, _)| exported_names.contains(name.as_str()))
            .collect();

        // Stamp ScopeIds on every typed function body before analysis/lowering.
        // Both auto_close and ir::lower rely on scope identity being stable and
        // unique — ScopeIds replace the fragile span-based lookup.
        crate::scope_ids::stamp_functions(&mut functions);

        // Only run auto_close if ownership checking passed — auto_close depends on
        // complete ownership results and may encounter unexpected types otherwise.
        let auto_close = if !has_ownership_errors {
            let (auto_close, auto_close_errors) = crate::auto_close::compute_auto_close(
                &functions,
                &results_tuples,
                trait_registry,
                &ownership_result.moves,
            );
            validation_errors.extend(auto_close_errors);
            auto_close
        } else {
            crate::typed_ast::AutoCloseInfo::default()
        };

        if !validation_errors.is_empty() {
            validation_errors.sort_by_key(|e| e.span);
            return Err(validation_errors);
        }

        let struct_decls: Vec<_> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Record { fields } => Some(StructDecl {
                        name: td.name.clone(),
                        type_params: td.type_params.clone(),
                        fields: fields.clone(),
                        qualified_name: typed_ast::QualifiedName::new(
                            module_path.to_string(),
                            td.name.clone(),
                        ),
                    }),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let sum_decls: Vec<SumDecl> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Sum { variants } => Some(SumDecl {
                        name: td.name.clone(),
                        type_params: td.type_params.clone(),
                        variants: variants.clone(),
                        qualified_name: typed_ast::QualifiedName::new(
                            module_path.to_string(),
                            td.name.clone(),
                        ),
                    }),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let _local_type_names: FxHashSet<String> = module
            .decls
            .iter()
            .filter_map(|d| {
                if let Decl::DefType(td) = d {
                    Some(td.name.clone())
                } else {
                    None
                }
            })
            .collect();
        let mut type_visibility: FxHashMap<String, Visibility> = FxHashMap::default();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                type_visibility.insert(td.name.clone(), td.visibility);
            }
            if let Decl::Extern {
                alias: Some(name),
                alias_visibility,
                is_trait: false,
                ..
            } = decl
            {
                type_visibility.insert(
                    name.clone(),
                    alias_visibility.unwrap_or(Visibility::Private),
                );
            }
        }

        let mut exported_trait_defs = exported_trait_defs;
        exported_trait_defs.extend(self.reexported_trait_defs);

        // Build exported_type_infos from fully-resolved TypeInfo in the registry.
        // This allows importers to register types without re-resolving from AST.
        let mut exported_type_infos: FxHashMap<String, typed_ast::ExportedTypeInfo> = FxHashMap::default();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                if matches!(td.visibility, Visibility::Private) {
                    continue;
                }
                if let Some(type_info) = self.registry.lookup_type(&td.name) {
                    let kind = match &type_info.kind {
                        crate::type_registry::TypeKind::Record { fields } => {
                            typed_ast::ExportedTypeKind::Record {
                                fields: fields.clone(),
                            }
                        }
                        crate::type_registry::TypeKind::Sum { variants } => {
                            typed_ast::ExportedTypeKind::Sum {
                                variants: variants
                                    .iter()
                                    .map(|v| typed_ast::ExportedVariantInfo {
                                        name: v.name.clone(),
                                        fields: v.fields.clone(),
                                    })
                                    .collect(),
                            }
                        }
                    };
                    exported_type_infos.insert(
                        td.name.clone(),
                        typed_ast::ExportedTypeInfo {
                            name: td.name.clone(),
                            source_module: module_path.to_string(),
                            type_params: td.type_params.clone(),
                            type_param_vars: type_info.type_param_vars.clone(),
                            kind,
                            lifts: type_info.lifts.clone(),
                        },
                    );
                }
            }
        }

        // Include extern type aliases in exported_type_infos so they flow
        // through the interface like any other type — consumers register
        // them uniformly via register_type_from_export.
        for decl in &module.decls {
            if let Decl::Extern {
                alias: Some(name),
                is_trait: false,
                ..
            } = decl
            {
                if exported_type_infos.contains_key(name) {
                    continue;
                }
                if let Some(type_info) = self.registry.lookup_type(name) {
                    exported_type_infos.insert(
                        name.clone(),
                        typed_ast::ExportedTypeInfo {
                            name: name.clone(),
                            source_module: module_path.to_string(),
                            type_params: type_info.type_params.clone(),
                            type_param_vars: type_info.type_param_vars.clone(),
                            kind: typed_ast::ExportedTypeKind::Opaque,
                            lifts: type_info.lifts.clone(),
                        },
                    );
                }
            }
        }

        // Include imported types (sum and record) in exported_type_infos so
        // IR lowering can resolve them without AST fallback.
        for (type_name, (source_path, _vis)) in &self.imports.imported_type_info {
            if exported_type_infos.contains_key(type_name) {
                continue;
            }
            if let Some(iface) = interface_cache.get(source_path.as_str()) {
                if let Some(ts) = iface.exported_types.iter().find(|t| t.name == *type_name) {
                    let export =
                        crate::module_interface::type_summary_to_export_info(ts, source_path);
                    exported_type_infos.insert(type_name.clone(), export);
                }
            }
        }

        let fn_types_by_name: FxHashMap<String, usize> = results
            .iter()
            .enumerate()
            .map(|(i, e)| (e.name.clone(), i))
            .collect();

        // Stamp `exported_symbol` on every TypedFnDecl using the shared
        // overload mangler so IR/codegen can read it directly without
        // re-implementing the rule. `params_per_decl` carries per-decl
        // param-type fingerprints built alongside the decls so overloaded
        // siblings can be distinguished by structure, not by name alone.
        let mangled_symbols = crate::module_interface::mangle_typed_fn_decls(
            &functions,
            &params_per_decl,
        );
        for (f, m) in functions.iter_mut().zip(mangled_symbols.into_iter()) {
            f.exported_symbol = m;
        }

        Ok(TypedModule {
            module_path,
            fn_types: results,
            fn_types_by_name,
            exported_fn_types,
            functions,
            trait_defs,
            instance_defs,
            extern_fns,
            extern_types,
            extern_traits,
            struct_decls,
            sum_decls,
            type_visibility,
            reexported_fn_types: self.reexported_fn_types,
            reexported_type_names: self.reexported_type_names,
            reexported_type_visibility: self.reexported_type_visibility,
            exported_trait_defs,
            exported_type_infos,
            auto_close,
            exported_fn_qualifiers,
            module_source: None,
        })
    }
}
