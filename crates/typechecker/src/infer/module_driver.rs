use std::collections::{HashMap, HashSet};

use krypton_parser::ast::Module;

use crate::typed_ast::TypedModule;
use crate::unify::{SpannedTypeError, TypeError};

use super::bodies::infer_function_bodies;
use super::helpers::{reserve_gen_for_env_schemes, spanned};
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

    let mut cache: HashMap<String, TypedModule> = HashMap::new();
    let mut interface_cache: HashMap<String, crate::module_interface::ModuleInterface> =
        HashMap::new();

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
    interface_cache: &HashMap<String, crate::module_interface::ModuleInterface>,
    module_path: String,
    prelude_tree_paths: &HashSet<String>,
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

    // Phase: SCC-based function inference
    let (fn_decls, result_schemes, fn_bodies, mut fn_constraint_requirements) =
        infer_function_bodies(
            &mut state,
            module,
            &extern_fns,
            &trait_registry,
            &trait_method_map,
            &module_path,
        )
        .map_err(|e| vec![e])?;

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
