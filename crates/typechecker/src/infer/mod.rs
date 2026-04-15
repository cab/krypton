use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, Module, Visibility};

use crate::scc;
use crate::trait_registry::TraitRegistry;
use crate::type_registry::{self, ResolutionContext};
use crate::typed_ast::{ExternFnInfo, TraitName, TypedExpr, TypedModule};
use crate::types::{BindingSource, Type, TypeEnv, TypeScheme, TypeVarId};
use crate::unify::{coerce_unify, unify, SecondaryLabel, SpannedTypeError, TypeError};

/// Error from `infer_module`, bundling the error with enough context
/// to render diagnostics against the correct file.
#[derive(Debug)]
pub enum InferError {
    /// A type error, possibly from an imported module.
    TypeError {
        error: SpannedTypeError,
        /// (module_path, source_text) for the module where the error originated.
        /// `None` means the error is in the root/user file.
        error_source: Option<(String, String)>,
    },
    /// Parse errors in an imported module — rendered via the parser's own diagnostics.
    ModuleParseError {
        path: String,
        source: String,
        errors: Vec<krypton_parser::diagnostics::ParseError>,
    },
}

impl InferError {
    /// Get the `SpannedTypeError` if this is a type error, or `None` for parse errors.
    pub fn type_error(&self) -> Option<&SpannedTypeError> {
        match self {
            InferError::TypeError { error, .. } => Some(error),
            InferError::ModuleParseError { .. } => None,
        }
    }
}

mod checks;
mod derive;
mod display;
mod entry;
mod expr;
mod extern_decl;
mod fork;
mod helpers;
mod import_ctx;
mod imports;
mod pattern;
mod resolve_multi;
mod resolve_overloads;
mod deriving_pass;
mod impls;
mod state;
mod traits_register;

pub use display::display_type;
pub use entry::infer_expr;
pub(super) use display::leading_type_var;
pub(crate) use entry::collect_parser_pattern_bindings;
pub(super) use entry::{
    find_first_recur_span, first_own_capture, instantiate_field_type,
};
pub(super) use helpers::*;
pub(crate) use import_ctx::ImportBinding;
pub(crate) use state::{InferFunctionBodiesResult, ModuleInferenceState};
use deriving_pass::process_deriving;
use impls::{register_impl_instances, typecheck_impl_methods};
use traits_register::{process_traits_and_deriving, resolve_fn_param_types_for_overlap};

pub(crate) use expr::InferenceContext;



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
fn map_graph_error(e: krypton_modules::module_graph::ModuleGraphError) -> SpannedTypeError {
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
fn infer_function_bodies<'a>(
    state: &mut ModuleInferenceState,
    module: &'a Module,
    _extern_fns: &[ExternFnInfo],
    trait_registry: &TraitRegistry,
    trait_method_map: &HashMap<String, TraitName>,
    mod_path: &str,
) -> Result<InferFunctionBodiesResult<'a>, SpannedTypeError> {
    let fn_decls: Vec<&krypton_parser::ast::FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Check that pub functions have full type annotations
    for decl in &fn_decls {
        if matches!(decl.visibility, Visibility::Pub) {
            let mut missing = Vec::new();
            for p in &decl.params {
                if p.ty.is_none() {
                    missing.push(format!("parameter `{}`", p.name));
                }
            }
            if decl.return_type.is_none() {
                missing.push("return type".to_string());
            }
            if !missing.is_empty() {
                return Err(spanned(
                    TypeError::MissingPubAnnotation {
                        fn_name: decl.name.clone(),
                        missing,
                    },
                    decl.span,
                ));
            }
        }
    }

    let adj = scc::build_dependency_graph(&fn_decls);
    let sccs = scc::tarjan_scc(&adj);

    let mut result_schemes: Vec<Option<TypeScheme>> = vec![None; fn_decls.len()];
    let mut fn_bodies: Vec<Option<TypedExpr>> = vec![None; fn_decls.len()];
    let mut fn_constraint_requirements: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> =
        HashMap::new();
    let mut saved_type_param_maps: HashMap<usize, HashMap<String, TypeVarId>> = HashMap::new();

    for component in &sccs {
        let mut deferred_overloads: Vec<expr::DeferredOverload> = Vec::new();
        let mut pre_bound: Vec<(usize, Type)> = Vec::new();
        for &idx in component {
            let tv = Type::Var(state.gen.fresh());
            state.env.bind_top_level_function(
                fn_decls[idx].name.clone(),
                TypeScheme::mono(tv.clone()),
                mod_path.to_string(),
                fn_decls[idx].name.clone(),
            );
            pre_bound.push((idx, tv));
        }

        let qual_snap = state.subst.push_qual_scope();
        let scc_result: Result<(), SpannedTypeError> = (|| {
            for &(idx, ref tv) in &pre_bound {
                let decl = fn_decls[idx];
                state.env.push_scope();

                let (type_param_map, type_param_arity) =
                    build_type_param_maps(&decl.type_params, &mut state.gen);
                saved_type_param_maps.insert(idx, type_param_map.clone());
                if !decl.constraints.is_empty() {
                    for constraint in &decl.constraints {
                        if trait_registry
                            .lookup_trait_by_name(&constraint.trait_name)
                            .is_none()
                        {
                            return Err(spanned(
                                TypeError::UnknownTrait {
                                    name: constraint.trait_name.clone(),
                                },
                                constraint.span,
                            ));
                        }
                    }

                    let requirements: Vec<(TraitName, Vec<TypeVarId>)> = decl
                        .constraints
                        .iter()
                        .map(|constraint| {
                            let tv_names = require_param_vars(constraint)?;
                            let tvs: Vec<TypeVarId> = tv_names
                                .iter()
                                .filter_map(|n| type_param_map.get(*n).copied())
                                .collect();
                            if tvs.len() != tv_names.len() || tvs.is_empty() {
                                return Ok(None);
                            }
                            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
                            // Validation deferred to instance resolution phase.
                            let tn = trait_registry
                                .lookup_trait_by_name(&constraint.trait_name)
                                .map(|ti| ti.trait_name())
                                .unwrap_or_else(|| {
                                    TraitName::new(
                                        mod_path.to_string(),
                                        constraint.trait_name.clone(),
                                    )
                                });
                            Ok(Some((tn, tvs)))
                        })
                        .collect::<Result<Vec<Option<_>>, SpannedTypeError>>()?
                        .into_iter()
                        .flatten()
                        .collect();
                    if !requirements.is_empty() {
                        fn_constraint_requirements.insert(decl.name.clone(), requirements);
                    }
                }

                let mut seen_params = HashSet::new();
                for p in &decl.params {
                    if !seen_params.insert(&p.name) {
                        return Err(spanned(
                            TypeError::DuplicateParam {
                                name: p.name.clone(),
                            },
                            p.span,
                        ));
                    }
                }

                let mut param_types = Vec::new();
                for p in &decl.params {
                    let ptv = Type::Var(state.gen.fresh());
                    if let Some(ref ty_expr) = p.ty {
                        let annotated_ty = type_registry::resolve_type_expr(
                            ty_expr,
                            &type_param_map,
                            &type_param_arity,
                            &state.registry,
                            ResolutionContext::UserAnnotation,
                            None,
                        )
                        .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                        .map_err(|e| spanned(e, decl.span))?;
                        // E0109: Consume-mode params with a bare
                        // resource-carrying type must be spelled `~T`.
                        // Borrow modes encode `&` via the mode, not the
                        // type, so the bare spelling is legal there.
                        if matches!(p.mode, crate::types::ParamMode::Consume) {
                            crate::ownership::check_no_bare_resource_use(
                                &annotated_ty,
                                &state.registry,
                                ty_expr.span(),
                                crate::type_error::BareResourceContext::ParamConsume,
                            )?;
                        }
                        unify(&ptv, &annotated_ty, &mut state.subst)
                            .map_err(|e| spanned(e, decl.span))?;
                    }
                    param_types.push(ptv.clone());
                    state.env.bind(p.name.clone(), TypeScheme::mono(ptv));
                }
                let prev_fn_return_type = state.env.fn_return_type.take();
                if let Some(ref ret_ty_expr) = decl.return_type {
                    let resolved_ret = type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, decl.span))?;
                    // E0109: return types are always value positions.
                    crate::ownership::check_no_bare_resource_use(
                        &resolved_ret,
                        &state.registry,
                        ret_ty_expr.span(),
                        crate::type_error::BareResourceContext::Return,
                    )?;
                    state.env.fn_return_type = Some(resolved_ret);
                } else {
                    state.env.fn_return_type = Some(Type::Var(state.gen.fresh()));
                }

                let body_typed = {
                    // Clone the resolved return type so we can pass it as the
                    // bidirectional `expected_type` to the body inference without
                    // keeping an immutable borrow of state.env alongside the
                    // mutable borrow that InferenceContext requires.
                    let fn_ret_expected = state.env.fn_return_type.clone();
                    let mut ctx = InferenceContext {
                        env: &mut state.env,
                        subst: &mut state.subst,
                        gen: &mut state.gen,
                        registry: Some(&state.registry),
                        recur_params: Some(
                            decl.params
                                .iter()
                                .zip(&param_types)
                                .map(|(p, t)| (p.mode, t.clone()))
                                .collect(),
                        ),
                        let_own_spans: Some(&mut state.let_own_spans),
                        lambda_own_captures: Some(&mut state.lambda_own_captures),
                        type_param_map: &type_param_map,
                        type_param_arity: &type_param_arity,
                        qualified_modules: &state.qualified_modules,
                        imported_type_info: &state.imports.imported_type_info,
                        module_path: mod_path,
                        shadowed_prelude_fns: &state.imports.shadowed_prelude_fns,
                        self_type: None,
                        deferred_overloads: &mut deferred_overloads,
                        owning_fn_idx: idx,
                    };
                    ctx.infer_expr_inner(&decl.body, fn_ret_expected.as_ref())?
                };
                state.env.fn_return_type = prev_fn_return_type;
                state.env.pop_scope();

                let param_types: Vec<Type> = param_types.iter().enumerate().map(|(i, t)| {
                let resolved = state.subst.apply(t);
                debug_assert!(
                    !matches!(&resolved, Type::Own(ref inner) if matches!(inner.as_ref(), Type::Own(_))),
                    "Own(Own(_)) should never arise — parser rejects ~~T and no codepath double-wraps: param '{}': {:?}",
                    decl.params.get(i).map(|p| p.name.as_str()).unwrap_or("?"),
                    resolved,
                );
                resolved
            }).collect();
                let body_ty = state.subst.apply(&body_typed.ty);

                let ret_ty = if let Some(ref ret_ty_expr) = decl.return_type {
                    let annotated_ret = type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, decl.span))?;
                    coerce_unify(&body_ty, &annotated_ret, &mut state.subst, Some(&state.registry)).map_err(|e| {
                        if let TypeError::InfiniteType { ref var, ref ty } = e {
                            if crate::type_error::is_own_wrapper_of(*var, ty) {
                                let var_names: Vec<(TypeVarId, String)> = type_param_map
                                    .iter()
                                    .map(|(name, &id)| (id, name.clone()))
                                    .collect();
                                let body_span = match &body_typed.kind {
                                    crate::typed_ast::TypedExprKind::Do(exprs) => {
                                        exprs.last().map_or(body_typed.span, |e| e.span)
                                    }
                                    _ => body_typed.span,
                                };
                                return SpannedTypeError {
                                    error: Box::new(e),
                                    span: body_span,
                                    note: None,
                                    secondary_span: Some(Box::new(SecondaryLabel {
                                        span: ret_ty_expr.span(),
                                        message: "return type declared here".to_string(),
                                        source_file: None,
                                    })),
                                    source_file: None,
                                    var_names: Some(var_names),
                                };
                            }
                        }
                        let mut err = spanned(e, decl.span);
                        if matches!(
                            &*err.error,
                            TypeError::Mismatch { .. }
                                | TypeError::FnCapabilityMismatch { .. }
                                | TypeError::ParamModeMismatch { .. }
                        ) {
                            let terminal = match &body_typed.kind {
                                crate::typed_ast::TypedExprKind::Do(exprs) => {
                                    exprs.last().unwrap_or(&body_typed)
                                }
                                _ => &body_typed,
                            };
                            if let crate::typed_ast::TypedExprKind::Lambda { .. } = &terminal.kind {
                                if let Some(cap_name) =
                                    state.lambda_own_captures.get(&terminal.span)
                                {
                                    err.note = Some(format!(
                                        "closure is single-use because it captures `~` value `{}`",
                                        cap_name
                                    ));
                                }
                            }
                        }
                        err
                    })?;
                    state.subst.apply(&annotated_ret)
                } else {
                    // Preserve `Own` in inferred return types — a body that produces
                    // `~T` should yield a `-> ~T` function. The previous `strip_own`
                    // here silently dropped ownership for inferred returns.
                    body_ty.clone()
                };

                // Use join_types (not unify) to reconcile the inferred fn type with the pre-bound
                // SCC type. This is not a value flow — it's two views of the same function that may
                // differ in Own wrappers (e.g. body infers Int, recursive call bound ~Int from literals).
                let fn_params: Vec<(crate::types::ParamMode, Type)> = decl
                    .params
                    .iter()
                    .zip(param_types.into_iter())
                    .map(|(p, t)| (p.mode, t))
                    .collect();
                let fn_ty = Type::Fn(fn_params, Box::new(ret_ty.clone()));
                crate::unify::join_types(&fn_ty, tv, &mut state.subst, Some(&state.registry))
                    .map_err(|e| spanned(e, decl.span))?;

                fn_bodies[idx] = Some(body_typed);
            }
            Ok(())
        })();
        match &scc_result {
            Ok(()) => state.subst.commit_qual_scope(qual_snap),
            Err(_) => state.subst.rollback_qual_scope(qual_snap),
        }
        scc_result?;

        // Eagerly resolve multi-parameter trait method calls before
        // generalization. Pinning secondary trait params (e.g. `?b = String`)
        // here ensures they don't get quantified into a function's scheme.
        //
        // Build the per-function set of "protected" type vars — the vars
        // bound by each function's declared `[a, b, ...]` type parameters.
        // These must stay abstract through generalization so declared
        // `where` constraints on polymorphic functions are forwarded to
        // callers rather than eagerly pinned to a matching instance.
        let protected_type_vars: Vec<HashSet<TypeVarId>> = (0..fn_bodies.len())
            .map(|idx| {
                saved_type_param_maps
                    .get(&idx)
                    .map(|m| m.values().copied().collect())
                    .unwrap_or_default()
            })
            .collect();
        resolve_multi::resolve_multi_param_constraints(
            &fn_bodies,
            &protected_type_vars,
            trait_registry,
            &mut state.subst,
            &mut state.gen,
        );

        resolve_overloads::resolve_deferred_overloads(
            &mut deferred_overloads,
            &mut fn_bodies,
            &mut state.subst,
            &mut state.gen,
        )?;

        // Generalize against an empty env: all env bindings are either fully-quantified
        // schemes (no free vars) or current-SCC monomorphic bindings whose vars should be
        // generalized. This must change if nested let-polymorphism is added.
        let empty_env = TypeEnv::new();
        for &(idx, ref tv) in &pre_bound {
            let final_ty = state.subst.apply(tv);
            let mut scheme = generalize(&final_ty, &empty_env, &state.subst);
            if let Some(tpm) = saved_type_param_maps.get(&idx) {
                let scheme_var_set: HashSet<TypeVarId> = scheme.vars.iter().copied().collect();
                for (name, &original_id) in tpm {
                    let resolved = state.subst.apply(&Type::Var(original_id));
                    if let Type::Var(final_id) = resolved {
                        if scheme_var_set.contains(&final_id) {
                            scheme.var_names.insert(final_id, name.clone());
                        }
                    }
                }
            }
            let local_source = BindingSource::TopLevelLocalFunction {
                qualified_name: crate::types::BindingQualifiedName {
                    module_path: mod_path.to_string(),
                    local_name: fn_decls[idx].name.clone(),
                },
            };
            let fn_name = fn_decls[idx].name.clone();
            // Check if this name has multiple definitions in this SCC or
            // already has overload candidates (from imports).
            let is_overloaded = pre_bound.iter().filter(|(i, _)| fn_decls[*i].name == fn_name).count() > 1
                || state.env.lookup_entry(&fn_name).is_some_and(|e| e.overload_candidates.is_some());
            if is_overloaded {
                if let Some(existing) = state.env.lookup_entry_mut(&fn_name) {
                    existing.add_overload_candidate(scheme.clone(), local_source);
                } else {
                    state.env.bind_with_source_and_def_span(
                        fn_name,
                        scheme.clone(),
                        local_source,
                        crate::types::DefSpan {
                            span: fn_decls[idx].span,
                            source_module: None,
                        },
                    );
                }
            } else {
                state.env.bind_with_source_and_def_span(
                    fn_name,
                    scheme.clone(),
                    local_source,
                    crate::types::DefSpan {
                        span: fn_decls[idx].span,
                        source_module: None,
                    },
                );
            }
            result_schemes[idx] = Some(scheme);
        }
    }

    // Normalize fn_constraint_requirements
    for requirements in fn_constraint_requirements.values_mut() {
        for (_, type_vars) in requirements.iter_mut() {
            for type_var in type_vars.iter_mut() {
                let resolved = state.subst.apply(&Type::Var(*type_var));
                if let Type::Var(new_id) = resolved {
                    *type_var = new_id;
                }
            }
        }
    }

    // Fold constraints into TypeSchemes so they propagate via normal import mechanisms
    for (idx, decl) in fn_decls.iter().enumerate() {
        if let Some(scheme) = &mut result_schemes[idx] {
            if let Some(reqs) = fn_constraint_requirements.get(&decl.name) {
                scheme.constraints = reqs.clone();
            }
        }
    }

    // Validate explicit trait bounds: fn_decl bodies must not use trait methods on type vars
    // unless the corresponding bound is declared in a `where` clause.
    for (idx, decl) in fn_decls.iter().enumerate() {
        if let Some(body) = &fn_bodies[idx] {
            let mut fn_type_param_vars: HashSet<TypeVarId> = HashSet::new();
            if let Some(scheme) = &result_schemes[idx] {
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
            if fn_type_param_vars.is_empty() {
                continue;
            }
            // Functions without explicit constraints have no entry
            let declared = fn_constraint_requirements
                .get(decl.name.as_str())
                .cloned()
                .unwrap_or_default();
            // Functions without explicit constraints have no entry
            let type_var_names: HashMap<TypeVarId, String> = saved_type_param_maps
                .get(&idx)
                .map(|tpm| tpm.iter().map(|(name, &id)| (id, name.clone())).collect())
                .unwrap_or_default();
            checks::validate_trait_constraints(
                body,
                trait_registry,
                &state.subst,
                &fn_type_param_vars,
                &declared,
                &decl.name,
                &type_var_names,
            )?;
        }
    }

    // Post-inference instance resolution
    // Build fn_schemes map for bind_type_vars resolution (constraints are in TypeSchemes)
    let mut fn_schemes_map: HashMap<String, TypeScheme> = HashMap::new();
    for (decl, scheme) in fn_decls.iter().zip(result_schemes.iter()) {
        if let Some(scheme) = scheme {
            fn_schemes_map.insert(decl.name.clone(), scheme.clone());
        }
    }
    for imp in &state.imports.imported_fn_types {
        fn_schemes_map
            .entry(imp.name.clone())
            .or_insert_with(|| imp.scheme.clone());
    }
    let has_constraints = fn_schemes_map.values().any(|s| !s.constraints.is_empty());
    if !trait_method_map.is_empty() || has_constraints {
        for (body, scheme) in fn_bodies.iter().zip(result_schemes.iter()) {
            if let Some(body) = body {
                // Monomorphic functions have no type variables
                let fn_type_vars: HashSet<TypeVarId> = scheme
                    .as_ref()
                    .map(|s| s.vars.iter().copied().collect())
                    .unwrap_or_default();
                // Monomorphic functions have no type variables
                let scheme_var_names = scheme
                    .as_ref()
                    .map(|s| &s.var_names)
                    .cloned()
                    .unwrap_or_default();
                checks::check_trait_instances(
                    body,
                    trait_registry,
                    &state.subst,
                    &fn_schemes_map,
                    &fn_type_vars,
                    &scheme_var_names,
                )?;
            }
        }
    }

    Ok((
        fn_decls,
        result_schemes,
        fn_bodies,
        fn_constraint_requirements,
    ))
}

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
