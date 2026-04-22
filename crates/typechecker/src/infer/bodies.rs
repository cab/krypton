use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Decl, Module, Visibility};

use crate::scc;
use crate::trait_registry::TraitRegistry;
use crate::type_registry::{self, ResolutionContext};
use crate::typed_ast::{ExternFnInfo, TraitName, TypedExpr};
use crate::types::{BindingSource, Type, TypeEnv, TypeScheme, TypeVarId};
use crate::unify::{coerce_unify, unify, SecondaryLabel, SpannedTypeError, TypeError};

use super::checks;
use super::expr::{self, InferenceContext};
use super::helpers::{build_type_param_maps, free_vars, generalize, require_param_vars, spanned};
use super::resolve_multi;
use super::resolve_overloads;
use super::state::{InferFunctionBodiesResult, ModuleInferenceState};

pub(super) fn infer_function_bodies<'a>(
    state: &mut ModuleInferenceState,
    module: &'a Module,
    _extern_fns: &[ExternFnInfo],
    trait_registry: &TraitRegistry,
    trait_method_map: &FxHashMap<String, TraitName>,
    mod_path: &str,
) -> Result<InferFunctionBodiesResult<'a>, Vec<SpannedTypeError>> {
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
                return Err(vec![spanned(
                    TypeError::MissingPubAnnotation {
                        fn_name: decl.name.clone(),
                        missing,
                    },
                    decl.span,
                )]);
            }
        }
    }

    let adj = scc::build_dependency_graph(&fn_decls);
    let sccs = scc::tarjan_scc(&adj);

    let mut result_schemes: Vec<Option<TypeScheme>> = vec![None; fn_decls.len()];
    let mut fn_bodies: Vec<Option<TypedExpr>> = vec![None; fn_decls.len()];
    // Name-keyed: when two local overloads both declare constraints, the
    // later insert overwrites the earlier. Harmless today because Krypton
    // overloads do not carry distinct `where`-constraint clauses in any
    // exercised fixture, and implicit body-detected constraints are merged
    // (not overwritten). A future per-overload constraint API would rekey
    // this to `(name, decl_idx)` — leaving name-keyed now to avoid rippling
    // the rekey through consumers in this phase.
    let mut fn_constraint_requirements: FxHashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> =
        FxHashMap::default();
    let mut saved_type_param_maps: FxHashMap<usize, FxHashMap<String, TypeVarId>> =
        FxHashMap::default();

    for component in &sccs {
        let mut deferred_overloads: Vec<expr::DeferredOverload> = Vec::new();
        let mut deferred_id_counter: u32 = 0;
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
                        if state
                            .resolve_trait(trait_registry, &constraint.trait_name)
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
                            let tn = state
                                .resolve_trait(trait_registry, &constraint.trait_name)
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

                let mut seen_params = FxHashSet::default();
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
                        deferred_id_counter: &mut deferred_id_counter,
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
                    coerce_unify(
                        &body_ty,
                        &annotated_ret,
                        &mut state.subst,
                        Some(&state.registry),
                    )
                    .map_err(|e| {
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
        scc_result.map_err(|e| vec![e])?;

        // Eagerly resolve multi-parameter trait method calls before
        // generalization. Pinning secondary trait params (e.g. `?b = String`)
        // here ensures they don't get quantified into a function's scheme.
        //
        // Build the per-function set of "protected" type vars — the vars
        // bound by each function's declared `[a, b, ...]` type parameters.
        // These must stay abstract through generalization so declared
        // `where` constraints on polymorphic functions are forwarded to
        // callers rather than eagerly pinned to a matching instance.
        let protected_type_vars: Vec<FxHashSet<TypeVarId>> = (0..fn_bodies.len())
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
                let scheme_var_set: FxHashSet<TypeVarId> = scheme.vars.iter().copied().collect();
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
            let is_overloaded = pre_bound
                .iter()
                .filter(|(i, _)| fn_decls[*i].name == fn_name)
                .count()
                > 1
                || state
                    .env
                    .lookup_entry(&fn_name)
                    .is_some_and(|e| e.overload_candidates.is_some());
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
    // Minimize declared constraints before the unconditional fold below writes
    // them into result_schemes. A user-written redundant where clause (e.g.
    // `where Functor[a], Monad[a]` where Functor is a superclass of Monad)
    // must be collapsed here or the redundancy will survive into scheme
    // constraints and cause spurious dict parameters at codegen.
    //
    // Why this can't be deferred to assemble_typed_module's companion drop:
    // its fold into results/exported_fn_types is guarded by `is_empty()` on
    // the existing scheme.constraints (to protect imported fn schemes from
    // being clobbered via local-name shadowing), so it cannot overwrite the
    // set folded here. The companion drop still runs — it minimizes the
    // in-flight fn_constraint_requirements dict after implicit-constraint
    // detection merges into it — but it only reaches scheme.constraints for
    // schemes whose slot is still empty (i.e. locals without declared
    // constraints).
    for reqs in fn_constraint_requirements.values_mut() {
        trait_registry.drop_entailed_constraints(reqs);
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
            let mut fn_type_param_vars: FxHashSet<TypeVarId> = FxHashSet::default();
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
            let type_var_names: FxHashMap<TypeVarId, String> = saved_type_param_maps
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
            )
            .map_err(|e| vec![e])?;
        }
    }

    // Post-inference instance resolution
    // Build fn_schemes map for bind_type_vars resolution (constraints are in TypeSchemes)
    let mut fn_schemes_map: FxHashMap<String, TypeScheme> = FxHashMap::default();
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
                let fn_type_vars: FxHashSet<TypeVarId> = scheme
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
                )
                .map_err(|e| vec![e])?;
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
