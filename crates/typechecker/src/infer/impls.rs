use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Decl, Expr, Module, Span, TypeConstraint};

use crate::trait_name_resolver::TraitNameResolver;
use crate::trait_registry::{InstanceInfo, TraitRegistry};
use crate::type_registry::{self, ResolutionContext};
use crate::typed_ast::{self, ExternFnInfo, InstanceDefInfo, ResolvedConstraint, TraitName};
use crate::types::{type_to_canonical_name, Type, TypeScheme, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::display::substitute_type_var;
use super::fork::{check_fork, ForkCommit};
use super::helpers::{
    collect_type_expr_var_names, duplicate_instance_spanned, free_vars, free_vars_ordered,
    require_param_vars, resolve_impl_target, spanned, spanned_with_names, strip_anon_type_args,
    validate_impl_wildcards,
};
use super::state::ModuleInferenceState;

/// Resolve parser `TypeConstraint`s (bare string trait names) to `ResolvedConstraint`s
/// using the trait registry to look up the full `TraitName`.
// TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
// Validation deferred to instance resolution phase.
pub(super) fn resolve_constraints(
    constraints: &[TypeConstraint],
    trait_registry: &TraitRegistry,
    trait_names: &TraitNameResolver,
    module_path: &str,
) -> Result<Vec<ResolvedConstraint>, SpannedTypeError> {
    constraints
        .iter()
        .map(|tc| {
            let tv_names = require_param_vars(tc)?;
            Ok(ResolvedConstraint {
                trait_name: trait_names
                    .resolve(&tc.trait_name)
                    .and_then(|tn| trait_registry.lookup_trait(tn))
                    .map(|ti| ti.trait_name())
                    .unwrap_or_else(|| {
                        TraitName::new(module_path.to_string(), tc.trait_name.clone())
                    }),
                type_vars: tv_names.iter().map(|s| s.to_string()).collect(),
                span: tc.span,
            })
        })
        .collect()
}
pub(super) fn register_impl_instances(
    state: &mut ModuleInferenceState,
    trait_registry: &mut TraitRegistry,
    module: &Module,
    module_path: &str,
) -> Result<(), SpannedTypeError> {
    // Collect locally-defined trait names for orphan check
    let local_trait_names: FxHashSet<String> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefTrait { name, .. } => Some(name.clone()),
            // Extern traits (`extern java "..." as trait Foo[a]`) are local trait definitions
            // and should be treated as such for the orphan check.
            Decl::Extern {
                is_trait: true,
                alias: Some(name),
                ..
            } => Some(name.clone()),
            _ => None,
        })
        .collect();

    // Process DefImpl declarations (register instances)
    for decl in &module.decls {
        if let Decl::DefImpl {
            trait_name,
            type_args,
            type_params,
            type_constraints,
            methods,
            span,
            ..
        } = decl
        {
            // Compute total wildcard count across all type args.
            let mut wildcard_count = 0usize;
            for arg in type_args {
                wildcard_count += validate_impl_wildcards(arg).map_err(|e| spanned(e, *span))?;
            }

            let type_param_map: FxHashMap<String, TypeVarId> = if !type_params.is_empty() {
                type_params
                    .iter()
                    .map(|tp| (tp.name.clone(), state.gen.fresh()))
                    .collect()
            } else {
                let mut impl_type_param_names = FxHashSet::default();
                for arg in type_args {
                    collect_type_expr_var_names(arg, &mut impl_type_param_names);
                }
                for constraint in type_constraints {
                    let tv_names = require_param_vars(constraint)?;
                    for n in tv_names {
                        impl_type_param_names.insert(n.to_string());
                    }
                }
                let mut sorted_names: Vec<_> = impl_type_param_names.into_iter().collect();
                sorted_names.sort();
                sorted_names
                    .into_iter()
                    .map(|name| (name, state.gen.fresh()))
                    .collect()
            };
            let type_param_arity: FxHashMap<String, usize> = FxHashMap::default();

            // Resolve each type argument into a concrete `Type`.
            let mut resolved_targets: Vec<Type> = Vec::with_capacity(type_args.len());
            for arg in type_args {
                let arg_wildcards = validate_impl_wildcards(arg).map_err(|e| spanned(e, *span))?;
                let resolved = if arg_wildcards > 0 {
                    resolve_impl_target(
                        arg,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        &mut state.gen,
                    )
                    .map_err(|e| spanned(e, *span))?
                } else {
                    type_registry::resolve_type_expr(
                        arg,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, *span))?
                };
                resolved_targets.push(resolved);
            }

            // D.2: reject `impl Disposable[<fn type>]` before orphan/well-formedness
            // so the user sees a targeted diagnostic. `~fn` is structurally Linear
            // and consumed by calling it; no separate `dispose` step exists.
            if trait_name == "Disposable" {
                for rt in &resolved_targets {
                    let inner = match rt {
                        Type::Own(inner) => inner.as_ref(),
                        other => other,
                    };
                    if matches!(inner, Type::Fn(_, _)) {
                        return Err(spanned(
                            TypeError::InvalidDisposableInstance {
                                ty: format!("{}", rt),
                            },
                            *span,
                        ));
                    }
                }
            }

            // Classify each arg for orphan checking: determine whether the arg's
            // head-type is locally defined, and collect a list of modules that
            // were consulted so we can report them in a helpful error message.
            let trait_is_local = local_trait_names.contains(trait_name);
            let mut any_arg_is_local = false;
            let mut modules_checked: Vec<String> = Vec::new();
            if trait_is_local {
                modules_checked.push(module_path.to_string());
                any_arg_is_local = true; // trait locality alone satisfies the rule
            }
            // Also validate well-formedness per arg (unknown type, owned type).
            for rt in &resolved_targets {
                match rt {
                    Type::Named(name, _) => {
                        if state.registry.lookup_type(name).is_none() {
                            return Err(spanned(
                                TypeError::OrphanInstance {
                                    trait_name: trait_name.clone(),
                                    ty: name.clone(),
                                    modules_checked: modules_checked.clone(),
                                },
                                *span,
                            ));
                        }
                        if let Some((src, _)) = state.imports.imported_type_info.get(name) {
                            modules_checked.push(src.clone());
                        } else {
                            modules_checked.push(module_path.to_string());
                            any_arg_is_local = true;
                        }
                    }
                    Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit => {
                        modules_checked.push("<builtin>".to_string());
                    }
                    Type::Fn(_, _) | Type::Tuple(_) => {
                        // Fn / Tuple types are structural — they have no defining
                        // module and cannot satisfy the orphan rule on their own.
                        modules_checked.push("<structural>".to_string());
                    }
                    Type::Var(_) => {
                        // Type parameters carry no locality information.
                    }
                    Type::Own(inner) => {
                        return Err(spanned(
                            TypeError::OwnedTypeImpl {
                                trait_name: trait_name.clone(),
                                ty: format!("{}", inner),
                            },
                            *span,
                        ));
                    }
                    other => {
                        return Err(spanned(
                            TypeError::OrphanInstance {
                                trait_name: trait_name.clone(),
                                ty: format!("{}", other),
                                modules_checked: modules_checked.clone(),
                            },
                            *span,
                        ));
                    }
                }
            }

            // Final orphan check: either the trait is local, or at least one type
            // argument has its head type defined locally.
            let joined_display = {
                let names: rustc_hash::FxHashMap<crate::types::TypeVarId, &str> = type_param_map
                    .iter()
                    .map(|(n, &id)| (id, n.as_str()))
                    .collect();
                resolved_targets
                    .iter()
                    .map(|rt| {
                        if type_param_map.is_empty() {
                            format!("{}", rt.renumber_for_display())
                        } else {
                            crate::types::format_type_with_var_map(rt, &names)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            if !trait_is_local && !any_arg_is_local {
                return Err(spanned(
                    TypeError::OrphanInstance {
                        trait_name: trait_name.clone(),
                        ty: joined_display.clone(),
                        modules_checked: modules_checked.clone(),
                    },
                    *span,
                ));
            }

            // Compute `target_name` for KindMismatch and InvalidImpl error messages
            // (still keyed on the first type argument for single-HK traits).
            let target_name = match &resolved_targets[0] {
                Type::Named(name, _) => name.clone(),
                Type::Int => "Int".to_string(),
                Type::Float => "Float".to_string(),
                Type::Bool => "Bool".to_string(),
                Type::String => "String".to_string(),
                Type::Unit => "Unit".to_string(),
                _ => format!("{}", resolved_targets[0]),
            };
            let target_display_name = joined_display.clone();

            for constraint in type_constraints {
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

            if let Some(trait_info) = state.resolve_trait(trait_registry, trait_name) {
                let expected_arity = trait_info.type_var_arity;
                if expected_arity > 0 {
                    if wildcard_count > 0 {
                        if wildcard_count != expected_arity {
                            return Err(spanned(
                                TypeError::KindMismatch {
                                    type_name: target_name.clone(),
                                    expected_arity,
                                    actual_arity: wildcard_count,
                                },
                                *span,
                            ));
                        }
                    } else {
                        let actual_arity = state.registry.expected_arity(&target_name).unwrap_or(0);
                        if actual_arity != expected_arity {
                            return Err(spanned(
                                TypeError::KindMismatch {
                                    type_name: target_name.clone(),
                                    expected_arity,
                                    actual_arity,
                                },
                                *span,
                            ));
                        }
                    }
                }

                let expected_methods: FxHashSet<&str> =
                    trait_info.methods.iter().map(|m| m.name.as_str()).collect();
                let actual_methods: FxHashSet<&str> =
                    methods.iter().map(|m| m.name.as_str()).collect();
                let missing_methods: Vec<String> = trait_info
                    .methods
                    .iter()
                    .filter(|m| !actual_methods.contains(m.name.as_str()))
                    .map(|m| m.name.clone())
                    .collect();
                let extra_methods: Vec<String> = methods
                    .iter()
                    .filter(|m| !expected_methods.contains(m.name.as_str()))
                    .map(|m| m.name.clone())
                    .collect();
                if !missing_methods.is_empty() || !extra_methods.is_empty() {
                    return Err(spanned_with_names(
                        TypeError::InvalidImpl {
                            trait_name: trait_name.clone(),
                            target_type: target_display_name.clone(),
                            missing_methods,
                            extra_methods,
                        },
                        *span,
                        &type_param_map,
                    ));
                }
            }

            let target_type_name = resolved_targets
                .iter()
                .map(type_to_canonical_name)
                .collect::<Vec<_>>()
                .join("$$");
            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
            // Validation deferred to instance resolution phase.
            let impl_full_trait_name = state
                .resolve_trait(trait_registry, trait_name)
                .map(|ti| ti.trait_name())
                .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));
            let resolved_constraints = resolve_constraints(
                type_constraints,
                trait_registry,
                &state.trait_names,
                module_path,
            )?;
            let instance = InstanceInfo {
                trait_name: impl_full_trait_name,
                target_types: resolved_targets,
                target_type_name,
                type_var_ids: type_param_map.clone(),
                constraints: resolved_constraints,
                span: *span,
                is_builtin: false,
            };

            trait_registry
                .check_superclasses(&instance)
                .map_err(|e| spanned(e, *span))?;

            trait_registry
                .register_instance(instance)
                .map_err(|boxed| {
                    let (e, existing_span) = *boxed;
                    duplicate_instance_spanned(e, *span, existing_span)
                })?;
        }
    }
    Ok(())
}
pub(super) fn typecheck_impl_methods(
    state: &mut ModuleInferenceState,
    module: &Module,
    module_path: &str,
    trait_registry: &TraitRegistry,
    _trait_method_map: &FxHashMap<String, TraitName>,
    _extern_fns: &[ExternFnInfo],
) -> Result<Vec<InstanceDefInfo>, SpannedTypeError> {
    let mut instance_defs: Vec<InstanceDefInfo> = Vec::new();

    for decl in &module.decls {
        if let Decl::DefImpl {
            trait_name,
            type_args: _,
            methods,
            span,
            ..
        } = decl
        {
            let resolved_trait_name = match state.trait_names.resolve(trait_name) {
                Some(tn) => tn.clone(),
                None => {
                    return Err(spanned(
                        TypeError::UnknownTrait {
                            name: trait_name.clone(),
                        },
                        *span,
                    ));
                }
            };
            let trait_info = trait_registry
                .lookup_trait(&resolved_trait_name)
                .expect("resolver maps to a trait_registry entry by construction");
            let impl_trait_name = trait_info.trait_name();
            let tv_id = trait_info.type_var_id;

            let instance = trait_registry
                .find_instance_by_trait_and_span(&impl_trait_name, *span)
                .unwrap();
            // Bind every trait type variable to its concrete instance target.
            // Applies uniformly to single-param, non-HK multi-param, and
            // multi-param HK traits. Position 0 of an HK trait is partial-applied:
            // strip anonymous type args so the binding acts as a partial
            // constructor (e.g. `Named("Result", [Var(e), Var(anon)])` →
            // `Named("Result", [Var(e)])`). All other positions are bound
            // directly to the registered instance target.
            //
            // This binding loop also closes a soundness gap for non-HK
            // multi-param traits: previously only position 0 was bound,
            // leaving positions 1+ freshened so the user annotation could pin
            // them to anything; now all positions are bound to the registered
            // instance target before body inference.
            let mut trait_target_bindings: FxHashMap<TypeVarId, Type> =
                FxHashMap::with_capacity_and_hasher(
                    trait_info.type_var_ids.len(),
                    rustc_hash::FxBuildHasher,
                );
            for (i, &trait_tv) in trait_info.type_var_ids.iter().enumerate() {
                let raw = &instance.target_types[i];
                let bound = if i == 0 && trait_info.type_var_arity > 0 {
                    strip_anon_type_args(raw, &instance.type_var_ids)
                } else {
                    raw.clone()
                };
                trait_target_bindings.insert(trait_tv, bound);
            }

            // Position 0 is preserved for `check_fork`'s `Some(resolved_target.clone())`
            // self-type and for the existing single-param shape-var special case.
            let resolved_target = trait_target_bindings
                .get(&tv_id)
                .cloned()
                .expect("trait_info.type_var_ids[0] == tv_id by construction");
            let target_type_name = instance.target_type_name.clone();

            let mut instance_methods = Vec::new();

            let all_intrinsic = methods.iter().all(|m| {
                matches!(&*m.body, Expr::App { func, args, .. }
                    if args.is_empty() && matches!(func.as_ref(), Expr::Var { name, .. } if name == "__krypton_intrinsic"))
            });

            for method in methods {
                let trait_method = trait_info
                    .methods
                    .iter()
                    .find(|m| m.name == method.name)
                    .unwrap();

                // Shape-polymorphic dual-check: when a trait method signature
                // mentions `shape a`, the impl body must typecheck for every
                // legal value form of `a` (plain and owned). Collect the shape
                // variables — both the trait primary (`tv_id`) and any
                // secondary trait / method vars that appear inside a `Shape(_)`
                // wrapper — so we can enumerate forks below.
                let shape_vars: Vec<TypeVarId> = {
                    let mut out: Vec<TypeVarId> = Vec::new();
                    let mut seen: FxHashSet<TypeVarId> = FxHashSet::default();
                    for (_, pt) in &trait_method.param_types {
                        for v in crate::types::collect_shape_vars(pt) {
                            if seen.insert(v) {
                                out.push(v);
                            }
                        }
                    }
                    for v in crate::types::collect_shape_vars(&trait_method.return_type) {
                        if seen.insert(v) {
                            out.push(v);
                        }
                    }
                    out
                };

                // For each shape variable, determine its candidate bindings.
                // A shape var that is *some* trait position with a concrete
                // instance target binds to that target; a shape var that is a
                // trait position with a non-concrete (Var/parametric) target,
                // or a non-trait method-local var, forks on (Plain, Owned).
                // This correctly extends the single-param HK special case to
                // multi-param HK, where any subset of trait vars may be a
                // shape var.
                #[derive(Clone)]
                enum ShapeCandidate {
                    Concrete(Type),
                    Plain,
                    Owned,
                }
                let mut per_var_candidates: Vec<(TypeVarId, Vec<ShapeCandidate>)> = Vec::new();
                for &sv in &shape_vars {
                    let concrete_target = trait_target_bindings
                        .get(&sv)
                        .filter(|t| free_vars(t).is_empty());
                    match concrete_target {
                        Some(t) => {
                            per_var_candidates.push((sv, vec![ShapeCandidate::Concrete(t.clone())]))
                        }
                        None => per_var_candidates
                            .push((sv, vec![ShapeCandidate::Plain, ShapeCandidate::Owned])),
                    }
                }

                // Cartesian product over shape var candidate sets. Empty shape
                // vars means a single fork with no overrides; all shape vars
                // concrete mono gives a single fork too — both reuse the
                // existing single-check code path.
                let mut combos: Vec<Vec<(TypeVarId, ShapeCandidate)>> = vec![vec![]];
                for (sv, cands) in &per_var_candidates {
                    let mut next: Vec<Vec<(TypeVarId, ShapeCandidate)>> =
                        Vec::with_capacity(combos.len() * cands.len());
                    for c in cands {
                        for existing in &combos {
                            let mut row = existing.clone();
                            row.push((*sv, c.clone()));
                            next.push(row);
                        }
                    }
                    combos = next;
                }
                assert!(combos.len() <= 64, "shape cap is 6 → at most 64 forks");

                // Track the committed fork's typed output so the post-loop
                // bookkeeping can push it into `instance_methods`. The first
                // successful fork wins; later forks are validation-only —
                // their typed ASTs are discarded and any ownership metadata
                // they wrote to `state.let_own_spans` / `state.lambda_own_captures`
                // is rolled back so the committed fork's metadata is not
                // unioned with later forks. After the loop, the committed
                // fork's captured metadata is restored.
                let mut committed: Option<ForkCommit> = None;
                let mut committed_metadata: Option<(FxHashSet<Span>, FxHashMap<Span, String>)> =
                    None;
                let mut dual_check_failure: Option<(String, SpannedTypeError)> = None;
                let is_multi_fork = combos.len() > 1;
                let pre_loop_let_own_spans = state.let_own_spans.clone();
                let pre_loop_lambda_own_captures = state.lambda_own_captures.clone();

                for combo in &combos {
                    // Per-fork freshening + shape-var overrides. Each fork
                    // allocates its own fresh vars so the subst map grows
                    // monotonically but fork reasoning stays independent.
                    let mut fork_overrides: FxHashMap<TypeVarId, Type> = FxHashMap::default();
                    let mut form_label_parts: Vec<String> = Vec::new();
                    let shape_var_names = &trait_info.type_var_names;
                    for (sv, cand) in combo {
                        let replacement = match cand {
                            ShapeCandidate::Concrete(t) => t.clone(),
                            ShapeCandidate::Plain => Type::Var(state.gen.fresh()),
                            ShapeCandidate::Owned => {
                                Type::Own(Box::new(Type::Var(state.gen.fresh())))
                            }
                        };
                        let name = trait_info
                            .type_var_ids
                            .iter()
                            .position(|id| id == sv)
                            .and_then(|idx| shape_var_names.get(idx).cloned())
                            .unwrap_or_else(|| format!("{}", sv));
                        let form = match cand {
                            ShapeCandidate::Concrete(t) => format!("{} = {}", name, t),
                            ShapeCandidate::Plain => format!("{} = T (plain)", name),
                            ShapeCandidate::Owned => format!("{} = ~T (owned)", name),
                        };
                        form_label_parts.push(form);
                        fork_overrides.insert(*sv, replacement);
                    }
                    // Bind every trait type variable to its declared instance
                    // target, unless the per-shape-var loop already wrote a
                    // fork-specific override (Plain/Owned for free shape
                    // positions). Handles single-param HK, non-HK multi-param,
                    // and multi-param HK uniformly.
                    for (&trait_tv, target_ty) in &trait_target_bindings {
                        fork_overrides
                            .entry(trait_tv)
                            .or_insert_with(|| target_ty.clone());
                    }
                    let form_label = if form_label_parts.is_empty() {
                        String::new()
                    } else {
                        form_label_parts.join(", ")
                    };

                    // Freshen trait's secondary/method vars that are NOT shape
                    // vars (those are handled above via fork_overrides).
                    // Walk vars in left-to-right encounter order so fresh-id
                    // allocation is deterministic across processes (FxHashSet
                    // iteration depends on RandomState seed).
                    let mut extra_subst: FxHashMap<TypeVarId, Type> = FxHashMap::default();
                    for (_, pt) in &trait_method.param_types {
                        for v in free_vars_ordered(pt) {
                            if v != tv_id && !fork_overrides.contains_key(&v) {
                                extra_subst
                                    .entry(v)
                                    .or_insert_with(|| Type::Var(state.gen.fresh()));
                            }
                        }
                    }
                    for v in free_vars_ordered(&trait_method.return_type) {
                        if v != tv_id && !fork_overrides.contains_key(&v) {
                            extra_subst
                                .entry(v)
                                .or_insert_with(|| Type::Var(state.gen.fresh()));
                        }
                    }
                    let fork_apply = |ty: &Type| -> Type {
                        let mut out = ty.clone();
                        for (old_id, new_ty) in &extra_subst {
                            out = substitute_type_var(&out, *old_id, new_ty);
                        }
                        for (old_id, new_ty) in &fork_overrides {
                            out = substitute_type_var(&out, *old_id, new_ty);
                        }
                        out
                    };

                    let fork_result = check_fork(
                        state,
                        module_path,
                        trait_registry,
                        trait_name,
                        method,
                        trait_method,
                        instance,
                        &resolved_target,
                        all_intrinsic,
                        *span,
                        &fork_apply,
                    );
                    match fork_result {
                        Ok(result) => {
                            if committed.is_none() && !all_intrinsic {
                                committed = Some(result.expect(
                                    "non-intrinsic check_fork must yield Some(ForkCommit)",
                                ));
                                // Capture the committed fork's post-inference
                                // metadata so we can restore it after all
                                // validation forks finish.
                                committed_metadata = Some((
                                    state.let_own_spans.clone(),
                                    state.lambda_own_captures.clone(),
                                ));
                            }
                        }
                        Err(err_with_label) => {
                            if dual_check_failure.is_none() {
                                dual_check_failure = Some((form_label, err_with_label));
                            }
                        }
                    }
                    // Roll back to pre-loop metadata so the next fork runs
                    // against a clean slate and later forks cannot leak
                    // per-span metadata into the committed fork's AST.
                    state.let_own_spans = pre_loop_let_own_spans.clone();
                    state.lambda_own_captures = pre_loop_lambda_own_captures.clone();
                }

                // Restore the committed fork's metadata so downstream
                // ownership checking reads exactly what the committed fork
                // observed.
                if let Some((spans, caps)) = committed_metadata {
                    state.let_own_spans = spans;
                    state.lambda_own_captures = caps;
                }

                if let Some((failing_form, inner_err)) = dual_check_failure {
                    if is_multi_fork {
                        return Err(spanned(
                            TypeError::ShapeImplDualCheckFailure {
                                trait_name: trait_name.clone(),
                                method_name: method.name.clone(),
                                failing_form,
                                inner: inner_err.error,
                            },
                            method.span,
                        ));
                    } else {
                        return Err(inner_err);
                    }
                }

                if all_intrinsic {
                    continue;
                }

                let ForkCommit {
                    body_typed,
                    method_constraint_pairs,
                    fn_ty,
                } = committed
                    .expect("check_fork returned no error and no commit for non-intrinsic impl");
                let scheme = TypeScheme {
                    vars: vec![],
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: FxHashMap::default(),
                };
                instance_methods.push(typed_ast::InstanceMethod {
                    name: method.name.clone(),
                    params: method
                        .params
                        .iter()
                        .map(|p| crate::typed_ast::TypedParam {
                            name: p.name.clone(),
                            mode: p.mode,
                        })
                        .collect(),
                    body: body_typed,
                    scheme,
                    constraint_pairs: method_constraint_pairs,
                });
            }

            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
            // Validation deferred to instance resolution phase.
            let inst_trait_name = state
                .resolve_trait(trait_registry, trait_name)
                .map(|ti| ti.trait_name())
                .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));
            // Preserve the full multi-param tuple; only the first is used for
            // resolution today, but downstream IR must see the real shape.
            let full_target_types = instance.target_types.clone();
            instance_defs.push(InstanceDefInfo {
                trait_name: inst_trait_name,
                target_type_name,
                target_types: full_target_types,
                type_var_ids: instance.type_var_ids.clone(),
                constraints: instance.constraints.clone(),
                methods: instance_methods,
                sub_dict_requirements: Vec::new(),
                is_intrinsic: all_intrinsic,
            });
        }
    }

    Ok(instance_defs)
}
