use std::collections::HashMap;

use krypton_parser::ast::Span;

use crate::trait_registry::{InstanceInfo, TraitMethod, TraitRegistry};
use crate::type_registry::{self, ResolutionContext};
use crate::typed_ast::{self, TraitName};
use crate::types::{ParamMode, Type, TypeScheme, TypeVarId};
use crate::unify::{coerce_unify, unify, SpannedTypeError, TypeError};

use super::{require_param_vars, spanned, spanned_with_names, InferenceContext, ModuleInferenceState};

/// Output of a committed fork: the typed body plus supporting metadata to
/// be reused by the caller (`typecheck_impl_methods`) when recording the
/// instance method.
///
/// Only the *first* successful fork is committed to the typed module;
/// monomorphization does not per-shape specialize, so the committed typed
/// AST only needs to be well-typed for one instantiation. Later forks are
/// validation-only — they prove that the *other* instantiations also
/// typecheck, but their typed ASTs are discarded.
pub(crate) struct ForkCommit {
    pub(crate) body_typed: crate::typed_ast::TypedExpr,
    pub(crate) method_constraint_pairs: Vec<(TraitName, Vec<TypeVarId>)>,
    pub(crate) fn_ty: Type,
}

/// Run one fork of impl-method body checking under a fork-specific type
/// substitution. Captures the original `typecheck_impl_methods` body-check
/// logic so it can be invoked per-fork during shape-polymorphic
/// dual-checking.
///
/// `fork_apply` materializes concrete types from the trait method signature
/// under the fork's shape-variable bindings. For mono impls a single fork
/// with the primary trait var bound to `resolved_target` reproduces the
/// original single-check behavior.
#[allow(clippy::too_many_arguments)]
pub(crate) fn check_fork<F>(
    state: &mut ModuleInferenceState,
    module_path: &str,
    trait_registry: &TraitRegistry,
    trait_name: &str,
    method: &krypton_parser::ast::FnDecl,
    trait_method: &TraitMethod,
    instance: &InstanceInfo,
    resolved_target: &Type,
    all_intrinsic: bool,
    impl_span: Span,
    fork_apply: &F,
) -> Result<Option<ForkCommit>, SpannedTypeError>
where
    F: Fn(&Type) -> Type,
{
    let concrete_param_types_with_modes: Vec<(ParamMode, Type)> = trait_method
        .param_types
        .iter()
        .map(|(m, t)| (*m, state.subst.apply(&fork_apply(t))))
        .collect();
    let concrete_param_types: Vec<Type> = concrete_param_types_with_modes
        .iter()
        .map(|(_, t)| t.clone())
        .collect();

    let mut impl_method_tpm: HashMap<String, TypeVarId> = instance.type_var_ids.clone();
    let mut impl_method_tpa = HashMap::new();
    for tv_param in &method.type_params {
        if !impl_method_tpm.contains_key(&tv_param.name) {
            impl_method_tpm.insert(tv_param.name.clone(), state.gen.fresh());
            impl_method_tpa.insert(tv_param.name.clone(), tv_param.arity);
        }
    }

    let mut method_constraint_pairs: Vec<(TraitName, Vec<TypeVarId>)> = Vec::new();
    for constraint in &method.constraints {
        let tv_names = require_param_vars(constraint)?;
        let tvs: Vec<TypeVarId> = tv_names
            .iter()
            .filter_map(|n| impl_method_tpm.get(*n).copied())
            .collect();
        if tvs.len() == tv_names.len() && !tvs.is_empty() {
            let tn = trait_registry
                .lookup_trait_by_name(&constraint.trait_name)
                .map(|ti| ti.trait_name())
                .unwrap_or_else(|| {
                    TraitName::new(module_path.to_string(), constraint.trait_name.clone())
                });
            method_constraint_pairs.push((tn, tvs));
        }
    }

    if method.params.len() != concrete_param_types.len() {
        return Err(spanned(
            TypeError::WrongArity {
                expected: concrete_param_types.len(),
                actual: method.params.len(),
            },
            impl_span,
        ));
    }

    for (i, (p, (trait_mode, _))) in method
        .params
        .iter()
        .zip(concrete_param_types_with_modes.iter())
        .enumerate()
    {
        if p.mode != *trait_mode {
            return Err(spanned(
                TypeError::ImplMethodModeMismatch {
                    trait_name: trait_name.to_string(),
                    method_name: method.name.clone(),
                    param_index: i,
                    param_name: p.name.clone(),
                    expected_mode: *trait_mode,
                    actual_mode: p.mode,
                },
                p.span,
            ));
        }
    }

    for (i, p) in method.params.iter().enumerate() {
        if let Some(ref ty_expr) = p.ty {
            if i < concrete_param_types.len() {
                let annotated_ty = type_registry::resolve_type_expr(
                    ty_expr,
                    &impl_method_tpm,
                    &impl_method_tpa,
                    &state.registry,
                    ResolutionContext::UserAnnotation,
                    Some(resolved_target),
                )
                .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                .map_err(|e| spanned(e, p.span))?;
                unify(&annotated_ty, &concrete_param_types[i], &mut state.subst)
                    .map_err(|e| spanned_with_names(e, p.span, &impl_method_tpm))?;
            }
        }
    }
    if let Some(ref ret_ty_expr) = method.return_type {
        let concrete_ret = state.subst.apply(&fork_apply(&trait_method.return_type));
        let annotated_ret = type_registry::resolve_type_expr(
            ret_ty_expr,
            &impl_method_tpm,
            &impl_method_tpa,
            &state.registry,
            ResolutionContext::UserAnnotation,
            Some(resolved_target),
        )
        .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
        .map_err(|e| spanned(e, method.span))?;
        unify(&concrete_ret, &annotated_ret, &mut state.subst).map_err(|e| {
            let error = match e {
                TypeError::WrongArity { .. } => TypeError::Mismatch {
                    expected: concrete_ret.clone(),
                    actual: annotated_ret.clone(),
                },
                other => other,
            };
            spanned_with_names(error, method.span, &impl_method_tpm)
        })?;
    }

    if all_intrinsic {
        let _ = method_constraint_pairs;
        return Ok(None);
    }

    state.env.push_scope();
    let mut param_types_inferred = Vec::new();
    for (i, p) in method.params.iter().enumerate() {
        let ptv = Type::Var(state.gen.fresh());
        if i < concrete_param_types.len() {
            if let Err(e) = unify(&ptv, &concrete_param_types[i], &mut state.subst) {
                state.env.pop_scope();
                return Err(spanned(e, impl_span));
            }
        }
        param_types_inferred.push(ptv.clone());
        state.env.bind(p.name.clone(), TypeScheme::mono(ptv));
    }
    let prev_fn_return_type = state.env.fn_return_type.take();
    let concrete_ret_type = state.subst.apply(&fork_apply(&trait_method.return_type));
    state.env.fn_return_type = Some(concrete_ret_type);

    let impl_qual_snap = state.subst.push_qual_scope();
    let mut impl_deferred = Vec::new();
    let body_result = {
        let fn_ret_expected = state.env.fn_return_type.clone();
        let mut ctx = InferenceContext {
            env: &mut state.env,
            subst: &mut state.subst,
            gen: &mut state.gen,
            registry: Some(&state.registry),
            recur_params: Some(
                method
                    .params
                    .iter()
                    .zip(&param_types_inferred)
                    .map(|(p, t)| (p.mode, t.clone()))
                    .collect(),
            ),
            let_own_spans: Some(&mut state.let_own_spans),
            lambda_own_captures: Some(&mut state.lambda_own_captures),
            type_param_map: &impl_method_tpm,
            type_param_arity: &impl_method_tpa,
            qualified_modules: &state.qualified_modules,
            imported_type_info: &state.imports.imported_type_info,
            module_path,
            shadowed_prelude_fns: &state.imports.shadowed_prelude_fns,
            self_type: Some(resolved_target.clone()),
            deferred_overloads: &mut impl_deferred,
            owning_fn_idx: 0,
        };
        ctx.infer_expr_inner(&method.body, fn_ret_expected.as_ref())
    };
    state.env.fn_return_type = prev_fn_return_type;
    state.env.pop_scope();
    match &body_result {
        Ok(_) => state.subst.commit_qual_scope(impl_qual_snap),
        Err(_) => {
            state.subst.rollback_qual_scope(impl_qual_snap);
        }
    }
    let mut body_typed = body_result?;
    typed_ast::apply_subst(&mut body_typed, &state.subst);

    let final_param_types: Vec<Type> = param_types_inferred
        .iter()
        .map(|t| state.subst.apply(t))
        .collect();
    let final_ret_type = state.subst.apply(&body_typed.ty);

    let expected_ret_type = state.subst.apply(&fork_apply(&trait_method.return_type));
    coerce_unify(&final_ret_type, &expected_ret_type, &mut state.subst, Some(&state.registry)).map_err(|_| {
        spanned_with_names(
            TypeError::Mismatch {
                expected: expected_ret_type.clone(),
                actual: final_ret_type.clone(),
            },
            method.span,
            &impl_method_tpm,
        )
    })?;

    let fn_params: Vec<(crate::types::ParamMode, Type)> = method
        .params
        .iter()
        .zip(final_param_types.clone())
        .map(|(p, t)| (p.mode, t))
        .collect();
    let fn_ty = Type::Fn(fn_params, Box::new(final_ret_type.clone()));

    let _ = final_param_types;
    let _ = final_ret_type;
    Ok(Some(ForkCommit {
        body_typed,
        method_constraint_pairs,
        fn_ty,
    }))
}
