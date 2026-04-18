use krypton_parser::ast::Span;

use crate::typed_ast::{OverloadSignature, ResolvedBindingRef, TypedExpr, TypedExprKind};
use crate::types::{ParamMode, Substitution, Type, TypeVarGen};
use crate::unify::{unify, SpannedTypeError, TypeError};

use super::expr::{contains_type_var, DeferredOverload};

/// Build an `OverloadSignature` from a (substitution-applied) function type,
/// stripping any outer `Own` wrapper. Mirrors `expr::make_overload_signature`
/// but without an inference context — deferred resolution operates on types
/// that have already had the substitution applied.
fn make_overload_signature_from(fn_ty: &Type) -> Option<OverloadSignature> {
    match fn_ty {
        Type::Fn(params, ret) => Some(OverloadSignature {
            param_types: params.iter().map(|(_, t)| t.clone()).collect(),
            return_type: (**ret).clone(),
        }),
        Type::Own(inner) => make_overload_signature_from(inner),
        _ => None,
    }
}

/// Resolve deferred overload calls after full body inference.
///
/// Mirrors the fixed-point pattern of `resolve_multi_param_constraints`:
/// repeatedly re-apply substitution and re-filter candidates until
/// no more progress is made.
pub(super) fn resolve_deferred_overloads(
    deferred: &mut Vec<DeferredOverload>,
    fn_bodies: &mut [Option<TypedExpr>],
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<(), SpannedTypeError> {
    if deferred.is_empty() {
        return Ok(());
    }

    // Fixed-point loop
    loop {
        let mut progress = false;

        let mut i = 0;
        while i < deferred.len() {
            // Re-apply substitution to arg types
            let arg_types: Vec<Type> = deferred[i]
                .arg_types
                .iter()
                .map(|t| subst.apply(t))
                .collect();

            let still_unsolved = arg_types.iter().any(contains_type_var);

            // Re-filter candidates
            let mut matches: Vec<(usize, crate::overload::CandidateMatch)> = Vec::new();
            for (ci, c) in deferred[i].candidates.iter().enumerate() {
                if let Some(m) =
                    crate::overload::candidate_matches(&c.scheme, &arg_types, gen)
                {
                    matches.push((ci, m));
                }
            }

            match matches.len() {
                1 => {
                    // Resolved! Commit and patch.
                    let entry = deferred.remove(i);
                    let (winner_idx, winner_match) = matches.into_iter().next().unwrap();
                    let winning = &entry.candidates[winner_idx];
                    let func_ty = winner_match.instantiated_ty;

                    subst.merge_type_bindings(winner_match.local_subst);

                    // Unify return type
                    let resolved_func_ty = subst.apply(&func_ty);
                    let ret_ty = extract_return_type(&resolved_func_ty)
                        .unwrap_or_else(|| subst.apply(&func_ty));
                    let _ = unify(&Type::Var(entry.ret_type_var), &ret_ty, subst);

                    // Extract param modes
                    let param_modes = extract_param_modes(&resolved_func_ty);

                    // Patch the AST
                    let overload_sig = make_overload_signature_from(&resolved_func_ty);
                    let resolved_ref = super::resolved_ref_from_binding_source_with_overload(
                        &winning.source,
                        overload_sig,
                    );
                    if let Some(body) = &mut fn_bodies[entry.owning_fn] {
                        patch_deferred_app(
                            body,
                            entry.span,
                            &resolved_ref,
                            &subst.apply(&func_ty),
                            &param_modes,
                        );
                    }

                    progress = true;
                    // Don't increment i — we removed the element
                }
                _ if still_unsolved => {
                    // Still ambiguous, keep deferring
                    deferred[i].arg_types = arg_types;
                    i += 1;
                }
                0 => {
                    // Concrete args, no match → E0511
                    let entry = deferred.remove(i);
                    return Err(super::spanned(
                        TypeError::NoMatchingOverload {
                            name: entry.name,
                            candidates: entry.candidate_descriptions,
                            arg_types,
                        },
                        entry.span,
                    ));
                }
                _ => {
                    // Concrete args, multiple matches → E0518
                    let entry = deferred.remove(i);
                    let ambiguous: Vec<String> = matches
                        .iter()
                        .map(|(ci, _)| entry.candidate_descriptions[*ci].clone())
                        .collect();
                    return Err(super::spanned(
                        TypeError::AmbiguousOverload {
                            name: entry.name,
                            candidates: ambiguous,
                        },
                        entry.span,
                    ));
                }
            }
        }

        if !progress {
            break;
        }
    }

    // Any remaining entries have unsolved args → E0510
    if let Some(entry) = deferred.drain(..).next() {
        return Err(super::spanned(
            TypeError::UnresolvedOverload {
                name: entry.name,
                candidates: entry.candidate_descriptions,
            },
            entry.span,
        ));
    }

    Ok(())
}

fn extract_return_type(ty: &Type) -> Option<Type> {
    match ty {
        Type::Fn(_, ret) => Some(*ret.clone()),
        Type::Own(inner) => extract_return_type(inner),
        _ => None,
    }
}

fn extract_param_modes(ty: &Type) -> Vec<ParamMode> {
    match ty {
        Type::Fn(params, _) => params.iter().map(|(m, _)| *m).collect(),
        Type::Own(inner) => extract_param_modes(inner),
        _ => vec![],
    }
}

/// Walk the typed AST to find a deferred `App` node by matching span and
/// `resolved_ref: None`, then patch it with the resolved reference,
/// function type, and param modes.
fn patch_deferred_app(
    expr: &mut TypedExpr,
    target_span: Span,
    resolved_ref: &Option<ResolvedBindingRef>,
    func_ty: &Type,
    param_modes: &[ParamMode],
) {
    if expr.span == target_span && expr.resolved_ref.is_none() {
        if let TypedExprKind::App {
            func,
            param_modes: ref mut pm,
            ..
        } = &mut expr.kind
        {
            expr.resolved_ref = resolved_ref.clone();
            *pm = param_modes.to_vec();
            func.resolved_ref = resolved_ref.clone();
            func.ty = func_ty.clone();
            return;
        }
    }

    // Recurse into children
    match &mut expr.kind {
        TypedExprKind::App { func, args, .. } => {
            patch_deferred_app(func, target_span, resolved_ref, func_ty, param_modes);
            for arg in args {
                patch_deferred_app(arg, target_span, resolved_ref, func_ty, param_modes);
            }
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs {
                patch_deferred_app(e, target_span, resolved_ref, func_ty, param_modes);
            }
        }
        TypedExprKind::Let { value, body, .. }
        | TypedExprKind::LetPattern { value, body, .. } => {
            patch_deferred_app(value, target_span, resolved_ref, func_ty, param_modes);
            if let Some(body) = body {
                patch_deferred_app(body, target_span, resolved_ref, func_ty, param_modes);
            }
        }
        TypedExprKind::If {
            cond,
            then_,
            else_,
        } => {
            patch_deferred_app(cond, target_span, resolved_ref, func_ty, param_modes);
            patch_deferred_app(then_, target_span, resolved_ref, func_ty, param_modes);
            patch_deferred_app(else_, target_span, resolved_ref, func_ty, param_modes);
        }
        TypedExprKind::Lambda { body, .. } => {
            patch_deferred_app(body, target_span, resolved_ref, func_ty, param_modes);
        }
        TypedExprKind::Match { scrutinee, arms } => {
            patch_deferred_app(scrutinee, target_span, resolved_ref, func_ty, param_modes);
            for arm in arms {
                patch_deferred_app(&mut arm.body, target_span, resolved_ref, func_ty, param_modes);
                if let Some(guard) = &mut arm.guard {
                    patch_deferred_app(guard, target_span, resolved_ref, func_ty, param_modes);
                }
            }
        }
        TypedExprKind::FieldAccess { expr: inner, .. }
        | TypedExprKind::UnaryOp { operand: inner, .. }
        | TypedExprKind::TypeApp { expr: inner, .. }
        | TypedExprKind::QuestionMark { expr: inner, .. }
        | TypedExprKind::Discharge(inner) => {
            patch_deferred_app(inner, target_span, resolved_ref, func_ty, param_modes);
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            patch_deferred_app(lhs, target_span, resolved_ref, func_ty, param_modes);
            patch_deferred_app(rhs, target_span, resolved_ref, func_ty, param_modes);
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, val) in fields {
                patch_deferred_app(val, target_span, resolved_ref, func_ty, param_modes);
            }
        }
        TypedExprKind::StructUpdate { base, fields } => {
            patch_deferred_app(base, target_span, resolved_ref, func_ty, param_modes);
            for (_, val) in fields {
                patch_deferred_app(val, target_span, resolved_ref, func_ty, param_modes);
            }
        }
        TypedExprKind::Tuple(elems) | TypedExprKind::VecLit(elems) => {
            for e in elems {
                patch_deferred_app(e, target_span, resolved_ref, func_ty, param_modes);
            }
        }
        TypedExprKind::Recur { args, .. } => {
            for e in args {
                patch_deferred_app(e, target_span, resolved_ref, func_ty, param_modes);
            }
        }
        TypedExprKind::Var(_) | TypedExprKind::Lit(_) => {}
    }
}
