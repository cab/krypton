use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Expr, Pattern, Span};

use crate::type_registry;
use crate::typed_ast::TypedExpr;
use crate::types::{ParamMode, Substitution, Type, TypeEnv, TypeVarGen};
use crate::unify::SpannedTypeError;

use super::expr::InferenceContext;
/// Infer the type of an expression using Algorithm J.
#[tracing::instrument(level = "trace", skip_all)]
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<Type, SpannedTypeError> {
    let empty_tpm = HashMap::new();
    let empty_tpa = HashMap::new();
    let empty_qm = HashMap::new();
    let empty_imported_types = HashMap::new();
    let mut deferred = Vec::new();
    let mut deferred_id_counter: u32 = 0;
    let mut ctx = InferenceContext {
        env,
        subst,
        gen,
        registry: None,
        recur_params: None,
        let_own_spans: None,
        lambda_own_captures: None,
        type_param_map: &empty_tpm,
        type_param_arity: &empty_tpa,
        qualified_modules: &empty_qm,
        imported_type_info: &empty_imported_types,
        module_path: "__expr__",
        shadowed_prelude_fns: &[],
        self_type: None,
        deferred_overloads: &mut deferred,
        owning_fn_idx: 0,
        deferred_id_counter: &mut deferred_id_counter,
    };
    ctx.infer_expr_inner(expr, None).map(|te| te.ty)
}

/// Instantiate a field type from the registry by substituting the original
/// type parameter var ids with the concrete type arguments.
pub(crate) fn instantiate_field_type(
    field_ty: &Type,
    info: &type_registry::TypeInfo,
    type_args: &[Type],
) -> Type {
    if info.type_param_vars.is_empty() {
        return field_ty.clone();
    }
    // Build a substitution from registry's original var ids to the actual type args
    let mut subst = Substitution::new();
    for (var_id, arg) in info.type_param_vars.iter().zip(type_args.iter()) {
        subst.insert(*var_id, arg.clone());
    }
    subst.apply(field_ty)
}

/// Return the name of the first free variable (not in `params`) whose type in
/// `env` (after substitution) is `Own(...)`.
pub(crate) fn collect_parser_pattern_bindings(pattern: &Pattern) -> Vec<&str> {
    fn collect_inner<'a>(pattern: &'a Pattern, out: &mut Vec<&'a str>) {
        match pattern {
            Pattern::Var { name, .. } => out.push(name.as_str()),
            Pattern::Constructor { args, .. } => {
                for arg in args {
                    collect_inner(arg, out);
                }
            }
            Pattern::Tuple { elements, .. } => {
                for element in elements {
                    collect_inner(element, out);
                }
            }
            Pattern::StructPat { fields, .. } => {
                for (_, field_pattern) in fields {
                    collect_inner(field_pattern, out);
                }
            }
            Pattern::Or { alternatives, .. } => {
                if let Some(first) = alternatives.first() {
                    collect_inner(first, out);
                }
            }
            Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
        }
    }

    let mut out = Vec::new();
    collect_inner(pattern, &mut out);
    out
}

/// Check whether `capture_name` is used in an own-requiring position
/// in the typed body. A capture demands own unless ALL of its occurrences
/// are in known-shared positions: binary-op operands, unary-op operands,
/// field-access bases, or function args where the param type is not `~T`.
fn capture_demands_own(body: &TypedExpr, capture_name: &str, subst: &Substitution) -> bool {
    use crate::typed_ast::TypedExprKind;

    /// Returns true if `expr` is `Var(capture_name)`.
    fn is_capture(expr: &TypedExpr, capture_name: &str) -> bool {
        matches!(&expr.kind, TypedExprKind::Var(name) if name == capture_name)
    }

    match &body.kind {
        // A bare capture var in a non-shared position demands own
        // (e.g. return position, let-binding value, etc.)
        TypedExprKind::Var(name) if name == capture_name => true,
        TypedExprKind::Var(_) | TypedExprKind::Lit(_) => false,

        // Binary-op operands are shared: coerces ~T → T
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            // If the capture is a direct operand, it's shared — skip it.
            // Only recurse into non-capture sub-expressions.
            (!is_capture(lhs, capture_name) && capture_demands_own(lhs, capture_name, subst))
                || (!is_capture(rhs, capture_name) && capture_demands_own(rhs, capture_name, subst))
        }
        // Unary-op operand is shared
        TypedExprKind::UnaryOp { operand, .. } => {
            !is_capture(operand, capture_name) && capture_demands_own(operand, capture_name, subst)
        }
        // Field-access base is shared
        TypedExprKind::FieldAccess { expr, .. } => {
            !is_capture(expr, capture_name) && capture_demands_own(expr, capture_name, subst)
        }

        // Function application: check param types and modes to decide shared vs own
        TypedExprKind::App { func, args, param_modes } => {
            let func_ty = subst.apply(&func.ty);
            let fn_params = match &func_ty {
                Type::Fn(p, _) => Some(p.as_slice()),
                Type::Own(inner) => match inner.as_ref() {
                    Type::Fn(p, _) => Some(p.as_slice()),
                    _ => None,
                },
                _ => None,
            };

            for (i, arg) in args.iter().enumerate() {
                if is_capture(arg, capture_name) {
                    // Check param mode first: borrow slots never demand own
                    let mode = param_modes.get(i).copied().unwrap_or(ParamMode::Consume);
                    if matches!(mode, ParamMode::Borrow | ParamMode::ObservationalBorrow) {
                        // Borrow slot — capture is not consumed, doesn't force ~fn
                        continue;
                    }
                    // Determine if this arg position demands own
                    let demands = if let Some(params) = fn_params {
                        if let Some((_, pty)) = params.get(i) {
                            let resolved = subst.apply(pty);
                            matches!(resolved, Type::Own(_) | Type::Var(_) | Type::Shape(_) | Type::MaybeOwn(_, _))
                        } else {
                            true // conservative: can't determine param type
                        }
                    } else {
                        true // conservative: can't resolve func type
                    };
                    if demands {
                        return true;
                    }
                    // Shared arg position — don't recurse into this arg
                } else if capture_demands_own(arg, capture_name, subst) {
                    return true;
                }
            }
            capture_demands_own(func, capture_name, subst)
        }

        // Nodes that just recurse into children
        TypedExprKind::If { cond, then_, else_ } => {
            capture_demands_own(cond, capture_name, subst)
                || capture_demands_own(then_, capture_name, subst)
                || capture_demands_own(else_, capture_name, subst)
        }
        TypedExprKind::Let { value, body, .. } => {
            capture_demands_own(value, capture_name, subst)
                || body
                    .as_ref()
                    .is_some_and(|b| capture_demands_own(b, capture_name, subst))
        }
        TypedExprKind::Do(exprs) => exprs
            .iter()
            .any(|e| capture_demands_own(e, capture_name, subst)),
        TypedExprKind::Match { scrutinee, arms } => {
            capture_demands_own(scrutinee, capture_name, subst)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|g| capture_demands_own(g, capture_name, subst))
                        || capture_demands_own(&arm.body, capture_name, subst)
                })
        }
        TypedExprKind::Lambda { body, .. } => capture_demands_own(body, capture_name, subst),
        TypedExprKind::TypeApp { expr, .. } => capture_demands_own(expr, capture_name, subst),
        // Conservative: struct fields, tuple elements, vec/recur elements
        // all treated as own-requiring when the capture appears directly
        TypedExprKind::StructLit { fields, .. } => fields.iter().any(|(_, val)| {
            is_capture(val, capture_name) || capture_demands_own(val, capture_name, subst)
        }),
        TypedExprKind::StructUpdate { base, fields } => {
            capture_demands_own(base, capture_name, subst)
                || fields.iter().any(|(_, val)| {
                    is_capture(val, capture_name) || capture_demands_own(val, capture_name, subst)
                })
        }
        TypedExprKind::Tuple(elements) | TypedExprKind::VecLit(elements) => {
            elements.iter().any(|elem| {
                is_capture(elem, capture_name) || capture_demands_own(elem, capture_name, subst)
            })
        }
        TypedExprKind::Recur { args, .. } => args.iter().any(|elem| {
            is_capture(elem, capture_name) || capture_demands_own(elem, capture_name, subst)
        }),
        TypedExprKind::LetPattern { value, body, .. } => {
            capture_demands_own(value, capture_name, subst)
                || body
                    .as_ref()
                    .is_some_and(|b| capture_demands_own(b, capture_name, subst))
        }
        TypedExprKind::QuestionMark { expr, .. } => capture_demands_own(expr, capture_name, subst),
        TypedExprKind::Discharge(inner) => capture_demands_own(inner, capture_name, subst),
    }
}

pub(crate) fn first_own_capture(
    body: &Expr,
    params: &HashSet<&str>,
    env: &TypeEnv,
    subst: &Substitution,
    typed_body: &TypedExpr,
) -> Option<String> {
    match body {
        Expr::Var { name, .. } => {
            if !params.contains(name.as_str()) {
                if let Some(scheme) = env.lookup(name) {
                    let ty = subst.apply(&scheme.ty);
                    if matches!(ty, Type::Own(_)) && capture_demands_own(typed_body, name, subst) {
                        return Some(name.clone());
                    }
                }
            }
            None
        }
        Expr::App { func, args, .. } => first_own_capture(func, params, env, subst, typed_body)
            .or_else(|| {
                args.iter()
                    .find_map(|a| first_own_capture(a, params, env, subst, typed_body))
            }),
        Expr::TypeApp { expr, .. } => first_own_capture(expr, params, env, subst, typed_body),
        Expr::Let {
            name,
            value,
            body: let_body,
            ..
        } => {
            if let Some(found) = first_own_capture(value, params, env, subst, typed_body) {
                return Some(found);
            }
            if let Some(b) = let_body {
                let mut inner = params.clone();
                inner.insert(name.as_str());
                return first_own_capture(b, &inner, env, subst, typed_body);
            }
            None
        }
        Expr::LetPattern {
            pattern,
            value,
            body,
            ..
        } => first_own_capture(value, params, env, subst, typed_body).or_else(|| {
            body.as_ref().and_then(|b| {
                let mut inner = params.clone();
                for name in collect_parser_pattern_bindings(pattern) {
                    inner.insert(name);
                }
                first_own_capture(b, &inner, env, subst, typed_body)
            })
        }),
        Expr::Do { exprs, .. } => exprs
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst, typed_body)),
        Expr::If {
            cond, then_, else_, ..
        } => first_own_capture(cond, params, env, subst, typed_body)
            .or_else(|| first_own_capture(then_, params, env, subst, typed_body))
            .or_else(|| first_own_capture(else_, params, env, subst, typed_body)),
        Expr::Match {
            scrutinee, arms, ..
        } => first_own_capture(scrutinee, params, env, subst, typed_body).or_else(|| {
            arms.iter().find_map(|arm| {
                let mut inner = params.clone();
                for name in collect_parser_pattern_bindings(&arm.pattern) {
                    inner.insert(name);
                }
                arm.guard
                    .as_ref()
                    .and_then(|guard| first_own_capture(guard, &inner, env, subst, typed_body))
                    .or_else(|| first_own_capture(&arm.body, &inner, env, subst, typed_body))
            })
        }),
        Expr::BinaryOp { lhs, rhs, .. } => first_own_capture(lhs, params, env, subst, typed_body)
            .or_else(|| first_own_capture(rhs, params, env, subst, typed_body)),
        Expr::UnaryOp { operand, .. } => first_own_capture(operand, params, env, subst, typed_body),
        Expr::Lambda {
            params: inner_params,
            body,
            ..
        } => {
            let mut inner = params.clone();
            for p in inner_params {
                inner.insert(p.name.as_str());
            }
            first_own_capture(body, &inner, env, subst, typed_body)
        }
        Expr::FieldAccess { expr, .. } => first_own_capture(expr, params, env, subst, typed_body),
        Expr::StructLit { fields, .. } => fields
            .iter()
            .find_map(|(_, e)| first_own_capture(e, params, env, subst, typed_body)),
        Expr::StructUpdate { base, fields, .. } => {
            first_own_capture(base, params, env, subst, typed_body).or_else(|| {
                fields
                    .iter()
                    .find_map(|(_, e)| first_own_capture(e, params, env, subst, typed_body))
            })
        }
        Expr::Tuple { elements, .. } => elements
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst, typed_body)),
        Expr::Recur { args, .. } => args
            .iter()
            .find_map(|a| first_own_capture(a, params, env, subst, typed_body)),
        Expr::QuestionMark { expr, .. } => first_own_capture(expr, params, env, subst, typed_body),
        Expr::List { elements, .. } => elements
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst, typed_body)),
        Expr::IfLet {
            pattern,
            scrutinee,
            guard,
            then_,
            else_,
            ..
        } => {
            if let Some(found) = first_own_capture(scrutinee, params, env, subst, typed_body) {
                return Some(found);
            }
            let mut inner = params.clone();
            for name in collect_parser_pattern_bindings(pattern) {
                inner.insert(name);
            }
            if let Some(guard) = guard {
                if let Some(found) = first_own_capture(guard, &inner, env, subst, typed_body) {
                    return Some(found);
                }
            }
            if let Some(found) = first_own_capture(then_, &inner, env, subst, typed_body) {
                return Some(found);
            }
            if let Some(else_) = else_ {
                return first_own_capture(else_, params, env, subst, typed_body);
            }
            None
        }
        Expr::Lit { .. } => None,
    }
}

/// Walk a typed lambda body and return the span of the first `Recur` node
/// that targets THIS lambda. Stops at nested `Lambda` bodies because those
/// rebind `recur` to themselves (the inner lambda's params).
pub(crate) fn find_first_recur_span(body: &TypedExpr) -> Option<Span> {
    use crate::typed_ast::TypedExprKind as K;
    match &body.kind {
        K::Recur { .. } => Some(body.span),
        K::Lambda { .. } => None,
        K::Lit(_) | K::Var(_) => None,
        K::App { func, args, .. } => find_first_recur_span(func)
            .or_else(|| args.iter().find_map(find_first_recur_span)),
        K::TypeApp { expr, .. } => find_first_recur_span(expr),
        K::If { cond, then_, else_ } => find_first_recur_span(cond)
            .or_else(|| find_first_recur_span(then_))
            .or_else(|| find_first_recur_span(else_)),
        K::Let { value, body, .. } => find_first_recur_span(value)
            .or_else(|| body.as_deref().and_then(find_first_recur_span)),
        K::Do(exprs) => exprs.iter().find_map(find_first_recur_span),
        K::Match { scrutinee, arms } => find_first_recur_span(scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_deref()
                    .and_then(find_first_recur_span)
                    .or_else(|| find_first_recur_span(&arm.body))
            })
        }),
        K::FieldAccess { expr, .. } => find_first_recur_span(expr),
        K::Tuple(elems) | K::VecLit(elems) => elems.iter().find_map(find_first_recur_span),
        K::BinaryOp { lhs, rhs, .. } => {
            find_first_recur_span(lhs).or_else(|| find_first_recur_span(rhs))
        }
        K::UnaryOp { operand, .. } => find_first_recur_span(operand),
        K::StructLit { fields, .. } => fields.iter().find_map(|(_, v)| find_first_recur_span(v)),
        K::StructUpdate { base, fields } => find_first_recur_span(base)
            .or_else(|| fields.iter().find_map(|(_, v)| find_first_recur_span(v))),
        K::LetPattern { value, body, .. } => find_first_recur_span(value)
            .or_else(|| body.as_deref().and_then(find_first_recur_span)),
        K::QuestionMark { expr, .. } => find_first_recur_span(expr),
        K::Discharge(inner) => find_first_recur_span(inner),
    }
}
