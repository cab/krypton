use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Decl, Expr, Lit, Module, Pattern, Span, UnaryOp};

use crate::scc;
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{self, TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedModule};
use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{unify, SpannedTypeError, TypeError};

/// Attempt call-site own→T coercion: if an arg is `Own(inner)` and the
/// corresponding param is a concrete non-Own, non-Var type, strip the Own wrapper.
fn coerce_own_args(func_ty: &Type, arg_types: &[Type], subst: &Substitution) -> Vec<Type> {
    let walked = subst.apply(func_ty);
    if let Type::Fn(param_types, _) = &walked {
        arg_types
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let resolved_arg = subst.apply(arg);
                if let Some(param) = param_types.get(i) {
                    let resolved_param = subst.apply(param);
                    // Allow fn() → own fn(): wrap bare Fn arg with Own when param expects Own(Fn(...))
                    if matches!(&resolved_arg, Type::Fn(_, _))
                        && matches!(&resolved_param, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)))
                    {
                        return Type::Own(Box::new(resolved_arg));
                    }
                    // Strip Own wrapper for non-function types (existing behavior),
                    // but keep Own(Fn(..)) intact so own fn() → fn() fails at unification.
                    if let Type::Own(inner) = &resolved_arg {
                        if !matches!(inner.as_ref(), Type::Fn(_, _))
                            && !matches!(resolved_param, Type::Own(_) | Type::Var(_))
                        {
                            return *inner.clone();
                        }
                    }
                }
                arg.clone()
            })
            .collect()
    } else {
        arg_types.to_vec()
    }
}

/// Collect free type variables in a type.
fn free_vars(ty: &Type) -> HashSet<TypeVarId> {
    match ty {
        Type::Var(id) => {
            let mut s = HashSet::new();
            s.insert(*id);
            s
        }
        Type::Fn(params, ret) => {
            let mut s = HashSet::new();
            for p in params {
                s.extend(free_vars(p));
            }
            s.extend(free_vars(ret));
            s
        }
        Type::Named(_, args) => {
            let mut s = HashSet::new();
            for a in args {
                s.extend(free_vars(a));
            }
            s
        }
        Type::Own(inner) => free_vars(inner),
        Type::Tuple(elems) => {
            let mut s = HashSet::new();
            for e in elems {
                s.extend(free_vars(e));
            }
            s
        }
        _ => HashSet::new(),
    }
}

/// Collect free type variables across all bindings in the environment.
fn free_vars_env(env: &TypeEnv, subst: &Substitution) -> HashSet<TypeVarId> {
    let mut s = HashSet::new();
    env.for_each_scheme(|scheme| {
        let applied = subst.apply_scheme(scheme);
        let fv = free_vars(&applied.ty);
        // Remove quantified vars
        for v in &fv {
            if !applied.vars.contains(v) {
                s.insert(*v);
            }
        }
    });
    s
}

/// Generalize a type into a type scheme by quantifying over variables
/// free in the type but not free in the environment.
fn generalize(ty: &Type, env: &TypeEnv, subst: &Substitution) -> TypeScheme {
    let ty = subst.apply(ty);
    let ty_vars = free_vars(&ty);
    let env_vars = free_vars_env(env, subst);
    let mut vars: Vec<TypeVarId> = ty_vars.difference(&env_vars).copied().collect();
    vars.sort();
    TypeScheme { vars, ty }
}

/// Attach a span to a TypeError, producing a SpannedTypeError.
fn spanned(error: TypeError, span: krypton_parser::ast::Span) -> SpannedTypeError {
    SpannedTypeError { error, span, note: None, secondary_span: None }
}

/// Check if a type is concretely not a function (after walking substitution).
fn is_concrete_non_function(ty: &Type, subst: &Substitution) -> bool {
    let walked = subst.apply(ty);
    match &walked {
        Type::Var(_) | Type::Fn(_, _) => false,
        Type::Own(inner) => is_concrete_non_function(inner, subst),
        _ => true,
    }
}

/// Infer the type of an expression using Algorithm J.
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<Type, SpannedTypeError> {
    infer_expr_inner(expr, env, subst, gen, None, None, None, None).map(|te| te.ty)
}

/// Infer the type of an expression, with optional access to the type registry
/// for struct field access and update operations.
fn infer_expr_inner(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    recur_params: Option<&[Type]>,
    mut let_own_spans: Option<&mut HashSet<Span>>,
    mut lambda_own_captures: Option<&mut HashMap<Span, String>>,
) -> Result<TypedExpr, SpannedTypeError> {
    match expr {
        Expr::Lit { value, span } => {
            let ty = match value {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::Bool(_) => Type::Bool,
                Lit::String(_) => Type::String,
                Lit::Unit => Type::Unit,
            };
            Ok(TypedExpr { kind: TypedExprKind::Lit(value.clone()), ty, span: *span })
        }

        Expr::Var { name, span, .. } => match env.lookup(name) {
            Some(scheme) => {
                let scheme = scheme.clone();
                let ty = scheme.instantiate(&mut || gen.fresh());
                Ok(TypedExpr { kind: TypedExprKind::Var(name.clone()), ty, span: *span })
            }
            None => Err(spanned(
                TypeError::UnknownVariable { name: name.clone() },
                *span,
            )),
        },

        Expr::Lambda { params, body, span, .. } => {
            let mut param_types = Vec::new();
            env.push_scope();
            for p in params {
                let tv = Type::Var(gen.fresh());
                param_types.push(tv.clone());
                env.bind(p.name.clone(), TypeScheme::mono(tv));
            }
            let body_typed = infer_expr_inner(body, env, subst, gen, registry, None, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            env.pop_scope();
            let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
            let body_ty = subst.apply(&body_typed.ty);
            let fn_ty = Type::Fn(param_types, Box::new(body_ty));
            let param_names: HashSet<&str> = params.iter().map(|p| p.name.as_str()).collect();
            let ty = if captures_own_value(body, &param_names, env, subst) {
                if let Some(ref mut captures) = lambda_own_captures {
                    if let Some(cap_name) = first_own_capture(body, &param_names, env, subst) {
                        captures.insert(*span, cap_name);
                    }
                }
                Type::Own(Box::new(fn_ty))
            } else {
                fn_ty
            };
            let kind = TypedExprKind::Lambda {
                params: params.iter().map(|p| p.name.clone()).collect(),
                body: Box::new(body_typed),
            };
            Ok(TypedExpr { kind, ty, span: *span })
        }

        Expr::App {
            func, args, span, ..
        } => {
            let func_typed = infer_expr_inner(func, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let mut args_typed = Vec::new();
            let mut arg_types = Vec::new();
            for a in args {
                let a_typed = infer_expr_inner(a, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                arg_types.push(a_typed.ty.clone());
                args_typed.push(a_typed);
            }

            if is_concrete_non_function(&func_typed.ty, subst) {
                let actual = subst.apply(&func_typed.ty);
                return Err(spanned(TypeError::NotAFunction { actual }, *span));
            }

            let ret_var = Type::Var(gen.fresh());
            let is_constructor = if let Expr::Var { name, .. } = func.as_ref() {
                registry.is_some_and(|r| r.is_constructor(name))
            } else {
                false
            };
            let coerced_args = if is_constructor {
                arg_types.clone()
            } else {
                coerce_own_args(&func_typed.ty, &arg_types, subst)
            };
            let expected_fn = Type::Fn(coerced_args, Box::new(ret_var.clone()));
            let unwrapped_func_ty = match subst.apply(&func_typed.ty) {
                Type::Own(inner) if matches!(*inner, Type::Fn(_, _)) => *inner,
                _ => func_typed.ty.clone(),
            };
            unify(&unwrapped_func_ty, &expected_fn, subst)
                .map_err(|e| {
                    let mut err = spanned(e, *span);
                    if matches!(&err.error, TypeError::Mismatch { .. }) {
                        if let Some(ref captures) = lambda_own_captures {
                            for arg in args.iter() {
                                if let Expr::Lambda { span: lspan, .. } = arg {
                                    if let Some(cap_name) = captures.get(lspan) {
                                        err.note = Some(format!(
                                            "closure is single-use because it captures own value `{}`",
                                            cap_name
                                        ));
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    err
                })?;
            let ty = subst.apply(&ret_var);
            Ok(TypedExpr {
                kind: TypedExprKind::App { func: Box::new(func_typed), args: args_typed },
                ty,
                span: *span,
            })
        }

        Expr::Let {
            name,
            value,
            body,
            span,
        } => {
            let val_typed = infer_expr_inner(value, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let resolved_val = subst.apply(&val_typed.ty);
            if matches!(&resolved_val, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _))) {
                if let Some(ref mut los) = let_own_spans {
                    los.insert(*span);
                }
            }
            match body {
                Some(body) => {
                    let scheme = generalize(&val_typed.ty, env, subst);
                    env.push_scope();
                    env.bind(name.clone(), scheme);
                    let body_typed = infer_expr_inner(body, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
                    env.pop_scope();
                    let ty = body_typed.ty.clone();
                    Ok(TypedExpr {
                        kind: TypedExprKind::Let {
                            name: name.clone(),
                            value: Box::new(val_typed),
                            body: Some(Box::new(body_typed)),
                        },
                        ty,
                        span: *span,
                    })
                }
                None => {
                    let scheme = generalize(&val_typed.ty, env, subst);
                    env.bind(name.clone(), scheme);
                    Ok(TypedExpr {
                        kind: TypedExprKind::Let {
                            name: name.clone(),
                            value: Box::new(val_typed),
                            body: None,
                        },
                        ty: Type::Unit,
                        span: *span,
                    })
                }
            }
        }

        Expr::If {
            cond,
            then_,
            else_,
            span,
            ..
        } => {
            let cond_typed = infer_expr_inner(cond, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            unify(&cond_typed.ty, &Type::Bool, subst)
                .map_err(|e| spanned(e, *span))?;
            let then_typed = infer_expr_inner(then_, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let else_typed = infer_expr_inner(else_, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
            unify(&then_typed.ty, &else_typed.ty, subst)
                .map_err(|e| spanned(e, *span))?;
            let ty = subst.apply(&then_typed.ty);
            Ok(TypedExpr {
                kind: TypedExprKind::If {
                    cond: Box::new(cond_typed),
                    then_: Box::new(then_typed),
                    else_: Box::new(else_typed),
                },
                ty,
                span: *span,
            })
        }

        Expr::Do { exprs, span } => {
            env.push_scope();
            if exprs.is_empty() {
                env.pop_scope();
                return Ok(TypedExpr {
                    kind: TypedExprKind::Do(Vec::new()),
                    ty: Type::Unit,
                    span: *span,
                });
            }
            let mut typed_exprs = Vec::new();
            for e in exprs {
                typed_exprs.push(infer_expr_inner(e, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?);
            }
            env.pop_scope();
            let ty = typed_exprs.last().unwrap().ty.clone();
            Ok(TypedExpr {
                kind: TypedExprKind::Do(typed_exprs),
                ty,
                span: *span,
            })
        }

        Expr::BinaryOp {
            op, lhs, rhs, span, ..
        } => {
            let lhs_typed = infer_expr_inner(lhs, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let rhs_typed = infer_expr_inner(rhs, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
            let ty = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                    unify(&lhs_typed.ty, &rhs_typed.ty, subst)
                        .map_err(|e| spanned(e, *span))?;
                    let resolved = subst.apply(&lhs_typed.ty);
                    match &resolved {
                        Type::Int | Type::Float => resolved,
                        Type::Var(_) => {
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                            Type::Int
                        }
                        _ => return Err(spanned(TypeError::Mismatch { expected: Type::Int, actual: resolved }, *span)),
                    }
                }
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    unify(&lhs_typed.ty, &rhs_typed.ty, subst)
                        .map_err(|e| spanned(e, *span))?;
                    let resolved = subst.apply(&lhs_typed.ty);
                    match &resolved {
                        Type::Int | Type::Float => {}
                        Type::Var(_) => {
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                        }
                        _ => return Err(spanned(TypeError::Mismatch { expected: Type::Int, actual: resolved }, *span)),
                    }
                    Type::Bool
                }
            };
            Ok(TypedExpr {
                kind: TypedExprKind::BinaryOp {
                    op: op.clone(),
                    lhs: Box::new(lhs_typed),
                    rhs: Box::new(rhs_typed),
                },
                ty,
                span: *span,
            })
        }

        Expr::UnaryOp {
            op, operand, span, ..
        } => {
            let operand_typed = infer_expr_inner(operand, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
            let ty = match op {
                UnaryOp::Neg => {
                    let resolved = subst.apply(&operand_typed.ty);
                    match &resolved {
                        Type::Int | Type::Float => resolved,
                        Type::Var(_) => {
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                            Type::Int
                        }
                        _ => return Err(spanned(TypeError::Mismatch { expected: Type::Int, actual: resolved }, *span)),
                    }
                }
            };
            Ok(TypedExpr {
                kind: TypedExprKind::UnaryOp {
                    op: op.clone(),
                    operand: Box::new(operand_typed),
                },
                ty,
                span: *span,
            })
        }

        Expr::Recur { args, span, .. } => {
            let mut typed_args = Vec::new();
            match recur_params {
                Some(params) => {
                    if args.len() != params.len() {
                        return Err(spanned(
                            TypeError::WrongArity { expected: params.len(), actual: args.len() },
                            *span,
                        ));
                    }
                    for (a, p) in args.iter().zip(params.iter()) {
                        let a_typed = infer_expr_inner(a, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                        unify(&a_typed.ty, p, subst).map_err(|e| spanned(e, *span))?;
                        typed_args.push(a_typed);
                    }
                }
                None => {
                    for a in args {
                        typed_args.push(infer_expr_inner(a, env, subst, gen, registry, None, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?);
                    }
                }
            }
            let ty = Type::Var(gen.fresh());
            Ok(TypedExpr {
                kind: TypedExprKind::Recur(typed_args),
                ty,
                span: *span,
            })
        }

        Expr::FieldAccess { expr: target, field, span } => {
            let target_typed = infer_expr_inner(target, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
            let resolved = subst.apply(&target_typed.ty);
            // Unwrap Own wrapper — field access works on the inner type
            let inner_resolved = match &resolved {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            let ty = resolve_field_access(inner_resolved, field, *span, registry)?;
            Ok(TypedExpr {
                kind: TypedExprKind::FieldAccess {
                    expr: Box::new(target_typed),
                    field: field.clone(),
                },
                ty,
                span: *span,
            })
        }

        Expr::StructUpdate { base, fields, span } => {
            let base_typed = infer_expr_inner(base, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let resolved = subst.apply(&base_typed.ty);
            // Unwrap Own wrapper — struct update works on the inner type
            let inner_resolved = match &resolved {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            let typed_fields = resolve_struct_update(inner_resolved, fields, *span, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
            Ok(TypedExpr {
                kind: TypedExprKind::StructUpdate {
                    base: Box::new(base_typed),
                    fields: typed_fields,
                },
                ty: resolved,
                span: *span,
            })
        }

        Expr::Match { scrutinee, arms, span } => {
            let scrutinee_typed = infer_expr_inner(scrutinee, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let result_ty = Type::Var(gen.fresh());
            let mut typed_arms = Vec::new();
            for arm in arms {
                env.push_scope();
                check_pattern(&arm.pattern, &subst.apply(&scrutinee_typed.ty), env, subst, gen, registry, *span)?;
                let body_typed = infer_expr_inner(&arm.body, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                unify(&result_ty, &body_typed.ty, subst).map_err(|e| spanned(e, *span))?;
                env.pop_scope();
                typed_arms.push(TypedMatchArm {
                    pattern: arm.pattern.clone(),
                    body: body_typed,
                });
            }
            crate::exhaustiveness::check_exhaustiveness(
                &subst.apply(&scrutinee_typed.ty),
                arms,
                registry,
                *span,
            )?;
            let ty = subst.apply(&result_ty);
            Ok(TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(scrutinee_typed),
                    arms: typed_arms,
                },
                ty,
                span: *span,
            })
        }

        Expr::Tuple { elements, span } => {
            let mut typed_elems = Vec::new();
            for e in elements {
                typed_elems.push(infer_expr_inner(e, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?);
            }
            let ty = Type::Tuple(typed_elems.iter().map(|te| te.ty.clone()).collect());
            Ok(TypedExpr {
                kind: TypedExprKind::Tuple(typed_elems),
                ty,
                span: *span,
            })
        }

        Expr::LetPattern { pattern, value, body, span } => {
            let val_typed = infer_expr_inner(value, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            match body {
                Some(body) => {
                    env.push_scope();
                    check_pattern(pattern, &subst.apply(&val_typed.ty), env, subst, gen, registry, *span)?;
                    let body_typed = infer_expr_inner(body, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
                    env.pop_scope();
                    let ty = body_typed.ty.clone();
                    Ok(TypedExpr {
                        kind: TypedExprKind::LetPattern {
                            pattern: pattern.clone(),
                            value: Box::new(val_typed),
                            body: Some(Box::new(body_typed)),
                        },
                        ty,
                        span: *span,
                    })
                }
                None => {
                    check_pattern(pattern, &subst.apply(&val_typed.ty), env, subst, gen, registry, *span)?;
                    Ok(TypedExpr {
                        kind: TypedExprKind::LetPattern {
                            pattern: pattern.clone(),
                            value: Box::new(val_typed),
                            body: None,
                        },
                        ty: Type::Unit,
                        span: *span,
                    })
                }
            }
        }

        Expr::StructLit { name, fields, span } => {
            let reg = registry.ok_or_else(|| {
                spanned(TypeError::UnknownVariable { name: name.clone() }, *span)
            })?;
            let info = reg.lookup_type(name).ok_or_else(|| {
                spanned(TypeError::UnknownVariable { name: name.clone() }, *span)
            })?;
            match &info.kind {
                type_registry::TypeKind::Record { fields: record_fields } => {
                    let fresh_args: Vec<Type> = info.type_param_vars.iter().map(|_| Type::Var(gen.fresh())).collect();
                    let struct_ty = Type::Named(name.clone(), fresh_args.clone());

                    let provided: HashSet<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                    let missing: Vec<String> = record_fields.iter()
                        .filter(|(n, _)| !provided.contains(n.as_str()))
                        .map(|(n, _)| n.clone())
                        .collect();
                    if !missing.is_empty() {
                        return Err(spanned(TypeError::MissingFields { type_name: name.clone(), fields: missing }, *span));
                    }

                    let mut typed_fields = Vec::new();
                    for (field_name, field_expr) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, expected_ty)) => {
                                let expected = instantiate_field_type(expected_ty, info, &fresh_args);
                                let field_typed = infer_expr_inner(field_expr, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                                unify(&field_typed.ty, &expected, subst)
                                    .map_err(|e| spanned(e, *span))?;
                                typed_fields.push((field_name.clone(), field_typed));
                            }
                            None => {
                                return Err(spanned(
                                    TypeError::UnknownField {
                                        type_name: name.clone(),
                                        field_name: field_name.clone(),
                                    },
                                    *span,
                                ));
                            }
                        }
                    }

                    Ok(TypedExpr {
                        kind: TypedExprKind::StructLit {
                            name: name.clone(),
                            fields: typed_fields,
                        },
                        ty: struct_ty,
                        span: *span,
                    })
                }
                _ => Err(spanned(
                    TypeError::NotAStruct { actual: Type::Named(name.clone(), vec![]) },
                    *span,
                )),
            }
        }

        Expr::List { span, .. } => Err(spanned(
            TypeError::UnsupportedExpr { description: "list literals".to_string() }, *span,
        )),
        Expr::QuestionMark { span, .. } => Err(spanned(
            TypeError::UnsupportedExpr { description: "? operator".to_string() }, *span,
        )),
    }
}

/// Check a pattern against an expected type, binding variables in the environment.
fn check_pattern(
    pattern: &Pattern,
    expected: &Type,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    span: krypton_parser::ast::Span,
) -> Result<(), SpannedTypeError> {
    match pattern {
        Pattern::Wildcard { .. } => Ok(()),

        Pattern::Var { name, .. } => {
            env.bind(name.clone(), TypeScheme::mono(expected.clone()));
            Ok(())
        }

        Pattern::Lit { value, .. } => {
            let lit_ty = match value {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::Bool(_) => Type::Bool,
                Lit::String(_) => Type::String,
                Lit::Unit => Type::Unit,
            };
            unify(expected, &lit_ty, subst).map_err(|e| spanned(e, span))
        }

        Pattern::Constructor { name, args, .. } => {
            match env.lookup(name) {
                Some(scheme) => {
                    let scheme = scheme.clone();
                    let instantiated = scheme.instantiate(&mut || gen.fresh());
                    match instantiated {
                        Type::Fn(param_types, ret_type) => {
                            unify(expected, &ret_type, subst).map_err(|e| spanned(e, span))?;
                            if args.len() != param_types.len() {
                                return Err(spanned(
                                    TypeError::WrongArity {
                                        expected: param_types.len(),
                                        actual: args.len(),
                                    },
                                    span,
                                ));
                            }
                            for (arg_pat, param_ty) in args.iter().zip(param_types.iter()) {
                                let resolved_param = subst.apply(param_ty);
                                check_pattern(arg_pat, &resolved_param, env, subst, gen, registry, span)?;
                            }
                            Ok(())
                        }
                        _ => {
                            // Nullary variant
                            unify(expected, &instantiated, subst).map_err(|e| spanned(e, span))?;
                            if !args.is_empty() {
                                return Err(spanned(
                                    TypeError::WrongArity {
                                        expected: 0,
                                        actual: args.len(),
                                    },
                                    span,
                                ));
                            }
                            Ok(())
                        }
                    }
                }
                None => Err(spanned(
                    TypeError::UnknownVariable { name: name.clone() },
                    span,
                )),
            }
        }

        Pattern::Tuple { elements, .. } => {
            let fresh_vars: Vec<Type> = elements.iter().map(|_| Type::Var(gen.fresh())).collect();
            unify(expected, &Type::Tuple(fresh_vars.clone()), subst).map_err(|e| spanned(e, span))?;
            for (elem_pat, fresh_var) in elements.iter().zip(fresh_vars.iter()) {
                let resolved = subst.apply(fresh_var);
                check_pattern(elem_pat, &resolved, env, subst, gen, registry, span)?;
            }
            Ok(())
        }

        Pattern::StructPat { name, fields, .. } => {
            let reg = registry.ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: expected.clone() }, span)
            })?;
            let info = reg.lookup_type(name).ok_or_else(|| {
                spanned(TypeError::UnknownVariable { name: name.clone() }, span)
            })?;
            // Create fresh type args for the struct's type params
            let fresh_args: Vec<Type> = info.type_param_vars.iter().map(|_| Type::Var(gen.fresh())).collect();
            let struct_ty = Type::Named(name.clone(), fresh_args.clone());
            unify(expected, &struct_ty, subst).map_err(|e| spanned(e, span))?;
            match &info.kind {
                type_registry::TypeKind::Record { fields: record_fields } => {
                    for (field_name, field_pat) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, field_ty)) => {
                                let instantiated = instantiate_field_type(field_ty, info, &fresh_args);
                                let resolved = subst.apply(&instantiated);
                                check_pattern(field_pat, &resolved, env, subst, gen, registry, span)?;
                            }
                            None => {
                                return Err(spanned(
                                    TypeError::UnknownField {
                                        type_name: name.clone(),
                                        field_name: field_name.clone(),
                                    },
                                    span,
                                ));
                            }
                        }
                    }
                    Ok(())
                }
                _ => Err(spanned(
                    TypeError::NotAStruct { actual: expected.clone() },
                    span,
                )),
            }
        }
    }
}

/// Given a resolved type and a field name, look up the field in the type registry
/// and return the field's type with type parameters instantiated.
fn resolve_field_access(
    resolved_ty: &Type,
    field_name: &str,
    span: krypton_parser::ast::Span,
    registry: Option<&TypeRegistry>,
) -> Result<Type, SpannedTypeError> {
    match resolved_ty {
        Type::Named(name, type_args) => {
            let registry = registry.ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            let info = registry.lookup_type(name).ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            match &info.kind {
                type_registry::TypeKind::Record { fields } => {
                    let field_ty = fields.iter().find(|(n, _)| n == field_name);
                    match field_ty {
                        Some((_, ty)) => {
                            let instantiated = instantiate_field_type(ty, info, type_args);
                            Ok(instantiated)
                        }
                        None => Err(spanned(
                            TypeError::UnknownField {
                                type_name: name.clone(),
                                field_name: field_name.to_string(),
                            },
                            span,
                        )),
                    }
                }
                _ => Err(spanned(
                    TypeError::NotAStruct { actual: resolved_ty.clone() },
                    span,
                )),
            }
        }
        _ => Err(spanned(
            TypeError::NotAStruct { actual: resolved_ty.clone() },
            span,
        )),
    }
}

/// Instantiate a field type from the registry by substituting the original
/// type parameter var ids with the concrete type arguments.
fn instantiate_field_type(
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

/// Validate a struct update expression and return typed field expressions.
fn resolve_struct_update(
    resolved_ty: &Type,
    fields: &[(String, Expr)],
    span: krypton_parser::ast::Span,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    recur_params: Option<&[Type]>,
    mut let_own_spans: Option<&mut HashSet<Span>>,
    mut lambda_own_captures: Option<&mut HashMap<Span, String>>,
) -> Result<Vec<(String, TypedExpr)>, SpannedTypeError> {
    match resolved_ty {
        Type::Named(name, type_args) => {
            let reg = registry.ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            let info = reg.lookup_type(name).ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            match &info.kind {
                type_registry::TypeKind::Record { fields: record_fields } => {
                    let mut typed_fields = Vec::new();
                    for (field_name, field_expr) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, expected_ty)) => {
                                let expected = instantiate_field_type(expected_ty, info, type_args);
                                let field_typed = infer_expr_inner(field_expr, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                                unify(&field_typed.ty, &expected, subst)
                                    .map_err(|e| spanned(e, span))?;
                                typed_fields.push((field_name.clone(), field_typed));
                            }
                            None => {
                                return Err(spanned(
                                    TypeError::UnknownField {
                                        type_name: name.clone(),
                                        field_name: field_name.clone(),
                                    },
                                    span,
                                ));
                            }
                        }
                    }
                    Ok(typed_fields)
                }
                _ => Err(spanned(
                    TypeError::NotAStruct { actual: resolved_ty.clone() },
                    span,
                )),
            }
        }
        _ => Err(spanned(
            TypeError::NotAStruct { actual: resolved_ty.clone() },
            span,
        )),
    }
}

/// Check if a lambda body references any free variables (not in `params`) whose
/// type in `env` (after substitution) is `Own(...)`.
fn captures_own_value(body: &Expr, params: &HashSet<&str>, env: &TypeEnv, subst: &Substitution) -> bool {
    match body {
        Expr::Var { name, .. } => {
            if !params.contains(name.as_str()) {
                if let Some(scheme) = env.lookup(name) {
                    let ty = subst.apply(&scheme.ty);
                    return matches!(ty, Type::Own(_));
                }
            }
            false
        }
        Expr::App { func, args, .. } => {
            captures_own_value(func, params, env, subst)
                || args.iter().any(|a| captures_own_value(a, params, env, subst))
        }
        Expr::Let { name, value, body: let_body, .. } => {
            if captures_own_value(value, params, env, subst) {
                return true;
            }
            if let Some(b) = let_body {
                let mut inner = params.clone();
                inner.insert(name.as_str());
                return captures_own_value(b, &inner, env, subst);
            }
            false
        }
        Expr::LetPattern { value, body, .. } => {
            captures_own_value(value, params, env, subst)
                || body.as_ref().is_some_and(|b| captures_own_value(b, params, env, subst))
        }
        Expr::Do { exprs, .. } => exprs.iter().any(|e| captures_own_value(e, params, env, subst)),
        Expr::If { cond, then_, else_, .. } => {
            captures_own_value(cond, params, env, subst)
                || captures_own_value(then_, params, env, subst)
                || captures_own_value(else_, params, env, subst)
        }
        Expr::Match { scrutinee, arms, .. } => {
            captures_own_value(scrutinee, params, env, subst)
                || arms.iter().any(|a| captures_own_value(&a.body, params, env, subst))
        }
        Expr::BinaryOp { lhs, rhs, .. } => {
            captures_own_value(lhs, params, env, subst) || captures_own_value(rhs, params, env, subst)
        }
        Expr::UnaryOp { operand, .. } => captures_own_value(operand, params, env, subst),
        Expr::Lambda { params: inner_params, body, .. } => {
            let mut inner = params.clone();
            for p in inner_params {
                inner.insert(p.name.as_str());
            }
            captures_own_value(body, &inner, env, subst)
        }
        Expr::FieldAccess { expr, .. } => captures_own_value(expr, params, env, subst),
        Expr::StructLit { fields, .. } => fields.iter().any(|(_, e)| captures_own_value(e, params, env, subst)),
        Expr::StructUpdate { base, fields, .. } => {
            captures_own_value(base, params, env, subst)
                || fields.iter().any(|(_, e)| captures_own_value(e, params, env, subst))
        }
        Expr::Tuple { elements, .. } => elements.iter().any(|e| captures_own_value(e, params, env, subst)),
        Expr::Recur { args, .. } => args.iter().any(|a| captures_own_value(a, params, env, subst)),
        Expr::QuestionMark { expr, .. } => captures_own_value(expr, params, env, subst),
        Expr::List { elements, .. } => elements.iter().any(|e| captures_own_value(e, params, env, subst)),
        Expr::Lit { .. } => false,
    }
}

/// Return the name of the first free variable (not in `params`) whose type in
/// `env` (after substitution) is `Own(...)`.
fn first_own_capture(body: &Expr, params: &HashSet<&str>, env: &TypeEnv, subst: &Substitution) -> Option<String> {
    match body {
        Expr::Var { name, .. } => {
            if !params.contains(name.as_str()) {
                if let Some(scheme) = env.lookup(name) {
                    let ty = subst.apply(&scheme.ty);
                    if matches!(ty, Type::Own(_)) {
                        return Some(name.clone());
                    }
                }
            }
            None
        }
        Expr::App { func, args, .. } => {
            first_own_capture(func, params, env, subst)
                .or_else(|| args.iter().find_map(|a| first_own_capture(a, params, env, subst)))
        }
        Expr::Let { name, value, body: let_body, .. } => {
            if let Some(found) = first_own_capture(value, params, env, subst) {
                return Some(found);
            }
            if let Some(b) = let_body {
                let mut inner = params.clone();
                inner.insert(name.as_str());
                return first_own_capture(b, &inner, env, subst);
            }
            None
        }
        Expr::LetPattern { value, body, .. } => {
            first_own_capture(value, params, env, subst)
                .or_else(|| body.as_ref().and_then(|b| first_own_capture(b, params, env, subst)))
        }
        Expr::Do { exprs, .. } => exprs.iter().find_map(|e| first_own_capture(e, params, env, subst)),
        Expr::If { cond, then_, else_, .. } => {
            first_own_capture(cond, params, env, subst)
                .or_else(|| first_own_capture(then_, params, env, subst))
                .or_else(|| first_own_capture(else_, params, env, subst))
        }
        Expr::Match { scrutinee, arms, .. } => {
            first_own_capture(scrutinee, params, env, subst)
                .or_else(|| arms.iter().find_map(|a| first_own_capture(&a.body, params, env, subst)))
        }
        Expr::BinaryOp { lhs, rhs, .. } => {
            first_own_capture(lhs, params, env, subst)
                .or_else(|| first_own_capture(rhs, params, env, subst))
        }
        Expr::UnaryOp { operand, .. } => first_own_capture(operand, params, env, subst),
        Expr::Lambda { params: inner_params, body, .. } => {
            let mut inner = params.clone();
            for p in inner_params {
                inner.insert(p.name.as_str());
            }
            first_own_capture(body, &inner, env, subst)
        }
        Expr::FieldAccess { expr, .. } => first_own_capture(expr, params, env, subst),
        Expr::StructLit { fields, .. } => fields.iter().find_map(|(_, e)| first_own_capture(e, params, env, subst)),
        Expr::StructUpdate { base, fields, .. } => {
            first_own_capture(base, params, env, subst)
                .or_else(|| fields.iter().find_map(|(_, e)| first_own_capture(e, params, env, subst)))
        }
        Expr::Tuple { elements, .. } => elements.iter().find_map(|e| first_own_capture(e, params, env, subst)),
        Expr::Recur { args, .. } => args.iter().find_map(|a| first_own_capture(a, params, env, subst)),
        Expr::QuestionMark { expr, .. } => first_own_capture(expr, params, env, subst),
        Expr::List { elements, .. } => elements.iter().find_map(|e| first_own_capture(e, params, env, subst)),
        Expr::Lit { .. } => None,
    }
}

/// Format an inferred type for display, renaming type variables to a, b, c, ...
/// and wrapping polymorphic types in `forall`.
pub fn display_type(ty: &Type, subst: &Substitution, env: &TypeEnv) -> String {
    let scheme = generalize(ty, env, subst);
    format!("{}", scheme)
}

/// Walk a typed expression tree and record struct update info for each
/// `StructUpdate` node: maps its span to (type_name, set of updated field names).
fn collect_struct_update_info(expr: &TypedExpr, info: &mut HashMap<Span, (String, HashSet<String>)>) {
    match &expr.kind {
        TypedExprKind::StructUpdate { base, fields } => {
            let inner_ty = match &base.ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            if let Type::Named(name, _) = inner_ty {
                let field_names: HashSet<String> = fields.iter().map(|(n, _)| n.clone()).collect();
                info.insert(expr.span, (name.clone(), field_names));
            }
            collect_struct_update_info(base, info);
            for (_, e) in fields {
                collect_struct_update_info(e, info);
            }
        }
        TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        TypedExprKind::App { func, args } => {
            collect_struct_update_info(func, info);
            for a in args { collect_struct_update_info(a, info); }
        }
        TypedExprKind::If { cond, then_, else_ } => {
            collect_struct_update_info(cond, info);
            collect_struct_update_info(then_, info);
            collect_struct_update_info(else_, info);
        }
        TypedExprKind::Let { value, body, .. } => {
            collect_struct_update_info(value, info);
            if let Some(b) = body { collect_struct_update_info(b, info); }
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs { collect_struct_update_info(e, info); }
        }
        TypedExprKind::Match { scrutinee, arms } => {
            collect_struct_update_info(scrutinee, info);
            for arm in arms { collect_struct_update_info(&arm.body, info); }
        }
        TypedExprKind::Lambda { body, .. } => collect_struct_update_info(body, info),
        TypedExprKind::FieldAccess { expr, .. } => collect_struct_update_info(expr, info),
        TypedExprKind::Recur(args) => {
            for a in args { collect_struct_update_info(a, info); }
        }
        TypedExprKind::Tuple(elems) => {
            for e in elems { collect_struct_update_info(e, info); }
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            collect_struct_update_info(lhs, info);
            collect_struct_update_info(rhs, info);
        }
        TypedExprKind::UnaryOp { operand, .. } => collect_struct_update_info(operand, info),
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields { collect_struct_update_info(e, info); }
        }
        TypedExprKind::LetPattern { value, body, .. } => {
            collect_struct_update_info(value, info);
            if let Some(b) = body { collect_struct_update_info(b, info); }
        }
    }
}

/// Infer types for all top-level definitions in a module.
///
/// Uses SCC (strongly connected component) analysis to process definitions
/// in dependency order. Functions within the same SCC are inferred together
/// as a mutually recursive group, then generalized before later SCCs see them.
pub fn infer_module(module: &Module) -> Result<TypedModule, SpannedTypeError> {
    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();
    let mut registry = TypeRegistry::new();
    let mut let_own_spans: HashSet<Span> = HashSet::new();
    let mut lambda_own_captures: HashMap<Span, String> = HashMap::new();

    // First pass: process all DefType declarations
    let mut constructor_schemes: Vec<(String, TypeScheme)> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            let constructors =
                type_registry::process_type_decl(type_decl, &mut registry, &mut gen)
                    .map_err(|e| spanned(e, type_decl.span))?;
            for (name, scheme) in constructors {
                env.bind(name.clone(), scheme.clone());
                constructor_schemes.push((name, scheme));
            }
        }
    }

    // Collect DefFn declarations
    let fn_decls: Vec<&krypton_parser::ast::FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Build dependency graph and compute SCCs in topological order
    let adj = scc::build_dependency_graph(&fn_decls);
    let sccs = scc::tarjan_scc(&adj);

    // Store results indexed by declaration order
    let mut result_schemes: Vec<Option<TypeScheme>> = vec![None; fn_decls.len()];
    let mut fn_bodies: Vec<Option<TypedExpr>> = vec![None; fn_decls.len()];

    // Process each SCC in topological order (dependencies first)
    for component in &sccs {
        // Bind each name in the SCC to a fresh type variable (monomorphic within SCC)
        let mut pre_bound: Vec<(usize, Type)> = Vec::new();
        for &idx in component {
            let tv = Type::Var(gen.fresh());
            env.bind(fn_decls[idx].name.clone(), TypeScheme::mono(tv.clone()));
            pre_bound.push((idx, tv));
        }

        // Infer all bodies in the SCC
        for &(idx, ref tv) in &pre_bound {
            let decl = fn_decls[idx];
            env.push_scope();
            let mut param_types = Vec::new();
            for p in &decl.params {
                let ptv = Type::Var(gen.fresh());
                if let Some(ref ty_expr) = p.ty {
                    let empty_map = HashMap::new();
                    let annotated_ty = type_registry::resolve_type_expr(ty_expr, &empty_map, &registry);
                    unify(&ptv, &annotated_ty, &mut subst)
                        .map_err(|e| spanned(e, decl.span))?;
                }
                param_types.push(ptv.clone());
                env.bind(p.name.clone(), TypeScheme::mono(ptv));
            }
            let body_typed = infer_expr_inner(&decl.body, &mut env, &mut subst, &mut gen, Some(&registry), Some(&param_types), Some(&mut let_own_spans), Some(&mut lambda_own_captures))?;
            env.pop_scope();

            let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
            let body_ty = subst.apply(&body_typed.ty);
            let fn_ty = Type::Fn(param_types, Box::new(body_ty));
            unify(tv, &fn_ty, &mut subst)
                .map_err(|e| spanned(e, decl.span))?;

            fn_bodies[idx] = Some(body_typed);
        }

        // Generalize all types in the SCC and update env with polymorphic schemes
        let empty_env = TypeEnv::new();
        for &(idx, ref tv) in &pre_bound {
            let final_ty = subst.apply(tv);
            let scheme = generalize(&final_ty, &empty_env, &subst);
            env.bind(fn_decls[idx].name.clone(), scheme.clone());
            result_schemes[idx] = Some(scheme);
        }
    }

    // Collect results: constructors first, then functions in declaration order
    let mut results: Vec<(String, TypeScheme)> = constructor_schemes;
    results.extend(
        fn_decls
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.clone(), result_schemes[i].clone().unwrap())),
    );

    // Apply final substitution to all typed function bodies
    let mut functions = Vec::new();
    for (i, decl) in fn_decls.iter().enumerate() {
        let mut body = fn_bodies[i].take().unwrap();
        typed_ast::apply_subst(&mut body, &subst);
        functions.push(TypedFnDecl {
            name: decl.name.clone(),
            params: decl.params.iter().map(|p| p.name.clone()).collect(),
            body,
        });
    }

    // Collect struct update info (type name + updated fields) from typed AST
    let mut struct_update_info: HashMap<Span, (String, HashSet<String>)> = HashMap::new();
    for func in &functions {
        collect_struct_update_info(&func.body, &mut struct_update_info);
    }

    // Run affine ownership verification after successful inference
    crate::ownership::check_ownership(module, &results, &registry, &let_own_spans, &lambda_own_captures, &struct_update_info)?;

    Ok(TypedModule {
        fn_types: results,
        functions,
    })
}
