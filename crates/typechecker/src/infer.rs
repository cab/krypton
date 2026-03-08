use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Decl, Expr, Lit, Module, Pattern, Span, UnaryOp};

use crate::scc;
use crate::trait_registry::{self, TraitInfo, TraitMethod, TraitRegistry, InstanceInfo};
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{self, ExternFnInfo, TraitDefInfo, InstanceDefInfo, TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedModule};
use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{unify, SpannedTypeError, TypeError};

/// Strip `Own` wrapper from non-function types.
/// Used at consumption sites (binary ops, if conditions, etc.) where
/// the ownership wrapper is not meaningful.
fn strip_own(ty: &Type) -> Type {
    match ty {
        Type::Own(inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => *inner.clone(),
        other => other.clone(),
    }
}

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
    let mut out = HashSet::new();
    free_vars_into(ty, &mut out);
    out
}

/// Recursive accumulator for `free_vars`.
fn free_vars_into(ty: &Type, out: &mut HashSet<TypeVarId>) {
    match ty {
        Type::Var(id) => { out.insert(*id); }
        Type::Fn(params, ret) => {
            for p in params {
                free_vars_into(p, out);
            }
            free_vars_into(ret, out);
        }
        Type::Named(_, args) => {
            for a in args {
                free_vars_into(a, out);
            }
        }
        Type::Own(inner) => free_vars_into(inner, out),
        Type::Tuple(elems) => {
            for e in elems {
                free_vars_into(e, out);
            }
        }
        _ => {}
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
            Ok(TypedExpr { kind: TypedExprKind::Lit(value.clone()), ty: Type::Own(Box::new(ty)), span: *span })
        }

        Expr::Var { name, span, .. } => match env.lookup(name) {
            Some(scheme) => {
                let scheme = scheme.clone();
                let ty = scheme.instantiate(&mut || gen.fresh());
                let ty = if !matches!(&ty, Type::Fn(_, _))
                    && registry.is_some_and(|r| r.is_constructor(name))
                {
                    Type::Own(Box::new(ty))
                } else {
                    ty
                };
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
            let ty = if let Some(cap_name) = first_own_capture(body, &param_names, env, subst) {
                if let Some(ref mut captures) = lambda_own_captures {
                    captures.insert(*span, cap_name);
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
            let ty = if is_constructor { Type::Own(Box::new(ty)) } else { ty };
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
                    let resolved = strip_own(&subst.apply(&lhs_typed.ty));
                    match &resolved {
                        Type::Var(_) => {
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                            Type::Int
                        }
                        _ => resolved,
                    }
                }
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    unify(&lhs_typed.ty, &rhs_typed.ty, subst)
                        .map_err(|e| spanned(e, *span))?;
                    let resolved = strip_own(&subst.apply(&lhs_typed.ty));
                    if let Type::Var(_) = &resolved {
                        unify(&resolved, &Type::Int, subst)
                            .map_err(|e| spanned(e, *span))?;
                    }
                    Type::Bool
                }
                BinOp::And | BinOp::Or => {
                    unify(&lhs_typed.ty, &Type::Bool, subst)
                        .map_err(|e| spanned(e, *span))?;
                    unify(&rhs_typed.ty, &Type::Bool, subst)
                        .map_err(|e| spanned(e, *span))?;
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
                    let resolved = strip_own(&subst.apply(&operand_typed.ty));
                    match &resolved {
                        Type::Var(_) => {
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                            Type::Int
                        }
                        _ => resolved,
                    }
                }
                UnaryOp::Not => {
                    unify(&operand_typed.ty, &Type::Bool, subst)
                        .map_err(|e| spanned(e, *span))?;
                    Type::Bool
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
            let scrutinee_ty = subst.apply(&scrutinee_typed.ty);
            // Unwrap Own wrapper — match works on the inner type
            let match_ty = match &scrutinee_ty {
                Type::Own(inner) => inner.as_ref().clone(),
                other => other.clone(),
            };
            let result_ty = Type::Var(gen.fresh());
            let mut typed_arms = Vec::new();
            for arm in arms {
                env.push_scope();
                check_pattern(&arm.pattern, &match_ty, env, subst, gen, registry, *span)?;
                let body_typed = infer_expr_inner(&arm.body, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                unify(&result_ty, &body_typed.ty, subst).map_err(|e| spanned(e, *span))?;
                env.pop_scope();
                typed_arms.push(TypedMatchArm {
                    pattern: arm.pattern.clone(),
                    body: body_typed,
                });
            }
            let match_ty = subst.apply(&match_ty);
            crate::exhaustiveness::check_exhaustiveness(
                &match_ty,
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
                        ty: Type::Own(Box::new(struct_ty)),
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

/// Substitute a type variable with a concrete type throughout a type.
fn substitute_type_var(ty: &Type, var_id: TypeVarId, replacement: &Type) -> Type {
    match ty {
        Type::Var(id) if *id == var_id => replacement.clone(),
        Type::Var(_) | Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit => ty.clone(),
        Type::Fn(params, ret) => {
            let new_params = params.iter().map(|p| substitute_type_var(p, var_id, replacement)).collect();
            let new_ret = substitute_type_var(ret, var_id, replacement);
            Type::Fn(new_params, Box::new(new_ret))
        }
        Type::Named(name, args) => {
            let new_args = args.iter().map(|a| substitute_type_var(a, var_id, replacement)).collect();
            Type::Named(name.clone(), new_args)
        }
        Type::Own(inner) => Type::Own(Box::new(substitute_type_var(inner, var_id, replacement))),
        Type::Tuple(elems) => {
            let new_elems = elems.iter().map(|e| substitute_type_var(e, var_id, replacement)).collect();
            Type::Tuple(new_elems)
        }
    }
}

/// Detect trait method calls on type variables (indicating the function needs a dict param).
fn detect_trait_constraints(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, String>,
    subst: &Substitution,
    constraints: &mut Vec<String>,
) {
    match &expr.kind {
        TypedExprKind::App { func, args } => {
            if let TypedExprKind::Var(name) = &func.kind {
                if let Some(trait_name) = trait_method_map.get(name) {
                    if let Some(first_arg) = args.first() {
                        let arg_ty = subst.apply(&first_arg.ty);
                        let concrete_ty = strip_own(&arg_ty);
                        if matches!(concrete_ty, Type::Var(_)) {
                            constraints.push(trait_name.clone());
                        }
                    }
                }
            }
            detect_trait_constraints(func, trait_method_map, subst, constraints);
            for arg in args {
                detect_trait_constraints(arg, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::Lambda { body, .. } => {
            detect_trait_constraints(body, trait_method_map, subst, constraints);
        }
        TypedExprKind::If { cond, then_, else_ } => {
            detect_trait_constraints(cond, trait_method_map, subst, constraints);
            detect_trait_constraints(then_, trait_method_map, subst, constraints);
            detect_trait_constraints(else_, trait_method_map, subst, constraints);
        }
        TypedExprKind::Let { value, body, .. } => {
            detect_trait_constraints(value, trait_method_map, subst, constraints);
            if let Some(body) = body {
                detect_trait_constraints(body, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs {
                detect_trait_constraints(e, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::Match { scrutinee, arms } => {
            detect_trait_constraints(scrutinee, trait_method_map, subst, constraints);
            for arm in arms {
                detect_trait_constraints(&arm.body, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            detect_trait_constraints(lhs, trait_method_map, subst, constraints);
            detect_trait_constraints(rhs, trait_method_map, subst, constraints);
        }
        TypedExprKind::UnaryOp { operand, .. } => {
            detect_trait_constraints(operand, trait_method_map, subst, constraints);
        }
        TypedExprKind::FieldAccess { expr, .. } => {
            detect_trait_constraints(expr, trait_method_map, subst, constraints);
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields {
                detect_trait_constraints(e, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::StructUpdate { base, fields, .. } => {
            detect_trait_constraints(base, trait_method_map, subst, constraints);
            for (_, e) in fields {
                detect_trait_constraints(e, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::LetPattern { value, body, .. } => {
            detect_trait_constraints(value, trait_method_map, subst, constraints);
            if let Some(body) = body {
                detect_trait_constraints(body, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::Tuple(elems) | TypedExprKind::Recur(elems) => {
            for e in elems {
                detect_trait_constraints(e, trait_method_map, subst, constraints);
            }
        }
        TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
    }
}

/// Walk a typed AST looking for calls to trait methods. For each call,
/// resolve the argument type and verify that a matching instance exists.
fn check_trait_instances(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, String>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
) -> Result<(), SpannedTypeError> {
    match &expr.kind {
        TypedExprKind::App { func, args } => {
            // Check if the function being called is a trait method
            if let TypedExprKind::Var(name) = &func.kind {
                if let Some(trait_name) = trait_method_map.get(name) {
                    // Resolve the first argument's type to determine the concrete type
                    if let Some(first_arg) = args.first() {
                        let arg_ty = subst.apply(&first_arg.ty);
                        let concrete_ty = strip_own(&arg_ty);
                        // Skip check if type is still a variable (constrained function)
                        if !matches!(concrete_ty, Type::Var(_))
                            && trait_registry.find_instance(trait_name, &concrete_ty).is_none()
                        {
                            return Err(spanned(
                                TypeError::NoInstance {
                                    trait_name: trait_name.clone(),
                                    ty: format!("{}", concrete_ty),
                                    required_by: None,
                                },
                                expr.span,
                            ));
                        }
                    }
                }
            }
            // Recurse into func and args
            check_trait_instances(func, trait_method_map, trait_registry, subst)?;
            for arg in args {
                check_trait_instances(arg, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::Lambda { body, .. } => {
            check_trait_instances(body, trait_method_map, trait_registry, subst)?;
        }
        TypedExprKind::If { cond, then_, else_ } => {
            check_trait_instances(cond, trait_method_map, trait_registry, subst)?;
            check_trait_instances(then_, trait_method_map, trait_registry, subst)?;
            check_trait_instances(else_, trait_method_map, trait_registry, subst)?;
        }
        TypedExprKind::Let { value, body, .. } => {
            check_trait_instances(value, trait_method_map, trait_registry, subst)?;
            if let Some(body) = body {
                check_trait_instances(body, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs {
                check_trait_instances(e, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::Match { scrutinee, arms } => {
            check_trait_instances(scrutinee, trait_method_map, trait_registry, subst)?;
            for arm in arms {
                check_trait_instances(&arm.body, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::FieldAccess { expr: inner, .. } => {
            check_trait_instances(inner, trait_method_map, trait_registry, subst)?;
        }
        TypedExprKind::BinaryOp { op, lhs, rhs } => {
            // Check that the operand type has the required trait instance
            let trait_name = match op {
                BinOp::Add => "Add",
                BinOp::Sub => "Sub",
                BinOp::Mul => "Mul",
                BinOp::Div => "Div",
                BinOp::Eq | BinOp::Neq => "Eq",
                BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => "Ord",
                BinOp::And | BinOp::Or => {
                    // Boolean ops don't require trait instances
                    check_trait_instances(lhs, trait_method_map, trait_registry, subst)?;
                    check_trait_instances(rhs, trait_method_map, trait_registry, subst)?;
                    return Ok(());
                }
            };
            let operand_ty = strip_own(&subst.apply(&lhs.ty));
            if !matches!(operand_ty, Type::Var(_))
                && trait_registry.find_instance(trait_name, &operand_ty).is_none()
            {
                return Err(spanned(
                    TypeError::NoInstance {
                        trait_name: trait_name.to_string(),
                        ty: format!("{}", operand_ty),
                        required_by: None,
                    },
                    expr.span,
                ));
            }
            check_trait_instances(lhs, trait_method_map, trait_registry, subst)?;
            check_trait_instances(rhs, trait_method_map, trait_registry, subst)?;
        }
        TypedExprKind::UnaryOp { op, operand } => {
            let trait_name = match op {
                UnaryOp::Neg => "Neg",
                UnaryOp::Not => {
                    // Boolean NOT doesn't require trait instances
                    check_trait_instances(operand, trait_method_map, trait_registry, subst)?;
                    return Ok(());
                }
            };
            let operand_ty = strip_own(&subst.apply(&operand.ty));
            if !matches!(operand_ty, Type::Var(_))
                && trait_registry.find_instance(trait_name, &operand_ty).is_none()
            {
                return Err(spanned(
                    TypeError::NoInstance {
                        trait_name: trait_name.to_string(),
                        ty: format!("{}", operand_ty),
                        required_by: None,
                    },
                    expr.span,
                ));
            }
            check_trait_instances(operand, trait_method_map, trait_registry, subst)?;
        }
        TypedExprKind::Tuple(elems) => {
            for e in elems {
                check_trait_instances(e, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields {
                check_trait_instances(e, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::StructUpdate { base, fields, .. } => {
            check_trait_instances(base, trait_method_map, trait_registry, subst)?;
            for (_, e) in fields {
                check_trait_instances(e, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::LetPattern { value, body, .. } => {
            check_trait_instances(value, trait_method_map, trait_registry, subst)?;
            if let Some(body) = body {
                check_trait_instances(body, trait_method_map, trait_registry, subst)?;
            }
        }
        TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        TypedExprKind::Recur(args) => {
            for a in args {
                check_trait_instances(a, trait_method_map, trait_registry, subst)?;
            }
        }
    }
    Ok(())
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

    // Seed intrinsic function types (user defs can shadow these)
    crate::intrinsics::register_intrinsics(&mut env, &mut gen);

    // Seed prelude types (Option, Result, List, Ordering) from stdlib
    crate::prelude::register_prelude_types(&mut env, &mut registry, &mut gen);

    // Process ExternJava declarations
    let mut extern_fns: Vec<ExternFnInfo> = Vec::new();
    for decl in &module.decls {
        if let Decl::ExternJava { class_name, methods, span } = decl {
            let empty_map = HashMap::new();
            for method in methods {
                let mut scheme_vars = Vec::new();
                let mut param_types = Vec::new();
                for ty_expr in &method.param_types {
                    let resolved = type_registry::resolve_type_expr(ty_expr, &empty_map, &registry)
                        .map_err(|e| spanned(e, *span))?;
                    if matches!(&resolved, Type::Named(n, args) if n == "Object" && args.is_empty()) {
                        let fresh = gen.fresh();
                        scheme_vars.push(fresh);
                        param_types.push(Type::Var(fresh));
                    } else {
                        param_types.push(resolved);
                    }
                }

                let return_type = type_registry::resolve_type_expr(&method.return_type, &empty_map, &registry)
                    .map_err(|e| spanned(e, *span))?;
                let ret = if matches!(&return_type, Type::Named(n, args) if n == "Object" && args.is_empty()) {
                    let fresh = gen.fresh();
                    scheme_vars.push(fresh);
                    Type::Var(fresh)
                } else {
                    return_type.clone()
                };

                let fn_ty = Type::Fn(param_types.clone(), Box::new(ret));
                let scheme = if scheme_vars.is_empty() {
                    TypeScheme::mono(fn_ty)
                } else {
                    TypeScheme { vars: scheme_vars, ty: fn_ty }
                };
                env.bind(method.name.clone(), scheme);

                // Store concrete types for codegen (Object stays as-is)
                let mut concrete_params = Vec::new();
                for ty_expr in &method.param_types {
                    concrete_params.push(type_registry::resolve_type_expr(ty_expr, &empty_map, &registry)
                        .map_err(|e| spanned(e, *span))?);
                }
                extern_fns.push(ExternFnInfo {
                    name: method.name.clone(),
                    java_class: class_name.clone(),
                    param_types: concrete_params,
                    return_type,
                });
            }
        }
    }

    // Pre-register all type names so self-referential and mutually
    // recursive type declarations can resolve each other.
    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            registry.register_name(&type_decl.name);
        }
    }

    // First pass: process all DefType declarations
    let mut constructor_schemes: Vec<(String, TypeScheme)> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            // If shadowing a prelude type, unbind old constructors first
            if let Some(existing) = registry.lookup_type(&type_decl.name) {
                if existing.is_prelude {
                    if let crate::type_registry::TypeKind::Sum { variants } = &existing.kind {
                        for v in variants {
                            env.unbind(&v.name);
                        }
                    }
                }
            }

            let constructors =
                type_registry::process_type_decl(type_decl, &mut registry, &mut gen)
                    .map_err(|e| spanned(e, type_decl.span))?;
            for (name, scheme) in constructors {
                env.bind(name.clone(), scheme.clone());
                constructor_schemes.push((name, scheme));
            }
        }
    }

    // Register built-in operator traits (Add, Sub, Mul, Div, Eq, Ord, Neg)
    let mut trait_registry = TraitRegistry::new();
    trait_registry::register_builtin_traits(&mut trait_registry, &mut env, &mut gen);

    // Second pass: process DefTrait declarations
    for decl in &module.decls {
        if let Decl::DefTrait { name, type_var, superclasses, methods, span } = decl {
            // Skip if this trait is already registered as a built-in
            if trait_registry.lookup_trait(name).is_some() {
                continue;
            }
            let tv_id = gen.fresh();
            let mut type_param_map = HashMap::new();
            type_param_map.insert(type_var.clone(), tv_id);

            let mut trait_methods = Vec::new();
            for method in methods {
                let mut param_types = Vec::new();
                for p in &method.params {
                    if let Some(ref ty_expr) = p.ty {
                        param_types.push(type_registry::resolve_type_expr(ty_expr, &type_param_map, &registry)
                            .map_err(|e| spanned(e, method.span))?);
                    } else {
                        param_types.push(Type::Var(gen.fresh()));
                    }
                }
                let return_type = if let Some(ref ret_expr) = method.return_type {
                    type_registry::resolve_type_expr(ret_expr, &type_param_map, &registry)
                        .map_err(|e| spanned(e, method.span))?
                } else {
                    Type::Var(gen.fresh())
                };

                // Bind the method as a polymorphic function: forall a. fn(params) -> ret
                let fn_ty = Type::Fn(param_types.clone(), Box::new(return_type.clone()));
                let scheme = TypeScheme { vars: vec![tv_id], ty: fn_ty };
                env.bind(method.name.clone(), scheme);

                trait_methods.push(TraitMethod {
                    name: method.name.clone(),
                    param_types,
                    return_type,
                });
            }

            trait_registry.register_trait(TraitInfo {
                name: name.clone(),
                type_var: type_var.clone(),
                type_var_id: tv_id,
                superclasses: superclasses.clone(),
                methods: trait_methods,
                span: *span,
            }).map_err(|e| spanned(e, *span))?;
        }
    }

    // Deriving pass: process DefType declarations with `deriving` clauses
    let mut derived_impl_functions: Vec<TypedFnDecl> = Vec::new();
    let mut derived_impl_fn_types: Vec<(String, TypeScheme)> = Vec::new();
    let mut derived_instance_defs: Vec<InstanceDefInfo> = Vec::new();

    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            if type_decl.deriving.is_empty() {
                continue;
            }
            let type_info = registry.lookup_type(&type_decl.name).unwrap();

            for trait_name in &type_decl.deriving {
                if trait_registry.lookup_trait(trait_name).is_none() {
                    return Err(spanned(
                        TypeError::NoInstance {
                            trait_name: trait_name.clone(),
                            ty: type_decl.name.clone(),
                            required_by: None,
                        },
                        type_decl.span,
                    ));
                }

                // Collect all field types that need the trait
                let field_types: Vec<&Type> = match &type_info.kind {
                    crate::type_registry::TypeKind::Record { fields } => {
                        fields.iter().map(|(_, ty)| ty).collect()
                    }
                    crate::type_registry::TypeKind::Sum { variants } => {
                        variants.iter().flat_map(|v| v.fields.iter()).collect()
                    }
                };

                // Track which type params need subdictionaries
                let mut subdict_traits: Vec<(String, usize)> = Vec::new();

                // Validate that all field types have instances for this trait
                for ft in &field_types {
                    match ft {
                        Type::Var(v) => {
                            // Type parameter — record constraint
                            if let Some(idx) = type_info.type_param_vars.iter().position(|&pv| pv == *v) {
                                if !subdict_traits.iter().any(|(t, i)| t == trait_name && *i == idx) {
                                    subdict_traits.push((trait_name.clone(), idx));
                                }
                            }
                        }
                        _ => {
                            if trait_registry.find_instance(trait_name, ft).is_none() {
                                return Err(spanned(
                                    TypeError::CannotDerive {
                                        trait_name: trait_name.clone(),
                                        type_name: type_decl.name.clone(),
                                        field_type: format!("{}", ft),
                                    },
                                    type_decl.span,
                                ));
                            }
                        }
                    }
                }

                // Build the target type
                let type_args: Vec<Type> = type_info.type_param_vars.iter().map(|&v| Type::Var(v)).collect();
                let target_type = Type::Named(type_decl.name.clone(), type_args);
                let target_type_name = type_decl.name.clone();

                // Register the instance
                let method_name = match trait_name.as_str() {
                    "Eq" => "eq",
                    "Show" => "show",
                    _ => continue,
                };

                let instance = InstanceInfo {
                    trait_name: trait_name.clone(),
                    target_type: target_type.clone(),
                    target_type_name: target_type_name.clone(),
                    methods: vec![method_name.to_string()],
                    span: type_decl.span,
                    is_builtin: false,
                };
                trait_registry.register_instance(instance)
                    .map_err(|e| spanned(e, type_decl.span))?;

                // Synthesize the method body
                let syn_span: Span = (0, 0);
                let qualified_name = format!("{}${}${}", trait_name, target_type_name, method_name);

                let (body, fn_ty) = match trait_name.as_str() {
                    "Eq" => {
                        synthesize_eq_body(type_info, &target_type, syn_span)
                    }
                    "Show" => {
                        synthesize_show_body(type_info, &target_type, syn_span)
                    }
                    _ => continue,
                };

                let params = match trait_name.as_str() {
                    "Eq" => vec!["__a".to_string(), "__b".to_string()],
                    "Show" => vec!["__a".to_string()],
                    _ => vec![],
                };

                derived_impl_fn_types.push((qualified_name.clone(), TypeScheme { vars: vec![], ty: fn_ty }));
                derived_impl_functions.push(TypedFnDecl {
                    name: qualified_name.clone(),
                    params,
                    body,
                });

                derived_instance_defs.push(InstanceDefInfo {
                    trait_name: trait_name.clone(),
                    target_type_name,
                    target_type,
                    qualified_method_names: vec![(method_name.to_string(), qualified_name)],
                    subdict_traits,
                });
            }
        }
    }

    // Third pass: process DefImpl declarations
    for decl in &module.decls {
        if let Decl::DefImpl { trait_name, target_type, methods: _, span, .. } = decl {
            let empty_map = HashMap::new();
            let resolved_target = type_registry::resolve_type_expr(target_type, &empty_map, &registry)
                .map_err(|e| spanned(e, *span))?;

            // Orphan check: target must be a user-defined Named type or a built-in type
            let target_name = match &resolved_target {
                Type::Named(name, _) => {
                    if registry.lookup_type(name).is_none() {
                        return Err(spanned(TypeError::OrphanInstance {
                            trait_name: trait_name.clone(),
                            ty: name.clone(),
                        }, *span));
                    }
                    name.clone()
                }
                Type::Int => "Int".to_string(),
                Type::Float => "Float".to_string(),
                Type::Bool => "Bool".to_string(),
                Type::String => "String".to_string(),
                other => {
                    return Err(spanned(TypeError::OrphanInstance {
                        trait_name: trait_name.clone(),
                        ty: format!("{}", other),
                    }, *span));
                }
            };

            let method_names: Vec<String> = if let Decl::DefImpl { methods, .. } = decl {
                methods.iter().map(|m| m.name.clone()).collect()
            } else {
                Vec::new()
            };

            let instance = InstanceInfo {
                trait_name: trait_name.clone(),
                target_type: resolved_target,
                target_type_name: target_name,
                methods: method_names,
                span: *span,
                is_builtin: false,
            };

            // Superclass check before registering
            trait_registry.check_superclasses(&instance)
                .map_err(|e| spanned(e, *span))?;

            trait_registry.register_instance(instance)
                .map_err(|e| spanned(e, *span))?;
        }
    }

    // Collect the mapping of trait method names → trait names for post-inference resolution
    let trait_method_map: HashMap<String, String> = trait_registry.trait_method_names().into_iter().collect();

    // Check for top-level def names conflicting with user-defined trait method names
    {
        let mut user_trait_methods: HashMap<String, (String, Span)> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefTrait { name, methods, .. } = decl {
                for method in methods {
                    user_trait_methods.insert(method.name.clone(), (name.clone(), method.span));
                }
            }
        }
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if let Some((trait_name, method_span)) = user_trait_methods.get(&f.name) {
                    return Err(SpannedTypeError {
                        error: TypeError::DefinitionConflictsWithTraitMethod {
                            def_name: f.name.clone(),
                            trait_name: trait_name.clone(),
                        },
                        span: f.span,
                        note: None,
                        secondary_span: Some((*method_span, "trait method defined here".into())),
                    });
                }
            }
        }
    }

    // Collect DefFn declarations (includes impl method bodies for type checking)
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

            // Build type_param_map from explicit type parameters
            let mut type_param_map: HashMap<String, TypeVarId> = HashMap::new();
            for tp in &decl.type_params {
                type_param_map.insert(tp.clone(), gen.fresh());
            }

            let mut param_types = Vec::new();
            for p in &decl.params {
                let ptv = Type::Var(gen.fresh());
                if let Some(ref ty_expr) = p.ty {
                    let annotated_ty = type_registry::resolve_type_expr(ty_expr, &type_param_map, &registry)
                        .map_err(|e| spanned(e, decl.span))?;
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

            // Enforce return type annotation if present
            let ret_ty = if let Some(ref ret_ty_expr) = decl.return_type {
                let annotated_ret = type_registry::resolve_type_expr(ret_ty_expr, &type_param_map, &registry)
                    .map_err(|e| spanned(e, decl.span))?;
                // Fabrication guard: body must produce `own T` to satisfy an `own T` annotation.
                // Bare `T` cannot be upgraded to `own T` — ownership must come from a literal,
                // constructor, or another `own` source.
                if let Type::Own(ref inner) = annotated_ret {
                    if !matches!(inner.as_ref(), Type::Fn(_, _)) && !matches!(body_ty, Type::Own(_)) {
                        return Err(spanned(
                            TypeError::Mismatch { expected: annotated_ret.clone(), actual: body_ty.clone() },
                            decl.span,
                        ));
                    }
                }
                let coerced_body_ty = strip_own(&body_ty);
                unify(&coerced_body_ty, &annotated_ret, &mut subst)
                    .map_err(|e| spanned(e, decl.span))?;
                subst.apply(&annotated_ret)
            } else {
                strip_own(&body_ty)
            };

            let fn_ty = Type::Fn(param_types, Box::new(ret_ty));
            unify(tv, &fn_ty, &mut subst)
                .map_err(|e| spanned(e, decl.span))?;

            fn_bodies[idx] = Some(body_typed);
        }

        // Generalize against an empty env: all env bindings are either fully-quantified
        // schemes (no free vars) or current-SCC monomorphic bindings whose vars should be
        // generalized. This must change if nested let-polymorphism is added.
        let empty_env = TypeEnv::new();
        for &(idx, ref tv) in &pre_bound {
            let final_ty = subst.apply(tv);
            let scheme = generalize(&final_ty, &empty_env, &subst);
            env.bind(fn_decls[idx].name.clone(), scheme.clone());
            result_schemes[idx] = Some(scheme);
        }
    }

    // Post-inference instance resolution: check that all trait method calls have instances
    if !trait_method_map.is_empty() {
        for body in fn_bodies.iter() {
            if let Some(body) = body {
                check_trait_instances(body, &trait_method_map, &trait_registry, &subst)?;
            }
        }
    }

    // Type-check impl method bodies and produce TypedFnDecls with qualified names
    let mut impl_functions: Vec<TypedFnDecl> = Vec::new();
    let mut impl_fn_types: Vec<(String, TypeScheme)> = Vec::new();
    let mut instance_defs: Vec<InstanceDefInfo> = Vec::new();

    for decl in &module.decls {
        if let Decl::DefImpl { trait_name, target_type: _, methods, span, .. } = decl {
            // Look up the trait and instance
            let trait_info = trait_registry.lookup_trait(trait_name).unwrap();
            let tv_id = trait_info.type_var_id;

            // Find the registered instance to get the resolved target type
            let instance = trait_registry.find_instance_by_trait_and_span(trait_name, *span).unwrap();
            let resolved_target = instance.target_type.clone();
            let target_type_name = instance.target_type_name.clone();

            let mut qualified_method_names = Vec::new();

            for method in methods {
                let qualified_name = format!("{}${}${}", trait_name, target_type_name, method.name);

                // Find the trait method signature
                let trait_method = trait_info.methods.iter().find(|m| m.name == method.name).unwrap();

                // Substitute trait type var → concrete target type
                let concrete_param_types: Vec<Type> = trait_method.param_types.iter().map(|t| {
                    substitute_type_var(t, tv_id, &resolved_target)
                }).collect();
                let _concrete_ret_type = substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);

                // Type-check the method body
                env.push_scope();
                let mut param_types_inferred = Vec::new();
                for (i, p) in method.params.iter().enumerate() {
                    let ptv = Type::Var(gen.fresh());
                    if i < concrete_param_types.len() {
                        unify(&ptv, &concrete_param_types[i], &mut subst)
                            .map_err(|e| spanned(e, *span))?;
                    }
                    param_types_inferred.push(ptv.clone());
                    env.bind(p.name.clone(), TypeScheme::mono(ptv));
                }
                let body_typed = infer_expr_inner(&method.body, &mut env, &mut subst, &mut gen, Some(&registry), Some(&param_types_inferred), Some(&mut let_own_spans), Some(&mut lambda_own_captures))?;
                env.pop_scope();

                let mut body_typed = body_typed;
                typed_ast::apply_subst(&mut body_typed, &subst);

                let final_param_types: Vec<Type> = param_types_inferred.iter().map(|t| subst.apply(t)).collect();
                let final_ret_type = subst.apply(&body_typed.ty);

                let fn_ty = Type::Fn(final_param_types, Box::new(final_ret_type));
                let scheme = TypeScheme { vars: vec![], ty: fn_ty };

                impl_fn_types.push((qualified_name.clone(), scheme));
                impl_functions.push(TypedFnDecl {
                    name: qualified_name.clone(),
                    params: method.params.iter().map(|p| p.name.clone()).collect(),
                    body: body_typed,
                });

                qualified_method_names.push((method.name.clone(), qualified_name));
            }

            instance_defs.push(InstanceDefInfo {
                trait_name: trait_name.clone(),
                target_type_name,
                target_type: resolved_target,
                qualified_method_names,
                subdict_traits: vec![],
            });
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
    results.extend(impl_fn_types);
    results.extend(derived_impl_fn_types);

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
    functions.extend(impl_functions);
    functions.extend(derived_impl_functions);

    // Detect constrained functions: functions that call trait methods on type variables
    let mut fn_constraints: HashMap<String, Vec<String>> = HashMap::new();
    for func in &functions {
        let mut constraints = Vec::new();
        detect_trait_constraints(&func.body, &trait_method_map, &subst, &mut constraints);
        if !constraints.is_empty() {
            constraints.sort();
            constraints.dedup();
            fn_constraints.insert(func.name.clone(), constraints);
        }
    }

    // Build trait_defs for codegen (include built-in traits that have user instances)
    let mut trait_defs = Vec::new();
    let mut seen_traits = std::collections::HashSet::new();
    // First add built-in traits (needed if user code has `impl Add Vec2` etc.)
    for (trait_name, info) in trait_registry.traits() {
        let method_info: Vec<(String, usize)> = info.methods.iter().map(|m| {
            (m.name.clone(), m.param_types.len())
        }).collect();
        trait_defs.push(TraitDefInfo {
            name: trait_name.clone(),
            methods: method_info,
        });
        seen_traits.insert(trait_name.clone());
    }
    // Then add user-defined traits (skip if already registered as built-in)
    for decl in &module.decls {
        if let Decl::DefTrait { name, methods, .. } = decl {
            if !seen_traits.contains(name) {
                let method_info: Vec<(String, usize)> = methods.iter().map(|m| {
                    (m.name.clone(), m.params.len())
                }).collect();
                trait_defs.push(TraitDefInfo {
                    name: name.clone(),
                    methods: method_info,
                });
            }
        }
    }

    // Collect struct update info (type name + updated fields) from typed AST
    let mut struct_update_info: HashMap<Span, (String, HashSet<String>)> = HashMap::new();
    for func in &functions {
        collect_struct_update_info(&func.body, &mut struct_update_info);
    }

    // Run affine ownership verification after successful inference
    crate::ownership::check_ownership(module, &results, &registry, &let_own_spans, &lambda_own_captures, &struct_update_info)?;

    instance_defs.extend(derived_instance_defs);

    Ok(TypedModule {
        fn_types: results,
        functions,
        trait_defs,
        instance_defs,
        fn_constraints,
        trait_method_map: trait_method_map.clone(),
        extern_fns,
    })
}

/// Synthesize an `eq` method body for a derived Eq instance.
fn synthesize_eq_body(
    type_info: &crate::type_registry::TypeInfo,
    target_type: &Type,
    span: Span,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
    };
    let param_b = TypedExpr {
        kind: TypedExprKind::Var("__b".to_string()),
        ty: target_type.clone(),
        span,
    };
    let true_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(true)),
        ty: Type::Bool,
        span,
    };
    let false_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(false)),
        ty: Type::Bool,
        span,
    };

    let body = match &type_info.kind {
        crate::type_registry::TypeKind::Record { fields } => {
            if fields.is_empty() {
                true_expr()
            } else {
                // Chain: if (== .a.f1 .b.f1) (if (== .a.f2 .b.f2) ... true) false
                let mut result = true_expr();
                for (field_name, field_ty) in fields.iter().rev() {
                    let lhs = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_a.clone()),
                            field: field_name.clone(),
                        },
                        ty: field_ty.clone(),
                        span,
                    };
                    let rhs = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_b.clone()),
                            field: field_name.clone(),
                        },
                        ty: field_ty.clone(),
                        span,
                    };
                    let cmp = TypedExpr {
                        kind: TypedExprKind::BinaryOp {
                            op: BinOp::Eq,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        ty: Type::Bool,
                        span,
                    };
                    result = TypedExpr {
                        kind: TypedExprKind::If {
                            cond: Box::new(cmp),
                            then_: Box::new(result),
                            else_: Box::new(false_expr()),
                        },
                        ty: Type::Bool,
                        span,
                    };
                }
                result
            }
        }
        crate::type_registry::TypeKind::Sum { variants } => {
            // Outer match on __a, inner match on __b
            let arms: Vec<TypedMatchArm> = variants.iter().map(|variant| {
                let a_bindings: Vec<String> = (0..variant.fields.len())
                    .map(|i| format!("__x{}", i))
                    .collect();
                let a_pattern = Pattern::Constructor {
                    name: variant.name.clone(),
                    args: a_bindings.iter().map(|n| Pattern::Var { name: n.clone(), span }).collect(),
                    span,
                };

                // Inner match on __b
                let inner_arms: Vec<TypedMatchArm> = variants.iter().map(|inner_variant| {
                    if inner_variant.name == variant.name {
                        let b_bindings: Vec<String> = (0..inner_variant.fields.len())
                            .map(|i| format!("__y{}", i))
                            .collect();
                        let b_pattern = Pattern::Constructor {
                            name: inner_variant.name.clone(),
                            args: b_bindings.iter().map(|n| Pattern::Var { name: n.clone(), span }).collect(),
                            span,
                        };
                        // Compare all payload fields
                        if inner_variant.fields.is_empty() {
                            TypedMatchArm { pattern: b_pattern, body: true_expr() }
                        } else {
                            let mut result = true_expr();
                            for (i, ft) in inner_variant.fields.iter().enumerate().rev() {
                                let x = TypedExpr {
                                    kind: TypedExprKind::Var(format!("__x{}", i)),
                                    ty: ft.clone(),
                                    span,
                                };
                                let y = TypedExpr {
                                    kind: TypedExprKind::Var(format!("__y{}", i)),
                                    ty: ft.clone(),
                                    span,
                                };
                                let cmp = TypedExpr {
                                    kind: TypedExprKind::BinaryOp {
                                        op: BinOp::Eq,
                                        lhs: Box::new(x),
                                        rhs: Box::new(y),
                                    },
                                    ty: Type::Bool,
                                    span,
                                };
                                result = TypedExpr {
                                    kind: TypedExprKind::If {
                                        cond: Box::new(cmp),
                                        then_: Box::new(result),
                                        else_: Box::new(false_expr()),
                                    },
                                    ty: Type::Bool,
                                    span,
                                };
                            }
                            TypedMatchArm { pattern: b_pattern, body: result }
                        }
                    } else {
                        // Different variant → false
                        TypedMatchArm {
                            pattern: Pattern::Wildcard { span },
                            body: false_expr(),
                        }
                    }
                }).collect();

                let inner_match = TypedExpr {
                    kind: TypedExprKind::Match {
                        scrutinee: Box::new(param_b.clone()),
                        arms: inner_arms,
                    },
                    ty: Type::Bool,
                    span,
                };

                TypedMatchArm { pattern: a_pattern, body: inner_match }
            }).collect();

            TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(param_a.clone()),
                    arms,
                },
                ty: Type::Bool,
                span,
            }
        }
    };

    let fn_ty = Type::Fn(vec![target_type.clone(), target_type.clone()], Box::new(Type::Bool));
    (body, fn_ty)
}

/// Synthesize a `show` method body for a derived Show instance.
fn synthesize_show_body(
    type_info: &crate::type_registry::TypeInfo,
    target_type: &Type,
    span: Span,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
    };

    let str_lit = |s: &str| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::Lit(Lit::String(s.to_string())),
            ty: Type::String,
            span,
        }
    };

    let str_concat = |lhs: TypedExpr, rhs: TypedExpr| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::BinaryOp {
                op: BinOp::Add,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty: Type::String,
            span,
        }
    };

    let show_call = |expr: TypedExpr| -> TypedExpr {
        let arg_ty = expr.ty.clone();
        TypedExpr {
            kind: TypedExprKind::App {
                func: Box::new(TypedExpr {
                    kind: TypedExprKind::Var("show".to_string()),
                    ty: Type::Fn(vec![arg_ty], Box::new(Type::String)),
                    span,
                }),
                args: vec![expr],
            },
            ty: Type::String,
            span,
        }
    };

    let body = match &type_info.kind {
        crate::type_registry::TypeKind::Record { fields } => {
            // "Point(" + show(.a x) + ", " + show(.a y) + ")"
            let mut result = str_lit(&format!("{}(", type_info.name));
            for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                if i > 0 {
                    result = str_concat(result, str_lit(", "));
                }
                let field_access = TypedExpr {
                    kind: TypedExprKind::FieldAccess {
                        expr: Box::new(param_a.clone()),
                        field: field_name.clone(),
                    },
                    ty: field_ty.clone(),
                    span,
                };
                result = str_concat(result, show_call(field_access));
            }
            str_concat(result, str_lit(")"))
        }
        crate::type_registry::TypeKind::Sum { variants } => {
            let arms: Vec<TypedMatchArm> = variants.iter().map(|variant| {
                let bindings: Vec<String> = (0..variant.fields.len())
                    .map(|i| format!("__x{}", i))
                    .collect();
                let pattern = Pattern::Constructor {
                    name: variant.name.clone(),
                    args: bindings.iter().map(|n| Pattern::Var { name: n.clone(), span }).collect(),
                    span,
                };

                let body = if variant.fields.is_empty() {
                    str_lit(&variant.name)
                } else {
                    // "Some(" + show(x0) + ")"
                    let mut result = str_lit(&format!("{}(", variant.name));
                    for (i, ft) in variant.fields.iter().enumerate() {
                        if i > 0 {
                            result = str_concat(result, str_lit(", "));
                        }
                        let var_expr = TypedExpr {
                            kind: TypedExprKind::Var(format!("__x{}", i)),
                            ty: ft.clone(),
                            span,
                        };
                        result = str_concat(result, show_call(var_expr));
                    }
                    str_concat(result, str_lit(")"))
                };

                TypedMatchArm { pattern, body }
            }).collect();

            TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(param_a),
                    arms,
                },
                ty: Type::String,
                span,
            }
        }
    };

    let fn_ty = Type::Fn(vec![target_type.clone()], Box::new(Type::String));
    (body, fn_ty)
}
