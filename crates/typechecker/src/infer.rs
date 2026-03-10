use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Decl, ExternMethod, Expr, Lit, Module, Pattern, Span, TypeDeclKind, UnaryOp, Variant, Visibility};

use crate::scc;
use crate::trait_registry::{self, TraitInfo, TraitMethod, TraitRegistry, InstanceInfo};
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{self, ExternFnInfo, ExportedTraitDef, ExportedTraitMethod, TraitDefInfo, InstanceDefInfo, TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedModule, TypedPattern};
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
        Type::App(ctor, args) => {
            free_vars_into(ctor, out);
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

/// Recursively replace Type::Var(old_id) with Type::Var(new_id) in a type tree.
fn remap_type_var(ty: &Type, old_id: u32, new_id: u32) -> Type {
    match ty {
        Type::Var(id) if *id == old_id => Type::Var(new_id),
        Type::Fn(params, ret) => Type::Fn(
            params.iter().map(|p| remap_type_var(p, old_id, new_id)).collect(),
            Box::new(remap_type_var(ret, old_id, new_id)),
        ),
        Type::Named(name, args) => Type::Named(
            name.clone(),
            args.iter().map(|a| remap_type_var(a, old_id, new_id)).collect(),
        ),
        Type::App(ctor, args) => Type::App(
            Box::new(remap_type_var(ctor, old_id, new_id)),
            args.iter().map(|a| remap_type_var(a, old_id, new_id)).collect(),
        ),
        Type::Tuple(elems) => Type::Tuple(
            elems.iter().map(|e| remap_type_var(e, old_id, new_id)).collect(),
        ),
        Type::Own(inner) => Type::Own(Box::new(remap_type_var(inner, old_id, new_id))),
        _ => ty.clone(),
    }
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
#[tracing::instrument(level = "trace", skip_all)]
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
            let prev_fn_return_type = env.fn_return_type.take();
            env.fn_return_type = Some(Type::Var(gen.fresh()));
            let body_typed = infer_expr_inner(body, env, subst, gen, registry, None, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            env.fn_return_type = prev_fn_return_type;
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
            ty: ty_ann,
            value,
            body,
            span,
        } => {
            let val_typed = infer_expr_inner(value, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;

            // If there's a type annotation, resolve it and unify with the inferred type
            if let Some(ty_expr) = ty_ann {
                if let Some(reg) = registry {
                    let annotated_ty = type_registry::resolve_type_expr(ty_expr, &std::collections::HashMap::new(), reg)
                        .map_err(|e| spanned(e, *span))?;
                    unify(&val_typed.ty, &annotated_ty, subst)
                        .map_err(|e| spanned(e, *span))?;
                }
            }

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
                let typed_pattern = check_pattern(&arm.pattern, &match_ty, env, subst, gen, registry, *span)?;
                let body_typed = infer_expr_inner(&arm.body, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                unify(&result_ty, &body_typed.ty, subst).map_err(|e| spanned(e, *span))?;
                env.pop_scope();
                typed_arms.push(TypedMatchArm {
                    pattern: typed_pattern,
                    body: body_typed,
                });
            }
            let match_ty = subst.apply(&match_ty);
            crate::exhaustiveness::check_exhaustiveness(
                &match_ty,
                &typed_arms,
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

        Expr::LetPattern { pattern, ty: ty_ann, value, body, span } => {
            let val_typed = infer_expr_inner(value, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;

            // If there's a type annotation, resolve it and unify with the inferred type
            if let Some(ty_expr) = ty_ann {
                if let Some(reg) = registry {
                    let annotated_ty = type_registry::resolve_type_expr(ty_expr, &std::collections::HashMap::new(), reg)
                        .map_err(|e| spanned(e, *span))?;
                    unify(&val_typed.ty, &annotated_ty, subst)
                        .map_err(|e| spanned(e, *span))?;
                }
            }
            match body {
                Some(body) => {
                    env.push_scope();
                    let typed_pattern = check_pattern(pattern, &subst.apply(&val_typed.ty), env, subst, gen, registry, *span)?;
                    let body_typed = infer_expr_inner(body, env, subst, gen, registry, recur_params, let_own_spans, lambda_own_captures)?;
                    env.pop_scope();
                    let ty = body_typed.ty.clone();
                    Ok(TypedExpr {
                        kind: TypedExprKind::LetPattern {
                            pattern: typed_pattern,
                            value: Box::new(val_typed),
                            body: Some(Box::new(body_typed)),
                        },
                        ty,
                        span: *span,
                    })
                }
                None => {
                    let typed_pattern = check_pattern(pattern, &subst.apply(&val_typed.ty), env, subst, gen, registry, *span)?;
                    Ok(TypedExpr {
                        kind: TypedExprKind::LetPattern {
                            pattern: typed_pattern,
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

        Expr::List { elements, span } => {
            // Infer as Vec[a] — [e1, e2, e3] produces Vec[elem_type]
            let elem_var = Type::Var(gen.fresh());
            let mut typed_elems = Vec::new();
            for elem in elements {
                let typed = infer_expr_inner(elem, env, subst, gen, registry, recur_params,
                                             let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                unify(&subst.apply(&typed.ty), &subst.apply(&elem_var), subst)
                    .map_err(|e| spanned(e, *span))?;
                typed_elems.push(typed);
            }
            let resolved_elem = subst.apply(&elem_var);
            Ok(TypedExpr {
                kind: TypedExprKind::VecLit(typed_elems),
                ty: Type::Named("Vec".to_string(), vec![resolved_elem]),
                span: *span,
            })
        }
        Expr::QuestionMark { expr, span } => {
            let inner_typed = infer_expr_inner(expr, env, subst, gen, registry, recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let inner_ty = subst.apply(&inner_typed.ty);
            // Strip Own wrapper for analysis
            let inner_ty_unwrapped = strip_own(&inner_ty);

            // Determine what kind of type the inner expr is
            let (is_option, unwrapped_ty) = match &inner_ty_unwrapped {
                Type::Named(name, args) if name == "Option" && args.len() == 1 => {
                    (true, args[0].clone())
                }
                Type::Named(name, args) if name == "Result" && args.len() == 2 => {
                    (false, args[1].clone()) // Result[e, a] → unwraps to a
                }
                Type::Var(_) => {
                    // Inner type is unknown — try to constrain it based on return type
                    let fn_ret = env.fn_return_type.as_ref().map(|t| subst.apply(t));
                    match fn_ret.as_ref().map(|t| strip_own(t)) {
                        Some(Type::Named(name, _)) if name == "Option" => {
                            let a = Type::Var(gen.fresh());
                            let option_ty = Type::Named("Option".to_string(), vec![a.clone()]);
                            unify(&inner_ty_unwrapped, &option_ty, subst).map_err(|e| spanned(e, *span))?;
                            (true, a)
                        }
                        Some(Type::Named(name, _)) if name == "Result" => {
                            let e = Type::Var(gen.fresh());
                            let a = Type::Var(gen.fresh());
                            let result_ty = Type::Named("Result".to_string(), vec![e, a.clone()]);
                            unify(&inner_ty_unwrapped, &result_ty, subst).map_err(|e| spanned(e, *span))?;
                            (false, a)
                        }
                        _ => {
                            // Return type also unknown — default to Result
                            let e = Type::Var(gen.fresh());
                            let a = Type::Var(gen.fresh());
                            let result_ty = Type::Named("Result".to_string(), vec![e, a.clone()]);
                            unify(&inner_ty_unwrapped, &result_ty, subst).map_err(|e| spanned(e, *span))?;
                            (false, a)
                        }
                    }
                }
                other => {
                    return Err(spanned(
                        TypeError::QuestionMarkBadOperand { actual: other.clone() },
                        *span,
                    ));
                }
            };

            // Now check that the function's return type is compatible
            let fn_ret = env.fn_return_type.as_ref().map(|t| subst.apply(t));
            let fn_ret_unwrapped = fn_ret.map(|t| strip_own(&t));

            match &fn_ret_unwrapped {
                Some(Type::Named(name, args)) if name == "Option" => {
                    if !is_option {
                        return Err(spanned(
                            TypeError::QuestionMarkMismatch {
                                expr_kind: "Result".to_string(),
                                return_kind: "Option".to_string(),
                            },
                            *span,
                        ));
                    }
                    // Option ? in Option fn — OK. Unify inner type params if needed.
                    let _ = args; // already compatible
                }
                Some(Type::Named(name, args)) if name == "Result" => {
                    if is_option {
                        return Err(spanned(
                            TypeError::QuestionMarkMismatch {
                                expr_kind: "Option".to_string(),
                                return_kind: "Result".to_string(),
                            },
                            *span,
                        ));
                    }
                    // Result ? in Result fn — unify error types
                    if args.len() == 2 {
                        // inner expr is Result[e1, a], fn returns Result[e2, b] → unify e1 = e2
                        let inner_resolved = subst.apply(&inner_ty_unwrapped);
                        if let Type::Named(_, inner_args) = &inner_resolved {
                            if inner_args.len() == 2 {
                                unify(&inner_args[0], &args[0], subst)
                                    .map_err(|e| spanned(e, *span))?;
                            }
                        }
                    }
                }
                Some(Type::Var(_)) => {
                    // Return type is still a type var — constrain it
                    if is_option {
                        let b = Type::Var(gen.fresh());
                        let option_ret = Type::Named("Option".to_string(), vec![b]);
                        if let Some(ref ret) = env.fn_return_type {
                            unify(&subst.apply(ret), &option_ret, subst)
                                .map_err(|e| spanned(e, *span))?;
                        }
                    } else {
                        // Result — unify return type as Result[e, b] with same error type
                        let inner_resolved = subst.apply(&inner_ty_unwrapped);
                        let err_ty = if let Type::Named(_, ref iargs) = inner_resolved {
                            if iargs.len() == 2 { iargs[0].clone() } else { Type::Var(gen.fresh()) }
                        } else { Type::Var(gen.fresh()) };
                        let b = Type::Var(gen.fresh());
                        let result_ret = Type::Named("Result".to_string(), vec![err_ty, b]);
                        if let Some(ref ret) = env.fn_return_type {
                            unify(&subst.apply(ret), &result_ret, subst)
                                .map_err(|e| spanned(e, *span))?;
                        }
                    }
                }
                Some(other) => {
                    return Err(spanned(
                        TypeError::QuestionMarkBadReturn { actual: other.clone() },
                        *span,
                    ));
                }
                None => {
                    return Err(spanned(
                        TypeError::QuestionMarkBadReturn { actual: Type::Unit },
                        *span,
                    ));
                }
            }

            let result_ty = subst.apply(&unwrapped_ty);
            Ok(TypedExpr {
                kind: TypedExprKind::QuestionMark {
                    expr: Box::new(inner_typed),
                    is_option,
                },
                ty: result_ty,
                span: *span,
            })
        },
    }
}

/// Check a pattern against an expected type, binding variables in the environment.
/// Returns a TypedPattern carrying resolved type information.
fn check_pattern(
    pattern: &Pattern,
    expected: &Type,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    span: krypton_parser::ast::Span,
) -> Result<TypedPattern, SpannedTypeError> {
    match pattern {
        Pattern::Wildcard { span: pat_span } => Ok(TypedPattern::Wildcard {
            ty: expected.clone(),
            span: *pat_span,
        }),

        Pattern::Var { name, span: pat_span } => {
            env.bind(name.clone(), TypeScheme::mono(expected.clone()));
            Ok(TypedPattern::Var {
                name: name.clone(),
                ty: expected.clone(),
                span: *pat_span,
            })
        }

        Pattern::Lit { value, span: pat_span } => {
            let lit_ty = match value {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::Bool(_) => Type::Bool,
                Lit::String(_) => Type::String,
                Lit::Unit => Type::Unit,
            };
            unify(expected, &lit_ty, subst).map_err(|e| spanned(e, span))?;
            Ok(TypedPattern::Lit {
                value: value.clone(),
                ty: lit_ty,
                span: *pat_span,
            })
        }

        Pattern::Constructor { name, args, span: pat_span } => {
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
                            let mut typed_args = Vec::new();
                            for (arg_pat, param_ty) in args.iter().zip(param_types.iter()) {
                                let resolved_param = subst.apply(param_ty);
                                typed_args.push(check_pattern(arg_pat, &resolved_param, env, subst, gen, registry, span)?);
                            }
                            Ok(TypedPattern::Constructor {
                                name: name.clone(),
                                args: typed_args,
                                ty: expected.clone(),
                                span: *pat_span,
                            })
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
                            Ok(TypedPattern::Constructor {
                                name: name.clone(),
                                args: vec![],
                                ty: expected.clone(),
                                span: *pat_span,
                            })
                        }
                    }
                }
                None => Err(spanned(
                    TypeError::UnknownVariable { name: name.clone() },
                    span,
                )),
            }
        }

        Pattern::Tuple { elements, span: pat_span } => {
            let fresh_vars: Vec<Type> = elements.iter().map(|_| Type::Var(gen.fresh())).collect();
            unify(expected, &Type::Tuple(fresh_vars.clone()), subst).map_err(|e| spanned(e, span))?;
            let mut typed_elems = Vec::new();
            for (elem_pat, fresh_var) in elements.iter().zip(fresh_vars.iter()) {
                let resolved = subst.apply(fresh_var);
                typed_elems.push(check_pattern(elem_pat, &resolved, env, subst, gen, registry, span)?);
            }
            Ok(TypedPattern::Tuple {
                elements: typed_elems,
                ty: expected.clone(),
                span: *pat_span,
            })
        }

        Pattern::StructPat { name, fields, rest, span: pat_span } => {
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
                    let mut typed_fields = Vec::new();
                    for (field_name, field_pat) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, field_ty)) => {
                                let instantiated = instantiate_field_type(field_ty, info, &fresh_args);
                                let resolved = subst.apply(&instantiated);
                                let typed_field_pat = check_pattern(field_pat, &resolved, env, subst, gen, registry, span)?;
                                typed_fields.push((field_name.clone(), typed_field_pat));
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
                    Ok(TypedPattern::StructPat {
                        name: name.clone(),
                        fields: typed_fields,
                        rest: *rest,
                        ty: expected.clone(),
                        span: *pat_span,
                    })
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
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
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
                work.push(base);
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
            TypedExprKind::App { func, args } => {
                work.push(func);
                for a in args { work.push(a); }
            }
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. } | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(b) = body { work.push(b); }
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs { work.push(e); }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms { work.push(&arm.body); }
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::Recur(args) | TypedExprKind::Tuple(args) | TypedExprKind::VecLit(args) => {
                for a in args { work.push(a); }
            }
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
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
        Type::App(ctor, args) => {
            let new_ctor = substitute_type_var(ctor, var_id, replacement);
            let new_args: Vec<Type> = args.iter().map(|a| substitute_type_var(a, var_id, replacement)).collect();
            crate::types::normalize_app(new_ctor, new_args)
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
    param_type_var_map: &HashMap<TypeVarId, usize>,
    constraints: &mut Vec<(String, usize)>,
) {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args } => {
                if let TypedExprKind::Var(name) = &func.kind {
                    if let Some(trait_name) = trait_method_map.get(name) {
                        if let Some(first_arg) = args.first() {
                            let arg_ty = subst.apply(&first_arg.ty);
                            let concrete_ty = strip_own(&arg_ty);
                            if let Type::Var(v) = concrete_ty {
                                if let Some(param_idx) = param_type_var_map.get(&v).copied() {
                                    constraints.push((trait_name.clone(), param_idx));
                                }
                            }
                        }
                    }
                }
                work.push(func);
                for a in args { work.push(a); }
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. } | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(body) = body { work.push(body); }
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs { work.push(e); }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms { work.push(&arm.body); }
            }
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::StructUpdate { base, fields, .. } => {
                work.push(base);
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::Tuple(elems) | TypedExprKind::Recur(elems) | TypedExprKind::VecLit(elems) => {
                for e in elems { work.push(e); }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }
}

/// Walk a typed AST looking for calls to trait methods. For each call,
/// resolve the argument type and verify that a matching instance exists.
/// Also checks calls to imported constrained functions (via `fn_constraints`).
fn check_trait_instances(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, String>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_constraints: &HashMap<String, Vec<(String, usize)>>,
) -> Result<(), SpannedTypeError> {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args } => {
                if let TypedExprKind::Var(name) = &func.kind {
                    if let Some(trait_name) = trait_method_map.get(name) {
                        if let Some(first_arg) = args.first() {
                            let arg_ty = subst.apply(&first_arg.ty);
                            let concrete_ty = strip_own(&arg_ty);
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
                    // Check calls to constrained functions (e.g., imported `println` requires Show)
                    if let Some(constraints) = fn_constraints.get(name.as_str()) {
                        for (trait_name, param_idx) in constraints {
                            if let Some(arg) = args.get(*param_idx) {
                                let arg_ty = subst.apply(&arg.ty);
                                let concrete_ty = strip_own(&arg_ty);
                                if !matches!(concrete_ty, Type::Var(_)) {
                                    if trait_registry.find_instance(trait_name, &concrete_ty).is_none() {
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
                    }
                }
                work.push(func);
                for a in args { work.push(a); }
            }
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let trait_name = match op {
                    BinOp::Add => Some("Add"),
                    BinOp::Sub => Some("Sub"),
                    BinOp::Mul => Some("Mul"),
                    BinOp::Div => Some("Div"),
                    BinOp::Eq | BinOp::Neq => Some("Eq"),
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => Some("Ord"),
                    BinOp::And | BinOp::Or => None,
                };
                if let Some(trait_name) = trait_name {
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
                }
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { op, operand } => {
                let trait_name = match op {
                    UnaryOp::Neg => Some("Neg"),
                    UnaryOp::Not => None,
                };
                if let Some(trait_name) = trait_name {
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
                }
                work.push(operand);
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. } | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(body) = body { work.push(body); }
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs { work.push(e); }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms { work.push(&arm.body); }
            }
            TypedExprKind::FieldAccess { expr: inner, .. } => work.push(inner),
            TypedExprKind::Tuple(elems) | TypedExprKind::Recur(elems) | TypedExprKind::VecLit(elems) => {
                for e in elems { work.push(e); }
            }
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::StructUpdate { base, fields, .. } => {
                work.push(base);
                for (_, e) in fields { work.push(e); }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }
    Ok(())
}

/// Process extern methods from an `extern "class" { ... }` block, binding their
/// types into the environment and returning `ExternFnInfo` entries for codegen.
fn process_extern_methods(
    class_name: &str,
    methods: &[ExternMethod],
    env: &mut TypeEnv,
    gen: &mut TypeVarGen,
    registry: &TypeRegistry,
    span: Span,
    name_filter: Option<&HashSet<&str>>,
    aliases: &HashMap<String, String>,
) -> Result<Vec<ExternFnInfo>, SpannedTypeError> {
    let empty_map = HashMap::new();
    let mut extern_fns = Vec::new();
    for method in methods {
        let bind_name = aliases.get(&method.name).unwrap_or(&method.name);
        if let Some(filter) = name_filter {
            if !filter.contains(method.name.as_str()) && !filter.contains(bind_name.as_str()) {
                continue;
            }
        }

        let mut scheme_vars = Vec::new();
        let mut param_types = Vec::new();
        for ty_expr in &method.param_types {
            let resolved = type_registry::resolve_type_expr(ty_expr, &empty_map, registry)
                .map_err(|e| spanned(e, span))?;
            if matches!(&resolved, Type::Named(n, args) if n == "Object" && args.is_empty()) {
                let fresh = gen.fresh();
                scheme_vars.push(fresh);
                param_types.push(Type::Var(fresh));
            } else {
                param_types.push(resolved);
            }
        }

        let return_type = type_registry::resolve_type_expr(&method.return_type, &empty_map, registry)
            .map_err(|e| spanned(e, span))?;
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
        env.bind(bind_name.clone(), scheme);

        // Store concrete types for codegen (Object stays as-is)
        let mut concrete_params = Vec::new();
        for ty_expr in &method.param_types {
            concrete_params.push(type_registry::resolve_type_expr(ty_expr, &empty_map, registry)
                .map_err(|e| spanned(e, span))?);
        }
        extern_fns.push(ExternFnInfo {
            name: bind_name.clone(),
            java_class: class_name.to_string(),
            param_types: concrete_params,
            return_type,
        });
    }
    Ok(extern_fns)
}

/// Infer types for all top-level definitions in a module.
///
/// Returns a `Vec<TypedModule>` containing the main module (first, `module_path: None`)
/// followed by any imported modules discovered during inference.
///
/// Uses SCC (strongly connected component) analysis to process definitions
/// in dependency order. Functions within the same SCC are inferred together
/// as a mutually recursive group, then generalized before later SCCs see them.
#[tracing::instrument(skip(module, resolver), fields(decls = module.decls.len()))]
pub fn infer_module(module: &Module, resolver: &dyn krypton_modules::module_resolver::ModuleResolver) -> Result<Vec<TypedModule>, SpannedTypeError> {
    use krypton_modules::module_graph;

    // Build the module graph (resolves, parses, toposorts all imports + prelude)
    let graph = module_graph::build_module_graph(module, resolver)
        .map_err(map_graph_error)?;

    // Build parsed module lookup for import binding (borrows from graph)
    let mut parsed_modules: HashMap<String, &Module> = HashMap::new();
    let mut cache: HashMap<String, TypedModule> = HashMap::new();

    // Type-check each dependency in topological order
    for resolved in &graph.modules {
        parsed_modules.insert(resolved.path.clone(), &resolved.module);
        if !cache.contains_key(&resolved.path) {
            let typed = infer_module_inner(
                &resolved.module, &mut cache, &parsed_modules,
                Some(resolved.path.clone()),
            )?;
            cache.insert(resolved.path.clone(), typed);
        }
    }

    // Type-check the root module
    let main = infer_module_inner(module, &mut cache, &parsed_modules, None)?;

    let mut result = vec![main];
    // Collect cached imported modules (stable ordering by path)
    let mut paths: Vec<String> = cache.keys().cloned().collect();
    paths.sort();
    for path in paths {
        result.push(cache.remove(&path).unwrap());
    }
    Ok(result)
}

/// Convert a `ModuleGraphError` into a `SpannedTypeError`.
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
        ModuleGraphError::ParseError { path, errors } => {
            spanned(TypeError::ModuleParseError { path, errors }, (0, 0))
        }
    }
}

/// Return the main `TypedModule` from `infer_module` result (for backward compatibility).
pub fn infer_module_single(module: &Module, resolver: &dyn krypton_modules::module_resolver::ModuleResolver) -> Result<TypedModule, SpannedTypeError> {
    let mut modules = infer_module(module, resolver)?;
    Ok(modules.remove(0))
}

/// Internal per-module inference with pre-resolved module cache.
///
/// The module graph has already been resolved and toposorted by `infer_module`.
/// Import declarations look up parsed ASTs from `parsed_modules` and typed
/// results from `cache` — no recursive resolution or cycle detection needed.
pub(crate) fn infer_module_inner(
    module: &Module,
    cache: &mut HashMap<String, TypedModule>,
    parsed_modules: &HashMap<String, &Module>,
    module_path: Option<String>,
) -> Result<TypedModule, SpannedTypeError> {
    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();
    let mut registry = TypeRegistry::new();
    registry.register_builtins();
    let mut let_own_spans: HashSet<Span> = HashSet::new();
    let mut lambda_own_captures: HashMap<Span, String> = HashMap::new();

    // Seed intrinsic function types (user defs can shadow these)
    crate::intrinsics::register_intrinsics(&mut env, &mut gen);

    // These must be declared before auto_import_prelude since it populates them
    let mut imported_extern_fns: Vec<ExternFnInfo> = Vec::new();
    let mut fn_provenance_map: HashMap<String, (String, String)> = HashMap::new();
    let mut type_provenance: HashMap<String, String> = HashMap::new();
    // Mark builtins as non-local so the orphan check rejects `impl Trait[Int]` etc.
    for name in &["Int", "Float", "Bool", "String", "Unit"] {
        type_provenance.insert(name.to_string(), "core".to_string());
    }

    // Auto-import prelude types (Option, Result, List, Ordering) from stdlib prelude.kr
    // Prelude is already type-checked and in cache (graph builder ensures this).
    // Skip when we ARE the prelude or one of its transitive deps.
    let is_prelude_tree = module_path.as_ref().is_some_and(|p| {
        p == "prelude" || krypton_modules::stdlib_loader::StdlibLoader::PRELUDE_MODULES.contains(&p.as_str())
    });
    crate::prelude::auto_import_prelude(
        &mut env, &mut registry, &mut gen,
        parsed_modules, cache, is_prelude_tree,
        &mut fn_provenance_map, &mut type_provenance,
        &mut imported_extern_fns,
    )?;

    // Process import declarations with per-module inference, caching, and circular detection
    let mut imported_fn_types: Vec<(String, TypeScheme)> = Vec::new();
    // Track imported type info for pub use re-exports: type_name → (source_module_path, visibility)
    let mut imported_type_info: HashMap<String, (String, Visibility)> = HashMap::new();
    // Track fn_constraints from imported modules for cross-module constraint checking
    let mut imported_fn_constraints: HashMap<String, Vec<(String, usize)>> = HashMap::new();
    // Track trait definitions from imported modules for cross-module trait usage
    let mut imported_trait_defs: Vec<ExportedTraitDef> = Vec::new();
    let mut imported_trait_names: HashSet<String> = HashSet::new();
    // Track re-exports from `pub import` declarations
    let mut reexported_fn_types: Vec<(String, TypeScheme)> = Vec::new();
    let mut reexported_type_names: Vec<String> = Vec::new();
    let mut reexported_type_visibility: HashMap<String, Visibility> = HashMap::new();
    for decl in &module.decls {
        if let Decl::Import { is_pub, path, names, span } = decl {
            // Graph builder already validated: no cycles, no bare imports, no unknown modules.
            // Look up the parsed AST from the pre-resolved graph.
            let imported_module = parsed_modules.get(path)
                .expect("module graph should contain all imported modules");

            // Module should already be type-checked (topological order guarantees this)
            assert!(cache.contains_key(path), "module {path} should be in cache (topological order)");

            let requested: HashSet<&str> = names.iter().map(|n| n.name.as_str()).collect();
            let import_all = names.is_empty();

            // Build alias map from ImportName
            let aliases: HashMap<String, String> = names.iter()
                .filter_map(|n| n.alias.as_ref().map(|a| (n.name.clone(), a.clone())))
                .collect();

            // Build fn visibility map from parsed imported module
            let mut fn_vis: HashMap<&str, &Visibility> = imported_module.decls.iter()
                .filter_map(|d| {
                    if let Decl::DefFn(f) = d { Some((f.name.as_str(), &f.visibility)) } else { None }
                })
                .collect();

            // Also include extern method visibility
            for d in &imported_module.decls {
                if let Decl::ExternJava { methods, .. } = d {
                    for m in methods {
                        fn_vis.entry(m.name.as_str()).or_insert(&m.visibility);
                    }
                }
            }

            // Build set of constructor names belonging to non-PubOpen types.
            // These should not be bound from fn_types (they are handled by
            // the type declaration processing below with visibility control).
            let mut opaque_constructors: HashSet<String> = HashSet::new();
            for sdecl in &imported_module.decls {
                if let Decl::DefType(td) = sdecl {
                    if !matches!(td.visibility, Visibility::PubOpen) {
                        // Record type: constructor has same name as type
                        match &td.kind {
                            TypeDeclKind::Record { .. } => {
                                opaque_constructors.insert(td.name.clone());
                            }
                            TypeDeclKind::Sum { variants } => {
                                for v in variants {
                                    opaque_constructors.insert(v.name.clone());
                                }
                            }
                        }
                    }
                }
            }

            // Check visibility of explicitly requested extern methods
            for name in &requested {
                if let Some(vis) = fn_vis.get(name) {
                    if matches!(vis, Visibility::Private) && requested.contains(name) {
                        return Err(spanned(TypeError::PrivateName {
                            name: name.to_string(), module_path: path.clone(),
                        }, *span));
                    }
                }
            }

            // Extract type signatures from cached module and bind with provenance.
            // Enforce visibility: private names cannot be imported explicitly.
            let cached = cache.get(path).unwrap();
            for (name, scheme) in &cached.fn_types {
                // Skip constructors of non-PubOpen types — these are not
                // accessible from the importing module.
                if opaque_constructors.contains(name) {
                    continue;
                }
                let vis = fn_vis.get(name.as_str()).copied().unwrap_or(&Visibility::Pub);
                if requested.contains(name.as_str()) {
                    // Explicitly requested — check visibility
                    if matches!(vis, Visibility::Private) {
                        return Err(spanned(TypeError::PrivateName {
                            name: name.clone(), module_path: path.clone(),
                        }, *span));
                    }
                    let effective_name = aliases.get(name)
                        .cloned()
                        .unwrap_or_else(|| name.clone());
                    env.bind_with_provenance(effective_name.clone(), scheme.clone(), path.clone());
                    imported_fn_types.push((effective_name.clone(), scheme.clone()));
                    fn_provenance_map.insert(effective_name, (path.clone(), name.clone()));
                } else if import_all {
                    // Wildcard import — skip private names silently
                    if matches!(vis, Visibility::Private) {
                        // Still bind for internal dependency resolution
                        env.bind(name.clone(), scheme.clone());
                        continue;
                    }
                    let effective_name = aliases.get(name)
                        .cloned()
                        .unwrap_or_else(|| name.clone());
                    env.bind_with_provenance(effective_name.clone(), scheme.clone(), path.clone());
                    imported_fn_types.push((effective_name.clone(), scheme.clone()));
                    fn_provenance_map.insert(effective_name, (path.clone(), name.clone()));
                }
            }

            // Process re-exported functions from the cached module
            for (name, scheme) in &cached.reexported_fn_types {
                if requested.contains(name.as_str()) {
                    let effective_name = aliases.get(name)
                        .cloned()
                        .unwrap_or_else(|| name.clone());
                    env.bind_with_provenance(effective_name.clone(), scheme.clone(), path.clone());
                    imported_fn_types.push((effective_name.clone(), scheme.clone()));
                    // Use the original provenance if available, otherwise point to the re-exporting module
                    let original_prov = cached.fn_provenance.get(name)
                        .cloned()
                        .unwrap_or_else(|| (path.clone(), name.clone()));
                    fn_provenance_map.insert(effective_name, original_prov);
                }
            }

            // Process re-exported types from the cached module
            for reex_type_name in &cached.reexported_type_names {
                if requested.contains(reex_type_name.as_str()) {
                    let original_vis = cached.reexported_type_visibility.get(reex_type_name)
                        .cloned()
                        .unwrap_or(Visibility::Pub);
                    // Look up the type info from the cached module's type provenance
                    // to find the original source module, then register in our registry
                    if registry.lookup_type(reex_type_name).is_none() {
                        // The type was already registered in the re-exporting module's inference.
                        // We need to re-parse the original source to get the type declaration.
                        let original_path = cached.type_provenance.get(reex_type_name);
                        if let Some(orig_path) = original_path {
                            if let Some(orig_module) = parsed_modules.get(orig_path.as_str()) {
                                for odecl in &orig_module.decls {
                                    if let Decl::DefType(td) = odecl {
                                        if td.name == *reex_type_name {
                                            registry.register_name(&td.name);
                                            let constructors = type_registry::process_type_decl(td, &mut registry, &mut gen)
                                                .map_err(|e| spanned(e, *span))?;
                                            if matches!(original_vis, Visibility::PubOpen) {
                                                for (cname, scheme) in &constructors {
                                                    env.bind(cname.clone(), scheme.clone());
                                                    // Also add constructors to imported_fn_types so they're visible
                                                    imported_fn_types.push((cname.clone(), scheme.clone()));
                                                    fn_provenance_map.insert(cname.clone(), (orig_path.clone(), cname.clone()));
                                                }
                                            }
                                            imported_type_info.insert(td.name.clone(), (orig_path.clone(), original_vis.clone()));
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Process type declarations from imported module source with visibility enforcement
            for sdecl in &imported_module.decls {
                if let Decl::DefType(td) = sdecl {
                    if requested.contains(td.name.as_str()) {
                        // Explicitly requested — check visibility
                        if matches!(td.visibility, Visibility::Private) {
                            return Err(spanned(TypeError::PrivateName {
                                name: td.name.clone(), module_path: path.clone(),
                            }, *span));
                        }
                        if registry.lookup_type(&td.name).is_none() {
                            registry.register_name(&td.name);
                            let constructors = type_registry::process_type_decl(td, &mut registry, &mut gen)
                                .map_err(|e| spanned(e, *span))?;
                            // Only bind constructors if pub open
                            if matches!(td.visibility, Visibility::PubOpen) {
                                for (cname, scheme) in constructors {
                                    env.bind(cname, scheme);
                                }
                            }
                        }
                        // Track imported type info for pub use re-exports
                        imported_type_info.insert(td.name.clone(), (path.clone(), td.visibility.clone()));
                    } else if import_all {
                        // Wildcard import — skip private types silently
                        if matches!(td.visibility, Visibility::Private) {
                            continue;
                        }
                        if registry.lookup_type(&td.name).is_none() {
                            registry.register_name(&td.name);
                            let constructors = type_registry::process_type_decl(td, &mut registry, &mut gen)
                                .map_err(|e| spanned(e, *span))?;
                            if matches!(td.visibility, Visibility::PubOpen) {
                                for (cname, scheme) in constructors {
                                    env.bind(cname, scheme);
                                }
                            }
                        }
                    } else if registry.lookup_type(&td.name).is_none() {
                        // Non-requested, non-wildcard: register for internal deps
                        registry.register_name(&td.name);
                        let constructors = type_registry::process_type_decl(td, &mut registry, &mut gen)
                            .map_err(|e| spanned(e, *span))?;
                        for (cname, scheme) in constructors {
                            env.bind(cname, scheme);
                        }
                    }
                }
            }

            // Process extern declarations from imported module (no name filter —
            // extern methods are internal dependencies for DefFn functions)
            for sdecl in &imported_module.decls {
                if let Decl::ExternJava { class_name, methods, span: ext_span } = sdecl {
                    let mut fns = process_extern_methods(
                        class_name, methods, &mut env, &mut gen, &registry,
                        *ext_span, None, &aliases,
                    )?;
                    imported_extern_fns.append(&mut fns);
                }
            }

            // Copy imported extern fns for codegen
            for ext in &cached.extern_fns {
                imported_extern_fns.push(ext.clone());
            }
            for ext in &cached.imported_extern_fns {
                imported_extern_fns.push(ext.clone());
            }

            // Collect fn_constraints from imported module for cross-module constraint checking.
            // Map using the effective name (after aliasing) so callers see constraints.
            for (name, constraints) in &cached.fn_constraints {
                let effective_name = aliases.get(name)
                    .cloned()
                    .unwrap_or_else(|| name.clone());
                if requested.contains(name.as_str()) || import_all {
                    imported_fn_constraints.insert(effective_name, constraints.clone());
                }
            }
            // Also propagate constraints from the imported module's own imports
            for (name, constraints) in &cached.imported_fn_constraints {
                let effective_name = aliases.get(name)
                    .cloned()
                    .unwrap_or_else(|| name.clone());
                if requested.contains(name.as_str()) || import_all {
                    imported_fn_constraints.insert(effective_name, constraints.clone());
                }
            }

            // Propagate trait definitions from the imported module
            for trait_def in &cached.exported_trait_defs {
                let explicitly_requested = requested.contains(trait_def.name.as_str())
                    || trait_def.methods.iter().any(|m| requested.contains(m.name.as_str()));
                if (explicitly_requested || import_all)
                    && !imported_trait_names.contains(&trait_def.name)
                {
                    // Enforce visibility: private traits cannot be imported
                    if matches!(trait_def.visibility, Visibility::Private) {
                        if explicitly_requested {
                            return Err(spanned(TypeError::PrivateName {
                                name: trait_def.name.clone(), module_path: path.clone(),
                            }, *span));
                        }
                        // Wildcard import — skip private traits silently
                        continue;
                    }
                    imported_trait_defs.push(trait_def.clone());
                    imported_trait_names.insert(trait_def.name.clone());
                    type_provenance.insert(trait_def.name.clone(), path.clone());
                }
            }

            // Process pub import re-exports: mark all imported names as re-exported
            if *is_pub {
                for name in names {
                    let name = &name.name;
                    let found_fn = imported_fn_types.iter().any(|(n, _)| n == name);
                    let found_type = imported_type_info.contains_key(name);

                    if !found_fn && !found_type {
                        return Err(spanned(TypeError::PrivateReexport {
                            name: name.clone(),
                        }, *span));
                    }
                    if found_fn {
                        if let Some((_, scheme)) = imported_fn_types.iter().find(|(n, _)| n == name) {
                            reexported_fn_types.push((name.clone(), scheme.clone()));
                        }
                    }
                    if found_type {
                        reexported_type_names.push(name.clone());
                        let original_vis = imported_type_info.get(name)
                            .map(|(_, vis)| vis.clone())
                            .unwrap_or(Visibility::Pub);
                        reexported_type_visibility.insert(name.clone(), original_vis);
                    }
                }
            }
        }
    }

    // Process ExternJava declarations
    let mut extern_fns: Vec<ExternFnInfo> = Vec::new();
    for decl in &module.decls {
        if let Decl::ExternJava { class_name, methods, span } = decl {
            let no_aliases = HashMap::new();
            let mut fns = process_extern_methods(
                class_name, methods, &mut env, &mut gen, &registry,
                *span, None, &no_aliases,
            )?;
            extern_fns.append(&mut fns);
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
            // If shadowing a prelude type, unbind old constructors and clear provenance
            if let Some(existing) = registry.lookup_type(&type_decl.name) {
                if existing.is_prelude {
                    if let crate::type_registry::TypeKind::Sum { variants } = &existing.kind {
                        for v in variants {
                            env.unbind(&v.name);
                            fn_provenance_map.remove(&v.name);
                        }
                    }
                    type_provenance.remove(&type_decl.name);
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
    let builtin_trait_names: HashSet<String> = trait_registry.traits().keys().cloned().collect();

    // Structural instance lookup: for each type/trait in scope, look up instances
    // in the defining module. The orphan rule guarantees instances live in the
    // module defining the type or the trait.
    {
        let mut source_modules: HashSet<&str> = HashSet::new();
        for (_, source_path) in &type_provenance {
            source_modules.insert(source_path.as_str());
        }
        // Also include sources from imported_type_info (not yet in type_provenance)
        for (_, (source_path, _)) in &imported_type_info {
            source_modules.insert(source_path.as_str());
        }

        let mut seen_instances: HashSet<(String, String)> = HashSet::new();
        for module_path in &source_modules {
            if let Some(cached_module) = cache.get(*module_path) {
                for inst in &cached_module.instance_defs {
                    let key = (inst.trait_name.clone(), inst.target_type_name.clone());
                    if seen_instances.insert(key) {
                        let instance = InstanceInfo {
                            trait_name: inst.trait_name.clone(),
                            target_type: inst.target_type.clone(),
                            target_type_name: inst.target_type_name.clone(),
                            methods: inst.qualified_method_names.iter().map(|(m, _)| m.clone()).collect(),
                            span: (0, 0),
                            is_builtin: false,
                        };
                        // A-T14: silently ignores duplicate imported instances; should be an error
                        let _ = trait_registry.register_instance(instance);
                    }
                }
            }
        }
    }

    // Register trait definitions imported from other modules
    for trait_def in &imported_trait_defs {
        // Skip if already registered (builtin overlap)
        if trait_registry.lookup_trait(&trait_def.name).is_some() {
            continue;
        }
        let new_tv_id = gen.fresh();
        let old_tv_id = trait_def.type_var_id;

        let mut trait_methods = Vec::new();
        for method in &trait_def.methods {
            let param_types: Vec<Type> = method.param_types.iter()
                .map(|t| remap_type_var(t, old_tv_id, new_tv_id))
                .collect();
            let return_type = remap_type_var(&method.return_type, old_tv_id, new_tv_id);

            // Bind the method as a polymorphic function: forall a. fn(params) -> ret
            let fn_ty = Type::Fn(param_types.clone(), Box::new(return_type.clone()));
            let scheme = TypeScheme { vars: vec![new_tv_id], ty: fn_ty };
            env.bind(method.name.clone(), scheme);

            trait_methods.push(TraitMethod {
                name: method.name.clone(),
                param_types,
                return_type,
            });
        }

        trait_registry.register_trait(TraitInfo {
            name: trait_def.name.clone(),
            type_var: trait_def.type_var.clone(),
            type_var_id: new_tv_id,
            type_var_arity: trait_def.type_var_arity,
            superclasses: trait_def.superclasses.clone(),
            methods: trait_methods,
            span: (0, 0),
        }).map_err(|e| spanned(e, (0, 0)))?;
    }

    // Second pass: process DefTrait declarations
    let mut exported_trait_defs: Vec<ExportedTraitDef> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefTrait { visibility, name, type_param, superclasses, methods, span } = decl {
            // Skip if this trait is already registered as a built-in
            if trait_registry.lookup_trait(name).is_some() {
                continue;
            }
            let tv_id = gen.fresh();
            let type_var_arity = type_param.arity;
            let mut type_param_map = HashMap::new();
            type_param_map.insert(type_param.name.clone(), tv_id);

            // For HK trait methods, use explicit type_params from the method declaration
            let mut trait_methods = Vec::new();
            let mut exported_methods = Vec::new();
            for method in methods {
                let mut method_type_param_map = type_param_map.clone();
                let mut method_tv_ids = Vec::new();
                for tv_name in &method.type_params {
                    if !method_type_param_map.contains_key(tv_name) {
                        let mv_id = gen.fresh();
                        method_type_param_map.insert(tv_name.clone(), mv_id);
                        method_tv_ids.push(mv_id);
                    }
                }

                let mut param_types = Vec::new();
                for p in &method.params {
                    if let Some(ref ty_expr) = p.ty {
                        param_types.push(type_registry::resolve_type_expr(ty_expr, &method_type_param_map, &registry)
                            .map_err(|e| spanned(e, method.span))?);
                    } else {
                        param_types.push(Type::Var(gen.fresh()));
                    }
                }
                let return_type = if let Some(ref ret_expr) = method.return_type {
                    type_registry::resolve_type_expr(ret_expr, &method_type_param_map, &registry)
                        .map_err(|e| spanned(e, method.span))?
                } else {
                    Type::Var(gen.fresh())
                };

                // Bind the method as a polymorphic function: forall tv_id, method_tvs. fn(params) -> ret
                let fn_ty = Type::Fn(param_types.clone(), Box::new(return_type.clone()));
                let mut all_vars = vec![tv_id];
                all_vars.extend_from_slice(&method_tv_ids);
                let scheme = TypeScheme { vars: all_vars, ty: fn_ty };
                env.bind(method.name.clone(), scheme);

                exported_methods.push(ExportedTraitMethod {
                    name: method.name.clone(),
                    param_types: param_types.clone(),
                    return_type: return_type.clone(),
                });

                trait_methods.push(TraitMethod {
                    name: method.name.clone(),
                    param_types,
                    return_type,
                });
            }

            trait_registry.register_trait(TraitInfo {
                name: name.clone(),
                type_var: type_param.name.clone(),
                type_var_id: tv_id,
                type_var_arity,
                superclasses: superclasses.clone(),
                methods: trait_methods,
                span: *span,
            }).map_err(|e| spanned(e, *span))?;

            exported_trait_defs.push(ExportedTraitDef {
                visibility: visibility.clone(),
                name: name.clone(),
                type_var: type_param.name.clone(),
                type_var_id: tv_id,
                type_var_arity,
                superclasses: superclasses.clone(),
                methods: exported_methods,
            });
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
                    visibility: Visibility::Pub,
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

    // Collect locally-defined trait names for orphan check
    let local_trait_names: HashSet<String> = module.decls.iter()
        .filter_map(|d| if let Decl::DefTrait { name, .. } = d { Some(name.clone()) } else { None })
        .collect();

    // Third pass: process DefImpl declarations
    for decl in &module.decls {
        if let Decl::DefImpl { trait_name, target_type, methods: _, span, .. } = decl {
            let empty_map = HashMap::new();
            let resolved_target = type_registry::resolve_type_expr(target_type, &empty_map, &registry)
                .map_err(|e| spanned(e, *span))?;

            // Orphan check: type must be known, and either the type or the trait must be locally defined
            let target_name = match &resolved_target {
                Type::Named(name, _) => {
                    if registry.lookup_type(name).is_none() {
                        return Err(spanned(TypeError::OrphanInstance {
                            trait_name: trait_name.clone(),
                            ty: name.clone(),
                        }, *span));
                    }
                    let trait_is_local = local_trait_names.contains(trait_name);
                    let type_is_local = !type_provenance.contains_key(name);
                    if !type_is_local && !trait_is_local {
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

            // Kind-arity check: verify the impl target has the right arity for the trait
            if let Some(trait_info) = trait_registry.lookup_trait(trait_name) {
                let expected_arity = trait_info.type_var_arity;
                if expected_arity > 0 {
                    let actual_arity = registry.expected_arity(&target_name).unwrap_or(0);
                    if actual_arity != expected_arity {
                        return Err(spanned(TypeError::KindMismatch {
                            type_name: target_name.clone(),
                            expected_arity,
                            actual_arity,
                        }, *span));
                    }
                }
            }

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

    // Check for top-level def names conflicting with ANY trait method names (including built-ins)
    {
        // Determine if the module uses traits (has DefTrait, DefImpl, or deriving)
        let has_trait_usage = module.decls.iter().any(|d| matches!(d,
            Decl::DefTrait { .. } | Decl::DefImpl { .. }
        )) || module.decls.iter().any(|d| {
            if let Decl::DefType(td) = d { !td.deriving.is_empty() } else { false }
        });

        // First pass: check user-defined traits (with secondary span)
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
                // Second pass: check built-in traits (no secondary span)
                // Only check when module uses traits (has instances, trait defs, or deriving)
                if !user_trait_methods.contains_key(&f.name) && has_trait_usage {
                    if let Some(trait_name) = trait_method_map.get(&f.name) {
                        return Err(SpannedTypeError {
                            error: TypeError::DefinitionConflictsWithTraitMethod {
                                def_name: f.name.clone(),
                                trait_name: trait_name.clone(),
                            },
                            span: f.span,
                            note: None,
                            secondary_span: None,
                        });
                    }
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
            // Set fn_return_type for ? operator support
            let prev_fn_return_type = env.fn_return_type.take();
            if let Some(ref ret_ty_expr) = decl.return_type {
                let resolved_ret = type_registry::resolve_type_expr(ret_ty_expr, &type_param_map, &registry)
                    .map_err(|e| spanned(e, decl.span))?;
                env.fn_return_type = Some(resolved_ret);
            } else {
                env.fn_return_type = Some(Type::Var(gen.fresh()));
            }

            let body_typed = infer_expr_inner(&decl.body, &mut env, &mut subst, &mut gen, Some(&registry), Some(&param_types), Some(&mut let_own_spans), Some(&mut lambda_own_captures))?;
            env.fn_return_type = prev_fn_return_type;
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
    // and check cross-module constraints (e.g., imported `println` requires Show)
    if !trait_method_map.is_empty() || !imported_fn_constraints.is_empty() {
        for body in fn_bodies.iter() {
            if let Some(body) = body {
                check_trait_instances(body, &trait_method_map, &trait_registry, &subst, &imported_fn_constraints)?;
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

                // Build type_param_map for impl method annotations
                // (needed for type vars in HKT method annotations like `Box[a]`)
                let mut impl_method_tpm = HashMap::new();
                for tv_name in &method.type_params {
                    if !impl_method_tpm.contains_key(tv_name) {
                        impl_method_tpm.insert(tv_name.clone(), gen.fresh());
                    }
                }

                // Validate user-provided type annotations against the trait signature
                for (i, p) in method.params.iter().enumerate() {
                    if let Some(ref ty_expr) = p.ty {
                        if i < concrete_param_types.len() {
                            let annotated_ty = type_registry::resolve_type_expr(ty_expr, &impl_method_tpm, &registry)
                                .map_err(|e| spanned(e, p.span))?;
                            unify(&annotated_ty, &concrete_param_types[i], &mut subst)
                                .map_err(|e| spanned(e, p.span))?;
                        }
                    }
                }
                if let Some(ref ret_ty_expr) = method.return_type {
                    let concrete_ret = substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);
                    let annotated_ret = type_registry::resolve_type_expr(ret_ty_expr, &impl_method_tpm, &registry)
                        .map_err(|e| spanned(e, method.span))?;
                    unify(&annotated_ret, &concrete_ret, &mut subst)
                        .map_err(|e| spanned(e, method.span))?;
                }

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
                // Set fn_return_type for ? operator support
                let prev_fn_return_type = env.fn_return_type.take();
                let concrete_ret_type = substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);
                env.fn_return_type = Some(concrete_ret_type);

                let body_typed = infer_expr_inner(&method.body, &mut env, &mut subst, &mut gen, Some(&registry), Some(&param_types_inferred), Some(&mut let_own_spans), Some(&mut lambda_own_captures))?;
                env.fn_return_type = prev_fn_return_type;
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
                    visibility: Visibility::Pub,
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

    // Collect results: imported stdlib functions first, then constructors, then user functions
    let mut results: Vec<(String, TypeScheme)> = imported_fn_types;
    results.extend(constructor_schemes);
    results.extend(
        fn_decls
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.clone(), result_schemes[i].clone().unwrap())),
    );
    results.extend(impl_fn_types);
    results.extend(derived_impl_fn_types);

    // Apply final substitution to all typed function bodies
    let mut functions: Vec<TypedFnDecl> = Vec::new();
    for (i, decl) in fn_decls.iter().enumerate() {
        let mut body = fn_bodies[i].take().unwrap();
        typed_ast::apply_subst(&mut body, &subst);
        functions.push(TypedFnDecl {
            name: decl.name.clone(),
            visibility: decl.visibility.clone(),
            params: decl.params.iter().map(|p| p.name.clone()).collect(),
            body,
        });
    }
    functions.extend(impl_functions);
    functions.extend(derived_impl_functions);

    // Detect constrained functions: functions that call trait methods on type variables
    let mut fn_constraints: HashMap<String, Vec<(String, usize)>> = HashMap::new();
    for func in &functions {
        // Build param_type_var_map: type var id → param index for this function
        let mut param_type_var_map: HashMap<TypeVarId, usize> = HashMap::new();
        if let Some((_, scheme)) = results.iter().find(|(n, _)| n == &func.name) {
            if let Type::Fn(param_types, _) = &scheme.ty {
                for (idx, pty) in param_types.iter().enumerate() {
                    // Collect all type vars in this param (including nested ones
                    // like `a` in `Option[a]`) so parameterized instances work
                    for v in free_vars(pty) {
                        param_type_var_map.entry(v).or_insert(idx);
                    }
                }
            }
        }
        let mut constraints = Vec::new();
        detect_trait_constraints(&func.body, &trait_method_map, &subst, &param_type_var_map, &mut constraints);
        if !constraints.is_empty() {
            constraints.sort();
            constraints.dedup();
            fn_constraints.insert(func.name.clone(), constraints);
        }
    }

    // Build trait_defs for codegen (include built-in traits that have user instances)
    let mut trait_defs = Vec::new();
    let mut seen_traits = std::collections::HashSet::new();
    // First add all traits from registry
    for (trait_name, info) in trait_registry.traits() {
        let is_imported = imported_trait_names.contains(trait_name);
        let method_info: Vec<(String, usize)> = info.methods.iter().map(|m| {
            (m.name.clone(), m.param_types.len())
        }).collect();
        trait_defs.push(TraitDefInfo {
            name: trait_name.clone(),
            methods: method_info,
            is_imported,
        });
        seen_traits.insert(trait_name.clone());
        // Only set "core" provenance for actual built-in traits (not imported or user-defined)
        if builtin_trait_names.contains(trait_name) && !is_imported {
            type_provenance.insert(trait_name.clone(), "core".to_string());
        }
    }
    // Then add user-defined traits (skip if already registered)
    for decl in &module.decls {
        if let Decl::DefTrait { name, methods, .. } = decl {
            if !seen_traits.contains(name) {
                let method_info: Vec<(String, usize)> = methods.iter().map(|m| {
                    (m.name.clone(), m.params.len())
                }).collect();
                trait_defs.push(TraitDefInfo {
                    name: name.clone(),
                    methods: method_info,
                    is_imported: false,
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

    // Collect struct declarations from AST for codegen
    let struct_decls: Vec<_> = module.decls.iter().filter_map(|decl| match decl {
        Decl::DefType(td) => match &td.kind {
            TypeDeclKind::Record { fields } => Some((td.name.clone(), fields.clone())),
            _ => None,
        },
        _ => None,
    }).collect();

    // Collect sum type declarations from AST for codegen
    let mut sum_decls: Vec<(String, Vec<String>, Vec<Variant>)> = module.decls.iter().filter_map(|decl| match decl {
        Decl::DefType(td) => match &td.kind {
            TypeDeclKind::Sum { variants } => Some((td.name.clone(), td.type_params.clone(), variants.clone())),
            _ => None,
        },
        _ => None,
    }).collect();

    // Inject prelude sum types not shadowed by user declarations
    {
        let user_type_names: HashSet<String> = sum_decls.iter().map(|(n, _, _): &(String, Vec<String>, Vec<Variant>)| n.clone()).collect();
        for &module_path in krypton_modules::stdlib_loader::StdlibLoader::PRELUDE_MODULES {
            if let Some(source) = krypton_modules::stdlib_loader::StdlibLoader::get_source(module_path) {
                let (stdlib_module, _) = krypton_parser::parser::parse(source);
                for decl in stdlib_module.decls {
                    if let Decl::DefType(td) = decl {
                        if let TypeDeclKind::Sum { variants } = td.kind {
                            if !user_type_names.contains(&td.name) {
                                type_provenance.insert(td.name.clone(), module_path.to_string());
                                for v in &variants {
                                    type_provenance.insert(v.name.clone(), module_path.to_string());
                                }
                                sum_decls.push((td.name, td.type_params, variants));
                            }
                        }
                    }
                }
            }
        }
    }

    // Inject imported sum types into sum_decls for codegen
    {
        let existing_type_names: HashSet<String> = sum_decls.iter().map(|(n, _, _)| n.clone()).collect();
        for (type_name, (source_path, vis)) in &imported_type_info {
            if existing_type_names.contains(type_name) || !matches!(vis, Visibility::PubOpen) {
                continue;
            }
            if let Some(imported_mod) = parsed_modules.get(source_path.as_str()) {
                for decl in &imported_mod.decls {
                    if let Decl::DefType(td) = decl {
                        if td.name == *type_name {
                            if let TypeDeclKind::Sum { variants } = &td.kind {
                                type_provenance.insert(td.name.clone(), source_path.clone());
                                for v in variants {
                                    type_provenance.insert(v.name.clone(), source_path.clone());
                                }
                                sum_decls.push((td.name.clone(), td.type_params.clone(), variants.clone()));
                            }
                            break;
                        }
                    }
                }
            }
        }
    }

    // Add type provenance entries from imported types (for re-exports and cross-module codegen)
    for (type_name, (source_path, _)) in &imported_type_info {
        type_provenance.insert(type_name.clone(), source_path.clone());
    }

    // Build type_visibility map from parsed type declarations
    let mut type_visibility: HashMap<String, Visibility> = HashMap::new();
    for decl in &module.decls {
        if let Decl::DefType(td) = decl {
            type_visibility.insert(td.name.clone(), td.visibility.clone());
        }
    }

    Ok(TypedModule {
        module_path,
        fn_types: results,
        functions,
        trait_defs,
        instance_defs,
        fn_constraints,
        imported_fn_constraints,
        trait_method_map: trait_method_map.clone(),
        extern_fns,
        imported_extern_fns,
        struct_decls,
        sum_decls,
        fn_provenance: fn_provenance_map,
        type_provenance,
        type_visibility,
        reexported_fn_types,
        reexported_type_names,
        reexported_type_visibility,
        exported_trait_defs,
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
                let a_pattern = TypedPattern::Constructor {
                    name: variant.name.clone(),
                    args: a_bindings.iter().zip(variant.fields.iter()).map(|(n, ft)| TypedPattern::Var { name: n.clone(), ty: ft.clone(), span }).collect(),
                    ty: target_type.clone(),
                    span,
                };

                // Inner match on __b
                let inner_arms: Vec<TypedMatchArm> = variants.iter().map(|inner_variant| {
                    if inner_variant.name == variant.name {
                        let b_bindings: Vec<String> = (0..inner_variant.fields.len())
                            .map(|i| format!("__y{}", i))
                            .collect();
                        let b_pattern = TypedPattern::Constructor {
                            name: inner_variant.name.clone(),
                            args: b_bindings.iter().zip(inner_variant.fields.iter()).map(|(n, ft)| TypedPattern::Var { name: n.clone(), ty: ft.clone(), span }).collect(),
                            ty: target_type.clone(),
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
                            pattern: TypedPattern::Wildcard { ty: target_type.clone(), span },
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
                let pattern = TypedPattern::Constructor {
                    name: variant.name.clone(),
                    args: bindings.iter().zip(variant.fields.iter()).map(|(n, ft)| TypedPattern::Var { name: n.clone(), ty: ft.clone(), span }).collect(),
                    ty: target_type.clone(),
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
