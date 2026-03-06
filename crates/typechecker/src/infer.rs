use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Decl, Expr, Lit, Module, Pattern, Span, UnaryOp};

use crate::scc;
use crate::type_registry::{self, TypeRegistry};
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

/// Result of type inference for a module.
pub struct ModuleTypeInfo {
    pub fn_types: Vec<(String, TypeScheme)>,
    /// Maps each lambda's span (start, end) to its (param_types, return_type).
    pub lambda_types: HashMap<Span, (Vec<Type>, Type)>,
    /// Spans of `let` bindings whose inferred type is `Own(Fn(...))`.
    pub let_own_spans: HashSet<Span>,
    /// Maps each lambda span to the name of the first own-captured variable.
    pub lambda_own_captures: HashMap<Span, String>,
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
    SpannedTypeError { error, span, note: None }
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
    infer_expr_inner(expr, env, subst, gen, None, None, None, None, None)
}

/// Infer the type of an expression, with optional access to the type registry
/// for struct field access and update operations.
fn infer_expr_inner(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    mut lambda_types: Option<&mut HashMap<Span, (Vec<Type>, Type)>>,
    recur_params: Option<&[Type]>,
    mut let_own_spans: Option<&mut HashSet<Span>>,
    mut lambda_own_captures: Option<&mut HashMap<Span, String>>,
) -> Result<Type, SpannedTypeError> {
    match expr {
        Expr::Lit { value, .. } => match value {
            Lit::Int(_) => Ok(Type::Int),
            Lit::Float(_) => Ok(Type::Float),
            Lit::Bool(_) => Ok(Type::Bool),
            Lit::String(_) => Ok(Type::String),
            Lit::Unit => Ok(Type::Unit),
        },

        Expr::Var { name, span, .. } => match env.lookup(name) {
            Some(scheme) => {
                let scheme = scheme.clone();
                Ok(scheme.instantiate(&mut || gen.fresh()))
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
            let body_ty = infer_expr_inner(body, env, subst, gen, registry, lambda_types.as_deref_mut(), None, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            env.pop_scope();
            let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
            let body_ty = subst.apply(&body_ty);
            if let Some(lt) = lambda_types.as_deref_mut() {
                lt.insert(*span, (param_types.clone(), body_ty.clone()));
            }
            let fn_ty = Type::Fn(param_types, Box::new(body_ty));
            let param_names: HashSet<&str> = params.iter().map(|p| p.name.as_str()).collect();
            if captures_own_value(body, &param_names, env, subst) {
                if let Some(ref mut captures) = lambda_own_captures {
                    if let Some(cap_name) = first_own_capture(body, &param_names, env, subst) {
                        captures.insert(*span, cap_name);
                    }
                }
                Ok(Type::Own(Box::new(fn_ty)))
            } else {
                Ok(fn_ty)
            }
        }

        Expr::App {
            func, args, span, ..
        } => {
            let func_ty = infer_expr_inner(func, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let mut arg_types = Vec::new();
            for a in args {
                arg_types.push(infer_expr_inner(a, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?);
            }

            // Check if the function type is concretely not a function
            if is_concrete_non_function(&func_ty, subst) {
                let actual = subst.apply(&func_ty);
                return Err(spanned(TypeError::NotAFunction { actual }, *span));
            }

            let ret_var = Type::Var(gen.fresh());
            // Only apply own coercion for non-constructor calls
            let is_constructor = if let Expr::Var { name, .. } = func.as_ref() {
                registry.is_some_and(|r| r.is_constructor(name))
            } else {
                false
            };
            let coerced_args = if is_constructor {
                arg_types.clone()
            } else {
                coerce_own_args(&func_ty, &arg_types, subst)
            };
            let expected_fn = Type::Fn(coerced_args, Box::new(ret_var.clone()));
            // Unwrap Own wrapper for callable own fn types
            let unwrapped_func_ty = match subst.apply(&func_ty) {
                Type::Own(inner) if matches!(*inner, Type::Fn(_, _)) => *inner,
                _ => func_ty,
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
            Ok(subst.apply(&ret_var))
        }

        Expr::Let {
            name,
            value,
            body,
            span,
        } => {
            let val_ty = infer_expr_inner(value, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            // Track let bindings whose type is Own(Fn(...))
            let resolved_val = subst.apply(&val_ty);
            if matches!(&resolved_val, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _))) {
                if let Some(ref mut los) = let_own_spans {
                    los.insert(*span);
                }
            }
            match body {
                Some(body) => {
                    let scheme = generalize(&val_ty, env, subst);
                    env.push_scope();
                    env.bind(name.clone(), scheme);
                    let body_ty = infer_expr_inner(body, env, subst, gen, registry, lambda_types, recur_params, let_own_spans, lambda_own_captures)?;
                    env.pop_scope();
                    Ok(body_ty)
                }
                None => {
                    // Statement form in a do block — generalize for let-polymorphism
                    let scheme = generalize(&val_ty, env, subst);
                    env.bind(name.clone(), scheme);
                    Ok(Type::Unit)
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
            let cond_ty = infer_expr_inner(cond, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            unify(&cond_ty, &Type::Bool, subst)
                .map_err(|e| spanned(e, *span))?;
            let then_ty = infer_expr_inner(then_, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let else_ty = infer_expr_inner(else_, env, subst, gen, registry, lambda_types, recur_params, let_own_spans, lambda_own_captures)?;
            unify(&then_ty, &else_ty, subst)
                .map_err(|e| spanned(e, *span))?;
            Ok(subst.apply(&then_ty))
        }

        Expr::Do { exprs, .. } => {
            env.push_scope();
            if exprs.is_empty() {
                env.pop_scope();
                return Ok(Type::Unit);
            }
            let mut last_ty = Type::Unit;
            for e in exprs {
                last_ty = infer_expr_inner(e, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            }
            env.pop_scope();
            Ok(last_ty)
        }

        Expr::BinaryOp {
            op, lhs, rhs, span, ..
        } => {
            let lhs_ty = infer_expr_inner(lhs, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let rhs_ty = infer_expr_inner(rhs, env, subst, gen, registry, lambda_types, recur_params, let_own_spans, lambda_own_captures)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                    unify(&lhs_ty, &rhs_ty, subst)
                        .map_err(|e| spanned(e, *span))?;
                    let resolved = subst.apply(&lhs_ty);
                    match &resolved {
                        Type::Int | Type::Float => Ok(resolved),
                        Type::Var(_) => {
                            // Unconstrained numeric type defaults to Int
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                            Ok(Type::Int)
                        }
                        _ => Err(spanned(TypeError::Mismatch { expected: Type::Int, actual: resolved }, *span)),
                    }
                }
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    unify(&lhs_ty, &rhs_ty, subst)
                        .map_err(|e| spanned(e, *span))?;
                    let resolved = subst.apply(&lhs_ty);
                    match &resolved {
                        Type::Int | Type::Float => {}
                        Type::Var(_) => {
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                        }
                        _ => return Err(spanned(TypeError::Mismatch { expected: Type::Int, actual: resolved }, *span)),
                    }
                    Ok(Type::Bool)
                }
            }
        }

        Expr::UnaryOp {
            op, operand, span, ..
        } => {
            let operand_ty = infer_expr_inner(operand, env, subst, gen, registry, lambda_types, recur_params, let_own_spans, lambda_own_captures)?;
            match op {
                UnaryOp::Neg => {
                    let resolved = subst.apply(&operand_ty);
                    match &resolved {
                        Type::Int | Type::Float => Ok(resolved),
                        Type::Var(_) => {
                            unify(&resolved, &Type::Int, subst)
                                .map_err(|e| spanned(e, *span))?;
                            Ok(Type::Int)
                        }
                        _ => Err(spanned(TypeError::Mismatch { expected: Type::Int, actual: resolved }, *span)),
                    }
                }
            }
        }

        Expr::Recur { args, span, .. } => {
            match recur_params {
                Some(params) => {
                    if args.len() != params.len() {
                        return Err(spanned(
                            TypeError::WrongArity { expected: params.len(), actual: args.len() },
                            *span,
                        ));
                    }
                    for (a, p) in args.iter().zip(params.iter()) {
                        let arg_ty = infer_expr_inner(a, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                        unify(&arg_ty, p, subst).map_err(|e| spanned(e, *span))?;
                    }
                    Ok(Type::Var(gen.fresh()))
                }
                None => {
                    for a in args {
                        infer_expr_inner(a, env, subst, gen, registry, lambda_types.as_deref_mut(), None, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                    }
                    Ok(Type::Var(gen.fresh()))
                }
            }
        }

        Expr::FieldAccess { expr: target, field, span } => {
            let target_ty = infer_expr_inner(target, env, subst, gen, registry, lambda_types, recur_params, let_own_spans, lambda_own_captures)?;
            let resolved = subst.apply(&target_ty);
            resolve_field_access(&resolved, field, *span, registry)
        }

        Expr::StructUpdate { base, fields, span } => {
            let base_ty = infer_expr_inner(base, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let resolved = subst.apply(&base_ty);
            resolve_struct_update(&resolved, fields, *span, env, subst, gen, registry, lambda_types, recur_params, let_own_spans, lambda_own_captures)?;
            Ok(resolved)
        }

        Expr::Match { scrutinee, arms, span } => {
            let scrutinee_ty = infer_expr_inner(scrutinee, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            let result_ty = Type::Var(gen.fresh());
            for arm in arms {
                env.push_scope();
                check_pattern(&arm.pattern, &subst.apply(&scrutinee_ty), env, subst, gen, registry, *span)?;
                let body_ty = infer_expr_inner(&arm.body, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                unify(&result_ty, &body_ty, subst).map_err(|e| spanned(e, *span))?;
                env.pop_scope();
            }
            crate::exhaustiveness::check_exhaustiveness(
                &subst.apply(&scrutinee_ty),
                arms,
                registry,
                *span,
            )?;
            Ok(subst.apply(&result_ty))
        }

        Expr::Tuple { elements, .. } => {
            let mut elem_types = Vec::new();
            for e in elements {
                elem_types.push(infer_expr_inner(e, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?);
            }
            Ok(Type::Tuple(elem_types))
        }

        Expr::LetPattern { pattern, value, body, span } => {
            let val_ty = infer_expr_inner(value, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
            match body {
                Some(body) => {
                    env.push_scope();
                    check_pattern(pattern, &subst.apply(&val_ty), env, subst, gen, registry, *span)?;
                    let body_ty = infer_expr_inner(body, env, subst, gen, registry, lambda_types, recur_params, let_own_spans, lambda_own_captures)?;
                    env.pop_scope();
                    Ok(body_ty)
                }
                None => {
                    check_pattern(pattern, &subst.apply(&val_ty), env, subst, gen, registry, *span)?;
                    Ok(Type::Unit)
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
                    // Create fresh type args for generic structs
                    let fresh_args: Vec<Type> = info.type_param_vars.iter().map(|_| Type::Var(gen.fresh())).collect();
                    let struct_ty = Type::Named(name.clone(), fresh_args.clone());

                    // Check for missing fields
                    let provided: HashSet<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                    let missing: Vec<String> = record_fields.iter()
                        .filter(|(n, _)| !provided.contains(n.as_str()))
                        .map(|(n, _)| n.clone())
                        .collect();
                    if !missing.is_empty() {
                        return Err(spanned(TypeError::MissingFields { type_name: name.clone(), fields: missing }, *span));
                    }

                    // Type-check each provided field
                    for (field_name, field_expr) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, expected_ty)) => {
                                let expected = instantiate_field_type(expected_ty, info, &fresh_args);
                                let actual_ty = infer_expr_inner(field_expr, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                                unify(&actual_ty, &expected, subst)
                                    .map_err(|e| spanned(e, *span))?;
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

                    Ok(struct_ty)
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

/// Validate a struct update expression.
fn resolve_struct_update(
    resolved_ty: &Type,
    fields: &[(String, Expr)],
    span: krypton_parser::ast::Span,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    mut lambda_types: Option<&mut HashMap<Span, (Vec<Type>, Type)>>,
    recur_params: Option<&[Type]>,
    mut let_own_spans: Option<&mut HashSet<Span>>,
    mut lambda_own_captures: Option<&mut HashMap<Span, String>>,
) -> Result<(), SpannedTypeError> {
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
                    for (field_name, field_expr) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, expected_ty)) => {
                                let expected = instantiate_field_type(expected_ty, info, type_args);
                                let actual_ty = infer_expr_inner(field_expr, env, subst, gen, registry, lambda_types.as_deref_mut(), recur_params, let_own_spans.as_deref_mut(), lambda_own_captures.as_deref_mut())?;
                                unify(&actual_ty, &expected, subst)
                                    .map_err(|e| spanned(e, span))?;
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

/// Infer types for all top-level definitions in a module.
///
/// Uses SCC (strongly connected component) analysis to process definitions
/// in dependency order. Functions within the same SCC are inferred together
/// as a mutually recursive group, then generalized before later SCCs see them.
pub fn infer_module(module: &Module) -> Result<ModuleTypeInfo, SpannedTypeError> {
    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();
    let mut registry = TypeRegistry::new();
    let mut lambda_types: HashMap<Span, (Vec<Type>, Type)> = HashMap::new();
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
            let body_ty = infer_expr_inner(&decl.body, &mut env, &mut subst, &mut gen, Some(&registry), Some(&mut lambda_types), Some(&param_types), Some(&mut let_own_spans), Some(&mut lambda_own_captures))?;
            env.pop_scope();

            let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
            let body_ty = subst.apply(&body_ty);
            let fn_ty = Type::Fn(param_types, Box::new(body_ty));
            unify(tv, &fn_ty, &mut subst)
                .map_err(|e| spanned(e, decl.span))?;
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

    // Apply final substitution to lambda types
    let lambda_types = lambda_types
        .into_iter()
        .map(|(span, (params, ret))| {
            let params = params.iter().map(|t| subst.apply(t)).collect();
            let ret = subst.apply(&ret);
            (span, (params, ret))
        })
        .collect();

    // Run affine ownership verification after successful inference
    crate::ownership::check_ownership(module, &results, &registry, &let_own_spans, &lambda_own_captures)?;

    Ok(ModuleTypeInfo {
        fn_types: results,
        lambda_types,
        let_own_spans,
        lambda_own_captures,
    })
}
