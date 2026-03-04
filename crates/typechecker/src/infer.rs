use std::collections::HashSet;

use alang_parser::ast::{BinOp, Decl, Expr, Lit, Module, UnaryOp};

use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{unify, SpannedTypeError, TypeError};

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
fn spanned(error: TypeError, span: alang_parser::ast::Span) -> SpannedTypeError {
    SpannedTypeError { error, span }
}

/// Check if a type is concretely not a function (after walking substitution).
fn is_concrete_non_function(ty: &Type, subst: &Substitution) -> bool {
    let walked = subst.apply(ty);
    !matches!(walked, Type::Var(_) | Type::Fn(_, _))
}

/// Infer the type of an expression using Algorithm J.
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
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

        Expr::Lambda { params, body, .. } => {
            let mut param_types = Vec::new();
            env.push_scope();
            for p in params {
                let tv = Type::Var(gen.fresh());
                param_types.push(tv.clone());
                env.bind(p.name.clone(), TypeScheme::mono(tv));
            }
            let body_ty = infer_expr(body, env, subst, gen)?;
            env.pop_scope();
            let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
            let body_ty = subst.apply(&body_ty);
            Ok(Type::Fn(param_types, Box::new(body_ty)))
        }

        Expr::App {
            func, args, span, ..
        } => {
            let func_ty = infer_expr(func, env, subst, gen)?;
            let mut arg_types = Vec::new();
            for a in args {
                arg_types.push(infer_expr(a, env, subst, gen)?);
            }

            // Check if the function type is concretely not a function
            if is_concrete_non_function(&func_ty, subst) {
                let actual = subst.apply(&func_ty);
                return Err(spanned(TypeError::NotAFunction { actual }, *span));
            }

            let ret_var = Type::Var(gen.fresh());
            let expected_fn = Type::Fn(arg_types, Box::new(ret_var.clone()));
            unify(&func_ty, &expected_fn, subst)
                .map_err(|e| spanned(e, *span))?;
            Ok(subst.apply(&ret_var))
        }

        Expr::Let {
            name,
            value,
            body,
            ..
        } => {
            let val_ty = infer_expr(value, env, subst, gen)?;
            match body {
                Some(body) => {
                    let scheme = generalize(&val_ty, env, subst);
                    env.push_scope();
                    env.bind(name.clone(), scheme);
                    let body_ty = infer_expr(body, env, subst, gen)?;
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
            let cond_ty = infer_expr(cond, env, subst, gen)?;
            unify(&cond_ty, &Type::Bool, subst)
                .map_err(|e| spanned(e, *span))?;
            let then_ty = infer_expr(then_, env, subst, gen)?;
            let else_ty = infer_expr(else_, env, subst, gen)?;
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
                last_ty = infer_expr(e, env, subst, gen)?;
            }
            env.pop_scope();
            Ok(last_ty)
        }

        Expr::BinaryOp {
            op, lhs, rhs, span, ..
        } => {
            let lhs_ty = infer_expr(lhs, env, subst, gen)?;
            let rhs_ty = infer_expr(rhs, env, subst, gen)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                    unify(&lhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    unify(&rhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    Ok(Type::Int)
                }
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    unify(&lhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    unify(&rhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    Ok(Type::Bool)
                }
            }
        }

        Expr::UnaryOp {
            op, operand, span, ..
        } => {
            let operand_ty = infer_expr(operand, env, subst, gen)?;
            match op {
                UnaryOp::Neg => {
                    unify(&operand_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    Ok(Type::Int)
                }
            }
        }

        // Unsupported expression forms return a fresh type variable for now
        _ => Ok(Type::Var(gen.fresh())),
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
/// Uses a three-pass approach to support forward references:
/// 1. Bind each def name to a fresh type variable
/// 2. Infer each def body and unify with its pre-bound variable
/// 3. Apply final substitution and generalize into type schemes
pub fn infer_module(module: &Module) -> Result<Vec<(String, TypeScheme)>, SpannedTypeError> {
    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();

    // Collect DefFn declarations
    let fn_decls: Vec<&alang_parser::ast::FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Pass 1: bind each name to a fresh type variable
    let mut pre_bound: Vec<(String, Type)> = Vec::new();
    for decl in &fn_decls {
        let tv = Type::Var(gen.fresh());
        env.bind(decl.name.clone(), TypeScheme::mono(tv.clone()));
        pre_bound.push((decl.name.clone(), tv));
    }

    // Pass 2: infer each body and unify with the pre-bound variable
    for (i, decl) in fn_decls.iter().enumerate() {
        // Create a scope for the function parameters
        env.push_scope();
        let mut param_types = Vec::new();
        for p in &decl.params {
            let tv = Type::Var(gen.fresh());
            param_types.push(tv.clone());
            env.bind(p.name.clone(), TypeScheme::mono(tv));
        }
        let body_ty = infer_expr(&decl.body, &mut env, &mut subst, &mut gen)?;
        env.pop_scope();

        // Build the function type and unify with the pre-bound variable
        let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
        let body_ty = subst.apply(&body_ty);
        let fn_ty = Type::Fn(param_types, Box::new(body_ty));
        unify(&pre_bound[i].1, &fn_ty, &mut subst)
            .map_err(|e| spanned(e, decl.span))?;
    }

    // Pass 3: apply final substitution and generalize
    // Use an empty env for generalization — all free vars in top-level defs
    // should be universally quantified (the pre-bound names in env would
    // incorrectly prevent generalization of their own type variables).
    let empty_env = TypeEnv::new();
    let mut results = Vec::new();
    for (name, tv) in &pre_bound {
        let final_ty = subst.apply(tv);
        let scheme = generalize(&final_ty, &empty_env, &subst);
        results.push((name.clone(), scheme));
    }

    Ok(results)
}
