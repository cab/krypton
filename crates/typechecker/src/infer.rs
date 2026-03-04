use std::collections::HashSet;

use alang_parser::ast::{BinOp, Expr, Lit, UnaryOp};

use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{unify, TypeError};

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

/// Infer the type of an expression using Algorithm J.
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<Type, TypeError> {
    match expr {
        Expr::Lit { value, .. } => match value {
            Lit::Int(_) => Ok(Type::Int),
            Lit::Float(_) => Ok(Type::Float),
            Lit::Bool(_) => Ok(Type::Bool),
            Lit::String(_) => Ok(Type::String),
            Lit::Unit => Ok(Type::Unit),
        },

        Expr::Var { name, .. } => match env.lookup(name) {
            Some(scheme) => {
                let scheme = scheme.clone();
                Ok(scheme.instantiate(&mut || gen.fresh()))
            }
            None => Err(TypeError::Mismatch {
                expected: Type::Unit,
                actual: Type::Named(format!("undefined: {}", name), vec![]),
            }),
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

        Expr::App { func, args, .. } => {
            let func_ty = infer_expr(func, env, subst, gen)?;
            let mut arg_types = Vec::new();
            for a in args {
                arg_types.push(infer_expr(a, env, subst, gen)?);
            }
            let ret_var = Type::Var(gen.fresh());
            let expected_fn = Type::Fn(arg_types, Box::new(ret_var.clone()));
            unify(&func_ty, &expected_fn, subst)?;
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
            ..
        } => {
            let cond_ty = infer_expr(cond, env, subst, gen)?;
            unify(&cond_ty, &Type::Bool, subst)?;
            let then_ty = infer_expr(then_, env, subst, gen)?;
            let else_ty = infer_expr(else_, env, subst, gen)?;
            unify(&then_ty, &else_ty, subst)?;
            Ok(subst.apply(&then_ty))
        }

        Expr::Do { exprs, .. } => {
            if exprs.is_empty() {
                return Ok(Type::Unit);
            }
            let mut last_ty = Type::Unit;
            for e in exprs {
                last_ty = infer_expr(e, env, subst, gen)?;
            }
            Ok(last_ty)
        }

        Expr::BinaryOp { op, lhs, rhs, .. } => {
            let lhs_ty = infer_expr(lhs, env, subst, gen)?;
            let rhs_ty = infer_expr(rhs, env, subst, gen)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                    unify(&lhs_ty, &Type::Int, subst)?;
                    unify(&rhs_ty, &Type::Int, subst)?;
                    Ok(Type::Int)
                }
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    unify(&lhs_ty, &Type::Int, subst)?;
                    unify(&rhs_ty, &Type::Int, subst)?;
                    Ok(Type::Bool)
                }
            }
        }

        Expr::UnaryOp { op, operand, .. } => {
            let operand_ty = infer_expr(operand, env, subst, gen)?;
            match op {
                UnaryOp::Neg => {
                    unify(&operand_ty, &Type::Int, subst)?;
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
