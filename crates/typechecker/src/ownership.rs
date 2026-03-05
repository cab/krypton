use std::collections::HashSet;

use krypton_parser::ast::{Expr, FnDecl, Module, Decl, TypeExpr};

use crate::unify::{SpannedTypeError, TypeError};

/// Check if a param has an `own` type annotation.
fn is_own_param(param: &krypton_parser::ast::Param) -> bool {
    matches!(&param.ty, Some(TypeExpr::Own { .. }))
}

/// Affine verification: track `own` bindings and flag double-use as E0101.
pub fn check_ownership(module: &Module) -> Result<(), SpannedTypeError> {
    for decl in &module.decls {
        if let Decl::DefFn(fn_decl) = decl {
            check_fn(fn_decl)?;
        }
    }
    Ok(())
}

fn check_fn(decl: &FnDecl) -> Result<(), SpannedTypeError> {
    let owned: HashSet<String> = decl
        .params
        .iter()
        .filter(|p| is_own_param(p))
        .map(|p| p.name.clone())
        .collect();

    if owned.is_empty() {
        return Ok(());
    }

    let mut consumed = HashSet::new();
    check_expr(&decl.body, &owned, &mut consumed)
}

fn check_expr(
    expr: &Expr,
    owned: &HashSet<String>,
    consumed: &mut HashSet<String>,
) -> Result<(), SpannedTypeError> {
    match expr {
        Expr::Var { name, span, .. } => {
            if owned.contains(name) {
                if consumed.contains(name) {
                    return Err(SpannedTypeError {
                        error: TypeError::AlreadyMoved {
                            name: name.clone(),
                        },
                        span: *span,
                    });
                }
                consumed.insert(name.clone());
            }
            Ok(())
        }

        Expr::App { func, args, span, .. } => {
            check_expr(func, owned, consumed)?;
            for arg in args {
                check_expr(arg, owned, consumed)?;
            }
            // If func is a Var that's owned, it was already checked above.
            // But App with a Var func — the Var reference in func is already handled.
            let _ = span;
            Ok(())
        }

        Expr::Let { value, body, .. } => {
            check_expr(value, owned, consumed)?;
            if let Some(body) = body {
                check_expr(body, owned, consumed)?;
            }
            Ok(())
        }

        Expr::LetPattern { value, body, .. } => {
            check_expr(value, owned, consumed)?;
            if let Some(body) = body {
                check_expr(body, owned, consumed)?;
            }
            Ok(())
        }

        Expr::Do { exprs, .. } => {
            for e in exprs {
                check_expr(e, owned, consumed)?;
            }
            Ok(())
        }

        Expr::If { cond, then_, else_, .. } => {
            check_expr(cond, owned, consumed)?;
            let mut then_consumed = consumed.clone();
            let mut else_consumed = consumed.clone();
            check_expr(then_, owned, &mut then_consumed)?;
            check_expr(else_, owned, &mut else_consumed)?;
            // Union: consumed in ANY branch → consumed after
            for name in then_consumed.iter().chain(else_consumed.iter()) {
                consumed.insert(name.clone());
            }
            Ok(())
        }

        Expr::Match { scrutinee, arms, .. } => {
            check_expr(scrutinee, owned, consumed)?;
            let mut all_consumed = consumed.clone();
            for arm in arms {
                let mut arm_consumed = consumed.clone();
                check_expr(&arm.body, owned, &mut arm_consumed)?;
                for name in &arm_consumed {
                    all_consumed.insert(name.clone());
                }
            }
            *consumed = all_consumed;
            Ok(())
        }

        Expr::BinaryOp { lhs, rhs, .. } => {
            check_expr(lhs, owned, consumed)?;
            check_expr(rhs, owned, consumed)
        }

        Expr::UnaryOp { operand, .. } => {
            check_expr(operand, owned, consumed)
        }

        Expr::Lambda { body, .. } => {
            check_expr(body, owned, consumed)
        }

        Expr::FieldAccess { expr, .. } => {
            check_expr(expr, owned, consumed)
        }

        Expr::StructLit { fields, .. } => {
            for (_, field_expr) in fields {
                check_expr(field_expr, owned, consumed)?;
            }
            Ok(())
        }

        Expr::StructUpdate { base, fields, .. } => {
            check_expr(base, owned, consumed)?;
            for (_, field_expr) in fields {
                check_expr(field_expr, owned, consumed)?;
            }
            Ok(())
        }

        Expr::Tuple { elements, .. } => {
            for e in elements {
                check_expr(e, owned, consumed)?;
            }
            Ok(())
        }

        Expr::Recur { args, .. } => {
            for a in args {
                check_expr(a, owned, consumed)?;
            }
            Ok(())
        }

        Expr::Send { target, message, .. } => {
            check_expr(target, owned, consumed)?;
            check_expr(message, owned, consumed)
        }

        Expr::Spawn { func, args, .. } => {
            check_expr(func, owned, consumed)?;
            for a in args {
                check_expr(a, owned, consumed)?;
            }
            Ok(())
        }

        Expr::QuestionMark { expr, .. } => {
            check_expr(expr, owned, consumed)
        }

        Expr::List { elements, .. } => {
            for e in elements {
                check_expr(e, owned, consumed)?;
            }
            Ok(())
        }

        // Lit, Self_, Receive — no owned vars to consume
        Expr::Lit { .. } | Expr::Self_ { .. } | Expr::Receive { .. } => Ok(()),
    }
}
