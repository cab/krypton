use std::collections::HashSet;

use krypton_parser::ast::{Expr, FnDecl, Module, Decl, TypeExpr};

use crate::unify::{SpannedTypeError, TypeError};

/// Check if a param has an `own` type annotation.
fn is_own_param(param: &krypton_parser::ast::Param) -> bool {
    matches!(&param.ty, Some(TypeExpr::Own { .. }))
}

/// Affine verification: track `own` bindings and flag double-use as E0101,
/// or partial-branch use as E0102.
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
    let mut partially_consumed = HashSet::new();
    check_expr(&decl.body, &owned, &mut consumed, &mut partially_consumed)
}

fn check_expr(
    expr: &Expr,
    owned: &HashSet<String>,
    consumed: &mut HashSet<String>,
    partially_consumed: &mut HashSet<String>,
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
                if partially_consumed.contains(name) {
                    return Err(SpannedTypeError {
                        error: TypeError::MovedInBranch {
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
            check_expr(func, owned, consumed, partially_consumed)?;
            for arg in args {
                check_expr(arg, owned, consumed, partially_consumed)?;
            }
            let _ = span;
            Ok(())
        }

        Expr::Let { value, body, .. } => {
            check_expr(value, owned, consumed, partially_consumed)?;
            if let Some(body) = body {
                check_expr(body, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        Expr::LetPattern { value, body, .. } => {
            check_expr(value, owned, consumed, partially_consumed)?;
            if let Some(body) = body {
                check_expr(body, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        Expr::Do { exprs, .. } => {
            for e in exprs {
                check_expr(e, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        Expr::If { cond, then_, else_, .. } => {
            check_expr(cond, owned, consumed, partially_consumed)?;
            let before = consumed.clone();
            let mut then_consumed = consumed.clone();
            let mut then_partial = partially_consumed.clone();
            let mut else_consumed = consumed.clone();
            let mut else_partial = partially_consumed.clone();
            check_expr(then_, owned, &mut then_consumed, &mut then_partial)?;
            check_expr(else_, owned, &mut else_consumed, &mut else_partial)?;

            let newly_in_then: HashSet<String> = then_consumed.difference(&before).cloned().collect();
            let newly_in_else: HashSet<String> = else_consumed.difference(&before).cloned().collect();
            let in_all: HashSet<String> = newly_in_then.intersection(&newly_in_else).cloned().collect();
            let in_some: HashSet<String> = newly_in_then.symmetric_difference(&newly_in_else).cloned().collect();

            for name in &in_all {
                consumed.insert(name.clone());
            }
            for name in &in_some {
                partially_consumed.insert(name.clone());
            }
            // Merge partial sets from branches
            for name in then_partial.union(&else_partial) {
                partially_consumed.insert(name.clone());
            }
            Ok(())
        }

        Expr::Match { scrutinee, arms, .. } => {
            check_expr(scrutinee, owned, consumed, partially_consumed)?;
            let before = consumed.clone();
            let n = arms.len();
            let mut per_arm_new: Vec<HashSet<String>> = Vec::new();
            let mut merged_partial = partially_consumed.clone();

            for arm in arms {
                let mut arm_consumed = consumed.clone();
                let mut arm_partial = partially_consumed.clone();
                check_expr(&arm.body, owned, &mut arm_consumed, &mut arm_partial)?;
                let newly: HashSet<String> = arm_consumed.difference(&before).cloned().collect();
                per_arm_new.push(newly);
                for name in &arm_partial {
                    merged_partial.insert(name.clone());
                }
            }

            // Count how many arms consumed each name
            let all_names: HashSet<String> = per_arm_new.iter().flat_map(|s| s.iter().cloned()).collect();
            for name in &all_names {
                let count = per_arm_new.iter().filter(|s| s.contains(name)).count();
                if count == n {
                    consumed.insert(name.clone());
                } else {
                    merged_partial.insert(name.clone());
                }
            }
            *partially_consumed = merged_partial;
            Ok(())
        }

        Expr::BinaryOp { lhs, rhs, .. } => {
            check_expr(lhs, owned, consumed, partially_consumed)?;
            check_expr(rhs, owned, consumed, partially_consumed)
        }

        Expr::UnaryOp { operand, .. } => {
            check_expr(operand, owned, consumed, partially_consumed)
        }

        Expr::Lambda { body, .. } => {
            check_expr(body, owned, consumed, partially_consumed)
        }

        Expr::FieldAccess { expr, .. } => {
            check_expr(expr, owned, consumed, partially_consumed)
        }

        Expr::StructLit { fields, .. } => {
            for (_, field_expr) in fields {
                check_expr(field_expr, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        Expr::StructUpdate { base, fields, .. } => {
            check_expr(base, owned, consumed, partially_consumed)?;
            for (_, field_expr) in fields {
                check_expr(field_expr, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        Expr::Tuple { elements, .. } => {
            for e in elements {
                check_expr(e, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        Expr::Recur { args, .. } => {
            for a in args {
                check_expr(a, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        Expr::QuestionMark { expr, .. } => {
            check_expr(expr, owned, consumed, partially_consumed)
        }

        Expr::List { elements, .. } => {
            for e in elements {
                check_expr(e, owned, consumed, partially_consumed)?;
            }
            Ok(())
        }

        // Lit — no owned vars to consume
        Expr::Lit { .. } => Ok(()),
    }
}
