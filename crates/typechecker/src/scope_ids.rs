//! Pre-pass that stamps each scope-bearing `TypedExpr` node with a unique
//! [`ScopeId`]. Runs before `compute_auto_close` so both that analyzer and
//! the downstream IR lowerer can refer to scopes by identity rather than
//! by span (which desugaring is free to duplicate).
//!
//! Scope nodes are:
//! - `Do(_)`
//! - `Let { body: Some(_), .. }`
//! - `LetPattern { body: Some(_), .. }`
//! - function body (stamped at the entry)
//! - `Lambda { body, .. }` body
//!
//! All other `TypedExpr` nodes are left with `scope_id: None`.

use crate::typed_ast::{
    ScopeId, TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedPattern,
};

/// Allocator for ScopeIds. One allocator per typechecker run produces
/// globally unique IDs across functions, so collisions are impossible
/// within the same module lowering unit.
#[derive(Default)]
pub struct ScopeIdGen {
    next: u32,
}

impl ScopeIdGen {
    pub fn fresh(&mut self) -> ScopeId {
        let id = ScopeId(self.next);
        self.next += 1;
        id
    }
}

/// Stamp scope IDs on every `TypedFnDecl` in the module.
pub fn stamp_functions(functions: &mut [TypedFnDecl]) {
    let mut gen = ScopeIdGen::default();
    for decl in functions {
        // Allocate the fn-level scope (owns params, parent of any body scope).
        decl.fn_scope_id = gen.fresh();
        // Walk the body. Scope-bearing body nodes (Do / Let{body:Some} /
        // LetPattern{body:Some}) get their own ScopeIds inside `walk`.
        // Non-scope-bearing bodies leave `body.scope_id == None`; the
        // fn-level scope already covers them.
        walk(&mut decl.body, &mut gen);
    }
}

fn walk(expr: &mut TypedExpr, gen: &mut ScopeIdGen) {
    match &mut expr.kind {
        TypedExprKind::Let { value, body, .. } => {
            walk(value, gen);
            if let Some(body) = body {
                expr.scope_id = Some(gen.fresh());
                walk(body, gen);
            }
        }
        TypedExprKind::LetPattern {
            value,
            body,
            pattern,
        } => {
            walk(value, gen);
            walk_pattern(pattern, gen);
            if let Some(body) = body {
                expr.scope_id = Some(gen.fresh());
                walk(body, gen);
            }
        }
        TypedExprKind::Do(exprs) => {
            expr.scope_id = Some(gen.fresh());
            for e in exprs {
                walk(e, gen);
            }
        }
        TypedExprKind::Lambda { body, .. } => {
            // The lambda body is an independent scope.
            body.scope_id = Some(gen.fresh());
            walk(body, gen);
        }
        TypedExprKind::App { func, args } => {
            walk(func, gen);
            for a in args {
                walk(a, gen);
            }
        }
        TypedExprKind::TypeApp { expr: inner, .. } => walk(inner, gen),
        TypedExprKind::If { cond, then_, else_ } => {
            walk(cond, gen);
            walk(then_, gen);
            walk(else_, gen);
        }
        TypedExprKind::Match { scrutinee, arms } => {
            walk(scrutinee, gen);
            for arm in arms.iter_mut() {
                let TypedMatchArm {
                    guard,
                    body,
                    pattern,
                } = arm;
                walk_pattern(pattern, gen);
                if let Some(g) = guard {
                    walk(g, gen);
                }
                walk(body, gen);
            }
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            walk(lhs, gen);
            walk(rhs, gen);
        }
        TypedExprKind::UnaryOp { operand, .. } => walk(operand, gen),
        TypedExprKind::FieldAccess { expr: inner, .. } => walk(inner, gen),
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields {
                walk(e, gen);
            }
        }
        TypedExprKind::StructUpdate { base, fields } => {
            walk(base, gen);
            for (_, e) in fields {
                walk(e, gen);
            }
        }
        TypedExprKind::Recur(args) | TypedExprKind::Tuple(args) | TypedExprKind::VecLit(args) => {
            for a in args {
                walk(a, gen);
            }
        }
        TypedExprKind::QuestionMark { expr: inner, .. } => walk(inner, gen),
        TypedExprKind::Var(_) | TypedExprKind::Lit(_) => {}
    }
}

fn walk_pattern(_pattern: &mut TypedPattern, _gen: &mut ScopeIdGen) {
    // Patterns themselves contain no scope-bearing sub-expressions in the
    // current typed AST; guard/body are handled at the match-arm level.
}
