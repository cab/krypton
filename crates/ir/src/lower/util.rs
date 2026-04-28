// Pure helper functions used across the lowering pipeline. These do not touch
// `LowerCtx` and have no shared mutable state, so they live as free `fn` items
// here, separate from the impl-block files. Includes pattern-matrix helpers,
// free-variable analysis on `TypedExpr`, expression-kind detection, IR-side
// referenced-var collection, expression constructors, and instance-target
// type binding.

use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

use krypton_parser::ast::{Lit, Span};
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedMatchArm, TypedPattern};
use krypton_typechecker::types::{self as types, Type, TypeVarId};

use super::ctx::Clause;
use super::LowerError;
use crate::Type as IrType;
use crate::{Atom, Expr, ExprKind, SimpleExpr, SimpleExprKind, SwitchBranch, VarId};

/// Check if a pattern is a wildcard or variable (always matches).
pub(super) fn is_wildcard_or_var(pat: &TypedPattern) -> bool {
    matches!(
        pat,
        TypedPattern::Wildcard { .. }
            | TypedPattern::Var { .. }
            | TypedPattern::Lit {
                value: Lit::Unit,
                ..
            }
    )
}

/// Flatten or-patterns in a specific column, expanding each clause with an Or pattern
/// into multiple clauses (one per alternative). All other columns are preserved.
pub(super) fn flatten_or_at_column(clauses: Vec<Clause>, col: usize) -> Vec<Clause> {
    let mut result = Vec::new();
    for clause in clauses {
        if col < clause.patterns.len() {
            if let TypedPattern::Or { alternatives, .. } = &clause.patterns[col] {
                for alt in alternatives {
                    let mut new_pats = clause.patterns.clone();
                    new_pats[col] = alt.clone();
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                continue;
            }
        }
        result.push(clause);
    }
    result
}

/// Get the type annotation from a pattern.
pub(super) fn pattern_type(pat: &TypedPattern) -> Type {
    match pat {
        TypedPattern::Wildcard { ty, .. }
        | TypedPattern::Var { ty, .. }
        | TypedPattern::Constructor { ty, .. }
        | TypedPattern::Lit { ty, .. }
        | TypedPattern::Tuple { ty, .. }
        | TypedPattern::Or { ty, .. }
        | TypedPattern::StructPat { ty, .. } => ty.clone(),
    }
}

// ---------------------------------------------------------------------------
// Free variable analysis (on TypedExpr, before IR lowering)
// ---------------------------------------------------------------------------

/// Walk a TypedExpr tree and collect variable names that are referenced but not
/// bound locally (by Let, Lambda, or LetPattern). Returns deduplicated names in
/// stable (first-seen) order.
pub(super) fn free_vars(expr: &TypedExpr, bound: &FxHashSet<String>) -> Vec<String> {
    let mut free = Vec::new();
    let mut seen = FxHashSet::default();
    free_vars_inner(expr, bound, &mut free, &mut seen);
    free
}

fn free_vars_inner(
    expr: &TypedExpr,
    bound: &FxHashSet<String>,
    free: &mut Vec<String>,
    seen: &mut FxHashSet<String>,
) {
    match &expr.kind {
        TypedExprKind::Lit(_) => {}
        TypedExprKind::Var(name) => {
            if !bound.contains(name) && seen.insert(name.clone()) {
                free.push(name.clone());
            }
        }
        TypedExprKind::App { func, args, .. } => {
            free_vars_inner(func, bound, free, seen);
            for a in args {
                free_vars_inner(a, bound, free, seen);
            }
        }
        TypedExprKind::TypeApp { expr: inner, .. } => {
            free_vars_inner(inner, bound, free, seen);
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            free_vars_inner(lhs, bound, free, seen);
            free_vars_inner(rhs, bound, free, seen);
        }
        TypedExprKind::UnaryOp { operand, .. } => {
            free_vars_inner(operand, bound, free, seen);
        }
        TypedExprKind::If { cond, then_, else_ } => {
            free_vars_inner(cond, bound, free, seen);
            free_vars_inner(then_, bound, free, seen);
            free_vars_inner(else_, bound, free, seen);
        }
        TypedExprKind::Let {
            name, value, body, ..
        } => {
            free_vars_inner(value, bound, free, seen);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                free_vars_inner(body, &inner_bound, free, seen);
            }
        }
        TypedExprKind::Do(exprs) => {
            let mut do_bound = bound.clone();
            for e in exprs {
                free_vars_inner(e, &do_bound, free, seen);
                // Let with no body introduces a binding for subsequent exprs
                if let TypedExprKind::Let {
                    name, body: None, ..
                } = &e.kind
                {
                    do_bound.insert(name.clone());
                }
            }
        }
        TypedExprKind::Lambda { params, body } => {
            let mut inner_bound = bound.clone();
            for p in params {
                inner_bound.insert(p.clone());
            }
            free_vars_inner(body, &inner_bound, free, seen);
        }
        TypedExprKind::Match { scrutinee, arms } => {
            free_vars_inner(scrutinee, bound, free, seen);
            for arm in arms {
                let mut inner_bound = bound.clone();
                collect_pattern_bindings(&arm.pattern, &mut inner_bound);
                if let Some(guard) = &arm.guard {
                    free_vars_inner(guard, &inner_bound, free, seen);
                }
                free_vars_inner(&arm.body, &inner_bound, free, seen);
            }
        }
        TypedExprKind::FieldAccess { expr: inner, .. } => {
            free_vars_inner(inner, bound, free, seen);
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, fexpr) in fields {
                free_vars_inner(fexpr, bound, free, seen);
            }
        }
        TypedExprKind::StructUpdate { base, fields } => {
            free_vars_inner(base, bound, free, seen);
            for (_, fexpr) in fields {
                free_vars_inner(fexpr, bound, free, seen);
            }
        }
        TypedExprKind::Tuple(elems) | TypedExprKind::VecLit(elems) => {
            for e in elems {
                free_vars_inner(e, bound, free, seen);
            }
        }
        TypedExprKind::Recur { args, .. } => {
            for a in args {
                free_vars_inner(a, bound, free, seen);
            }
        }
        TypedExprKind::QuestionMark { expr: inner, .. } => {
            free_vars_inner(inner, bound, free, seen);
        }
        TypedExprKind::Discharge(inner) => {
            free_vars_inner(inner, bound, free, seen);
        }
        TypedExprKind::LetPattern {
            pattern,
            value,
            body,
            ..
        } => {
            free_vars_inner(value, bound, free, seen);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                collect_pattern_bindings(pattern, &mut inner_bound);
                free_vars_inner(body, &inner_bound, free, seen);
            }
        }
    }
}

/// Collect all variable names bound by a pattern.
pub(super) fn collect_pattern_bindings(
    pattern: &krypton_typechecker::typed_ast::TypedPattern,
    bound: &mut FxHashSet<String>,
) {
    use krypton_typechecker::typed_ast::TypedPattern;
    match pattern {
        TypedPattern::Var { name, .. } => {
            bound.insert(name.clone());
        }
        TypedPattern::Constructor { args, .. } => {
            for p in args {
                collect_pattern_bindings(p, bound);
            }
        }
        TypedPattern::Tuple { elements, .. } => {
            for p in elements {
                collect_pattern_bindings(p, bound);
            }
        }
        TypedPattern::StructPat { fields, .. } => {
            for (_, p) in fields {
                collect_pattern_bindings(p, bound);
            }
        }
        TypedPattern::Wildcard { .. } | TypedPattern::Lit { .. } => {}
        TypedPattern::Or { alternatives, .. } => {
            if let Some(first) = alternatives.first() {
                collect_pattern_bindings(first, bound);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Expression-kind detection (on TypedExpr, before IR lowering)
// ---------------------------------------------------------------------------

/// Walk a TypedExpr tree and return true if any node matches the predicate.
/// Lambdas and match-arm guards are not crossed (preserves the pre-visitor
/// semantic of the original recursive walker).
fn contains_expr_kind(expr: &TypedExpr, pred: &dyn Fn(&TypedExprKind) -> bool) -> bool {
    use krypton_typechecker::visit::TypedExprVisitor;
    let mut v = ExprKindContains { pred };
    v.visit_expr(expr).is_err()
}

struct ExprKindContains<'a> {
    pred: &'a dyn Fn(&TypedExprKind) -> bool,
}

impl<'a> krypton_typechecker::visit::TypedExprVisitor for ExprKindContains<'a> {
    type Result = Result<(), ()>;

    fn visit_expr(&mut self, expr: &TypedExpr) -> Self::Result {
        if (self.pred)(&expr.kind) {
            return Err(());
        }
        krypton_typechecker::visit::walk_expr(self, expr)
    }

    /// Lambdas rebind `recur` and shadow `?` semantics inside their body, so
    /// the original walker stopped here. Skip the body to preserve that.
    fn visit_lambda(
        &mut self,
        _params: &[String],
        _body: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        Ok(())
    }

    /// Original walker only descended into match-arm bodies, never guards.
    fn visit_match_arm(&mut self, arm: &TypedMatchArm) -> Self::Result {
        self.visit_expr(&arm.body)
    }
}

pub(super) fn contains_recur(expr: &TypedExpr) -> bool {
    contains_expr_kind(expr, &|kind| matches!(kind, TypedExprKind::Recur { .. }))
}

pub(super) fn contains_question_mark(expr: &TypedExpr) -> bool {
    contains_expr_kind(expr, &|kind| {
        matches!(kind, TypedExprKind::QuestionMark { .. })
    })
}

// ---------------------------------------------------------------------------
// Referenced-var collection (on lowered IR Expr)
// ---------------------------------------------------------------------------

/// Collect all VarIds referenced in an IR expression tree.
pub(super) fn referenced_vars_in_expr(expr: &Expr) -> FxHashSet<VarId> {
    use crate::visit::ExprVisitor;
    let mut vars = FxHashSet::default();
    let mut collector = RefVarCollector { vars: &mut vars };
    collector.visit_expr(expr);
    vars
}

/// Visitor-based replacement for the old `referenced_vars_{walk,simple,atom}`
/// trio. Atoms are the bottom-line: every variant eventually descends to a
/// `visit_atom` call. `AutoClose`'s `resource` is a binder-level reference
/// consumed by the close, so the override inserts it before delegating to
/// `walk_auto_close`.
struct RefVarCollector<'a> {
    vars: &'a mut FxHashSet<VarId>,
}

impl<'a> crate::visit::SimpleExprVisitor for RefVarCollector<'a> {
    type Result = ();

    fn visit_atom(&mut self, atom: &Atom) {
        if let Atom::Var(id) = atom {
            self.vars.insert(*id);
        }
    }
}

impl<'a> crate::visit::ExprVisitor for RefVarCollector<'a> {
    fn visit_auto_close(
        &mut self,
        resource: VarId,
        dict: &Atom,
        _type_name: &str,
        _null_slot: bool,
        body: &Expr,
        _expr: &Expr,
    ) {
        self.vars.insert(resource);
        crate::visit::walk_auto_close(self, dict, body);
    }
}

// ---------------------------------------------------------------------------
// Expression constructors
// ---------------------------------------------------------------------------

pub(super) fn expr_at(span: Span, ty: IrType, kind: ExprKind) -> Expr {
    Expr::new(span, ty, kind)
}

pub(super) fn atom_expr_at(span: Span, ty: IrType, atom: Atom) -> Expr {
    Expr::new(span, ty, ExprKind::Atom(atom))
}

pub(super) fn simple_at(span: Span, kind: SimpleExprKind) -> SimpleExpr {
    SimpleExpr::new(span, kind)
}

/// Thin alias over the public substitution helper, kept local for the
/// hot path and to match the surrounding call sites' naming.
pub(super) fn substitute_ir_type(ty: &IrType, params: &[TypeVarId], args: &[IrType]) -> IrType {
    crate::substitute_type_vars(ty, params, args)
}

// ---------------------------------------------------------------------------
// Tail-position rewriting
// ---------------------------------------------------------------------------

/// Replace tail positions of an expression with `jump target(tail_value)`.
pub(super) fn replace_tail_with_jump(expr: Expr, target: VarId) -> Expr {
    let span = expr.span;
    let result_ty = expr.ty.clone();
    match expr.kind {
        ExprKind::Atom(atom) => expr_at(
            span,
            result_ty,
            ExprKind::Jump {
                target,
                args: vec![atom],
            },
        ),
        ExprKind::Let {
            bind,
            ty,
            value,
            body,
        } => {
            let new_body = replace_tail_with_jump(*body, target);
            expr_at(
                span,
                result_ty,
                ExprKind::Let {
                    bind,
                    ty,
                    value,
                    body: Box::new(new_body),
                },
            )
        }
        ExprKind::BoolSwitch {
            scrutinee,
            true_body,
            false_body,
        } => expr_at(
            span,
            result_ty,
            ExprKind::BoolSwitch {
                scrutinee,
                true_body: Box::new(replace_tail_with_jump(*true_body, target)),
                false_body: Box::new(replace_tail_with_jump(*false_body, target)),
            },
        ),
        ExprKind::Switch {
            scrutinee,
            branches,
            default,
        } => {
            let new_branches: Vec<_> = branches
                .into_iter()
                .map(|b| SwitchBranch {
                    tag: b.tag,
                    bindings: b.bindings,
                    body: replace_tail_with_jump(b.body, target),
                })
                .collect();
            let new_default = default.map(|d| Box::new(replace_tail_with_jump(*d, target)));
            expr_at(
                span,
                result_ty,
                ExprKind::Switch {
                    scrutinee,
                    branches: new_branches,
                    default: new_default,
                },
            )
        }
        ExprKind::LetJoin {
            name,
            params,
            join_body,
            body: join_scope,
            is_recur,
        } => {
            let new_join_body = replace_tail_with_jump(*join_body, target);
            let new_scope = replace_tail_with_jump(*join_scope, target);
            expr_at(
                span,
                result_ty,
                ExprKind::LetJoin {
                    name,
                    params,
                    join_body: Box::new(new_join_body),
                    body: Box::new(new_scope),
                    is_recur,
                },
            )
        }
        ExprKind::AutoClose {
            resource,
            dict,
            type_name,
            null_slot,
            body,
        } => {
            // Recurse into the AutoClose body: the tail atom inside is the
            // real producer of the enclosing compound value. The close call
            // itself is not a tail position.
            let new_body = replace_tail_with_jump(*body, target);
            expr_at(
                span,
                result_ty,
                ExprKind::AutoClose {
                    resource,
                    dict,
                    type_name,
                    null_slot,
                    body: Box::new(new_body),
                },
            )
        }
        // Jump and LetRec shouldn't appear as compound value tails
        _ => expr,
    }
}

// ---------------------------------------------------------------------------
// Type-var binding (instance dispatch + dict resolution)
// ---------------------------------------------------------------------------

/// Wrap a [`crate::BindConflict`] as a [`LowerError::InternalError`] carrying
/// the offending variable, its pre-existing binding, and the binding the
/// current match would have introduced. Used by `resolve_call_dicts`,
/// `resolve_dispatch_type_with_bindings`, and `lower_constrained_fn_as_value`
/// to turn typechecker-authorized pin conflicts into loud ICEs.
pub(super) fn ice_bind_conflict(where_: &str, bc: crate::BindConflict<Type>) -> LowerError {
    LowerError::InternalError(format!(
        "ICE: bind conflict in {}: var {:?} pinned to {:?} but pattern would bind it to {:?}",
        where_, bc.var, bc.existing, bc.proposed,
    ))
}

/// Match a type pattern against a concrete type to bind type variables.
/// Ported from codegen's `bind_type_vars` (calls.rs).
///
/// * `Ok(true)` — bindings extended (or already consistent); pattern matches.
/// * `Ok(false)` — structural mismatch.
/// * `Err(BindConflict)` — existing binding disagrees with what this match
///   would assign.
pub(super) fn bind_type_vars(
    pattern: &Type,
    actual: &Type,
    bindings: &mut FxHashMap<TypeVarId, Type>,
) -> Result<bool, crate::BindConflict<Type>> {
    match (pattern, actual) {
        (Type::Var(id), _) => match bindings.get(id) {
            Some(existing) => {
                if existing == actual {
                    Ok(true)
                } else {
                    Err(crate::BindConflict {
                        var: *id,
                        existing: Box::new(existing.clone()),
                        proposed: Box::new(actual.clone()),
                    })
                }
            }
            None => {
                bindings.insert(*id, actual.clone());
                Ok(true)
            }
        },
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) => {
            if p_name != a_name || p_args.len() != a_args.len() {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(a_args.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
            if p_params.len() != a_params.len() {
                return Ok(false);
            }
            for ((_, p), (_, a)) in p_params.iter().zip(a_params.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            bind_type_vars(p_ret, a_ret, bindings)
        }
        (Type::Tuple(p_elems), Type::Tuple(a_elems)) => {
            if p_elems.len() != a_elems.len() {
                return Ok(false);
            }
            for (p, a) in p_elems.iter().zip(a_elems.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Type::Own(p), Type::Own(a)) => bind_type_vars(p, a, bindings),
        (Type::Own(p), a) => bind_type_vars(p, a, bindings),
        (a, Type::Own(p)) => bind_type_vars(a, p, bindings),
        (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
            if !bind_type_vars(p_ctor, a_ctor, bindings)? {
                return Ok(false);
            }
            if p_args.len() != a_args.len() {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(a_args.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // HKT cross-arm: App(Var(f), [a]) vs Named("Box", [Int])
        // Partial application: when a_args.len() > p_args.len(), the prefix bakes
        // into the constructor (f = Named("Result", [String]) when pattern is
        // f[a] and actual is Result[String, Int]).
        (Type::App(p_ctor, p_args), Type::Named(a_name, a_args)) => {
            if p_args.len() > a_args.len() {
                return Ok(false);
            }
            let prefix_len = a_args.len() - p_args.len();
            let prefix: Vec<Type> = a_args[..prefix_len].to_vec();
            if !bind_type_vars(p_ctor, &Type::Named(a_name.clone(), prefix), bindings)? {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(a_args[prefix_len..].iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // HKT cross-arm: App(Var(f), [a]) vs Fn([Int], Int)
        (Type::App(p_ctor, p_args), Type::Fn(a_params, a_ret))
            if types::decompose_fn_for_app(a_params, a_ret, p_args.len()).is_some() =>
        {
            let (ctor_fn, remaining) =
                types::decompose_fn_for_app(a_params, a_ret, p_args.len()).unwrap();
            if !bind_type_vars(p_ctor, &ctor_fn, bindings)? {
                return Ok(false);
            }
            if remaining.len() != p_args.len() {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(remaining.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(pattern == actual),
    }
}

/// Match a single instance-target pattern against a dispatch type.
///
/// Instance patterns are stored in full form (e.g. `Map[Var(k), Var(anon)]`);
/// dispatch types may be partial (e.g. `Map[String]`) when HKT method
/// resolution binds the trait's type var to a partial constructor. At the
/// top level of a target type, a pattern with more slots than the actual
/// matches by zipping the prefix — trailing pattern slots stay unbound.
/// Nested types use strict [`bind_type_vars`].
pub(super) fn bind_instance_target(
    pattern: &Type,
    actual: &Type,
    bindings: &mut FxHashMap<TypeVarId, Type>,
) -> bool {
    match (pattern, actual) {
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args))
            if p_args.len() > a_args.len() =>
        {
            if p_name != a_name {
                return false;
            }
            for (p, a) in p_args.iter().take(a_args.len()).zip(a_args.iter()) {
                if !matches!(bind_type_vars(p, a, bindings), Ok(true)) {
                    return false;
                }
            }
            true
        }
        _ => matches!(bind_type_vars(pattern, actual, bindings), Ok(true)),
    }
}

/// Array-level counterpart to [`bind_instance_target`]: zips instance-target
/// tuples with dispatch tuples.
pub(super) fn bind_instance_targets(
    patterns: &[Type],
    dispatch_tys: &[Type],
    bindings: &mut FxHashMap<TypeVarId, Type>,
) -> bool {
    if patterns.len() != dispatch_tys.len() {
        return false;
    }
    patterns
        .iter()
        .zip(dispatch_tys.iter())
        .all(|(p, a)| bind_instance_target(p, a, bindings))
}
