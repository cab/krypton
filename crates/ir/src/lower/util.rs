// Pure helper functions used across the lowering pipeline. These do not touch
// `LowerCtx` and have no shared mutable state, so they live as free `fn` items
// here, separate from the impl-block files. Includes pattern-matrix helpers,
// free-variable analysis on `TypedExpr`, expression-kind detection, IR-side
// referenced-var collection, expression constructors, and tuple-arity
// collection on lowered IR.

use rustc_hash::FxHashSet;
use std::rc::Rc;

use krypton_parser::ast::{Lit, Span};
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedMatchArm, TypedPattern};
use krypton_typechecker::types::{Type, TypeVarId};

use super::ctx::Clause;
use crate::Type as IrType;
use crate::{Atom, Expr, ExprKind, SimpleExpr, SimpleExprKind, VarId};

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
// Tuple arity collection (on lowered IR)
// ---------------------------------------------------------------------------

pub(super) fn collect_tuple_arities_from_fn(
    func: &crate::FnDef,
    arities: &mut std::collections::BTreeSet<usize>,
) {
    for (_, ty) in &func.params {
        collect_tuple_arities_from_type(ty, arities);
    }
    collect_tuple_arities_from_type(&func.return_type, arities);
    collect_tuple_arities_from_expr(&func.body, arities);
}

pub(super) fn collect_tuple_arities_from_type(
    ty: &IrType,
    arities: &mut std::collections::BTreeSet<usize>,
) {
    match ty {
        IrType::Tuple(elems) => {
            arities.insert(elems.len());
            for e in elems {
                collect_tuple_arities_from_type(e, arities);
            }
        }
        IrType::Fn(params, ret) => {
            for p in params {
                collect_tuple_arities_from_type(p, arities);
            }
            collect_tuple_arities_from_type(ret, arities);
        }
        IrType::Named(_, args) => {
            for a in args {
                collect_tuple_arities_from_type(a, arities);
            }
        }
        IrType::Own(inner) => collect_tuple_arities_from_type(inner, arities),
        IrType::Dict { target_types, .. } => {
            for t in target_types {
                collect_tuple_arities_from_type(t, arities);
            }
        }
        _ => {}
    }
}

pub(super) fn collect_tuple_arities_from_expr(
    expr: &Expr,
    arities: &mut std::collections::BTreeSet<usize>,
) {
    collect_tuple_arities_from_type(&expr.ty, arities);
    match &expr.kind {
        ExprKind::Let {
            ty, value, body, ..
        } => {
            collect_tuple_arities_from_type(ty, arities);
            collect_tuple_arities_from_simple(value, arities);
            collect_tuple_arities_from_expr(body, arities);
        }
        ExprKind::LetRec { bindings, body } => {
            for (_, ty, _, _) in bindings {
                collect_tuple_arities_from_type(ty, arities);
            }
            collect_tuple_arities_from_expr(body, arities);
        }
        ExprKind::LetJoin {
            params,
            join_body,
            body,
            ..
        } => {
            for (_, ty) in params {
                collect_tuple_arities_from_type(ty, arities);
            }
            collect_tuple_arities_from_expr(join_body, arities);
            collect_tuple_arities_from_expr(body, arities);
        }
        ExprKind::BoolSwitch {
            true_body,
            false_body,
            ..
        } => {
            collect_tuple_arities_from_expr(true_body, arities);
            collect_tuple_arities_from_expr(false_body, arities);
        }
        ExprKind::Switch {
            branches, default, ..
        } => {
            for branch in branches {
                for (_, ty) in &branch.bindings {
                    collect_tuple_arities_from_type(ty, arities);
                }
                collect_tuple_arities_from_expr(&branch.body, arities);
            }
            if let Some(d) = default {
                collect_tuple_arities_from_expr(d, arities);
            }
        }
        ExprKind::AutoClose { body, .. } => {
            collect_tuple_arities_from_expr(body, arities);
        }
        ExprKind::Jump { .. } | ExprKind::Atom(_) => {}
    }
}

pub(super) fn collect_tuple_arities_from_simple(
    expr: &SimpleExpr,
    arities: &mut std::collections::BTreeSet<usize>,
) {
    match &expr.kind {
        SimpleExprKind::MakeTuple { elements } => {
            arities.insert(elements.len());
        }
        SimpleExprKind::MakeVec { element_type, .. } => {
            collect_tuple_arities_from_type(element_type, arities);
        }
        _ => {}
    }
}
