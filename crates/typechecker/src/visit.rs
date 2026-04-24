//! `TypedExprVisitor`: a rustc-style immutable walker over `TypedExpr` trees.
//!
//! Every consumer of `TypedExpr` that needs recursive descent should
//! `impl TypedExprVisitor`, override the variants it cares about, and leave the
//! rest to the defaults — which delegate to the free `walk_*` functions below
//! so descent happens uniformly. Adding a new `TypedExprKind` variant becomes a
//! one-location edit (the variant itself plus the exhaustive match in
//! `walk_expr`); all visitors continue to compile and acknowledge the new
//! variant through their default `visit_*` method.
//!
//! The associated [`VisitorResult`] type lets visitors pick between:
//!   - `type Result = ()` for infallible walkers that accumulate state in
//!     `self` (see `AutoCloseAnalyzer`).
//!   - `type Result = Result<(), E>` for early-exit walkers that short-circuit
//!     on the first error (see `OwnershipChecker`) or carry a found value in
//!     the `Err` arm (see `find_first_recur_span`).

use std::ops::ControlFlow;

use krypton_parser::ast::{BinOp, Lit, UnaryOp};

use crate::typed_ast::{
    DeferredId, ResolvedTypeRef, TypedExpr, TypedExprKind, TypedMatchArm, TypedPattern,
};
use crate::types::{ParamMode, SchemeVarId, Type};

/// Visitor return-type trait. Implemented for `()` (infallible) and
/// `Result<(), E>` (early-exit). The `branch` method drives the `try_visit!`
/// macro: it returns `ControlFlow::Break(r)` when the walker should stop
/// descending and propagate `r`, or `ControlFlow::Continue(())` to keep going.
pub trait VisitorResult {
    fn output() -> Self;
    fn from_branch(c: ControlFlow<Self>) -> Self
    where
        Self: Sized;
    fn branch(self) -> ControlFlow<Self>
    where
        Self: Sized;
}

impl VisitorResult for () {
    fn output() -> Self {}
    fn from_branch(_: ControlFlow<Self>) -> Self {}
    fn branch(self) -> ControlFlow<Self> {
        ControlFlow::Continue(())
    }
}

impl<E> VisitorResult for Result<(), E> {
    fn output() -> Self {
        Ok(())
    }
    fn from_branch(c: ControlFlow<Self>) -> Self {
        match c {
            ControlFlow::Break(r) => r,
            ControlFlow::Continue(()) => Ok(()),
        }
    }
    fn branch(self) -> ControlFlow<Self> {
        match self {
            Ok(()) => ControlFlow::Continue(()),
            Err(_) => ControlFlow::Break(self),
        }
    }
}

/// Run a visitor call and early-exit the enclosing `walk_*` if the result
/// signals `Break`. Usable only from functions whose return type is
/// `V::Result` (or any `Self::Result: VisitorResult`).
macro_rules! try_visit {
    ($e:expr) => {
        match $crate::visit::VisitorResult::branch($e) {
            ::std::ops::ControlFlow::Break(r) => return r,
            ::std::ops::ControlFlow::Continue(()) => {}
        }
    };
}

/// Immutable walker over `TypedExpr`. Override the variants you care about;
/// leave the rest to the defaults, which delegate to the free `walk_*`
/// functions below.
#[allow(clippy::too_many_arguments)]
pub trait TypedExprVisitor {
    type Result: VisitorResult;

    fn visit_expr(&mut self, expr: &TypedExpr) -> Self::Result {
        walk_expr(self, expr)
    }

    fn visit_lit(&mut self, _lit: &Lit) -> Self::Result {
        Self::Result::output()
    }

    fn visit_var(&mut self, _name: &str, _expr: &TypedExpr) -> Self::Result {
        Self::Result::output()
    }

    fn visit_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        _param_modes: &[ParamMode],
        _deferred_id: Option<DeferredId>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_app(self, func, args)
    }

    fn visit_type_app(
        &mut self,
        inner: &TypedExpr,
        _type_bindings: &[(SchemeVarId, Type)],
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_type_app(self, inner)
    }

    fn visit_if(
        &mut self,
        cond: &TypedExpr,
        then_: &TypedExpr,
        else_: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_if(self, cond, then_, else_)
    }

    fn visit_let(
        &mut self,
        _name: &str,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_let(self, value, body)
    }

    fn visit_do(&mut self, exprs: &[TypedExpr], _expr: &TypedExpr) -> Self::Result {
        walk_do(self, exprs)
    }

    fn visit_match(
        &mut self,
        scrutinee: &TypedExpr,
        arms: &[TypedMatchArm],
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_match(self, scrutinee, arms)
    }

    fn visit_match_arm(&mut self, arm: &TypedMatchArm) -> Self::Result {
        walk_match_arm(self, arm)
    }

    fn visit_lambda(
        &mut self,
        _params: &[String],
        body: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_lambda(self, body)
    }

    fn visit_field_access(
        &mut self,
        inner: &TypedExpr,
        _field: &str,
        _resolved_type_ref: Option<&ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_field_access(self, inner)
    }

    fn visit_recur(
        &mut self,
        args: &[TypedExpr],
        _param_modes: &[ParamMode],
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_recur(self, args)
    }

    fn visit_tuple(&mut self, elements: &[TypedExpr], _expr: &TypedExpr) -> Self::Result {
        walk_tuple(self, elements)
    }

    fn visit_binary_op(
        &mut self,
        _op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_binary_op(self, lhs, rhs)
    }

    fn visit_unary_op(
        &mut self,
        _op: &UnaryOp,
        operand: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_unary_op(self, operand)
    }

    fn visit_struct_lit(
        &mut self,
        _name: &str,
        fields: &[(String, TypedExpr)],
        _resolved_type_ref: Option<&ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_struct_lit(self, fields)
    }

    fn visit_struct_update(
        &mut self,
        base: &TypedExpr,
        fields: &[(String, TypedExpr)],
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_struct_update(self, base, fields)
    }

    fn visit_let_pattern(
        &mut self,
        _pattern: &TypedPattern,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_let_pattern(self, value, body)
    }

    fn visit_question_mark(
        &mut self,
        inner: &TypedExpr,
        _is_option: bool,
        _expr: &TypedExpr,
    ) -> Self::Result {
        walk_question_mark(self, inner)
    }

    fn visit_vec_lit(&mut self, elements: &[TypedExpr], _expr: &TypedExpr) -> Self::Result {
        walk_vec_lit(self, elements)
    }

    fn visit_discharge(&mut self, inner: &TypedExpr, _expr: &TypedExpr) -> Self::Result {
        walk_discharge(self, inner)
    }
}

// ── walk_* free functions ─────────────────────────────────────────────────
//
// Each `walk_*` performs the default pre-order descent for one variant. It
// calls `visit_expr` on each child through `try_visit!` so early-exit
// propagates. The exhaustive match lives in `walk_expr`.

pub fn walk_expr<V: TypedExprVisitor + ?Sized>(v: &mut V, expr: &TypedExpr) -> V::Result {
    match &expr.kind {
        TypedExprKind::Lit(lit) => v.visit_lit(lit),
        TypedExprKind::Var(name) => v.visit_var(name, expr),
        TypedExprKind::App {
            func,
            args,
            param_modes,
            deferred_id,
        } => v.visit_app(func, args, param_modes, *deferred_id, expr),
        TypedExprKind::TypeApp {
            expr: inner,
            type_bindings,
        } => v.visit_type_app(inner, type_bindings, expr),
        TypedExprKind::If { cond, then_, else_ } => v.visit_if(cond, then_, else_, expr),
        TypedExprKind::Let { name, value, body } => v.visit_let(name, value, body.as_deref(), expr),
        TypedExprKind::Do(exprs) => v.visit_do(exprs, expr),
        TypedExprKind::Match { scrutinee, arms } => v.visit_match(scrutinee, arms, expr),
        TypedExprKind::Lambda { params, body } => v.visit_lambda(params, body, expr),
        TypedExprKind::FieldAccess {
            expr: inner,
            field,
            resolved_type_ref,
        } => v.visit_field_access(inner, field, resolved_type_ref.as_ref(), expr),
        TypedExprKind::Recur { args, param_modes } => v.visit_recur(args, param_modes, expr),
        TypedExprKind::Tuple(elements) => v.visit_tuple(elements, expr),
        TypedExprKind::BinaryOp { op, lhs, rhs } => v.visit_binary_op(op, lhs, rhs, expr),
        TypedExprKind::UnaryOp { op, operand } => v.visit_unary_op(op, operand, expr),
        TypedExprKind::StructLit {
            name,
            fields,
            resolved_type_ref,
        } => v.visit_struct_lit(name, fields, resolved_type_ref.as_ref(), expr),
        TypedExprKind::StructUpdate { base, fields } => v.visit_struct_update(base, fields, expr),
        TypedExprKind::LetPattern {
            pattern,
            value,
            body,
        } => v.visit_let_pattern(pattern, value, body.as_deref(), expr),
        TypedExprKind::QuestionMark {
            expr: inner,
            is_option,
        } => v.visit_question_mark(inner, *is_option, expr),
        TypedExprKind::VecLit(elements) => v.visit_vec_lit(elements, expr),
        TypedExprKind::Discharge(inner) => v.visit_discharge(inner, expr),
    }
}

pub fn walk_app<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    func: &TypedExpr,
    args: &[TypedExpr],
) -> V::Result {
    try_visit!(v.visit_expr(func));
    for a in args {
        try_visit!(v.visit_expr(a));
    }
    V::Result::output()
}

pub fn walk_type_app<V: TypedExprVisitor + ?Sized>(v: &mut V, inner: &TypedExpr) -> V::Result {
    v.visit_expr(inner)
}

pub fn walk_if<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    cond: &TypedExpr,
    then_: &TypedExpr,
    else_: &TypedExpr,
) -> V::Result {
    try_visit!(v.visit_expr(cond));
    try_visit!(v.visit_expr(then_));
    v.visit_expr(else_)
}

pub fn walk_let<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    value: &TypedExpr,
    body: Option<&TypedExpr>,
) -> V::Result {
    try_visit!(v.visit_expr(value));
    if let Some(body) = body {
        return v.visit_expr(body);
    }
    V::Result::output()
}

pub fn walk_do<V: TypedExprVisitor + ?Sized>(v: &mut V, exprs: &[TypedExpr]) -> V::Result {
    for e in exprs {
        try_visit!(v.visit_expr(e));
    }
    V::Result::output()
}

pub fn walk_match<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    scrutinee: &TypedExpr,
    arms: &[TypedMatchArm],
) -> V::Result {
    try_visit!(v.visit_expr(scrutinee));
    for arm in arms {
        try_visit!(v.visit_match_arm(arm));
    }
    V::Result::output()
}

pub fn walk_match_arm<V: TypedExprVisitor + ?Sized>(v: &mut V, arm: &TypedMatchArm) -> V::Result {
    if let Some(guard) = &arm.guard {
        try_visit!(v.visit_expr(guard));
    }
    v.visit_expr(&arm.body)
}

pub fn walk_lambda<V: TypedExprVisitor + ?Sized>(v: &mut V, body: &TypedExpr) -> V::Result {
    v.visit_expr(body)
}

pub fn walk_field_access<V: TypedExprVisitor + ?Sized>(v: &mut V, inner: &TypedExpr) -> V::Result {
    v.visit_expr(inner)
}

pub fn walk_recur<V: TypedExprVisitor + ?Sized>(v: &mut V, args: &[TypedExpr]) -> V::Result {
    for a in args {
        try_visit!(v.visit_expr(a));
    }
    V::Result::output()
}

pub fn walk_tuple<V: TypedExprVisitor + ?Sized>(v: &mut V, elements: &[TypedExpr]) -> V::Result {
    for e in elements {
        try_visit!(v.visit_expr(e));
    }
    V::Result::output()
}

pub fn walk_binary_op<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    lhs: &TypedExpr,
    rhs: &TypedExpr,
) -> V::Result {
    try_visit!(v.visit_expr(lhs));
    v.visit_expr(rhs)
}

pub fn walk_unary_op<V: TypedExprVisitor + ?Sized>(v: &mut V, operand: &TypedExpr) -> V::Result {
    v.visit_expr(operand)
}

pub fn walk_struct_lit<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    fields: &[(String, TypedExpr)],
) -> V::Result {
    for (_, e) in fields {
        try_visit!(v.visit_expr(e));
    }
    V::Result::output()
}

pub fn walk_struct_update<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    base: &TypedExpr,
    fields: &[(String, TypedExpr)],
) -> V::Result {
    try_visit!(v.visit_expr(base));
    for (_, e) in fields {
        try_visit!(v.visit_expr(e));
    }
    V::Result::output()
}

pub fn walk_let_pattern<V: TypedExprVisitor + ?Sized>(
    v: &mut V,
    value: &TypedExpr,
    body: Option<&TypedExpr>,
) -> V::Result {
    try_visit!(v.visit_expr(value));
    if let Some(body) = body {
        return v.visit_expr(body);
    }
    V::Result::output()
}

pub fn walk_question_mark<V: TypedExprVisitor + ?Sized>(v: &mut V, inner: &TypedExpr) -> V::Result {
    v.visit_expr(inner)
}

pub fn walk_vec_lit<V: TypedExprVisitor + ?Sized>(v: &mut V, elements: &[TypedExpr]) -> V::Result {
    for e in elements {
        try_visit!(v.visit_expr(e));
    }
    V::Result::output()
}

pub fn walk_discharge<V: TypedExprVisitor + ?Sized>(v: &mut V, inner: &TypedExpr) -> V::Result {
    v.visit_expr(inner)
}
