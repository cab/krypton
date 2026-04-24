//! `SimpleExprVisitor` and `ExprVisitor`: rustc-style immutable walkers over
//! IR `SimpleExpr` and `Expr` trees.
//!
//! Two traits, not one — `impl Display for SimpleExpr` formats a bare
//! `SimpleExpr` with no surrounding `Expr`, so `SimpleExprVisitor` is a
//! standalone dispatch point. `ExprVisitor: SimpleExprVisitor` so any
//! `ExprKind::Let { value, .. }` can recurse into its `SimpleExpr` child via
//! `visit_simple_expr`. The single associated `Result` lives on the parent
//! trait; default `ExprVisitor` methods reuse it through the supertrait bound.
//!
//! Each consumer that needs recursive descent should `impl` the appropriate
//! trait(s), override the variants it cares about, and leave the rest to the
//! defaults — which delegate to the free `walk_*` functions below so descent
//! happens uniformly. Adding a new `SimpleExprKind` or `ExprKind` variant
//! becomes a one-location edit (the variant itself plus the exhaustive match
//! in `walk_simple_expr` / `walk_expr`); all visitors continue to compile and
//! acknowledge the new variant through their default `visit_*` method.
//!
//! `VisitorResult` is reused from `krypton_typechecker::visit` — duplicating
//! the `()` / `Result<(), E>` impls would serve no one.

use krypton_typechecker::visit::VisitorResult;

use crate::expr::{Atom, Expr, ExprKind, PrimOp, SimpleExpr, SimpleExprKind, SwitchBranch};
use crate::{CanonicalRef, FnId, TraitName, Type, VarId};

/// Run a visitor call and early-exit the enclosing `walk_*` if the result
/// signals `Break`. Usable only from functions whose return type is
/// `V::Result` (or any `Self::Result: VisitorResult`).
macro_rules! try_visit {
    ($e:expr) => {
        match ::krypton_typechecker::visit::VisitorResult::branch($e) {
            ::std::ops::ControlFlow::Break(r) => return r,
            ::std::ops::ControlFlow::Continue(()) => {}
        }
    };
}

/// Immutable walker over `SimpleExpr`. Override the variants you care about;
/// leave the rest to the defaults, which delegate to the free `walk_*`
/// functions below. Every variant bottom-lines at one or more `Atom`s, so
/// override `visit_atom` for atom-keyed analyses.
#[allow(clippy::too_many_arguments)]
pub trait SimpleExprVisitor {
    type Result: VisitorResult;

    fn visit_simple_expr(&mut self, simple: &SimpleExpr) -> Self::Result {
        walk_simple_expr(self, simple)
    }

    fn visit_atom(&mut self, _atom: &Atom) -> Self::Result {
        Self::Result::output()
    }

    fn visit_call(&mut self, _func: FnId, args: &[Atom], _simple: &SimpleExpr) -> Self::Result {
        walk_call(self, args)
    }

    fn visit_trait_call(
        &mut self,
        _trait_name: &TraitName,
        _method_name: &str,
        args: &[Atom],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_trait_call(self, args)
    }

    fn visit_call_closure(
        &mut self,
        closure: &Atom,
        args: &[Atom],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_call_closure(self, closure, args)
    }

    fn visit_make_closure(
        &mut self,
        _func: FnId,
        captures: &[Atom],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_make_closure(self, captures)
    }

    fn visit_construct(
        &mut self,
        _type_ref: &CanonicalRef,
        fields: &[Atom],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_construct(self, fields)
    }

    fn visit_construct_variant(
        &mut self,
        _type_ref: &CanonicalRef,
        _variant: &str,
        _tag: u32,
        fields: &[Atom],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_construct_variant(self, fields)
    }

    fn visit_project(
        &mut self,
        value: &Atom,
        _field_index: usize,
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_project(self, value)
    }

    fn visit_tag(&mut self, value: &Atom, _simple: &SimpleExpr) -> Self::Result {
        walk_tag(self, value)
    }

    fn visit_make_tuple(&mut self, elements: &[Atom], _simple: &SimpleExpr) -> Self::Result {
        walk_make_tuple(self, elements)
    }

    fn visit_tuple_project(
        &mut self,
        value: &Atom,
        _index: usize,
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_tuple_project(self, value)
    }

    fn visit_prim_op(&mut self, _op: PrimOp, args: &[Atom], _simple: &SimpleExpr) -> Self::Result {
        walk_prim_op(self, args)
    }

    fn visit_get_dict(
        &mut self,
        _instance_ref: &CanonicalRef,
        _trait_name: &TraitName,
        _target_types: &[Type],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        Self::Result::output()
    }

    fn visit_make_dict(
        &mut self,
        _instance_ref: &CanonicalRef,
        _trait_name: &TraitName,
        _target_types: &[Type],
        sub_dicts: &[Atom],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_make_dict(self, sub_dicts)
    }

    fn visit_project_dict_field(
        &mut self,
        dict: &Atom,
        _field_index: usize,
        _result_trait: &TraitName,
        _result_target_types: &[Type],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_project_dict_field(self, dict)
    }

    fn visit_make_vec(
        &mut self,
        _element_type: &Type,
        elements: &[Atom],
        _simple: &SimpleExpr,
    ) -> Self::Result {
        walk_make_vec(self, elements)
    }

    fn visit_simple_atom(&mut self, atom: &Atom, _simple: &SimpleExpr) -> Self::Result {
        self.visit_atom(atom)
    }
}

/// Immutable walker over `Expr`. Inherits its `Result` type and `visit_atom`
/// from `SimpleExprVisitor`, so a consumer that descends through both layers
/// (e.g. `Let { value, .. }`) gets a single coherent result type.
#[allow(clippy::too_many_arguments)]
pub trait ExprVisitor: SimpleExprVisitor {
    fn visit_expr(&mut self, expr: &Expr) -> Self::Result {
        walk_expr(self, expr)
    }

    fn visit_switch_branch(&mut self, branch: &SwitchBranch) -> Self::Result {
        walk_switch_branch(self, branch)
    }

    fn visit_let(
        &mut self,
        _bind: VarId,
        _ty: &Type,
        value: &SimpleExpr,
        body: &Expr,
        _expr: &Expr,
    ) -> Self::Result {
        walk_let(self, value, body)
    }

    fn visit_let_rec(
        &mut self,
        bindings: &[(VarId, Type, FnId, Vec<Atom>)],
        body: &Expr,
        _expr: &Expr,
    ) -> Self::Result {
        walk_let_rec(self, bindings, body)
    }

    fn visit_let_join(
        &mut self,
        _name: VarId,
        _params: &[(VarId, Type)],
        join_body: &Expr,
        body: &Expr,
        _is_recur: bool,
        _expr: &Expr,
    ) -> Self::Result {
        walk_let_join(self, join_body, body)
    }

    fn visit_jump(&mut self, _target: VarId, args: &[Atom], _expr: &Expr) -> Self::Result {
        walk_jump(self, args)
    }

    fn visit_bool_switch(
        &mut self,
        scrutinee: &Atom,
        true_body: &Expr,
        false_body: &Expr,
        _expr: &Expr,
    ) -> Self::Result {
        walk_bool_switch(self, scrutinee, true_body, false_body)
    }

    fn visit_switch(
        &mut self,
        scrutinee: &Atom,
        branches: &[SwitchBranch],
        default: Option<&Expr>,
        _expr: &Expr,
    ) -> Self::Result {
        walk_switch(self, scrutinee, branches, default)
    }

    fn visit_auto_close(
        &mut self,
        _resource: VarId,
        dict: &Atom,
        _type_name: &str,
        _null_slot: bool,
        body: &Expr,
        _expr: &Expr,
    ) -> Self::Result {
        walk_auto_close(self, dict, body)
    }

    fn visit_expr_atom(&mut self, atom: &Atom, _expr: &Expr) -> Self::Result {
        self.visit_atom(atom)
    }
}

// ── walk_* free functions ─────────────────────────────────────────────────
//
// Each `walk_*` performs the default pre-order descent for one variant. It
// calls the appropriate visitor entry point on each child through `try_visit!`
// so early-exit propagates. The exhaustive matches live in `walk_simple_expr`
// and `walk_expr`.

pub fn walk_simple_expr<V: SimpleExprVisitor + ?Sized>(
    v: &mut V,
    simple: &SimpleExpr,
) -> V::Result {
    match &simple.kind {
        SimpleExprKind::Call { func, args } => v.visit_call(*func, args, simple),
        SimpleExprKind::TraitCall {
            trait_name,
            method_name,
            args,
        } => v.visit_trait_call(trait_name, method_name, args, simple),
        SimpleExprKind::CallClosure { closure, args } => {
            v.visit_call_closure(closure, args, simple)
        }
        SimpleExprKind::MakeClosure { func, captures } => {
            v.visit_make_closure(*func, captures, simple)
        }
        SimpleExprKind::Construct { type_ref, fields } => {
            v.visit_construct(type_ref, fields, simple)
        }
        SimpleExprKind::ConstructVariant {
            type_ref,
            variant,
            tag,
            fields,
        } => v.visit_construct_variant(type_ref, variant, *tag, fields, simple),
        SimpleExprKind::Project { value, field_index } => {
            v.visit_project(value, *field_index, simple)
        }
        SimpleExprKind::Tag { value } => v.visit_tag(value, simple),
        SimpleExprKind::MakeTuple { elements } => v.visit_make_tuple(elements, simple),
        SimpleExprKind::TupleProject { value, index } => {
            v.visit_tuple_project(value, *index, simple)
        }
        SimpleExprKind::PrimOp { op, args } => v.visit_prim_op(*op, args, simple),
        SimpleExprKind::GetDict {
            instance_ref,
            trait_name,
            target_types,
        } => v.visit_get_dict(instance_ref, trait_name, target_types, simple),
        SimpleExprKind::MakeDict {
            instance_ref,
            trait_name,
            target_types,
            sub_dicts,
        } => v.visit_make_dict(instance_ref, trait_name, target_types, sub_dicts, simple),
        SimpleExprKind::ProjectDictField {
            dict,
            field_index,
            result_trait,
            result_target_types,
        } => v.visit_project_dict_field(
            dict,
            *field_index,
            result_trait,
            result_target_types,
            simple,
        ),
        SimpleExprKind::MakeVec {
            element_type,
            elements,
        } => v.visit_make_vec(element_type, elements, simple),
        SimpleExprKind::Atom(atom) => v.visit_simple_atom(atom, simple),
    }
}

pub fn walk_call<V: SimpleExprVisitor + ?Sized>(v: &mut V, args: &[Atom]) -> V::Result {
    for a in args {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_trait_call<V: SimpleExprVisitor + ?Sized>(v: &mut V, args: &[Atom]) -> V::Result {
    for a in args {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_call_closure<V: SimpleExprVisitor + ?Sized>(
    v: &mut V,
    closure: &Atom,
    args: &[Atom],
) -> V::Result {
    try_visit!(v.visit_atom(closure));
    for a in args {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_make_closure<V: SimpleExprVisitor + ?Sized>(v: &mut V, captures: &[Atom]) -> V::Result {
    for a in captures {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_construct<V: SimpleExprVisitor + ?Sized>(v: &mut V, fields: &[Atom]) -> V::Result {
    for a in fields {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_construct_variant<V: SimpleExprVisitor + ?Sized>(
    v: &mut V,
    fields: &[Atom],
) -> V::Result {
    for a in fields {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_project<V: SimpleExprVisitor + ?Sized>(v: &mut V, value: &Atom) -> V::Result {
    v.visit_atom(value)
}

pub fn walk_tag<V: SimpleExprVisitor + ?Sized>(v: &mut V, value: &Atom) -> V::Result {
    v.visit_atom(value)
}

pub fn walk_make_tuple<V: SimpleExprVisitor + ?Sized>(v: &mut V, elements: &[Atom]) -> V::Result {
    for a in elements {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_tuple_project<V: SimpleExprVisitor + ?Sized>(v: &mut V, value: &Atom) -> V::Result {
    v.visit_atom(value)
}

pub fn walk_prim_op<V: SimpleExprVisitor + ?Sized>(v: &mut V, args: &[Atom]) -> V::Result {
    for a in args {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_make_dict<V: SimpleExprVisitor + ?Sized>(v: &mut V, sub_dicts: &[Atom]) -> V::Result {
    for a in sub_dicts {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_project_dict_field<V: SimpleExprVisitor + ?Sized>(v: &mut V, dict: &Atom) -> V::Result {
    v.visit_atom(dict)
}

pub fn walk_make_vec<V: SimpleExprVisitor + ?Sized>(v: &mut V, elements: &[Atom]) -> V::Result {
    for a in elements {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_expr<V: ExprVisitor + ?Sized>(v: &mut V, expr: &Expr) -> V::Result {
    match &expr.kind {
        ExprKind::Let {
            bind,
            ty,
            value,
            body,
        } => v.visit_let(*bind, ty, value, body, expr),
        ExprKind::LetRec { bindings, body } => v.visit_let_rec(bindings, body, expr),
        ExprKind::LetJoin {
            name,
            params,
            join_body,
            body,
            is_recur,
        } => v.visit_let_join(*name, params, join_body, body, *is_recur, expr),
        ExprKind::Jump { target, args } => v.visit_jump(*target, args, expr),
        ExprKind::BoolSwitch {
            scrutinee,
            true_body,
            false_body,
        } => v.visit_bool_switch(scrutinee, true_body, false_body, expr),
        ExprKind::Switch {
            scrutinee,
            branches,
            default,
        } => v.visit_switch(scrutinee, branches, default.as_deref(), expr),
        ExprKind::AutoClose {
            resource,
            dict,
            type_name,
            null_slot,
            body,
        } => v.visit_auto_close(*resource, dict, type_name, *null_slot, body, expr),
        ExprKind::Atom(atom) => v.visit_expr_atom(atom, expr),
    }
}

pub fn walk_let<V: ExprVisitor + ?Sized>(v: &mut V, value: &SimpleExpr, body: &Expr) -> V::Result {
    try_visit!(v.visit_simple_expr(value));
    v.visit_expr(body)
}

/// Default `LetRec` walk: descend into each binding's capture atoms (the bound
/// `VarId` is a binder, not a referenced var, and is never visited as an
/// atom), then walk the body. Visitors that need to mark the bound vars as
/// in-scope must override `visit_let_rec` and call `walk_let_rec` after.
pub fn walk_let_rec<V: ExprVisitor + ?Sized>(
    v: &mut V,
    bindings: &[(VarId, Type, FnId, Vec<Atom>)],
    body: &Expr,
) -> V::Result {
    for (_, _, _, captures) in bindings {
        for a in captures {
            try_visit!(v.visit_atom(a));
        }
    }
    v.visit_expr(body)
}

pub fn walk_let_join<V: ExprVisitor + ?Sized>(
    v: &mut V,
    join_body: &Expr,
    body: &Expr,
) -> V::Result {
    try_visit!(v.visit_expr(join_body));
    v.visit_expr(body)
}

pub fn walk_jump<V: ExprVisitor + ?Sized>(v: &mut V, args: &[Atom]) -> V::Result {
    for a in args {
        try_visit!(v.visit_atom(a));
    }
    V::Result::output()
}

pub fn walk_bool_switch<V: ExprVisitor + ?Sized>(
    v: &mut V,
    scrutinee: &Atom,
    true_body: &Expr,
    false_body: &Expr,
) -> V::Result {
    try_visit!(v.visit_atom(scrutinee));
    try_visit!(v.visit_expr(true_body));
    v.visit_expr(false_body)
}

pub fn walk_switch<V: ExprVisitor + ?Sized>(
    v: &mut V,
    scrutinee: &Atom,
    branches: &[SwitchBranch],
    default: Option<&Expr>,
) -> V::Result {
    try_visit!(v.visit_atom(scrutinee));
    for branch in branches {
        try_visit!(v.visit_switch_branch(branch));
    }
    if let Some(d) = default {
        return v.visit_expr(d);
    }
    V::Result::output()
}

pub fn walk_switch_branch<V: ExprVisitor + ?Sized>(v: &mut V, branch: &SwitchBranch) -> V::Result {
    v.visit_expr(&branch.body)
}

/// Default `AutoClose` walk: descend into `dict` (atom) then `body`. The
/// `resource` `VarId` is a binder reference: it identifies the variable being
/// closed and is the override's responsibility to insert into any analysis
/// state (see `RefVarCollector::visit_auto_close` in `lower.rs`). The walk
/// helper deliberately does not invoke `visit_atom` on `resource` so the
/// helper stays "walk only descends"; visitors that don't override get
/// `dict + body` traversal and must call `walk_auto_close` themselves after
/// any binder bookkeeping.
pub fn walk_auto_close<V: ExprVisitor + ?Sized>(v: &mut V, dict: &Atom, body: &Expr) -> V::Result {
    try_visit!(v.visit_atom(dict));
    v.visit_expr(body)
}
