use std::collections::{HashMap, HashSet};

use crate::trait_registry::TraitRegistry;
use crate::type_error::LeakReason;
use crate::typed_ast::{
    AutoCloseBinding, AutoCloseInfo, ScopeId, TraitName, TypedExpr, TypedExprKind, TypedFnDecl,
    TypedPattern,
};
use crate::types::{ParamMode, Type, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};
use krypton_parser::ast::Span;

/// Classification of an `~T` ("own") type for the leak checker.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OwnedKind {
    /// `~T` where `T: Disposable` — auto-close will synthesize a `dispose(x)` call.
    Disposable(String),
    /// `~T` where `T` is not Disposable — must be consumed explicitly before
    /// scope exit, otherwise E0108 fires. The `String` is the pretty-printed
    /// inner type used in the diagnostic.
    Linear(String),
    /// Not an `~T` value at all.
    NotOwned,
}

fn concrete_type_name(ty: &Type) -> Option<&str> {
    match ty {
        Type::Named(name, _) => Some(name.as_str()),
        Type::Int => Some("Int"),
        Type::Float => Some("Float"),
        Type::Bool => Some("Bool"),
        Type::String => Some("String"),
        _ => None,
    }
}

/// Classify an `~T` value for the leak checker.
///
/// `scheme_constraints` is the current function's where-clause, used to
/// recognize a polymorphic `~Var(a)` whose type variable carries a
/// `Disposable[a]` bound (body-sensitive rule).
///
/// Caller must have normalized the type. `Type::Own(Type::Own(_))`,
/// `Type::Own(Type::MaybeOwn(..))`, and `Type::Own(Type::FnHole)` are treated
/// as ICEs — if any slip through, the bug is in the caller, not here. The
/// inner panics stay as defense-in-depth.
fn classify_owned(
    ty: &Type,
    registry: &TraitRegistry,
    has_disposable_trait: bool,
    scheme_constraints: &[(TraitName, Vec<TypeVarId>)],
) -> OwnedKind {
    let inner = match ty {
        Type::Own(inner) => inner.as_ref(),
        _ => return OwnedKind::NotOwned,
    };

    let disposable_tn = TraitName::core_disposable();

    match inner {
        // Concrete named type: ask the registry whether it implements Disposable.
        Type::Named(name, _) => {
            let is_disposable =
                has_disposable_trait && registry.find_instance(&disposable_tn, inner).is_some();
            if is_disposable {
                OwnedKind::Disposable(name.clone())
            } else {
                OwnedKind::Linear(name.clone())
            }
        }

        // Polymorphic var: only counts as Disposable if the surrounding scheme
        // constrains the var with a Disposable bound.
        Type::Var(id) => {
            let has_bound = has_disposable_trait
                && scheme_constraints
                    .iter()
                    .any(|(tn, vids)| *tn == disposable_tn && vids.contains(id));
            let display = id.display_name();
            if has_bound {
                OwnedKind::Disposable(display)
            } else {
                OwnedKind::Linear(display)
            }
        }

        // Aggregates and other shapes: never Disposable in v0 (M39-T3 scope).
        // Replaces the prior ICE at this site.
        Type::App(_, _) | Type::Tuple(_) | Type::Fn(_, _) => OwnedKind::Linear(inner.to_string()),

        // Primitives wrapped in Own — degenerate but legal under M39-T3.
        Type::Int | Type::Float | Type::Bool | Type::String => OwnedKind::Linear(inner.to_string()),

        // Genuine compiler bugs: nested Own, MaybeOwn at this level, etc.
        Type::Own(_) => {
            panic!("ICE: Type::Own(Type::Own(_)) reached auto_close — possible compiler bug")
        }
        Type::Unit => OwnedKind::Linear("Unit".to_string()),
        Type::MaybeOwn(_, _) => {
            panic!("ICE: Type::Own(Type::MaybeOwn(..)) reached auto_close — possible compiler bug")
        }
        Type::FnHole => {
            panic!("ICE: Type::Own(Type::FnHole) reached auto_close — sentinel must be normalized")
        }
    }
}

/// A live binding tracked by the analyzer. Either a Disposable (auto-closed
/// at scope exit by inserting `dispose`) or a Linear (must be explicitly
/// consumed; otherwise E0108 fires).
#[derive(Debug, Clone)]
enum LiveKind {
    Disposable,
    Linear,
}

#[derive(Debug, Clone)]
struct LiveBinding {
    name: String,
    type_name: String,
    kind: LiveKind,
    binding_span: Span,
}

impl LiveBinding {
    fn from_kind(name: String, binding_span: Span, kind: OwnedKind) -> Option<Self> {
        match kind {
            OwnedKind::Disposable(type_name) => Some(LiveBinding {
                name,
                type_name,
                kind: LiveKind::Disposable,
                binding_span,
            }),
            OwnedKind::Linear(type_name) => Some(LiveBinding {
                name,
                type_name,
                kind: LiveKind::Linear,
                binding_span,
            }),
            OwnedKind::NotOwned => None,
        }
    }

    fn as_auto_close(&self) -> AutoCloseBinding {
        AutoCloseBinding {
            name: self.name.clone(),
            type_name: self.type_name.clone(),
        }
    }
}

/// Recursively collect every `Var` reference inside an expression tree
/// whose span is recorded in the ownership checker's move set.
fn collect_moved_vars(expr: &TypedExpr, ownership_moves: &HashMap<Span, String>) -> Vec<String> {
    let mut acc = Vec::new();
    collect_moved_vars_inner(expr, ownership_moves, &mut acc);
    acc
}

fn collect_moved_vars_inner(
    expr: &TypedExpr,
    ownership_moves: &HashMap<Span, String>,
    acc: &mut Vec<String>,
) {
    match &expr.kind {
        TypedExprKind::Var(name) => {
            if ownership_moves.get(&expr.span).is_some_and(|n| n == name) {
                acc.push(name.clone());
            }
        }
        TypedExprKind::App { func, args } => {
            collect_moved_vars_inner(func, ownership_moves, acc);
            for arg in args {
                collect_moved_vars_inner(arg, ownership_moves, acc);
            }
        }
        TypedExprKind::TypeApp { expr, .. } => collect_moved_vars_inner(expr, ownership_moves, acc),
        TypedExprKind::Tuple(elems) | TypedExprKind::VecLit(elems) => {
            for e in elems {
                collect_moved_vars_inner(e, ownership_moves, acc);
            }
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields {
                collect_moved_vars_inner(e, ownership_moves, acc);
            }
        }
        TypedExprKind::StructUpdate { base, fields } => {
            collect_moved_vars_inner(base, ownership_moves, acc);
            for (_, e) in fields {
                collect_moved_vars_inner(e, ownership_moves, acc);
            }
        }
        TypedExprKind::FieldAccess { expr, .. } => {
            collect_moved_vars_inner(expr, ownership_moves, acc);
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            collect_moved_vars_inner(lhs, ownership_moves, acc);
            collect_moved_vars_inner(rhs, ownership_moves, acc);
        }
        TypedExprKind::UnaryOp { operand, .. } => {
            collect_moved_vars_inner(operand, ownership_moves, acc);
        }
        _ => {}
    }
}

/// Walk an expression and return the names of any `Var` nodes that occupy a
/// "tail" (return-value) position. A function whose body ends in `x` is
/// returning `x`; we treat that as consuming `x` for the purposes of the
/// linear-leak check.
fn collect_tail_vars(expr: &TypedExpr) -> Vec<String> {
    let mut acc = Vec::new();
    collect_tail_vars_inner(expr, &mut acc);
    acc
}

fn collect_tail_vars_inner(expr: &TypedExpr, acc: &mut Vec<String>) {
    match &expr.kind {
        TypedExprKind::Var(name) => acc.push(name.clone()),
        TypedExprKind::Do(exprs) => {
            if let Some(last) = exprs.last() {
                collect_tail_vars_inner(last, acc);
            }
        }
        TypedExprKind::Let { body: Some(b), .. } => collect_tail_vars_inner(b, acc),
        TypedExprKind::LetPattern { body: Some(b), .. } => collect_tail_vars_inner(b, acc),
        TypedExprKind::If { then_, else_, .. } => {
            collect_tail_vars_inner(then_, acc);
            collect_tail_vars_inner(else_, acc);
        }
        TypedExprKind::Match { arms, .. } => {
            for arm in arms {
                collect_tail_vars_inner(&arm.body, acc);
            }
        }
        _ => {}
    }
}

/// Recursively collect owned bindings introduced by a let-pattern. For each
/// `_` wildcard targeting a linear field, also push an immediate scope-exit
/// E0108 error to `errors`.
fn collect_owned_bindings(
    pattern: &TypedPattern,
    registry: &TraitRegistry,
    has_disposable_trait: bool,
    scheme_constraints: &[(TraitName, Vec<TypeVarId>)],
    errors: &mut Vec<SpannedTypeError>,
) -> Vec<LiveBinding> {
    let mut acc = Vec::new();
    collect_owned_bindings_inner(
        pattern,
        registry,
        has_disposable_trait,
        scheme_constraints,
        &mut acc,
        errors,
    );
    acc
}

fn collect_owned_bindings_inner(
    pattern: &TypedPattern,
    registry: &TraitRegistry,
    has_disposable_trait: bool,
    scheme_constraints: &[(TraitName, Vec<TypeVarId>)],
    acc: &mut Vec<LiveBinding>,
    errors: &mut Vec<SpannedTypeError>,
) {
    match pattern {
        TypedPattern::Var { name, ty, span } => {
            let kind = classify_owned(ty, registry, has_disposable_trait, scheme_constraints);
            if let Some(b) = LiveBinding::from_kind(name.clone(), *span, kind) {
                acc.push(b);
            }
        }
        TypedPattern::Wildcard { ty, span } => {
            let kind = classify_owned(ty, registry, has_disposable_trait, scheme_constraints);
            if let OwnedKind::Linear(type_name) = kind {
                errors.push(SpannedTypeError {
                    error: Box::new(TypeError::LinearValueNotConsumed {
                        name: "_".to_string(),
                        type_name,
                        reason: LeakReason::ScopeExit,
                    }),
                    span: *span,
                    note: Some(
                        "`_` cannot discard a linear field; bind it and consume explicitly"
                            .to_string(),
                    ),
                    secondary_span: None,
                    source_file: None,
                    var_names: None,
                });
            }
        }
        TypedPattern::Constructor { args, .. } => {
            for arg in args {
                collect_owned_bindings_inner(
                    arg,
                    registry,
                    has_disposable_trait,
                    scheme_constraints,
                    acc,
                    errors,
                );
            }
        }
        TypedPattern::Tuple { elements, .. } => {
            for elem in elements {
                collect_owned_bindings_inner(
                    elem,
                    registry,
                    has_disposable_trait,
                    scheme_constraints,
                    acc,
                    errors,
                );
            }
        }
        TypedPattern::StructPat { fields, .. } => {
            for (_, field_pat) in fields {
                collect_owned_bindings_inner(
                    field_pat,
                    registry,
                    has_disposable_trait,
                    scheme_constraints,
                    acc,
                    errors,
                );
            }
            // Note: `..` rest fields are not iterated in v0. The struct
            // typechecker has already enforced that the parent expression's
            // type matched; if any elided field is linear and the parent
            // struct itself is non-Disposable, the parent binding's leak
            // diagnostic still fires (the struct is classified as Linear).
        }
        TypedPattern::Lit { .. } => {}
        TypedPattern::Or { alternatives, .. } => {
            if let Some(first) = alternatives.first() {
                collect_owned_bindings_inner(
                    first,
                    registry,
                    has_disposable_trait,
                    scheme_constraints,
                    acc,
                    errors,
                );
            }
        }
    }
}

struct AutoCloseAnalyzer<'a> {
    registry: &'a TraitRegistry,
    ownership_moves: &'a HashMap<Span, String>,
    has_disposable_trait: bool,
    scheme_constraints: &'a [(TraitName, Vec<TypeVarId>)],
    info: AutoCloseInfo,
    errors: Vec<SpannedTypeError>,
    /// Bindings (keyed by `(name, binding_span)`) for which an E0108 has
    /// already been emitted in the current function. Used to avoid
    /// double-reporting (e.g. branch-leak + scope-exit on the same binding).
    reported_linear: HashSet<(String, Span)>,
}

impl<'a> AutoCloseAnalyzer<'a> {
    fn new(
        registry: &'a TraitRegistry,
        ownership_moves: &'a HashMap<Span, String>,
        has_disposable_trait: bool,
        scheme_constraints: &'a [(TraitName, Vec<TypeVarId>)],
    ) -> Self {
        Self {
            registry,
            ownership_moves,
            has_disposable_trait,
            scheme_constraints,
            info: AutoCloseInfo::default(),
            errors: Vec::new(),
            reported_linear: HashSet::new(),
        }
    }

    /// Find the live binding with the given name. Uses LIFO (rposition) to match
    /// lexical scoping for name-resolved references. The analyzer maintains the
    /// invariant "at most one live binding per name" via the Let-shadow handler,
    /// so this is equivalent to position() today — rposition is used for
    /// defense-in-depth should the invariant ever relax.
    fn find_live(live: &[LiveBinding], name: &str) -> Option<usize> {
        let found = live.iter().rposition(|b| b.name == name);
        assert!(
            live.iter().filter(|b| b.name == name).count() <= 1,
            "ICE: auto_close invariant violated: multiple live bindings named `{name}`"
        );
        found
    }

    /// Walk `branch` against an empty `self.info`, returning the info delta
    /// produced by the branch. The caller is responsible for restoring
    /// `self.info` to its pre-branch state and merging the returned delta.
    fn walk_branch_isolated(
        &mut self,
        branch: &TypedExpr,
        branch_live: &mut Vec<LiveBinding>,
    ) -> AutoCloseInfo {
        let prior = std::mem::take(&mut self.info);
        self.walk_expr(branch, branch_live);
        std::mem::replace(&mut self.info, prior)
    }

    /// Merge a branch's info deltas back into `self.info`. Panics on key
    /// collisions (which would indicate duplicate spans across branches — a
    /// desugaring bug).
    fn merge_branch_info(&mut self, branch_info: AutoCloseInfo) {
        for (k, v) in branch_info.shadow_closes {
            assert!(
                self.info.shadow_closes.insert(k, v).is_none(),
                "duplicate shadow_closes span across branches: {:?}",
                k
            );
        }
        for (k, v) in branch_info.early_returns {
            assert!(
                self.info.early_returns.insert(k, v).is_none(),
                "duplicate early_returns span across branches: {:?}",
                k
            );
        }
        for (k, v) in branch_info.recur_closes {
            assert!(
                self.info.recur_closes.insert(k, v).is_none(),
                "duplicate recur_closes span across branches: {:?}",
                k
            );
        }
        for (k, v) in branch_info.consumptions {
            assert!(
                self.info.consumptions.insert(k, v).is_none(),
                "duplicate consumptions span across branches: {:?}",
                k
            );
        }
        for (k, v) in branch_info.scope_exits {
            assert!(
                self.info.scope_exits.insert(k, v).is_none(),
                "duplicate scope_exits ScopeId across branches: {:?}",
                k
            );
        }
    }

    fn classify(&self, ty: &Type) -> OwnedKind {
        classify_owned(
            ty,
            self.registry,
            self.has_disposable_trait,
            self.scheme_constraints,
        )
    }

    /// Emit a linear-leak diagnostic for `binding`, deduplicated by the
    /// binding's introduction span.
    fn emit_linear_leak(&mut self, binding: &LiveBinding, leak_span: Span, reason: LeakReason) {
        if !self
            .reported_linear
            .insert((binding.name.clone(), binding.binding_span))
        {
            return;
        }
        self.errors.push(SpannedTypeError {
            error: Box::new(TypeError::LinearValueNotConsumed {
                name: binding.name.clone(),
                type_name: binding.type_name.clone(),
                reason,
            }),
            span: leak_span,
            note: None,
            secondary_span: None,
            source_file: None,
            var_names: None,
        });
    }

    fn analyze_function(
        &mut self,
        decl: &TypedFnDecl,
        fn_param_types: &[Type],
        close_self_type: Option<&str>,
    ) {
        let mut live: Vec<LiveBinding> = Vec::new();

        self.scoped(decl.fn_scope_id, &mut live, |this, live| {
            for (i, param) in decl.params.iter().enumerate() {
                if let Some(param_ty) = fn_param_types.get(i) {
                    // Borrow-mode params (`&~T`) do not transfer ownership to
                    // the function; the caller still owns the value. Skip them.
                    if param.mode == ParamMode::Borrow {
                        continue;
                    }
                    // Self-skip: inside an `impl Disposable[T] { fun dispose(...) }`,
                    // the self parameter is excluded from BOTH the disposable and the
                    // linear track to avoid infinite recursion / bogus leaks.
                    if let Some(self_name) = close_self_type {
                        if let Type::Own(inner) = param_ty {
                            if concrete_type_name(inner) == Some(self_name) {
                                continue;
                            }
                        }
                    }
                    let kind = this.classify(param_ty);
                    // TypedParam has no span; use the function body span as a
                    // stable proxy. Dedup is keyed on (name, span) so two params
                    // sharing the same span still emit distinct diagnostics.
                    if let Some(b) =
                        LiveBinding::from_kind(param.name.clone(), decl.body.span, kind)
                    {
                        live.push(b);
                    }
                }
            }
            this.walk_expr(&decl.body, live);

            // Tail-return consumption: if the body ends in `x` (or in branches
            // each ending in some `x`), treat those as consumed by the return.
            let tail_vars = collect_tail_vars(&decl.body);
            for var_name in tail_vars {
                if let Some(pos) = Self::find_live(live, &var_name) {
                    live.remove(pos);
                }
            }
        });
    }

    fn assert_no_duplicate_span(&self, map_name: &str, span: Span, map_contains: bool) {
        assert!(
            !map_contains,
            "duplicate span in auto_close {} — possible desugaring bug at {:?}",
            map_name, span
        );
    }

    /// Run `f` with `live` as a scope. After it returns, any bindings introduced
    /// inside the scope are processed: Disposable bindings are recorded in
    /// `scope_exits` for IR lowering; Linear bindings produce E0108 errors.
    fn scoped<F>(&mut self, scope_id: ScopeId, live: &mut Vec<LiveBinding>, f: F)
    where
        F: FnOnce(&mut Self, &mut Vec<LiveBinding>),
    {
        let base = live.len();
        f(self, live);
        if live.len() > base {
            let drained: Vec<LiveBinding> = live.drain(base..).collect();
            let mut disposable_bindings: Vec<AutoCloseBinding> = Vec::new();
            // Iterate in LIFO order (matches existing behaviour for scope_exits).
            for b in drained.into_iter().rev() {
                match b.kind {
                    LiveKind::Disposable => {
                        disposable_bindings.push(b.as_auto_close());
                    }
                    LiveKind::Linear => {
                        self.emit_linear_leak(&b, b.binding_span, LeakReason::ScopeExit);
                    }
                }
            }
            if !disposable_bindings.is_empty() {
                assert!(
                    !self.info.scope_exits.contains_key(&scope_id),
                    "duplicate ScopeId in scope_exits: {:?}",
                    scope_id
                );
                self.info.scope_exits.insert(scope_id, disposable_bindings);
            }
        }
    }

    fn expect_scope_id(&self, expr: &TypedExpr, what: &'static str) -> ScopeId {
        expr.scope_id
            .unwrap_or_else(|| panic!("ICE: {} node at {:?} has no ScopeId", what, expr.span))
    }

    fn walk_expr(&mut self, expr: &TypedExpr, live: &mut Vec<LiveBinding>) {
        match &expr.kind {
            TypedExprKind::Let { name, value, body } => {
                self.walk_expr(value, live);

                // Shadow check: a let that re-binds an already-live name closes
                // the previous binding (Disposable) or leaks it (Linear).
                if let Some(pos) = Self::find_live(live, name) {
                    let removed = live.remove(pos);
                    match &removed.kind {
                        LiveKind::Disposable => {
                            self.assert_no_duplicate_span(
                                "shadow_closes",
                                expr.span,
                                self.info.shadow_closes.contains_key(&expr.span),
                            );
                            self.info
                                .shadow_closes
                                .insert(expr.span, removed.as_auto_close());
                        }
                        LiveKind::Linear => {
                            self.emit_linear_leak(&removed, expr.span, LeakReason::ScopeExit);
                        }
                    }
                }

                let new_kind = self.classify(&value.ty);
                let new_binding = LiveBinding::from_kind(name.clone(), expr.span, new_kind);

                if let Some(body) = body {
                    let sid = self.expect_scope_id(expr, "Let{body:Some}");
                    self.scoped(sid, live, |this, live| {
                        if let Some(b) = new_binding {
                            live.push(b);
                        }
                        this.walk_expr(body, live);
                    });
                } else if let Some(b) = new_binding {
                    live.push(b);
                }
            }

            TypedExprKind::App { func, args } => {
                self.walk_expr(func, live);
                for arg in args {
                    self.walk_expr(arg, live);
                }
                // Deep consumption detection: any var moved within an arg is
                // removed from `live` and recorded in `consumptions`.
                for arg in args {
                    let consumed = collect_moved_vars(arg, self.ownership_moves);
                    for var_name in consumed {
                        if let Some(pos) = Self::find_live(live, &var_name) {
                            let removed = live.remove(pos);
                            // Only Disposable consumptions get tooling-tracked;
                            // linear bindings are silently consumed.
                            if matches!(removed.kind, LiveKind::Disposable) {
                                self.info
                                    .consumptions
                                    .entry(arg.span)
                                    .or_default()
                                    .push(removed.as_auto_close());
                            }
                        }
                    }
                }
            }

            TypedExprKind::TypeApp { expr, .. } => {
                self.walk_expr(expr, live);
            }

            TypedExprKind::QuestionMark { expr: inner, .. } => {
                self.walk_expr(inner, live);
                if !live.is_empty() {
                    let mut disposable_snapshot: Vec<AutoCloseBinding> = Vec::new();
                    for b in live.iter().rev() {
                        match &b.kind {
                            LiveKind::Disposable => disposable_snapshot.push(b.as_auto_close()),
                            LiveKind::Linear => {
                                let cloned = b.clone();
                                self.emit_linear_leak(
                                    &cloned,
                                    expr.span,
                                    LeakReason::EarlyReturnViaQuestion,
                                );
                            }
                        }
                    }
                    if !disposable_snapshot.is_empty() {
                        self.assert_no_duplicate_span(
                            "early_returns",
                            expr.span,
                            self.info.early_returns.contains_key(&expr.span),
                        );
                        self.info
                            .early_returns
                            .insert(expr.span, disposable_snapshot);
                    }
                }
            }

            TypedExprKind::If { cond, then_, else_ } => {
                self.walk_expr(cond, live);
                let mut then_live = live.clone();
                let mut else_live = live.clone();
                let then_info = self.walk_branch_isolated(then_, &mut then_live);
                let else_info = self.walk_branch_isolated(else_, &mut else_live);
                self.merge_branch_info(then_info);
                self.merge_branch_info(else_info);

                for binding in live.iter() {
                    let in_then = then_live.iter().any(|b| b.name == binding.name);
                    let in_else = else_live.iter().any(|b| b.name == binding.name);
                    if in_then != in_else {
                        match &binding.kind {
                            LiveKind::Disposable => {
                                self.errors.push(SpannedTypeError {
                                    error: Box::new(TypeError::DisposableBranchLeak {
                                        name: binding.name.clone(),
                                        type_name: binding.type_name.clone(),
                                    }),
                                    span: expr.span,
                                    note: None,
                                    secondary_span: None,
                                    source_file: None,
                                    var_names: None,
                                });
                            }
                            LiveKind::Linear => {
                                let cloned = binding.clone();
                                self.emit_linear_leak(
                                    &cloned,
                                    expr.span,
                                    LeakReason::BranchMissing,
                                );
                            }
                        }
                    }
                }

                // Merge: keep only bindings present in both branches.
                live.retain(|binding| {
                    then_live.iter().any(|b| b.name == binding.name)
                        && else_live.iter().any(|b| b.name == binding.name)
                });
            }

            TypedExprKind::Match { scrutinee, arms } => {
                self.walk_expr(scrutinee, live);
                if arms.is_empty() {
                    return;
                }
                let mut branch_lives: Vec<Vec<LiveBinding>> = Vec::new();
                let mut branch_infos: Vec<AutoCloseInfo> = Vec::new();
                for arm in arms {
                    let mut arm_live = live.clone();
                    let prior = std::mem::take(&mut self.info);
                    if let Some(guard) = &arm.guard {
                        self.walk_expr(guard, &mut arm_live);
                    }
                    self.walk_expr(&arm.body, &mut arm_live);
                    let arm_info = std::mem::replace(&mut self.info, prior);
                    branch_lives.push(arm_live);
                    branch_infos.push(arm_info);
                }
                for arm_info in branch_infos {
                    self.merge_branch_info(arm_info);
                }

                for binding in live.iter() {
                    let present_count = branch_lives
                        .iter()
                        .filter(|bl| bl.iter().any(|b| b.name == binding.name))
                        .count();
                    if present_count > 0 && present_count < branch_lives.len() {
                        match &binding.kind {
                            LiveKind::Disposable => {
                                self.errors.push(SpannedTypeError {
                                    error: Box::new(TypeError::DisposableBranchLeak {
                                        name: binding.name.clone(),
                                        type_name: binding.type_name.clone(),
                                    }),
                                    span: expr.span,
                                    note: None,
                                    secondary_span: None,
                                    source_file: None,
                                    var_names: None,
                                });
                            }
                            LiveKind::Linear => {
                                let cloned = binding.clone();
                                self.emit_linear_leak(
                                    &cloned,
                                    expr.span,
                                    LeakReason::BranchMissing,
                                );
                            }
                        }
                    }
                }

                live.retain(|binding| {
                    branch_lives
                        .iter()
                        .all(|bl| bl.iter().any(|b| b.name == binding.name))
                });
            }

            // Lambda soundness chain:
            //   1. `infer_lambda` (crates/typechecker/src/infer/expr.rs:712-718,
            //      `first_own_capture`) promotes any closure that captures a `~T`
            //      to `~fn`.
            //   2. The ownership checker enforces single-call semantics on `~fn`
            //      (crates/typechecker/src/ownership.rs:844-847).
            // Therefore: walking the lambda body and removing consumed linears
            // from the outer `live` is sound — the linear is "transferred into"
            // the closure, which itself appears in outer `live` as a `Linear ~fn`
            // and will be leak-checked normally. If the closure is never called,
            // the leak is reported on the closure binding (not the captured
            // value); if called twice, ownership flags the double-use.
            TypedExprKind::Lambda { body, .. } => {
                // Walk the lambda body with a clone of the outer live list so
                // that linear bindings captured by the closure are seen as
                // consumed by their reference inside the body. After the walk,
                // propagate any *linear* removals back to the outer live list
                // (Disposable bindings remain owned by the outer scope and are
                // closed there).
                let mut lambda_live = live.clone();
                self.walk_expr(body, &mut lambda_live);
                live.retain(|b| {
                    if matches!(b.kind, LiveKind::Linear) {
                        lambda_live.iter().any(|lb| lb.name == b.name)
                    } else {
                        true
                    }
                });
            }

            TypedExprKind::Do(exprs) => {
                let sid = self.expect_scope_id(expr, "Do");
                self.scoped(sid, live, |this, live| {
                    for e in exprs {
                        this.walk_expr(e, live);
                    }
                });
            }

            TypedExprKind::Var(name) => {
                // Linear bindings: any reference at all is treated as a use,
                // and a use is a consume under M39-T3 strict linearity. The
                // ownership tracker enforces single-use, so this can fire at
                // most once per binding. Disposable bindings keep the existing
                // semantics: only App-arg moves count, attributed via the
                // App-handler's deep consumption walk.
                if let Some(pos) = Self::find_live(live, name) {
                    if matches!(live[pos].kind, LiveKind::Linear) {
                        live.remove(pos);
                    }
                }
            }

            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                self.walk_expr(lhs, live);
                self.walk_expr(rhs, live);
            }

            TypedExprKind::UnaryOp { operand, .. } => {
                self.walk_expr(operand, live);
            }

            TypedExprKind::FieldAccess { expr, .. } => {
                self.walk_expr(expr, live);
            }

            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    self.walk_expr(e, live);
                }
                // A struct literal moves any owned vars in its field exprs.
                for (_, e) in fields {
                    let consumed = collect_moved_vars(e, self.ownership_moves);
                    for var_name in consumed {
                        if let Some(pos) = Self::find_live(live, &var_name) {
                            live.remove(pos);
                        }
                    }
                }
            }

            TypedExprKind::StructUpdate { base, fields } => {
                self.walk_expr(base, live);
                for (_, e) in fields {
                    self.walk_expr(e, live);
                }
            }

            TypedExprKind::LetPattern {
                pattern,
                value,
                body,
            } => {
                self.walk_expr(value, live);

                // Destructuring may move owned vars from the value expression.
                let consumed = collect_moved_vars(value, self.ownership_moves);
                for var_name in consumed {
                    if let Some(pos) = Self::find_live(live, &var_name) {
                        live.remove(pos);
                    }
                }

                let bindings = collect_owned_bindings(
                    pattern,
                    self.registry,
                    self.has_disposable_trait,
                    self.scheme_constraints,
                    &mut self.errors,
                );

                if let Some(body) = body {
                    let sid = self.expect_scope_id(expr, "LetPattern{body:Some}");
                    self.scoped(sid, live, |this, live| {
                        for b in bindings {
                            live.push(b);
                        }
                        this.walk_expr(body, live);
                    });
                } else {
                    for b in bindings {
                        live.push(b);
                    }
                }
            }

            TypedExprKind::Recur(args) => {
                // Walk args first so any linear forwarded through `recur(b, ...)`
                // is removed from `live` before the back-edge leak check runs.
                // Mirrors the QuestionMark handler.
                for arg in args {
                    self.walk_expr(arg, live);
                }
                if !live.is_empty() {
                    let mut disposable_snapshot: Vec<AutoCloseBinding> = Vec::new();
                    for b in live.iter().rev() {
                        match &b.kind {
                            LiveKind::Disposable => disposable_snapshot.push(b.as_auto_close()),
                            LiveKind::Linear => {
                                let cloned = b.clone();
                                self.emit_linear_leak(&cloned, expr.span, LeakReason::RecurBack);
                            }
                        }
                    }
                    if !disposable_snapshot.is_empty() {
                        self.assert_no_duplicate_span(
                            "recur_closes",
                            expr.span,
                            self.info.recur_closes.contains_key(&expr.span),
                        );
                        self.info
                            .recur_closes
                            .insert(expr.span, disposable_snapshot);
                    }
                }
            }

            TypedExprKind::Tuple(args) | TypedExprKind::VecLit(args) => {
                for arg in args {
                    self.walk_expr(arg, live);
                }
                // Tuple/Vec literals move any owned vars among their elements.
                for arg in args {
                    let consumed = collect_moved_vars(arg, self.ownership_moves);
                    for var_name in consumed {
                        if let Some(pos) = Self::find_live(live, &var_name) {
                            live.remove(pos);
                        }
                    }
                }
            }

            TypedExprKind::Lit(_) => {}
        }
    }
}

/// Compute auto-close information for all functions in the module.
/// Returns the auto-close info plus any diagnostic errors (branch leaks +
/// linear-value-not-consumed).
pub fn compute_auto_close(
    functions: &[TypedFnDecl],
    fn_types: &[(
        String,
        crate::types::TypeScheme,
        Option<crate::typed_ast::TraitName>,
    )],
    registry: &TraitRegistry,
    ownership_moves: &HashMap<Span, String>,
) -> (AutoCloseInfo, Vec<SpannedTypeError>) {
    let disposable_tn = crate::typed_ast::TraitName::core_disposable();
    let has_disposable_trait = registry.lookup_trait(&disposable_tn).is_some();

    let mut info = AutoCloseInfo::default();
    let mut all_errors: Vec<SpannedTypeError> = Vec::new();

    for decl in functions {
        let (param_types, scheme_constraints): (Vec<Type>, Vec<(TraitName, Vec<TypeVarId>)>) =
            fn_types
                .iter()
                .find(|(name, _, _)| name == &decl.name)
                .map(|(_, scheme, _)| {
                    let params = if let Type::Fn(params, _) = &scheme.ty {
                        params.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>()
                    } else {
                        Vec::new()
                    };
                    (params, scheme.constraints.clone())
                })
                .unwrap_or_default();

        let mut analyzer = AutoCloseAnalyzer::new(
            registry,
            ownership_moves,
            has_disposable_trait,
            &scheme_constraints,
        );
        analyzer.info = std::mem::take(&mut info);
        analyzer.analyze_function(decl, &param_types, decl.close_self_type.as_deref());
        info = std::mem::take(&mut analyzer.info);
        all_errors.extend(analyzer.errors);
    }

    (info, all_errors)
}
