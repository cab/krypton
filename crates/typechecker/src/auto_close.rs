use rustc_hash::{FxHashMap, FxHashSet};

use crate::trait_registry::TraitRegistry;
use crate::type_error::LeakReason;
use crate::typed_ast::{
    AutoCloseBinding, AutoCloseInfo, ScopeId, TraitName, TypedExpr, TypedExprKind, TypedFnDecl,
    TypedMatchArm, TypedPattern,
};
use crate::types::{ParamMode, Type, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};
use crate::visit::TypedExprVisitor;
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
        // D.2: `~fn` is structurally Linear — never Disposable, regardless of
        // capture set. The `Fn` arm here is the classifier-side enforcement;
        // instance registration also rejects `impl Disposable[<fn type>]` up
        // front.
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
        Type::Shape(_) => {
            panic!("ICE: Type::Own(Type::Shape(..)) reached auto_close — should be resolved")
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
fn collect_moved_vars(expr: &TypedExpr, ownership_moves: &FxHashMap<Span, String>) -> Vec<String> {
    let mut acc = Vec::new();
    let mut collector = MovedVarsCollector {
        ownership_moves,
        acc: &mut acc,
    };
    collector.visit_expr(expr);
    acc
}

/// Visitor used by [`collect_moved_vars`]: sparse descent that deliberately
/// only recurses into the subset of variants where a value can flow into a
/// consuming position. Control-flow nodes (If, Match, Let, Do, Recur,
/// QuestionMark, Discharge, Lambda) do not descend — the App-arg consumption
/// pass in `visit_app` drives consumption attribution for those shapes.
struct MovedVarsCollector<'a> {
    ownership_moves: &'a FxHashMap<Span, String>,
    acc: &'a mut Vec<String>,
}

impl<'a> TypedExprVisitor for MovedVarsCollector<'a> {
    type Result = ();

    fn visit_var(&mut self, name: &str, expr: &TypedExpr) {
        if self
            .ownership_moves
            .get(&expr.span)
            .is_some_and(|n| n == name)
        {
            self.acc.push(name.to_string());
        }
    }

    // Block descent into variants that the original walker did not recurse
    // into. Defaults handle the remaining (App, TypeApp, Tuple, VecLit,
    // StructLit, StructUpdate, FieldAccess, BinaryOp, UnaryOp, Lit).
    fn visit_if(&mut self, _c: &TypedExpr, _t: &TypedExpr, _e: &TypedExpr, _expr: &TypedExpr) {}
    fn visit_let(&mut self, _n: &str, _v: &TypedExpr, _b: Option<&TypedExpr>, _expr: &TypedExpr) {}
    fn visit_let_pattern(
        &mut self,
        _p: &TypedPattern,
        _v: &TypedExpr,
        _b: Option<&TypedExpr>,
        _expr: &TypedExpr,
    ) {
    }
    fn visit_do(&mut self, _exprs: &[TypedExpr], _expr: &TypedExpr) {}
    fn visit_match(&mut self, _s: &TypedExpr, _arms: &[TypedMatchArm], _expr: &TypedExpr) {}
    fn visit_lambda(&mut self, _p: &[String], _b: &TypedExpr, _expr: &TypedExpr) {}
    fn visit_recur(&mut self, _args: &[TypedExpr], _modes: &[ParamMode], _expr: &TypedExpr) {}
    fn visit_question_mark(&mut self, _i: &TypedExpr, _opt: bool, _expr: &TypedExpr) {}
    fn visit_discharge(&mut self, _i: &TypedExpr, _expr: &TypedExpr) {}
}

/// Walk an expression and return the names of any `Var` nodes that occupy a
/// "tail" (return-value) position. A function whose body ends in `x` is
/// returning `x`; we treat that as consuming `x` for the purposes of the
/// linear-leak check.
fn collect_tail_vars(expr: &TypedExpr) -> Vec<String> {
    let mut acc = Vec::new();
    let mut collector = TailVarsCollector { acc: &mut acc };
    collector.visit_expr(expr);
    acc
}

struct TailVarsCollector<'a> {
    acc: &'a mut Vec<String>,
}

impl<'a> TypedExprVisitor for TailVarsCollector<'a> {
    type Result = ();

    fn visit_expr(&mut self, expr: &TypedExpr) {
        match &expr.kind {
            TypedExprKind::Var(name) => self.acc.push(name.clone()),
            TypedExprKind::Do(exprs) => {
                if let Some(last) = exprs.last() {
                    self.visit_expr(last);
                }
            }
            TypedExprKind::Let { body: Some(b), .. }
            | TypedExprKind::LetPattern { body: Some(b), .. } => self.visit_expr(b),
            TypedExprKind::If { then_, else_, .. } => {
                self.visit_expr(then_);
                self.visit_expr(else_);
            }
            TypedExprKind::Match { arms, .. } => {
                for arm in arms {
                    self.visit_expr(&arm.body);
                }
            }
            _ => {}
        }
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
    ownership_moves: &'a FxHashMap<Span, String>,
    has_disposable_trait: bool,
    scheme_constraints: &'a [(TraitName, Vec<TypeVarId>)],
    info: AutoCloseInfo,
    errors: Vec<SpannedTypeError>,
    /// Bindings (keyed by `(name, binding_span)`) for which an E0108 has
    /// already been emitted in the current function. Used to avoid
    /// double-reporting (e.g. branch-leak + scope-exit on the same binding).
    reported_linear: FxHashSet<(String, Span)>,
    /// Currently-live bindings inside the function body being walked. Carried
    /// on the struct (rather than as a `&mut Vec<LiveBinding>` parameter) so
    /// the `TypedExprVisitor` impl can own the descent. Branches that need
    /// isolation swap this with a local via `std::mem::take` / `replace`.
    live: Vec<LiveBinding>,
}

impl<'a> AutoCloseAnalyzer<'a> {
    fn new(
        registry: &'a TraitRegistry,
        ownership_moves: &'a FxHashMap<Span, String>,
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
            reported_linear: FxHashSet::default(),
            live: Vec::new(),
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

    /// Walk `branch` with `branch_live` swapped in as `self.live`, isolating
    /// the branch's `self.info` delta. Returns `(final_live, branch_info)` so
    /// the caller can merge. The caller is responsible for saving `self.live`
    /// before calling this helper — on return, `self.live` is restored to
    /// `Vec::new()` (empty) and the real merge target must be re-installed.
    fn walk_branch_isolated(
        &mut self,
        branch: &TypedExpr,
        branch_live: Vec<LiveBinding>,
    ) -> (Vec<LiveBinding>, AutoCloseInfo) {
        let prior_info = std::mem::take(&mut self.info);
        let prior_live = std::mem::replace(&mut self.live, branch_live);
        self.visit_expr(branch);
        let final_live = std::mem::replace(&mut self.live, prior_live);
        let branch_info = std::mem::replace(&mut self.info, prior_info);
        (final_live, branch_info)
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
        self.live.clear();

        self.scoped(decl.fn_scope_id, |this| {
            for (i, param) in decl.params.iter().enumerate() {
                if let Some(param_ty) = fn_param_types.get(i) {
                    // Borrow-mode params (`&~T`) do not transfer ownership to
                    // the function; the caller still owns the value. Skip them.
                    if matches!(
                        param.mode,
                        ParamMode::Borrow | ParamMode::ObservationalBorrow
                    ) {
                        continue;
                    }
                    // Inside an `impl Disposable[T] { fun dispose(...) }`, the
                    // self parameter is always classified as Linear, never as
                    // Disposable. Classifying it as Disposable would recursively
                    // insert an auto-dispose call on itself; classifying it by
                    // its fields would let an empty body silently leak `~`
                    // fields. Linear forces the body to explicitly discharge
                    // the obligation by destructuring or by passing the value
                    // to an extern consuming function.
                    let kind = if let Some(self_name) = close_self_type {
                        if let Type::Own(inner) = param_ty {
                            if concrete_type_name(inner) == Some(self_name) {
                                OwnedKind::Linear(self_name.to_string())
                            } else {
                                this.classify(param_ty)
                            }
                        } else {
                            this.classify(param_ty)
                        }
                    } else {
                        this.classify(param_ty)
                    };
                    // TypedParam has no span; use the function body span as a
                    // stable proxy. Dedup is keyed on (name, span) so two params
                    // sharing the same span still emit distinct diagnostics.
                    if let Some(b) =
                        LiveBinding::from_kind(param.name.clone(), decl.body.span, kind)
                    {
                        this.live.push(b);
                    }
                }
            }
            this.visit_expr(&decl.body);

            // Tail-return consumption: if the body ends in `x` (or in branches
            // each ending in some `x`), treat those as consumed by the return.
            let tail_vars = collect_tail_vars(&decl.body);
            for var_name in tail_vars {
                if let Some(pos) = Self::find_live(&this.live, &var_name) {
                    this.live.remove(pos);
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

    /// Run `f` with `self.live` as the active scope. After it returns, any
    /// bindings introduced inside the scope are processed: Disposable bindings
    /// are recorded in `scope_exits` for IR lowering; Linear bindings produce
    /// E0108 errors.
    fn scoped<F>(&mut self, scope_id: ScopeId, f: F)
    where
        F: FnOnce(&mut Self),
    {
        let base = self.live.len();
        f(self);
        if self.live.len() > base {
            let drained: Vec<LiveBinding> = self.live.drain(base..).collect();
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
}

impl<'a> TypedExprVisitor for AutoCloseAnalyzer<'a> {
    type Result = ();

    fn visit_let(
        &mut self,
        name: &str,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        expr: &TypedExpr,
    ) {
        self.visit_expr(value);

        // Shadow check: a let that re-binds an already-live name closes
        // the previous binding (Disposable) or leaks it (Linear).
        if let Some(pos) = Self::find_live(&self.live, name) {
            let removed = self.live.remove(pos);
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
        let new_binding = LiveBinding::from_kind(name.to_string(), expr.span, new_kind);

        if let Some(body) = body {
            let sid = self.expect_scope_id(expr, "Let{body:Some}");
            self.scoped(sid, |this| {
                if let Some(b) = new_binding {
                    this.live.push(b);
                }
                this.visit_expr(body);
            });
        } else if let Some(b) = new_binding {
            self.live.push(b);
        }
    }

    fn visit_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        param_modes: &[ParamMode],
        _deferred_id: Option<crate::typed_ast::DeferredId>,
        _expr: &TypedExpr,
    ) {
        self.visit_expr(func);
        for arg in args {
            self.visit_expr(arg);
        }
        // Consumption detection: only examine consume-mode args.
        // Borrow slots receive a place expression whose root must
        // stay live (M37-T6 guarantees the arg cannot itself perform
        // a consume), so auto-close skips them rather than relying
        // on `ownership_moves` being empty for those spans.
        for (i, arg) in args.iter().enumerate() {
            let mode = param_modes.get(i).copied().unwrap_or(ParamMode::Consume);
            if !matches!(mode, ParamMode::Consume) {
                continue;
            }
            let consumed = collect_moved_vars(arg, self.ownership_moves);
            for var_name in consumed {
                if let Some(pos) = Self::find_live(&self.live, &var_name) {
                    let removed = self.live.remove(pos);
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

    fn visit_type_app(
        &mut self,
        inner: &TypedExpr,
        _type_bindings: &[(crate::types::SchemeVarId, crate::types::Type)],
        _expr: &TypedExpr,
    ) {
        self.visit_expr(inner);
    }

    fn visit_question_mark(&mut self, inner: &TypedExpr, _is_option: bool, expr: &TypedExpr) {
        self.visit_expr(inner);
        if !self.live.is_empty() {
            let mut disposable_snapshot: Vec<AutoCloseBinding> = Vec::new();
            let live_snapshot: Vec<LiveBinding> = self.live.iter().rev().cloned().collect();
            for b in &live_snapshot {
                match &b.kind {
                    LiveKind::Disposable => disposable_snapshot.push(b.as_auto_close()),
                    LiveKind::Linear => {
                        self.emit_linear_leak(b, expr.span, LeakReason::EarlyReturnViaQuestion);
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

    fn visit_if(
        &mut self,
        cond: &TypedExpr,
        then_: &TypedExpr,
        else_: &TypedExpr,
        expr: &TypedExpr,
    ) {
        self.visit_expr(cond);
        let live_after_cond = std::mem::take(&mut self.live);
        let (then_live, then_info) = self.walk_branch_isolated(then_, live_after_cond.clone());
        let (else_live, else_info) = self.walk_branch_isolated(else_, live_after_cond.clone());
        self.merge_branch_info(then_info);
        self.merge_branch_info(else_info);

        for binding in &live_after_cond {
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
                        self.emit_linear_leak(binding, expr.span, LeakReason::BranchMissing);
                    }
                }
            }
        }

        // Merge: keep only bindings present in both branches.
        self.live = live_after_cond
            .into_iter()
            .filter(|binding| {
                then_live.iter().any(|b| b.name == binding.name)
                    && else_live.iter().any(|b| b.name == binding.name)
            })
            .collect();
    }

    fn visit_match(&mut self, scrutinee: &TypedExpr, arms: &[TypedMatchArm], expr: &TypedExpr) {
        self.visit_expr(scrutinee);
        if arms.is_empty() {
            return;
        }
        let live_after_scrutinee = std::mem::take(&mut self.live);
        let mut branch_lives: Vec<Vec<LiveBinding>> = Vec::new();
        let mut branch_infos: Vec<AutoCloseInfo> = Vec::new();
        for arm in arms {
            let (arm_live, arm_info) = self.walk_arm_isolated(arm, live_after_scrutinee.clone());
            branch_lives.push(arm_live);
            branch_infos.push(arm_info);
        }
        for arm_info in branch_infos {
            self.merge_branch_info(arm_info);
        }

        for binding in &live_after_scrutinee {
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
                        self.emit_linear_leak(binding, expr.span, LeakReason::BranchMissing);
                    }
                }
            }
        }

        self.live = live_after_scrutinee
            .into_iter()
            .filter(|binding| {
                branch_lives
                    .iter()
                    .all(|bl| bl.iter().any(|b| b.name == binding.name))
            })
            .collect();
    }

    fn visit_match_arm(&mut self, arm: &TypedMatchArm) {
        // Arms are walked with explicit isolation in `visit_match`; this hook
        // exists only to satisfy the trait and must not fire during normal
        // descent.
        let _ = arm;
    }

    // Lambda soundness chain:
    //   1. `infer_lambda` (crates/typechecker/src/infer/expr.rs:712-718,
    //      `first_own_capture`) promotes any closure that captures a `~T`
    //      to `~fn`.
    //   2. The ownership checker enforces single-call semantics on `~fn`.
    // Therefore: walking the lambda body and removing consumed linears
    // from the outer `live` is sound — the linear is "transferred into"
    // the closure, which itself appears in outer `live` as a `Linear ~fn`
    // and will be leak-checked normally.
    fn visit_lambda(&mut self, _params: &[String], body: &TypedExpr, _expr: &TypedExpr) {
        // Walk the lambda body with a clone of the outer live list so
        // that linear bindings captured by the closure are seen as
        // consumed by their reference inside the body. After the walk,
        // propagate any *linear* removals back to the outer live list
        // (Disposable bindings remain owned by the outer scope and are
        // closed there).
        let saved_live = std::mem::take(&mut self.live);
        self.live = saved_live.clone();
        self.visit_expr(body);
        let lambda_live = std::mem::replace(&mut self.live, saved_live);
        self.live.retain(|b| {
            if matches!(b.kind, LiveKind::Linear) {
                lambda_live.iter().any(|lb| lb.name == b.name)
            } else {
                true
            }
        });
    }

    fn visit_do(&mut self, exprs: &[TypedExpr], expr: &TypedExpr) {
        let sid = self.expect_scope_id(expr, "Do");
        self.scoped(sid, |this| {
            for e in exprs {
                this.visit_expr(e);
            }
        });
    }

    fn visit_var(&mut self, name: &str, _expr: &TypedExpr) {
        // Linear bindings: any reference at all is treated as a use,
        // and a use is a consume under M39-T3 strict linearity. The
        // ownership tracker enforces single-use, so this can fire at
        // most once per binding. Disposable bindings keep the existing
        // semantics: only App-arg moves count, attributed via the
        // App-handler's deep consumption walk.
        if let Some(pos) = Self::find_live(&self.live, name) {
            if matches!(self.live[pos].kind, LiveKind::Linear) {
                self.live.remove(pos);
            }
        }
    }

    fn visit_binary_op(
        &mut self,
        _op: &krypton_parser::ast::BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        _expr: &TypedExpr,
    ) {
        self.visit_expr(lhs);
        self.visit_expr(rhs);
    }

    fn visit_unary_op(
        &mut self,
        _op: &krypton_parser::ast::UnaryOp,
        operand: &TypedExpr,
        _expr: &TypedExpr,
    ) {
        self.visit_expr(operand);
    }

    fn visit_field_access(
        &mut self,
        inner: &TypedExpr,
        _field: &str,
        _resolved_type_ref: Option<&crate::typed_ast::ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) {
        self.visit_expr(inner);
    }

    fn visit_struct_lit(
        &mut self,
        _name: &str,
        fields: &[(String, TypedExpr)],
        _resolved_type_ref: Option<&crate::typed_ast::ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) {
        for (_, e) in fields {
            self.visit_expr(e);
        }
        // A struct literal moves any owned vars in its field exprs.
        for (_, e) in fields {
            let consumed = collect_moved_vars(e, self.ownership_moves);
            for var_name in consumed {
                if let Some(pos) = Self::find_live(&self.live, &var_name) {
                    self.live.remove(pos);
                }
            }
        }
    }

    fn visit_struct_update(
        &mut self,
        base: &TypedExpr,
        fields: &[(String, TypedExpr)],
        _expr: &TypedExpr,
    ) {
        self.visit_expr(base);
        for (_, e) in fields {
            self.visit_expr(e);
        }
    }

    fn visit_let_pattern(
        &mut self,
        pattern: &TypedPattern,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        expr: &TypedExpr,
    ) {
        self.visit_expr(value);

        // Destructuring may move owned vars from the value expression.
        let consumed = collect_moved_vars(value, self.ownership_moves);
        for var_name in consumed {
            if let Some(pos) = Self::find_live(&self.live, &var_name) {
                self.live.remove(pos);
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
            self.scoped(sid, |this| {
                for b in bindings {
                    this.live.push(b);
                }
                this.visit_expr(body);
            });
        } else {
            for b in bindings {
                self.live.push(b);
            }
        }
    }

    fn visit_recur(&mut self, args: &[TypedExpr], _param_modes: &[ParamMode], expr: &TypedExpr) {
        // Walk args first so any linear forwarded through `recur(b, ...)`
        // is removed from `live` before the back-edge leak check runs.
        // Mirrors the QuestionMark handler.
        for arg in args {
            self.visit_expr(arg);
        }
        if !self.live.is_empty() {
            let mut disposable_snapshot: Vec<AutoCloseBinding> = Vec::new();
            let live_snapshot: Vec<LiveBinding> = self.live.iter().rev().cloned().collect();
            for b in &live_snapshot {
                match &b.kind {
                    LiveKind::Disposable => disposable_snapshot.push(b.as_auto_close()),
                    LiveKind::Linear => {
                        self.emit_linear_leak(b, expr.span, LeakReason::RecurBack);
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

    fn visit_tuple(&mut self, args: &[TypedExpr], _expr: &TypedExpr) {
        for arg in args {
            self.visit_expr(arg);
        }
        // Tuple literals move any owned vars among their elements.
        for arg in args {
            let consumed = collect_moved_vars(arg, self.ownership_moves);
            for var_name in consumed {
                if let Some(pos) = Self::find_live(&self.live, &var_name) {
                    self.live.remove(pos);
                }
            }
        }
    }

    fn visit_vec_lit(&mut self, args: &[TypedExpr], _expr: &TypedExpr) {
        for arg in args {
            self.visit_expr(arg);
        }
        // Vec literals move any owned vars among their elements.
        for arg in args {
            let consumed = collect_moved_vars(arg, self.ownership_moves);
            for var_name in consumed {
                if let Some(pos) = Self::find_live(&self.live, &var_name) {
                    self.live.remove(pos);
                }
            }
        }
    }

    fn visit_discharge(&mut self, inner: &TypedExpr, _expr: &TypedExpr) {
        self.visit_expr(inner);
        let consumed = collect_moved_vars(inner, self.ownership_moves);
        for var_name in consumed {
            if let Some(pos) = Self::find_live(&self.live, &var_name) {
                self.live.remove(pos);
            }
        }
    }

    fn visit_lit(&mut self, _lit: &krypton_parser::ast::Lit) {}
}

impl<'a> AutoCloseAnalyzer<'a> {
    /// Walk a match arm (guard + body) with an isolated `self.live` and
    /// `self.info`. Returns the post-arm live set and the info produced by
    /// the arm. Structurally mirrors `walk_branch_isolated` for if-branches.
    fn walk_arm_isolated(
        &mut self,
        arm: &TypedMatchArm,
        arm_live: Vec<LiveBinding>,
    ) -> (Vec<LiveBinding>, AutoCloseInfo) {
        let prior_info = std::mem::take(&mut self.info);
        let prior_live = std::mem::replace(&mut self.live, arm_live);
        if let Some(guard) = &arm.guard {
            self.visit_expr(guard);
        }
        self.visit_expr(&arm.body);
        let final_live = std::mem::replace(&mut self.live, prior_live);
        let arm_info = std::mem::replace(&mut self.info, prior_info);
        (final_live, arm_info)
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
    ownership_moves: &FxHashMap<Span, String>,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::ParamMode;

    /// D.2: `~fn` is structurally Linear — never Disposable. Even when the
    /// Disposable trait is in scope (`has_disposable_trait = true`), the
    /// classifier short-circuits on `Type::Fn` to `Linear`, irrespective of
    /// any instances the registry might claim. Pins D.2 at the classifier
    /// seam in case future refactors add a fall-through to `find_instance`.
    #[test]
    fn fn_is_never_disposable() {
        let fn_ty = Type::Fn(vec![(ParamMode::Consume, Type::Int)], Box::new(Type::Unit));
        let owned = Type::Own(Box::new(fn_ty));
        let registry = TraitRegistry::new();
        let result = classify_owned(&owned, &registry, true, &[]);
        assert!(
            matches!(result, OwnedKind::Linear(_)),
            "expected Linear, got {:?}",
            result
        );
    }
}
