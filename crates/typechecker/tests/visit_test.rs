//! Unit tests for `TypedExprVisitor`. Exercises the trait shape directly
//! without depending on any consumer that's been ported to it — these tests
//! must be able to fail in isolation and pin the visitor API.

use krypton_parser::ast::{BinOp, Lit, UnaryOp};
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedMatchArm, TypedPattern};
use krypton_typechecker::types::Type;
use krypton_typechecker::visit::{walk_expr, walk_lambda, TypedExprVisitor};

/// Shortcut for a dummy source span. Tests never read span data, so `(0, 0)`
/// is safe — the same form `module_interface::instance_summary_to_def_info`
/// uses when it synthesizes dummy typed exprs.
fn sp() -> krypton_parser::ast::Span {
    (0, 0)
}

fn expr(kind: TypedExprKind, ty: Type) -> TypedExpr {
    TypedExpr {
        kind,
        ty,
        span: sp(),
        resolved_ref: None,
        scope_id: None,
    }
}

fn lit_int(n: i64) -> TypedExpr {
    expr(TypedExprKind::Lit(Lit::Int(n)), Type::Int)
}

fn var(name: &str) -> TypedExpr {
    expr(TypedExprKind::Var(name.to_string()), Type::Int)
}

fn var_pat(name: &str) -> TypedPattern {
    TypedPattern::Var {
        name: name.to_string(),
        ty: Type::Int,
        span: sp(),
    }
}

/// Build a single `TypedExpr` that structurally contains every
/// `TypedExprKind` variant at least once. The exact shape is not legal krypton
/// — we're exercising the walker, not running typechecking.
fn every_variant() -> TypedExpr {
    // Leaves.
    let lit = lit_int(1);
    let v = var("a");

    // Constructions that will appear inside the Do block.
    let app = expr(
        TypedExprKind::App {
            func: Box::new(var("f")),
            args: vec![lit_int(2)],
            param_modes: vec![],
            deferred_id: None,
        },
        Type::Int,
    );
    let type_app = expr(
        TypedExprKind::TypeApp {
            expr: Box::new(var("g")),
            type_bindings: vec![],
        },
        Type::Int,
    );
    let if_expr = expr(
        TypedExprKind::If {
            cond: Box::new(lit_int(3)),
            then_: Box::new(lit_int(4)),
            else_: Box::new(lit_int(5)),
        },
        Type::Int,
    );
    let let_expr = expr(
        TypedExprKind::Let {
            name: "x".to_string(),
            value: Box::new(lit_int(6)),
            body: Some(Box::new(var("x"))),
        },
        Type::Int,
    );
    let match_expr = expr(
        TypedExprKind::Match {
            scrutinee: Box::new(lit_int(7)),
            arms: vec![TypedMatchArm {
                pattern: var_pat("p"),
                guard: Some(Box::new(lit_int(8))),
                body: lit_int(9),
            }],
        },
        Type::Int,
    );
    let lambda = expr(
        TypedExprKind::Lambda {
            params: vec!["y".to_string()],
            body: Box::new(var("y")),
        },
        Type::Int,
    );
    let field_access = expr(
        TypedExprKind::FieldAccess {
            expr: Box::new(var("r")),
            field: "f".to_string(),
            resolved_type_ref: None,
        },
        Type::Int,
    );
    let recur = expr(
        TypedExprKind::Recur {
            args: vec![lit_int(10)],
            param_modes: vec![],
        },
        Type::Int,
    );
    let tuple = expr(
        TypedExprKind::Tuple(vec![lit_int(11), lit_int(12)]),
        Type::Int,
    );
    let bin = expr(
        TypedExprKind::BinaryOp {
            op: BinOp::Add,
            lhs: Box::new(lit_int(13)),
            rhs: Box::new(lit_int(14)),
        },
        Type::Int,
    );
    let un = expr(
        TypedExprKind::UnaryOp {
            op: UnaryOp::Neg,
            operand: Box::new(lit_int(15)),
        },
        Type::Int,
    );
    let struct_lit = expr(
        TypedExprKind::StructLit {
            name: "S".to_string(),
            fields: vec![("f".to_string(), lit_int(16))],
            resolved_type_ref: None,
        },
        Type::Int,
    );
    let struct_update = expr(
        TypedExprKind::StructUpdate {
            base: Box::new(var("s")),
            fields: vec![("f".to_string(), lit_int(17))],
        },
        Type::Int,
    );
    let let_pattern = expr(
        TypedExprKind::LetPattern {
            pattern: var_pat("q"),
            value: Box::new(lit_int(18)),
            body: Some(Box::new(var("q"))),
        },
        Type::Int,
    );
    let question_mark = expr(
        TypedExprKind::QuestionMark {
            expr: Box::new(var("r")),
            is_option: true,
        },
        Type::Int,
    );
    let vec_lit = expr(
        TypedExprKind::VecLit(vec![lit_int(19), lit_int(20)]),
        Type::Int,
    );
    let discharge = expr(TypedExprKind::Discharge(Box::new(lit_int(21))), Type::Unit);

    // Wrap everything in a Do so a single walk hits every variant.
    expr(
        TypedExprKind::Do(vec![
            lit,
            v,
            app,
            type_app,
            if_expr,
            let_expr,
            match_expr,
            lambda,
            field_access,
            recur,
            tuple,
            bin,
            un,
            struct_lit,
            struct_update,
            let_pattern,
            question_mark,
            vec_lit,
            discharge,
        ]),
        Type::Int,
    )
}

#[derive(Default)]
struct CountingVisitor {
    lit: u32,
    var: u32,
    app: u32,
    type_app: u32,
    if_: u32,
    let_: u32,
    do_: u32,
    match_: u32,
    match_arm: u32,
    lambda: u32,
    field_access: u32,
    recur: u32,
    tuple: u32,
    binary_op: u32,
    unary_op: u32,
    struct_lit: u32,
    struct_update: u32,
    let_pattern: u32,
    question_mark: u32,
    vec_lit: u32,
    discharge: u32,
}

impl TypedExprVisitor for CountingVisitor {
    type Result = ();

    fn visit_lit(&mut self, _lit: &Lit) {
        self.lit += 1;
    }
    fn visit_var(&mut self, _name: &str, _expr: &TypedExpr) {
        self.var += 1;
    }
    fn visit_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        _param_modes: &[krypton_typechecker::types::ParamMode],
        _deferred_id: Option<krypton_typechecker::typed_ast::DeferredId>,
        _expr: &TypedExpr,
    ) {
        self.app += 1;
        krypton_typechecker::visit::walk_app(self, func, args);
    }
    fn visit_type_app(
        &mut self,
        inner: &TypedExpr,
        _type_bindings: &[(
            krypton_typechecker::types::SchemeVarId,
            krypton_typechecker::types::Type,
        )],
        _expr: &TypedExpr,
    ) {
        self.type_app += 1;
        krypton_typechecker::visit::walk_type_app(self, inner);
    }
    fn visit_if(
        &mut self,
        cond: &TypedExpr,
        then_: &TypedExpr,
        else_: &TypedExpr,
        _expr: &TypedExpr,
    ) {
        self.if_ += 1;
        krypton_typechecker::visit::walk_if(self, cond, then_, else_);
    }
    fn visit_let(
        &mut self,
        _name: &str,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        _expr: &TypedExpr,
    ) {
        self.let_ += 1;
        krypton_typechecker::visit::walk_let(self, value, body);
    }
    fn visit_do(&mut self, exprs: &[TypedExpr], _expr: &TypedExpr) {
        self.do_ += 1;
        krypton_typechecker::visit::walk_do(self, exprs);
    }
    fn visit_match(&mut self, scrutinee: &TypedExpr, arms: &[TypedMatchArm], _expr: &TypedExpr) {
        self.match_ += 1;
        krypton_typechecker::visit::walk_match(self, scrutinee, arms);
    }
    fn visit_match_arm(&mut self, arm: &TypedMatchArm) {
        self.match_arm += 1;
        krypton_typechecker::visit::walk_match_arm(self, arm);
    }
    fn visit_lambda(&mut self, _params: &[String], body: &TypedExpr, _expr: &TypedExpr) {
        self.lambda += 1;
        krypton_typechecker::visit::walk_lambda(self, body);
    }
    fn visit_field_access(
        &mut self,
        inner: &TypedExpr,
        _field: &str,
        _resolved: Option<&krypton_typechecker::typed_ast::ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) {
        self.field_access += 1;
        krypton_typechecker::visit::walk_field_access(self, inner);
    }
    fn visit_recur(
        &mut self,
        args: &[TypedExpr],
        _param_modes: &[krypton_typechecker::types::ParamMode],
        _expr: &TypedExpr,
    ) {
        self.recur += 1;
        krypton_typechecker::visit::walk_recur(self, args);
    }
    fn visit_tuple(&mut self, elements: &[TypedExpr], _expr: &TypedExpr) {
        self.tuple += 1;
        krypton_typechecker::visit::walk_tuple(self, elements);
    }
    fn visit_binary_op(
        &mut self,
        _op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        _expr: &TypedExpr,
    ) {
        self.binary_op += 1;
        krypton_typechecker::visit::walk_binary_op(self, lhs, rhs);
    }
    fn visit_unary_op(&mut self, _op: &UnaryOp, operand: &TypedExpr, _expr: &TypedExpr) {
        self.unary_op += 1;
        krypton_typechecker::visit::walk_unary_op(self, operand);
    }
    fn visit_struct_lit(
        &mut self,
        _name: &str,
        fields: &[(String, TypedExpr)],
        _resolved: Option<&krypton_typechecker::typed_ast::ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) {
        self.struct_lit += 1;
        krypton_typechecker::visit::walk_struct_lit(self, fields);
    }
    fn visit_struct_update(
        &mut self,
        base: &TypedExpr,
        fields: &[(String, TypedExpr)],
        _expr: &TypedExpr,
    ) {
        self.struct_update += 1;
        krypton_typechecker::visit::walk_struct_update(self, base, fields);
    }
    fn visit_let_pattern(
        &mut self,
        _pattern: &TypedPattern,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        _expr: &TypedExpr,
    ) {
        self.let_pattern += 1;
        krypton_typechecker::visit::walk_let_pattern(self, value, body);
    }
    fn visit_question_mark(&mut self, inner: &TypedExpr, _is_option: bool, _expr: &TypedExpr) {
        self.question_mark += 1;
        krypton_typechecker::visit::walk_question_mark(self, inner);
    }
    fn visit_vec_lit(&mut self, elements: &[TypedExpr], _expr: &TypedExpr) {
        self.vec_lit += 1;
        krypton_typechecker::visit::walk_vec_lit(self, elements);
    }
    fn visit_discharge(&mut self, inner: &TypedExpr, _expr: &TypedExpr) {
        self.discharge += 1;
        krypton_typechecker::visit::walk_discharge(self, inner);
    }
}

#[test]
fn counts_all_variants_visited() {
    let tree = every_variant();
    let mut v = CountingVisitor::default();
    v.visit_expr(&tree);

    assert!(v.lit >= 1, "lit not visited");
    assert!(v.var >= 1, "var not visited");
    assert!(v.app >= 1, "app not visited");
    assert!(v.type_app >= 1, "type_app not visited");
    assert!(v.if_ >= 1, "if not visited");
    assert!(v.let_ >= 1, "let not visited");
    assert!(v.do_ >= 1, "do not visited");
    assert!(v.match_ >= 1, "match not visited");
    assert!(v.match_arm >= 1, "match_arm not visited");
    assert!(v.lambda >= 1, "lambda not visited");
    assert!(v.field_access >= 1, "field_access not visited");
    assert!(v.recur >= 1, "recur not visited");
    assert!(v.tuple >= 1, "tuple not visited");
    assert!(v.binary_op >= 1, "binary_op not visited");
    assert!(v.unary_op >= 1, "unary_op not visited");
    assert!(v.struct_lit >= 1, "struct_lit not visited");
    assert!(v.struct_update >= 1, "struct_update not visited");
    assert!(v.let_pattern >= 1, "let_pattern not visited");
    assert!(v.question_mark >= 1, "question_mark not visited");
    assert!(v.vec_lit >= 1, "vec_lit not visited");
    assert!(v.discharge >= 1, "discharge not visited");
}

#[derive(Default)]
struct LabelVisitor {
    labels: Vec<String>,
}

impl TypedExprVisitor for LabelVisitor {
    type Result = ();

    fn visit_expr(&mut self, expr: &TypedExpr) {
        // Record the node type before descending so ordering is pre-order DFS.
        let label = match &expr.kind {
            TypedExprKind::App { .. } => "app".to_string(),
            TypedExprKind::Var(n) => format!("var:{n}"),
            TypedExprKind::Let { name, .. } => format!("let:{name}"),
            TypedExprKind::Lit(Lit::Int(n)) => format!("lit:{n}"),
            TypedExprKind::Lit(_) => "lit".to_string(),
            _ => "other".to_string(),
        };
        self.labels.push(label);
        walk_expr(self, expr);
    }
}

#[test]
fn walk_order_is_pre_order_dfs() {
    // App { Var("f"), [Let { name: "x", value: Lit(1), body: Some(Var("x")) }] }
    let let_x = expr(
        TypedExprKind::Let {
            name: "x".to_string(),
            value: Box::new(lit_int(1)),
            body: Some(Box::new(var("x"))),
        },
        Type::Int,
    );
    let tree = expr(
        TypedExprKind::App {
            func: Box::new(var("f")),
            args: vec![let_x],
            param_modes: vec![],
            deferred_id: None,
        },
        Type::Int,
    );
    let mut v = LabelVisitor::default();
    v.visit_expr(&tree);
    assert_eq!(v.labels, vec!["app", "var:f", "let:x", "lit:1", "var:x"]);
}

/// Visitor that refuses to descend into `Lambda` bodies — mirrors what
/// `find_first_recur_span` needs (stop at lambda boundary).
struct NoLambdaDescentVisitor {
    vars_seen: Vec<String>,
}

impl TypedExprVisitor for NoLambdaDescentVisitor {
    type Result = ();

    fn visit_var(&mut self, name: &str, _expr: &TypedExpr) {
        self.vars_seen.push(name.to_string());
    }

    fn visit_lambda(&mut self, _params: &[String], _body: &TypedExpr, _expr: &TypedExpr) {
        // Deliberately do NOT call walk_lambda — the body must not be
        // descended into.
    }
}

#[test]
fn override_prevents_descent() {
    let lambda = expr(
        TypedExprKind::Lambda {
            params: vec!["p".to_string()],
            body: Box::new(var("captured")),
        },
        Type::Int,
    );
    let mut v = NoLambdaDescentVisitor { vars_seen: vec![] };
    v.visit_expr(&lambda);
    assert!(
        v.vars_seen.is_empty(),
        "expected no vars to be visited, got {:?}",
        v.vars_seen
    );
}

/// Early-exit visitor using `type Result = Result<(), &'static str>`: the
/// first `Var` aborts the walk with `Err`. Regression pin for `find_first_*`
/// style consumers.
struct StopOnVar;

impl TypedExprVisitor for StopOnVar {
    type Result = Result<(), &'static str>;

    fn visit_var(&mut self, _name: &str, _expr: &TypedExpr) -> Self::Result {
        Err("found")
    }
}

#[test]
fn early_exit_short_circuits() {
    let tree = expr(
        TypedExprKind::Do(vec![lit_int(1), var("boom"), lit_int(2)]),
        Type::Int,
    );
    let mut v = StopOnVar;
    let r = v.visit_expr(&tree);
    assert_eq!(r, Err("found"));
}

/// Another early-exit shape: `Result<(), Span>` where `Err(span)` carries the
/// "found-it" value. Pins the `find_first_recur_span` pattern.
struct FindFirstBinaryOp;

impl TypedExprVisitor for FindFirstBinaryOp {
    type Result = Result<(), krypton_parser::ast::Span>;

    fn visit_binary_op(
        &mut self,
        _op: &BinOp,
        _lhs: &TypedExpr,
        _rhs: &TypedExpr,
        expr: &TypedExpr,
    ) -> Self::Result {
        Err(expr.span)
    }

    fn visit_lambda(
        &mut self,
        _params: &[String],
        _body: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        // Lambdas are a hard boundary — don't descend, and treat as "not
        // found" at this level.
        Ok(())
    }
}

#[test]
fn early_exit_carries_value() {
    let bin = expr(
        TypedExprKind::BinaryOp {
            op: BinOp::Add,
            lhs: Box::new(lit_int(1)),
            rhs: Box::new(lit_int(2)),
        },
        Type::Int,
    );
    // Lambda body contains a BinaryOp but lambda override stops descent, so
    // the first returned BinaryOp must be the outer one.
    let lambda = expr(
        TypedExprKind::Lambda {
            params: vec![],
            body: Box::new(expr(
                TypedExprKind::BinaryOp {
                    op: BinOp::Sub,
                    lhs: Box::new(lit_int(3)),
                    rhs: Box::new(lit_int(4)),
                },
                Type::Int,
            )),
        },
        Type::Int,
    );
    let tree = expr(TypedExprKind::Do(vec![lambda, bin]), Type::Int);
    let mut v = FindFirstBinaryOp;
    assert!(v.visit_expr(&tree).is_err());
}

/// Silence dead-code warning for the unused `walk_lambda` re-export above —
/// it's imported for readers to discover the walk_* set. No other tests use
/// it directly.
#[allow(dead_code)]
fn _use_walk_lambda<V: TypedExprVisitor + ?Sized>(v: &mut V, body: &TypedExpr) -> V::Result {
    walk_lambda(v, body)
}
