//! Unit tests for `SimpleExprVisitor` and `ExprVisitor`. Exercises the trait
//! shape directly without depending on any consumer that's been ported to it
//! — these tests must be able to fail in isolation and pin the visitor API.

use krypton_ir::expr::{
    Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SimpleExprKind, SwitchBranch,
};
use krypton_ir::visit::{
    walk_expr, walk_let_rec, walk_simple_expr, ExprVisitor, SimpleExprVisitor,
};
use krypton_ir::{CanonicalRef, FnId, LocalSymbolKey, ModulePath, TraitName, Type, VarId};
use krypton_parser::ast::Span;

// ── construction helpers ──────────────────────────────────────────────────

fn sp() -> Span {
    (0, 0)
}

fn expr(kind: ExprKind, ty: Type) -> Expr {
    Expr::new(sp(), ty, kind)
}

fn simple(kind: SimpleExprKind) -> SimpleExpr {
    SimpleExpr::new(sp(), kind)
}

fn atom_expr(atom: Atom, ty: Type) -> Expr {
    expr(ExprKind::Atom(atom), ty)
}

fn type_ref(name: &str) -> CanonicalRef {
    CanonicalRef {
        module: ModulePath::new("test"),
        symbol: LocalSymbolKey::Type(name.to_string()),
    }
}

fn trait_name() -> TraitName {
    TraitName::new("test/show".to_string(), "Show".to_string())
}

/// Build a `SimpleExpr` whose walk hits every `SimpleExprKind` variant at
/// least once. The wrapper variant is `MakeTuple` since it can carry an arm
/// per non-leaf variant via tuple fields — but tuple elements are atoms only,
/// so we instead surface each variant by walking each one independently in
/// `counts_all_simple_variants_visited`.
fn one_of_each_simple() -> Vec<SimpleExpr> {
    vec![
        simple(SimpleExprKind::Call {
            func: FnId(0),
            args: vec![Atom::Var(VarId(1))],
        }),
        simple(SimpleExprKind::TraitCall {
            trait_name: trait_name(),
            method_name: "show".to_string(),
            args: vec![Atom::Var(VarId(2))],
        }),
        simple(SimpleExprKind::CallClosure {
            closure: Atom::Var(VarId(3)),
            args: vec![Atom::Var(VarId(4))],
        }),
        simple(SimpleExprKind::MakeClosure {
            func: FnId(1),
            captures: vec![Atom::Var(VarId(5))],
        }),
        simple(SimpleExprKind::Construct {
            type_ref: type_ref("Point"),
            fields: vec![Atom::Var(VarId(6))],
        }),
        simple(SimpleExprKind::ConstructVariant {
            type_ref: type_ref("Option"),
            variant: "Some".to_string(),
            tag: 0,
            fields: vec![Atom::Var(VarId(7))],
        }),
        simple(SimpleExprKind::Project {
            value: Atom::Var(VarId(8)),
            field_index: 0,
        }),
        simple(SimpleExprKind::Tag {
            value: Atom::Var(VarId(9)),
        }),
        simple(SimpleExprKind::MakeTuple {
            elements: vec![Atom::Var(VarId(10)), Atom::Var(VarId(11))],
        }),
        simple(SimpleExprKind::TupleProject {
            value: Atom::Var(VarId(12)),
            index: 0,
        }),
        simple(SimpleExprKind::PrimOp {
            op: PrimOp::AddInt,
            args: vec![Atom::Var(VarId(13)), Atom::Var(VarId(14))],
        }),
        simple(SimpleExprKind::GetDict {
            instance_ref: type_ref("ShowInt"),
            trait_name: trait_name(),
            target_types: vec![Type::Int],
        }),
        simple(SimpleExprKind::MakeDict {
            instance_ref: type_ref("ShowMap"),
            trait_name: trait_name(),
            target_types: vec![Type::Int],
            sub_dicts: vec![Atom::Var(VarId(15))],
        }),
        simple(SimpleExprKind::ProjectDictField {
            dict: Atom::Var(VarId(16)),
            field_index: 0,
            result_trait: trait_name(),
            result_target_types: vec![Type::Int],
        }),
        simple(SimpleExprKind::MakeVec {
            element_type: Type::Int,
            elements: vec![Atom::Var(VarId(17))],
        }),
        simple(SimpleExprKind::Atom(Atom::Var(VarId(18)))),
    ]
}

/// Build an `Expr` whose walk hits every `ExprKind` variant at least once.
/// The shape is not legal lowered IR — we're exercising the walker, not
/// running lint.
fn every_expr_variant() -> Expr {
    let leaf = atom_expr(Atom::Lit(Literal::Unit), Type::Unit);

    // Atom (terminal).
    let atom = atom_expr(Atom::Var(VarId(100)), Type::Int);

    // Jump (terminal).
    let jump = expr(
        ExprKind::Jump {
            target: VarId(101),
            args: vec![Atom::Var(VarId(102))],
        },
        Type::Unit,
    );

    // BoolSwitch.
    let bool_switch = expr(
        ExprKind::BoolSwitch {
            scrutinee: Atom::Var(VarId(103)),
            true_body: Box::new(leaf.clone()),
            false_body: Box::new(leaf.clone()),
        },
        Type::Unit,
    );

    // Switch with one branch and a default.
    let switch = expr(
        ExprKind::Switch {
            scrutinee: Atom::Var(VarId(104)),
            branches: vec![SwitchBranch {
                tag: 0,
                bindings: vec![(VarId(105), Type::Int)],
                body: leaf.clone(),
            }],
            default: Some(Box::new(leaf.clone())),
        },
        Type::Unit,
    );

    // AutoClose.
    let auto_close = expr(
        ExprKind::AutoClose {
            resource: VarId(106),
            dict: Atom::Var(VarId(107)),
            type_name: "File".to_string(),
            null_slot: false,
            body: Box::new(leaf.clone()),
        },
        Type::Unit,
    );

    // LetJoin (wraps the Jump above).
    let let_join = expr(
        ExprKind::LetJoin {
            name: VarId(108),
            params: vec![(VarId(109), Type::Int)],
            join_body: Box::new(leaf.clone()),
            body: Box::new(jump),
            is_recur: false,
        },
        Type::Unit,
    );

    // LetRec.
    let let_rec = expr(
        ExprKind::LetRec {
            bindings: vec![(
                VarId(110),
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                FnId(99),
                vec![Atom::Var(VarId(111))],
            )],
            body: Box::new(leaf.clone()),
        },
        Type::Unit,
    );

    // Let with a SimpleExpr value (PrimOp) so visit_simple_expr is exercised
    // and visit_atom under the simple walk gets a chance.
    let let_node = expr(
        ExprKind::Let {
            bind: VarId(112),
            ty: Type::Int,
            value: simple(SimpleExprKind::PrimOp {
                op: PrimOp::AddInt,
                args: vec![Atom::Var(VarId(113)), Atom::Lit(Literal::Int(1))],
            }),
            body: Box::new(atom),
        },
        Type::Int,
    );

    // Wrap everything inside a sequence of nested Lets so a single walk hits
    // every variant.
    let chain = expr(
        ExprKind::Let {
            bind: VarId(200),
            ty: Type::Unit,
            value: simple(SimpleExprKind::Atom(Atom::Lit(Literal::Unit))),
            body: Box::new(expr(
                ExprKind::Let {
                    bind: VarId(201),
                    ty: Type::Unit,
                    value: simple(SimpleExprKind::Atom(Atom::Lit(Literal::Unit))),
                    body: Box::new(expr(
                        ExprKind::Let {
                            bind: VarId(202),
                            ty: Type::Unit,
                            value: simple(SimpleExprKind::Atom(Atom::Lit(Literal::Unit))),
                            body: Box::new(expr(
                                ExprKind::Let {
                                    bind: VarId(203),
                                    ty: Type::Unit,
                                    value: simple(SimpleExprKind::Atom(Atom::Lit(Literal::Unit))),
                                    body: Box::new(expr(
                                        ExprKind::Let {
                                            bind: VarId(204),
                                            ty: Type::Unit,
                                            value: simple(SimpleExprKind::Atom(Atom::Lit(
                                                Literal::Unit,
                                            ))),
                                            body: Box::new(expr(
                                                ExprKind::Let {
                                                    bind: VarId(205),
                                                    ty: Type::Unit,
                                                    value: simple(SimpleExprKind::Atom(Atom::Lit(
                                                        Literal::Unit,
                                                    ))),
                                                    body: Box::new(let_node),
                                                },
                                                Type::Unit,
                                            )),
                                        },
                                        Type::Unit,
                                    )),
                                },
                                Type::Unit,
                            )),
                        },
                        Type::Unit,
                    )),
                },
                Type::Unit,
            )),
        },
        Type::Unit,
    );

    // Now wire each variant as the "value" of an outer Let with that variant
    // in its body — easiest way to thread them all into one tree without a
    // do/seq construct in the IR.
    expr(
        ExprKind::LetJoin {
            name: VarId(300),
            params: vec![],
            join_body: Box::new(let_rec),
            body: Box::new(expr(
                ExprKind::LetJoin {
                    name: VarId(301),
                    params: vec![],
                    join_body: Box::new(let_join),
                    body: Box::new(expr(
                        ExprKind::LetJoin {
                            name: VarId(302),
                            params: vec![],
                            join_body: Box::new(bool_switch),
                            body: Box::new(expr(
                                ExprKind::LetJoin {
                                    name: VarId(303),
                                    params: vec![],
                                    join_body: Box::new(switch),
                                    body: Box::new(expr(
                                        ExprKind::LetJoin {
                                            name: VarId(304),
                                            params: vec![],
                                            join_body: Box::new(auto_close),
                                            body: Box::new(chain),
                                            is_recur: false,
                                        },
                                        Type::Unit,
                                    )),
                                    is_recur: false,
                                },
                                Type::Unit,
                            )),
                            is_recur: false,
                        },
                        Type::Unit,
                    )),
                    is_recur: false,
                },
                Type::Unit,
            )),
            is_recur: false,
        },
        Type::Unit,
    )
}

// ── counting visitor over both traits ─────────────────────────────────────

#[derive(Default)]
struct CountingExprVisitor {
    // SimpleExprKind counters
    call: u32,
    trait_call: u32,
    call_closure: u32,
    make_closure: u32,
    construct: u32,
    construct_variant: u32,
    project: u32,
    tag: u32,
    make_tuple: u32,
    tuple_project: u32,
    prim_op: u32,
    get_dict: u32,
    make_dict: u32,
    project_dict_field: u32,
    make_vec: u32,
    simple_atom: u32,
    // ExprKind counters
    let_: u32,
    let_rec: u32,
    let_join: u32,
    jump: u32,
    bool_switch: u32,
    switch: u32,
    switch_branch: u32,
    auto_close: u32,
    expr_atom: u32,
    // Atom counter
    atom: u32,
}

impl SimpleExprVisitor for CountingExprVisitor {
    type Result = ();

    fn visit_atom(&mut self, _a: &Atom) {
        self.atom += 1;
    }

    fn visit_call(&mut self, _func: FnId, args: &[Atom], _simple: &SimpleExpr) {
        self.call += 1;
        krypton_ir::visit::walk_call(self, args);
    }
    fn visit_trait_call(
        &mut self,
        _trait_name: &TraitName,
        _method_name: &str,
        args: &[Atom],
        _simple: &SimpleExpr,
    ) {
        self.trait_call += 1;
        krypton_ir::visit::walk_trait_call(self, args);
    }
    fn visit_call_closure(&mut self, closure: &Atom, args: &[Atom], _simple: &SimpleExpr) {
        self.call_closure += 1;
        krypton_ir::visit::walk_call_closure(self, closure, args);
    }
    fn visit_make_closure(&mut self, _func: FnId, captures: &[Atom], _simple: &SimpleExpr) {
        self.make_closure += 1;
        krypton_ir::visit::walk_make_closure(self, captures);
    }
    fn visit_construct(&mut self, _type_ref: &CanonicalRef, fields: &[Atom], _simple: &SimpleExpr) {
        self.construct += 1;
        krypton_ir::visit::walk_construct(self, fields);
    }
    fn visit_construct_variant(
        &mut self,
        _type_ref: &CanonicalRef,
        _variant: &str,
        _tag: u32,
        fields: &[Atom],
        _simple: &SimpleExpr,
    ) {
        self.construct_variant += 1;
        krypton_ir::visit::walk_construct_variant(self, fields);
    }
    fn visit_project(&mut self, value: &Atom, _field_index: usize, _simple: &SimpleExpr) {
        self.project += 1;
        krypton_ir::visit::walk_project(self, value);
    }
    fn visit_tag(&mut self, value: &Atom, _simple: &SimpleExpr) {
        self.tag += 1;
        krypton_ir::visit::walk_tag(self, value);
    }
    fn visit_make_tuple(&mut self, elements: &[Atom], _simple: &SimpleExpr) {
        self.make_tuple += 1;
        krypton_ir::visit::walk_make_tuple(self, elements);
    }
    fn visit_tuple_project(&mut self, value: &Atom, _index: usize, _simple: &SimpleExpr) {
        self.tuple_project += 1;
        krypton_ir::visit::walk_tuple_project(self, value);
    }
    fn visit_prim_op(&mut self, _op: PrimOp, args: &[Atom], _simple: &SimpleExpr) {
        self.prim_op += 1;
        krypton_ir::visit::walk_prim_op(self, args);
    }
    fn visit_get_dict(
        &mut self,
        _instance_ref: &CanonicalRef,
        _trait_name: &TraitName,
        _target_types: &[Type],
        _simple: &SimpleExpr,
    ) {
        self.get_dict += 1;
    }
    fn visit_make_dict(
        &mut self,
        _instance_ref: &CanonicalRef,
        _trait_name: &TraitName,
        _target_types: &[Type],
        sub_dicts: &[Atom],
        _simple: &SimpleExpr,
    ) {
        self.make_dict += 1;
        krypton_ir::visit::walk_make_dict(self, sub_dicts);
    }
    fn visit_project_dict_field(
        &mut self,
        dict: &Atom,
        _field_index: usize,
        _result_trait: &TraitName,
        _result_target_types: &[Type],
        _simple: &SimpleExpr,
    ) {
        self.project_dict_field += 1;
        krypton_ir::visit::walk_project_dict_field(self, dict);
    }
    fn visit_make_vec(&mut self, _element_type: &Type, elements: &[Atom], _simple: &SimpleExpr) {
        self.make_vec += 1;
        krypton_ir::visit::walk_make_vec(self, elements);
    }
    fn visit_simple_atom(&mut self, atom: &Atom, _simple: &SimpleExpr) {
        self.simple_atom += 1;
        self.visit_atom(atom);
    }
}

impl ExprVisitor for CountingExprVisitor {
    fn visit_let(
        &mut self,
        _bind: VarId,
        _ty: &Type,
        value: &SimpleExpr,
        body: &Expr,
        _expr: &Expr,
    ) {
        self.let_ += 1;
        krypton_ir::visit::walk_let(self, value, body);
    }
    fn visit_let_rec(
        &mut self,
        bindings: &[(VarId, Type, FnId, Vec<Atom>)],
        body: &Expr,
        _expr: &Expr,
    ) {
        self.let_rec += 1;
        krypton_ir::visit::walk_let_rec(self, bindings, body);
    }
    fn visit_let_join(
        &mut self,
        _name: VarId,
        _params: &[(VarId, Type)],
        join_body: &Expr,
        body: &Expr,
        _is_recur: bool,
        _expr: &Expr,
    ) {
        self.let_join += 1;
        krypton_ir::visit::walk_let_join(self, join_body, body);
    }
    fn visit_jump(&mut self, _target: VarId, args: &[Atom], _expr: &Expr) {
        self.jump += 1;
        krypton_ir::visit::walk_jump(self, args);
    }
    fn visit_bool_switch(
        &mut self,
        scrutinee: &Atom,
        true_body: &Expr,
        false_body: &Expr,
        _expr: &Expr,
    ) {
        self.bool_switch += 1;
        krypton_ir::visit::walk_bool_switch(self, scrutinee, true_body, false_body);
    }
    fn visit_switch(
        &mut self,
        scrutinee: &Atom,
        branches: &[SwitchBranch],
        default: Option<&Expr>,
        _expr: &Expr,
    ) {
        self.switch += 1;
        krypton_ir::visit::walk_switch(self, scrutinee, branches, default);
    }
    fn visit_switch_branch(&mut self, branch: &SwitchBranch) {
        self.switch_branch += 1;
        krypton_ir::visit::walk_switch_branch(self, branch);
    }
    fn visit_auto_close(
        &mut self,
        _resource: VarId,
        dict: &Atom,
        _type_name: &str,
        _null_slot: bool,
        body: &Expr,
        _expr: &Expr,
    ) {
        self.auto_close += 1;
        krypton_ir::visit::walk_auto_close(self, dict, body);
    }
    fn visit_expr_atom(&mut self, atom: &Atom, _expr: &Expr) {
        self.expr_atom += 1;
        self.visit_atom(atom);
    }
}

#[test]
fn counts_all_expr_variants_visited() {
    let tree = every_expr_variant();
    let mut v = CountingExprVisitor::default();
    v.visit_expr(&tree);

    assert!(v.let_ >= 1, "let not visited");
    assert!(v.let_rec >= 1, "let_rec not visited");
    assert!(v.let_join >= 1, "let_join not visited");
    assert!(v.jump >= 1, "jump not visited");
    assert!(v.bool_switch >= 1, "bool_switch not visited");
    assert!(v.switch >= 1, "switch not visited");
    assert!(v.switch_branch >= 1, "switch_branch not visited");
    assert!(v.auto_close >= 1, "auto_close not visited");
    assert!(v.expr_atom >= 1, "expr_atom not visited");
    assert!(v.prim_op >= 1, "prim_op (SimpleExpr value) not visited");
    assert!(v.atom >= 1, "atom not visited");
}

/// SimpleExpr-only dispatch: walks every `SimpleExprKind` variant via a
/// visitor that only impls `SimpleExprVisitor`. Pins the standalone use case
/// (matches `impl Display for SimpleExpr`).
#[derive(Default)]
struct SimpleOnlyCounter {
    seen: Vec<&'static str>,
    atoms: u32,
}

impl SimpleExprVisitor for SimpleOnlyCounter {
    type Result = ();

    fn visit_atom(&mut self, _a: &Atom) {
        self.atoms += 1;
    }

    fn visit_call(&mut self, _func: FnId, args: &[Atom], _simple: &SimpleExpr) {
        self.seen.push("call");
        krypton_ir::visit::walk_call(self, args);
    }
    fn visit_trait_call(
        &mut self,
        _trait_name: &TraitName,
        _method_name: &str,
        args: &[Atom],
        _simple: &SimpleExpr,
    ) {
        self.seen.push("trait_call");
        krypton_ir::visit::walk_trait_call(self, args);
    }
    fn visit_call_closure(&mut self, closure: &Atom, args: &[Atom], _simple: &SimpleExpr) {
        self.seen.push("call_closure");
        krypton_ir::visit::walk_call_closure(self, closure, args);
    }
    fn visit_make_closure(&mut self, _func: FnId, captures: &[Atom], _simple: &SimpleExpr) {
        self.seen.push("make_closure");
        krypton_ir::visit::walk_make_closure(self, captures);
    }
    fn visit_construct(&mut self, _type_ref: &CanonicalRef, fields: &[Atom], _simple: &SimpleExpr) {
        self.seen.push("construct");
        krypton_ir::visit::walk_construct(self, fields);
    }
    fn visit_construct_variant(
        &mut self,
        _type_ref: &CanonicalRef,
        _variant: &str,
        _tag: u32,
        fields: &[Atom],
        _simple: &SimpleExpr,
    ) {
        self.seen.push("construct_variant");
        krypton_ir::visit::walk_construct_variant(self, fields);
    }
    fn visit_project(&mut self, value: &Atom, _field_index: usize, _simple: &SimpleExpr) {
        self.seen.push("project");
        krypton_ir::visit::walk_project(self, value);
    }
    fn visit_tag(&mut self, value: &Atom, _simple: &SimpleExpr) {
        self.seen.push("tag");
        krypton_ir::visit::walk_tag(self, value);
    }
    fn visit_make_tuple(&mut self, elements: &[Atom], _simple: &SimpleExpr) {
        self.seen.push("make_tuple");
        krypton_ir::visit::walk_make_tuple(self, elements);
    }
    fn visit_tuple_project(&mut self, value: &Atom, _index: usize, _simple: &SimpleExpr) {
        self.seen.push("tuple_project");
        krypton_ir::visit::walk_tuple_project(self, value);
    }
    fn visit_prim_op(&mut self, _op: PrimOp, args: &[Atom], _simple: &SimpleExpr) {
        self.seen.push("prim_op");
        krypton_ir::visit::walk_prim_op(self, args);
    }
    fn visit_get_dict(
        &mut self,
        _instance_ref: &CanonicalRef,
        _trait_name: &TraitName,
        _target_types: &[Type],
        _simple: &SimpleExpr,
    ) {
        self.seen.push("get_dict");
    }
    fn visit_make_dict(
        &mut self,
        _instance_ref: &CanonicalRef,
        _trait_name: &TraitName,
        _target_types: &[Type],
        sub_dicts: &[Atom],
        _simple: &SimpleExpr,
    ) {
        self.seen.push("make_dict");
        krypton_ir::visit::walk_make_dict(self, sub_dicts);
    }
    fn visit_project_dict_field(
        &mut self,
        dict: &Atom,
        _field_index: usize,
        _result_trait: &TraitName,
        _result_target_types: &[Type],
        _simple: &SimpleExpr,
    ) {
        self.seen.push("project_dict_field");
        krypton_ir::visit::walk_project_dict_field(self, dict);
    }
    fn visit_make_vec(&mut self, _element_type: &Type, elements: &[Atom], _simple: &SimpleExpr) {
        self.seen.push("make_vec");
        krypton_ir::visit::walk_make_vec(self, elements);
    }
    fn visit_simple_atom(&mut self, atom: &Atom, _simple: &SimpleExpr) {
        self.seen.push("simple_atom");
        self.visit_atom(atom);
    }
}

#[test]
fn counts_all_simple_variants_visited() {
    let mut v = SimpleOnlyCounter::default();
    for s in one_of_each_simple() {
        v.visit_simple_expr(&s);
    }
    let expected = [
        "call",
        "trait_call",
        "call_closure",
        "make_closure",
        "construct",
        "construct_variant",
        "project",
        "tag",
        "make_tuple",
        "tuple_project",
        "prim_op",
        "get_dict",
        "make_dict",
        "project_dict_field",
        "make_vec",
        "simple_atom",
    ];
    for label in expected {
        assert!(v.seen.contains(&label), "{label} not visited");
    }
    assert!(v.atoms > 0, "atoms not visited");
}

// ── pre-order DFS check ───────────────────────────────────────────────────

#[derive(Default)]
struct LabelVisitor {
    labels: Vec<String>,
}

impl SimpleExprVisitor for LabelVisitor {
    type Result = ();

    fn visit_simple_expr(&mut self, simple: &SimpleExpr) {
        let label = match &simple.kind {
            SimpleExprKind::PrimOp { op, .. } => format!("prim_op:{op:?}"),
            SimpleExprKind::Atom(a) => match a {
                Atom::Var(VarId(n)) => format!("simple_atom_var:{n}"),
                Atom::Lit(_) => "simple_atom_lit".to_string(),
            },
            _ => "simple_other".to_string(),
        };
        self.labels.push(label);
        walk_simple_expr(self, simple);
    }

    fn visit_atom(&mut self, a: &Atom) {
        let label = match a {
            Atom::Var(VarId(n)) => format!("atom_var:{n}"),
            Atom::Lit(_) => "atom_lit".to_string(),
        };
        self.labels.push(label);
    }
}

impl ExprVisitor for LabelVisitor {
    fn visit_expr(&mut self, e: &Expr) {
        let label = match &e.kind {
            ExprKind::Let { bind, .. } => format!("let:{}", bind.0),
            ExprKind::Atom(_) => "expr_atom".to_string(),
            ExprKind::Jump { target, .. } => format!("jump:{}", target.0),
            ExprKind::BoolSwitch { .. } => "bool_switch".to_string(),
            _ => "expr_other".to_string(),
        };
        self.labels.push(label);
        walk_expr(self, e);
    }
}

#[test]
fn walk_order_is_pre_order_dfs() {
    // Let { v1 = AddInt(v2, v3); body = Atom(v4) }
    let tree = expr(
        ExprKind::Let {
            bind: VarId(1),
            ty: Type::Int,
            value: simple(SimpleExprKind::PrimOp {
                op: PrimOp::AddInt,
                args: vec![Atom::Var(VarId(2)), Atom::Var(VarId(3))],
            }),
            body: Box::new(atom_expr(Atom::Var(VarId(4)), Type::Int)),
        },
        Type::Int,
    );
    let mut v = LabelVisitor::default();
    v.visit_expr(&tree);
    // Expected pre-order: outer Let, then SimpleExpr value (PrimOp), then its
    // two atoms, then body Expr (Atom), then the body's atom.
    assert_eq!(
        v.labels,
        vec![
            "let:1",
            "prim_op:AddInt",
            "atom_var:2",
            "atom_var:3",
            "expr_atom",
            "atom_var:4",
        ]
    );
}

// ── override prevents descent ─────────────────────────────────────────────

struct NoLetRecBodyDescent {
    atoms_seen: Vec<u32>,
}

impl SimpleExprVisitor for NoLetRecBodyDescent {
    type Result = ();

    fn visit_atom(&mut self, a: &Atom) {
        if let Atom::Var(VarId(n)) = a {
            self.atoms_seen.push(*n);
        }
    }
}

impl ExprVisitor for NoLetRecBodyDescent {
    fn visit_let_rec(
        &mut self,
        _bindings: &[(VarId, Type, FnId, Vec<Atom>)],
        _body: &Expr,
        _expr: &Expr,
    ) {
        // Deliberately do NOT call walk_let_rec — neither the captures nor
        // the body should be descended into.
    }
}

#[test]
fn override_prevents_descent() {
    let inner_atom = atom_expr(Atom::Var(VarId(42)), Type::Int);
    let let_rec = expr(
        ExprKind::LetRec {
            bindings: vec![(
                VarId(1),
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                FnId(0),
                vec![Atom::Var(VarId(99))],
            )],
            body: Box::new(inner_atom),
        },
        Type::Unit,
    );
    let mut v = NoLetRecBodyDescent { atoms_seen: vec![] };
    v.visit_expr(&let_rec);
    assert!(
        v.atoms_seen.is_empty(),
        "expected no atoms to be visited, got {:?}",
        v.atoms_seen
    );
}

// ── early exit ────────────────────────────────────────────────────────────

struct StopOnAtom;

impl SimpleExprVisitor for StopOnAtom {
    type Result = Result<(), &'static str>;

    fn visit_atom(&mut self, _a: &Atom) -> Self::Result {
        Err("found")
    }
}

impl ExprVisitor for StopOnAtom {}

#[test]
fn early_exit_short_circuits() {
    // Bool-switch whose scrutinee atom triggers immediately.
    let tree = expr(
        ExprKind::BoolSwitch {
            scrutinee: Atom::Var(VarId(1)),
            true_body: Box::new(atom_expr(Atom::Var(VarId(2)), Type::Unit)),
            false_body: Box::new(atom_expr(Atom::Var(VarId(3)), Type::Unit)),
        },
        Type::Unit,
    );
    let mut v = StopOnAtom;
    let r = v.visit_expr(&tree);
    assert_eq!(r, Err("found"));
}

struct FindFirstSwitch;

impl SimpleExprVisitor for FindFirstSwitch {
    type Result = Result<(), Span>;
}

impl ExprVisitor for FindFirstSwitch {
    fn visit_switch(
        &mut self,
        _scrutinee: &Atom,
        _branches: &[SwitchBranch],
        _default: Option<&Expr>,
        e: &Expr,
    ) -> Self::Result {
        Err(e.span)
    }
}

#[test]
fn early_exit_carries_value() {
    // Wrap the Switch inside a Let; the walk should reach the switch and
    // return its span via Err.
    let switch_span: Span = (123, 456);
    let switch = Expr::new(
        switch_span,
        Type::Unit,
        ExprKind::Switch {
            scrutinee: Atom::Var(VarId(0)),
            branches: vec![],
            default: Some(Box::new(atom_expr(Atom::Lit(Literal::Unit), Type::Unit))),
        },
    );
    let tree = expr(
        ExprKind::Let {
            bind: VarId(1),
            ty: Type::Unit,
            value: simple(SimpleExprKind::Atom(Atom::Lit(Literal::Unit))),
            body: Box::new(switch),
        },
        Type::Unit,
    );
    let mut v = FindFirstSwitch;
    assert_eq!(v.visit_expr(&tree), Err(switch_span));
}

/// Silence dead-code warning for the unused `walk_let_rec` re-export — it's
/// imported for readers to discover the walk_* set.
#[allow(dead_code)]
fn _use_walk_let_rec<V: ExprVisitor + ?Sized>(
    v: &mut V,
    bindings: &[(VarId, Type, FnId, Vec<Atom>)],
    body: &Expr,
) -> V::Result {
    walk_let_rec(v, bindings, body)
}
