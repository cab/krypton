use krypton_parser::ast::*;
use krypton_parser::parser::parse;
use insta::assert_yaml_snapshot;

#[test]
fn test_literal_expressions() {
    let s = (0, 0);
    let exprs = vec![
        Expr::Lit { value: Lit::Int(42), span: s },
        Expr::Lit { value: Lit::String("hello".into()), span: s },
        Expr::Lit { value: Lit::Bool(true), span: s },
        Expr::Lit { value: Lit::Unit, span: s },
        Expr::Lit { value: Lit::Float(3.14), span: s },
    ];
    assert_yaml_snapshot!(exprs);
}

#[test]
fn test_function_declaration() {
    let decl = FnDecl {
        name: "add".into(),
        visibility: Visibility::Private,
        params: vec![
            Param { name: "x".into(), ty: Some(TypeExpr::Named { name: "Int".into(), span: (8, 11) }), span: (6, 11) },
            Param { name: "y".into(), ty: Some(TypeExpr::Named { name: "Int".into(), span: (14, 17) }), span: (12, 17) },
        ],
        constraints: vec![],
        return_type: Some(TypeExpr::Named { name: "Int".into(), span: (19, 22) }),
        body: Box::new(Expr::BinaryOp {
            op: BinOp::Add,
            lhs: Box::new(Expr::Var { name: "x".into(), span: (25, 26) }),
            rhs: Box::new(Expr::Var { name: "y".into(), span: (27, 28) }),
            span: (23, 29),
        }),
        span: (0, 30),
    };
    assert_yaml_snapshot!(decl);
}

#[test]
fn test_type_declaration_record() {
    let decl = TypeDecl {
        name: "Point".into(),
        visibility: Visibility::Private,
        type_params: vec![],
        kind: TypeDeclKind::Record {
            fields: vec![
                ("x".into(), TypeExpr::Named { name: "Int".into(), span: (20, 23) }),
                ("y".into(), TypeExpr::Named { name: "Int".into(), span: (28, 31) }),
            ],
        },
        deriving: vec!["Eq".into(), "Show".into()],
        span: (0, 40),
    };
    assert_yaml_snapshot!(decl);
}

#[test]
fn test_sum_type_with_deriving() {
    let decl = TypeDecl {
        name: "Option".into(),
        visibility: Visibility::Private,
        type_params: vec!["a".into()],
        kind: TypeDeclKind::Sum {
            variants: vec![
                Variant {
                    name: "Some".into(),
                    fields: vec![TypeExpr::Var { name: "a".into(), span: (20, 21) }],
                    span: (15, 22),
                },
                Variant {
                    name: "None".into(),
                    fields: vec![],
                    span: (25, 29),
                },
            ],
        },
        deriving: vec!["Eq".into(), "Show".into()],
        span: (0, 50),
    };
    assert_yaml_snapshot!(decl);
}

#[test]
fn test_pattern_match() {
    let s = (0, 0);
    let expr = Expr::Match {
        scrutinee: Box::new(Expr::Var { name: "opt".into(), span: (7, 10) }),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".into(),
                    args: vec![Pattern::Var { name: "x".into(), span: (17, 18) }],
                    span: (12, 19),
                },
                guard: None,
                body: Expr::Var { name: "x".into(), span: (20, 21) },
                span: (12, 21),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".into(),
                    args: vec![],
                    span: (22, 26),
                },
                guard: None,
                body: Expr::Lit { value: Lit::Int(0), span: (27, 28) },
                span: (22, 28),
            },
            MatchArm {
                pattern: Pattern::Wildcard { span: s },
                guard: None,
                body: Expr::Lit { value: Lit::Int(-1), span: s },
                span: s,
            },
        ],
        span: (0, 30),
    };
    assert_yaml_snapshot!(expr);
}

#[test]
fn test_nested_arithmetic() {
    // (+ (* 2 3) (- 5 1))
    let expr = Expr::BinaryOp {
        op: BinOp::Add,
        lhs: Box::new(Expr::BinaryOp {
            op: BinOp::Mul,
            lhs: Box::new(Expr::Lit { value: Lit::Int(2), span: (5, 6) }),
            rhs: Box::new(Expr::Lit { value: Lit::Int(3), span: (7, 8) }),
            span: (2, 9),
        }),
        rhs: Box::new(Expr::BinaryOp {
            op: BinOp::Sub,
            lhs: Box::new(Expr::Lit { value: Lit::Int(5), span: (13, 14) }),
            rhs: Box::new(Expr::Lit { value: Lit::Int(1), span: (15, 16) }),
            span: (10, 17),
        }),
        span: (0, 18),
    };
    assert_yaml_snapshot!(expr);
}

#[test]
fn test_lambda_let_do_if() {
    let s = (0, 0);
    let exprs = vec![
        Expr::Lambda {
            params: vec![Param { name: "x".into(), ty: None, span: s }],
            return_type: None,
            body: Box::new(Expr::BinaryOp {
                op: BinOp::Add,
                lhs: Box::new(Expr::Var { name: "x".into(), span: s }),
                rhs: Box::new(Expr::Lit { value: Lit::Int(1), span: s }),
                span: s,
            }),
            span: s,
        },
        Expr::Let {
            name: "x".into(),
            value: Box::new(Expr::Lit { value: Lit::Int(42), span: s }),
            body: Some(Box::new(Expr::Var { name: "x".into(), span: s })),
            span: s,
        },
        Expr::Do {
            exprs: vec![
                Expr::Lit { value: Lit::Int(1), span: s },
                Expr::Lit { value: Lit::Int(2), span: s },
            ],
            span: s,
        },
        Expr::If {
            cond: Box::new(Expr::Lit { value: Lit::Bool(true), span: s }),
            then_: Box::new(Expr::Lit { value: Lit::Int(1), span: s }),
            else_: Box::new(Expr::Lit { value: Lit::Int(0), span: s }),
            span: s,
        },
    ];
    assert_yaml_snapshot!(exprs);
}

#[test]
fn test_full_module() {
    let s = (0, 0);
    let module = Module {
        decls: vec![
            Decl::DefType(TypeDecl {
                name: "Point".into(),
                visibility: Visibility::Private,
                type_params: vec![],
                kind: TypeDeclKind::Record {
                    fields: vec![
                        ("x".into(), TypeExpr::Named { name: "Int".into(), span: s }),
                        ("y".into(), TypeExpr::Named { name: "Int".into(), span: s }),
                    ],
                },
                deriving: vec!["Eq".into()],
                span: s,
            }),
            Decl::DefFn(FnDecl {
                name: "origin".into(),
                visibility: Visibility::Private,
                params: vec![],
                constraints: vec![],
                return_type: Some(TypeExpr::Named { name: "Point".into(), span: s }),
                body: Box::new(Expr::StructLit {
                    name: "Point".into(),
                    fields: vec![
                        ("x".into(), Expr::Lit { value: Lit::Int(0), span: s }),
                        ("y".into(), Expr::Lit { value: Lit::Int(0), span: s }),
                    ],
                    span: s,
                }),
                span: s,
            }),
            Decl::DefFn(FnDecl {
                name: "main".into(),
                visibility: Visibility::Private,
                params: vec![],
                constraints: vec![],
                return_type: Some(TypeExpr::Named { name: "Unit".into(), span: s }),
                body: Box::new(Expr::Do {
                    exprs: vec![
                        Expr::Let {
                            name: "p".into(),
                            value: Box::new(Expr::App {
                                func: Box::new(Expr::Var { name: "origin".into(), span: s }),
                                args: vec![],
                                span: s,
                            }),
                            body: None,
                            span: s,
                        },
                        Expr::FieldAccess {
                            expr: Box::new(Expr::Var { name: "p".into(), span: s }),
                            field: "x".into(),
                            span: s,
                        },
                    ],
                    span: s,
                }),
                span: s,
            }),
            Decl::Import {
                path: "std.io".into(),
                names: vec![ImportName { name: "println".into(), alias: None }],
                span: s,
            },
        ],
    };
    assert_yaml_snapshot!(module);
}

#[test]
fn test_extern_java_parsing() {
    let source = r#"(extern "java.lang.Math"
  (def abs [Int] Int)
  (def max [Int Int] Int)
)"#;
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "unexpected errors: {errors:?}");
    assert_yaml_snapshot!(module);
}
