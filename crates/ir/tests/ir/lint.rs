use std::collections::HashMap;

use krypton_ir::expr::{
    Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SimpleExprKind, SwitchBranch,
};
use krypton_ir::lint::LintPass;
use krypton_ir::pass::IrPass;
use krypton_ir::{
    CanonicalRef, FnDef, FnId, FnIdentity, InstanceDef, LocalSymbolKey, Module, ModulePath,
    TraitDef, TraitMethodDef, TraitName, Type, VarId,
};
use krypton_typechecker::types::TypeVarGen;

fn make_simple_module(functions: Vec<FnDef>, fn_identities: HashMap<FnId, FnIdentity>) -> Module {
    Module {
        name: "test".into(),
        structs: vec![],
        sum_types: vec![],
        functions,
        fn_identities,
        extern_fns: vec![],
        extern_types: vec![],
        extern_traits: vec![],
        imported_fns: vec![],
        traits: vec![],
        instances: vec![],
        tuple_arities: std::collections::BTreeSet::new(),
        module_path: ModulePath::new("test"),
        fn_dict_requirements: std::collections::HashMap::new(),
        fn_exit_closes: std::collections::HashMap::new(),
    }
}

fn expr(ty: Type, kind: ExprKind) -> Expr {
    Expr::new((0, 0), ty, kind)
}

fn simple(kind: SimpleExprKind) -> SimpleExpr {
    SimpleExpr::new((0, 0), kind)
}

fn unit_atom() -> Expr {
    expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit)))
}

#[test]
fn well_formed_module_passes() {
    let func = FnDef {
        id: FnId(0),
        name: "main".into(),
        params: vec![],
        return_type: Type::Unit,
        body: unit_atom(),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "main".to_string(),
            },
        )]),
    );
    assert!(LintPass.run(module).is_ok());
}

#[test]
fn well_formed_with_let_and_call() {
    let func = FnDef {
        id: FnId(0),
        name: "callee".into(),
        params: vec![(VarId(0), Type::Int)],
        return_type: Type::Int,
        body: expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(0)))),
    };
    let main_fn = FnDef {
        id: FnId(1),
        name: "main".into(),
        params: vec![],
        return_type: Type::Int,
        body: expr(
            Type::Int,
            ExprKind::Let {
                bind: VarId(1),
                ty: Type::Int,
                value: simple(SimpleExprKind::Call {
                    func: FnId(0),
                    args: vec![Atom::Lit(Literal::Int(42))],
                }),
                body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
            },
        ),
    };
    let module = make_simple_module(
        vec![func, main_fn],
        HashMap::from([
            (
                FnId(0),
                FnIdentity::Local {
                    name: "callee".to_string(),
                },
            ),
            (
                FnId(1),
                FnIdentity::Local {
                    name: "main".to_string(),
                },
            ),
        ]),
    );
    assert!(LintPass.run(module).is_ok());
}

#[test]
fn duplicate_var_id_is_error() {
    // Two Let bindings with the same VarId(0).
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Int,
        body: expr(
            Type::Int,
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: simple(SimpleExprKind::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                }),
                body: Box::new(expr(
                    Type::Int,
                    ExprKind::Let {
                        bind: VarId(0), // duplicate!
                        ty: Type::Int,
                        value: simple(SimpleExprKind::PrimOp {
                            op: PrimOp::AddInt,
                            args: vec![Atom::Lit(Literal::Int(3)), Atom::Lit(Literal::Int(4))],
                        }),
                        body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(0))))),
                    },
                )),
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(
        err.message.contains("duplicate VarId"),
        "got: {}",
        err.message
    );
}

#[test]
fn join_point_used_as_value_is_error() {
    // LetJoin defines j0, then body uses j0 as a regular Atom::Var.
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Unit,
        body: expr(
            Type::Unit,
            ExprKind::LetJoin {
                name: VarId(0),
                params: vec![],
                join_body: Box::new(unit_atom()),
                body: Box::new(expr(Type::Unit, ExprKind::Atom(Atom::Var(VarId(0))))),
                is_recur: false,
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(err.message.contains("join point"), "got: {}", err.message);
}

#[test]
fn jump_to_non_join_point_is_error() {
    // Jump to VarId(0) which is not defined by LetJoin.
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![(VarId(0), Type::Unit)],
        return_type: Type::Unit,
        body: expr(
            Type::Unit,
            ExprKind::Jump {
                target: VarId(0), // not a join point
                args: vec![],
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(
        err.message.contains("not a join point"),
        "got: {}",
        err.message
    );
}

#[test]
fn call_to_unknown_fn_id_is_error() {
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Int,
        body: expr(
            Type::Int,
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: simple(SimpleExprKind::Call {
                    func: FnId(99), // unknown!
                    args: vec![],
                }),
                body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(0))))),
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(
        err.message.contains("unknown FnId(99)"),
        "got: {}",
        err.message
    );
}

#[test]
fn make_closure_unknown_fn_id_is_error() {
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Fn(vec![], Box::new(Type::Unit)),
        body: expr(
            Type::Fn(vec![], Box::new(Type::Unit)),
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Fn(vec![], Box::new(Type::Unit)),
                value: simple(SimpleExprKind::MakeClosure {
                    func: FnId(99), // unknown!
                    captures: vec![],
                }),
                body: Box::new(expr(
                    Type::Fn(vec![], Box::new(Type::Unit)),
                    ExprKind::Atom(Atom::Var(VarId(0))),
                )),
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(
        err.message.contains("unknown FnId(99)"),
        "got: {}",
        err.message
    );
}

#[test]
fn letrec_unknown_fn_id_is_error() {
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Unit,
        body: expr(
            Type::Unit,
            ExprKind::LetRec {
                bindings: vec![(
                    VarId(0),
                    Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                    FnId(99), // unknown!
                    vec![],
                )],
                body: Box::new(unit_atom()),
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(
        err.message.contains("unknown FnId(99)"),
        "got: {}",
        err.message
    );
}

#[test]
fn primop_type_mismatch_is_error() {
    // AddInt should return Int, but we bind it as Bool.
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Bool,
        body: expr(
            Type::Bool,
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Bool, // wrong! AddInt returns Int
                value: simple(SimpleExprKind::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                }),
                body: Box::new(expr(Type::Bool, ExprKind::Atom(Atom::Var(VarId(0))))),
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(
        err.message.contains("type mismatch"),
        "got: {}",
        err.message
    );
}

#[test]
fn well_formed_join_point_passes() {
    let func = FnDef {
        id: FnId(0),
        name: "good".into(),
        params: vec![],
        return_type: Type::Unit,
        body: expr(
            Type::Unit,
            ExprKind::LetJoin {
                name: VarId(0),
                params: vec![(VarId(1), Type::Int)],
                join_body: Box::new(unit_atom()),
                body: Box::new(expr(
                    Type::Unit,
                    ExprKind::Jump {
                        target: VarId(0),
                        args: vec![Atom::Lit(Literal::Int(42))],
                    },
                )),
                is_recur: false,
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "good".to_string(),
            },
        )]),
    );
    assert!(LintPass.run(module).is_ok());
}

#[test]
fn letjoin_param_varid_reusable_in_body() {
    // LetJoin param v1 is scoped to join_body only, so re-binding v1 in body is valid.
    let func = FnDef {
        id: FnId(0),
        name: "good".into(),
        params: vec![],
        return_type: Type::Int,
        body: expr(
            Type::Int,
            ExprKind::LetJoin {
                name: VarId(0),
                params: vec![(VarId(1), Type::Int)],
                join_body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                body: Box::new(expr(
                    Type::Int,
                    ExprKind::Let {
                        bind: VarId(1), // same as join param — legal because param is out of scope
                        ty: Type::Int,
                        value: simple(SimpleExprKind::PrimOp {
                            op: PrimOp::AddInt,
                            args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                        }),
                        body: Box::new(expr(
                            Type::Int,
                            ExprKind::Jump {
                                target: VarId(0),
                                args: vec![Atom::Var(VarId(1))],
                            },
                        )),
                    },
                )),
                is_recur: false,
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "good".to_string(),
            },
        )]),
    );
    assert!(LintPass.run(module).is_ok());
}

#[test]
fn switch_branch_varid_reusable_across_branches() {
    // Each Switch branch's bindings are scoped to that branch, so reusing VarIds is valid.
    let func = FnDef {
        id: FnId(0),
        name: "good".into(),
        params: vec![(VarId(0), Type::Int)],
        return_type: Type::Int,
        body: expr(
            Type::Int,
            ExprKind::Switch {
                scrutinee: Atom::Var(VarId(0)),
                branches: vec![
                    SwitchBranch {
                        tag: 0,
                        bindings: vec![(VarId(1), Type::Int)],
                        body: expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1)))),
                    },
                    SwitchBranch {
                        tag: 1,
                        bindings: vec![(VarId(1), Type::Int)], // same VarId as branch 0
                        body: expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1)))),
                    },
                ],
                default: None,
            },
        ),
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "good".to_string(),
            },
        )]),
    );
    assert!(LintPass.run(module).is_ok());
}

#[test]
fn getdict_unknown_trait_is_error() {
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Unit,
        body: expr(
            Type::Unit,
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Named("Dict".into(), vec![]),
                value: simple(SimpleExprKind::GetDict {
                    instance_ref: CanonicalRef {
                        module: ModulePath::new("test"),
                        symbol: LocalSymbolKey::Instance {
                            trait_name: "NonexistentTrait".into(),
                            target_type: "Int".into(),
                        },
                    },
                    trait_name: TraitName::new("test".to_string(), "NonexistentTrait".to_string()),
                    target_types: vec![Type::Int],
                }),
                body: Box::new(unit_atom()),
            },
        ),
    };
    let mut module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "bad".to_string(),
            },
        )]),
    );
    module.traits.push(TraitDef {
        name: "Show".into(),
        trait_name: TraitName::new("core/show".into(), "Show".into()),
        type_var: TypeVarGen::new().fresh(),
        is_imported: false,
        methods: vec![TraitMethodDef {
            name: "show".into(),
            param_count: 1,
            param_types: vec![Type::Int],
            return_type: Type::String,
        }],
    });
    let result = LintPass.run(module);
    assert!(result.is_err());
    assert!(result.unwrap_err().message.contains("unknown trait"));
}

#[test]
fn getdict_valid_trait_and_instance_passes() {
    let func = FnDef {
        id: FnId(0),
        name: "good".into(),
        params: vec![],
        return_type: Type::Unit,
        body: expr(
            Type::Unit,
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Named("Dict".into(), vec![]),
                value: simple(SimpleExprKind::GetDict {
                    instance_ref: CanonicalRef {
                        module: ModulePath::new("core/show"),
                        symbol: LocalSymbolKey::Instance {
                            trait_name: "Show".into(),
                            target_type: "Int".into(),
                        },
                    },
                    trait_name: TraitName::new("core/show".into(), "Show".into()),
                    target_types: vec![Type::Int],
                }),
                body: Box::new(unit_atom()),
            },
        ),
    };
    let mut module = make_simple_module(
        vec![func],
        HashMap::from([(
            FnId(0),
            FnIdentity::Local {
                name: "good".to_string(),
            },
        )]),
    );
    module.traits.push(TraitDef {
        name: "Show".into(),
        trait_name: TraitName::new("core/show".into(), "Show".into()),
        type_var: TypeVarGen::new().fresh(),
        is_imported: false,
        methods: vec![],
    });
    module.instances.push(InstanceDef {
        trait_name: TraitName::new("core/show".into(), "Show".into()),
        target_types: vec![Type::Int],
        target_type_name: "Int".into(),
        method_fn_ids: vec![],
        sub_dict_requirements: vec![],
        is_intrinsic: false,
        is_imported: false,
    });
    assert!(LintPass.run(module).is_ok());
}
