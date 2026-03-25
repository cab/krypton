use std::collections::HashMap;

use krypton_ir::expr::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SwitchBranch};
use krypton_ir::lint::LintPass;
use krypton_ir::pass::IrPass;
use krypton_ir::{FnDef, FnId, InstanceDef, Module, TraitDef, TraitMethodDef, TraitName, Type, VarId};
use krypton_typechecker::types::TypeVarGen;

fn make_simple_module(functions: Vec<FnDef>, fn_names: HashMap<FnId, String>) -> Module {
    Module {
        name: "test".into(),
        structs: vec![],
        sum_types: vec![],
        functions,
        fn_names,
        extern_fns: vec![],
        extern_types: vec![],
        imported_fns: vec![],
        traits: vec![],
        instances: vec![],
        tuple_arities: std::collections::BTreeSet::new(),
        module_path: String::new(),
        fn_dict_requirements: std::collections::HashMap::new(),
        trait_method_fn_ids: std::collections::HashMap::new(),
    }
}

fn unit_atom() -> Expr {
    Expr {
        kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
        ty: Type::Unit,
    }
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
        HashMap::from([(FnId(0), "main".into())]),
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
        body: Expr {
            kind: ExprKind::Atom(Atom::Var(VarId(0))),
            ty: Type::Int,
        },
    };
    let main_fn = FnDef {
        id: FnId(1),
        name: "main".into(),
        params: vec![],
        return_type: Type::Int,
        body: Expr {
            kind: ExprKind::Let {
                bind: VarId(1),
                ty: Type::Int,
                value: SimpleExpr::Call {
                    func: FnId(0),
                    args: vec![Atom::Lit(Literal::Int(42))],
                },
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(1))),
                    ty: Type::Int,
                }),
            },
            ty: Type::Int,
        },
    };
    let module = make_simple_module(
        vec![func, main_fn],
        HashMap::from([(FnId(0), "callee".into()), (FnId(1), "main".into())]),
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
        body: Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: SimpleExpr::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                },
                body: Box::new(Expr {
                    kind: ExprKind::Let {
                        bind: VarId(0), // duplicate!
                        ty: Type::Int,
                        value: SimpleExpr::PrimOp {
                            op: PrimOp::AddInt,
                            args: vec![Atom::Lit(Literal::Int(3)), Atom::Lit(Literal::Int(4))],
                        },
                        body: Box::new(Expr {
                            kind: ExprKind::Atom(Atom::Var(VarId(0))),
                            ty: Type::Int,
                        }),
                    },
                    ty: Type::Int,
                }),
            },
            ty: Type::Int,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(err.message.contains("duplicate VarId"), "got: {}", err.message);
}

#[test]
fn join_point_used_as_value_is_error() {
    // LetJoin defines j0, then body uses j0 as a regular Atom::Var.
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Unit,
        body: Expr {
            kind: ExprKind::LetJoin {
                name: VarId(0),
                params: vec![],
                join_body: Box::new(unit_atom()),
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(0))), // using join point as value!
                    ty: Type::Unit,
                }),
                is_recur: false,
            },
            ty: Type::Unit,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
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
        body: Expr {
            kind: ExprKind::Jump {
                target: VarId(0), // not a join point
                args: vec![],
            },
            ty: Type::Unit,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(err.message.contains("not a join point"), "got: {}", err.message);
}

#[test]
fn call_to_unknown_fn_id_is_error() {
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Int,
        body: Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: SimpleExpr::Call {
                    func: FnId(99), // unknown!
                    args: vec![],
                },
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(0))),
                    ty: Type::Int,
                }),
            },
            ty: Type::Int,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(err.message.contains("unknown FnId(99)"), "got: {}", err.message);
}

#[test]
fn make_closure_unknown_fn_id_is_error() {
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Fn(vec![], Box::new(Type::Unit)),
        body: Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Fn(vec![], Box::new(Type::Unit)),
                value: SimpleExpr::MakeClosure {
                    func: FnId(99), // unknown!
                    captures: vec![],
                },
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(0))),
                    ty: Type::Fn(vec![], Box::new(Type::Unit)),
                }),
            },
            ty: Type::Fn(vec![], Box::new(Type::Unit)),
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(err.message.contains("unknown FnId(99)"), "got: {}", err.message);
}

#[test]
fn letrec_unknown_fn_id_is_error() {
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Unit,
        body: Expr {
            kind: ExprKind::LetRec {
                bindings: vec![(
                    VarId(0),
                    Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                    FnId(99), // unknown!
                    vec![],
                )],
                body: Box::new(unit_atom()),
            },
            ty: Type::Unit,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(err.message.contains("unknown FnId(99)"), "got: {}", err.message);
}

#[test]
fn primop_type_mismatch_is_error() {
    // AddInt should return Int, but we bind it as Bool.
    let func = FnDef {
        id: FnId(0),
        name: "bad".into(),
        params: vec![],
        return_type: Type::Bool,
        body: Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Bool, // wrong! AddInt returns Int
                value: SimpleExpr::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                },
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(0))),
                    ty: Type::Bool,
                }),
            },
            ty: Type::Bool,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
    );
    let err = LintPass.run(module).unwrap_err();
    assert!(err.message.contains("type mismatch"), "got: {}", err.message);
}

#[test]
fn well_formed_join_point_passes() {
    let func = FnDef {
        id: FnId(0),
        name: "good".into(),
        params: vec![],
        return_type: Type::Unit,
        body: Expr {
            kind: ExprKind::LetJoin {
                name: VarId(0),
                params: vec![(VarId(1), Type::Int)],
                join_body: Box::new(unit_atom()),
                body: Box::new(Expr {
                    kind: ExprKind::Jump {
                        target: VarId(0),
                        args: vec![Atom::Lit(Literal::Int(42))],
                    },
                    ty: Type::Unit,
                }),
                is_recur: false,
            },
            ty: Type::Unit,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "good".into())]),
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
        body: Expr {
            kind: ExprKind::LetJoin {
                name: VarId(0),
                params: vec![(VarId(1), Type::Int)],
                join_body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Var(VarId(1))),
                    ty: Type::Int,
                }),
                body: Box::new(Expr {
                    kind: ExprKind::Let {
                        bind: VarId(1), // same as join param — legal because param is out of scope
                        ty: Type::Int,
                        value: SimpleExpr::PrimOp {
                            op: PrimOp::AddInt,
                            args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                        },
                        body: Box::new(Expr {
                            kind: ExprKind::Jump {
                                target: VarId(0),
                                args: vec![Atom::Var(VarId(1))],
                            },
                            ty: Type::Int,
                        }),
                    },
                    ty: Type::Int,
                }),
                is_recur: false,
            },
            ty: Type::Int,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "good".into())]),
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
        body: Expr {
            kind: ExprKind::Switch {
                scrutinee: Atom::Var(VarId(0)),
                branches: vec![
                    SwitchBranch {
                        tag: 0,
                        bindings: vec![(VarId(1), Type::Int)],
                        body: Expr {
                            kind: ExprKind::Atom(Atom::Var(VarId(1))),
                            ty: Type::Int,
                        },
                    },
                    SwitchBranch {
                        tag: 1,
                        bindings: vec![(VarId(1), Type::Int)], // same VarId as branch 0
                        body: Expr {
                            kind: ExprKind::Atom(Atom::Var(VarId(1))),
                            ty: Type::Int,
                        },
                    },
                ],
                default: None,
            },
            ty: Type::Int,
        },
    };
    let module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "good".into())]),
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
        body: Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Named("Dict".into(), vec![]),
                value: SimpleExpr::GetDict {
                    trait_name: TraitName::new(String::new(), "NonexistentTrait".to_string()),
                    ty: Type::Int,
                },
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                    ty: Type::Unit,
                }),
            },
            ty: Type::Unit,
        },
    };
    let mut module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "bad".into())]),
    );
    module.traits.push(TraitDef {
        name: "Show".into(),
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
        body: Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Named("Dict".into(), vec![]),
                value: SimpleExpr::GetDict {
                    trait_name: TraitName::new("core/show".into(), "Show".into()),
                    ty: Type::Int,
                },
                body: Box::new(Expr {
                    kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                    ty: Type::Unit,
                }),
            },
            ty: Type::Unit,
        },
    };
    let mut module = make_simple_module(
        vec![func],
        HashMap::from([(FnId(0), "good".into())]),
    );
    module.traits.push(TraitDef {
        name: "Show".into(),
        type_var: TypeVarGen::new().fresh(),
        is_imported: false,
        methods: vec![],
    });
    module.instances.push(InstanceDef {
        trait_name: TraitName::new("core/show".into(), "Show".into()),
        target_type: Type::Int,
        target_type_name: "Int".into(),
        method_fn_ids: vec![],
        sub_dict_requirements: vec![],
        is_intrinsic: false,
        is_imported: false,
    });
    assert!(LintPass.run(module).is_ok());
}
