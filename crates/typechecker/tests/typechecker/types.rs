use krypton_typechecker::types::*;
use std::collections::HashMap;

// ── 1a. Types construct, substitute, and pretty-print ──

#[test]
fn display_primitives() {
    assert_eq!(Type::Int.to_string(), "Int");
    assert_eq!(Type::Float.to_string(), "Float");
    assert_eq!(Type::Bool.to_string(), "Bool");
    assert_eq!(Type::String.to_string(), "String");
    assert_eq!(Type::Unit.to_string(), "Unit");
}

#[test]
fn display_fn_type() {
    let ty = Type::fn_consuming(vec![Type::Int, Type::Int], Type::Bool);
    assert_eq!(ty.to_string(), "(Int, Int) -> Bool");
}

#[test]
fn type_fn_carries_param_modes() {
    let file_t = Type::Named("File".into(), vec![]);
    let ty = Type::Fn(
        vec![
            (ParamMode::Borrow, Type::Own(Box::new(file_t.clone()))),
            (ParamMode::Consume, Type::Int),
        ],
        Box::new(Type::Unit),
    );
    match &ty {
        Type::Fn(params, ret) => {
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].0, ParamMode::Borrow);
            assert_eq!(params[1].0, ParamMode::Consume);
            assert_eq!(**ret, Type::Unit);
        }
        _ => panic!("expected Type::Fn"),
    }
    assert_eq!(ty.to_string(), "(&~File, Int) -> Unit");
}

#[test]
fn type_fn_consuming_helper_default() {
    let ty = Type::fn_consuming(vec![Type::Int, Type::Bool], Type::Unit);
    match &ty {
        Type::Fn(params, _) => {
            assert!(params.iter().all(|(m, _)| *m == ParamMode::Consume));
            assert_eq!(params.len(), 2);
        }
        _ => panic!("expected Type::Fn"),
    }
}

#[test]
fn type_fn_display_borrow_slot() {
    let file_t = Type::Named("File".into(), vec![]);
    let borrow = Type::Fn(
        vec![(ParamMode::Borrow, Type::Own(Box::new(file_t.clone())))],
        Box::new(Type::Unit),
    );
    assert_eq!(borrow.to_string(), "(&~File) -> Unit");
    let consume = Type::Fn(
        vec![(ParamMode::Consume, Type::Own(Box::new(file_t)))],
        Box::new(Type::Unit),
    );
    assert_eq!(consume.to_string(), "(~File) -> Unit");
}

#[test]
fn display_var() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    assert_eq!(Type::Var(a).to_string(), "a");
    assert_eq!(Type::Var(b).to_string(), "b");
}

#[test]
fn display_named() {
    let ty = Type::Named("List".into(), vec![Type::Int]);
    assert_eq!(ty.to_string(), "List[Int]");
}

#[test]
fn display_named_no_args() {
    let ty = Type::Named("Foo".into(), vec![]);
    assert_eq!(ty.to_string(), "Foo");
}

#[test]
fn display_own() {
    let ty = Type::Own(Box::new(Type::Int));
    assert_eq!(ty.to_string(), "~Int");
}

#[test]
fn display_tuple() {
    let ty = Type::Tuple(vec![Type::Int, Type::Bool]);
    assert_eq!(ty.to_string(), "(Int, Bool)");
}

#[test]
fn display_all_types_snapshot() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let types = vec![
        ("Int", Type::Int),
        ("Float", Type::Float),
        ("Bool", Type::Bool),
        ("String", Type::String),
        ("Unit", Type::Unit),
        (
            "Fn",
            Type::fn_consuming(vec![Type::Int, Type::Int], Type::Bool),
        ),
        ("Var", Type::Var(a)),
        ("Named", Type::Named("List".into(), vec![Type::Int])),
        ("Own", Type::Own(Box::new(Type::Int))),
        ("Tuple", Type::Tuple(vec![Type::Int, Type::Bool])),
    ];
    let output: String = types
        .iter()
        .map(|(label, ty)| format!("{}: {}", label, ty))
        .collect::<Vec<_>>()
        .join("\n");
    insta::assert_snapshot!(output, @"
    Int: Int
    Float: Float
    Bool: Bool
    String: String
    Unit: Unit
    Fn: (Int, Int) -> Bool
    Var: a
    Named: List[Int]
    Own: ~Int
    Tuple: (Int, Bool)
    ");
}

#[test]
fn substitute_fn_type() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    // Fn([Var(a)], Var(a)) with {a -> Int} → Fn([Int], Int)
    let ty = Type::fn_consuming(vec![Type::Var(a)], Type::Var(a));
    let sub = Substitution::bind(a, Type::Int);
    let result = sub.apply(&ty);
    assert_eq!(result, Type::fn_consuming(vec![Type::Int], Type::Int));
    assert_eq!(result.to_string(), "(Int) -> Int");
}

// ── 1b. Substitution composition and application ──

#[test]
fn empty_substitution_is_identity() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let sub = Substitution::new();
    let ty = Type::Var(a);
    assert_eq!(sub.apply(&ty), Type::Var(a));

    let complex = Type::fn_consuming(vec![Type::Var(a)], Type::Int);
    assert_eq!(sub.apply(&complex), complex);
}

#[test]
fn single_binding() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let sub = Substitution::bind(a, Type::Int);
    assert_eq!(sub.apply(&Type::Var(a)), Type::Int);
}

#[test]
fn substitution_composition() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    // {a -> Var(b)} then {b -> Int} composed = {a -> Int, b -> Int}
    let s1 = Substitution::bind(a, Type::Var(b)); // a -> b
    let s2 = Substitution::bind(b, Type::Int); // b -> Int
    let composed = s2.compose(&s1);

    assert_eq!(composed.apply(&Type::Var(a)), Type::Int);
    assert_eq!(composed.apply(&Type::Var(b)), Type::Int);
}

#[test]
fn composed_equals_sequential() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    let s1 = Substitution::bind(a, Type::Var(b)); // a -> b
    let s2 = Substitution::bind(b, Type::Int); // b -> Int
    let composed = s2.compose(&s1);

    let ty = Type::fn_consuming(vec![Type::Var(a)], Type::Var(b));
    // Sequential: apply s1 first, then s2
    let sequential = s2.apply(&s1.apply(&ty));
    let via_composed = composed.apply(&ty);
    assert_eq!(via_composed, sequential);
}

#[test]
fn substitution_into_named() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let ty = Type::Named("List".into(), vec![Type::Var(a)]);
    let sub = Substitution::bind(a, Type::Int);
    let result = sub.apply(&ty);
    assert_eq!(result, Type::Named("List".into(), vec![Type::Int]));
}

#[test]
fn substitution_ignores_unrelated_vars() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    let sub = Substitution::bind(a, Type::Int);
    assert_eq!(sub.apply(&Type::Var(b)), Type::Var(b));
    assert_eq!(sub.apply(&Type::Bool), Type::Bool);
}

// ── 1c. TypeEnv scoping ──

#[test]
fn env_bind_and_lookup() {
    let mut env = TypeEnv::new();
    env.bind("x".into(), TypeScheme::mono(Type::Int));
    assert_eq!(env.lookup("x").unwrap().ty, Type::Int);
}

#[test]
fn env_lookup_missing() {
    let env = TypeEnv::new();
    assert!(env.lookup("x").is_none());
}

#[test]
fn env_scoped_binding() {
    let mut env = TypeEnv::new();
    env.push_scope();
    env.bind("x".into(), TypeScheme::mono(Type::Int));
    assert_eq!(env.lookup("x").unwrap().ty, Type::Int);
    env.pop_scope();
    assert!(env.lookup("x").is_none());
}

#[test]
fn env_shadowing() {
    let mut env = TypeEnv::new();
    env.bind("x".into(), TypeScheme::mono(Type::Int));
    env.push_scope();
    env.bind("x".into(), TypeScheme::mono(Type::Bool));
    assert_eq!(env.lookup("x").unwrap().ty, Type::Bool);
    env.pop_scope();
    assert_eq!(env.lookup("x").unwrap().ty, Type::Int);
}

// ── TypeScheme ──

#[test]
fn type_scheme_mono_display() {
    let scheme = TypeScheme::mono(Type::Int);
    assert_eq!(scheme.to_string(), "Int");
}

#[test]
fn type_scheme_poly_display() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    let scheme = TypeScheme {
        vars: vec![a, b],
        constraints: Vec::new(),
        ty: Type::fn_consuming(vec![Type::Var(a)], Type::Var(b)),
        var_names: HashMap::new(),
    };
    insta::assert_snapshot!(scheme.to_string(), @"forall a b. (a) -> b");
}

#[test]
fn type_scheme_instantiate() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    let scheme = TypeScheme {
        vars: vec![a, b],
        constraints: Vec::new(),
        ty: Type::fn_consuming(vec![Type::Var(a)], Type::Var(b)),
        var_names: HashMap::new(),
    };
    let instantiated = scheme.instantiate(&mut || gen.fresh());
    let c = gen.fresh(); // this is the 5th var (index 4), but we need the 3rd and 4th
                         // gen produced vars 2 and 3 during instantiate; var 4 is `c` above
                         // Instead, just check the structure: two fresh vars replaced a and b
    let _ = c;
    // Re-check: instantiate consumed vars 2,3 from gen. Verify the result has them.
    match &instantiated {
        Type::Fn(params, ret) => {
            // params[0] and ret should both be Var, and different from a,b
            match (&params[0].1, ret.as_ref()) {
                (Type::Var(v1), Type::Var(v2)) => {
                    assert_ne!(*v1, a);
                    assert_ne!(*v1, b);
                    assert_ne!(*v2, a);
                    assert_ne!(*v2, b);
                    assert_ne!(v1, v2);
                }
                _ => panic!("expected Var types"),
            }
        }
        _ => panic!("expected Fn type"),
    }
}

// ── TypeVarGen ──

#[test]
fn type_var_gen_sequential() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    let c = gen.fresh();
    // Each call produces a distinct ID
    assert_ne!(a, b);
    assert_ne!(b, c);
    assert_ne!(a, c);
}

// ── apply_scheme ──

#[test]
fn apply_scheme_respects_quantified_vars() {
    let mut gen = TypeVarGen::new();
    let a = gen.fresh();
    let b = gen.fresh();
    let scheme = TypeScheme {
        vars: vec![a],
        constraints: Vec::new(),
        ty: Type::fn_consuming(vec![Type::Var(a), Type::Var(b)], Type::Var(a)),
        var_names: HashMap::new(),
    };
    // Substituting {a -> Int, b -> Bool}: var a is quantified so should NOT be substituted
    let s1 = Substitution::bind(a, Type::Int);
    let s2 = Substitution::bind(b, Type::Bool);
    let sub = s1.compose(&s2);
    let result = sub.apply_scheme(&scheme);
    assert_eq!(
        result.ty,
        Type::fn_consuming(vec![Type::Var(a), Type::Bool], Type::Var(a))
    );
}
