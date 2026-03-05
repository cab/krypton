use krypton_typechecker::types::*;

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
    let ty = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool));
    assert_eq!(ty.to_string(), "fn(Int, Int) -> Bool");
}

#[test]
fn display_var() {
    assert_eq!(Type::Var(0).to_string(), "a");
    assert_eq!(Type::Var(1).to_string(), "b");
}

#[test]
fn display_named() {
    let ty = Type::Named("List".into(), vec![Type::Int]);
    assert_eq!(ty.to_string(), "List<Int>");
}

#[test]
fn display_named_no_args() {
    let ty = Type::Named("Foo".into(), vec![]);
    assert_eq!(ty.to_string(), "Foo");
}

#[test]
fn display_own() {
    let ty = Type::Own(Box::new(Type::Int));
    assert_eq!(ty.to_string(), "own Int");
}

#[test]
fn display_tuple() {
    let ty = Type::Tuple(vec![Type::Int, Type::Bool]);
    assert_eq!(ty.to_string(), "(Int, Bool)");
}

#[test]
fn display_all_types_snapshot() {
    let types = vec![
        ("Int", Type::Int),
        ("Float", Type::Float),
        ("Bool", Type::Bool),
        ("String", Type::String),
        ("Unit", Type::Unit),
        (
            "Fn",
            Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
        ),
        ("Var", Type::Var(0)),
        ("Named", Type::Named("List".into(), vec![Type::Int])),
        ("Own", Type::Own(Box::new(Type::Int))),
        ("Tuple", Type::Tuple(vec![Type::Int, Type::Bool])),
    ];
    let output: String = types
        .iter()
        .map(|(label, ty)| format!("{}: {}", label, ty))
        .collect::<Vec<_>>()
        .join("\n");
    insta::assert_snapshot!(output, @r"
    Int: Int
    Float: Float
    Bool: Bool
    String: String
    Unit: Unit
    Fn: fn(Int, Int) -> Bool
    Var: a
    Named: List<Int>
    Own: own Int
    Tuple: (Int, Bool)
    ");
}

#[test]
fn substitute_fn_type() {
    // Fn([Var(a)], Var(a)) with {a -> Int} → Fn([Int], Int)
    let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0)));
    let sub = Substitution::bind(0, Type::Int);
    let result = sub.apply(&ty);
    assert_eq!(result, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
    assert_eq!(result.to_string(), "fn(Int) -> Int");
}

// ── 1b. Substitution composition and application ──

#[test]
fn empty_substitution_is_identity() {
    let sub = Substitution::new();
    let ty = Type::Var(0);
    assert_eq!(sub.apply(&ty), Type::Var(0));

    let complex = Type::Fn(vec![Type::Var(0)], Box::new(Type::Int));
    assert_eq!(sub.apply(&complex), complex);
}

#[test]
fn single_binding() {
    let sub = Substitution::bind(0, Type::Int);
    assert_eq!(sub.apply(&Type::Var(0)), Type::Int);
}

#[test]
fn substitution_composition() {
    // {a -> Var(b)} then {b -> Int} composed = {a -> Int, b -> Int}
    let s1 = Substitution::bind(0, Type::Var(1)); // a -> b
    let s2 = Substitution::bind(1, Type::Int); // b -> Int
    let composed = s2.compose(&s1);

    assert_eq!(composed.apply(&Type::Var(0)), Type::Int);
    assert_eq!(composed.apply(&Type::Var(1)), Type::Int);
}

#[test]
fn composed_equals_sequential() {
    let s1 = Substitution::bind(0, Type::Var(1)); // a -> b
    let s2 = Substitution::bind(1, Type::Int); // b -> Int
    let composed = s2.compose(&s1);

    let ty = Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1)));
    // Sequential: apply s1 first, then s2
    let sequential = s2.apply(&s1.apply(&ty));
    let via_composed = composed.apply(&ty);
    assert_eq!(via_composed, sequential);
}

#[test]
fn substitution_into_named() {
    let ty = Type::Named("List".into(), vec![Type::Var(0)]);
    let sub = Substitution::bind(0, Type::Int);
    let result = sub.apply(&ty);
    assert_eq!(result, Type::Named("List".into(), vec![Type::Int]));
}

#[test]
fn substitution_ignores_unrelated_vars() {
    let sub = Substitution::bind(0, Type::Int);
    assert_eq!(sub.apply(&Type::Var(1)), Type::Var(1));
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
    let scheme = TypeScheme {
        vars: vec![0, 1],
        ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1))),
    };
    insta::assert_snapshot!(scheme.to_string(), @"forall a b. fn(a) -> b");
}

#[test]
fn type_scheme_instantiate() {
    let scheme = TypeScheme {
        vars: vec![0, 1],
        ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(1))),
    };
    let mut gen = TypeVarGen::new();
    // Skip 0 and 1 so fresh vars are 2 and 3
    gen.fresh();
    gen.fresh();
    let instantiated = scheme.instantiate(&mut || gen.fresh());
    assert_eq!(
        instantiated,
        Type::Fn(vec![Type::Var(2)], Box::new(Type::Var(3)))
    );
}

// ── TypeVarGen ──

#[test]
fn type_var_gen_sequential() {
    let mut gen = TypeVarGen::new();
    assert_eq!(gen.fresh(), 0);
    assert_eq!(gen.fresh(), 1);
    assert_eq!(gen.fresh(), 2);
}

// ── apply_scheme ──

#[test]
fn apply_scheme_respects_quantified_vars() {
    let scheme = TypeScheme {
        vars: vec![0],
        ty: Type::Fn(vec![Type::Var(0), Type::Var(1)], Box::new(Type::Var(0))),
    };
    // Substituting {0 -> Int, 1 -> Bool}: var 0 is quantified so should NOT be substituted
    let s1 = Substitution::bind(0, Type::Int);
    let s2 = Substitution::bind(1, Type::Bool);
    let sub = s1.compose(&s2);
    let result = sub.apply_scheme(&scheme);
    assert_eq!(
        result.ty,
        Type::Fn(vec![Type::Var(0), Type::Bool], Box::new(Type::Var(0)))
    );
}
