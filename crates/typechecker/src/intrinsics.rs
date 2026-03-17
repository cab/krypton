use crate::types::{Type, TypeEnv, TypeScheme, TypeVarGen};

pub fn register_intrinsics(env: &mut TypeEnv, gen: &mut TypeVarGen, is_core_module: bool) {
    // panic: forall a. fn(String) -> a
    let a = gen.fresh();
    env.bind(
        "panic".to_string(),
        TypeScheme {
            vars: vec![a],
            ty: Type::Fn(vec![Type::String], Box::new(Type::Var(a))),
        },
    );

    // trait_dict: forall a b. fn(a) -> b  (pseudo-intrinsic for explicit dict references)
    {
        let a = gen.fresh();
        let b = gen.fresh();
        env.bind(
            "trait_dict".to_string(),
            TypeScheme {
                vars: vec![a, b],
                ty: Type::Fn(vec![Type::Var(a)], Box::new(Type::Var(b))),
            },
        );
    }

    // __krypton_intrinsic: forall b. fn() -> b  (only available in core/ modules)
    if is_core_module {
        let b = gen.fresh();
        env.bind(
            "__krypton_intrinsic".to_string(),
            TypeScheme {
                vars: vec![b],
                ty: Type::Fn(vec![], Box::new(Type::Var(b))),
            },
        );
    }
}
