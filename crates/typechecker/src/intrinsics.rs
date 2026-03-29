use crate::types::{Type, TypeEnv, TypeScheme, TypeVarGen};
use std::collections::HashMap;

pub fn register_intrinsics(env: &mut TypeEnv, gen: &mut TypeVarGen, is_core_module: bool) {
    // panic: forall a. fn(String) -> a
    let a = gen.fresh();
    env.bind_intrinsic_function(
        "panic".to_string(),
        TypeScheme {
            vars: vec![a],
            ty: Type::Fn(vec![Type::String], Box::new(Type::Var(a))),
            constraints: Vec::new(),
            var_names: HashMap::new(),
        },
    );

    // trait_dict: forall a b. fn(a) -> b  (pseudo-intrinsic for explicit dict references)
    {
        let a = gen.fresh();
        let b = gen.fresh();
        env.bind_intrinsic_function(
            "trait_dict".to_string(),
            TypeScheme {
                vars: vec![a, b],
                ty: Type::Fn(vec![Type::Var(a)], Box::new(Type::Var(b))),
                constraints: Vec::new(),
            var_names: HashMap::new(),
            },
        );
    }

    // __krypton_intrinsic: forall b. fn() -> b  (only available in core/ modules)
    if is_core_module {
        let b = gen.fresh();
        env.bind_intrinsic_function(
            "__krypton_intrinsic".to_string(),
            TypeScheme {
                vars: vec![b],
                ty: Type::Fn(vec![], Box::new(Type::Var(b))),
                constraints: Vec::new(),
            var_names: HashMap::new(),
            },
        );

        // is_null: forall a. fn(a) -> Bool  (only available in core/ modules)
        let a = gen.fresh();
        env.bind_intrinsic_function(
            "is_null".to_string(),
            TypeScheme {
                vars: vec![a],
                ty: Type::Fn(vec![Type::Var(a)], Box::new(Type::Bool)),
                constraints: Vec::new(),
            var_names: HashMap::new(),
            },
        );
    }
}
