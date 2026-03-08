use crate::types::{Type, TypeEnv, TypeScheme, TypeVarGen};

pub fn register_intrinsics(env: &mut TypeEnv, gen: &mut TypeVarGen) {
    // panic: forall a. fn(String) -> a
    let a = gen.fresh();
    env.bind("panic".to_string(), TypeScheme {
        vars: vec![a],
        ty: Type::Fn(vec![Type::String], Box::new(Type::Var(a))),
    });
}
