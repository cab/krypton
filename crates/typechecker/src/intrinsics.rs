use crate::types::{Type, TypeEnv, TypeScheme, TypeVarGen};

pub fn register_intrinsics(env: &mut TypeEnv, gen: &mut TypeVarGen) {
    // println: fn(String) -> Unit
    env.bind("println".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::String], Box::new(Type::Unit))
    ));

    // print: fn(String) -> Unit
    env.bind("print".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::String], Box::new(Type::Unit))
    ));

    // panic: forall a. fn(String) -> a
    let a = gen.fresh();
    env.bind("panic".to_string(), TypeScheme {
        vars: vec![a],
        ty: Type::Fn(vec![Type::String], Box::new(Type::Var(a))),
    });

    // to_float: fn(Int) -> Float
    env.bind("to_float".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::Int], Box::new(Type::Float))
    ));

    // to_int: fn(Float) -> Int
    env.bind("to_int".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::Float], Box::new(Type::Int))
    ));

    // int_to_string: fn(Int) -> String
    env.bind("int_to_string".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::Int], Box::new(Type::String))
    ));

    // float_to_string: fn(Float) -> String
    env.bind("float_to_string".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::Float], Box::new(Type::String))
    ));

    // string_concat: fn(String, String) -> String
    env.bind("string_concat".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::String, Type::String], Box::new(Type::String))
    ));

    // string_length: fn(String) -> Int
    env.bind("string_length".to_string(), TypeScheme::mono(
        Type::Fn(vec![Type::String], Box::new(Type::Int))
    ));
}
