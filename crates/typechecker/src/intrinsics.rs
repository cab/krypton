use crate::types::{Type, TypeEnv, TypeScheme, TypeVarGen};
use std::collections::HashMap;

pub fn register_intrinsics(env: &mut TypeEnv, gen: &mut TypeVarGen, is_core_module: bool) {
    // panic, todo, unreachable: fn(String) -> Never
    let never_ty = Type::Named("Never".into(), vec![]);
    for name in &["panic", "todo", "unreachable"] {
        env.bind_intrinsic_function(
            name.to_string(),
            TypeScheme {
                vars: vec![],
                ty: Type::fn_consuming(vec![Type::String], never_ty.clone()),
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
                ty: Type::fn_consuming(vec![], Type::Var(b)),
                constraints: Vec::new(),
                var_names: HashMap::new(),
            },
        );
    }
}
