use krypton_typechecker::types::{Substitution, Type, TypeVarGen};
use krypton_typechecker::unify::{coerce_unify, join_types, unify, TypeError};

fn fresh_var(gen: &mut TypeVarGen) -> Type {
    Type::Var(gen.fresh())
}

#[test]
fn unify_same_primitives() {
    let mut subst = Substitution::new();
    assert!(unify(&Type::Int, &Type::Int, &mut subst).is_ok());
    assert!(unify(&Type::Bool, &Type::Bool, &mut subst).is_ok());
    assert!(unify(&Type::Float, &Type::Float, &mut subst).is_ok());
    assert!(unify(&Type::String, &Type::String, &mut subst).is_ok());
    assert!(unify(&Type::Unit, &Type::Unit, &mut subst).is_ok());
}

#[test]
fn unify_different_primitives_fails() {
    let mut subst = Substitution::new();
    let err = unify(&Type::Int, &Type::Bool, &mut subst).unwrap_err();
    assert_eq!(
        err,
        TypeError::Mismatch {
            expected: Type::Int,
            actual: Type::Bool,
        }
    );
}

#[test]
fn unify_var_with_concrete() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let mut subst = Substitution::new();
    assert!(unify(&a, &Type::Int, &mut subst).is_ok());
    assert_eq!(subst.apply(&a), Type::Int);
}

#[test]
fn unify_fn_binds_return_var() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let mut subst = Substitution::new();

    let t1 = Type::Fn(vec![Type::Int], Box::new(a.clone()));
    let t2 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
    assert!(unify(&t1, &t2, &mut subst).is_ok());
    assert_eq!(subst.apply(&a), Type::Bool);
}

#[test]
fn unify_infinite_type_fails() {
    let mut gen = TypeVarGen::new();
    let a_id = gen.fresh();
    let a = Type::Var(a_id);
    let mut subst = Substitution::new();

    let list_a = Type::Named("List".into(), vec![a.clone()]);
    let err = unify(&a, &list_a, &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::InfiniteType { var, .. } if var == a_id));
}

#[test]
fn unify_fn_wrong_arity() {
    let mut subst = Substitution::new();
    let t1 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
    let t2 = Type::Fn(vec![Type::Int, Type::Float], Box::new(Type::Bool));
    let err = unify(&t1, &t2, &mut subst).unwrap_err();
    assert_eq!(
        err,
        TypeError::WrongArity {
            expected: 1,
            actual: 2,
        }
    );
}

#[test]
fn unify_var_with_var() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let b = fresh_var(&mut gen);
    let mut subst = Substitution::new();
    assert!(unify(&a, &b, &mut subst).is_ok());
    // One should be bound to the other
    let resolved_a = subst.apply(&a);
    let resolved_b = subst.apply(&b);
    assert_eq!(resolved_a, resolved_b);
}

#[test]
fn unify_named_different_args_fails() {
    let mut subst = Substitution::new();
    let t1 = Type::Named("List".into(), vec![Type::Int]);
    let t2 = Type::Named("List".into(), vec![Type::Bool]);
    let err = unify(&t1, &t2, &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn unify_named_different_names_fails() {
    let mut subst = Substitution::new();
    let t1 = Type::Named("List".into(), vec![Type::Int]);
    let t2 = Type::Named("Set".into(), vec![Type::Int]);
    let err = unify(&t1, &t2, &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn unify_own_same() {
    let mut subst = Substitution::new();
    let t1 = Type::Own(Box::new(Type::Int));
    let t2 = Type::Own(Box::new(Type::Int));
    assert!(unify(&t1, &t2, &mut subst).is_ok());
}

#[test]
fn unify_own_vs_bare_succeeds_for_non_fn() {
    let mut subst = Substitution::new();
    // Symmetric rule removed: own T vs T now fails in unify (handled by coerce_unify)
    let t1 = Type::Own(Box::new(Type::Int));
    let err = unify(&t1, &Type::Int, &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
    // own fn(...) vs fn(...) should still fail
    let own_fn = Type::Own(Box::new(Type::Fn(vec![], Box::new(Type::Int))));
    let bare_fn = Type::Fn(vec![], Box::new(Type::Int));
    let err = unify(&own_fn, &bare_fn, &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn unify_tuple_same() {
    let mut subst = Substitution::new();
    let t1 = Type::Tuple(vec![Type::Int, Type::Bool]);
    let t2 = Type::Tuple(vec![Type::Int, Type::Bool]);
    assert!(unify(&t1, &t2, &mut subst).is_ok());
}

#[test]
fn unify_tuple_wrong_arity() {
    let mut subst = Substitution::new();
    let t1 = Type::Tuple(vec![Type::Int]);
    let t2 = Type::Tuple(vec![Type::Int, Type::Bool]);
    let err = unify(&t1, &t2, &mut subst).unwrap_err();
    assert_eq!(
        err,
        TypeError::WrongArity {
            expected: 1,
            actual: 2,
        }
    );
}

#[test]
fn unify_transitive_vars() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let b = fresh_var(&mut gen);
    let mut subst = Substitution::new();

    // a ~ b, then b ~ Int → a should resolve to Int
    assert!(unify(&a, &b, &mut subst).is_ok());
    assert!(unify(&b, &Type::Int, &mut subst).is_ok());
    assert_eq!(subst.apply(&a), Type::Int);
}

// --- coerce_unify tests ---

#[test]
fn coerce_own_to_var_strips_own() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let mut subst = Substitution::new();
    // coerce_unify(Own(Int), Var(a)) → a = Int (strips Own)
    assert!(coerce_unify(&Type::Own(Box::new(Type::Int)), &a, &mut subst).is_ok());
    assert_eq!(subst.apply(&a), Type::Int);
}

#[test]
fn coerce_bare_to_own_fails() {
    let mut subst = Substitution::new();
    // coerce_unify(Int, Own(Int)) → OwnershipMismatch (fabrication rejected)
    let err = coerce_unify(&Type::Int, &Type::Own(Box::new(Type::Int)), &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::OwnershipMismatch { .. }));
}

#[test]
fn coerce_own_to_bare_ok() {
    let mut subst = Substitution::new();
    // coerce_unify(Own(Int), Int) → OK (drop ownership)
    assert!(coerce_unify(&Type::Own(Box::new(Type::Int)), &Type::Int, &mut subst).is_ok());
}

#[test]
fn coerce_own_to_own_ok() {
    let mut subst = Substitution::new();
    // coerce_unify(Own(Int), Own(Int)) → OK
    assert!(coerce_unify(&Type::Own(Box::new(Type::Int)), &Type::Own(Box::new(Type::Int)), &mut subst).is_ok());
}

#[test]
fn coerce_fn_to_own_fn_ok() {
    let mut subst = Substitution::new();
    let bare_fn = Type::Fn(vec![], Box::new(Type::Int));
    let own_fn = Type::Own(Box::new(Type::Fn(vec![], Box::new(Type::Int))));
    // fn → ~fn coercion is OK
    assert!(coerce_unify(&bare_fn, &own_fn, &mut subst).is_ok());
}

#[test]
fn coerce_own_fn_to_bare_fn_fails() {
    let mut subst = Substitution::new();
    let bare_fn = Type::Fn(vec![], Box::new(Type::Int));
    let own_fn = Type::Own(Box::new(Type::Fn(vec![], Box::new(Type::Int))));
    // ~fn → fn rejected
    let err = coerce_unify(&own_fn, &bare_fn, &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn coerce_fn_param_contravariant_preserves_own() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let mut subst = Substitution::new();
    // coerce_unify(Fn([Own(Int)], Int), Fn([Var(a)], Int))
    // Fn params are contravariant: coerce_unify(pb, pa) → coerce_unify(Var(a), Own(Int))
    // Var(a) is on actual side, so it binds to Own(Int) without stripping.
    let fn_own_param = Type::Fn(vec![Type::Own(Box::new(Type::Int))], Box::new(Type::Int));
    let fn_var_param = Type::Fn(vec![a.clone()], Box::new(Type::Int));
    assert!(coerce_unify(&fn_own_param, &fn_var_param, &mut subst).is_ok());
    // Contravariant: Var on actual side preserves Own
    assert_eq!(subst.apply(&a), Type::Own(Box::new(Type::Int)));
}

// --- join_types tests ---

#[test]
fn join_own_own_preserves() {
    let mut subst = Substitution::new();
    // join_types(Own(Int), Own(Int)) → OK (preserves structure)
    assert!(join_types(&Type::Own(Box::new(Type::Int)), &Type::Own(Box::new(Type::Int)), &mut subst).is_ok());
}

#[test]
fn join_own_bare_strips() {
    let mut subst = Substitution::new();
    // join_types(Own(Int), Int) → OK (strips to common)
    assert!(join_types(&Type::Own(Box::new(Type::Int)), &Type::Int, &mut subst).is_ok());
}

#[test]
fn join_bare_bare_ok() {
    let mut subst = Substitution::new();
    // join_types(Int, Int) → OK
    assert!(join_types(&Type::Int, &Type::Int, &mut subst).is_ok());
}
