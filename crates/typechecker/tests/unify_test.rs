use krypton_typechecker::types::{Substitution, Type, TypeVarGen};
use krypton_typechecker::unify::{unify, TypeError};

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
    let a = fresh_var(&mut gen); // Var(0)
    let mut subst = Substitution::new();

    let list_a = Type::Named("List".into(), vec![a.clone()]);
    let err = unify(&a, &list_a, &mut subst).unwrap_err();
    assert!(matches!(err, TypeError::InfiniteType { var: 0, .. }));
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
fn unify_own_vs_bare_fails() {
    let mut subst = Substitution::new();
    let t1 = Type::Own(Box::new(Type::Int));
    let err = unify(&t1, &Type::Int, &mut subst).unwrap_err();
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
