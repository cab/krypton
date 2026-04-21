use krypton_typechecker::types::{QualifierState, Substitution, Type, TypeVarGen};
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

    let t1 = Type::fn_consuming(vec![Type::Int], a.clone());
    let t2 = Type::fn_consuming(vec![Type::Int], Type::Bool);
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
    let t1 = Type::fn_consuming(vec![Type::Int], Type::Bool);
    let t2 = Type::fn_consuming(vec![Type::Int, Type::Float], Type::Bool);
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
    let own_fn = Type::Own(Box::new(Type::fn_consuming(vec![], Type::Int)));
    let bare_fn = Type::fn_consuming(vec![], Type::Int);
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
fn coerce_own_to_var_binds_eagerly() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let mut subst = Substitution::new();
    // coerce_unify(Own(Int), Var(a)) binds a := Own(Int) directly; no MaybeOwn
    // metavariable is introduced for the non-`(x, x)` shape.
    assert!(coerce_unify(&Type::Own(Box::new(Type::Int)), &a, &mut subst, None).is_ok());
    assert_eq!(subst.apply(&a), Type::Own(Box::new(Type::Int)));
}

#[test]
fn coerce_own_to_var_then_own_own_structural() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let mut subst = Substitution::new();
    // coerce_unify(Own(Int), Var(a)) → a = Own(Int)
    assert!(coerce_unify(&Type::Own(Box::new(Type::Int)), &a, &mut subst, None).is_ok());
    // A follow-up coerce against Own(Int) succeeds via the (Own, Own) structural arm.
    assert!(coerce_unify(&a, &Type::Own(Box::new(Type::Int)), &mut subst, None).is_ok());
    assert_eq!(subst.apply(&a), Type::Own(Box::new(Type::Int)));
}

#[test]
fn coerce_bare_to_own_fails() {
    let mut subst = Substitution::new();
    // coerce_unify(Int, Own(Int)) → OwnershipMismatch (fabrication rejected)
    let err = coerce_unify(
        &Type::Int,
        &Type::Own(Box::new(Type::Int)),
        &mut subst,
        None,
    )
    .unwrap_err();
    assert!(matches!(err, TypeError::OwnershipMismatch { .. }));
}

#[test]
fn coerce_own_to_bare_rejected() {
    let mut subst = Substitution::new();
    // coerce_unify(Own(Int), Int) → rejected (no silent drop; linear-by-default
    // requires an explicit consume, per disposable.md §"No ~T → T coercion").
    let err = coerce_unify(
        &Type::Own(Box::new(Type::Int)),
        &Type::Int,
        &mut subst,
        None,
    )
    .unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn coerce_own_to_own_ok() {
    let mut subst = Substitution::new();
    // coerce_unify(Own(Int), Own(Int)) → OK
    assert!(coerce_unify(
        &Type::Own(Box::new(Type::Int)),
        &Type::Own(Box::new(Type::Int)),
        &mut subst,
        None,
    )
    .is_ok());
}

#[test]
fn coerce_fn_to_own_fn_ok() {
    let mut subst = Substitution::new();
    let bare_fn = Type::fn_consuming(vec![], Type::Int);
    let own_fn = Type::Own(Box::new(Type::fn_consuming(vec![], Type::Int)));
    // fn → ~fn coercion is OK
    assert!(coerce_unify(&bare_fn, &own_fn, &mut subst, None).is_ok());
}

#[test]
fn coerce_own_fn_to_bare_fn_fails() {
    let mut subst = Substitution::new();
    let bare_fn = Type::fn_consuming(vec![], Type::Int);
    let own_fn = Type::Own(Box::new(Type::fn_consuming(vec![], Type::Int)));
    // ~fn → fn rejected
    let err = coerce_unify(&own_fn, &bare_fn, &mut subst, None).unwrap_err();
    assert!(matches!(err, TypeError::FnCapabilityMismatch { .. }));
}

#[test]
fn coerce_fn_param_contravariant_preserves_own() {
    let mut gen = TypeVarGen::new();
    let a = fresh_var(&mut gen);
    let mut subst = Substitution::new();
    // coerce_unify(Fn([Own(Int)], Int), Fn([Var(a)], Int))
    // Fn params are contravariant: coerce_unify(pb, pa) → coerce_unify(Var(a), Own(Int))
    // Var(a) is on actual side, so it binds to Own(Int) without stripping.
    let fn_own_param = Type::fn_consuming(vec![Type::Own(Box::new(Type::Int))], Type::Int);
    let fn_var_param = Type::fn_consuming(vec![a.clone()], Type::Int);
    assert!(coerce_unify(&fn_own_param, &fn_var_param, &mut subst, None).is_ok());
    // Contravariant: Var on actual side preserves Own
    assert_eq!(subst.apply(&a), Type::Own(Box::new(Type::Int)));
}

// --- join_types tests ---

#[test]
fn join_own_own_preserves() {
    let mut subst = Substitution::new();
    // join_types(Own(Int), Own(Int)) → OK (preserves structure)
    assert!(join_types(
        &Type::Own(Box::new(Type::Int)),
        &Type::Own(Box::new(Type::Int)),
        &mut subst,
        None,
    )
    .is_ok());
}

#[test]
fn join_own_bare_strips() {
    let mut subst = Substitution::new();
    // join_types(Own(Int), Int) → OK (strips to common)
    assert!(join_types(
        &Type::Own(Box::new(Type::Int)),
        &Type::Int,
        &mut subst,
        None
    )
    .is_ok());
}

#[test]
fn join_bare_bare_ok() {
    let mut subst = Substitution::new();
    // join_types(Int, Int) → OK
    assert!(join_types(&Type::Int, &Type::Int, &mut subst, None).is_ok());
}

#[test]
fn join_own_maybeown_confirms_affine() {
    let mut subst = Substitution::new();
    let q = subst.fresh_qual();
    // Before: q is Pending
    assert_eq!(subst.get_qualifier(q), Some(&QualifierState::Pending));
    // join_types(Own(Int), MaybeOwn(q, Int)) → commits q to Affine
    assert!(join_types(
        &Type::Own(Box::new(Type::Int)),
        &Type::MaybeOwn(q, Box::new(Type::Int)),
        &mut subst,
        None,
    )
    .is_ok());
    assert_eq!(subst.get_qualifier(q), Some(&QualifierState::Affine));
}

#[test]
fn join_maybeown_own_confirms_affine() {
    let mut subst = Substitution::new();
    let q = subst.fresh_qual();
    assert_eq!(subst.get_qualifier(q), Some(&QualifierState::Pending));
    // Symmetric: join_types(MaybeOwn(q, Int), Own(Int)) → commits q to Affine
    assert!(join_types(
        &Type::MaybeOwn(q, Box::new(Type::Int)),
        &Type::Own(Box::new(Type::Int)),
        &mut subst,
        None,
    )
    .is_ok());
    assert_eq!(subst.get_qualifier(q), Some(&QualifierState::Affine));
}

#[test]
fn join_maybeown_maybeown_aliases() {
    let mut subst = Substitution::new();
    let q1 = subst.fresh_qual();
    let q2 = subst.fresh_qual();
    // join_types(MaybeOwn(q1, Int), MaybeOwn(q2, Int)) aliases q1/q2
    assert!(join_types(
        &Type::MaybeOwn(q1, Box::new(Type::Int)),
        &Type::MaybeOwn(q2, Box::new(Type::Int)),
        &mut subst,
        None,
    )
    .is_ok());
    // Now confirming q1 as Affine must propagate to q2 via alias.
    assert!(subst.confirm_affine(q1).is_ok());
    assert_eq!(subst.get_qualifier(q1), Some(&QualifierState::Affine));
    assert_eq!(subst.get_qualifier(q2), Some(&QualifierState::Affine));
}

#[test]
fn join_own_bare_int_still_strips() {
    // Regression guard: the new Own/MaybeOwn arms must not disturb the
    // existing (Own, bare) literal-strip join.
    let mut subst = Substitution::new();
    assert!(join_types(
        &Type::Own(Box::new(Type::Int)),
        &Type::Int,
        &mut subst,
        None,
    )
    .is_ok());
}

#[test]
fn mismatch_with_var_names() {
    use krypton_typechecker::unify::SpannedTypeError;

    let mut gen = TypeVarGen::new();
    let var_a = gen.fresh();
    let err = SpannedTypeError {
        error: Box::new(TypeError::Mismatch {
            expected: Type::fn_consuming(vec![Type::Var(var_a)], Type::Int),
            actual: Type::String,
        }),
        span: (0, 1),
        note: None,
        secondary_span: None,
        source_file: None,
        var_names: Some(vec![(var_a, "elem".to_string())]),
    };
    let msg = err.format_message();
    assert!(msg.contains("elem"), "expected user name 'elem' in: {msg}");
    assert!(
        msg.contains("(elem) -> Int"),
        "expected '(elem) -> Int' in: {msg}"
    );
}

#[test]
fn mismatch_without_var_names() {
    let err = krypton_typechecker::unify::SpannedTypeError {
        error: Box::new(TypeError::Mismatch {
            expected: Type::Int,
            actual: Type::String,
        }),
        span: (0, 1),
        note: None,
        secondary_span: None,
        source_file: None,
        var_names: None,
    };
    let msg = err.format_message();
    assert!(
        msg.contains("expected Int"),
        "expected 'expected Int' in: {msg}"
    );
    assert!(
        msg.contains("found String"),
        "expected 'found String' in: {msg}"
    );
}

// --- empty sum (Never) tests ---

use krypton_typechecker::type_registry::{TypeInfo, TypeKind, TypeRegistry};

fn registry_with_empty_sum(name: &str) -> TypeRegistry {
    let mut registry = TypeRegistry::new();
    let mut gen = TypeVarGen::new();
    registry.register_builtins(&mut gen);
    registry
        .register_type(TypeInfo {
            name: name.to_string(),
            type_params: vec![],
            type_param_vars: vec![],
            kind: TypeKind::Sum { variants: vec![] },
            lifts: None,
            is_prelude: false,
        })
        .unwrap();
    registry
}

#[test]
fn coerce_empty_sum_to_int() {
    let reg = registry_with_empty_sum("Never");
    let mut subst = Substitution::new();
    let never = Type::Named("Never".into(), vec![]);
    assert!(coerce_unify(&never, &Type::Int, &mut subst, Some(&reg)).is_ok());
}

#[test]
fn coerce_int_to_empty_sum_fails() {
    let reg = registry_with_empty_sum("Never");
    let mut subst = Substitution::new();
    let never = Type::Named("Never".into(), vec![]);
    let err = coerce_unify(&Type::Int, &never, &mut subst, Some(&reg)).unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
}

#[test]
fn coerce_empty_sum_to_var_no_bind() {
    let reg = registry_with_empty_sum("Never");
    let mut gen = TypeVarGen::new();
    let v_id = gen.fresh();
    let v = Type::Var(v_id);
    let mut subst = Substitution::new();
    let never = Type::Named("Never".into(), vec![]);
    assert!(coerce_unify(&never, &v, &mut subst, Some(&reg)).is_ok());
    assert!(subst.get(v_id).is_none(), "var should stay unbound");
}

#[test]
fn coerce_empty_sum_to_empty_sum() {
    let reg = registry_with_empty_sum("Never");
    let mut subst = Substitution::new();
    let never = Type::Named("Never".into(), vec![]);
    assert!(coerce_unify(&never, &never, &mut subst, Some(&reg)).is_ok());
}

#[test]
fn join_empty_sum_with_int() {
    let reg = registry_with_empty_sum("Never");
    let mut subst = Substitution::new();
    let never = Type::Named("Never".into(), vec![]);
    assert!(join_types(&never, &Type::Int, &mut subst, Some(&reg)).is_ok());
}

#[test]
fn join_int_with_empty_sum() {
    let reg = registry_with_empty_sum("Never");
    let mut subst = Substitution::new();
    let never = Type::Named("Never".into(), vec![]);
    assert!(join_types(&Type::Int, &never, &mut subst, Some(&reg)).is_ok());
}

#[test]
fn coerce_without_registry_no_rule() {
    let mut subst = Substitution::new();
    let never = Type::Named("Never".into(), vec![]);
    let err = coerce_unify(&never, &Type::Int, &mut subst, None).unwrap_err();
    assert!(matches!(err, TypeError::Mismatch { .. }));
}
