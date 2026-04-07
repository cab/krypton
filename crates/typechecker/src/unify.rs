//! Unification algorithms for the Krypton type system.
//!
//! Three functions, each for a different context:
//!
//! - `unify(t1, t2)` — symmetric structural unification. Use for internal
//!   constraints where neither side has priority (e.g., recursive function
//!   pre-binding, type annotation matching).
//!
//! - `coerce_unify(actual, expected)` — directional. Allows Own(T) → T
//!   (dropping ownership) but not T → Own(T) (fabrication). Also allows
//!   fn → ~fn (multi-use satisfies single-use), but rejects ~fn → fn with
//!   a specialized `FnCapabilityMismatch` (E0104) diagnostic. Use at
//!   value-flow sites: argument → parameter, value → annotation, body →
//!   return type.
//!
//! - `join_types(a, b)` — peer merge at branch join points (if/match arms,
//!   list elements). Strips Own from either side to find the common type.
//!   join(~T, ~T) preserves Own; join(~T, T) strips it.

use std::collections::HashSet;

pub use crate::type_error::{SecondaryLabel, SpannedTypeError, TypeError, TypeErrorCode};
use crate::types;
use crate::types::{QualifierState, Substitution, Type, TypeVarId};

/// Resolve type variable chains through the substitution.
fn walk(ty: &Type, subst: &Substitution) -> Type {
    let mut visiting = HashSet::new();
    let mut chain = Vec::new();
    walk_inner(ty, subst, &mut visiting, &mut chain)
}

fn walk_inner(
    ty: &Type,
    subst: &Substitution,
    visiting: &mut HashSet<TypeVarId>,
    chain: &mut Vec<TypeVarId>,
) -> Type {
    match ty {
        Type::Var(id) => match subst.get(*id) {
            Some(t) => {
                if !visiting.insert(*id) {
                    chain.push(*id);
                    panic!(
                        "substitution cycle detected in walk for type vars {:?}",
                        chain
                    );
                }
                chain.push(*id);
                let resolved = walk_inner(t, subst, visiting, chain);
                chain.pop();
                visiting.remove(id);
                resolved
            }
            None => ty.clone(),
        },
        _ => ty.clone(),
    }
}

/// Check if a type variable occurs in a type (after applying the substitution).
fn occurs_in(var: TypeVarId, ty: &Type, subst: &Substitution) -> bool {
    let ty = walk(ty, subst);
    match &ty {
        Type::Var(id) => *id == var,
        Type::Fn(params, ret) => {
            params.iter().any(|(_, p)| occurs_in(var, p, subst)) || occurs_in(var, ret, subst)
        }
        Type::Named(_, args) => args.iter().any(|a| occurs_in(var, a, subst)),
        Type::App(ctor, args) => {
            occurs_in(var, ctor, subst) || args.iter().any(|a| occurs_in(var, a, subst))
        }
        Type::Own(inner) => occurs_in(var, inner, subst),
        Type::MaybeOwn(_, inner) => occurs_in(var, inner, subst),
        Type::Tuple(elems) => elems.iter().any(|e| occurs_in(var, e, subst)),
        _ => false,
    }
}

/// Prepare a type for binding to a shared-bounded var in `unify`.
/// - MaybeOwn(q, T): force q = Shared, return T (defer_own artifact)
/// - Own(T): error — structural ownership can't be silently stripped
/// - other: return unchanged
fn prepare_rhs_for_shared_binding(
    var: TypeVarId,
    rhs: &Type,
    subst: &mut Substitution,
) -> Result<Type, TypeError> {
    match rhs {
        Type::MaybeOwn(q, inner) => {
            let root = subst.resolve_qual(*q);
            if matches!(
                subst.get_qualifier(*q),
                Some(QualifierState::Pending) | None
            ) {
                subst.force_shared(root)?;
            }
            Ok(*inner.clone())
        }
        Type::Own(_) => {
            // Structural Own meeting a shared var is a type mismatch.
            // This preserves Option[~String] vs Option[String] distinction.
            Err(TypeError::Mismatch {
                expected: Type::Var(var),
                actual: rhs.clone(),
            })
        }
        _ => Ok(rhs.clone()),
    }
}

/// Unify two types, mutating the substitution in place.
#[tracing::instrument(level = "trace", skip(subst))]
pub fn unify(t1: &Type, t2: &Type, subst: &mut Substitution) -> Result<(), TypeError> {
    let t1 = walk(t1, subst);
    let t2 = walk(t2, subst);

    match (&t1, &t2) {
        // Same type variables
        (Type::Var(a), Type::Var(b)) if a == b => Ok(()),

        // Bind type variable — with shared + MaybeOwn/Own awareness
        (Type::Var(a), _) => {
            let rhs = if subst.is_shared_var(*a) {
                prepare_rhs_for_shared_binding(*a, &t2, subst)?
            } else {
                t2.clone()
            };
            if occurs_in(*a, &rhs, subst) {
                return Err(TypeError::InfiniteType { var: *a, ty: rhs });
            }
            subst.insert(*a, rhs);
            Ok(())
        }
        (_, Type::Var(b)) => {
            let rhs = if subst.is_shared_var(*b) {
                prepare_rhs_for_shared_binding(*b, &t1, subst)?
            } else {
                t1.clone()
            };
            if occurs_in(*b, &rhs, subst) {
                return Err(TypeError::InfiniteType { var: *b, ty: rhs });
            }
            subst.insert(*b, rhs);
            Ok(())
        }

        // Primitives
        (Type::Int, Type::Int)
        | (Type::Float, Type::Float)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Unit, Type::Unit) => Ok(()),

        // Function types
        (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
            if p1.len() != p2.len() {
                return Err(TypeError::WrongArity {
                    expected: p1.len(),
                    actual: p2.len(),
                });
            }
            for (i, ((m1, a), (m2, b))) in p1.iter().zip(p2.iter()).enumerate() {
                if m1 != m2 {
                    return Err(TypeError::ParamModeMismatch {
                        expected: t1.clone(),
                        actual: t2.clone(),
                        param_index: i,
                        expected_mode: *m1,
                        actual_mode: *m2,
                    });
                }
                unify(a, b, subst)?;
            }
            unify(r1, r2, subst)
        }

        // Named types
        (Type::Named(n1, args1), Type::Named(n2, args2)) => {
            if n1 != n2 {
                return Err(TypeError::Mismatch {
                    expected: t1,
                    actual: t2,
                });
            }
            if args1.len() != args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args1.len(),
                    actual: args2.len(),
                });
            }
            for (a, b) in args1.iter().zip(args2.iter()) {
                unify(a, b, subst)?;
            }
            Ok(())
        }

        // Own types
        (Type::Own(a), Type::Own(b)) => unify(a, b, subst),

        // MaybeOwn structural cases
        (Type::MaybeOwn(q1, inner1), Type::MaybeOwn(q2, inner2)) => {
            subst.unify_qualifiers(*q1, *q2)?;
            unify(inner1, inner2, subst)
        }
        (Type::MaybeOwn(q, inner), Type::Own(other))
        | (Type::Own(other), Type::MaybeOwn(q, inner)) => {
            subst.confirm_affine(*q)?;
            unify(inner, other, subst)
        }
        (Type::MaybeOwn(_, inner), other) | (other, Type::MaybeOwn(_, inner)) => {
            unify(inner, other, subst)
        }

        // Type constructor application (HKT)
        (Type::App(ctor1, args1), Type::App(ctor2, args2)) => {
            unify(ctor1, ctor2, subst)?;
            if args1.len() != args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args1.len(),
                    actual: args2.len(),
                });
            }
            for (a, b) in args1.iter().zip(args2.iter()) {
                unify(a, b, subst)?;
            }
            Ok(())
        }
        // App(Var(f), args) vs Named(name, args2): bind f to the constructor
        (Type::App(ctor, args1), Type::Named(name, args2))
        | (Type::Named(name, args2), Type::App(ctor, args1)) => {
            // Unify the constructor with the zero-arg Named type (the constructor itself)
            unify(ctor, &Type::Named(name.clone(), vec![]), subst)?;
            if args1.len() != args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args1.len(),
                    actual: args2.len(),
                });
            }
            for (a, b) in args1.iter().zip(args2.iter()) {
                unify(a, b, subst)?;
            }
            Ok(())
        }

        // App(Var(f), [arg]) vs Fn(params, ret): bind f to partial fn constructor
        (Type::App(ctor, args), Type::Fn(params, ret))
        | (Type::Fn(params, ret), Type::App(ctor, args))
            if types::decompose_fn_for_app(params, ret, args.len()).is_some() =>
        {
            let (ctor_fn, remaining) =
                types::decompose_fn_for_app(params, ret, args.len()).unwrap();
            unify(ctor, &ctor_fn, subst)?;
            if remaining.len() != args.len() {
                return Err(TypeError::WrongArity {
                    expected: remaining.len(),
                    actual: args.len(),
                });
            }
            for (a, b) in args.iter().zip(remaining.iter()) {
                unify(a, b, subst)?;
            }
            Ok(())
        }

        // Tuple types
        (Type::Tuple(e1), Type::Tuple(e2)) => {
            if e1.len() != e2.len() {
                return Err(TypeError::WrongArity {
                    expected: e1.len(),
                    actual: e2.len(),
                });
            }
            for (a, b) in e1.iter().zip(e2.iter()) {
                unify(a, b, subst)?;
            }
            Ok(())
        }

        // Mismatch
        _ => Err(TypeError::Mismatch {
            expected: t1,
            actual: t2,
        }),
    }
}

/// Resolve a MaybeOwn type if its qualifier is decided.
fn resolve_maybe_own(ty: Type, subst: &Substitution) -> Type {
    match &ty {
        Type::MaybeOwn(q, inner) => {
            let resolved_q = subst.resolve_qual(*q);
            match subst.qualifiers_ref().get(&resolved_q) {
                Some(QualifierState::Affine) => Type::Own(inner.clone()),
                Some(QualifierState::Shared) => *inner.clone(),
                _ => ty,
            }
        }
        _ => ty,
    }
}

/// Directional coercion: allows Own(T) → T (drop ownership) but not T → Own(T) (fabrication).
/// Used at value-flow sites: arg→param, value→annotation, body→return.
///
/// When expected is an unbound Var and actual is Own(T):
/// - If the var is shared-bounded: strip Own, bind var = T
/// - If in_constructor position: absorb Own directly, bind var = ~T
/// - Otherwise: defer via MaybeOwn(fresh_q, T)
pub fn coerce_unify(
    actual: &Type,
    expected: &Type,
    subst: &mut Substitution,
) -> Result<(), TypeError> {
    coerce_unify_inner(actual, expected, subst, false)
}

fn coerce_unify_inner(
    actual: &Type,
    expected: &Type,
    subst: &mut Substitution,
    in_constructor: bool,
) -> Result<(), TypeError> {
    let actual = walk(actual, subst);
    let expected = walk(expected, subst);

    // Same type variables — identity
    if let (Type::Var(a), Type::Var(b)) = (&actual, &expected) {
        if a == b {
            return Ok(());
        }
    }

    // Var on expected side: handle Own/MaybeOwn binding with shared/constructor awareness.
    if let Type::Var(b) = &expected {
        if subst.get(*b).is_none() {
            match &actual {
                Type::Own(inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => {
                    if subst.is_shared_var(*b) {
                        // shared bound: strip Own, bind bare type T (not ~T)
                        let base = *inner.clone();
                        if let Type::Var(s) = &base {
                            if s == b {
                                return Ok(());
                            }
                        }
                        if occurs_in(*b, &base, subst) {
                            return Err(TypeError::InfiniteType {
                                var: *b,
                                ty: base,
                            });
                        }
                        subst.insert(*b, base);
                    } else if in_constructor {
                        // Inside constructor: absorb ~T directly (no MaybeOwn)
                        if occurs_in(*b, &actual, subst) {
                            return Err(TypeError::InfiniteType {
                                var: *b,
                                ty: actual,
                            });
                        }
                        subst.insert(*b, actual.clone());
                    } else {
                        // Bare position: defer via MaybeOwn
                        let q = subst.fresh_qual();
                        let base = *inner.clone();
                        if let Type::Var(s) = &base {
                            if s == b {
                                return Ok(());
                            }
                        }
                        if occurs_in(*b, &base, subst) {
                            return Err(TypeError::InfiniteType {
                                var: *b,
                                ty: base,
                            });
                        }
                        subst.insert(*b, Type::MaybeOwn(q, Box::new(base)));
                    }
                    return Ok(());
                }
                _ => {
                    if let Type::Var(s) = &actual {
                        if s == b {
                            return Ok(());
                        }
                    }
                    if occurs_in(*b, &actual, subst) {
                        return Err(TypeError::InfiniteType {
                            var: *b,
                            ty: actual,
                        });
                    }
                    subst.insert(*b, actual.clone());
                    return Ok(());
                }
            }
        }
        // b is bound — walk resolved it above, fall through to structural cases
    }

    // Var on actual side: standard HM binding via unify
    if let Type::Var(a) = &actual {
        if subst.get(*a).is_none() {
            if occurs_in(*a, &expected, subst) {
                return Err(TypeError::InfiniteType {
                    var: *a,
                    ty: expected,
                });
            }
            subst.insert(*a, expected);
            return Ok(());
        }
    }

    // Pending MaybeOwn on actual side
    if let Type::MaybeOwn(q, inner) = &actual {
        if matches!(
            subst.get_qualifier(*q),
            Some(QualifierState::Pending) | None
        ) {
            match &expected {
                Type::Own(_exp_inner) => {
                    subst.confirm_affine(*q)?;
                    let resolved_actual = resolve_maybe_own(actual.clone(), subst);
                    let resolved_expected = resolve_maybe_own(expected.clone(), subst);
                    return coerce_unify_inner(
                        &resolved_actual,
                        &resolved_expected,
                        subst,
                        in_constructor,
                    );
                }
                Type::MaybeOwn(q2, exp_inner) => {
                    subst.unify_qualifiers(*q, *q2)?;
                    return coerce_unify_inner(inner, exp_inner, subst, in_constructor);
                }
                _ => {
                    // Plain context: do NOT set Shared. Coerce inner against expected.
                    return coerce_unify_inner(inner, &expected, subst, in_constructor);
                }
            }
        }
    }

    // Pending MaybeOwn on expected side: coerce actual against the inner type.
    // Own(actual) is compatible with both Affine and Shared outcomes of q
    // (coerce_unify allows ~T → T), so we must NOT confirm q here.
    // Note: defer_own never wraps Fn, so ~fn rejection is unreachable here.
    if let Type::MaybeOwn(q, inner) = &expected {
        if matches!(
            subst.get_qualifier(*q),
            Some(QualifierState::Pending) | None
        ) {
            return coerce_unify_inner(&actual, inner, subst, in_constructor);
        }
    }

    // Both Own: recurse on inner
    if let (Type::Own(a_inner), Type::Own(e_inner)) = (&actual, &expected) {
        return coerce_unify_inner(a_inner, e_inner, subst, in_constructor);
    }

    // Own(T) → T: drop ownership (data types only, not fn)
    if let Type::Own(inner) = &actual {
        if !matches!(inner.as_ref(), Type::Fn(_, _)) {
            return coerce_unify_inner(inner, &expected, subst, in_constructor);
        }
    }

    // fn → ~fn: multi-use function satisfies single-use requirement
    if let Type::Fn(..) = &actual {
        if let Type::Own(inner) = &expected {
            if let Type::Fn(..) = inner.as_ref() {
                return coerce_unify_inner(&actual, inner, subst, in_constructor);
            }
        }
    }

    // ~fn → fn rejection: specialized closure-capability error (E0104 family).
    // A single-use closure cannot satisfy a multi-use function slot.
    if let Type::Own(actual_inner) = &actual {
        if matches!(actual_inner.as_ref(), Type::Fn(_, _))
            && matches!(&expected, Type::Fn(_, _))
        {
            return Err(TypeError::FnCapabilityMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            });
        }
    }

    // Fn: contravariant params, covariant return — stays in_constructor: false
    if let (Type::Fn(params_a, ret_a), Type::Fn(params_b, ret_b)) = (&actual, &expected) {
        if params_a.len() != params_b.len() {
            return Err(TypeError::WrongArity {
                expected: params_b.len(),
                actual: params_a.len(),
            });
        }
        for (i, ((ma, pa), (mb, pb))) in params_a.iter().zip(params_b.iter()).enumerate() {
            if ma != mb {
                return Err(TypeError::ParamModeMismatch {
                    expected: expected.clone(),
                    actual: actual.clone(),
                    param_index: i,
                    expected_mode: *mb,
                    actual_mode: *ma,
                });
            }
            coerce_unify_inner(pb, pa, subst, false)?; // FLIP: contravariant; fn positions are not constructor
        }
        return coerce_unify_inner(ret_a, ret_b, subst, false); // covariant
    }

    // Named types: covariant — recurse with in_constructor: true
    if let (Type::Named(n1, args1), Type::Named(n2, args2)) = (&actual, &expected) {
        if n1 == n2 {
            if args1.len() != args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args2.len(),
                    actual: args1.len(),
                });
            }
            for (a, e) in args1.iter().zip(args2.iter()) {
                coerce_unify_inner(a, e, subst, true)?; // inside constructor
            }
            return Ok(());
        }
    }

    // Tuple: covariant — recurse with in_constructor: true
    if let (Type::Tuple(elems_a), Type::Tuple(elems_b)) = (&actual, &expected) {
        if elems_a.len() != elems_b.len() {
            return Err(TypeError::WrongArity {
                expected: elems_b.len(),
                actual: elems_a.len(),
            });
        }
        for (a, b) in elems_a.iter().zip(elems_b.iter()) {
            coerce_unify_inner(a, b, subst, true)?; // inside constructor
        }
        return Ok(());
    }

    // T → ~T fabrication: ownership-specific error (E0104)
    if let Type::Own(inner) = &expected {
        if !matches!(inner.as_ref(), Type::Fn(_, _)) {
            return Err(TypeError::OwnershipMismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            });
        }
    }

    // Everything else: delegate to plain unify.
    // Pass expected first so Mismatch { expected, actual } labels are correct.
    unify(&expected, &actual, subst)
}

/// Join two peer types at a join site (if-branches, match arms, binop operands, list elements).
/// Strips Own from either side to find the common supertype:
///   join(Own(T), Own(T)) = unify inner, both Own → result can be Own
///   join(Own(T), T) = strip Own, unify → result is T
pub fn join_types(a: &Type, b: &Type, subst: &mut Substitution) -> Result<(), TypeError> {
    let a = walk(a, subst);
    let b = walk(b, subst);

    // Both Own: join inner types
    if let (Type::Own(a_inner), Type::Own(b_inner)) = (&a, &b) {
        return join_types(a_inner, b_inner, subst);
    }

    // One Own, one bare (non-fn): strip Own, join inner with bare.
    // This strips ownership from literals at join sites (e.g., match { Some(x) => x, None => 0 })
    // so that type vars are bound to bare types, not Own types.
    if let Type::Own(a_inner) = &a {
        if !matches!(a_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(a_inner, &b, subst);
        }
    }
    if let Type::Own(b_inner) = &b {
        if !matches!(b_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(&a, b_inner, subst);
        }
    }

    // MaybeOwn stripping — same as Own at join points
    if let Type::MaybeOwn(_, a_inner) = &a {
        if !matches!(a_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(a_inner, &b, subst);
        }
    }
    if let Type::MaybeOwn(_, b_inner) = &b {
        if !matches!(b_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(&a, b_inner, subst);
        }
    }

    // Fn types: join params and return element-wise
    if let (Type::Fn(params_a, ret_a), Type::Fn(params_b, ret_b)) = (&a, &b) {
        if params_a.len() != params_b.len() {
            return Err(TypeError::WrongArity {
                expected: params_a.len(),
                actual: params_b.len(),
            });
        }
        for ((_, pa), (_, pb)) in params_a.iter().zip(params_b.iter()) {
            join_types(pa, pb, subst)?;
        }
        return join_types(ret_a, ret_b, subst);
    }

    // Tuple: join element-wise
    if let (Type::Tuple(elems_a), Type::Tuple(elems_b)) = (&a, &b) {
        if elems_a.len() != elems_b.len() {
            return Err(TypeError::WrongArity {
                expected: elems_a.len(),
                actual: elems_b.len(),
            });
        }
        for (ea, eb) in elems_a.iter().zip(elems_b.iter()) {
            join_types(ea, eb, subst)?;
        }
        return Ok(());
    }

    // Named types: join args element-wise
    if let (Type::Named(n1, args1), Type::Named(n2, args2)) = (&a, &b) {
        if n1 == n2 {
            if args1.len() != args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args1.len(),
                    actual: args2.len(),
                });
            }
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                join_types(a1, a2, subst)?;
            }
            return Ok(());
        }
    }

    // No Own involved: regular unify
    unify(&a, &b, subst)
}

