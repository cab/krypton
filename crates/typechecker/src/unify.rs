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
//!   fn → ~fn (multi-use satisfies single-use). Use at value-flow sites:
//!   argument → parameter, value → annotation, body → return type.
//!
//! - `join_types(a, b)` — peer merge at branch join points (if/match arms,
//!   list elements). Strips Own from either side to find the common type.
//!   join(~T, ~T) preserves Own; join(~T, T) strips it.

use std::collections::HashSet;

use crate::types;
use crate::types::{Substitution, Type, TypeVarId};
pub use crate::type_error::{TypeError, TypeErrorCode, SpannedTypeError, SecondaryLabel};

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
            params.iter().any(|p| occurs_in(var, p, subst)) || occurs_in(var, ret, subst)
        }
        Type::Named(_, args) => args.iter().any(|a| occurs_in(var, a, subst)),
        Type::App(ctor, args) => {
            occurs_in(var, ctor, subst) || args.iter().any(|a| occurs_in(var, a, subst))
        }
        Type::Own(inner) => occurs_in(var, inner, subst),
        Type::Tuple(elems) => elems.iter().any(|e| occurs_in(var, e, subst)),
        _ => false,
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

        // Bind type variable
        (Type::Var(a), _) => {
            if occurs_in(*a, &t2, subst) {
                return Err(TypeError::InfiniteType { var: *a, ty: t2 });
            }
            subst.insert(*a, t2);
            Ok(())
        }
        (_, Type::Var(b)) => {
            if occurs_in(*b, &t1, subst) {
                return Err(TypeError::InfiniteType { var: *b, ty: t1 });
            }
            subst.insert(*b, t1);
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
            for (a, b) in p1.iter().zip(p2.iter()) {
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
            let (ctor_fn, remaining) = types::decompose_fn_for_app(params, ret, args.len()).unwrap();
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

/// Directional coercion: allows Own(T) → T (drop ownership) but not T → Own(T) (fabrication).
/// Used at value-flow sites: arg→param, value→annotation, body→return.
///
/// Key rule: when expected is an unbound Var, strip Own before binding.
/// This means `fold(list, 0, f)` works (B = Int, not Own(Int)), but
/// `identity(owned_val)` returns T not ~T. Use explicit type app for the latter.
pub fn coerce_unify(actual: &Type, expected: &Type, subst: &mut Substitution) -> Result<(), TypeError> {
    let actual = walk(actual, subst);
    let expected = walk(expected, subst);

    // Same type variables — identity
    if let (Type::Var(a), Type::Var(b)) = (&actual, &expected) {
        if a == b {
            return Ok(());
        }
    }

    // Var on expected side: strip Own, then bind.
    // This prevents literals from poisoning type variables with Own.
    if let Type::Var(b) = &expected {
        if subst.get(*b).is_none() {
            let stripped = strip_own_shallow(&actual);
            // After stripping, if the result is the same var, it's identity (e.g., ~T → T)
            if let Type::Var(s) = &stripped {
                if s == b {
                    return Ok(());
                }
            }
            if occurs_in(*b, &stripped, subst) {
                return Err(TypeError::InfiniteType {
                    var: *b,
                    ty: stripped,
                });
            }
            subst.insert(*b, stripped);
            return Ok(());
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

    // Both Own: recurse on inner
    if let (Type::Own(a_inner), Type::Own(e_inner)) = (&actual, &expected) {
        return coerce_unify(a_inner, e_inner, subst);
    }

    // Own(T) → T: drop ownership (data types only, not fn)
    if let Type::Own(inner) = &actual {
        if !matches!(inner.as_ref(), Type::Fn(_, _)) {
            return coerce_unify(inner, &expected, subst);
        }
    }

    // fn → ~fn: multi-use function satisfies single-use requirement
    if let Type::Fn(..) = &actual {
        if let Type::Own(inner) = &expected {
            if let Type::Fn(..) = inner.as_ref() {
                return coerce_unify(&actual, inner, subst);
            }
        }
    }

    // Fn: contravariant params, covariant return
    if let (Type::Fn(params_a, ret_a), Type::Fn(params_b, ret_b)) = (&actual, &expected) {
        if params_a.len() != params_b.len() {
            return Err(TypeError::WrongArity {
                expected: params_b.len(),
                actual: params_a.len(),
            });
        }
        for (pa, pb) in params_a.iter().zip(params_b.iter()) {
            coerce_unify(pb, pa, subst)?; // FLIP: contravariant
        }
        return coerce_unify(ret_a, ret_b, subst); // covariant
    }

    // Named types: covariant (functional language, no mutation)
    if let (Type::Named(n1, args1), Type::Named(n2, args2)) = (&actual, &expected) {
        if n1 == n2 {
            if args1.len() != args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args2.len(),
                    actual: args1.len(),
                });
            }
            for (a, e) in args1.iter().zip(args2.iter()) {
                coerce_unify(a, e, subst)?;
            }
            return Ok(());
        }
    }

    // Tuple: covariant
    if let (Type::Tuple(elems_a), Type::Tuple(elems_b)) = (&actual, &expected) {
        if elems_a.len() != elems_b.len() {
            return Err(TypeError::WrongArity {
                expected: elems_b.len(),
                actual: elems_a.len(),
            });
        }
        for (a, b) in elems_a.iter().zip(elems_b.iter()) {
            coerce_unify(a, b, subst)?;
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

    // Fn types: join params and return element-wise
    if let (Type::Fn(params_a, ret_a), Type::Fn(params_b, ret_b)) = (&a, &b) {
        if params_a.len() != params_b.len() {
            return Err(TypeError::WrongArity {
                expected: params_a.len(),
                actual: params_b.len(),
            });
        }
        for (pa, pb) in params_a.iter().zip(params_b.iter()) {
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

/// Strip one level of Own for non-function types. Used by coerce_unify's Var rule.
fn strip_own_shallow(ty: &Type) -> Type {
    match ty {
        Type::Own(inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => *inner.clone(),
        other => other.clone(),
    }
}
