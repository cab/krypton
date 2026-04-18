//! Unification algorithms for the Krypton type system.
//!
//! Three functions, each for a different context:
//!
//! - `unify(t1, t2)` — symmetric structural unification. Use for internal
//!   constraints where neither side has priority (e.g., recursive function
//!   pre-binding, type annotation matching).
//!
//! - `coerce_unify(actual, expected)` — directional. Rejects both T → Own(T)
//!   (fabrication) and Own(T) → T (silent drop) on the data path — linear-by-
//!   default requires explicit consume. Allows fn → ~fn (multi-use satisfies
//!   single-use), but rejects ~fn → fn with a specialized `FnCapabilityMismatch`
//!   (E0104) diagnostic. Use at value-flow sites: argument → parameter, value
//!   → annotation, body → return type.
//!
//! - `join_types(a, b)` — peer merge at branch join points (if/match arms,
//!   list elements). Strips Own from either side to find the common type.
//!   join(~T, ~T) preserves Own; join(~T, T) strips it.

use std::collections::HashSet;

pub use crate::type_error::{
    BareResourceContext, BorrowMisuseContext, SecondaryLabel, SpannedTypeError, TypeError,
    TypeErrorCode,
};
use crate::type_registry::TypeRegistry;
use crate::types;
use crate::types::{QualifierState, Substitution, Type, TypeVarId};

fn is_empty_sum_type(ty: &Type, registry: Option<&TypeRegistry>) -> bool {
    match ty {
        Type::Named(name, _) => registry.is_some_and(|r| r.is_empty_sum(name)),
        _ => false,
    }
}

/// Resolve type variable chains through the substitution.
pub(crate) fn walk(ty: &Type, subst: &Substitution) -> Type {
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
        Type::Shape(inner) => occurs_in(var, inner, subst),
        Type::MaybeOwn(_, inner) => occurs_in(var, inner, subst),
        Type::Tuple(elems) => elems.iter().any(|e| occurs_in(var, e, subst)),
        _ => false,
    }
}

/// Eagerly evaluate a `Shape` wrapper if its inner type is fully resolved.
fn resolve_shape(ty: Type, subst: &Substitution) -> Type {
    match ty {
        Type::Shape(inner) => subst.apply(&inner),
        other => other,
    }
}

/// Unify two types, mutating the substitution in place.
#[tracing::instrument(level = "trace", skip(subst))]
pub fn unify(t1: &Type, t2: &Type, subst: &mut Substitution) -> Result<(), TypeError> {
    let t1 = resolve_shape(walk(t1, subst), subst);
    let t2 = resolve_shape(walk(t2, subst), subst);

    match (&t1, &t2) {
        // Same type variables
        (Type::Var(a), Type::Var(b)) if a == b => Ok(()),

        // Bind type variable
        (Type::Var(a), _) => {
            if occurs_in(*a, &t2, subst) {
                return Err(TypeError::InfiniteType {
                    var: *a,
                    ty: t2.clone(),
                });
            }
            subst.insert(*a, t2.clone());
            Ok(())
        }
        (_, Type::Var(b)) => {
            if occurs_in(*b, &t1, subst) {
                return Err(TypeError::InfiniteType {
                    var: *b,
                    ty: t1.clone(),
                });
            }
            subst.insert(*b, t1.clone());
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

        // Shape: both sides are unresolved shapes — unify inners
        (Type::Shape(a), Type::Shape(b)) => unify(a, b, subst),
        // Shape vs concrete: unify the Shape inner with the other side
        (Type::Shape(inner), other) | (other, Type::Shape(inner)) => {
            unify(inner, other, subst)
        }

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
        // App(Var(f), args1) vs Named(name, args2): bind f to the (possibly partial)
        // Named constructor. When args2.len() > args1.len(), split off a prefix that
        // bakes into the constructor — mirrors the Fn partial-application rule above.
        // e.g. App(Var(f), [Int]) vs Result[String, Int] binds f = Named("Result", [String]).
        (Type::App(ctor, args1), Type::Named(name, args2))
        | (Type::Named(name, args2), Type::App(ctor, args1)) => {
            if args1.len() > args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args1.len(),
                    actual: args2.len(),
                });
            }
            let prefix_len = args2.len() - args1.len();
            let prefix: Vec<Type> = args2[..prefix_len].to_vec();
            unify(ctor, &Type::Named(name.clone(), prefix), subst)?;
            for (a, b) in args1.iter().zip(args2[prefix_len..].iter()) {
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

/// Directional coercion used at value-flow sites (arg→param, value→annotation,
/// body→return). Neither T → Own(T) (fabrication) nor Own(T) → T (silent drop)
/// is permitted on the data path: linear-by-default requires an explicit consume
/// to move from `~T` to `T`. The only preserved Own rules are `(Own, Own)`
/// structural recursion and the function-arrow `fn → ~fn` effect-polarity rule.
///
/// When expected is an unbound Var and actual is Own(T), bind β := Own(T)
/// eagerly regardless of constructor context (see `typechecker_DESIGN.md` §4.2).
/// The prior split that deferred via `MaybeOwn(fresh_q, T)` outside constructor
/// position is no longer needed for the four `let_*_{owned,shared}` shapes —
/// they are subsumed by eager binding plus the downstream coerce rules. The
/// `(x, x)` duplicate-use case still flows through the pre-existing `MaybeOwn`
/// consumer arms below, which remain intact.
pub fn coerce_unify(
    actual: &Type,
    expected: &Type,
    subst: &mut Substitution,
    registry: Option<&TypeRegistry>,
) -> Result<(), TypeError> {
    coerce_unify_inner(actual, expected, subst, false, registry)
}

/// Raw (unsubstituted) parameter metadata used by [`coerce_unify_arg`] to
/// emit targeted `BareTypeVarResourceArg` diagnostics when an unbound bare
/// type-variable slot absorbs an owned argument.
pub struct ArgCoerceCtx<'a> {
    pub raw_param_ty: Option<&'a Type>,
    pub is_constructor: bool,
    pub callee_name: Option<&'a str>,
    pub param_index: usize,
}

/// Arg-flavored entry point for [`coerce_unify`] that rejects the
/// `(raw: Var, actual: Own(_))` pair preemptively outside constructor
/// position. Centralizes the invariant that eager `β := Own(T)` binding
/// must not silently absorb `~T` into a bare `α` slot — every arg-coerce
/// site gets it automatically, so adding a new arg form cannot forget to
/// surface the `shape a` hint. The retarget companion in
/// `infer/retarget_bare_var_owned_arg` still covers the case where
/// downstream context pins the slot before this entry runs.
pub fn coerce_unify_arg(
    arg_ty: &Type,
    param_ty: &Type,
    ctx: &ArgCoerceCtx<'_>,
    subst: &mut Substitution,
    registry: Option<&TypeRegistry>,
) -> Result<(), TypeError> {
    if !ctx.is_constructor {
        if let Some(raw) = ctx.raw_param_ty {
            if matches!(raw, Type::Var(_))
                && matches!(walk(raw, subst), Type::Var(_))
                && matches!(walk(arg_ty, subst), Type::Own(_))
            {
                return Err(TypeError::BareTypeVarResourceArg {
                    callee_name: ctx.callee_name.map(|s| s.to_string()),
                    param_index: ctx.param_index,
                    param_ty: raw.clone(),
                    arg_ty: subst.apply(arg_ty),
                });
            }
        }
    }
    coerce_unify_inner(arg_ty, param_ty, subst, false, registry)
}

fn coerce_unify_inner(
    actual: &Type,
    expected: &Type,
    subst: &mut Substitution,
    in_constructor: bool,
    registry: Option<&TypeRegistry>,
) -> Result<(), TypeError> {
    let actual = resolve_shape(walk(actual, subst), subst);
    let expected = resolve_shape(walk(expected, subst), subst);

    // Same type variables — identity
    if let (Type::Var(a), Type::Var(b)) = (&actual, &expected) {
        if a == b {
            return Ok(());
        }
    }

    // Empty sum directional rule: an empty sum type flows into any expected type.
    if is_empty_sum_type(&actual, registry) {
        if let Type::Var(b) = &expected {
            if subst.get(*b).is_none() {
                return Ok(());
            }
        }
        return Ok(());
    }

    // Reverse direction: non-empty-sum actual against empty-sum expected is a mismatch.
    if is_empty_sum_type(&expected, registry) && !is_empty_sum_type(&actual, registry) {
        if !matches!(&actual, Type::Var(_)) {
            return Err(TypeError::Mismatch {
                expected: expected.clone(),
                actual: actual.clone(),
            });
        }
    }

    // Var on expected side: handle Own/MaybeOwn binding with constructor awareness.
    if let Type::Var(b) = &expected {
        if subst.get(*b).is_none() {
            match &actual {
                Type::Own(inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => {
                    // Eager Own-preserving binding: bind `β := Own(T)`
                    // regardless of `in_constructor`. See
                    // `typechecker_DESIGN.md` §4.2. The `(x, x)` case is the
                    // only shape that still needs `MaybeOwn` deferral (§5);
                    // that path is retained at the consumer arms below but no
                    // longer populated from this site.
                    //
                    // SOUNDNESS: the `actual = ~β, expected = β` self-reference
                    // arm below can only arise from instantiating a scheme of
                    // the shape `~α → α` (e.g. `fun view[t](x: ~t) -> t`),
                    // where both occurrences of `α` share the same fresh var
                    // id. Binding `β := Own(Var(β))` would trip the occurs
                    // check; accepting silently matches the scheme's intent.
                    // Any other caller reaching this arm is a compiler bug.
                    if let Type::Var(s) = inner.as_ref() {
                        if s == b {
                            debug_assert!(
                                subst.get(*s).is_none(),
                                "~β → β self-reference arm requires β unbound"
                            );
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
                        registry,
                    );
                }
                Type::MaybeOwn(q2, exp_inner) => {
                    subst.unify_qualifiers(*q, *q2)?;
                    return coerce_unify_inner(inner, exp_inner, subst, in_constructor, registry);
                }
                _ => {
                    // Plain context: do NOT set Shared. Coerce inner against expected.
                    return coerce_unify_inner(inner, &expected, subst, in_constructor, registry);
                }
            }
        }
    }

    // Pending MaybeOwn on expected side: coerce actual against the inner type.
    // We must NOT confirm q here: the `(Own, Own)` structural arm below or the
    // Var-side MaybeOwn deferral earlier may still succeed for an Own actual,
    // so committing q to Affine/Shared now would be premature.
    // Note: defer_own never wraps Fn, so ~fn rejection is unreachable here.
    if let Type::MaybeOwn(q, inner) = &expected {
        if matches!(
            subst.get_qualifier(*q),
            Some(QualifierState::Pending) | None
        ) {
            return coerce_unify_inner(&actual, inner, subst, in_constructor, registry);
        }
    }

    // Both Own: recurse on inner
    if let (Type::Own(a_inner), Type::Own(e_inner)) = (&actual, &expected) {
        return coerce_unify_inner(a_inner, e_inner, subst, in_constructor, registry);
    }

    // fn → ~fn: multi-use function satisfies single-use requirement
    if let Type::Fn(..) = &actual {
        if let Type::Own(inner) = &expected {
            if let Type::Fn(..) = inner.as_ref() {
                return coerce_unify_inner(&actual, inner, subst, in_constructor, registry);
            }
        }
    }

    // ~fn → fn rejection: specialized closure-capability error (E0104 family).
    // A single-use closure cannot satisfy a multi-use function slot.
    if let Type::Own(actual_inner) = &actual {
        if matches!(actual_inner.as_ref(), Type::Fn(_, _)) && matches!(&expected, Type::Fn(_, _)) {
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
            coerce_unify_inner(pb, pa, subst, false, registry)?; // FLIP: contravariant; fn positions are not constructor
        }
        return coerce_unify_inner(ret_a, ret_b, subst, false, registry); // covariant
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
                coerce_unify_inner(a, e, subst, true, registry)?; // inside constructor
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
            coerce_unify_inner(a, b, subst, true, registry)?; // inside constructor
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
pub fn join_types(
    a: &Type,
    b: &Type,
    subst: &mut Substitution,
    registry: Option<&TypeRegistry>,
) -> Result<(), TypeError> {
    let a = resolve_shape(walk(a, subst), subst);
    let b = resolve_shape(walk(b, subst), subst);

    // Empty sum is the identity for join: join(E, T) = T, join(T, E) = T.
    if is_empty_sum_type(&a, registry) {
        return Ok(());
    }
    if is_empty_sum_type(&b, registry) {
        return Ok(());
    }

    // Both Own: join inner types
    if let (Type::Own(a_inner), Type::Own(b_inner)) = (&a, &b) {
        return join_types(a_inner, b_inner, subst, registry);
    }

    // MaybeOwn + MaybeOwn: alias qualifiers so a later commit propagates.
    // `Fn`-inner is handled the same way — joining two `~fn` branches of an
    // `if` should preserve the deferred qualifier rather than falling through
    // to structural join which would drop it.
    if let (Type::MaybeOwn(q1, a_inner), Type::MaybeOwn(q2, b_inner)) = (&a, &b) {
        subst.unify_qualifiers(*q1, *q2)?;
        return join_types(a_inner, b_inner, subst, registry);
    }

    // Own + MaybeOwn: confirm qualifier as Affine, then recurse on inners.
    // Mirrors the unify arm so the annotation's `Own` wrapper is authoritative
    // over the deferred qualifier introduced at self-recursive call sites.
    // Applies to `Fn`-inner as well — joining `~fn` with a deferred `fn`
    // commits the qualifier before descending.
    if let (Type::Own(a_inner), Type::MaybeOwn(q, b_inner)) = (&a, &b) {
        subst.confirm_affine(*q)?;
        return join_types(a_inner, b_inner, subst, registry);
    }
    if let (Type::MaybeOwn(q, a_inner), Type::Own(b_inner)) = (&a, &b) {
        subst.confirm_affine(*q)?;
        return join_types(a_inner, b_inner, subst, registry);
    }

    // One Own, one bare (non-fn): strip Own, join inner with bare.
    // This strips ownership from literals at join sites (e.g., match { Some(x) => x, None => 0 })
    // so that type vars are bound to bare types, not Own types.
    if let Type::Own(a_inner) = &a {
        if !matches!(a_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(a_inner, &b, subst, registry);
        }
    }
    if let Type::Own(b_inner) = &b {
        if !matches!(b_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(&a, b_inner, subst, registry);
        }
    }

    // MaybeOwn stripping — same as Own at join points
    if let Type::MaybeOwn(_, a_inner) = &a {
        if !matches!(a_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(a_inner, &b, subst, registry);
        }
    }
    if let Type::MaybeOwn(_, b_inner) = &b {
        if !matches!(b_inner.as_ref(), Type::Fn(_, _)) {
            return join_types(&a, b_inner, subst, registry);
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
            join_types(pa, pb, subst, registry)?;
        }
        return join_types(ret_a, ret_b, subst, registry);
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
            join_types(ea, eb, subst, registry)?;
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
                join_types(a1, a2, subst, registry)?;
            }
            return Ok(());
        }
    }

    // No Own involved: regular unify
    unify(&a, &b, subst)
}
