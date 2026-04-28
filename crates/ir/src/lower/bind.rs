// Type-var binding logic shared between dict resolution and instance
// dispatch. `bind_type_vars` is the strict structural matcher;
// `bind_instance_target(s)` is the slightly looser top-level matcher
// used when an instance pattern carries more slots than the dispatch
// type (HKT method resolution). `ice_bind_conflict` wraps the
// underlying [`crate::BindConflict`] as a loud `LowerError` for the
// pin-conflict cases the typechecker is supposed to have authorized.

use rustc_hash::FxHashMap;

use krypton_typechecker::types::{self as types, Type, TypeVarId};

use super::LowerError;

/// Wrap a [`crate::BindConflict`] as a [`LowerError::InternalError`] carrying
/// the offending variable, its pre-existing binding, and the binding the
/// current match would have introduced. Used by `resolve_call_dicts`,
/// `resolve_dispatch_type_with_bindings`, and `lower_constrained_fn_as_value`
/// to turn typechecker-authorized pin conflicts into loud ICEs.
pub(super) fn ice_bind_conflict(where_: &str, bc: crate::BindConflict<Type>) -> LowerError {
    LowerError::InternalError(format!(
        "ICE: bind conflict in {}: var {:?} pinned to {:?} but pattern would bind it to {:?}",
        where_, bc.var, bc.existing, bc.proposed,
    ))
}

/// Match a type pattern against a concrete type to bind type variables.
/// Ported from codegen's `bind_type_vars` (calls.rs).
///
/// * `Ok(true)` — bindings extended (or already consistent); pattern matches.
/// * `Ok(false)` — structural mismatch.
/// * `Err(BindConflict)` — existing binding disagrees with what this match
///   would assign.
pub(super) fn bind_type_vars(
    pattern: &Type,
    actual: &Type,
    bindings: &mut FxHashMap<TypeVarId, Type>,
) -> Result<bool, crate::BindConflict<Type>> {
    match (pattern, actual) {
        (Type::Var(id), _) => match bindings.get(id) {
            Some(existing) => {
                if existing == actual {
                    Ok(true)
                } else {
                    Err(crate::BindConflict {
                        var: *id,
                        existing: Box::new(existing.clone()),
                        proposed: Box::new(actual.clone()),
                    })
                }
            }
            None => {
                bindings.insert(*id, actual.clone());
                Ok(true)
            }
        },
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) => {
            if p_name != a_name || p_args.len() != a_args.len() {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(a_args.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
            if p_params.len() != a_params.len() {
                return Ok(false);
            }
            for ((_, p), (_, a)) in p_params.iter().zip(a_params.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            bind_type_vars(p_ret, a_ret, bindings)
        }
        (Type::Tuple(p_elems), Type::Tuple(a_elems)) => {
            if p_elems.len() != a_elems.len() {
                return Ok(false);
            }
            for (p, a) in p_elems.iter().zip(a_elems.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Type::Own(p), Type::Own(a)) => bind_type_vars(p, a, bindings),
        (Type::Own(p), a) => bind_type_vars(p, a, bindings),
        (a, Type::Own(p)) => bind_type_vars(a, p, bindings),
        (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
            if !bind_type_vars(p_ctor, a_ctor, bindings)? {
                return Ok(false);
            }
            if p_args.len() != a_args.len() {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(a_args.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // HKT cross-arm: App(Var(f), [a]) vs Named("Box", [Int])
        // Partial application: when a_args.len() > p_args.len(), the prefix bakes
        // into the constructor (f = Named("Result", [String]) when pattern is
        // f[a] and actual is Result[String, Int]).
        (Type::App(p_ctor, p_args), Type::Named(a_name, a_args)) => {
            if p_args.len() > a_args.len() {
                return Ok(false);
            }
            let prefix_len = a_args.len() - p_args.len();
            let prefix: Vec<Type> = a_args[..prefix_len].to_vec();
            if !bind_type_vars(p_ctor, &Type::Named(a_name.clone(), prefix), bindings)? {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(a_args[prefix_len..].iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // HKT cross-arm: App(Var(f), [a]) vs Fn([Int], Int)
        (Type::App(p_ctor, p_args), Type::Fn(a_params, a_ret))
            if types::decompose_fn_for_app(a_params, a_ret, p_args.len()).is_some() =>
        {
            let (ctor_fn, remaining) =
                types::decompose_fn_for_app(a_params, a_ret, p_args.len()).unwrap();
            if !bind_type_vars(p_ctor, &ctor_fn, bindings)? {
                return Ok(false);
            }
            if remaining.len() != p_args.len() {
                return Ok(false);
            }
            for (p, a) in p_args.iter().zip(remaining.iter()) {
                if !bind_type_vars(p, a, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(pattern == actual),
    }
}

/// Match a single instance-target pattern against a dispatch type.
///
/// Instance patterns are stored in full form (e.g. `Map[Var(k), Var(anon)]`);
/// dispatch types may be partial (e.g. `Map[String]`) when HKT method
/// resolution binds the trait's type var to a partial constructor. At the
/// top level of a target type, a pattern with more slots than the actual
/// matches by zipping the prefix — trailing pattern slots stay unbound.
/// Nested types use strict [`bind_type_vars`].
pub(super) fn bind_instance_target(
    pattern: &Type,
    actual: &Type,
    bindings: &mut FxHashMap<TypeVarId, Type>,
) -> bool {
    match (pattern, actual) {
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args))
            if p_args.len() > a_args.len() =>
        {
            if p_name != a_name {
                return false;
            }
            for (p, a) in p_args.iter().take(a_args.len()).zip(a_args.iter()) {
                if !matches!(bind_type_vars(p, a, bindings), Ok(true)) {
                    return false;
                }
            }
            true
        }
        _ => matches!(bind_type_vars(pattern, actual, bindings), Ok(true)),
    }
}

/// Array-level counterpart to [`bind_instance_target`]: zips instance-target
/// tuples with dispatch tuples.
pub(super) fn bind_instance_targets(
    patterns: &[Type],
    dispatch_tys: &[Type],
    bindings: &mut FxHashMap<TypeVarId, Type>,
) -> bool {
    if patterns.len() != dispatch_tys.len() {
        return false;
    }
    patterns
        .iter()
        .zip(dispatch_tys.iter())
        .all(|(p, a)| bind_instance_target(p, a, bindings))
}
