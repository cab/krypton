use std::collections::HashMap;

use crate::trait_registry::freshen_type;
use crate::types::{Substitution, Type, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{coerce_unify, unify};

/// Check whether two parameter type tuples structurally overlap — i.e., whether
/// a substitution of type variables exists that makes them simultaneously equal.
///
/// Returns `false` if lengths differ. Otherwise freshens both sides into
/// separate var maps but a shared `TypeVarGen`, then unifies each position pair
/// in a single shared `Substitution`. Any unification failure → false.
pub fn types_overlap(a: &[Type], b: &[Type]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut gen = TypeVarGen::new();
    let mut a_map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
    let mut b_map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
    let a_fresh: Vec<Type> = a.iter().map(|t| freshen_type(t, &mut a_map, &mut gen)).collect();
    let b_fresh: Vec<Type> = b.iter().map(|t| freshen_type(t, &mut b_map, &mut gen)).collect();
    let mut subst = Substitution::new();
    for (x, y) in a_fresh.iter().zip(b_fresh.iter()) {
        if unify(x, y, &mut subst).is_err() {
            return false;
        }
    }
    true
}

/// Extract value-parameter types from a Type that is Fn (or ~Fn).
/// Returns None if the type is not a function.
pub fn fn_param_types(ty: &Type) -> Option<Vec<Type>> {
    match ty {
        Type::Fn(params, _) => Some(params.iter().map(|(_, ty)| ty.clone()).collect()),
        Type::Own(inner) => fn_param_types(inner),
        _ => None,
    }
}

pub struct OverloadArityMismatch {
    pub name: String,
    pub arities: Vec<(String, usize)>,
}

/// Returns `Err` if any two candidates have different value-parameter counts.
/// The error includes all (module, arity) pairs for diagnostic use.
pub fn check_overload_arity(
    name: &str,
    candidates: &[(String, usize)],
) -> Result<(), OverloadArityMismatch> {
    if let Some((_, first_arity)) = candidates.first() {
        if candidates.iter().any(|(_, a)| a != first_arity) {
            return Err(OverloadArityMismatch {
                name: name.to_string(),
                arities: candidates.to_vec(),
            });
        }
    }
    Ok(())
}

/// Result of a successful candidate match — carries the instantiated function
/// type and the local substitution so the caller can commit them without
/// re-instantiating.
pub struct CandidateMatch {
    pub instantiated_ty: Type,
    pub local_subst: Substitution,
}

/// Check whether a candidate function scheme matches the given argument types.
/// Instantiates the scheme with fresh type variables, then tries coerce_unify
/// for each arg/param pair in a fresh substitution. On success returns the
/// instantiated type and local substitution so the caller can commit them.
pub fn candidate_matches(
    scheme: &TypeScheme,
    arg_types: &[Type],
    gen: &mut TypeVarGen,
) -> Option<CandidateMatch> {
    let instantiated = scheme.instantiate(&mut || gen.fresh());
    let params = match fn_param_types(&instantiated) {
        Some(p) => p,
        None => return None,
    };
    if params.len() != arg_types.len() {
        return None;
    }
    let mut subst = Substitution::new();
    for (arg, param) in arg_types.iter().zip(params.iter()) {
        if coerce_unify(arg, param, &mut subst).is_err() {
            return None;
        }
    }
    Some(CandidateMatch {
        instantiated_ty: instantiated,
        local_subst: subst,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Type, TypeVarId};

    fn var(n: u32) -> Type {
        Type::Var(TypeVarId(n))
    }

    fn named(name: &str, args: Vec<Type>) -> Type {
        Type::Named(name.to_string(), args)
    }

    #[test]
    fn distinct_constructors() {
        let a = [named("Vec", vec![var(0)])];
        let b = [named("List", vec![var(0)])];
        assert!(!types_overlap(&a, &b));
    }

    #[test]
    fn var_unifies_with_named() {
        let a = [named("Vec", vec![var(0)])];
        let b = [var(0)];
        assert!(types_overlap(&a, &b));
    }

    #[test]
    fn distinct_second_param() {
        let a = [Type::Int, named("Format", vec![])];
        let b = [Type::Int, named("Locale", vec![])];
        assert!(!types_overlap(&a, &b));
    }

    #[test]
    fn concrete_unifies_with_var() {
        let a = [named("Vec", vec![Type::Int])];
        let b = [named("Vec", vec![var(0)])];
        assert!(types_overlap(&a, &b));
    }

    #[test]
    fn empty_params() {
        assert!(types_overlap(&[], &[]));
    }

    #[test]
    fn different_lengths() {
        let a = [Type::Int];
        let b = [Type::Int, Type::Int];
        assert!(!types_overlap(&a, &b));
    }

    #[test]
    fn two_vars_unify() {
        let a = [var(0)];
        let b = [var(1)];
        assert!(types_overlap(&a, &b));
    }

    #[test]
    fn shared_var_consistency() {
        // Same var in both positions of a — must unify with both Int and String,
        // which is impossible.
        let a = [var(0), var(0)];
        let b = [Type::Int, Type::String];
        assert!(!types_overlap(&a, &b));
    }

    #[test]
    fn all_same_arity() {
        let candidates = vec![("mod_a".to_string(), 2), ("mod_b".to_string(), 2)];
        assert!(check_overload_arity("foo", &candidates).is_ok());
    }

    #[test]
    fn mixed_arities() {
        let candidates = vec![("mod_a".to_string(), 2), ("mod_b".to_string(), 3)];
        let err = check_overload_arity("foo", &candidates).unwrap_err();
        assert_eq!(err.name, "foo");
        assert_eq!(err.arities.len(), 2);
    }

    #[test]
    fn single_candidate() {
        let candidates = vec![("mod_a".to_string(), 2)];
        assert!(check_overload_arity("foo", &candidates).is_ok());
    }

    #[test]
    fn empty() {
        assert!(check_overload_arity("foo", &[]).is_ok());
    }

    #[test]
    fn fn_param_types_extracts_params() {
        use crate::types::ParamMode;
        let ty = Type::Fn(
            vec![
                (ParamMode::Borrow, Type::Int),
                (ParamMode::Borrow, Type::String),
            ],
            Box::new(Type::Bool),
        );
        let params = fn_param_types(&ty).unwrap();
        assert_eq!(params, vec![Type::Int, Type::String]);
    }

    #[test]
    fn fn_param_types_not_fn() {
        assert!(fn_param_types(&Type::Int).is_none());
    }

    #[test]
    fn fn_param_types_zero_params() {
        let ty = Type::Fn(vec![], Box::new(Type::Unit));
        let params = fn_param_types(&ty).unwrap();
        assert!(params.is_empty());
    }
}
