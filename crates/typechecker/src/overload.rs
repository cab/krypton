use rustc_hash::FxHashMap;
use std::fmt::Write;

use crate::trait_registry::freshen_type;
use crate::types::{ParamMode, Substitution, Type, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{coerce_unify, unify};

/// Canonicalize a slice of parameter types into a stable string fingerprint.
/// Type variables are renumbered by first-appearance to `α0`, `α1`, ... so that
/// `Vec[a]` and `Vec[b]` produce the same fingerprint. No whitespace; every
/// qualifier (`Own`, `MaybeOwn`, `Shape`) is serialized deterministically.
///
/// Used as the input to `overload_hash` when mangling overload-sibling names.
pub fn canonical_type_string(tys: &[Type]) -> String {
    let mut vars: FxHashMap<TypeVarId, u32> = FxHashMap::default();
    let mut qvars: FxHashMap<crate::types::QualVarId, u32> = FxHashMap::default();
    let mut out = String::new();
    out.push('(');
    for (i, t) in tys.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write_canonical(&mut out, t, &mut vars, &mut qvars);
    }
    out.push(')');
    out
}

fn write_canonical(
    out: &mut String,
    ty: &Type,
    vars: &mut FxHashMap<TypeVarId, u32>,
    qvars: &mut FxHashMap<crate::types::QualVarId, u32>,
) {
    match ty {
        Type::Int => out.push_str("I"),
        Type::Float => out.push_str("F"),
        Type::Bool => out.push_str("B"),
        Type::String => out.push_str("S"),
        Type::Unit => out.push_str("U"),
        Type::FnHole => out.push_str("H"),
        Type::Var(v) => {
            let next = vars.len() as u32;
            let n = *vars.entry(*v).or_insert(next);
            let _ = write!(out, "α{}", n);
        }
        Type::Named(name, args) => {
            out.push_str("N:");
            out.push_str(name);
            if !args.is_empty() {
                out.push('[');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    write_canonical(out, a, vars, qvars);
                }
                out.push(']');
            }
        }
        Type::App(ctor, args) => {
            out.push_str("A(");
            write_canonical(out, ctor, vars, qvars);
            out.push('|');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_canonical(out, a, vars, qvars);
            }
            out.push(')');
        }
        Type::Tuple(elems) => {
            out.push_str("T(");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_canonical(out, e, vars, qvars);
            }
            out.push(')');
        }
        Type::Fn(params, ret) => {
            out.push_str("Fn(");
            for (i, (m, p)) in params.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                match m {
                    ParamMode::Consume => out.push_str("c:"),
                    ParamMode::Borrow => out.push_str("b:"),
                    ParamMode::ObservationalBorrow => out.push_str("o:"),
                }
                write_canonical(out, p, vars, qvars);
            }
            out.push_str("->");
            write_canonical(out, ret, vars, qvars);
            out.push(')');
        }
        Type::Own(inner) => {
            out.push('~');
            write_canonical(out, inner, vars, qvars);
        }
        Type::Shape(inner) => {
            out.push_str("Sh(");
            write_canonical(out, inner, vars, qvars);
            out.push(')');
        }
        Type::MaybeOwn(q, inner) => {
            let next = qvars.len() as u32;
            let n = *qvars.entry(*q).or_insert(next);
            let _ = write!(out, "M{}:", n);
            write_canonical(out, inner, vars, qvars);
        }
    }
}

/// FNV-1a 64-bit hash of UTF-8 bytes, rendered in full as 16 lowercase hex
/// digits. Used to mangle overload-sibling symbol names. Full-length output is
/// collision-free for any plausible overload group: distinct canonical forms
/// would require a 64-bit FNV-1a collision, which is not attainable from
/// realistic overload sibling counts. If adversarial robustness is ever a
/// concern the hash function is a drop-in change; the output encoding is
/// intentionally stable at 16 hex chars so downstream consumers (IR,
/// codegen, module interfaces) do not need to parse the width.
pub fn overload_hash(bytes: &str) -> String {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;
    let mut h: u64 = FNV_OFFSET;
    for b in bytes.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(FNV_PRIME);
    }
    format!("{:016x}", h)
}

/// Assign stable mangled names to a group of overload siblings that share a
/// bare `name`. Entries are sorted by `def_spans[i]` start offset (entries
/// without a span sort last, preserving their declaration order as a
/// tiebreaker). The earliest entry keeps the bare `name`; subsequent siblings
/// are suffixed with `_<hash16>` where the hash is the full 64-bit FNV-1a
/// digest (16 hex chars) over the canonical type-string of the entry's
/// parameter types.
///
/// Used by both `mangle_overload_symbols` (on `ExportedFnSummary`) and
/// TypedFnDecl mangling at end-of-typechecking so interface-export mangling
/// and AST mangling cannot diverge.
///
/// A duplicate mangled name within a sibling group implies two siblings share
/// the same canonical parameter types, which is an overlap the typechecker is
/// responsible for rejecting upstream. This invariant is asserted via
/// `debug_assert!` rather than a user-reachable panic: if it ever trips in
/// debug builds it points at a missing overlap check, not user error.
pub fn mangle_group(
    name: &str,
    params: &[Vec<Type>],
    def_spans: &[Option<krypton_parser::ast::Span>],
) -> Vec<String> {
    assert_eq!(
        params.len(),
        def_spans.len(),
        "ICE: mangle_group: params and def_spans length mismatch",
    );
    let n = params.len();
    if n == 0 {
        return vec![];
    }
    if n == 1 {
        return vec![name.to_string()];
    }

    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&i| {
        (
            def_spans[i].map(|(start, _)| start).unwrap_or(usize::MAX),
            i,
        )
    });

    let mut out = vec![String::new(); n];
    let mut seen_mangled: FxHashMap<String, usize> = FxHashMap::default();
    for (rank, idx) in order.iter().enumerate() {
        let mangled = if rank == 0 {
            name.to_string()
        } else {
            let canon = canonical_type_string(&params[*idx]);
            format!("{name}_{}", overload_hash(&canon))
        };
        debug_assert!(
            !seen_mangled.contains_key(&mangled),
            "ICE: mangle_group produced duplicate mangled name `{}` in sibling set \
             for `{}` (siblings #{} and #{}) — upstream overlap check should have \
             rejected this",
            mangled,
            name,
            seen_mangled.get(&mangled).copied().unwrap_or(usize::MAX),
            idx,
        );
        seen_mangled.insert(mangled.clone(), *idx);
        out[*idx] = mangled;
    }
    out
}

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
    let mut a_map: FxHashMap<TypeVarId, TypeVarId> = FxHashMap::default();
    let mut b_map: FxHashMap<TypeVarId, TypeVarId> = FxHashMap::default();
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
        if coerce_unify(arg, param, &mut subst, None).is_err() {
            return None;
        }
    }
    Some(CandidateMatch {
        instantiated_ty: instantiated,
        local_subst: subst,
    })
}

/// Check whether a candidate function scheme matches a given expected type.
/// Instantiates the scheme with fresh type variables, then tries coerce_unify
/// against the whole expected type. On success returns the instantiated type
/// and local substitution so the caller can commit them.
pub fn candidate_matches_expected_type(
    scheme: &TypeScheme,
    expected: &Type,
    gen: &mut TypeVarGen,
) -> Option<CandidateMatch> {
    let instantiated = scheme.instantiate(&mut || gen.fresh());
    let mut subst = Substitution::new();
    if coerce_unify(&instantiated, expected, &mut subst, None).is_err() {
        return None;
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

    #[test]
    fn expected_type_matching_concrete() {
        use crate::types::{ParamMode, TypeScheme};
        let scheme = TypeScheme::mono(Type::Fn(
            vec![(ParamMode::Borrow, named("Vec", vec![Type::Int]))],
            Box::new(Type::Int),
        ));
        let expected = Type::Fn(
            vec![(ParamMode::Borrow, named("Vec", vec![Type::Int]))],
            Box::new(Type::Int),
        );
        let mut gen = TypeVarGen::new();
        assert!(candidate_matches_expected_type(&scheme, &expected, &mut gen).is_some());
    }

    #[test]
    fn expected_type_non_matching() {
        use crate::types::{ParamMode, TypeScheme};
        let scheme = TypeScheme::mono(Type::Fn(
            vec![(ParamMode::Borrow, named("List", vec![Type::Int]))],
            Box::new(Type::Int),
        ));
        let expected = Type::Fn(
            vec![(ParamMode::Borrow, named("Vec", vec![Type::Int]))],
            Box::new(Type::Int),
        );
        let mut gen = TypeVarGen::new();
        assert!(candidate_matches_expected_type(&scheme, &expected, &mut gen).is_none());
    }

    #[test]
    fn expected_type_generic_scheme() {
        use crate::types::{ParamMode, TypeScheme};
        use rustc_hash::FxHashMap;
        let a = TypeVarId(100);
        let scheme = TypeScheme {
            vars: vec![a],
            constraints: vec![],
            ty: Type::Fn(
                vec![(ParamMode::Borrow, named("Vec", vec![Type::Var(a)]))],
                Box::new(Type::Int),
            ),
            var_names: FxHashMap::default(),
        };
        let expected = Type::Fn(
            vec![(ParamMode::Borrow, named("Vec", vec![Type::Int]))],
            Box::new(Type::Int),
        );
        let mut gen = TypeVarGen::new();
        assert!(candidate_matches_expected_type(&scheme, &expected, &mut gen).is_some());
    }
}
