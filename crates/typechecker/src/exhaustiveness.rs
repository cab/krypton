use std::collections::HashSet;

use krypton_parser::ast::{Lit, Span};

use crate::type_registry::{TypeKind, TypeRegistry};
use crate::typed_ast::{TypedMatchArm, TypedPattern};
use crate::types::Type;
use crate::unify::{SpannedTypeError, TypeError};

/// Maximum constructor expansion depth. Beyond this, types are treated as
/// infinite (like Int/String). This bounds recursion for recursive types
/// like List where Cons(a, List[a]) would otherwise expand forever.
/// This is the same approach used by GHC and rustc.
const MAX_DEPTH: usize = 20;

/// A constructor in the pattern matrix.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Con {
    Variant(String),
    BoolLit(bool),
    Literal(String),
    Tuple(usize),
    Record(String),
}

/// Internal pattern representation for the matrix algorithm.
#[derive(Clone, Debug)]
enum Pat {
    Con(Con, Vec<Pat>),
    Wild,
}

/// Expand a top-level pattern into multiple Pat rows (for or-patterns).
/// Non-or patterns produce a single row. Or-patterns produce one row per alternative.
/// Nested or-patterns inside constructors are expanded recursively.
fn convert_or_expand(pat: &TypedPattern) -> Vec<Pat> {
    match pat {
        TypedPattern::Or { alternatives, .. } => {
            alternatives.iter().flat_map(convert_or_expand).collect()
        }
        _ => expand_nested_or(pat),
    }
}

/// Expand nested or-patterns within a single pattern into multiple Pat alternatives.
/// E.g., `Some(A | B)` becomes `[Some(A), Some(B)]`.
fn expand_nested_or(pat: &TypedPattern) -> Vec<Pat> {
    match pat {
        TypedPattern::Wildcard { .. } | TypedPattern::Var { .. } => vec![Pat::Wild],
        TypedPattern::Lit { value, .. } => {
            let p = match value {
                Lit::Bool(b) => Pat::Con(Con::BoolLit(*b), vec![]),
                Lit::Int(n) => Pat::Con(Con::Literal(n.to_string()), vec![]),
                Lit::Float(f) => Pat::Con(Con::Literal(f.to_string()), vec![]),
                Lit::String(s) => Pat::Con(Con::Literal(s.clone()), vec![]),
                Lit::Unit => Pat::Con(Con::Tuple(0), vec![]),
            };
            vec![p]
        }
        TypedPattern::Constructor { name, args, .. } => {
            let sub_expansions: Vec<Vec<Pat>> = args.iter().map(|a| expand_nested_or(a)).collect();
            let combos = cartesian_product(&sub_expansions);
            combos
                .into_iter()
                .map(|subs| Pat::Con(Con::Variant(name.clone()), subs))
                .collect()
        }
        TypedPattern::Tuple { elements, .. } => {
            let sub_expansions: Vec<Vec<Pat>> =
                elements.iter().map(|e| expand_nested_or(e)).collect();
            let combos = cartesian_product(&sub_expansions);
            combos
                .into_iter()
                .map(|subs| Pat::Con(Con::Tuple(elements.len()), subs))
                .collect()
        }
        TypedPattern::StructPat { name, fields, .. } => {
            let sub_expansions: Vec<Vec<Pat>> =
                fields.iter().map(|(_, p)| expand_nested_or(p)).collect();
            let combos = cartesian_product(&sub_expansions);
            combos
                .into_iter()
                .map(|subs| Pat::Con(Con::Record(name.clone()), subs))
                .collect()
        }
        TypedPattern::Or { alternatives, .. } => {
            alternatives.iter().flat_map(expand_nested_or).collect()
        }
    }
}

/// Compute the cartesian product of a list of Vec<Pat> alternatives.
fn cartesian_product(lists: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    if lists.is_empty() {
        return vec![vec![]];
    }
    let mut result = vec![vec![]];
    for list in lists {
        let mut new_result = Vec::new();
        for existing in &result {
            for item in list {
                let mut new = existing.clone();
                new.push(item.clone());
                new_result.push(new);
            }
        }
        result = new_result;
    }
    result
}

/// Enumerate all constructors for a type. Returns None when the constructor
/// set cannot be enumerated (Int/String have infinitely many values).
/// When `depth >= MAX_DEPTH`, returns None to bound recursion on recursive
/// types like List where Cons would otherwise expand forever.
fn all_constructors(ty: &Type, registry: &TypeRegistry, depth: usize) -> Option<Vec<Con>> {
    if depth >= MAX_DEPTH {
        return None;
    }
    match ty {
        Type::Bool => Some(vec![Con::BoolLit(true), Con::BoolLit(false)]),
        Type::Named(name, _) => {
            let info = registry.lookup_type(name)?;
            match &info.kind {
                TypeKind::Sum { variants } => Some(
                    variants
                        .iter()
                        .map(|v| Con::Variant(v.name.clone()))
                        .collect(),
                ),
                TypeKind::Record { .. } => Some(vec![Con::Record(name.clone())]),
            }
        }
        Type::Tuple(elems) => Some(vec![Con::Tuple(elems.len())]),
        Type::Unit => Some(vec![Con::Tuple(0)]),
        Type::Int | Type::Float | Type::String => None,
        _ => None,
    }
}

/// Return the number of sub-patterns a constructor carries.
fn constructor_arity(con: &Con, ty: &Type, registry: &TypeRegistry) -> usize {
    match con {
        Con::BoolLit(_) | Con::Literal(_) => 0,
        Con::Tuple(n) => *n,
        Con::Variant(name) => {
            if let Type::Named(type_name, _) = ty {
                if let Some(info) = registry.lookup_type(type_name) {
                    if let TypeKind::Sum { variants } = &info.kind {
                        for v in variants {
                            if &v.name == name {
                                return v.fields.len();
                            }
                        }
                    }
                }
            }
            0
        }
        Con::Record(name) => {
            if let Some(info) = registry.lookup_type(name) {
                if let TypeKind::Record { fields } = &info.kind {
                    return fields.len();
                }
            }
            0
        }
    }
}

/// Return the types of sub-patterns for a constructor applied to a scrutinee type.
fn sub_types(con: &Con, ty: &Type, registry: &TypeRegistry) -> Vec<Type> {
    match con {
        Con::BoolLit(_) | Con::Literal(_) => vec![],
        Con::Tuple(_) => {
            if let Type::Tuple(elems) = ty {
                elems.clone()
            } else {
                vec![]
            }
        }
        Con::Variant(name) => {
            if let Type::Named(type_name, type_args) = ty {
                if let Some(info) = registry.lookup_type(type_name) {
                    if let TypeKind::Sum { variants } = &info.kind {
                        for v in variants {
                            if &v.name == name {
                                return v
                                    .fields
                                    .iter()
                                    .map(|f| {
                                        substitute_type_params(f, &info.type_param_vars, type_args)
                                    })
                                    .collect();
                            }
                        }
                    }
                }
            }
            vec![]
        }
        Con::Record(name) => {
            if let Some(info) = registry.lookup_type(name) {
                if let TypeKind::Record { fields } = &info.kind {
                    if let Type::Named(_, type_args) = ty {
                        return fields
                            .iter()
                            .map(|(_, f)| {
                                substitute_type_params(f, &info.type_param_vars, type_args)
                            })
                            .collect();
                    }
                    return fields.iter().map(|(_, f)| f.clone()).collect();
                }
            }
            vec![]
        }
    }
}

/// Simple type parameter substitution: replace Var(id) with concrete type args.
fn substitute_type_params(
    ty: &Type,
    param_vars: &[crate::types::TypeVarId],
    type_args: &[Type],
) -> Type {
    match ty {
        Type::Var(id) => {
            for (i, pv) in param_vars.iter().enumerate() {
                if pv == id {
                    if let Some(arg) = type_args.get(i) {
                        return arg.clone();
                    }
                }
            }
            ty.clone()
        }
        Type::Named(n, args) => Type::Named(
            n.clone(),
            args.iter()
                .map(|a| substitute_type_params(a, param_vars, type_args))
                .collect(),
        ),
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|e| substitute_type_params(e, param_vars, type_args))
                .collect(),
        ),
        Type::Fn(params, ret) => Type::Fn(
            params
                .iter()
                .map(|p| substitute_type_params(p, param_vars, type_args))
                .collect(),
            Box::new(substitute_type_params(ret, param_vars, type_args)),
        ),
        Type::Own(inner) => Type::Own(Box::new(substitute_type_params(
            inner, param_vars, type_args,
        ))),
        Type::MaybeOwn(q, inner) => Type::MaybeOwn(
            *q,
            Box::new(substitute_type_params(inner, param_vars, type_args)),
        ),
        _ => ty.clone(),
    }
}

/// Specialize the matrix by a constructor: keep rows whose first column matches `con`,
/// expanding sub-patterns; drop rows that don't match (unless wildcard).
fn specialize(matrix: &[Vec<Pat>], con: &Con, arity: usize) -> Vec<Vec<Pat>> {
    let mut result = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        match &row[0] {
            Pat::Con(c, subs) if c == con => {
                let mut new_row: Vec<Pat> = subs.clone();
                while new_row.len() < arity {
                    new_row.push(Pat::Wild);
                }
                new_row.extend_from_slice(&row[1..]);
                result.push(new_row);
            }
            Pat::Wild => {
                let mut new_row: Vec<Pat> = vec![Pat::Wild; arity];
                new_row.extend_from_slice(&row[1..]);
                result.push(new_row);
            }
            _ => {}
        }
    }
    result
}

/// Default matrix: rows where first column is Wild, with column 0 removed.
fn default_matrix(matrix: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    let mut result = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        if matches!(&row[0], Pat::Wild) {
            result.push(row[1..].to_vec());
        }
    }
    result
}

/// Collect the set of head constructors from column 0 of the matrix.
fn head_constructors(matrix: &[Vec<Pat>]) -> Vec<Con> {
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for row in matrix {
        if row.is_empty() {
            continue;
        }
        if let Pat::Con(c, _) = &row[0] {
            if seen.insert(c.clone()) {
                result.push(c.clone());
            }
        }
    }
    result
}

/// Core usefulness check: is `pattern_vec` useful with respect to `matrix`?
/// The `depth` parameter limits constructor expansion for recursive types.
fn is_useful(
    matrix: &[Vec<Pat>],
    pattern_vec: &[Pat],
    type_stack: &[Type],
    registry: &TypeRegistry,
    depth: usize,
) -> bool {
    if pattern_vec.is_empty() {
        return matrix.is_empty();
    }

    let ty = &type_stack[0];

    match &pattern_vec[0] {
        Pat::Con(con, subs) => {
            let arity = constructor_arity(con, ty, registry);
            let spec_matrix = specialize(matrix, con, arity);
            let mut new_pat: Vec<Pat> = subs.clone();
            while new_pat.len() < arity {
                new_pat.push(Pat::Wild);
            }
            new_pat.extend_from_slice(&pattern_vec[1..]);
            let mut new_types = sub_types(con, ty, registry);
            new_types.extend_from_slice(&type_stack[1..]);
            is_useful(&spec_matrix, &new_pat, &new_types, registry, depth + 1)
        }
        Pat::Wild => {
            let heads = head_constructors(matrix);
            if let Some(all_cons) = all_constructors(ty, registry, depth) {
                let head_set: HashSet<Con> = heads.into_iter().collect();
                let is_complete = all_cons.iter().all(|c| head_set.contains(c));
                if is_complete {
                    for con in &all_cons {
                        let arity = constructor_arity(con, ty, registry);
                        let spec_matrix = specialize(matrix, con, arity);
                        let mut new_pat: Vec<Pat> = vec![Pat::Wild; arity];
                        new_pat.extend_from_slice(&pattern_vec[1..]);
                        let mut new_types = sub_types(con, ty, registry);
                        new_types.extend_from_slice(&type_stack[1..]);
                        if is_useful(&spec_matrix, &new_pat, &new_types, registry, depth + 1) {
                            return true;
                        }
                    }
                    return false;
                }
            }
            // Incomplete or infinite: use default matrix
            let def = default_matrix(matrix);
            is_useful(
                &def,
                &pattern_vec[1..],
                &type_stack[1..],
                registry,
                depth + 1,
            )
        }
    }
}

/// Witness generation: find a pattern vector that is not covered by the matrix.
/// Returns None if the matrix is exhaustive.
fn witness(
    matrix: &[Vec<Pat>],
    type_stack: &[Type],
    registry: &TypeRegistry,
    depth: usize,
) -> Option<Vec<Pat>> {
    if type_stack.is_empty() {
        return if matrix.is_empty() {
            Some(vec![])
        } else {
            None
        };
    }

    let ty = &type_stack[0];
    let heads = head_constructors(matrix);

    if let Some(all_cons) = all_constructors(ty, registry, depth) {
        let head_set: HashSet<Con> = heads.into_iter().collect();
        let is_complete = all_cons.iter().all(|c| head_set.contains(c));

        if is_complete {
            for con in &all_cons {
                let arity = constructor_arity(con, ty, registry);
                let spec_matrix = specialize(matrix, con, arity);
                let mut new_types = sub_types(con, ty, registry);
                new_types.extend_from_slice(&type_stack[1..]);
                if let Some(mut w) = witness(&spec_matrix, &new_types, registry, depth + 1) {
                    let rest: Vec<Pat> = w.split_off(arity);
                    let sub_pats = w;
                    let mut result = vec![Pat::Con(con.clone(), sub_pats)];
                    result.extend(rest);
                    return Some(result);
                }
            }
            None
        } else {
            // Find a missing constructor
            let missing_con = all_cons.iter().find(|c| !head_set.contains(c));
            if let Some(con) = missing_con {
                let arity = constructor_arity(con, ty, registry);
                let spec_matrix = specialize(matrix, con, arity);
                let mut new_types = sub_types(con, ty, registry);
                new_types.extend_from_slice(&type_stack[1..]);
                if let Some(mut w) = witness(&spec_matrix, &new_types, registry, depth + 1) {
                    let rest: Vec<Pat> = w.split_off(arity);
                    let sub_pats = w;
                    let mut result = vec![Pat::Con(con.clone(), sub_pats)];
                    result.extend(rest);
                    return Some(result);
                }
                None
            } else {
                // No constructors known — use default matrix
                let def = default_matrix(matrix);
                if let Some(mut w) = witness(&def, &type_stack[1..], registry, depth + 1) {
                    let mut result = vec![Pat::Wild];
                    result.append(&mut w);
                    Some(result)
                } else {
                    None
                }
            }
        }
    } else {
        // Non-enumerable type or depth exceeded — use default matrix
        let def = default_matrix(matrix);
        if let Some(mut w) = witness(&def, &type_stack[1..], registry, depth + 1) {
            let mut result = vec![Pat::Wild];
            result.append(&mut w);
            Some(result)
        } else {
            None
        }
    }
}

/// Format a witness pattern for error messages.
fn format_pat(pat: &Pat) -> String {
    match pat {
        Pat::Wild => "_".to_string(),
        Pat::Con(con, subs) => match con {
            Con::Variant(name) => {
                if subs.is_empty() {
                    name.clone()
                } else {
                    format!(
                        "{}({})",
                        name,
                        subs.iter().map(format_pat).collect::<Vec<_>>().join(", ")
                    )
                }
            }
            Con::BoolLit(b) => b.to_string(),
            Con::Literal(s) => s.clone(),
            Con::Tuple(n) => {
                if *n == 0 {
                    "()".to_string()
                } else {
                    format!(
                        "({})",
                        subs.iter().map(format_pat).collect::<Vec<_>>().join(", ")
                    )
                }
            }
            Con::Record(name) => {
                format!("{} {{ .. }}", name)
            }
        },
    }
}

/// Format witness patterns into missing pattern strings.
fn format_witness(witness: &[Pat]) -> Vec<String> {
    witness.iter().map(format_pat).collect()
}

pub fn check_exhaustiveness(
    scrutinee_ty: &Type,
    arms: &[TypedMatchArm],
    registry: Option<&TypeRegistry>,
    span: Span,
) -> Result<(), SpannedTypeError> {
    let registry = match registry {
        Some(r) => r,
        None => return Ok(()),
    };

    let types = vec![scrutinee_ty.clone()];
    // Matrix of only unguarded rows — guarded arms don't contribute to coverage
    // or make later arms redundant (since the guard might fail).
    let mut unguarded_matrix: Vec<Vec<Pat>> = Vec::new();

    let mut checked_arms: HashSet<usize> = HashSet::new();

    for (arm_idx, arm) in arms.iter().enumerate() {
        let converted = convert_or_expand(&arm.pattern);
        let has_guard = arm.guard.is_some();

        // Redundancy: check against unguarded prior rows only.
        // A guarded arm can never make a later arm unreachable.
        let any_useful = converted.iter().any(|row| {
            is_useful(&unguarded_matrix, &[row.clone()], &types, registry, 0)
        });
        if !any_useful && !checked_arms.contains(&arm_idx) {
            let arm_span = arm.pattern.span();
            return Err(SpannedTypeError {
                error: TypeError::RedundantPattern,
                span: arm_span,
                note: Some("this arm can never be reached".to_string()),
                secondary_span: None,
                source_file: None,
                var_names: None,
            });
        }
        checked_arms.insert(arm_idx);

        // Only unguarded rows count toward the matrix
        if !has_guard {
            for row in converted {
                unguarded_matrix.push(vec![row]);
            }
        }
    }

    // Exhaustiveness: only unguarded arms count
    if let Some(w) = witness(&unguarded_matrix, &types, registry, 0) {
        let missing = format_witness(&w);
        return Err(SpannedTypeError {
            error: TypeError::NonExhaustive { missing },
            span,
            note: None,
            secondary_span: None,
            source_file: None,
            var_names: None,
        });
    }

    Ok(())
}
