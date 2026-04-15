use std::collections::HashMap;

use crate::types::{Substitution, Type, TypeEnv, TypeVarId};

use super::generalize;

/// Format an inferred type for display, renaming type variables to a, b, c, ...
/// and wrapping polymorphic types in `forall`.
pub fn display_type(ty: &Type, subst: &Substitution, env: &TypeEnv) -> String {
    let scheme = generalize(ty, env, subst);
    format!("{}", scheme)
}

/// Substitute a type variable with a concrete type throughout a type.
pub(crate) fn substitute_type_var(ty: &Type, var_id: TypeVarId, replacement: &Type) -> Type {
    match ty {
        Type::Var(id) if *id == var_id => replacement.clone(),
        Type::Var(_)
        | Type::Int
        | Type::Float
        | Type::Bool
        | Type::String
        | Type::Unit
        | Type::FnHole => ty.clone(),
        Type::Fn(params, ret) => {
            let new_params = params
                .iter()
                .map(|(m, p)| (*m, substitute_type_var(p, var_id, replacement)))
                .collect();
            let new_ret = substitute_type_var(ret, var_id, replacement);
            Type::Fn(new_params, Box::new(new_ret))
        }
        Type::Named(name, args) => {
            let new_args = args
                .iter()
                .map(|a| substitute_type_var(a, var_id, replacement))
                .collect();
            Type::Named(name.clone(), new_args)
        }
        Type::App(ctor, args) => {
            let new_ctor = substitute_type_var(ctor, var_id, replacement);
            let new_args: Vec<Type> = args
                .iter()
                .map(|a| substitute_type_var(a, var_id, replacement))
                .collect();
            crate::types::normalize_app(new_ctor, new_args)
        }
        Type::Own(inner) => Type::Own(Box::new(substitute_type_var(inner, var_id, replacement))),
        Type::Shape(inner) => {
            Type::Shape(Box::new(substitute_type_var(inner, var_id, replacement)))
        }
        Type::MaybeOwn(q, inner) => Type::MaybeOwn(
            *q,
            Box::new(substitute_type_var(inner, var_id, replacement)),
        ),
        Type::Tuple(elems) => {
            let new_elems = elems
                .iter()
                .map(|e| substitute_type_var(e, var_id, replacement))
                .collect();
            Type::Tuple(new_elems)
        }
    }
}

pub(crate) fn leading_type_var(ty: &Type) -> Option<TypeVarId> {
    match ty {
        Type::Var(v) => Some(*v),
        Type::App(ctor, _) => leading_type_var(ctor),
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            leading_type_var(inner)
        }
        _ => None,
    }
}

/// Build the type_param_map and arity map from parallel slices of names and vars.
pub(crate) fn build_type_param_map(
    type_params: &[String],
    type_param_vars: &[TypeVarId],
    type_name: &str,
) -> (HashMap<String, TypeVarId>, HashMap<String, usize>) {
    let mut map = HashMap::new();
    let mut arity = HashMap::new();
    for (param_name, &var) in type_params.iter().zip(type_param_vars.iter()) {
        map.insert(param_name.clone(), var);
    }
    arity.insert(type_name.to_string(), type_params.len());
    (map, arity)
}
