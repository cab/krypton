use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, UnaryOp};

use crate::trait_registry::TraitRegistry;
use crate::typed_ast::{TraitName, TypedExpr, TypedExprKind};
use crate::types;
use crate::types::{Substitution, Type, TypeScheme, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::{free_vars, leading_type_var, match_type_with_bindings, no_instance_error, spanned, strip_own};

fn bare_function_ref_name(expr: &TypedExpr) -> Option<&str> {
    match &expr.kind {
        TypedExprKind::Var(name) => Some(name.as_str()),
        TypedExprKind::TypeApp { expr, .. } => bare_function_ref_name(expr),
        _ => None,
    }
}

fn resolve_function_ref_requirement_type(
    trait_name: &str,
    type_var: TypeVarId,
    declared_param_types: &[Type],
    actual_param_types: &[Type],
) -> Option<Type> {
    let _ = trait_name;
    let mut bindings = HashMap::new();
    for (declared, actual) in declared_param_types.iter().zip(actual_param_types.iter()) {
        if !match_type_with_bindings(declared, actual, &mut bindings) {
            return None;
        }
    }
    bindings.get(&type_var).cloned()
}

fn typed_callee_var_name(expr: &TypedExpr) -> Option<&str> {
    match &expr.kind {
        TypedExprKind::Var(name) => Some(name.as_str()),
        TypedExprKind::TypeApp { expr, .. } => typed_callee_var_name(expr),
        _ => None,
    }
}

/// Simple type var binding: walk pattern and actual types, recording Var → concrete mappings.
fn bind_type_vars_simple(pattern: &Type, actual: &Type, bindings: &mut HashMap<TypeVarId, Type>) {
    match (pattern, actual) {
        (Type::Var(id), _) => {
            bindings.entry(*id).or_insert_with(|| actual.clone());
        }
        (Type::Own(p), _) => bind_type_vars_simple(p, actual, bindings),
        (_, Type::Own(a)) => bind_type_vars_simple(pattern, a, bindings),
        (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
            bind_type_vars_simple(p_ctor, a_ctor, bindings);
            for (p, a) in p_args.iter().zip(a_args.iter()) {
                bind_type_vars_simple(p, a, bindings);
            }
        }
        // Cross-arm for HKT: pattern App(Var(f), [a]) vs actual Named("Box", [Int])
        (Type::App(p_ctor, p_args), Type::Named(a_name, a_args)) if p_args.len() == a_args.len() => {
            bind_type_vars_simple(p_ctor, &Type::Named(a_name.clone(), vec![]), bindings);
            for (p, a) in p_args.iter().zip(a_args.iter()) {
                bind_type_vars_simple(p, a, bindings);
            }
        }
        // Cross-arm for HKT: pattern App(Var(f), [a]) vs actual Fn([Int], Int)
        (Type::App(p_ctor, p_args), Type::Fn(a_params, a_ret))
            if types::decompose_fn_for_app(a_params, a_ret, p_args.len()).is_some() =>
        {
            let (ctor_fn, remaining) = types::decompose_fn_for_app(a_params, a_ret, p_args.len()).unwrap();
            bind_type_vars_simple(p_ctor, &ctor_fn, bindings);
            for (p, a) in p_args.iter().zip(remaining.iter()) {
                bind_type_vars_simple(p, a, bindings);
            }
        }
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) if p_name == a_name => {
            for (p, a) in p_args.iter().zip(a_args.iter()) {
                bind_type_vars_simple(p, a, bindings);
            }
        }
        (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
            for (p, a) in p_params.iter().zip(a_params.iter()) {
                bind_type_vars_simple(p, a, bindings);
            }
            bind_type_vars_simple(p_ret, a_ret, bindings);
        }
        (Type::Tuple(p_elems), Type::Tuple(a_elems)) => {
            for (p, a) in p_elems.iter().zip(a_elems.iter()) {
                bind_type_vars_simple(p, a, bindings);
            }
        }
        _ => {}
    }
}

pub(super) fn check_constrained_function_refs(
    expr: &TypedExpr,
    current_requirements: &[(TraitName, TypeVarId)],
    fn_schemes: &HashMap<String, TypeScheme>,
    fn_constraint_requirements: &HashMap<String, Vec<(TraitName, TypeVarId)>>,
    trait_registry: &TraitRegistry,
) -> Result<(), SpannedTypeError> {
    let mut work: Vec<&TypedExpr> = vec![expr];
    while let Some(expr) = work.pop() {
        if let Some(name) = bare_function_ref_name(expr) {
            let fn_type = match &expr.ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            if let Type::Fn(actual_param_types, _) = fn_type {
                let requirements = fn_constraint_requirements
                    .get(name)
                    .cloned()
                    .unwrap_or_default();

                if !requirements.is_empty() {
                    let scheme = fn_schemes.get(name).ok_or_else(|| {
                        spanned(
                            TypeError::UnsupportedExpr {
                                description: format!(
                                    "missing function type metadata for constrained function reference `{name}`"
                                ),
                            },
                            expr.span,
                        )
                    })?;
                    let declared_param_types = match &scheme.ty {
                        Type::Fn(params, _) => params,
                        other => {
                            return Err(spanned(
                                TypeError::UnsupportedExpr {
                                    description: format!(
                                        "constrained function reference `{name}` has non-function type `{other}`"
                                    ),
                                },
                                expr.span,
                            ))
                        }
                    };

                    for (req_trait_name, req_type_var) in &requirements {
                        let requirement_ty = resolve_function_ref_requirement_type(
                            &req_trait_name.local_name,
                            *req_type_var,
                            declared_param_types,
                            actual_param_types,
                        )
                        .ok_or_else(|| {
                            spanned(
                                TypeError::UnsupportedExpr {
                                    description: format!(
                                        "could not resolve `{req_trait_name}` for constrained function reference `{name}`"
                                    ),
                                },
                                expr.span,
                            )
                        })?;

                        let requirement_ty = strip_own(&requirement_ty);
                        if free_vars(&requirement_ty).is_empty() {
                            let missing = if trait_registry.lookup_trait(req_trait_name).is_some() {
                                trait_registry.find_instance(req_trait_name, &requirement_ty).is_none()
                            } else {
                                true
                            };
                            if missing {
                                return Err(no_instance_error(
                                    trait_registry,
                                    req_trait_name,
                                    &requirement_ty,
                                    expr.span,
                                ));
                            }
                            continue;
                        }

                        if let Type::Var(type_var) = requirement_ty {
                            if current_requirements.iter().any(|(trait_name, current_type_var)| {
                                trait_name == req_trait_name && *current_type_var == type_var
                            }) {
                                continue;
                            }
                        }

                        if current_requirements
                            .iter()
                            .any(|(trait_name, _)| trait_name == req_trait_name)
                        {
                            continue;
                        }

                        return Err(spanned(
                            TypeError::UnsupportedExpr {
                                description: format!(
                                    "Krypton does not support first-class constrained polymorphic function values like `{name}`; instantiate the function or wrap the call in a lambda"
                                ),
                            },
                            expr.span,
                        ));
                    }
                }
            }
        }

        match &expr.kind {
            TypedExprKind::App { args, .. } => {
                for arg in args {
                    work.push(arg);
                }
            }
            TypedExprKind::TypeApp { .. } => {}
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. }
            | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::Do(exprs)
            | TypedExprKind::Tuple(exprs)
            | TypedExprKind::Recur(exprs)
            | TypedExprKind::VecLit(exprs) => {
                for expr in exprs {
                    work.push(expr);
                }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms {
                    work.push(&arm.body);
                }
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, expr) in fields {
                    work.push(expr);
                }
            }
            TypedExprKind::StructUpdate { base, fields, .. } => {
                work.push(base);
                for (_, expr) in fields {
                    work.push(expr);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }

    Ok(())
}

/// Detect trait method calls on type variables and collect as constraints (used for codegen dict params).
pub(super) fn detect_trait_constraints(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, TraitName>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_type_param_vars: &HashSet<TypeVarId>,
    constraints: &mut Vec<(TraitName, TypeVarId)>,
) {
    walk_trait_method_calls(expr, trait_method_map, trait_registry, subst, fn_type_param_vars, &mut |trait_name, var| {
        constraints.push((trait_name, var));
    });
}

/// Validate that all trait method calls on type variables have corresponding declared constraints.
pub(super) fn validate_trait_constraints(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, TraitName>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_type_param_vars: &HashSet<TypeVarId>,
    declared_constraints: &[(TraitName, TypeVarId)],
    fn_name: &str,
    type_var_names: &HashMap<TypeVarId, String>,
) -> Result<(), SpannedTypeError> {
    let mut first_error: Option<SpannedTypeError> = None;
    walk_trait_method_calls(expr, trait_method_map, trait_registry, subst, fn_type_param_vars, &mut |trait_name, var| {
        if first_error.is_some() {
            return;
        }
        let is_declared = declared_constraints.iter().any(|(t, v)| t.local_name == trait_name.local_name && *v == var);
        if !is_declared {
            let type_var_display = type_var_names
                .get(&var)
                .cloned()
                .unwrap_or_else(|| format!("?{}", var.0));
            first_error = Some(super::spanned(
                TypeError::MissingTraitBound {
                    fn_name: fn_name.to_string(),
                    trait_name: trait_name.local_name.clone(),
                    type_var: type_var_display,
                },
                expr.span,
            ));
        }
    });
    match first_error {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

/// Shared walker: finds trait method calls on type variables and invokes the callback for each.
fn walk_trait_method_calls(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, TraitName>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_type_param_vars: &HashSet<TypeVarId>,
    callback: &mut dyn FnMut(TraitName, TypeVarId),
) {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args } => {
                if let Some(name) = typed_callee_var_name(func) {
                    if let Some(trait_id) = trait_method_map.get(name) {
                        // Try first arg, then fall back to return type
                        let candidate_var = if let Some(first_arg) = args.first() {
                            let arg_ty = subst.apply(&first_arg.ty);
                            let concrete_ty = strip_own(&arg_ty);
                            leading_type_var(&concrete_ty)
                        } else {
                            None
                        };
                        let candidate_var = candidate_var.or_else(|| {
                            let ret_ty = subst.apply(&func.ty);
                            let concrete_ret = match &ret_ty {
                                Type::Fn(_, ret) => strip_own(ret),
                                other => strip_own(other),
                            };
                            leading_type_var(&concrete_ret)
                        });
                        if let Some(v) = candidate_var {
                            if fn_type_param_vars.contains(&v) {
                                callback(trait_id.clone(), v);
                            }
                        }
                    }
                }
                work.push(func);
                for a in args {
                    work.push(a);
                }
            }
            TypedExprKind::TypeApp { expr, .. } => work.push(expr),
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. }
            | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs {
                    work.push(e);
                }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms {
                    work.push(&arm.body);
                }
            }
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let trait_name = match op {
                    BinOp::Add => Some("Semigroup"),
                    BinOp::Sub => Some("Sub"),
                    BinOp::Mul => Some("Mul"),
                    BinOp::Div => Some("Div"),
                    BinOp::Eq | BinOp::Neq => Some("Eq"),
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => Some("Ord"),
                    BinOp::And | BinOp::Or => None,
                };
                if let Some(tn) = trait_name {
                    let operand_ty = strip_own(&subst.apply(&lhs.ty));
                    if let Some(v) = leading_type_var(&operand_ty) {
                        if fn_type_param_vars.contains(&v) {
                            let module = match tn {
                                "Semigroup" => "core/semigroup",
                                "Sub" => "core/sub",
                                "Mul" => "core/mul",
                                "Div" => "core/div",
                                "Eq" => "core/eq",
                                "Ord" => "core/ord",
                                _ => "",
                            };
                            callback(TraitName::new(module.into(), tn.into()), v);
                        }
                    }
                }
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { op, operand } => {
                if matches!(op, UnaryOp::Neg) {
                    let operand_ty = strip_own(&subst.apply(&operand.ty));
                    if let Some(v) = leading_type_var(&operand_ty) {
                        if fn_type_param_vars.contains(&v) {
                            callback(TraitName::core_neg(), v);
                        }
                    }
                }
                work.push(operand);
            }
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::StructUpdate { base, fields, .. } => {
                work.push(base);
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::Tuple(elems)
            | TypedExprKind::Recur(elems)
            | TypedExprKind::VecLit(elems) => {
                for e in elems {
                    work.push(e);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }
}

/// Walk a typed AST looking for calls to trait methods. For each call,
/// resolve the argument type and verify that a matching instance exists.
/// Also checks calls to imported constrained functions (via `fn_constraint_requirements`).
pub(super) fn check_trait_instances(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, TraitName>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_constraint_requirements: &HashMap<String, Vec<(TraitName, TypeVarId)>>,
    fn_schemes: &HashMap<String, TypeScheme>,
    fn_type_vars: &HashSet<TypeVarId>,
) -> Result<(), SpannedTypeError> {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args } => {
                if let Some(name) = typed_callee_var_name(func) {
                    if let Some(trait_id) = trait_method_map.get(name) {
                        // trait_method_map is derived from trait_registry, so lookup cannot fail
                        let info = trait_registry.lookup_trait(trait_id)
                            .expect("trait in trait_method_map must be in registry");
                        if let Some(method) = info.methods.iter().find(|m| m.name == name) {
                            let mut bindings = HashMap::new();
                            // Bind from params
                            for (pattern, arg) in method.param_types.iter().zip(args.iter()) {
                                bind_type_vars_simple(pattern, &subst.apply(&arg.ty), &mut bindings);
                            }
                            // Bind from return type
                            let ret_ty = subst.apply(&func.ty);
                            let actual_ret = match &ret_ty {
                                Type::Fn(_, ret) => ret.as_ref().clone(),
                                other => other.clone(),
                            };
                            bind_type_vars_simple(&method.return_type, &actual_ret, &mut bindings);
                            // Bind from explicit type application
                            if let TypedExprKind::TypeApp { type_args, .. } = &func.kind {
                                if !type_args.is_empty() {
                                    bindings.entry(info.type_var_id).or_insert_with(|| type_args[0].clone());
                                }
                            }
                            // Check dispatch type var — must always be bindable from the
                            // method signature (params, return type, or explicit type args)
                            let dispatch_ty = bindings.get(&info.type_var_id)
                                .unwrap_or_else(|| panic!(
                                    "ICE: trait type var for `{}::{}` not bound from method signature",
                                    trait_id.local_name, name
                                ));
                            let concrete_ty = strip_own(dispatch_ty);
                            if let Some(v) = leading_type_var(&concrete_ty) {
                                if !fn_type_vars.contains(&v) {
                                    return Err(spanned(
                                        TypeError::AmbiguousType {
                                            trait_name: trait_id.local_name.clone(),
                                            method_name: name.to_string(),
                                        },
                                        expr.span,
                                    ));
                                }
                            } else if trait_registry.find_instance(trait_id, &concrete_ty).is_none()
                            {
                                return Err(no_instance_error(
                                    trait_registry,
                                    trait_id,
                                    &concrete_ty,
                                    expr.span,
                                ));
                            }
                        }
                    }
                    // Check calls to constrained functions (e.g., imported `println` requires Show)
                    if let Some(requirements) = fn_constraint_requirements.get(name) {
                        // Resolve each constraint's type via bind_type_vars approach
                        let fn_scheme = fn_schemes.get(name);
                        for (req_trait_name, type_var) in requirements {
                            let resolved_ty = fn_scheme.and_then(|scheme| {
                                if let Type::Fn(param_types, ret_ty) = &scheme.ty {
                                    let mut bindings: HashMap<TypeVarId, Type> = HashMap::new();
                                    for (pattern, arg) in param_types.iter().zip(args.iter()) {
                                        bind_type_vars_simple(pattern, &subst.apply(&arg.ty), &mut bindings);
                                    }
                                    if bindings.get(type_var).is_none() {
                                        // Also try return type
                                        let ret_actual = subst.apply(&func.ty);
                                        if let Type::Fn(_, actual_ret) = &ret_actual {
                                            bind_type_vars_simple(ret_ty, actual_ret, &mut bindings);
                                        }
                                    }
                                    bindings.get(type_var).cloned()
                                } else {
                                    None
                                }
                            });
                            if let Some(ty) = resolved_ty {
                                let concrete_ty = strip_own(&ty);
                                if leading_type_var(&concrete_ty).is_none() {
                                    let missing = if trait_registry.lookup_trait(req_trait_name).is_some() {
                                        trait_registry.find_instance(req_trait_name, &concrete_ty).is_none()
                                    } else {
                                        true
                                    };
                                    if missing {
                                        return Err(no_instance_error(
                                            trait_registry,
                                            req_trait_name,
                                            &concrete_ty,
                                            expr.span,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
                work.push(func);
                for a in args {
                    work.push(a);
                }
            }
            TypedExprKind::TypeApp { expr, .. } => work.push(expr),
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let trait_name = match op {
                    BinOp::Add => Some(TraitName::core_semigroup()),
                    BinOp::Sub => Some(TraitName::core_sub()),
                    BinOp::Mul => Some(TraitName::core_mul()),
                    BinOp::Div => Some(TraitName::core_div()),
                    BinOp::Eq | BinOp::Neq => Some(TraitName::core_eq()),
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => Some(TraitName::core_ord()),
                    BinOp::And | BinOp::Or => None,
                };
                if let Some(ref trait_name) = trait_name {
                    let operand_ty = strip_own(&subst.apply(&lhs.ty));
                    if !matches!(operand_ty, Type::Var(_)) {
                        if trait_registry.lookup_trait(trait_name).is_some()
                            && trait_registry.find_instance(trait_name, &operand_ty).is_none()
                        {
                            return Err(no_instance_error(
                                trait_registry,
                                trait_name,
                                &operand_ty,
                                expr.span,
                            ));
                        }
                    }
                }
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { op, operand } => {
                if matches!(op, UnaryOp::Neg) {
                    let neg_trait = TraitName::core_neg();
                    let operand_ty = strip_own(&subst.apply(&operand.ty));
                    if !matches!(operand_ty, Type::Var(_)) {
                        if trait_registry.lookup_trait(&neg_trait).is_some()
                            && trait_registry.find_instance(&neg_trait, &operand_ty).is_none()
                        {
                            return Err(no_instance_error(
                                trait_registry,
                                &neg_trait,
                                &operand_ty,
                                expr.span,
                            ));
                        }
                    }
                }
                work.push(operand);
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. }
            | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs {
                    work.push(e);
                }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms {
                    work.push(&arm.body);
                }
            }
            TypedExprKind::FieldAccess { expr: inner, .. } => work.push(inner),
            TypedExprKind::Tuple(elems)
            | TypedExprKind::Recur(elems)
            | TypedExprKind::VecLit(elems) => {
                for e in elems {
                    work.push(e);
                }
            }
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::StructUpdate { base, fields, .. } => {
                work.push(base);
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }
    Ok(())
}
