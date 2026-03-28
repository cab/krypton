use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, UnaryOp};

use crate::trait_registry::TraitRegistry;
use crate::typed_ast::{TraitName, TypedExpr, TypedExprKind};
use crate::types;
use crate::types::{Substitution, Type, TypeScheme, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::{
    free_vars, leading_type_var, match_type_with_bindings, no_instance_error, spanned, strip_own,
};

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

/// Collect type variable bindings while enforcing consistency for repeated vars.
/// Fixed non-variable structure that does not bind anything is ignored.
fn collect_type_var_bindings_strict(
    pattern: &Type,
    actual: &Type,
    bindings: &mut HashMap<TypeVarId, Type>,
) -> bool {
    match (pattern, actual) {
        // Unresolved actuals are still informative enough to establish a first binding,
        // but they should not contradict an existing concrete binding during this pass.
        (Type::Var(id), _) => match bindings.get(id) {
            Some(existing) if !free_vars(existing).is_empty() || !free_vars(actual).is_empty() => {
                true
            }
            Some(existing) => existing == actual,
            None => {
                bindings.insert(*id, actual.clone());
                true
            }
        },
        (Type::Own(p), _) => collect_type_var_bindings_strict(p, actual, bindings),
        (_, Type::Own(a)) => collect_type_var_bindings_strict(pattern, a, bindings),
        (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
            collect_type_var_bindings_strict(p_ctor, a_ctor, bindings)
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings))
        }
        // Cross-arm for HKT: pattern App(Var(f), [a]) vs actual Named("Box", [Int])
        (Type::App(p_ctor, p_args), Type::Named(a_name, a_args))
            if p_args.len() == a_args.len() =>
        {
            collect_type_var_bindings_strict(p_ctor, &Type::Named(a_name.clone(), vec![]), bindings)
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings))
        }
        // Cross-arm for HKT: pattern App(Var(f), [a]) vs actual Fn([Int], Int)
        (Type::App(p_ctor, p_args), Type::Fn(a_params, a_ret))
            if types::decompose_fn_for_app(a_params, a_ret, p_args.len()).is_some() =>
        {
            let (ctor_fn, remaining) =
                types::decompose_fn_for_app(a_params, a_ret, p_args.len()).unwrap();
            collect_type_var_bindings_strict(p_ctor, &ctor_fn, bindings)
                && p_args
                    .iter()
                    .zip(remaining.iter())
                    .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings))
        }
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) if p_name == a_name => {
            p_args
                .iter()
                .zip(a_args.iter())
                .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings))
        }
        (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
            p_params
                .iter()
                .zip(a_params.iter())
                .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings))
                && collect_type_var_bindings_strict(p_ret, a_ret, bindings)
        }
        (Type::Tuple(p_elems), Type::Tuple(a_elems)) => {
            p_elems
                .iter()
                .zip(a_elems.iter())
                .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings))
        }
        _ => true,
    }
}

pub(super) fn check_constrained_function_refs(
    expr: &TypedExpr,
    current_requirements: &[(TraitName, TypeVarId)],
    fn_schemes: &HashMap<String, TypeScheme>,
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
                let requirements = fn_schemes
                    .get(name)
                    .map(|s| s.constraints.clone())
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
                                trait_registry
                                    .find_instance(req_trait_name, &requirement_ty)
                                    .is_none()
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
                            if current_requirements
                                .iter()
                                .any(|(trait_name, current_type_var)| {
                                    trait_name == req_trait_name && *current_type_var == type_var
                                })
                            {
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
    fn_schemes: &HashMap<String, TypeScheme>,
    constraints: &mut Vec<(TraitName, TypeVarId)>,
) {
    walk_trait_method_calls(
        expr,
        trait_method_map,
        trait_registry,
        subst,
        fn_type_param_vars,
        fn_schemes,
        &mut |trait_name, var| {
            constraints.push((trait_name, var));
        },
    );
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
    // Validate uses an empty fn schemes map — constrained function call detection is
    // only done in the detect pass (for auto-inference). The validate pass only checks
    // direct trait method calls and operator uses, which can precisely identify the
    // constrained type variable.
    let empty_fn_schemes = HashMap::new();
    let mut first_error: Option<SpannedTypeError> = None;
    walk_trait_method_calls(
        expr,
        trait_method_map,
        trait_registry,
        subst,
        fn_type_param_vars,
        &empty_fn_schemes,
        &mut |trait_name, var| {
            if first_error.is_some() {
                return;
            }
            let is_declared = declared_constraints
                .iter()
                .any(|(t, v)| t.local_name == trait_name.local_name && *v == var);
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
        },
    );
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
    fn_schemes: &HashMap<String, TypeScheme>,
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
                        // Check method-level where constraints for polymorphic propagation
                        let info = trait_registry
                            .lookup_trait(trait_id)
                            .expect("trait in trait_method_map must be in registry");
                        if let Some(method) = info.methods.iter().find(|m| m.name == name) {
                            if !method.constraints.is_empty() {
                                let mut bindings = HashMap::new();
                                for (pattern, arg) in method.param_types.iter().zip(args.iter()) {
                                    collect_type_var_bindings_strict(
                                        pattern,
                                        &subst.apply(&arg.ty),
                                        &mut bindings,
                                    );
                                }
                                let ret_ty = subst.apply(&func.ty);
                                let actual_ret = match &ret_ty {
                                    Type::Fn(_, ret) => ret.as_ref().clone(),
                                    other => other.clone(),
                                };
                                collect_type_var_bindings_strict(
                                    &method.return_type,
                                    &actual_ret,
                                    &mut bindings,
                                );
                                for (req_trait, req_var) in &method.constraints {
                                    if let Some(resolved) = bindings.get(req_var) {
                                        let concrete = strip_own(resolved);
                                        if let Some(v) = leading_type_var(&concrete) {
                                            if fn_type_param_vars.contains(&v) {
                                                callback(req_trait.clone(), v);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // Also detect calls to constrained regular functions (e.g., println where a: Show)
                    if let Some(scheme) = fn_schemes.get(name).filter(|s| !s.constraints.is_empty()) {
                        let declared_param_types = match &scheme.ty {
                            Type::Fn(params, _) => params.as_slice(),
                            _ => &[],
                        };
                        let actual_param_types: Vec<Type> =
                            args.iter().map(|a| subst.apply(&a.ty)).collect();
                        for (req_trait, req_var) in &scheme.constraints {
                            if let Some(resolved) = resolve_function_ref_requirement_type(
                                &req_trait.local_name,
                                *req_var,
                                declared_param_types,
                                &actual_param_types,
                            ) {
                                let concrete = strip_own(&resolved);
                                if let Some(v) = leading_type_var(&concrete) {
                                    if fn_type_param_vars.contains(&v) {
                                        callback(req_trait.clone(), v);
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
/// Also checks calls to imported constrained functions (via `TypeScheme.constraints`).
pub(super) fn check_trait_instances(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, TraitName>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
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
                        let info = trait_registry
                            .lookup_trait(trait_id)
                            .expect("trait in trait_method_map must be in registry");
                        if let Some(method) = info.methods.iter().find(|m| m.name == name) {
                            let mut bindings = HashMap::new();
                            // Bind from params
                            for (pattern, arg) in method.param_types.iter().zip(args.iter()) {
                                collect_type_var_bindings_strict(
                                    pattern,
                                    &subst.apply(&arg.ty),
                                    &mut bindings,
                                );
                            }
                            // Bind from return type
                            let ret_ty = subst.apply(&func.ty);
                            let actual_ret = match &ret_ty {
                                Type::Fn(_, ret) => ret.as_ref().clone(),
                                other => other.clone(),
                            };
                            collect_type_var_bindings_strict(
                                &method.return_type,
                                &actual_ret,
                                &mut bindings,
                            );
                            // Bind from explicit type application
                            if let TypedExprKind::TypeApp { type_args, .. } = &func.kind {
                                if !type_args.is_empty() {
                                    bindings
                                        .entry(info.type_var_id)
                                        .or_insert_with(|| type_args[0].clone());
                                }
                            }
                            // Check dispatch type var — must always be bindable from the
                            // method signature (params, return type, or explicit type args)
                            let dispatch_ty = bindings.get(&info.type_var_id).cloned().or_else(|| {
                                args.first().map(|arg| subst.apply(&arg.ty))
                            }).unwrap_or(actual_ret);
                            let concrete_ty = strip_own(&dispatch_ty);
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
                            } else if trait_registry
                                .find_instance(trait_id, &concrete_ty)
                                .is_none()
                            {
                                return Err(no_instance_error(
                                    trait_registry,
                                    trait_id,
                                    &concrete_ty,
                                    expr.span,
                                ));
                            }
                            // Check method-level where constraints
                            for (req_trait, req_var) in &method.constraints {
                                if let Some(resolved) = bindings.get(req_var) {
                                    let concrete = strip_own(resolved);
                                    if leading_type_var(&concrete).is_none() {
                                        if trait_registry.lookup_trait(req_trait).is_some()
                                            && trait_registry
                                                .find_instance(req_trait, &concrete)
                                                .is_none()
                                        {
                                            return Err(no_instance_error(
                                                trait_registry,
                                                req_trait,
                                                &concrete,
                                                expr.span,
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                    // Check calls to constrained functions (e.g., imported `println` requires Show)
                    let fn_reqs = fn_schemes.get(name).map(|s| &s.constraints);
                    if let Some(requirements) = fn_reqs.filter(|r| !r.is_empty()) {
                        // Resolve each constraint's type via bind_type_vars approach
                        let fn_scheme = fn_schemes.get(name);
                        for (req_trait_name, type_var) in requirements {
                            let resolved_ty = fn_scheme.and_then(|scheme| {
                                if let Type::Fn(param_types, ret_ty) = &scheme.ty {
                                    let mut bindings: HashMap<TypeVarId, Type> = HashMap::new();
                                    for (pattern, arg) in param_types.iter().zip(args.iter()) {
                                        if !collect_type_var_bindings_strict(
                                            pattern,
                                            &subst.apply(&arg.ty),
                                            &mut bindings,
                                        ) {
                                            return None;
                                        }
                                    }
                                    if bindings.get(type_var).is_none() {
                                        // Also try return type
                                        let ret_actual = subst.apply(&func.ty);
                                        if let Type::Fn(_, actual_ret) = &ret_actual {
                                            if !collect_type_var_bindings_strict(
                                                ret_ty,
                                                actual_ret,
                                                &mut bindings,
                                            ) {
                                                return None;
                                            }
                                        }
                                    }
                                    bindings.get(type_var).cloned()
                                } else {
                                    None
                                }
                            });
                            if let Some(ty) = resolved_ty {
                                let concrete_ty = strip_own(&ty);
                                if let Some(v) = leading_type_var(&concrete_ty) {
                                    // Type var from enclosing fn's polymorphism —
                                    // constraint will be checked at that fn's call site.
                                    // Unresolved inference vars are NOT in fn_type_vars
                                    // and must be rejected.
                                    if !fn_type_vars.contains(&v) {
                                        return Err(no_instance_error(
                                            trait_registry,
                                            req_trait_name,
                                            &concrete_ty,
                                            expr.span,
                                        ));
                                    }
                                } else {
                                    let missing =
                                        if trait_registry.lookup_trait(req_trait_name).is_some() {
                                            trait_registry
                                                .find_instance(req_trait_name, &concrete_ty)
                                                .is_none()
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
                            && trait_registry
                                .find_instance(trait_name, &operand_ty)
                                .is_none()
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
                            && trait_registry
                                .find_instance(&neg_trait, &operand_ty)
                                .is_none()
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

#[cfg(test)]
mod tests {
    use super::collect_type_var_bindings_strict;
    use crate::types::{Type, TypeVarGen};
    use std::collections::HashMap;

    #[test]
    fn strict_binding_rejects_inconsistent_repeated_vars() {
        let mut gen = TypeVarGen::new();
        let tv = gen.fresh();
        let pattern = Type::Tuple(vec![Type::Var(tv), Type::Var(tv)]);
        let actual = Type::Tuple(vec![Type::Int, Type::String]);
        let mut bindings = HashMap::new();
        assert!(!collect_type_var_bindings_strict(&pattern, &actual, &mut bindings));
    }
}
