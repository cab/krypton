use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, UnaryOp};

use crate::trait_registry::TraitRegistry;
use crate::typed_ast::{
    ResolvedBindingRef, ResolvedCallableRef, ResolvedTraitMethodRef, TraitName, TypedExpr,
    TypedExprKind,
};
use crate::types;
use crate::types::{Substitution, Type, TypeScheme, TypeVarId};
use crate::unify::{SpannedTypeError, TypeError};

use super::{
    free_vars, leading_type_var, match_type_with_bindings, no_instance_error, spanned, strip_own,
};

fn bare_function_ref(expr: &TypedExpr) -> Option<(&str, &ResolvedCallableRef)> {
    match &expr.kind {
        TypedExprKind::Var(name) => match expr.resolved_ref.as_ref() {
            Some(ResolvedBindingRef::Callable(callable_ref)) => Some((name.as_str(), callable_ref)),
            _ => None,
        },
        TypedExprKind::TypeApp { expr, .. } => bare_function_ref(expr),
        _ => None,
    }
}

fn resolve_function_ref_requirement_type(
    trait_name: &str,
    type_var: TypeVarId,
    declared_param_types: &[(crate::types::ParamMode, Type)],
    actual_param_types: &[(crate::types::ParamMode, Type)],
) -> Option<Type> {
    let _ = trait_name;
    let mut bindings = HashMap::new();
    for ((_, declared), (_, actual)) in declared_param_types.iter().zip(actual_param_types.iter()) {
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

fn typed_callee_resolved_ref(expr: &TypedExpr) -> Option<&ResolvedBindingRef> {
    match &expr.kind {
        TypedExprKind::Var(_) => expr.resolved_ref.as_ref(),
        TypedExprKind::TypeApp { expr: inner, .. } => expr
            .resolved_ref
            .as_ref()
            .or_else(|| typed_callee_resolved_ref(inner)),
        _ => expr.resolved_ref.as_ref(),
    }
}

/// Collect type variable bindings while enforcing consistency for repeated vars.
/// Fixed non-variable structure that does not bind anything is ignored.
pub(super) fn collect_type_var_bindings_strict(
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
        (Type::Own(p), _) | (Type::Shape(p), _) | (Type::MaybeOwn(_, p), _) => {
            collect_type_var_bindings_strict(p, actual, bindings)
        }
        (_, Type::Own(a)) | (_, Type::Shape(a)) | (_, Type::MaybeOwn(_, a)) => {
            collect_type_var_bindings_strict(pattern, a, bindings)
        }
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
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) if p_name == a_name => p_args
            .iter()
            .zip(a_args.iter())
            .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings)),
        (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
            p_params
                .iter()
                .zip(a_params.iter())
                .all(|((_, p), (_, a))| collect_type_var_bindings_strict(p, a, bindings))
                && collect_type_var_bindings_strict(p_ret, a_ret, bindings)
        }
        (Type::Tuple(p_elems), Type::Tuple(a_elems)) => p_elems
            .iter()
            .zip(a_elems.iter())
            .all(|(p, a)| collect_type_var_bindings_strict(p, a, bindings)),
        _ => true,
    }
}

pub(super) fn check_constrained_function_refs(
    expr: &TypedExpr,
    current_requirements: &[(TraitName, Vec<TypeVarId>)],
    fn_schemes: &HashMap<String, TypeScheme>,
    trait_registry: &TraitRegistry,
    var_names: &HashMap<TypeVarId, String>,
) -> Result<(), SpannedTypeError> {
    let mut work: Vec<&TypedExpr> = vec![expr];
    while let Some(expr) = work.pop() {
        if let Some((name, _callable_ref)) = bare_function_ref(expr) {
            let fn_type = match &expr.ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            if let Type::Fn(actual_param_types, _) = fn_type {
                // Functions without constraints have no entry
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

                    let mut unsatisfied_constraints: Vec<(String, String)> = Vec::new();

                    for (req_trait_name, req_type_vars) in &requirements {
                        for req_type_var in req_type_vars {
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
                                let missing =
                                    if trait_registry.lookup_trait(req_trait_name).is_some() {
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
                                        var_names,
                                    ));
                                }
                                continue;
                            }

                            if let Type::Var(type_var) = requirement_ty {
                                if current_requirements.iter().any(
                                    |(trait_name, current_type_vars)| {
                                        trait_name == req_trait_name
                                            && current_type_vars.contains(&type_var)
                                    },
                                ) {
                                    continue;
                                }
                            }

                            if current_requirements
                                .iter()
                                .any(|(trait_name, _)| trait_name == req_trait_name)
                            {
                                continue;
                            }

                            let type_param_name = scheme
                                .var_names
                                .get(req_type_var)
                                .cloned()
                                .unwrap_or_else(|| format!("?{}", req_type_var.0));
                            unsatisfied_constraints
                                .push((req_trait_name.local_name.clone(), type_param_name));
                        }
                    }

                    if !unsatisfied_constraints.is_empty() {
                        return Err(spanned(
                            TypeError::ConstrainedFunctionRef {
                                name: name.to_string(),
                                constraints: unsatisfied_constraints,
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
                    if let Some(guard) = &arm.guard {
                        work.push(guard);
                    }
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
            TypedExprKind::Discharge(inner) => work.push(inner),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }

    Ok(())
}

/// Detect trait method calls on type variables and collect as constraints (used for codegen dict params).
pub(super) fn detect_trait_constraints(
    expr: &TypedExpr,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_type_param_vars: &HashSet<TypeVarId>,
    fn_schemes: &HashMap<String, TypeScheme>,
    constraints: &mut Vec<(TraitName, Vec<TypeVarId>)>,
) {
    walk_trait_method_calls(
        expr,
        trait_registry,
        subst,
        fn_type_param_vars,
        fn_schemes,
        &mut |trait_name, vars| {
            constraints.push((trait_name, vars));
        },
    );
}

/// Validate that all trait method calls on type variables have corresponding declared constraints.
pub(super) fn validate_trait_constraints(
    expr: &TypedExpr,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_type_param_vars: &HashSet<TypeVarId>,
    declared_constraints: &[(TraitName, Vec<TypeVarId>)],
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
        trait_registry,
        subst,
        fn_type_param_vars,
        &empty_fn_schemes,
        &mut |trait_name, vars| {
            if first_error.is_some() {
                return;
            }
            // A declared constraint satisfies the use if it names the same trait
            // and its type-var tuple matches position-by-position. For single-param
            // traits this degrades to the previous `contains(&var)` check because
            // both sides are length 1.
            let is_declared = declared_constraints.iter().any(|(t, declared_vars)| {
                t.local_name == trait_name.local_name && declared_vars.as_slice() == vars.as_slice()
            });
            if !is_declared {
                // For diagnostics, show the first position's name (existing
                // single-param error rendering).
                let type_var_display = vars.first().and_then(|v| type_var_names.get(v).cloned());
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

/// Shared walker: finds trait method calls on type variables and invokes the
/// callback with the **full position tuple** of the trait's type arguments.
///
/// For a single-parameter trait this is `vec![v]`; for multi-parameter traits
/// like `Convert[a, b]` called as `convert(x): b` where `x: a`, this is
/// `vec![a_var, b_var]`. The callback is only invoked if **every** trait type
/// parameter resolves to a fresh type var that belongs to `fn_type_param_vars`.
/// Positions that resolve to concrete types don't generate constraint
/// requirements on the enclosing function.
fn walk_trait_method_calls(
    expr: &TypedExpr,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_type_param_vars: &HashSet<TypeVarId>,
    fn_schemes: &HashMap<String, TypeScheme>,
    callback: &mut dyn FnMut(TraitName, Vec<TypeVarId>),
) {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args, .. } => {
                if let Some(ResolvedBindingRef::TraitMethod(ResolvedTraitMethodRef {
                    trait_name: trait_id,
                    method_name,
                })) = typed_callee_resolved_ref(func)
                {
                    let info = trait_registry
                        .lookup_trait(trait_id)
                        .expect("trait in trait_method_map must be in registry");

                    // Build a type-var → resolved-Type binding map by unifying
                    // the method's declared parameter/return types against the
                    // call-site's actual types. This carries bindings for every
                    // trait type-parameter (not just the primary dispatch var).
                    let mut bindings: HashMap<TypeVarId, Type> = HashMap::new();
                    if let Some(method) = info.methods.iter().find(|m| m.name == *method_name) {
                        for ((_, pattern), arg) in method.param_types.iter().zip(args.iter()) {
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
                    }

                    // For each trait type-parameter, extract a leading type var
                    // from its resolved binding (or fall back to the param id
                    // itself, which may still be a free var in fn_type_param_vars).
                    let mut position_vars: Vec<TypeVarId> =
                        Vec::with_capacity(info.type_var_ids.len());
                    let mut all_free_params = true;
                    for tv_id in &info.type_var_ids {
                        let resolved = bindings
                            .get(tv_id)
                            .cloned()
                            .map(|t| subst.apply(&t))
                            .unwrap_or(Type::Var(*tv_id));
                        let stripped = strip_own(&resolved);
                        match leading_type_var(&stripped) {
                            Some(v) if fn_type_param_vars.contains(&v) => {
                                position_vars.push(v);
                            }
                            _ => {
                                all_free_params = false;
                                break;
                            }
                        }
                    }
                    if all_free_params && !position_vars.is_empty() {
                        callback(trait_id.clone(), position_vars);
                    }

                    // Method-level where-constraints propagate independently.
                    if let Some(method) = info.methods.iter().find(|m| m.name == *method_name) {
                        if !method.constraints.is_empty() {
                            for (req_trait, req_vars) in &method.constraints {
                                let mut resolved_vars: Vec<TypeVarId> =
                                    Vec::with_capacity(req_vars.len());
                                let mut all_ok = true;
                                for req_var in req_vars {
                                    let resolved = bindings
                                        .get(req_var)
                                        .cloned()
                                        .map(|t| subst.apply(&t))
                                        .unwrap_or(Type::Var(*req_var));
                                    let concrete = strip_own(&resolved);
                                    match leading_type_var(&concrete) {
                                        Some(v) if fn_type_param_vars.contains(&v) => {
                                            resolved_vars.push(v);
                                        }
                                        _ => {
                                            all_ok = false;
                                            break;
                                        }
                                    }
                                }
                                if all_ok && !resolved_vars.is_empty() {
                                    callback(req_trait.clone(), resolved_vars);
                                }
                            }
                        }
                    }
                }
                // Also detect calls to constrained regular functions (e.g., println where a: Show)
                if matches!(
                    typed_callee_resolved_ref(func),
                    Some(ResolvedBindingRef::Callable(_))
                ) {
                    if let Some(name) = typed_callee_var_name(func) {
                        if let Some(scheme) =
                            fn_schemes.get(name).filter(|s| !s.constraints.is_empty())
                        {
                            let declared_param_types = match &scheme.ty {
                                Type::Fn(params, _) => params.as_slice(),
                                _ => &[],
                            };
                            let actual_param_types: Vec<(crate::types::ParamMode, Type)> = args
                                .iter()
                                .map(|a| (crate::types::ParamMode::Consume, subst.apply(&a.ty)))
                                .collect();
                            for (req_trait, req_vars) in &scheme.constraints {
                                let mut resolved_vars: Vec<TypeVarId> =
                                    Vec::with_capacity(req_vars.len());
                                let mut all_ok = true;
                                for req_var in req_vars {
                                    let resolved = resolve_function_ref_requirement_type(
                                        &req_trait.local_name,
                                        *req_var,
                                        declared_param_types,
                                        &actual_param_types,
                                    );
                                    let v = resolved
                                        .as_ref()
                                        .and_then(|t| leading_type_var(&strip_own(t)));
                                    match v {
                                        Some(v) if fn_type_param_vars.contains(&v) => {
                                            resolved_vars.push(v);
                                        }
                                        _ => {
                                            all_ok = false;
                                            break;
                                        }
                                    }
                                }
                                if all_ok && !resolved_vars.is_empty() {
                                    callback(req_trait.clone(), resolved_vars);
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
                    if let Some(guard) = &arm.guard {
                        work.push(guard);
                    }
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
                                _ => unreachable!("ICE: unknown numeric op trait: {tn}"),
                            };
                            callback(TraitName::new(module.into(), tn.into()), vec![v]);
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
                            callback(TraitName::core_neg(), vec![v]);
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
            TypedExprKind::Discharge(inner) => work.push(inner),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }
}

/// Walk a typed AST looking for calls to trait methods. For each call,
/// resolve the argument type and verify that a matching instance exists.
/// Also checks calls to imported constrained functions (via `TypeScheme.constraints`).
pub(super) fn check_trait_instances(
    expr: &TypedExpr,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_schemes: &HashMap<String, TypeScheme>,
    fn_type_vars: &HashSet<TypeVarId>,
    var_names: &HashMap<TypeVarId, String>,
) -> Result<(), SpannedTypeError> {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args, .. } => {
                if let Some(ResolvedBindingRef::TraitMethod(ResolvedTraitMethodRef {
                    trait_name: trait_id,
                    method_name,
                })) = typed_callee_resolved_ref(func)
                {
                    // trait_method_map is derived from trait_registry, so lookup cannot fail
                    let info = trait_registry
                        .lookup_trait(trait_id)
                        .expect("trait in trait_method_map must be in registry");
                    if let Some(method) = info.methods.iter().find(|m| m.name == *method_name) {
                        let mut bindings = HashMap::new();
                        // Bind from params
                        for ((_, pattern), arg) in method.param_types.iter().zip(args.iter()) {
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
                        // Multi-parameter trait method validation.
                        // The single-param dispatch logic below assumes a single
                        // dispatch type variable; for multi-param traits we instead
                        // build the full position tuple and look up via
                        // `find_instance_multi`.
                        if info.type_var_ids.len() > 1 {
                            let mut tys: Vec<Type> = Vec::with_capacity(info.type_var_ids.len());
                            let mut any_unresolved = false;
                            let mut any_forwarded = false;
                            let mut unresolved_names: Vec<String> = Vec::new();
                            for (i, tv_id) in info.type_var_ids.iter().enumerate() {
                                let raw = bindings
                                    .get(tv_id)
                                    .cloned()
                                    .map(|t| subst.apply(&t))
                                    .unwrap_or_else(|| Type::Var(*tv_id));
                                let stripped = strip_own(&raw);
                                if let Some(v) = leading_type_var(&stripped) {
                                    if fn_type_vars.contains(&v) {
                                        // Position resolves to one of the
                                        // enclosing function's quantified
                                        // type vars — the constraint is
                                        // forwarded via a `where` clause
                                        // and will be dispatched at the
                                        // caller. `validate_trait_constraints`
                                        // has already verified the bound
                                        // was declared.
                                        any_forwarded = true;
                                    } else {
                                        any_unresolved = true;
                                        let name = info
                                            .type_var_names
                                            .get(i)
                                            .cloned()
                                            .unwrap_or_else(|| format!("?{}", tv_id.0));
                                        unresolved_names.push(name);
                                    }
                                }
                                tys.push(stripped);
                            }
                            if any_unresolved {
                                return Err(spanned(
                                    TypeError::UnresolvedMultiParamConstraint {
                                        trait_name: trait_id.local_name.clone(),
                                        params: unresolved_names,
                                    },
                                    expr.span,
                                ));
                            }
                            if any_forwarded {
                                // Don't attempt a concrete instance lookup
                                // when the positions are polymorphic in the
                                // enclosing fn — there's nothing to dispatch
                                // here, the caller will provide the dict.
                            } else if trait_registry.find_instance_multi(trait_id, &tys).is_none() {
                                // Reuse the single-param error path for the
                                // first concrete position; the joined display
                                // form is handled inside the registry.
                                let display = tys
                                    .iter()
                                    .map(|t| format!("{t}"))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                return Err(spanned(
                                    TypeError::NoInstance {
                                        trait_name: trait_id.local_name.clone(),
                                        ty: display,
                                        required_by: None,
                                    },
                                    expr.span,
                                ));
                            }
                        } else {
                            // Single-parameter dispatch (existing path).
                            let dispatch_ty = bindings
                                .get(&info.type_var_id)
                                .cloned()
                                .or_else(|| args.first().map(|arg| subst.apply(&arg.ty)))
                                .unwrap_or(actual_ret);
                            let concrete_ty = strip_own(&dispatch_ty);
                            if let Some(v) = leading_type_var(&concrete_ty) {
                                if !fn_type_vars.contains(&v) {
                                    return Err(spanned(
                                        TypeError::AmbiguousType {
                                            trait_name: trait_id.local_name.clone(),
                                            method_name: method_name.to_string(),
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
                                    var_names,
                                ));
                            }
                        }
                        // Check method-level where constraints
                        for (req_trait, req_vars) in &method.constraints {
                            for req_var in req_vars {
                                if let Some(resolved) = bindings.get(req_var) {
                                    let concrete = strip_own(resolved);
                                    if leading_type_var(&concrete).is_none()
                                        && trait_registry.lookup_trait(req_trait).is_some()
                                        && trait_registry
                                            .find_instance(req_trait, &concrete)
                                            .is_none()
                                    {
                                        return Err(no_instance_error(
                                            trait_registry,
                                            req_trait,
                                            &concrete,
                                            expr.span,
                                            var_names,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
                // Check calls to constrained functions (e.g., imported `println` requires Show)
                if matches!(
                    typed_callee_resolved_ref(func),
                    Some(ResolvedBindingRef::Callable(_))
                ) {
                    if let Some(name) = typed_callee_var_name(func) {
                        let fn_reqs = fn_schemes.get(name).map(|s| &s.constraints);
                        if let Some(requirements) = fn_reqs.filter(|r| !r.is_empty()) {
                            // Resolve each constraint's type via bind_type_vars approach
                            let fn_scheme = fn_schemes.get(name);
                            for (req_trait_name, type_vars) in requirements {
                                // Build bindings once per constraint so we can
                                // resolve every position and dispatch multi-param
                                // constraints against `find_instance_for` rather
                                // than iterating positions independently (which
                                // would mis-dispatch a multi-param trait through
                                // the single-param `find_instance`).
                                let constraint_bindings: Option<HashMap<TypeVarId, Type>> =
                                    fn_scheme.and_then(|scheme| {
                                        if let Type::Fn(param_types, ret_ty) = &scheme.ty {
                                            let mut bindings: HashMap<TypeVarId, Type> =
                                                HashMap::new();
                                            for ((_, pattern), arg) in
                                                param_types.iter().zip(args.iter())
                                            {
                                                if !collect_type_var_bindings_strict(
                                                    pattern,
                                                    &subst.apply(&arg.ty),
                                                    &mut bindings,
                                                ) {
                                                    return None;
                                                }
                                            }
                                            let ret_actual = subst.apply(&func.ty);
                                            if let Type::Fn(_, actual_ret) = &ret_actual {
                                                let _ = collect_type_var_bindings_strict(
                                                    ret_ty,
                                                    actual_ret,
                                                    &mut bindings,
                                                );
                                            }
                                            Some(bindings)
                                        } else {
                                            None
                                        }
                                    });

                                let Some(bindings) = constraint_bindings else {
                                    continue;
                                };

                                // Resolve each position. If any position is
                                // still a type var in the enclosing fn's
                                // polymorphism the constraint is forwarded —
                                // skip the dispatch check. If it's an
                                // unresolved inference var (not in fn_type_vars)
                                // report the usual no-instance error.
                                let mut position_tys: Vec<Type> =
                                    Vec::with_capacity(type_vars.len());
                                let mut forwarded = false;
                                let mut resolution_failed = false;
                                for type_var in type_vars {
                                    let Some(ty) = bindings.get(type_var).cloned() else {
                                        resolution_failed = true;
                                        break;
                                    };
                                    let concrete = strip_own(&ty);
                                    if let Some(v) = leading_type_var(&concrete) {
                                        if fn_type_vars.contains(&v) {
                                            forwarded = true;
                                        } else {
                                            return Err(no_instance_error(
                                                trait_registry,
                                                req_trait_name,
                                                &concrete,
                                                expr.span,
                                                var_names,
                                            ));
                                        }
                                    }
                                    position_tys.push(concrete);
                                }
                                if resolution_failed || forwarded {
                                    continue;
                                }

                                // All positions are concrete — dispatch via the
                                // canonical arity-aware lookup.
                                if trait_registry.lookup_trait(req_trait_name).is_none()
                                    || trait_registry
                                        .find_instance_for(req_trait_name, &position_tys)
                                        .is_none()
                                {
                                    let display_ty =
                                        position_tys.first().cloned().unwrap_or(Type::Unit);
                                    return Err(no_instance_error(
                                        trait_registry,
                                        req_trait_name,
                                        &display_ty,
                                        expr.span,
                                        var_names,
                                    ));
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
                    if !matches!(operand_ty, Type::Var(_))
                        && trait_registry.lookup_trait(trait_name).is_some()
                        && trait_registry
                            .find_instance(trait_name, &operand_ty)
                            .is_none()
                    {
                        return Err(no_instance_error(
                            trait_registry,
                            trait_name,
                            &operand_ty,
                            expr.span,
                            var_names,
                        ));
                    }
                }
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { op, operand } => {
                if matches!(op, UnaryOp::Neg) {
                    let neg_trait = TraitName::core_neg();
                    let operand_ty = strip_own(&subst.apply(&operand.ty));
                    if !matches!(operand_ty, Type::Var(_))
                        && trait_registry.lookup_trait(&neg_trait).is_some()
                        && trait_registry
                            .find_instance(&neg_trait, &operand_ty)
                            .is_none()
                    {
                        return Err(no_instance_error(
                            trait_registry,
                            &neg_trait,
                            &operand_ty,
                            expr.span,
                            var_names,
                        ));
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
                    if let Some(guard) = &arm.guard {
                        work.push(guard);
                    }
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
            TypedExprKind::Discharge(inner) => work.push(inner),
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
        assert!(!collect_type_var_bindings_strict(
            &pattern,
            &actual,
            &mut bindings
        ));
    }
}
