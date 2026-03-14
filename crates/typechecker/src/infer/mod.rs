use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{
    BinOp, Decl, Expr, ExternMethod, Lit, Module, Span, TypeConstraint,
    TypeDecl, TypeDeclKind, TypeExpr, TypeParam, UnaryOp, Variant, Visibility,
};

use crate::scc;
use crate::trait_registry::{InstanceInfo, TraitInfo, TraitMethod, TraitRegistry};
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{
    self, ExportedTraitDef, ExportedTraitMethod, ExternFnInfo, FnOrigin, InstanceDefInfo,
    TraitDefInfo, TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedModule, TypedPattern,
};
use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{unify, SpannedTypeError, TypeError};

fn find_type_decl<'a>(decls: &'a [Decl], name: &str) -> Option<&'a TypeDecl> {
    decls.iter().find_map(|d| match d {
        Decl::DefType(td) if td.name == name => Some(td),
        _ => None,
    })
}

fn constructor_names(td: &TypeDecl) -> Vec<String> {
    match &td.kind {
        TypeDeclKind::Sum { variants } => variants.iter().map(|v| v.name.clone()).collect(),
        TypeDeclKind::Record { .. } => vec![td.name.clone()],
    }
}

mod expr;
mod imports;
mod pattern;

#[derive(Clone)]
pub(super) struct QualifiedExport {
    pub(super) local_name: String,
    pub(super) scheme: TypeScheme,
}

#[derive(Clone)]
pub(super) struct QualifiedModuleBinding {
    pub(super) module_path: String,
    pub(super) exports: HashMap<String, QualifiedExport>,
}

fn is_callable_scheme(scheme: &TypeScheme) -> bool {
    match &scheme.ty {
        Type::Fn(_, _) => true,
        Type::Own(inner) => matches!(inner.as_ref(), Type::Fn(_, _)),
        _ => false,
    }
}

pub(super) fn qualifier_suggested_usage(
    qualifier: &str,
    binding: &QualifiedModuleBinding,
) -> Option<String> {
    binding
        .exports
        .iter()
        .map(|(name, export)| (name.as_str(), is_callable_scheme(&export.scheme)))
        .min_by_key(|(name, callable)| (!*callable, *name))
        .map(|(name, callable)| {
            if callable {
                format!("{qualifier}.{name}(...)")
            } else {
                format!("{qualifier}.{name}")
            }
        })
}

fn build_type_param_maps(
    params: &[TypeParam],
    gen: &mut TypeVarGen,
) -> (HashMap<String, TypeVarId>, HashMap<String, usize>) {
    let mut ids = HashMap::new();
    let mut arities = HashMap::new();
    for param in params {
        ids.insert(param.name.clone(), gen.fresh());
        arities.insert(param.name.clone(), param.arity);
    }
    (ids, arities)
}

/// Strip `Own` wrapper from non-function types.
/// Used at consumption sites (binary ops, if conditions, etc.) where
/// the ownership wrapper is not meaningful.
pub(super) fn strip_own(ty: &Type) -> Type {
    match ty {
        Type::Own(inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => *inner.clone(),
        other => other.clone(),
    }
}

/// Attempt call-site own→T coercion: if an arg is `Own(inner)` and the
/// corresponding param is a concrete non-Own, non-Var type, strip the Own wrapper.
pub(super) fn coerce_own_args(func_ty: &Type, arg_types: &[Type], subst: &Substitution) -> Vec<Type> {
    let walked = subst.apply(func_ty);
    if let Type::Fn(param_types, _) = &walked {
        arg_types
            .iter()
            .enumerate()
            .map(|(i, arg)| {
                let resolved_arg = subst.apply(arg);
                if let Some(param) = param_types.get(i) {
                    let resolved_param = subst.apply(param);
                    // Allow fn() → own fn(): wrap bare Fn arg with Own when param expects Own(Fn(...))
                    if matches!(&resolved_arg, Type::Fn(_, _))
                        && matches!(&resolved_param, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)))
                    {
                        return Type::Own(Box::new(resolved_arg));
                    }
                    // Strip Own wrapper for non-function types (existing behavior),
                    // but keep Own(Fn(..)) intact so own fn() → fn() fails at unification.
                    if let Type::Own(inner) = &resolved_arg {
                        if !matches!(inner.as_ref(), Type::Fn(_, _))
                            && !matches!(resolved_param, Type::Own(_) | Type::Var(_))
                        {
                            return *inner.clone();
                        }
                    }
                }
                arg.clone()
            })
            .collect()
    } else {
        arg_types.to_vec()
    }
}

/// Collect free type variables in a type.
fn free_vars(ty: &Type) -> HashSet<TypeVarId> {
    let mut out = HashSet::new();
    free_vars_into(ty, &mut out);
    out
}

fn match_type_with_bindings(
    pattern: &Type,
    actual: &Type,
    bindings: &mut HashMap<TypeVarId, Type>,
) -> bool {
    match (pattern, actual) {
        (Type::Var(id), _) => match bindings.get(id) {
            Some(existing) => existing == actual,
            None => {
                bindings.insert(*id, actual.clone());
                true
            }
        },
        (Type::Int, Type::Int)
        | (Type::Float, Type::Float)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Unit, Type::Unit) => true,
        (Type::Own(lhs), Type::Own(rhs)) => match_type_with_bindings(lhs, rhs, bindings),
        (Type::Fn(lhs_params, lhs_ret), Type::Fn(rhs_params, rhs_ret)) => {
            lhs_params.len() == rhs_params.len()
                && lhs_params
                    .iter()
                    .zip(rhs_params.iter())
                    .all(|(lhs, rhs)| match_type_with_bindings(lhs, rhs, bindings))
                && match_type_with_bindings(lhs_ret, rhs_ret, bindings)
        }
        (Type::Named(lhs_name, lhs_args), Type::Named(rhs_name, rhs_args)) => {
            lhs_name == rhs_name
                && lhs_args.len() == rhs_args.len()
                && lhs_args
                    .iter()
                    .zip(rhs_args.iter())
                    .all(|(lhs, rhs)| match_type_with_bindings(lhs, rhs, bindings))
        }
        _ => false,
    }
}

fn bare_function_ref_name(expr: &TypedExpr) -> Option<&str> {
    match &expr.kind {
        TypedExprKind::Var(name) => Some(name.as_str()),
        TypedExprKind::TypeApp { expr } => bare_function_ref_name(expr),
        _ => None,
    }
}

#[derive(Clone)]
enum FunctionConstraintRef {
    TypeParam { trait_name: String, param_idx: usize },
    TypeVar {
        trait_name: String,
        type_var: TypeVarId,
    },
}

impl FunctionConstraintRef {
    fn trait_name(&self) -> &str {
        match self {
            FunctionConstraintRef::TypeParam { trait_name, .. }
            | FunctionConstraintRef::TypeVar { trait_name, .. } => trait_name,
        }
    }
}

fn resolve_function_ref_requirement_type(
    requirement: &FunctionConstraintRef,
    declared_param_types: &[Type],
    actual_param_types: &[Type],
) -> Option<Type> {
    match requirement {
        FunctionConstraintRef::TypeParam { param_idx, .. } => {
            actual_param_types.get(*param_idx).cloned()
        }
        FunctionConstraintRef::TypeVar { type_var, .. } => {
            let mut bindings = HashMap::new();
            for (declared, actual) in declared_param_types.iter().zip(actual_param_types.iter()) {
                if !match_type_with_bindings(declared, actual, &mut bindings) {
                    return None;
                }
            }
            bindings.get(type_var).cloned()
        }
    }
}

fn check_constrained_function_refs(
    expr: &TypedExpr,
    current_requirements: &[(String, TypeVarId)],
    fn_schemes: &HashMap<String, TypeScheme>,
    fn_constraint_requirements: &HashMap<String, Vec<(String, TypeVarId)>>,
    imported_fn_constraints: &HashMap<String, Vec<(String, usize)>>,
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
                let requirements: Vec<FunctionConstraintRef> =
                    if let Some(reqs) = fn_constraint_requirements.get(name) {
                        reqs.iter()
                            .map(|(trait_name, type_var)| FunctionConstraintRef::TypeVar {
                                trait_name: trait_name.clone(),
                                type_var: *type_var,
                            })
                            .collect()
                    } else if let Some(reqs) = imported_fn_constraints.get(name) {
                        reqs.iter()
                            .map(|(trait_name, param_idx)| FunctionConstraintRef::TypeParam {
                                trait_name: trait_name.clone(),
                                param_idx: *param_idx,
                            })
                            .collect()
                    } else {
                        Vec::new()
                    };

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

                    for requirement in &requirements {
                        let requirement_ty = resolve_function_ref_requirement_type(
                            requirement,
                            declared_param_types,
                            actual_param_types,
                        )
                        .ok_or_else(|| {
                            spanned(
                                TypeError::UnsupportedExpr {
                                    description: format!(
                                        "could not resolve `{}` for constrained function reference `{name}`",
                                        requirement.trait_name()
                                    ),
                                },
                                expr.span,
                            )
                        })?;

                        let requirement_ty = strip_own(&requirement_ty);
                        if free_vars(&requirement_ty).is_empty() {
                            if trait_registry
                                .find_instance(requirement.trait_name(), &requirement_ty)
                                .is_none()
                            {
                                return Err(spanned(
                                    TypeError::NoInstance {
                                        trait_name: requirement.trait_name().to_string(),
                                        ty: format!("{requirement_ty}"),
                                        required_by: None,
                                    },
                                    expr.span,
                                ));
                            }
                            continue;
                        }

                        if let Type::Var(type_var) = requirement_ty {
                            if current_requirements.iter().any(|(trait_name, current_type_var)| {
                                trait_name == requirement.trait_name() && *current_type_var == type_var
                            }) {
                                continue;
                            }
                        }

                        if current_requirements
                            .iter()
                            .any(|(trait_name, _)| trait_name == requirement.trait_name())
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

fn collect_derived_constraints_for_type(
    trait_registry: &TraitRegistry,
    trait_name: &str,
    field_type: &Type,
    local_type_params: &HashMap<TypeVarId, String>,
    visited: &mut HashSet<(String, String)>,
    constraints: &mut Vec<TypeConstraint>,
) -> bool {
    let key = (trait_name.to_string(), format!("{field_type}"));
    if !visited.insert(key) {
        return true;
    }

    if let Type::Var(type_var) = field_type {
        if let Some(type_var_name) = local_type_params.get(type_var) {
            if !constraints.iter().any(|constraint| {
                constraint.trait_name == trait_name && constraint.type_var == *type_var_name
            }) {
                constraints.push(TypeConstraint {
                    type_var: type_var_name.clone(),
                    trait_name: trait_name.to_string(),
                    span: (0, 0),
                });
            }
            return true;
        }
    }

    let Some(instance) = trait_registry.find_instance(trait_name, field_type) else {
        return false;
    };

    if instance.constraints.is_empty() {
        return true;
    }

    let mut bindings = HashMap::new();
    if !match_type_with_bindings(&instance.target_type, field_type, &mut bindings) {
        return false;
    }

    for constraint in &instance.constraints {
        let Some(type_var_id) = instance.type_var_ids.get(&constraint.type_var) else {
            return false;
        };
        let Some(required_type) = bindings.get(type_var_id) else {
            return false;
        };
        if !collect_derived_constraints_for_type(
            trait_registry,
            &constraint.trait_name,
            required_type,
            local_type_params,
            visited,
            constraints,
        ) {
            return false;
        }
    }

    true
}

/// Recursive accumulator for `free_vars`.
fn free_vars_into(ty: &Type, out: &mut HashSet<TypeVarId>) {
    match ty {
        Type::Var(id) => {
            out.insert(*id);
        }
        Type::Fn(params, ret) => {
            for p in params {
                free_vars_into(p, out);
            }
            free_vars_into(ret, out);
        }
        Type::Named(_, args) => {
            for a in args {
                free_vars_into(a, out);
            }
        }
        Type::App(ctor, args) => {
            free_vars_into(ctor, out);
            for a in args {
                free_vars_into(a, out);
            }
        }
        Type::Own(inner) => free_vars_into(inner, out),
        Type::Tuple(elems) => {
            for e in elems {
                free_vars_into(e, out);
            }
        }
        _ => {}
    }
}

/// Collect free type variables across all bindings in the environment.
fn free_vars_env(env: &TypeEnv, subst: &Substitution) -> HashSet<TypeVarId> {
    let mut s = HashSet::new();
    env.for_each_scheme(|scheme| {
        let applied = subst.apply_scheme(scheme);
        let fv = free_vars(&applied.ty);
        // Remove quantified vars
        for v in &fv {
            if !applied.vars.contains(v) {
                s.insert(*v);
            }
        }
    });
    s
}

fn collect_type_expr_var_names(texpr: &krypton_parser::ast::TypeExpr, out: &mut HashSet<String>) {
    match texpr {
        krypton_parser::ast::TypeExpr::Var { name, .. } => {
            out.insert(name.clone());
        }
        krypton_parser::ast::TypeExpr::App { args, .. } => {
            for arg in args {
                collect_type_expr_var_names(arg, out);
            }
        }
        krypton_parser::ast::TypeExpr::Fn { params, ret, .. } => {
            for param in params {
                collect_type_expr_var_names(param, out);
            }
            collect_type_expr_var_names(ret, out);
        }
        krypton_parser::ast::TypeExpr::Own { inner, .. } => {
            collect_type_expr_var_names(inner, out);
        }
        krypton_parser::ast::TypeExpr::Tuple { elements, .. } => {
            for element in elements {
                collect_type_expr_var_names(element, out);
            }
        }
        krypton_parser::ast::TypeExpr::Named { .. } => {}
    }
}

fn reserve_gen_for_env_schemes(env: &TypeEnv, gen: &mut TypeVarGen) {
    let mut next_reserved = 0;
    env.for_each_scheme(|scheme| {
        for var in &scheme.vars {
            next_reserved = next_reserved.max(*var + 1);
        }
        for var in free_vars(&scheme.ty) {
            next_reserved = next_reserved.max(var + 1);
        }
    });
    gen.reserve_at_least(next_reserved);
}

/// Generalize a type into a type scheme by quantifying over variables
/// free in the type but not free in the environment.
pub(super) fn generalize(ty: &Type, env: &TypeEnv, subst: &Substitution) -> TypeScheme {
    let ty = subst.apply(ty);
    let ty_vars = free_vars(&ty);
    let env_vars = free_vars_env(env, subst);
    let mut vars: Vec<TypeVarId> = ty_vars.difference(&env_vars).copied().collect();
    vars.sort();
    TypeScheme { vars, ty }
}

/// Attach a span to a TypeError, producing a SpannedTypeError.
pub(super) fn spanned(error: TypeError, span: krypton_parser::ast::Span) -> SpannedTypeError {
    SpannedTypeError {
        error,
        span,
        note: None,
        secondary_span: None,
    }
}

/// Recursively replace Type::Var(old_id) with Type::Var(new_id) in a type tree.
fn remap_type_var(ty: &Type, old_id: u32, new_id: u32) -> Type {
    match ty {
        Type::Var(id) if *id == old_id => Type::Var(new_id),
        Type::Fn(params, ret) => Type::Fn(
            params
                .iter()
                .map(|p| remap_type_var(p, old_id, new_id))
                .collect(),
            Box::new(remap_type_var(ret, old_id, new_id)),
        ),
        Type::Named(name, args) => Type::Named(
            name.clone(),
            args.iter()
                .map(|a| remap_type_var(a, old_id, new_id))
                .collect(),
        ),
        Type::App(ctor, args) => Type::App(
            Box::new(remap_type_var(ctor, old_id, new_id)),
            args.iter()
                .map(|a| remap_type_var(a, old_id, new_id))
                .collect(),
        ),
        Type::Tuple(elems) => Type::Tuple(
            elems
                .iter()
                .map(|e| remap_type_var(e, old_id, new_id))
                .collect(),
        ),
        Type::Own(inner) => Type::Own(Box::new(remap_type_var(inner, old_id, new_id))),
        _ => ty.clone(),
    }
}

/// Check if a type is concretely not a function (after walking substitution).
pub(super) fn is_concrete_non_function(ty: &Type, subst: &Substitution) -> bool {
    let walked = subst.apply(ty);
    match &walked {
        Type::Var(_) | Type::Fn(_, _) => false,
        Type::Own(inner) => is_concrete_non_function(inner, subst),
        _ => true,
    }
}

pub(super) fn instantiate_scheme_with_types(
    scheme: &TypeScheme,
    explicit_types: &[Type],
    span: Span,
    gen: &mut TypeVarGen,
) -> Result<Type, SpannedTypeError> {
    if explicit_types.len() > scheme.vars.len() {
        return Err(spanned(
            TypeError::WrongArity {
                expected: scheme.vars.len(),
                actual: explicit_types.len(),
            },
            span,
        ));
    }

    let mut sub = Substitution::new();
    for &var in &scheme.vars {
        sub = sub.compose(&Substitution::bind(var, Type::Var(gen.fresh())));
    }
    let offset = scheme.vars.len() - explicit_types.len();
    for (&var, ty) in scheme.vars.iter().skip(offset).zip(explicit_types.iter()) {
        sub = sub.compose(&Substitution::bind(var, ty.clone()));
    }
    Ok(sub.apply(&scheme.ty))
}

pub(crate) use expr::InferenceContext;

/// Infer the type of an expression using Algorithm J.
#[tracing::instrument(level = "trace", skip_all)]
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<Type, SpannedTypeError> {
    let empty_tpm = HashMap::new();
    let empty_tpa = HashMap::new();
    let empty_qm = HashMap::new();
    let mut ctx = InferenceContext {
        env,
        subst,
        gen,
        registry: None,
        recur_params: None,
        let_own_spans: None,
        lambda_own_captures: None,
        type_param_map: &empty_tpm,
        type_param_arity: &empty_tpa,
        qualified_modules: &empty_qm,
    };
    ctx.infer_expr_inner(expr, None).map(|te| te.ty)
}


/// Instantiate a field type from the registry by substituting the original
/// type parameter var ids with the concrete type arguments.
pub(super) fn instantiate_field_type(
    field_ty: &Type,
    info: &type_registry::TypeInfo,
    type_args: &[Type],
) -> Type {
    if info.type_param_vars.is_empty() {
        return field_ty.clone();
    }
    // Build a substitution from registry's original var ids to the actual type args
    let mut subst = Substitution::new();
    for (var_id, arg) in info.type_param_vars.iter().zip(type_args.iter()) {
        subst.insert(*var_id, arg.clone());
    }
    subst.apply(field_ty)
}

/// Return the name of the first free variable (not in `params`) whose type in
/// `env` (after substitution) is `Own(...)`.
pub(super) fn first_own_capture(
    body: &Expr,
    params: &HashSet<&str>,
    env: &TypeEnv,
    subst: &Substitution,
) -> Option<String> {
    match body {
        Expr::Var { name, .. } => {
            if !params.contains(name.as_str()) {
                if let Some(scheme) = env.lookup(name) {
                    let ty = subst.apply(&scheme.ty);
                    if matches!(ty, Type::Own(_)) {
                        return Some(name.clone());
                    }
                }
            }
            None
        }
        Expr::App { func, args, .. } => first_own_capture(func, params, env, subst).or_else(|| {
            args.iter()
                .find_map(|a| first_own_capture(a, params, env, subst))
        }),
        Expr::TypeApp { expr, .. } => first_own_capture(expr, params, env, subst),
        Expr::Let {
            name,
            value,
            body: let_body,
            ..
        } => {
            if let Some(found) = first_own_capture(value, params, env, subst) {
                return Some(found);
            }
            if let Some(b) = let_body {
                let mut inner = params.clone();
                inner.insert(name.as_str());
                return first_own_capture(b, &inner, env, subst);
            }
            None
        }
        Expr::LetPattern { value, body, .. } => first_own_capture(value, params, env, subst)
            .or_else(|| {
                body.as_ref()
                    .and_then(|b| first_own_capture(b, params, env, subst))
            }),
        Expr::Do { exprs, .. } => exprs
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst)),
        Expr::If {
            cond, then_, else_, ..
        } => first_own_capture(cond, params, env, subst)
            .or_else(|| first_own_capture(then_, params, env, subst))
            .or_else(|| first_own_capture(else_, params, env, subst)),
        Expr::Match {
            scrutinee, arms, ..
        } => first_own_capture(scrutinee, params, env, subst).or_else(|| {
            arms.iter()
                .find_map(|a| first_own_capture(&a.body, params, env, subst))
        }),
        Expr::BinaryOp { lhs, rhs, .. } => first_own_capture(lhs, params, env, subst)
            .or_else(|| first_own_capture(rhs, params, env, subst)),
        Expr::UnaryOp { operand, .. } => first_own_capture(operand, params, env, subst),
        Expr::Lambda {
            params: inner_params,
            body,
            ..
        } => {
            let mut inner = params.clone();
            for p in inner_params {
                inner.insert(p.name.as_str());
            }
            first_own_capture(body, &inner, env, subst)
        }
        Expr::FieldAccess { expr, .. } => first_own_capture(expr, params, env, subst),
        Expr::StructLit { fields, .. } => fields
            .iter()
            .find_map(|(_, e)| first_own_capture(e, params, env, subst)),
        Expr::StructUpdate { base, fields, .. } => first_own_capture(base, params, env, subst)
            .or_else(|| {
                fields
                    .iter()
                    .find_map(|(_, e)| first_own_capture(e, params, env, subst))
            }),
        Expr::Tuple { elements, .. } => elements
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst)),
        Expr::Recur { args, .. } => args
            .iter()
            .find_map(|a| first_own_capture(a, params, env, subst)),
        Expr::QuestionMark { expr, .. } => first_own_capture(expr, params, env, subst),
        Expr::List { elements, .. } => elements
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst)),
        Expr::Lit { .. } => None,
    }
}

/// Format an inferred type for display, renaming type variables to a, b, c, ...
/// and wrapping polymorphic types in `forall`.
pub fn display_type(ty: &Type, subst: &Substitution, env: &TypeEnv) -> String {
    let scheme = generalize(ty, env, subst);
    format!("{}", scheme)
}

/// Walk a typed expression tree and record struct update info for each
/// `StructUpdate` node: maps its span to (type_name, set of updated field names).
fn collect_struct_update_info(
    expr: &TypedExpr,
    info: &mut HashMap<Span, (String, HashSet<String>)>,
) {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::StructUpdate { base, fields } => {
                let inner_ty = match &base.ty {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                if let Type::Named(name, _) = inner_ty {
                    let field_names: HashSet<String> =
                        fields.iter().map(|(n, _)| n.clone()).collect();
                    info.insert(expr.span, (name.clone(), field_names));
                }
                work.push(base);
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
            TypedExprKind::App { func, args } => {
                work.push(func);
                for a in args {
                    work.push(a);
                }
            }
            TypedExprKind::TypeApp { expr } => work.push(expr),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. }
            | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(b) = body {
                    work.push(b);
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
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::Recur(args)
            | TypedExprKind::Tuple(args)
            | TypedExprKind::VecLit(args) => {
                for a in args {
                    work.push(a);
                }
            }
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
        }
    }
}

/// Substitute a type variable with a concrete type throughout a type.
fn substitute_type_var(ty: &Type, var_id: TypeVarId, replacement: &Type) -> Type {
    match ty {
        Type::Var(id) if *id == var_id => replacement.clone(),
        Type::Var(_) | Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit => {
            ty.clone()
        }
        Type::Fn(params, ret) => {
            let new_params = params
                .iter()
                .map(|p| substitute_type_var(p, var_id, replacement))
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
        Type::Tuple(elems) => {
            let new_elems = elems
                .iter()
                .map(|e| substitute_type_var(e, var_id, replacement))
                .collect();
            Type::Tuple(new_elems)
        }
    }
}

fn leading_type_var(ty: &Type) -> Option<TypeVarId> {
    match ty {
        Type::Var(v) => Some(*v),
        Type::App(ctor, _) => leading_type_var(ctor),
        Type::Own(inner) => leading_type_var(inner),
        _ => None,
    }
}

fn typed_callee_var_name(expr: &TypedExpr) -> Option<&str> {
    match &expr.kind {
        TypedExprKind::Var(name) => Some(name.as_str()),
        TypedExprKind::TypeApp { expr } => typed_callee_var_name(expr),
        _ => None,
    }
}

/// Detect trait method calls on type variables (indicating the function needs a dict param).
fn detect_trait_constraints(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, String>,
    subst: &Substitution,
    param_type_var_map: &HashMap<TypeVarId, usize>,
    constraints: &mut Vec<(String, usize)>,
) {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args } => {
                if let Some(name) = typed_callee_var_name(func) {
                    if let Some(trait_name) = trait_method_map.get(name) {
                        if let Some(first_arg) = args.first() {
                            let arg_ty = subst.apply(&first_arg.ty);
                            let concrete_ty = strip_own(&arg_ty);
                            if let Some(v) = leading_type_var(&concrete_ty) {
                                if let Some(param_idx) = param_type_var_map.get(&v).copied() {
                                    constraints.push((trait_name.clone(), param_idx));
                                }
                            }
                        } else {
                            // Zero-arg trait method: check return type for type variable
                            let ret_ty = subst.apply(&func.ty);
                            let concrete_ret = match &ret_ty {
                                Type::Fn(_, ret) => strip_own(ret),
                                other => strip_own(other),
                            };
                            if let Some(v) = leading_type_var(&concrete_ret) {
                                if let Some(param_idx) = param_type_var_map.get(&v).copied() {
                                    constraints.push((trait_name.clone(), param_idx));
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
            TypedExprKind::TypeApp { expr } => work.push(expr),
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
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
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
/// Also checks calls to imported constrained functions (via `fn_constraints`).
fn check_trait_instances(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, String>,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    fn_constraints: &HashMap<String, Vec<(String, usize)>>,
) -> Result<(), SpannedTypeError> {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::App { func, args } => {
                if let Some(name) = typed_callee_var_name(func) {
                    if let Some(trait_name) = trait_method_map.get(name) {
                        if let Some(first_arg) = args.first() {
                            let arg_ty = subst.apply(&first_arg.ty);
                            let concrete_ty = strip_own(&arg_ty);
                            if leading_type_var(&concrete_ty).is_none()
                                && trait_registry
                                    .find_instance(trait_name, &concrete_ty)
                                    .is_none()
                            {
                                return Err(spanned(
                                    TypeError::NoInstance {
                                        trait_name: trait_name.clone(),
                                        ty: format!("{}", concrete_ty),
                                        required_by: None,
                                    },
                                    expr.span,
                                ));
                            }
                        } else {
                            // Zero-arg trait method: check return type for instance
                            let ret_ty = subst.apply(&func.ty);
                            let concrete_ret = match &ret_ty {
                                Type::Fn(_, ret) => strip_own(ret),
                                other => strip_own(other),
                            };
                            if leading_type_var(&concrete_ret).is_none()
                                && trait_registry
                                    .find_instance(trait_name, &concrete_ret)
                                    .is_none()
                            {
                                return Err(spanned(
                                    TypeError::NoInstance {
                                        trait_name: trait_name.clone(),
                                        ty: format!("{}", concrete_ret),
                                        required_by: None,
                                    },
                                    expr.span,
                                ));
                            }
                        }
                    }
                    // Check calls to constrained functions (e.g., imported `println` requires Show)
                    if let Some(constraints) = fn_constraints.get(name) {
                        for (trait_name, param_idx) in constraints {
                            if let Some(arg) = args.get(*param_idx) {
                                let arg_ty = subst.apply(&arg.ty);
                                let concrete_ty = strip_own(&arg_ty);
                                if leading_type_var(&concrete_ty).is_none() {
                                    if trait_registry
                                        .find_instance(trait_name, &concrete_ty)
                                        .is_none()
                                    {
                                        return Err(spanned(
                                            TypeError::NoInstance {
                                                trait_name: trait_name.clone(),
                                                ty: format!("{}", concrete_ty),
                                                required_by: None,
                                            },
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
            TypedExprKind::TypeApp { expr } => work.push(expr),
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let trait_name = match op {
                    BinOp::Add => Some("Add"),
                    BinOp::Sub => Some("Sub"),
                    BinOp::Mul => Some("Mul"),
                    BinOp::Div => Some("Div"),
                    BinOp::Eq | BinOp::Neq => Some("Eq"),
                    BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => Some("Ord"),
                    BinOp::And | BinOp::Or => None,
                };
                if let Some(trait_name) = trait_name {
                    let operand_ty = strip_own(&subst.apply(&lhs.ty));
                    if !matches!(operand_ty, Type::Var(_))
                        && trait_registry
                            .find_instance(trait_name, &operand_ty)
                            .is_none()
                    {
                        return Err(spanned(
                            TypeError::NoInstance {
                                trait_name: trait_name.to_string(),
                                ty: format!("{}", operand_ty),
                                required_by: None,
                            },
                            expr.span,
                        ));
                    }
                }
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { op, operand } => {
                let trait_name = match op {
                    UnaryOp::Neg => Some("Neg"),
                    UnaryOp::Not => None,
                };
                if let Some(trait_name) = trait_name {
                    let operand_ty = strip_own(&subst.apply(&operand.ty));
                    if !matches!(operand_ty, Type::Var(_))
                        && trait_registry
                            .find_instance(trait_name, &operand_ty)
                            .is_none()
                    {
                        return Err(spanned(
                            TypeError::NoInstance {
                                trait_name: trait_name.to_string(),
                                ty: format!("{}", operand_ty),
                                required_by: None,
                            },
                            expr.span,
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

/// Process extern methods from an `extern "class" { ... }` block, binding their
/// types into the environment and returning `ExternFnInfo` entries for codegen.
fn process_extern_methods(
    class_name: &str,
    methods: &[ExternMethod],
    env: &mut TypeEnv,
    gen: &mut TypeVarGen,
    registry: &TypeRegistry,
    span: Span,
    name_filter: Option<&HashSet<&str>>,
    aliases: &HashMap<String, String>,
) -> Result<Vec<ExternFnInfo>, SpannedTypeError> {
    let empty_map = HashMap::new();
    let empty_arity = HashMap::new();
    let mut extern_fns = Vec::new();
    for method in methods {
        let bind_name = aliases.get(&method.name).unwrap_or(&method.name);
        if let Some(filter) = name_filter {
            if !filter.contains(method.name.as_str()) && !filter.contains(bind_name.as_str()) {
                continue;
            }
        }

        let mut scheme_vars = Vec::new();
        let mut param_types = Vec::new();
        for ty_expr in &method.param_types {
            let resolved =
                type_registry::resolve_type_expr(ty_expr, &empty_map, &empty_arity, registry)
                .map_err(|e| spanned(e, span))?;
            if matches!(&resolved, Type::Named(n, args) if n == "Object" && args.is_empty()) {
                let fresh = gen.fresh();
                scheme_vars.push(fresh);
                param_types.push(Type::Var(fresh));
            } else {
                param_types.push(resolved);
            }
        }

        let return_type =
            type_registry::resolve_type_expr(&method.return_type, &empty_map, &empty_arity, registry)
                .map_err(|e| spanned(e, span))?;
        let ret = if matches!(&return_type, Type::Named(n, args) if n == "Object" && args.is_empty())
        {
            let fresh = gen.fresh();
            scheme_vars.push(fresh);
            Type::Var(fresh)
        } else {
            return_type.clone()
        };

        let fn_ty = Type::Fn(param_types.clone(), Box::new(ret));
        let scheme = if scheme_vars.is_empty() {
            TypeScheme::mono(fn_ty)
        } else {
            TypeScheme {
                vars: scheme_vars,
                ty: fn_ty,
            }
        };
        env.bind(bind_name.clone(), scheme);

        // Store concrete types for codegen (Object stays as-is)
        let mut concrete_params = Vec::new();
        for ty_expr in &method.param_types {
            concrete_params.push(
                type_registry::resolve_type_expr(ty_expr, &empty_map, &empty_arity, registry)
                    .map_err(|e| spanned(e, span))?,
            );
        }
        extern_fns.push(ExternFnInfo {
            name: bind_name.clone(),
            java_class: class_name.to_string(),
            param_types: concrete_params,
            return_type,
        });
    }
    Ok(extern_fns)
}

/// Infer types for all top-level definitions in a module.
///
/// Returns a `Vec<TypedModule>` containing the main module (first, `module_path: None`)
/// followed by any imported modules discovered during inference.
///
/// Uses SCC (strongly connected component) analysis to process definitions
/// in dependency order. Functions within the same SCC are inferred together
/// as a mutually recursive group, then generalized before later SCCs see them.
#[tracing::instrument(skip(module, resolver), fields(decls = module.decls.len()))]
pub fn infer_module(
    module: &Module,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<Vec<TypedModule>, SpannedTypeError> {
    use krypton_modules::module_graph;

    // Build the module graph (resolves, parses, toposorts all imports + prelude)
    let graph = module_graph::build_module_graph(module, resolver).map_err(map_graph_error)?;

    // Build parsed module lookup for import binding (borrows from graph)
    let mut parsed_modules: HashMap<String, &Module> = HashMap::new();
    let mut cache: HashMap<String, TypedModule> = HashMap::new();

    // Type-check each dependency in topological order
    for resolved in &graph.modules {
        parsed_modules.insert(resolved.path.clone(), &resolved.module);
        if !cache.contains_key(&resolved.path) {
            let typed = infer_module_inner(
                &resolved.module,
                &mut cache,
                &parsed_modules,
                Some(resolved.path.clone()),
            )?;
            cache.insert(resolved.path.clone(), typed);
        }
    }

    // Type-check the root module
    let main = infer_module_inner(module, &mut cache, &parsed_modules, None)?;

    let mut result = vec![main];
    // Collect cached imported modules (stable ordering by path)
    let mut paths: Vec<String> = cache.keys().cloned().collect();
    paths.sort();
    for path in paths {
        result.push(cache.remove(&path).unwrap());
    }
    Ok(result)
}

/// Convert a `ModuleGraphError` into a `SpannedTypeError`.
fn map_graph_error(e: krypton_modules::module_graph::ModuleGraphError) -> SpannedTypeError {
    use krypton_modules::module_graph::ModuleGraphError;
    match e {
        ModuleGraphError::CircularImport { cycle, span } => {
            spanned(TypeError::CircularImport { cycle }, span)
        }
        ModuleGraphError::UnknownModule { path, span } => {
            spanned(TypeError::UnknownModule { path }, span)
        }
        ModuleGraphError::BareImport { path, span } => {
            spanned(TypeError::BareImport { path }, span)
        }
        ModuleGraphError::ParseError { path, errors } => {
            spanned(TypeError::ModuleParseError { path, errors }, (0, 0))
        }
    }
}

/// Return the main `TypedModule` from `infer_module` result (for backward compatibility).
pub fn infer_module_single(
    module: &Module,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<TypedModule, SpannedTypeError> {
    let mut modules = infer_module(module, resolver)?;
    Ok(modules.remove(0))
}

/// State accumulated during the bootstrap phases of module inference
/// (env setup, import processing, extern loading, type registration).
/// Consumed by `assemble_typed_module` at the end.
pub(crate) struct ModuleInferenceState {
    // Core inference state
    pub(super) env: TypeEnv,
    pub(super) subst: Substitution,
    pub(super) gen: TypeVarGen,
    pub(super) registry: TypeRegistry,
    pub(super) let_own_spans: HashSet<Span>,
    pub(super) lambda_own_captures: HashMap<Span, String>,
    // Import accumulation
    pub(super) imported_fn_types: Vec<(String, TypeScheme, FnOrigin)>,
    pub(super) fn_provenance_map: HashMap<String, (String, String)>,
    pub(super) type_provenance: HashMap<String, String>,
    pub(super) imported_extern_fns: Vec<ExternFnInfo>,
    pub(super) imported_type_info: HashMap<String, (String, Visibility)>,
    pub(super) imported_fn_constraints: HashMap<String, Vec<(String, usize)>>,
    pub(super) imported_trait_defs: Vec<ExportedTraitDef>,
    pub(super) imported_trait_names: HashSet<String>,
    pub(super) qualified_modules: HashMap<String, QualifiedModuleBinding>,
    // Re-export state
    pub(super) reexported_fn_types: Vec<(String, TypeScheme, FnOrigin)>,
    pub(super) reexported_type_names: Vec<String>,
    pub(super) reexported_type_visibility: HashMap<String, Visibility>,
    pub(super) reexported_trait_defs: Vec<ExportedTraitDef>,
    // Prelude tracking
    pub(super) prelude_imported_names: HashSet<String>,
}

impl ModuleInferenceState {
    fn new(is_core_module: bool) -> Self {
        let mut env = TypeEnv::new();
        let mut gen = TypeVarGen::new();
        let mut registry = TypeRegistry::new();
        registry.register_builtins();

        crate::intrinsics::register_intrinsics(&mut env, &mut gen, is_core_module);

        let mut type_provenance: HashMap<String, String> = HashMap::new();
        for name in &["Int", "Float", "Bool", "String", "Unit"] {
            type_provenance.insert(name.to_string(), "core".to_string());
        }

        registry.register_name("Vec");

        ModuleInferenceState {
            env,
            subst: Substitution::new(),
            gen,
            registry,
            let_own_spans: HashSet::new(),
            lambda_own_captures: HashMap::new(),
            imported_fn_types: Vec::new(),
            fn_provenance_map: HashMap::new(),
            type_provenance,
            imported_extern_fns: Vec::new(),
            imported_type_info: HashMap::new(),
            imported_fn_constraints: HashMap::new(),
            imported_trait_defs: Vec::new(),
            imported_trait_names: HashSet::new(),
            qualified_modules: HashMap::new(),
            reexported_fn_types: Vec::new(),
            reexported_type_names: Vec::new(),
            reexported_type_visibility: HashMap::new(),
            reexported_trait_defs: Vec::new(),
            prelude_imported_names: HashSet::new(),
        }
    }

    fn process_local_externs(&mut self, module: &Module) -> Result<Vec<ExternFnInfo>, SpannedTypeError> {
        let mut extern_fns: Vec<ExternFnInfo> = Vec::new();
        for decl in &module.decls {
            if let Decl::ExternJava {
                class_name,
                methods,
                span,
            } = decl
            {
                let no_aliases = HashMap::new();
                let mut fns = process_extern_methods(
                    class_name, methods, &mut self.env, &mut self.gen, &self.registry,
                    *span, None, &no_aliases,
                )?;
                extern_fns.append(&mut fns);
            }
        }
        Ok(extern_fns)
    }

    fn cleanup_prelude_shadows(&mut self, module: &Module) {
        if self.prelude_imported_names.is_empty() {
            return;
        }
        for decl in &module.decls {
            match decl {
                Decl::ExternJava { methods, .. } => {
                    for m in methods {
                        if self.prelude_imported_names.contains(&m.name) {
                            self.imported_fn_constraints.remove(&m.name);
                        }
                    }
                }
                Decl::DefFn(f) => {
                    if self.prelude_imported_names.contains(&f.name) {
                        self.imported_fn_constraints.remove(&f.name);
                    }
                }
                _ => {}
            }
        }
    }

    fn preregister_type_names(&mut self, module: &Module) {
        for decl in &module.decls {
            if let Decl::DefType(type_decl) = decl {
                self.registry.register_name(&type_decl.name);
            }
        }
    }

    fn process_local_type_decls(&mut self, module: &Module) -> Result<Vec<(String, TypeScheme)>, SpannedTypeError> {
        let mut constructor_schemes: Vec<(String, TypeScheme)> = Vec::new();
        for decl in &module.decls {
            if let Decl::DefType(type_decl) = decl {
                if let Some(existing) = self.registry.lookup_type(&type_decl.name) {
                    if existing.is_prelude {
                        if let crate::type_registry::TypeKind::Sum { variants } = &existing.kind {
                            for v in variants {
                                self.env.unbind(&v.name);
                                self.fn_provenance_map.remove(&v.name);
                            }
                        }
                        self.type_provenance.remove(&type_decl.name);
                        self.imported_type_info.remove(&type_decl.name);
                    }
                }

                let constructors = type_registry::process_type_decl(type_decl, &mut self.registry, &mut self.gen)
                    .map_err(|e| spanned(e, type_decl.span))?;
                for (name, scheme) in constructors {
                    self.env.bind(name.clone(), scheme.clone());
                    constructor_schemes.push((name, scheme));
                }
            }
        }
        Ok(constructor_schemes)
    }

    /// Assemble the final TypedModule from accumulated state and inference-phase outputs.
    fn assemble_typed_module(
        mut self,
        module: &Module,
        module_path: Option<String>,
        fn_decls: &[&krypton_parser::ast::FnDecl],
        result_schemes: Vec<Option<TypeScheme>>,
        fn_bodies: Vec<Option<TypedExpr>>,
        instance_defs: Vec<InstanceDefInfo>,
        derived_instance_defs: Vec<InstanceDefInfo>,
        fn_constraint_requirements: &HashMap<String, Vec<(String, TypeVarId)>>,
        trait_method_map: &HashMap<String, String>,
        trait_registry: &TraitRegistry,
        exported_trait_defs: Vec<ExportedTraitDef>,
        extern_fns: Vec<ExternFnInfo>,
        constructor_schemes: Vec<(String, TypeScheme)>,
        parsed_modules: &HashMap<String, &Module>,
        shared_type_vars: &HashMap<String, HashSet<String>>,
    ) -> Result<TypedModule, SpannedTypeError> {
        let mut instance_defs = instance_defs;
        instance_defs.extend(derived_instance_defs);

        let mut results: Vec<(String, TypeScheme, FnOrigin)> = self.imported_fn_types;
        results.extend(constructor_schemes.iter().map(|(n, s)| (n.clone(), s.clone(), FnOrigin::Regular)));
        results.extend(
            fn_decls
                .iter()
                .enumerate()
                .map(|(i, d)| (d.name.clone(), result_schemes[i].clone().unwrap(), FnOrigin::Regular)),
        );
        // Add instance method types to the flat list for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(&inst.trait_name, &inst.target_type_name, &m.name);
                results.push((qualified, m.scheme.clone(), FnOrigin::Regular));
            }
        }

        // Build exported_fn_types: the public API surface for downstream importers.
        // Includes pub (transparent) constructors, pub local functions, and instance methods.
        // Does NOT include imported functions.
        let mut exported_fn_types: Vec<(String, TypeScheme, FnOrigin)> = Vec::new();

        // 1. Constructors for pub (transparent) types only
        for (cname, scheme) in &constructor_schemes {
            let is_pub_open = module.decls.iter().any(|d| {
                if let Decl::DefType(td) = d {
                    matches!(td.visibility, Visibility::Pub) && constructor_names(td).contains(cname)
                } else {
                    false
                }
            });
            if is_pub_open {
                exported_fn_types.push((cname.clone(), scheme.clone(), FnOrigin::Regular));
            }
        }

        // 2. Local pub function declarations
        for (i, decl) in fn_decls.iter().enumerate() {
            if matches!(decl.visibility, Visibility::Pub) {
                exported_fn_types.push((
                    decl.name.clone(),
                    result_schemes[i].clone().unwrap(),
                    FnOrigin::Regular,
                ));
            }
        }

        let mut functions: Vec<TypedFnDecl> = Vec::new();
        let mut fn_bodies = fn_bodies;
        for (i, decl) in fn_decls.iter().enumerate() {
            let mut body = fn_bodies[i].take().unwrap();
            typed_ast::apply_subst(&mut body, &self.subst);
            functions.push(TypedFnDecl {
                name: decl.name.clone(),
                visibility: decl.visibility.clone(),
                params: decl.params.iter().map(|p| p.name.clone()).collect(),
                body,
            });
        }
        // Build temporary flat list of instance method bodies for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(&inst.trait_name, &inst.target_type_name, &m.name);
                functions.push(TypedFnDecl {
                    name: qualified,
                    visibility: Visibility::Pub,
                    params: m.params.clone(),
                    body: m.body.clone(),
                });
            }
        }

        let fn_schemes: HashMap<String, TypeScheme> = results.iter().map(|(n, s, _)| (n.clone(), s.clone())).collect();
        for func in &functions {
            let current_requirements = fn_constraint_requirements
                .get(&func.name)
                .cloned()
                .unwrap_or_default();
            check_constrained_function_refs(
                &func.body,
                &current_requirements,
                &fn_schemes,
                fn_constraint_requirements,
                &self.imported_fn_constraints,
                trait_registry,
            )?;
        }

        let mut fn_constraints: HashMap<String, Vec<(String, usize)>> = HashMap::new();
        for func in &functions {
            let mut param_type_var_map: HashMap<TypeVarId, usize> = HashMap::new();
            if let Some((_, scheme, _)) = results.iter().find(|(n, _, _)| n == &func.name) {
                if let Type::Fn(param_types, _) = &scheme.ty {
                    for (idx, pty) in param_types.iter().enumerate() {
                        for v in free_vars(pty) {
                            param_type_var_map.entry(v).or_insert(idx);
                        }
                    }
                }
            }
            let mut constraints = Vec::new();
            detect_trait_constraints(
                &func.body,
                trait_method_map,
                &self.subst,
                &param_type_var_map,
                &mut constraints,
            );
            if !constraints.is_empty() {
                constraints.sort();
                constraints.dedup();
                fn_constraints.insert(func.name.clone(), constraints);
            }
        }

        let mut trait_defs = Vec::new();
        let mut seen_traits = std::collections::HashSet::new();
        for (trait_name, info) in trait_registry.traits() {
            let is_imported = self.imported_trait_names.contains(trait_name);
            let method_info: Vec<(String, usize)> = info
                .methods
                .iter()
                .map(|m| (m.name.clone(), m.param_types.len()))
                .collect();
            trait_defs.push(TraitDefInfo {
                name: trait_name.clone(),
                methods: method_info,
                is_imported,
            });
            seen_traits.insert(trait_name.clone());
        }
        for decl in &module.decls {
            if let Decl::DefTrait { name, methods, .. } = decl {
                if !seen_traits.contains(name) {
                    let method_info: Vec<(String, usize)> = methods
                        .iter()
                        .map(|m| (m.name.clone(), m.params.len()))
                        .collect();
                    trait_defs.push(TraitDefInfo {
                        name: name.clone(),
                        methods: method_info,
                        is_imported: false,
                    });
                }
            }
        }

        let mut struct_update_info: HashMap<Span, (String, HashSet<String>)> = HashMap::new();
        for func in &functions {
            collect_struct_update_info(&func.body, &mut struct_update_info);
        }

        crate::ownership::check_ownership(
            module,
            &results,
            &self.registry,
            &self.let_own_spans,
            &self.lambda_own_captures,
            &struct_update_info,
            &shared_type_vars,
        )?;

        let auto_close = crate::auto_close::compute_auto_close(&functions, &results, trait_registry)?;

        // Strip temporary instance method entries from functions and results —
        // they live on instance_defs now, codegen reads them from there
        functions.truncate(fn_decls.len());
        // results contains: imported + constructors + fn_decls + instance methods
        // Strip the instance method entries (they were appended last)
        let results_base_len = results.len() - instance_defs.iter().map(|i| i.methods.len()).sum::<usize>();
        results.truncate(results_base_len);

        let struct_decls: Vec<_> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Record { fields } => Some((td.name.clone(), fields.clone())),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let mut sum_decls: Vec<(String, Vec<String>, Vec<Variant>)> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Sum { variants } => {
                        Some((td.name.clone(), td.type_params.clone(), variants.clone()))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();

        {
            let existing_type_names: HashSet<String> =
                sum_decls.iter().map(|(n, _, _)| n.clone()).collect();
            for (type_name, (source_path, vis)) in &self.imported_type_info {
                if existing_type_names.contains(type_name) || !matches!(vis, Visibility::Pub) {
                    continue;
                }
                if let Some(imported_mod) = parsed_modules.get(source_path.as_str()) {
                    if let Some(td) = find_type_decl(&imported_mod.decls, type_name) {
                        if let TypeDeclKind::Sum { variants } = &td.kind {
                            self.type_provenance.insert(td.name.clone(), source_path.clone());
                            for v in variants {
                                self.type_provenance.insert(v.name.clone(), source_path.clone());
                            }
                            sum_decls.push((td.name.clone(), td.type_params.clone(), variants.clone()));
                        }
                    }
                }
            }
        }

        let local_type_names: HashSet<String> = module
            .decls
            .iter()
            .filter_map(|d| {
                if let Decl::DefType(td) = d {
                    Some(td.name.clone())
                } else {
                    None
                }
            })
            .collect();
        for (type_name, (source_path, _)) in &self.imported_type_info {
            if !local_type_names.contains(type_name) {
                self.type_provenance.insert(type_name.clone(), source_path.clone());
            }
        }

        let mut type_visibility: HashMap<String, Visibility> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                type_visibility.insert(td.name.clone(), td.visibility.clone());
            }
        }

        let mut exported_trait_defs = exported_trait_defs;
        exported_trait_defs.extend(self.reexported_trait_defs);

        Ok(TypedModule {
            module_path,
            fn_types: results,
            exported_fn_types,
            functions,
            trait_defs,
            instance_defs,
            fn_constraints,
            fn_constraint_requirements: fn_constraint_requirements.clone(),
            imported_fn_constraints: self.imported_fn_constraints,
            trait_method_map: trait_method_map.clone(),
            extern_fns,
            imported_extern_fns: self.imported_extern_fns,
            struct_decls,
            sum_decls,
            fn_provenance: self.fn_provenance_map,
            type_provenance: self.type_provenance,
            type_visibility,
            reexported_fn_types: self.reexported_fn_types,
            reexported_type_names: self.reexported_type_names,
            reexported_type_visibility: self.reexported_type_visibility,
            exported_trait_defs,
            auto_close,
        })
    }
}

/// Internal per-module inference with pre-resolved module cache.
///
/// The module graph has already been resolved and toposorted by `infer_module`.
/// Import declarations look up parsed ASTs from `parsed_modules` and typed
/// results from `cache` — no recursive resolution or cycle detection needed.
///
/// Pipeline phases:
///  1. Initialize state (env, registry, intrinsics)
///  2. Build synthetic prelude import
///  3. Process imports (types, fns, traits, re-exports)
///  4. Reserve type var generator past imported schemes
///  5. Process local extern declarations
///  6. Clean up prelude shadows
///  7. Pre-register local type names
///  8. Process local type declarations
///  9. Register traits (imported + local)
/// 10. Process deriving declarations
/// 11. Process impl blocks
/// 12. SCC-based function inference
/// 13. Post-inference instance resolution
/// 14. Impl method type-checking
/// 15. Assemble TypedModule
pub(crate) fn infer_module_inner(
    module: &Module,
    cache: &mut HashMap<String, TypedModule>,
    parsed_modules: &HashMap<String, &Module>,
    module_path: Option<String>,
) -> Result<TypedModule, SpannedTypeError> {
    let is_core_module = module_path.as_ref().is_some_and(|p| p.starts_with("core/"));
    let is_prelude_tree = module_path.as_ref().is_some_and(|p| {
        krypton_modules::stdlib_loader::PRELUDE_MODULES
            .iter()
            .any(|m| m == p)
    });

    let mut state = ModuleInferenceState::new(is_core_module);

    let synthetic_prelude_import = state.build_synthetic_prelude_import(
        is_prelude_tree,
        cache,
        parsed_modules,
    );

    state.process_imports(module, cache, parsed_modules, synthetic_prelude_import.as_ref())?;
    reserve_gen_for_env_schemes(&state.env, &mut state.gen);
    let extern_fns = state.process_local_externs(module)?;
    state.cleanup_prelude_shadows(module);
    state.preregister_type_names(module);
    let constructor_schemes = state.process_local_type_decls(module)?;

    // --- Phases 12-21: trait/impl/deriving/SCC inference (inline for M17-T3) ---

    let mut trait_registry = TraitRegistry::new();

    // Structural instance lookup: for each type/trait in scope, look up instances
    // in the defining module. The orphan rule guarantees instances live in the
    // module defining the type or the trait.
    {
        let mut source_modules: HashSet<&str> = HashSet::new();
        for (_, source_path) in &state.type_provenance {
            source_modules.insert(source_path.as_str());
        }
        for (_, (source_path, _)) in &state.imported_type_info {
            source_modules.insert(source_path.as_str());
        }

        let mut seen_instances: HashSet<(String, String)> = HashSet::new();
        for module_path in &source_modules {
            if let Some(cached_module) = cache.get(*module_path) {
                for inst in &cached_module.instance_defs {
                    let key = (inst.trait_name.clone(), inst.target_type_name.clone());
                    if seen_instances.insert(key) {
                        let instance = InstanceInfo {
                            trait_name: inst.trait_name.clone(),
                            target_type: inst.target_type.clone(),
                            target_type_name: inst.target_type_name.clone(),
                            type_var_ids: inst.type_var_ids.clone(),
                            constraints: inst.constraints.clone(),
                            methods: inst
                                .methods
                                .iter()
                                .map(|m| m.name.clone())
                                .collect(),
                            span: (0, 0),
                            is_builtin: false,
                        };
                        // A-T14: silently ignores duplicate imported instances; should be an error
                        let _ = trait_registry.register_instance(instance);
                    }
                }
            }
        }
    }

    // Register trait definitions imported from other modules
    for trait_def in &state.imported_trait_defs {
        if trait_registry.lookup_trait(&trait_def.name).is_some() {
            continue;
        }
        let new_tv_id = state.gen.fresh();
        let old_tv_id = trait_def.type_var_id;

        let mut trait_methods = Vec::new();
        for method in &trait_def.methods {
            let param_types: Vec<Type> = method
                .param_types
                .iter()
                .map(|t| remap_type_var(t, old_tv_id, new_tv_id))
                .collect();
            let return_type = remap_type_var(&method.return_type, old_tv_id, new_tv_id);

            trait_methods.push(TraitMethod {
                name: method.name.clone(),
                param_types,
                return_type,
            });
        }

        trait_registry
            .register_trait(TraitInfo {
                name: trait_def.name.clone(),
                type_var: trait_def.type_var.clone(),
                type_var_id: new_tv_id,
                type_var_arity: trait_def.type_var_arity,
                superclasses: trait_def.superclasses.clone(),
                methods: trait_methods,
                span: (0, 0),
            })
            .expect("imported trait should not already be registered (checked above)");
    }

    // Second pass: process DefTrait declarations
    let mut exported_trait_defs: Vec<ExportedTraitDef> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefTrait {
            visibility,
            name,
            type_param,
            superclasses,
            methods,
            span,
        } = decl
        {
            // Error if this trait conflicts with an imported trait
            if trait_registry.lookup_trait(name).is_some() {
                return Err(spanned(
                    TypeError::DuplicateType { name: name.clone() },
                    *span,
                ));
            }
            let tv_id = state.gen.fresh();
            let type_var_arity = type_param.arity;
            let mut type_param_map = HashMap::new();
            let mut type_param_arity = HashMap::new();
            type_param_map.insert(type_param.name.clone(), tv_id);
            type_param_arity.insert(type_param.name.clone(), type_param.arity);

            // For HK trait methods, use explicit type_params from the method declaration
            let mut trait_methods = Vec::new();
            let mut exported_methods = Vec::new();
            for method in methods {
                let mut method_type_param_map = type_param_map.clone();
                let mut method_type_param_arity = type_param_arity.clone();
                let mut method_tv_ids = Vec::new();
                for tv_param in &method.type_params {
                    if !method_type_param_map.contains_key(&tv_param.name) {
                        let mv_id = state.gen.fresh();
                        method_type_param_map.insert(tv_param.name.clone(), mv_id);
                        method_type_param_arity.insert(tv_param.name.clone(), tv_param.arity);
                        method_tv_ids.push(mv_id);
                    }
                }

                let mut param_types = Vec::new();
                for p in &method.params {
                    if let Some(ref ty_expr) = p.ty {
                        param_types.push(
                            type_registry::resolve_type_expr(
                                ty_expr,
                                &method_type_param_map,
                                &method_type_param_arity,
                                &state.registry,
                            )
                            .map_err(|e| spanned(e, method.span))?,
                        );
                    } else {
                        param_types.push(Type::Var(state.gen.fresh()));
                    }
                }
                let return_type = if let Some(ref ret_expr) = method.return_type {
                    type_registry::resolve_type_expr(
                        ret_expr,
                        &method_type_param_map,
                        &method_type_param_arity,
                        &state.registry,
                    )
                        .map_err(|e| spanned(e, method.span))?
                } else {
                    Type::Var(state.gen.fresh())
                };

                // Bind the method as a polymorphic function: forall tv_id, method_tvs. fn(params) -> ret
                let fn_ty = Type::Fn(param_types.clone(), Box::new(return_type.clone()));
                let mut all_vars = vec![tv_id];
                all_vars.extend_from_slice(&method_tv_ids);
                let scheme = TypeScheme {
                    vars: all_vars,
                    ty: fn_ty,
                };
                state.env.bind(method.name.clone(), scheme);

                exported_methods.push(ExportedTraitMethod {
                    name: method.name.clone(),
                    param_types: param_types.clone(),
                    return_type: return_type.clone(),
                });

                trait_methods.push(TraitMethod {
                    name: method.name.clone(),
                    param_types,
                    return_type,
                });
            }

            trait_registry
                .register_trait(TraitInfo {
                    name: name.clone(),
                    type_var: type_param.name.clone(),
                    type_var_id: tv_id,
                    type_var_arity,
                    superclasses: superclasses.clone(),
                    methods: trait_methods,
                    span: *span,
                })
                .map_err(|e| spanned(e, *span))?;

            exported_trait_defs.push(ExportedTraitDef {
                visibility: visibility.clone(),
                name: name.clone(),
                type_var: type_param.name.clone(),
                type_var_id: tv_id,
                type_var_arity,
                superclasses: superclasses.clone(),
                methods: exported_methods,
            });
        }
    }

    // Deriving pass: process DefType declarations with `deriving` clauses
    let mut derived_instance_defs: Vec<InstanceDefInfo> = Vec::new();

    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            if type_decl.deriving.is_empty() {
                continue;
            }
            let type_info = state.registry.lookup_type(&type_decl.name).unwrap();

            for trait_name in &type_decl.deriving {
                if trait_registry.lookup_trait(trait_name).is_none() {
                    return Err(spanned(
                        TypeError::NoInstance {
                            trait_name: trait_name.clone(),
                            ty: type_decl.name.clone(),
                            required_by: None,
                        },
                        type_decl.span,
                    ));
                }

                // Collect all field types that need the trait
                let field_types: Vec<&Type> = match &type_info.kind {
                    crate::type_registry::TypeKind::Record { fields } => {
                        fields.iter().map(|(_, ty)| ty).collect()
                    }
                    crate::type_registry::TypeKind::Sum { variants } => {
                        variants.iter().flat_map(|v| v.fields.iter()).collect()
                    }
                };

                let derived_type_var_ids: HashMap<String, TypeVarId> = type_decl
                    .type_params
                    .iter()
                    .cloned()
                    .zip(type_info.type_param_vars.iter().copied())
                    .collect();
                let local_type_params: HashMap<TypeVarId, String> = derived_type_var_ids
                    .iter()
                    .map(|(name, id)| (*id, name.clone()))
                    .collect();
                let mut derived_constraints: Vec<TypeConstraint> = Vec::new();
                let mut visited_constraints: HashSet<(String, String)> = HashSet::new();

                // Validate that all field types have instances for this trait
                for ft in &field_types {
                    if !collect_derived_constraints_for_type(
                        &trait_registry,
                        trait_name,
                        ft,
                        &local_type_params,
                        &mut visited_constraints,
                        &mut derived_constraints,
                    ) {
                        return Err(spanned(
                            TypeError::CannotDerive {
                                trait_name: trait_name.clone(),
                                type_name: type_decl.name.clone(),
                                field_type: format!("{}", ft),
                            },
                            type_decl.span,
                        ));
                    }
                }

                // Build the target type
                let type_args: Vec<Type> = type_info
                    .type_param_vars
                    .iter()
                    .map(|&v| Type::Var(v))
                    .collect();
                let target_type = Type::Named(type_decl.name.clone(), type_args);
                let target_type_name = type_decl.name.clone();

                // Register the instance
                let method_name = match trait_name.as_str() {
                    "Eq" => "eq",
                    "Show" => "show",
                    _ => continue,
                };

                let instance = InstanceInfo {
                    trait_name: trait_name.clone(),
                    target_type: target_type.clone(),
                    target_type_name: target_type_name.clone(),
                    type_var_ids: derived_type_var_ids.clone(),
                    constraints: derived_constraints.clone(),
                    methods: vec![method_name.to_string()],
                    span: type_decl.span,
                    is_builtin: false,
                };
                trait_registry
                    .register_instance(instance)
                    .map_err(|e| spanned(e, type_decl.span))?;

                // Synthesize the method body
                let syn_span: Span = (0, 0);

                let (body, fn_ty) = match trait_name.as_str() {
                    "Eq" => synthesize_eq_body(type_info, &target_type, syn_span),
                    "Show" => synthesize_show_body(type_info, &target_type, syn_span),
                    _ => continue,
                };

                let params = match trait_name.as_str() {
                    "Eq" => vec!["__a".to_string(), "__b".to_string()],
                    "Show" => vec!["__a".to_string()],
                    _ => vec![],
                };

                let scheme = TypeScheme {
                    vars: vec![],
                    ty: fn_ty,
                };

                derived_instance_defs.push(InstanceDefInfo {
                    trait_name: trait_name.clone(),
                    target_type_name,
                    target_type,
                    type_var_ids: derived_type_var_ids.clone(),
                    constraints: derived_constraints.clone(),
                    methods: vec![typed_ast::InstanceMethod {
                        name: method_name.to_string(),
                        params,
                        body,
                        scheme,
                    }],
                    subdict_traits: vec![],
                    is_intrinsic: false,
                });
            }
        }
    }

    // Collect locally-defined trait names for orphan check
    let local_trait_names: HashSet<String> = module
        .decls
        .iter()
        .filter_map(|d| {
            if let Decl::DefTrait { name, .. } = d {
                Some(name.clone())
            } else {
                None
            }
        })
        .collect();

    // Third pass: process DefImpl declarations
    for decl in &module.decls {
        if let Decl::DefImpl {
            trait_name,
            target_type,
            type_constraints,
            methods,
            span,
            ..
        } = decl
        {
            let mut impl_type_param_names = HashSet::new();
            collect_type_expr_var_names(target_type, &mut impl_type_param_names);
            for constraint in type_constraints {
                impl_type_param_names.insert(constraint.type_var.clone());
            }
            let type_param_map: HashMap<String, TypeVarId> = impl_type_param_names
                .into_iter()
                .map(|name| (name, state.gen.fresh()))
                .collect();
            let type_param_arity: HashMap<String, usize> = HashMap::new();
            let resolved_target =
                type_registry::resolve_type_expr(
                    target_type,
                    &type_param_map,
                    &type_param_arity,
                    &state.registry,
                )
                    .map_err(|e| spanned(e, *span))?;

            // Orphan check: type must be known, and either the type or the trait must be locally defined
            let target_name = match &resolved_target {
                Type::Named(name, _) => {
                    if state.registry.lookup_type(name).is_none() {
                        return Err(spanned(
                            TypeError::OrphanInstance {
                                trait_name: trait_name.clone(),
                                ty: name.clone(),
                            },
                            *span,
                        ));
                    }
                    let trait_is_local = local_trait_names.contains(trait_name);
                    let type_is_local = !state.type_provenance.contains_key(name);
                    if !type_is_local && !trait_is_local {
                        return Err(spanned(
                            TypeError::OrphanInstance {
                                trait_name: trait_name.clone(),
                                ty: name.clone(),
                            },
                            *span,
                        ));
                    }
                    name.clone()
                }
                Type::Int => "Int".to_string(),
                Type::Float => "Float".to_string(),
                Type::Bool => "Bool".to_string(),
                Type::String => "String".to_string(),
                other => {
                    return Err(spanned(
                        TypeError::OrphanInstance {
                            trait_name: trait_name.clone(),
                            ty: format!("{}", other),
                        },
                        *span,
                    ));
                }
            };

            // Kind-arity check: verify the impl target has the right arity for the trait
            if let Some(trait_info) = trait_registry.lookup_trait(trait_name) {
                let expected_arity = trait_info.type_var_arity;
                if expected_arity > 0 {
                    let actual_arity = state.registry.expected_arity(&target_name).unwrap_or(0);
                    if actual_arity != expected_arity {
                        return Err(spanned(
                            TypeError::KindMismatch {
                                type_name: target_name.clone(),
                                expected_arity,
                                actual_arity,
                            },
                            *span,
                        ));
                    }
                }

                let expected_methods: HashSet<&str> =
                    trait_info.methods.iter().map(|m| m.name.as_str()).collect();
                let actual_methods: HashSet<&str> =
                    methods.iter().map(|m| m.name.as_str()).collect();
                let missing_methods: Vec<String> = trait_info
                    .methods
                    .iter()
                    .filter(|m| !actual_methods.contains(m.name.as_str()))
                    .map(|m| m.name.clone())
                    .collect();
                let extra_methods: Vec<String> = methods
                    .iter()
                    .filter(|m| !expected_methods.contains(m.name.as_str()))
                    .map(|m| m.name.clone())
                    .collect();
                if !missing_methods.is_empty() || !extra_methods.is_empty() {
                    return Err(spanned(
                        TypeError::InvalidImpl {
                            trait_name: trait_name.clone(),
                            target_type: target_name.clone(),
                            missing_methods,
                            extra_methods,
                        },
                        *span,
                    ));
                }
            }

            let method_names: Vec<String> = methods.iter().map(|m| m.name.clone()).collect();

            let instance = InstanceInfo {
                trait_name: trait_name.clone(),
                target_type: resolved_target,
                target_type_name: target_name,
                type_var_ids: type_param_map.clone(),
                constraints: type_constraints.clone(),
                methods: method_names,
                span: *span,
                is_builtin: false,
            };

            // Superclass check before registering
            trait_registry
                .check_superclasses(&instance)
                .map_err(|e| spanned(e, *span))?;

            trait_registry
                .register_instance(instance)
                .map_err(|e| spanned(e, *span))?;
        }
    }

    // Collect the mapping of trait method names → trait names for post-inference resolution
    let trait_method_map: HashMap<String, String> =
        trait_registry.trait_method_names().into_iter().collect();

    // Check for top-level def names conflicting with ANY trait method names (including built-ins)
    {
        // Determine if the module uses traits (has DefTrait, DefImpl, or deriving)
        let has_trait_usage = module
            .decls
            .iter()
            .any(|d| matches!(d, Decl::DefTrait { .. } | Decl::DefImpl { .. }))
            || module.decls.iter().any(|d| {
                if let Decl::DefType(td) = d {
                    !td.deriving.is_empty()
                } else {
                    false
                }
            });

        // First pass: check user-defined traits (with secondary span)
        let mut user_trait_methods: HashMap<String, (String, Span)> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefTrait { name, methods, .. } = decl {
                for method in methods {
                    user_trait_methods.insert(method.name.clone(), (name.clone(), method.span));
                }
            }
        }
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if let Some((trait_name, method_span)) = user_trait_methods.get(&f.name) {
                    return Err(SpannedTypeError {
                        error: TypeError::DefinitionConflictsWithTraitMethod {
                            def_name: f.name.clone(),
                            trait_name: trait_name.clone(),
                        },
                        span: f.span,
                        note: None,
                        secondary_span: Some((*method_span, "trait method defined here".into())),
                    });
                }
                // Second pass: check built-in traits (no secondary span)
                // Only check when module uses traits (has instances, trait defs, or deriving)
                if !user_trait_methods.contains_key(&f.name) && has_trait_usage {
                    if let Some(trait_name) = trait_method_map.get(&f.name) {
                        return Err(SpannedTypeError {
                            error: TypeError::DefinitionConflictsWithTraitMethod {
                                def_name: f.name.clone(),
                                trait_name: trait_name.clone(),
                            },
                            span: f.span,
                            note: None,
                            secondary_span: None,
                        });
                    }
                }
            }
        }
    }

    // Reject user-defined functions with reserved __krypton_ prefix
    if !is_core_module {
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if f.name.starts_with("__krypton_") {
                    return Err(spanned(
                        TypeError::ReservedName {
                            name: f.name.clone(),
                        },
                        f.span,
                    ));
                }
            }
        }
    }

    // Collect DefFn declarations (includes impl method bodies for type checking)
    let fn_decls: Vec<&krypton_parser::ast::FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Build dependency graph and compute SCCs in topological order
    let adj = scc::build_dependency_graph(&fn_decls);
    let sccs = scc::tarjan_scc(&adj);

    // Store results indexed by declaration order
    let mut result_schemes: Vec<Option<TypeScheme>> = vec![None; fn_decls.len()];
    let mut fn_bodies: Vec<Option<TypedExpr>> = vec![None; fn_decls.len()];
    let mut fn_constraint_requirements: HashMap<String, Vec<(String, TypeVarId)>> = HashMap::new();
    let mut shared_type_vars: HashMap<String, HashSet<String>> = HashMap::new();

    // Process each SCC in topological order (dependencies first)
    for component in &sccs {
        // Bind each name in the SCC to a fresh type variable (monomorphic within SCC)
        let mut pre_bound: Vec<(usize, Type)> = Vec::new();
        for &idx in component {
            let tv = Type::Var(state.gen.fresh());
            state.env.bind(fn_decls[idx].name.clone(), TypeScheme::mono(tv.clone()));
            pre_bound.push((idx, tv));
        }

        // Infer all bodies in the SCC
        for &(idx, ref tv) in &pre_bound {
            let decl = fn_decls[idx];
            state.env.push_scope();

            // Build type_param_map from explicit type parameters
            let (type_param_map, type_param_arity) =
                build_type_param_maps(&decl.type_params, &mut state.gen);
            // Collect shared type vars and filter them out of trait constraints
            let mut shared_tv_names: HashSet<String> = HashSet::new();
            if !decl.constraints.is_empty() {
                for constraint in &decl.constraints {
                    if constraint.trait_name == "shared" {
                        shared_tv_names.insert(constraint.type_var.clone());
                    }
                }

                // Validate: ~a param where a: shared is contradictory
                for p in &decl.params {
                    if let Some(TypeExpr::Own { inner, .. }) = &p.ty {
                        if let TypeExpr::Var { name, .. } = inner.as_ref() {
                            if shared_tv_names.contains(name) {
                                return Err(spanned(
                                    TypeError::QualifierBoundViolation {
                                        type_var: name.clone(),
                                        param_name: p.name.clone(),
                                    },
                                    decl.span,
                                ));
                            }
                        }
                    }
                }

                let requirements: Vec<(String, TypeVarId)> = decl
                    .constraints
                    .iter()
                    .filter(|c| c.trait_name != "shared")
                    .filter_map(|constraint| {
                        type_param_map
                            .get(&constraint.type_var)
                            .copied()
                            .map(|type_var| (constraint.trait_name.clone(), type_var))
                    })
                    .collect();
                if !requirements.is_empty() {
                    fn_constraint_requirements.insert(decl.name.clone(), requirements);
                }
            }
            if !shared_tv_names.is_empty() {
                shared_type_vars.insert(decl.name.clone(), shared_tv_names);
            }

            let mut param_types = Vec::new();
            for p in &decl.params {
                let ptv = Type::Var(state.gen.fresh());
                if let Some(ref ty_expr) = p.ty {
                    let annotated_ty =
                        type_registry::resolve_type_expr(
                            ty_expr,
                            &type_param_map,
                            &type_param_arity,
                            &state.registry,
                        )
                        .map_err(|e| spanned(e, decl.span))?;
                    unify(&ptv, &annotated_ty, &mut state.subst).map_err(|e| spanned(e, decl.span))?;
                }
                param_types.push(ptv.clone());
                state.env.bind(p.name.clone(), TypeScheme::mono(ptv));
            }
            // Set fn_return_type for ? operator support
            let prev_fn_return_type = state.env.fn_return_type.take();
            if let Some(ref ret_ty_expr) = decl.return_type {
                let resolved_ret =
                    type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                    )
                    .map_err(|e| spanned(e, decl.span))?;
                state.env.fn_return_type = Some(resolved_ret);
            } else {
                state.env.fn_return_type = Some(Type::Var(state.gen.fresh()));
            }

            let body_typed = {
                let mut ctx = InferenceContext {
                    env: &mut state.env,
                    subst: &mut state.subst,
                    gen: &mut state.gen,
                    registry: Some(&state.registry),
                    recur_params: Some(&param_types),
                    let_own_spans: Some(&mut state.let_own_spans),
                    lambda_own_captures: Some(&mut state.lambda_own_captures),
                    type_param_map: &type_param_map,
                    type_param_arity: &type_param_arity,
                    qualified_modules: &state.qualified_modules,
                };
                ctx.infer_expr_inner(&decl.body, None)?
            };
            state.env.fn_return_type = prev_fn_return_type;
            state.env.pop_scope();

            let param_types: Vec<Type> = param_types.iter().map(|t| state.subst.apply(t)).collect();
            let body_ty = state.subst.apply(&body_typed.ty);

            // Enforce return type annotation if present
            let ret_ty = if let Some(ref ret_ty_expr) = decl.return_type {
                let annotated_ret =
                    type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                    )
                    .map_err(|e| spanned(e, decl.span))?;
                // Fabrication guard: body must produce `own T` to satisfy an `own T` annotation.
                // Bare `T` cannot be upgraded to `own T` — ownership must come from a literal,
                // constructor, or another `own` source.
                if let Type::Own(ref inner) = annotated_ret {
                    if !matches!(inner.as_ref(), Type::Fn(_, _)) && !matches!(body_ty, Type::Own(_))
                    {
                        return Err(spanned(
                            TypeError::Mismatch {
                                expected: annotated_ret.clone(),
                                actual: body_ty.clone(),
                            },
                            decl.span,
                        ));
                    }
                }
                let coerced_body_ty = strip_own(&body_ty);
                unify(&coerced_body_ty, &annotated_ret, &mut state.subst)
                    .map_err(|e| spanned(e, decl.span))?;
                state.subst.apply(&annotated_ret)
            } else {
                strip_own(&body_ty)
            };

            let fn_ty = Type::Fn(param_types, Box::new(ret_ty));
            unify(tv, &fn_ty, &mut state.subst).map_err(|e| spanned(e, decl.span))?;

            fn_bodies[idx] = Some(body_typed);
        }

        // Generalize against an empty env: all env bindings are either fully-quantified
        // schemes (no free vars) or current-SCC monomorphic bindings whose vars should be
        // generalized. This must change if nested let-polymorphism is added.
        let empty_env = TypeEnv::new();
        for &(idx, ref tv) in &pre_bound {
            let final_ty = state.subst.apply(tv);
            let scheme = generalize(&final_ty, &empty_env, &state.subst);
            state.env.bind(fn_decls[idx].name.clone(), scheme.clone());
            result_schemes[idx] = Some(scheme);
        }
    }

    // Post-inference instance resolution: check that all trait method calls have instances
    // and check cross-module constraints (e.g., imported `println` requires Show)
    if !trait_method_map.is_empty() || !state.imported_fn_constraints.is_empty() {
        for body in fn_bodies.iter() {
            if let Some(body) = body {
                check_trait_instances(
                    body,
                    &trait_method_map,
                    &trait_registry,
                    &state.subst,
                    &state.imported_fn_constraints,
                )?;
            }
        }
    }

    // Type-check impl method bodies and store on InstanceDefInfo
    let mut instance_defs: Vec<InstanceDefInfo> = Vec::new();

    for decl in &module.decls {
        if let Decl::DefImpl {
            trait_name,
            target_type: _,
            methods,
            span,
            ..
        } = decl
        {
            // Look up the trait and instance
            let trait_info = trait_registry.lookup_trait(trait_name).unwrap();
            let tv_id = trait_info.type_var_id;

            // Find the registered instance to get the resolved target type
            let instance = trait_registry
                .find_instance_by_trait_and_span(trait_name, *span)
                .unwrap();
            let resolved_target = instance.target_type.clone();
            let target_type_name = instance.target_type_name.clone();

            let mut instance_methods = Vec::new();

            // Detect if all method bodies are __krypton_intrinsic() calls
            let all_intrinsic = methods.iter().all(|m| {
                matches!(&*m.body, Expr::App { func, args, .. }
                    if args.is_empty() && matches!(func.as_ref(), Expr::Var { name, .. } if name == "__krypton_intrinsic"))
            });

            for method in methods {
                // Find the trait method signature
                let trait_method = trait_info
                    .methods
                    .iter()
                    .find(|m| m.name == method.name)
                    .unwrap();

                // Substitute trait type var → concrete target type
                let concrete_param_types: Vec<Type> = trait_method
                    .param_types
                    .iter()
                    .map(|t| substitute_type_var(t, tv_id, &resolved_target))
                    .collect();
                let _concrete_ret_type =
                    substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);

                // Build type_param_map for impl method annotations
                // (needed for type vars in HKT method annotations like `Box[a]`)
                let mut impl_method_tpm = HashMap::new();
                let mut impl_method_tpa = HashMap::new();
                for tv_param in &method.type_params {
                    if !impl_method_tpm.contains_key(&tv_param.name) {
                        impl_method_tpm.insert(tv_param.name.clone(), state.gen.fresh());
                        impl_method_tpa.insert(tv_param.name.clone(), tv_param.arity);
                    }
                }

                // Validate user-provided type annotations against the trait signature
                for (i, p) in method.params.iter().enumerate() {
                    if let Some(ref ty_expr) = p.ty {
                        if i < concrete_param_types.len() {
                            let annotated_ty = type_registry::resolve_type_expr(
                                ty_expr,
                                &impl_method_tpm,
                                &impl_method_tpa,
                                &state.registry,
                            )
                            .map_err(|e| spanned(e, p.span))?;
                            unify(&annotated_ty, &concrete_param_types[i], &mut state.subst)
                                .map_err(|e| spanned(e, p.span))?;
                        }
                    }
                }
                if let Some(ref ret_ty_expr) = method.return_type {
                    let concrete_ret =
                        substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);
                    let annotated_ret =
                        type_registry::resolve_type_expr(
                            ret_ty_expr,
                            &impl_method_tpm,
                            &impl_method_tpa,
                            &state.registry,
                        )
                        .map_err(|e| spanned(e, method.span))?;
                    unify(&annotated_ret, &concrete_ret, &mut state.subst)
                        .map_err(|e| spanned(e, method.span))?;
                }

                // For intrinsic impls, skip body type-checking (bridge bytecode handles these)
                if all_intrinsic {
                    continue;
                }

                // Type-check the method body
                state.env.push_scope();
                let mut param_types_inferred = Vec::new();
                for (i, p) in method.params.iter().enumerate() {
                    let ptv = Type::Var(state.gen.fresh());
                    if i < concrete_param_types.len() {
                        unify(&ptv, &concrete_param_types[i], &mut state.subst)
                            .map_err(|e| spanned(e, *span))?;
                    }
                    param_types_inferred.push(ptv.clone());
                    state.env.bind(p.name.clone(), TypeScheme::mono(ptv));
                }
                // Set fn_return_type for ? operator support
                let prev_fn_return_type = state.env.fn_return_type.take();
                let concrete_ret_type =
                    substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);
                state.env.fn_return_type = Some(concrete_ret_type);

                let body_typed = {
                    let mut ctx = InferenceContext {
                        env: &mut state.env,
                        subst: &mut state.subst,
                        gen: &mut state.gen,
                        registry: Some(&state.registry),
                        recur_params: Some(&param_types_inferred),
                        let_own_spans: Some(&mut state.let_own_spans),
                        lambda_own_captures: Some(&mut state.lambda_own_captures),
                        type_param_map: &impl_method_tpm,
                        type_param_arity: &impl_method_tpa,
                        qualified_modules: &state.qualified_modules,
                    };
                    ctx.infer_expr_inner(&method.body, None)?
                };
                state.env.fn_return_type = prev_fn_return_type;
                state.env.pop_scope();

                let mut body_typed = body_typed;
                typed_ast::apply_subst(&mut body_typed, &state.subst);

                let final_param_types: Vec<Type> = param_types_inferred
                    .iter()
                    .map(|t| state.subst.apply(t))
                    .collect();
                let final_ret_type = state.subst.apply(&body_typed.ty);

                let fn_ty = Type::Fn(final_param_types, Box::new(final_ret_type));
                let scheme = TypeScheme {
                    vars: vec![],
                    ty: fn_ty,
                };

                instance_methods.push(typed_ast::InstanceMethod {
                    name: method.name.clone(),
                    params: method.params.iter().map(|p| p.name.clone()).collect(),
                    body: body_typed,
                    scheme,
                });
            }

            instance_defs.push(InstanceDefInfo {
                trait_name: trait_name.clone(),
                target_type_name,
                target_type: resolved_target,
                type_var_ids: instance.type_var_ids.clone(),
                constraints: instance.constraints.clone(),
                methods: instance_methods,
                subdict_traits: vec![],
                is_intrinsic: all_intrinsic,
            });
        }
    }

    state.assemble_typed_module(
        module,
        module_path,
        &fn_decls,
        result_schemes,
        fn_bodies,
        instance_defs,
        derived_instance_defs,
        &fn_constraint_requirements,
        &trait_method_map,
        &trait_registry,
        exported_trait_defs,
        extern_fns,
        constructor_schemes,
        parsed_modules,
        &shared_type_vars,
    )
}

/// Synthesize an `eq` method body for a derived Eq instance.
fn synthesize_eq_body(
    type_info: &crate::type_registry::TypeInfo,
    target_type: &Type,
    span: Span,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
    };
    let param_b = TypedExpr {
        kind: TypedExprKind::Var("__b".to_string()),
        ty: target_type.clone(),
        span,
    };
    let true_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(true)),
        ty: Type::Bool,
        span,
    };
    let false_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(false)),
        ty: Type::Bool,
        span,
    };

    let body = match &type_info.kind {
        crate::type_registry::TypeKind::Record { fields } => {
            if fields.is_empty() {
                true_expr()
            } else {
                // Chain: if (== .a.f1 .b.f1) (if (== .a.f2 .b.f2) ... true) false
                let mut result = true_expr();
                for (field_name, field_ty) in fields.iter().rev() {
                    let lhs = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_a.clone()),
                            field: field_name.clone(),
                        },
                        ty: field_ty.clone(),
                        span,
                    };
                    let rhs = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_b.clone()),
                            field: field_name.clone(),
                        },
                        ty: field_ty.clone(),
                        span,
                    };
                    let cmp = TypedExpr {
                        kind: TypedExprKind::BinaryOp {
                            op: BinOp::Eq,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        ty: Type::Bool,
                        span,
                    };
                    result = TypedExpr {
                        kind: TypedExprKind::If {
                            cond: Box::new(cmp),
                            then_: Box::new(result),
                            else_: Box::new(false_expr()),
                        },
                        ty: Type::Bool,
                        span,
                    };
                }
                result
            }
        }
        crate::type_registry::TypeKind::Sum { variants } => {
            // Outer match on __a, inner match on __b
            let arms: Vec<TypedMatchArm> = variants
                .iter()
                .map(|variant| {
                    let a_bindings: Vec<String> = (0..variant.fields.len())
                        .map(|i| format!("__x{}", i))
                        .collect();
                    let a_pattern = TypedPattern::Constructor {
                        name: variant.name.clone(),
                        args: a_bindings
                            .iter()
                            .zip(variant.fields.iter())
                            .map(|(n, ft)| TypedPattern::Var {
                                name: n.clone(),
                                ty: ft.clone(),
                                span,
                            })
                            .collect(),
                        ty: target_type.clone(),
                        span,
                    };

                    // Inner match on __b
                    let inner_arms: Vec<TypedMatchArm> = variants
                        .iter()
                        .map(|inner_variant| {
                            if inner_variant.name == variant.name {
                                let b_bindings: Vec<String> = (0..inner_variant.fields.len())
                                    .map(|i| format!("__y{}", i))
                                    .collect();
                                let b_pattern = TypedPattern::Constructor {
                                    name: inner_variant.name.clone(),
                                    args: b_bindings
                                        .iter()
                                        .zip(inner_variant.fields.iter())
                                        .map(|(n, ft)| TypedPattern::Var {
                                            name: n.clone(),
                                            ty: ft.clone(),
                                            span,
                                        })
                                        .collect(),
                                    ty: target_type.clone(),
                                    span,
                                };
                                // Compare all payload fields
                                if inner_variant.fields.is_empty() {
                                    TypedMatchArm {
                                        pattern: b_pattern,
                                        body: true_expr(),
                                    }
                                } else {
                                    let mut result = true_expr();
                                    for (i, ft) in inner_variant.fields.iter().enumerate().rev() {
                                        let x = TypedExpr {
                                            kind: TypedExprKind::Var(format!("__x{}", i)),
                                            ty: ft.clone(),
                                            span,
                                        };
                                        let y = TypedExpr {
                                            kind: TypedExprKind::Var(format!("__y{}", i)),
                                            ty: ft.clone(),
                                            span,
                                        };
                                        let cmp = TypedExpr {
                                            kind: TypedExprKind::BinaryOp {
                                                op: BinOp::Eq,
                                                lhs: Box::new(x),
                                                rhs: Box::new(y),
                                            },
                                            ty: Type::Bool,
                                            span,
                                        };
                                        result = TypedExpr {
                                            kind: TypedExprKind::If {
                                                cond: Box::new(cmp),
                                                then_: Box::new(result),
                                                else_: Box::new(false_expr()),
                                            },
                                            ty: Type::Bool,
                                            span,
                                        };
                                    }
                                    TypedMatchArm {
                                        pattern: b_pattern,
                                        body: result,
                                    }
                                }
                            } else {
                                // Different variant → false
                                TypedMatchArm {
                                    pattern: TypedPattern::Wildcard {
                                        ty: target_type.clone(),
                                        span,
                                    },
                                    body: false_expr(),
                                }
                            }
                        })
                        .collect();

                    let inner_match = TypedExpr {
                        kind: TypedExprKind::Match {
                            scrutinee: Box::new(param_b.clone()),
                            arms: inner_arms,
                        },
                        ty: Type::Bool,
                        span,
                    };

                    TypedMatchArm {
                        pattern: a_pattern,
                        body: inner_match,
                    }
                })
                .collect();

            TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(param_a.clone()),
                    arms,
                },
                ty: Type::Bool,
                span,
            }
        }
    };

    let fn_ty = Type::Fn(
        vec![target_type.clone(), target_type.clone()],
        Box::new(Type::Bool),
    );
    (body, fn_ty)
}

/// Synthesize a `show` method body for a derived Show instance.
fn synthesize_show_body(
    type_info: &crate::type_registry::TypeInfo,
    target_type: &Type,
    span: Span,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
    };

    let str_lit = |s: &str| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::Lit(Lit::String(s.to_string())),
            ty: Type::String,
            span,
        }
    };

    let str_concat = |lhs: TypedExpr, rhs: TypedExpr| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::BinaryOp {
                op: BinOp::Add,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty: Type::String,
            span,
        }
    };

    let show_call = |expr: TypedExpr| -> TypedExpr {
        let arg_ty = expr.ty.clone();
        TypedExpr {
            kind: TypedExprKind::App {
                func: Box::new(TypedExpr {
                    kind: TypedExprKind::Var("show".to_string()),
                    ty: Type::Fn(vec![arg_ty], Box::new(Type::String)),
                    span,
                }),
                args: vec![expr],
            },
            ty: Type::String,
            span,
        }
    };

    let body = match &type_info.kind {
        crate::type_registry::TypeKind::Record { fields } => {
            // "Point(" + show(.a x) + ", " + show(.a y) + ")"
            let mut result = str_lit(&format!("{}(", type_info.name));
            for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                if i > 0 {
                    result = str_concat(result, str_lit(", "));
                }
                let field_access = TypedExpr {
                    kind: TypedExprKind::FieldAccess {
                        expr: Box::new(param_a.clone()),
                        field: field_name.clone(),
                    },
                    ty: field_ty.clone(),
                    span,
                };
                result = str_concat(result, show_call(field_access));
            }
            str_concat(result, str_lit(")"))
        }
        crate::type_registry::TypeKind::Sum { variants } => {
            let arms: Vec<TypedMatchArm> = variants
                .iter()
                .map(|variant| {
                    let bindings: Vec<String> = (0..variant.fields.len())
                        .map(|i| format!("__x{}", i))
                        .collect();
                    let pattern = TypedPattern::Constructor {
                        name: variant.name.clone(),
                        args: bindings
                            .iter()
                            .zip(variant.fields.iter())
                            .map(|(n, ft)| TypedPattern::Var {
                                name: n.clone(),
                                ty: ft.clone(),
                                span,
                            })
                            .collect(),
                        ty: target_type.clone(),
                        span,
                    };

                    let body = if variant.fields.is_empty() {
                        str_lit(&variant.name)
                    } else {
                        // "Some(" + show(x0) + ")"
                        let mut result = str_lit(&format!("{}(", variant.name));
                        for (i, ft) in variant.fields.iter().enumerate() {
                            if i > 0 {
                                result = str_concat(result, str_lit(", "));
                            }
                            let var_expr = TypedExpr {
                                kind: TypedExprKind::Var(format!("__x{}", i)),
                                ty: ft.clone(),
                                span,
                            };
                            result = str_concat(result, show_call(var_expr));
                        }
                        str_concat(result, str_lit(")"))
                    };

                    TypedMatchArm { pattern, body }
                })
                .collect();

            TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(param_a),
                    arms,
                },
                ty: Type::String,
                span,
            }
        }
    };

    let fn_ty = Type::Fn(vec![target_type.clone()], Box::new(Type::String));
    (body, fn_ty)
}
