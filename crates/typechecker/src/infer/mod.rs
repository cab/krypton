use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{
    BinOp, Decl, Expr, ExternMethod, Lit, Module, Span, TypeConstraint,
    TypeDecl, TypeDeclKind, TypeExpr, TypeParam, UnaryOp, Variant, Visibility,
};

use crate::scc;
use crate::trait_registry::{InstanceInfo, TraitInfo, TraitMethod, TraitRegistry};
use crate::type_registry::{self, ResolutionContext, TypeRegistry};
use crate::typed_ast::{
    self, ExportedTraitDef, ExportedTraitMethod, ExternFnInfo, InstanceDefInfo, TraitId,
    TraitDefInfo, TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedModule, TypedPattern,
};
use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId, type_to_canonical_name};
use crate::unify::{coerce_unify, unify, SpannedTypeError, TypeError};

/// Error from `infer_module`, bundling the error with enough context
/// to render diagnostics against the correct file.
#[derive(Debug)]
pub enum InferError {
    /// A type error, possibly from an imported module.
    TypeError {
        error: SpannedTypeError,
        /// (module_path, source_text) for the module where the error originated.
        /// `None` means the error is in the root/user file.
        error_source: Option<(String, String)>,
    },
    /// Parse errors in an imported module — rendered via the parser's own diagnostics.
    ModuleParseError {
        path: String,
        source: String,
        errors: Vec<krypton_parser::diagnostics::ParseError>,
    },
}

impl InferError {
    /// Get the `SpannedTypeError` if this is a type error, or `None` for parse errors.
    pub fn type_error(&self) -> Option<&SpannedTypeError> {
        match self {
            InferError::TypeError { error, .. } => Some(error),
            InferError::ModuleParseError { .. } => None,
        }
    }
}

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
        TypedExprKind::TypeApp { expr, .. } => bare_function_ref_name(expr),
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
                                return Err(no_instance_error(
                                    trait_registry,
                                    requirement.trait_name(),
                                    &requirement_ty,
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
        krypton_parser::ast::TypeExpr::Named { .. } | krypton_parser::ast::TypeExpr::Qualified { .. } => {}
        krypton_parser::ast::TypeExpr::Wildcard { .. } => {}
    }
}

/// Validate wildcards in an impl target type expression.
/// Returns the count of wildcards at the outermost App level.
/// Errors if wildcards are nested or appear outside an App.
fn validate_impl_wildcards(texpr: &krypton_parser::ast::TypeExpr) -> Result<usize, TypeError> {
    match texpr {
        krypton_parser::ast::TypeExpr::App { args, .. } => {
            let mut wildcard_count = 0;
            for arg in args {
                match arg {
                    krypton_parser::ast::TypeExpr::Wildcard { .. } => {
                        wildcard_count += 1;
                    }
                    other => {
                        // Check for nested wildcards
                        if contains_wildcard(other) {
                            let span = wildcard_span(other).unwrap_or((0, 0));
                            return Err(TypeError::NestedWildcard { span });
                        }
                    }
                }
            }
            Ok(wildcard_count)
        }
        krypton_parser::ast::TypeExpr::Wildcard { span } => {
            Err(TypeError::WildcardNotAllowed { span: *span })
        }
        _ => Ok(0),
    }
}

fn contains_wildcard(texpr: &krypton_parser::ast::TypeExpr) -> bool {
    match texpr {
        krypton_parser::ast::TypeExpr::Wildcard { .. } => true,
        krypton_parser::ast::TypeExpr::App { args, .. } => args.iter().any(contains_wildcard),
        krypton_parser::ast::TypeExpr::Fn { params, ret, .. } => {
            params.iter().any(contains_wildcard) || contains_wildcard(ret)
        }
        krypton_parser::ast::TypeExpr::Own { inner, .. } => contains_wildcard(inner),
        krypton_parser::ast::TypeExpr::Tuple { elements, .. } => elements.iter().any(contains_wildcard),
        krypton_parser::ast::TypeExpr::Named { .. } | krypton_parser::ast::TypeExpr::Var { .. } | krypton_parser::ast::TypeExpr::Qualified { .. } => false,
    }
}

fn wildcard_span(texpr: &krypton_parser::ast::TypeExpr) -> Option<krypton_parser::ast::Span> {
    match texpr {
        krypton_parser::ast::TypeExpr::Wildcard { span } => Some(*span),
        krypton_parser::ast::TypeExpr::App { args, .. } => args.iter().find_map(wildcard_span),
        krypton_parser::ast::TypeExpr::Fn { params, ret, .. } => {
            params.iter().find_map(wildcard_span).or_else(|| wildcard_span(ret))
        }
        krypton_parser::ast::TypeExpr::Own { inner, .. } => wildcard_span(inner),
        krypton_parser::ast::TypeExpr::Tuple { elements, .. } => elements.iter().find_map(wildcard_span),
        _ => None,
    }
}

/// Resolve an impl target type expression, handling wildcards by generating
/// fresh anonymous type variables for each `_`.
fn resolve_impl_target(
    texpr: &krypton_parser::ast::TypeExpr,
    type_param_map: &HashMap<String, TypeVarId>,
    type_param_arity: &HashMap<String, usize>,
    registry: &type_registry::TypeRegistry,
    gen: &mut TypeVarGen,
) -> Result<Type, TypeError> {
    match texpr {
        krypton_parser::ast::TypeExpr::App { name, args, .. } => {
            let mut resolved_args = Vec::new();
            for a in args {
                match a {
                    krypton_parser::ast::TypeExpr::Wildcard { .. } => {
                        // Generate a fresh anonymous type variable
                        resolved_args.push(Type::Var(gen.fresh()));
                    }
                    other => {
                        resolved_args.push(type_registry::resolve_type_expr(
                            other,
                            type_param_map,
                            type_param_arity,
                            registry,
                            type_registry::ResolutionContext::UserAnnotation,
                            None,
                        )?);
                    }
                }
            }
            // If name is a type parameter (HKT variable), produce Type::App
            if let Some(&var_id) = type_param_map.get(name) {
                return Ok(Type::App(Box::new(Type::Var(var_id)), resolved_args));
            }
            // Validate the type name
            type_registry::resolve_type_expr(
                &krypton_parser::ast::TypeExpr::Named { name: name.clone(), span: (0, 0) },
                type_param_map,
                type_param_arity,
                registry,
                type_registry::ResolutionContext::UserAnnotation,
                None,
            )?;
            // Kind check: verify arity matches
            let expected = registry.expected_arity(name);
            if let Some(expected) = expected {
                if expected != resolved_args.len() {
                    return Err(TypeError::KindMismatch {
                        type_name: name.clone(),
                        expected_arity: expected,
                        actual_arity: resolved_args.len(),
                    });
                }
            }
            Ok(Type::Named(
                registry.canonical_name(name).to_string(),
                resolved_args,
            ))
        }
        // No wildcards: delegate to normal resolution
        other => type_registry::resolve_type_expr(
            other,
            type_param_map,
            type_param_arity,
            registry,
            type_registry::ResolutionContext::UserAnnotation,
            None,
        ),
    }
}

/// Strip type arguments from a Named type that are anonymous (not in type_var_ids).
/// Used for HKT partial application: Named("Result", [Var(e), Var(anon)]) becomes
/// Named("Result", [Var(e)]) when anon is not a tracked type var.
fn strip_anon_type_args(ty: &Type, type_var_ids: &HashMap<String, TypeVarId>) -> Type {
    let known_var_ids: std::collections::HashSet<TypeVarId> = type_var_ids.values().copied().collect();
    match ty {
        Type::Named(name, args) => {
            let kept: Vec<Type> = args.iter().filter(|arg| {
                match arg {
                    Type::Var(id) => known_var_ids.contains(id),
                    _ => true,
                }
            }).cloned().collect();
            Type::Named(name.clone(), kept)
        }
        _ => ty.clone(),
    }
}

fn reserve_gen_for_env_schemes(env: &TypeEnv, gen: &mut TypeVarGen) {
    env.for_each_scheme(|scheme| {
        for &var in &scheme.vars {
            gen.reserve_past(var);
        }
        for var in free_vars(&scheme.ty) {
            gen.reserve_past(var);
        }
    });
}

/// Generalize a type into a type scheme by quantifying over variables
/// free in the type but not free in the environment.
pub(super) fn generalize(ty: &Type, env: &TypeEnv, subst: &Substitution) -> TypeScheme {
    let ty = subst.apply(ty);
    let ty_vars = free_vars(&ty);
    let env_vars = free_vars_env(env, subst);
    let mut vars: Vec<TypeVarId> = ty_vars.difference(&env_vars).copied().collect();
    vars.sort();
    TypeScheme { vars, ty, var_names: HashMap::new() }
}

/// Attach a span to a TypeError, producing a SpannedTypeError.
pub(super) fn spanned(error: TypeError, span: krypton_parser::ast::Span) -> SpannedTypeError {
    SpannedTypeError {
        error,
        span,
        note: None,
        secondary_span: None,
        source_file: None,
        var_names: None,
    }
}

/// Like `spanned` but populates var_names from a type_param_map for better error messages.
pub(super) fn spanned_with_names(
    error: TypeError,
    span: krypton_parser::ast::Span,
    type_param_map: &HashMap<String, TypeVarId>,
) -> SpannedTypeError {
    let var_names: Vec<(TypeVarId, String)> = type_param_map
        .iter()
        .map(|(name, &id)| (id, name.clone()))
        .collect();
    SpannedTypeError {
        error,
        span,
        note: None,
        secondary_span: None,
        source_file: None,
        var_names: Some(var_names),
    }
}

/// Construct a NoInstance error with diagnostic note when a near-miss instance exists.
fn no_instance_error(
    trait_registry: &TraitRegistry,
    trait_name: &str,
    ty: &Type,
    span: Span,
) -> SpannedTypeError {
    let display_ty = ty.strip_own();
    let mut err = spanned(
        TypeError::NoInstance {
            trait_name: trait_name.to_string(),
            ty: format!("{display_ty}"),
            required_by: None,
        },
        span,
    );
    if let Some(diag) = trait_registry.diagnose_missing_instance(trait_name, ty) {
        err.note = Some(diag.to_note());
    }
    err
}

/// Recursively replace Type::Var(old_id) with Type::Var(new_id) in a type tree.
fn remap_type_var(ty: &Type, old_id: TypeVarId, new_id: TypeVarId) -> Type {
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
    let empty_efn = HashSet::new();
    let empty_tmm = HashMap::new();
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
        imported_fn_types: &[],
        extern_fn_names: &empty_efn,
        enclosing_fn_constraints: &[],
        shadowed_prelude_fns: &[],
        self_type: None,
        trait_method_map: &empty_tmm,
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
        TypedExprKind::TypeApp { expr, .. } => typed_callee_var_name(expr),
        _ => None,
    }
}

/// Detect trait method calls on type variables (indicating the function needs a dict param).
fn detect_trait_constraints(
    expr: &TypedExpr,
    trait_method_map: &HashMap<String, TraitId>,
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
                    if let Some(trait_id) = trait_method_map.get(name) {
                        if let Some(first_arg) = args.first() {
                            let arg_ty = subst.apply(&first_arg.ty);
                            let concrete_ty = strip_own(&arg_ty);
                            if let Some(v) = leading_type_var(&concrete_ty) {
                                if let Some(param_idx) = param_type_var_map.get(&v).copied() {
                                    constraints.push((trait_id.name.clone(), param_idx));
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
                                    constraints.push((trait_id.name.clone(), param_idx));
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
    trait_method_map: &HashMap<String, TraitId>,
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
                    if let Some(trait_id) = trait_method_map.get(name) {
                        if let Some(first_arg) = args.first() {
                            let arg_ty = subst.apply(&first_arg.ty);
                            let concrete_ty = strip_own(&arg_ty);
                            if leading_type_var(&concrete_ty).is_none()
                                && trait_registry
                                    .find_instance(&trait_id.name, &concrete_ty)
                                    .is_none()
                            {
                                return Err(no_instance_error(
                                    trait_registry,
                                    &trait_id.name,
                                    &concrete_ty,
                                    expr.span,
                                ));
                            }
                        } else {
                            // Zero-arg trait method: prefer explicit type_args from TypeApp
                            let instance_ty = if let TypedExprKind::TypeApp { type_args, .. } = &func.kind {
                                if !type_args.is_empty() {
                                    Some(type_args[0].clone())
                                } else {
                                    None
                                }
                            } else {
                                None
                            };
                            let concrete_ty = if let Some(ty) = instance_ty {
                                strip_own(&ty).clone()
                            } else {
                                // Fallback: use return type (works when trait var IS the return type)
                                let ret_ty = subst.apply(&func.ty);
                                match &ret_ty {
                                    Type::Fn(_, ret) => strip_own(ret).clone(),
                                    other => strip_own(other).clone(),
                                }
                            };
                            if leading_type_var(&concrete_ty).is_none()
                                && trait_registry
                                    .find_instance(&trait_id.name, &concrete_ty)
                                    .is_none()
                            {
                                return Err(no_instance_error(
                                    trait_registry,
                                    &trait_id.name,
                                    &concrete_ty,
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
                                        return Err(no_instance_error(
                                            trait_registry,
                                            trait_name,
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
                    BinOp::Add => Some("Semigroup"),
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
                        return Err(no_instance_error(
                            trait_registry,
                            trait_name,
                            &operand_ty,
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
                        return Err(no_instance_error(
                            trait_registry,
                            trait_name,
                            &operand_ty,
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

/// Build the type_param_map and arity map from parallel slices of names and vars.
fn build_type_param_map(
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
    type_param_map: Option<&HashMap<String, TypeVarId>>,
    type_param_arity: Option<&HashMap<String, usize>>,
    type_param_names: Option<&[String]>,
) -> Result<Vec<ExternFnInfo>, SpannedTypeError> {
    let empty_map = HashMap::new();
    let empty_arity = HashMap::new();
    let resolve_map = type_param_map.unwrap_or(&empty_map);
    let resolve_arity = type_param_arity.unwrap_or(&empty_arity);
    // Collect type param vars for scheme quantification in declaration order
    let base_scheme_vars: Vec<TypeVarId> = match (type_param_names, type_param_map) {
        (Some(names), Some(map)) => names.iter().filter_map(|n| map.get(n).copied()).collect(),
        _ => vec![],
    };
    let has_type_params = type_param_map.is_some();
    let mut extern_fns = Vec::new();
    for method in methods {
        let bind_name = aliases.get(&method.name).unwrap_or(&method.name);
        if let Some(filter) = name_filter {
            if !filter.contains(method.name.as_str()) && !filter.contains(bind_name.as_str()) {
                continue;
            }
        }

        let mut scheme_vars = base_scheme_vars.clone();
        let mut param_types = Vec::new();
        for ty_expr in &method.param_types {
            let resolved =
                type_registry::resolve_type_expr(ty_expr, resolve_map, resolve_arity, registry, ResolutionContext::UserAnnotation, None)
                .map_err(|e| spanned(e, span))?;
            if !has_type_params && matches!(&resolved, Type::Named(n, args) if n == "Object" && args.is_empty()) {
                let fresh = gen.fresh();
                scheme_vars.push(fresh);
                param_types.push(Type::Var(fresh));
            } else {
                param_types.push(resolved);
            }
        }

        let return_type =
            type_registry::resolve_type_expr(&method.return_type, resolve_map, resolve_arity, registry, ResolutionContext::UserAnnotation, None)
                .map_err(|e| spanned(e, span))?;
        let ret = if !has_type_params && matches!(&return_type, Type::Named(n, args) if n == "Object" && args.is_empty())
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
                var_names: HashMap::new(),
            }
        };
        env.bind(bind_name.clone(), scheme);

        // Store concrete types for codegen — resolve without type param map so
        // erased positions stay as Object (JVM erasure). Bare type params like `a`
        // won't resolve and fall back to Object.
        let mut concrete_params = Vec::new();
        for ty_expr in &method.param_types {
            let resolved = match type_registry::resolve_type_expr(ty_expr, &empty_map, &empty_arity, registry, ResolutionContext::UserAnnotation, None) {
                Ok(ty) => ty,
                Err(TypeError::UnknownType { .. }) => Type::Named("Object".to_string(), vec![]),
                Err(e) => return Err(spanned(e, span)),
            };
            concrete_params.push(resolved);
        }
        let codegen_return = match type_registry::resolve_type_expr(&method.return_type, &empty_map, &empty_arity, registry, ResolutionContext::UserAnnotation, None) {
            Ok(ty) => ty,
            Err(TypeError::UnknownType { .. }) => Type::Named("Object".to_string(), vec![]),
            Err(e) => return Err(spanned(e, span)),
        };
        extern_fns.push(ExternFnInfo {
            name: bind_name.clone(),
            java_class: class_name.to_string(),
            param_types: concrete_params,
            return_type: codegen_return,
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
) -> Result<Vec<TypedModule>, InferError> {
    use krypton_modules::module_graph;
    use krypton_modules::stdlib_loader::StdlibLoader;

    // Build the module graph (resolves, parses, toposorts all imports + prelude)
    let graph = module_graph::build_module_graph(module, resolver).map_err(|e| {
        match e {
            module_graph::ModuleGraphError::ParseError { path, source, errors } => {
                InferError::ModuleParseError { path, source, errors }
            }
            other => InferError::TypeError {
                error: map_graph_error(other),
                error_source: None,
            },
        }
    })?;

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
                &graph.prelude_tree_paths,
            ).map_err(|mut e| {
                if e.source_file.is_none() {
                    e.source_file = Some(resolved.path.clone());
                }
                // Re-resolve source for the failing module (error path only)
                let source_text = StdlibLoader::get_source(&resolved.path)
                    .map(|s| s.to_string())
                    .or_else(|| resolver.resolve(&resolved.path));
                let error_source = source_text.map(|s| (resolved.path.clone(), s));
                InferError::TypeError { error: e, error_source }
            })?;
            cache.insert(resolved.path.clone(), typed);
        }
    }

    // Type-check the root module
    let main = infer_module_inner(module, &mut cache, &parsed_modules, None, &graph.prelude_tree_paths)
        .map_err(|e| InferError::TypeError { error: e, error_source: None })?;

    let mut result = vec![main];
    // Collect cached imported modules (stable ordering by path)
    let mut paths: Vec<String> = cache.keys().cloned().collect();
    paths.sort();
    for path in paths {
        result.push(cache.remove(&path).unwrap());
    }
    Ok(result)
}

/// Convert a non-parse `ModuleGraphError` into a `SpannedTypeError`.
/// ParseError is handled separately as `InferError::ModuleParseError`.
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
        ModuleGraphError::ParseError { .. } => {
            unreachable!("ParseError is handled directly as InferError::ModuleParseError")
        }
    }
}

/// Return the main `TypedModule` from `infer_module` result (for backward compatibility).
pub fn infer_module_single(
    module: &Module,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<TypedModule, InferError> {
    let mut modules = infer_module(module, resolver)?;
    Ok(modules.remove(0))
}

/// Grouped import state: the 4 maps that must stay in sync when binding/shadowing imports.
pub(crate) struct ImportContext {
    pub(super) imported_fn_types: Vec<typed_ast::ImportedFn>,
    pub(super) imported_type_info: HashMap<String, (String, Visibility)>,
    pub(super) imported_fn_constraints: HashMap<String, Vec<(String, usize)>>,
    pub(super) imported_fn_qualifiers: HashMap<String, Vec<(typed_ast::ParamQualifier, String)>>,
    /// Prelude functions that were shadowed by explicit imports: (name, source_module)
    pub(super) shadowed_prelude_fns: Vec<(String, String)>,
}

impl ImportContext {
    fn new() -> Self {
        ImportContext {
            imported_fn_types: Vec::new(),
            imported_type_info: HashMap::new(),
            imported_fn_constraints: HashMap::new(),
            imported_fn_qualifiers: HashMap::new(),
            shadowed_prelude_fns: Vec::new(),
        }
    }

    /// Atomically bind an imported function: env + fn_types + provenance.
    /// Returns an error if a same-name, same-first-param import already exists
    /// from a different (non-prelude) module.
    fn bind_import(
        &mut self,
        env: &mut TypeEnv,
        name: String,
        scheme: TypeScheme,
        origin: Option<TraitId>,
        source_module: String,
        original_name: String,
        prelude_imported_names: &HashSet<String>,
        gen: &mut TypeVarGen,
        span: Span,
        imported_fn_constraint_requirements: &mut HashMap<String, Vec<(String, TypeVarId)>>,
    ) -> Result<(), SpannedTypeError> {
        // Explicit import shadows any prelude entry for the same name
        if prelude_imported_names.contains(&name) {
            // Record shadowed prelude functions before removing
            for f in self.imported_fn_types.iter().filter(|f| f.name == name) {
                self.shadowed_prelude_fns.push((f.name.clone(), f.source_module.clone()));
            }
            self.imported_fn_types.retain(|f| f.name != name);
            self.imported_fn_constraints.remove(&name);
            imported_fn_constraint_requirements.remove(&name);
        }

        // Check for same-name + same-first-param from non-prelude imports
        if !prelude_imported_names.contains(&name) {
            let new_first_param = Self::extract_first_param(&scheme);
            for existing in &self.imported_fn_types {
                if existing.name == name
                    && existing.source_module != source_module
                    && !prelude_imported_names.contains(&existing.name)
                {
                    let existing_first = Self::extract_first_param(&existing.scheme);
                    if let (Some(_), Some(_)) = (&new_first_param, &existing_first) {
                        let mut trial_subst = Substitution::new();
                        let new_inst = scheme.instantiate(&mut || gen.fresh());
                        let old_inst = existing.scheme.instantiate(&mut || gen.fresh());
                        let new_fp = match &new_inst {
                            Type::Fn(params, _) => params.first().cloned(),
                            _ => None,
                        };
                        let old_fp = match &old_inst {
                            Type::Fn(params, _) => params.first().cloned(),
                            _ => None,
                        };
                        if let (Some(nfp), Some(ofp)) = (new_fp, old_fp) {
                            if unify(&nfp, &ofp, &mut trial_subst).is_ok() {
                                return Err(spanned(
                                    TypeError::AmbiguousCall {
                                        name: name.clone(),
                                        modules: vec![existing.source_module.clone(), source_module.clone()],
                                    },
                                    span,
                                ));
                            }
                        }
                    }
                }
            }
        }
        env.bind_with_provenance(name.clone(), scheme.clone(), source_module.clone());
        self.imported_fn_types.push(typed_ast::ImportedFn {
            name: name.clone(),
            scheme,
            origin,
            source_module: source_module.clone(),
            original_name,
        });
        Ok(())
    }

    /// Extract the first parameter type from a type scheme (if it's a function type).
    fn extract_first_param(scheme: &TypeScheme) -> Option<Type> {
        match &scheme.ty {
            Type::Fn(params, _) => params.first().cloned(),
            _ => None,
        }
    }

    /// Bind a hidden (qualified) function: fn_types + provenance, no env bind.
    fn bind_hidden_fn(
        &mut self,
        name: String,
        scheme: TypeScheme,
        origin: Option<TraitId>,
        provenance: (String, String),
    ) {
        self.imported_fn_types.push(typed_ast::ImportedFn {
            name,
            scheme,
            origin,
            source_module: provenance.0,
            original_name: provenance.1,
        });
    }

    /// Bind type info for an imported type.
    fn bind_type_info(&mut self, name: String, source: String, vis: Visibility) {
        self.imported_type_info.insert(name, (source, vis));
    }

    /// Bind fn constraints for an imported function.
    fn bind_fn_constraints(&mut self, name: String, constraints: Vec<(String, usize)>) {
        self.imported_fn_constraints.insert(name, constraints);
    }

    /// Remove stale import metadata for a name being locally redefined.
    /// Clears constraints but keeps imported_fn_types
    /// (the entry is still needed in the fn_types output list) and
    /// does not touch env (the local binding is already in place).
    fn remove_import_metadata(&mut self, name: &str) {
        self.imported_fn_constraints.remove(name);
    }

    /// Atomically shadow a name across all maps + env.
    fn shadow(&mut self, env: &mut TypeEnv, name: &str) {
        env.unbind(name);
        self.imported_fn_constraints.remove(name);
        self.imported_fn_types.retain(|f| f.name != name);
    }
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
    pub(super) imports: ImportContext,
    pub(super) type_provenance: HashMap<String, String>,
    pub(super) imported_fn_constraint_requirements: HashMap<String, Vec<(String, TypeVarId)>>,
    pub(super) imported_extern_fns: Vec<ExternFnInfo>,
    pub(super) imported_extern_java_types: Vec<(String, String)>,
    pub(super) imported_trait_defs: Vec<ExportedTraitDef>,
    pub(super) imported_trait_names: HashSet<String>,
    pub(super) qualified_modules: HashMap<String, QualifiedModuleBinding>,
    // Re-export state
    pub(super) reexported_fn_types: Vec<typed_ast::ExportedFn>,
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
        registry.register_builtins(&mut gen);

        crate::intrinsics::register_intrinsics(&mut env, &mut gen, is_core_module);

        let mut type_provenance: HashMap<String, String> = HashMap::new();
        for name in &["Int", "Float", "Bool", "String", "Unit", "Vec"] {
            type_provenance.insert(name.to_string(), "core".to_string());
        }

        ModuleInferenceState {
            env,
            subst: Substitution::new(),
            gen,
            registry,
            let_own_spans: HashSet::new(),
            lambda_own_captures: HashMap::new(),
            imports: ImportContext::new(),
            type_provenance,
            imported_fn_constraint_requirements: HashMap::new(),
            imported_extern_fns: Vec::new(),
            imported_extern_java_types: Vec::new(),
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

    fn process_local_externs(&mut self, module: &Module) -> Result<(Vec<ExternFnInfo>, Vec<(String, String)>), SpannedTypeError> {
        let mut extern_fns: Vec<ExternFnInfo> = Vec::new();
        let mut extern_java_types: Vec<(String, String)> = Vec::new();
        for decl in &module.decls {
            if let Decl::ExternJava {
                class_name,
                alias,
                type_params,
                methods,
                span,
                ..
            } = decl
            {
                // Register type binding if `as Name[params]` is present
                let mut tp_map: Option<HashMap<String, TypeVarId>> = None;
                let mut tp_arity: Option<HashMap<String, usize>> = None;
                if let Some(name) = alias {
                    // Check if already registered (e.g. Vec is a builtin)
                    let type_param_vars = if let Some(existing) = self.registry.lookup_type(name) {
                        existing.type_param_vars.clone()
                    } else {
                        let vars: Vec<_> = type_params.iter().map(|_| self.gen.fresh()).collect();
                        self.registry.register_type(crate::type_registry::TypeInfo {
                            name: name.clone(),
                            type_params: type_params.clone(),
                            type_param_vars: vars.clone(),
                            kind: crate::type_registry::TypeKind::Record { fields: vec![] },
                            is_prelude: false,
                        }).map_err(|e| spanned(e, *span))?;
                        vars
                    };
                    self.registry.mark_user_visible(name);
                    extern_java_types.push((name.clone(), class_name.clone()));

                    // Build type_param_map for method resolution
                    if !type_params.is_empty() {
                        let (map, arity) = build_type_param_map(type_params, &type_param_vars, name);
                        tp_map = Some(map);
                        tp_arity = Some(arity);
                    }
                }

                let no_aliases = HashMap::new();
                let tp_names = type_params.as_slice();
                let mut fns = process_extern_methods(
                    class_name, methods, &mut self.env, &mut self.gen, &self.registry,
                    *span, None, &no_aliases,
                    tp_map.as_ref(), tp_arity.as_ref(),
                    if tp_map.is_some() { Some(tp_names) } else { None },
                )?;
                extern_fns.append(&mut fns);
            }
        }
        Ok((extern_fns, extern_java_types))
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
                            self.imports.remove_import_metadata(&m.name);
                        }
                    }
                }
                Decl::DefFn(f) => {
                    if self.prelude_imported_names.contains(&f.name) {
                        self.imports.remove_import_metadata(&f.name);
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
                self.registry.mark_user_visible(&type_decl.name);
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
                            }
                        }
                        self.type_provenance.remove(&type_decl.name);
                        self.imports.imported_type_info.remove(&type_decl.name);
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
        trait_method_map: &HashMap<String, TraitId>,
        trait_registry: &TraitRegistry,
        exported_trait_defs: Vec<ExportedTraitDef>,
        extern_fns: Vec<ExternFnInfo>,
        extern_java_types: Vec<(String, String)>,
        constructor_schemes: Vec<(String, TypeScheme)>,
        parsed_modules: &HashMap<String, &Module>,
        shared_type_vars: &HashMap<String, HashSet<String>>,
    ) -> Result<TypedModule, SpannedTypeError> {
        let mut instance_defs = instance_defs;
        instance_defs.extend(derived_instance_defs);

        let mut results: Vec<typed_ast::FnTypeEntry> = self.imports.imported_fn_types
            .into_iter()
            .map(|f| typed_ast::FnTypeEntry {
                name: f.name,
                scheme: f.scheme,
                origin: f.origin,
                provenance: Some((f.source_module, f.original_name)),
            })
            .collect();
        results.extend(constructor_schemes.iter().map(|(n, s)| typed_ast::FnTypeEntry {
            name: n.clone(),
            scheme: s.clone(),
            origin: None,
            provenance: None,
        }));
        results.extend(
            fn_decls
                .iter()
                .enumerate()
                .map(|(i, d)| typed_ast::FnTypeEntry {
                    name: d.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    provenance: None,
                }),
        );
        // Add instance method types to the flat list for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(&inst.trait_name, &inst.target_type_name, &m.name);
                results.push(typed_ast::FnTypeEntry {
                    name: qualified,
                    scheme: m.scheme.clone(),
                    origin: None,
                    provenance: None,
                });
            }
        }

        // Build exported_fn_types: the public API surface for downstream importers.
        // Includes pub (transparent) constructors, pub local functions, and instance methods.
        // Does NOT include imported functions.
        let mut exported_fn_types: Vec<typed_ast::ExportedFn> = Vec::new();

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
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: cname.clone(),
                    scheme: scheme.clone(),
                    origin: None,
                    def_span: None,
                });
            }
        }

        // 2. Local pub function declarations
        for (i, decl) in fn_decls.iter().enumerate() {
            if matches!(decl.visibility, Visibility::Pub) {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: decl.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    def_span: Some(decl.span),
                });
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
                close_self_type: None,
            });
        }
        // Build temporary flat list of instance method bodies for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(&inst.trait_name, &inst.target_type_name, &m.name);
                let close_self_type = if inst.trait_name == "Resource" && m.name == "close" {
                    Some(inst.target_type_name.clone())
                } else {
                    None
                };
                functions.push(TypedFnDecl {
                    name: qualified,
                    visibility: Visibility::Pub,
                    params: m.params.clone(),
                    body: m.body.clone(),
                    close_self_type,
                });
            }
        }

        let fn_schemes: HashMap<String, TypeScheme> = results.iter().map(|e| (e.name.clone(), e.scheme.clone())).collect();
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
                &self.imports.imported_fn_constraints,
                trait_registry,
            )?;
        }

        let mut fn_constraints: HashMap<String, Vec<(String, usize)>> = HashMap::new();
        for func in &functions {
            let mut param_type_var_map: HashMap<TypeVarId, usize> = HashMap::new();
            if let Some(entry) = results.iter().find(|e| e.name == func.name) {
                if let Type::Fn(param_types, _) = &entry.scheme.ty {
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
                trait_id: TraitId::new(info.module_path.clone(), trait_name.clone()),
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
                        trait_id: TraitId::new(module_path.clone(), name.clone()),
                        methods: method_info,
                        is_imported: false,
                    });
                }
            }
        }

        // Convert FnTypeEntry to tuple format for ownership/auto_close APIs
        let results_tuples: Vec<(String, TypeScheme, Option<TraitId>)> = results.iter()
            .map(|e| (e.name.clone(), e.scheme.clone(), e.origin.clone()))
            .collect();

        let ownership_result = crate::ownership::check_ownership(
            module,
            &functions,
            &results_tuples,
            &self.registry,
            &self.let_own_spans,
            &self.lambda_own_captures,
            &shared_type_vars,
            &self.imports.imported_fn_qualifiers,
        )?;

        // Filter to exported functions only for cross-module propagation
        let exported_names: HashSet<&str> = exported_fn_types.iter().map(|ef| ef.name.as_str()).collect();
        let exported_fn_qualifiers: HashMap<_, _> = ownership_result.fn_qualifiers
            .into_iter()
            .filter(|(name, _)| exported_names.contains(name.as_str()))
            .collect();

        let auto_close = crate::auto_close::compute_auto_close(&functions, &results_tuples, trait_registry, &ownership_result.moves)?;

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
                    TypeDeclKind::Record { fields } => Some((td.name.clone(), td.type_params.clone(), fields.clone())),
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
            for (type_name, (source_path, vis)) in &self.imports.imported_type_info {
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
        for (type_name, (source_path, _)) in &self.imports.imported_type_info {
            if !local_type_names.contains(type_name) {
                self.type_provenance.insert(type_name.clone(), source_path.clone());
            }
        }

        let mut type_visibility: HashMap<String, Visibility> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                type_visibility.insert(td.name.clone(), td.visibility.clone());
            }
            if let Decl::ExternJava { alias: Some(name), alias_visibility, .. } = decl {
                type_visibility.insert(name.clone(), alias_visibility.clone().unwrap_or(Visibility::Private));
            }
        }

        let mut exported_trait_defs = exported_trait_defs;
        exported_trait_defs.extend(self.reexported_trait_defs);

        // Build exported_type_infos from fully-resolved TypeInfo in the registry.
        // This allows importers to register types without re-resolving from AST.
        let mut exported_type_infos: HashMap<String, typed_ast::ExportedTypeInfo> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                if matches!(td.visibility, Visibility::Private) {
                    continue;
                }
                if let Some(type_info) = self.registry.lookup_type(&td.name) {
                    let kind = match &type_info.kind {
                        crate::type_registry::TypeKind::Record { fields } => {
                            typed_ast::ExportedTypeKind::Record {
                                fields: fields.clone(),
                            }
                        }
                        crate::type_registry::TypeKind::Sum { variants } => {
                            typed_ast::ExportedTypeKind::Sum {
                                variants: variants
                                    .iter()
                                    .map(|v| typed_ast::ExportedVariantInfo {
                                        name: v.name.clone(),
                                        fields: v.fields.clone(),
                                    })
                                    .collect(),
                            }
                        }
                    };
                    exported_type_infos.insert(
                        td.name.clone(),
                        typed_ast::ExportedTypeInfo {
                            name: td.name.clone(),
                            type_params: td.type_params.clone(),
                            type_param_vars: type_info.type_param_vars.clone(),
                            kind,
                        },
                    );
                }
            }
        }

        Ok(TypedModule {
            module_path,
            fn_types: results,
            exported_fn_types,
            functions,
            trait_defs,
            instance_defs,
            fn_constraints,
            fn_constraint_requirements: fn_constraint_requirements.clone(),
            imported_fn_constraints: self.imports.imported_fn_constraints,
            imported_fn_constraint_requirements: self.imported_fn_constraint_requirements,
            extern_fns,
            imported_extern_fns: self.imported_extern_fns,
            extern_java_types,
            imported_extern_java_types: self.imported_extern_java_types,
            struct_decls,
            sum_decls,
            type_provenance: self.type_provenance,
            type_visibility,
            reexported_fn_types: self.reexported_fn_types,
            reexported_type_names: self.reexported_type_names,
            reexported_type_visibility: self.reexported_type_visibility,
            exported_trait_defs,
            exported_type_infos,
            auto_close,
            exported_fn_qualifiers,
        })
    }
}

/// Phase: Register traits (imported + local), process deriving, register impl instances.
/// Returns (trait_registry, exported_trait_defs, derived_instance_defs, trait_method_map).
///
/// Extracted from `infer_module_inner` so its locals are deallocated before the
/// SCC function inference phase, reducing peak stack usage.
fn process_traits_and_deriving(
    state: &mut ModuleInferenceState,
    module: &Module,
    cache: &HashMap<String, TypedModule>,
    module_path: &Option<String>,
    is_prelude_tree: bool,
    prelude_tree_paths: &HashSet<String>,
    is_core_module: bool,
) -> Result<
    (
        TraitRegistry,
        Vec<ExportedTraitDef>,
        Vec<InstanceDefInfo>,
        HashMap<String, TraitId>,
    ),
    SpannedTypeError,
> {
    let mut trait_registry = TraitRegistry::new();

    // Structural instance lookup: for each type/trait in scope, look up instances
    // in the defining module. The orphan rule guarantees instances live in the
    // module defining the type or the trait.
    {
        let mut source_modules: HashSet<&str> = HashSet::new();
        for (_, source_path) in &state.type_provenance {
            source_modules.insert(source_path.as_str());
        }
        for (_, (source_path, _)) in &state.imports.imported_type_info {
            source_modules.insert(source_path.as_str());
        }

        // Prelude-tree modules need instances from all already-compiled siblings
        if is_prelude_tree {
            for path in prelude_tree_paths {
                source_modules.insert(path.as_str());
            }
        }

        let mut seen_instances: HashSet<(String, Type)> = HashSet::new();
        for mod_path in &source_modules {
            if let Some(cached_module) = cache.get(*mod_path) {
                for inst in &cached_module.instance_defs {
                    let key = (inst.trait_name.clone(), inst.target_type.clone());
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
                module_path: trait_def.module_path.clone(),
                type_var: trait_def.type_var.clone(),
                type_var_id: new_tv_id,
                type_var_arity: trait_def.type_var_arity,
                superclasses: trait_def.superclasses.clone(),
                methods: trait_methods,
                span: (0, 0),
            })
            .expect("imported trait should not already be registered (checked above)");
    }

    // Process DefTrait declarations
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
                                ResolutionContext::UserAnnotation,
                                None,
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
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                        .map_err(|e| spanned(e, method.span))?
                } else {
                    Type::Var(state.gen.fresh())
                };

                let fn_ty = Type::Fn(param_types.clone(), Box::new(return_type.clone()));
                let mut all_vars = vec![tv_id];
                all_vars.extend_from_slice(&method_tv_ids);
                let scheme = TypeScheme {
                    vars: all_vars,
                    ty: fn_ty,
                    var_names: HashMap::new(),
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
                    module_path: module_path.clone(),
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
                module_path: module_path.clone(),
                type_var: type_param.name.clone(),
                type_var_id: tv_id,
                type_var_arity,
                superclasses: superclasses.clone(),
                methods: exported_methods,
            });
        }
    }

    // Deriving pass
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

                let type_args: Vec<Type> = type_info
                    .type_param_vars
                    .iter()
                    .map(|&v| Type::Var(v))
                    .collect();
                let target_type = Type::Named(type_decl.name.clone(), type_args);
                let target_type_name = type_decl.name.clone();

                let method_name = match trait_name.as_str() {
                    "Eq" => "eq",
                    "Show" => "show",
                    "Hash" => "hash",
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

                let syn_span: Span = (0, 0);
                let trait_id_for_synth = trait_registry.lookup_trait(trait_name)
                    .map(|ti| TraitId::new(ti.module_path.clone(), ti.name.clone()));
                let (body, fn_ty) = match trait_name.as_str() {
                    "Eq" => synthesize_eq_body(type_info, &target_type, syn_span),
                    "Show" => synthesize_show_body(type_info, &target_type, syn_span, trait_id_for_synth.clone()),
                    "Hash" => synthesize_hash_body(type_info, &target_type, syn_span, trait_id_for_synth.clone()),
                    _ => continue,
                };

                let params = match trait_name.as_str() {
                    "Eq" => vec!["__a".to_string(), "__b".to_string()],
                    "Show" | "Hash" => vec!["__a".to_string()],
                    _ => vec![],
                };

                let scheme = TypeScheme {
                    vars: vec![],
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };

                let derive_trait_id = trait_registry.lookup_trait(trait_name)
                    .map(|ti| TraitId::new(ti.module_path.clone(), ti.name.clone()))
                    .unwrap_or_else(|| TraitId::new(module_path.clone(), trait_name.clone()));
                derived_instance_defs.push(InstanceDefInfo {
                    trait_name: trait_name.clone(),
                    trait_id: derive_trait_id,
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

    // Process DefImpl declarations (register instances)
    for decl in &module.decls {
        if let Decl::DefImpl {
            trait_name,
            target_type,
            type_params,
            type_constraints,
            methods,
            span,
            ..
        } = decl
        {
            let wildcard_count = validate_impl_wildcards(target_type)
                .map_err(|e| spanned(e, *span))?;

            let type_param_map: HashMap<String, TypeVarId> = if !type_params.is_empty() {
                type_params
                    .iter()
                    .map(|tp| (tp.name.clone(), state.gen.fresh()))
                    .collect()
            } else {
                let mut impl_type_param_names = HashSet::new();
                collect_type_expr_var_names(target_type, &mut impl_type_param_names);
                for constraint in type_constraints {
                    impl_type_param_names.insert(constraint.type_var.clone());
                }
                impl_type_param_names
                    .into_iter()
                    .map(|name| (name, state.gen.fresh()))
                    .collect()
            };
            let type_param_arity: HashMap<String, usize> = HashMap::new();

            let resolved_target = if wildcard_count > 0 {
                resolve_impl_target(
                    target_type,
                    &type_param_map,
                    &type_param_arity,
                    &state.registry,
                    &mut state.gen,
                )
                    .map_err(|e| spanned(e, *span))?
            } else {
                type_registry::resolve_type_expr(
                    target_type,
                    &type_param_map,
                    &type_param_arity,
                    &state.registry,
                    ResolutionContext::UserAnnotation,
                    None,
                )
                    .map_err(|e| spanned(e, *span))?
            };

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
                Type::Fn(_params, _) => {
                    if !local_trait_names.contains(trait_name) {
                        return Err(spanned(
                            TypeError::OrphanInstance {
                                trait_name: trait_name.clone(),
                                ty: format!("{}", resolved_target),
                            },
                            *span,
                        ));
                    }
                    if type_param_map.is_empty() {
                        format!("{}", resolved_target.renumber_for_display())
                    } else {
                        let names: std::collections::HashMap<crate::types::TypeVarId, &str> =
                            type_param_map.iter().map(|(n, &id)| (id, n.as_str())).collect();
                        crate::types::format_type_with_var_map(&resolved_target, &names)
                    }
                }
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

            let target_display_name = if type_param_map.is_empty() {
                format!("{}", resolved_target.renumber_for_display())
            } else {
                let names: std::collections::HashMap<crate::types::TypeVarId, &str> =
                    type_param_map.iter().map(|(n, &id)| (id, n.as_str())).collect();
                crate::types::format_type_with_var_map(&resolved_target, &names)
            };

            for constraint in type_constraints {
                if constraint.trait_name != "shared" {
                    if trait_registry.lookup_trait(&constraint.trait_name).is_none() {
                        return Err(spanned(
                            TypeError::UnknownTrait {
                                name: constraint.trait_name.clone(),
                            },
                            constraint.span,
                        ));
                    }
                }
            }

            if let Some(trait_info) = trait_registry.lookup_trait(trait_name) {
                let expected_arity = trait_info.type_var_arity;
                if expected_arity > 0 {
                    if wildcard_count > 0 {
                        if wildcard_count != expected_arity {
                            return Err(spanned(
                                TypeError::KindMismatch {
                                    type_name: target_name.clone(),
                                    expected_arity,
                                    actual_arity: wildcard_count,
                                },
                                *span,
                            ));
                        }
                    } else {
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
                    return Err(spanned_with_names(
                        TypeError::InvalidImpl {
                            trait_name: trait_name.clone(),
                            target_type: target_display_name.clone(),
                            missing_methods,
                            extra_methods,
                        },
                        *span,
                        &type_param_map,
                    ));
                }
            }

            let method_names: Vec<String> = methods.iter().map(|m| m.name.clone()).collect();

            let target_type_name = type_to_canonical_name(&resolved_target);
            let instance = InstanceInfo {
                trait_name: trait_name.clone(),
                target_type: resolved_target,
                target_type_name,
                type_var_ids: type_param_map.clone(),
                constraints: type_constraints.clone(),
                methods: method_names,
                span: *span,
                is_builtin: false,
            };

            trait_registry
                .check_superclasses(&instance)
                .map_err(|e| spanned(e, *span))?;

            trait_registry
                .register_instance(instance)
                .map_err(|e| spanned(e, *span))?;
        }
    }

    let trait_method_map: HashMap<String, TraitId> =
        trait_registry.trait_method_names().into_iter().collect();

    // Check for top-level def names conflicting with trait method names
    {
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
                        secondary_span: Some(crate::unify::SecondaryLabel { span: *method_span, message: "trait method defined here".into(), source_file: None }),
                        source_file: None,
                        var_names: None,
                    });
                }
                if !user_trait_methods.contains_key(&f.name) && has_trait_usage {
                    if let Some(trait_id) = trait_method_map.get(&f.name) {
                        return Err(SpannedTypeError {
                            error: TypeError::DefinitionConflictsWithTraitMethod {
                                def_name: f.name.clone(),
                                trait_name: trait_id.name.clone(),
                            },
                            span: f.span,
                            note: None,
                            secondary_span: None,
                            source_file: None,
                            var_names: None,
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

    Ok((trait_registry, exported_trait_defs, derived_instance_defs, trait_method_map))
}

/// Phase: SCC-based function body inference.
/// Returns (fn_decls, result_schemes, fn_bodies, fn_constraint_requirements, shared_type_vars).
///
/// Extracted from `infer_module_inner` so that earlier phase locals are deallocated
/// before the deep `infer_expr_inner` recursion.
fn infer_function_bodies<'a>(
    state: &mut ModuleInferenceState,
    module: &'a Module,
    extern_fns: &[ExternFnInfo],
    trait_registry: &TraitRegistry,
    trait_method_map: &HashMap<String, TraitId>,
) -> Result<
    (
        Vec<&'a krypton_parser::ast::FnDecl>,
        Vec<Option<TypeScheme>>,
        Vec<Option<TypedExpr>>,
        HashMap<String, Vec<(String, TypeVarId)>>,
        HashMap<String, HashSet<String>>,
    ),
    SpannedTypeError,
> {
    let fn_decls: Vec<&krypton_parser::ast::FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    let adj = scc::build_dependency_graph(&fn_decls);
    let sccs = scc::tarjan_scc(&adj);

    let extern_fn_names: HashSet<String> = extern_fns
        .iter()
        .map(|ef| ef.name.clone())
        .chain(state.imported_extern_fns.iter().map(|ef| ef.name.clone()))
        .collect();

    let mut result_schemes: Vec<Option<TypeScheme>> = vec![None; fn_decls.len()];
    let mut fn_bodies: Vec<Option<TypedExpr>> = vec![None; fn_decls.len()];
    let mut fn_constraint_requirements: HashMap<String, Vec<(String, TypeVarId)>> = HashMap::new();
    let mut shared_type_vars: HashMap<String, HashSet<String>> = HashMap::new();
    let mut saved_type_param_maps: HashMap<usize, HashMap<String, TypeVarId>> = HashMap::new();

    for component in &sccs {
        let mut pre_bound: Vec<(usize, Type)> = Vec::new();
        for &idx in component {
            let tv = Type::Var(state.gen.fresh());
            state.env.bind(fn_decls[idx].name.clone(), TypeScheme::mono(tv.clone()));
            pre_bound.push((idx, tv));
        }

        for &(idx, ref tv) in &pre_bound {
            let decl = fn_decls[idx];
            state.env.push_scope();

            let (type_param_map, type_param_arity) =
                build_type_param_maps(&decl.type_params, &mut state.gen);
            saved_type_param_maps.insert(idx, type_param_map.clone());
            let mut shared_tv_names: HashSet<String> = HashSet::new();
            if !decl.constraints.is_empty() {
                for constraint in &decl.constraints {
                    if constraint.trait_name == "shared" {
                        shared_tv_names.insert(constraint.type_var.clone());
                    }
                }

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

                for constraint in &decl.constraints {
                    if constraint.trait_name != "shared" {
                        if trait_registry.lookup_trait(&constraint.trait_name).is_none() {
                            return Err(spanned(
                                TypeError::UnknownTrait {
                                    name: constraint.trait_name.clone(),
                                },
                                constraint.span,
                            ));
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
                            ResolutionContext::UserAnnotation,
                            None,
                        )
                        .map_err(|e| spanned(e, decl.span))?;
                    unify(&ptv, &annotated_ty, &mut state.subst).map_err(|e| spanned(e, decl.span))?;
                }
                param_types.push(ptv.clone());
                state.env.bind(p.name.clone(), TypeScheme::mono(ptv));
            }
            let prev_fn_return_type = state.env.fn_return_type.take();
            if let Some(ref ret_ty_expr) = decl.return_type {
                let resolved_ret =
                    type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| spanned(e, decl.span))?;
                state.env.fn_return_type = Some(resolved_ret);
            } else {
                state.env.fn_return_type = Some(Type::Var(state.gen.fresh()));
            }

            let body_typed = {
                let empty_constraints = Vec::new();
                let enclosing_constraints = fn_constraint_requirements
                    .get(&decl.name)
                    .unwrap_or(&empty_constraints);
                let mut ctx = InferenceContext {
                    env: &mut state.env,
                    subst: &mut state.subst,
                    gen: &mut state.gen,
                    registry: Some(&state.registry),
                    recur_params: Some(param_types.clone()),
                    let_own_spans: Some(&mut state.let_own_spans),
                    lambda_own_captures: Some(&mut state.lambda_own_captures),
                    type_param_map: &type_param_map,
                    type_param_arity: &type_param_arity,
                    qualified_modules: &state.qualified_modules,
                    imported_fn_types: &state.imports.imported_fn_types,
                    extern_fn_names: &extern_fn_names,
                    enclosing_fn_constraints: enclosing_constraints,
                    shadowed_prelude_fns: &state.imports.shadowed_prelude_fns,
                    trait_method_map,
                    self_type: None,
                };
                ctx.infer_expr_inner(&decl.body, None)?
            };
            state.env.fn_return_type = prev_fn_return_type;
            state.env.pop_scope();

            let param_types: Vec<Type> = param_types.iter().enumerate().map(|(i, t)| {
                let resolved = state.subst.apply(t);
                debug_assert!(
                    !matches!(&resolved, Type::Own(ref inner) if matches!(inner.as_ref(), Type::Own(_))),
                    "Own(Own(_)) should never arise — parser rejects ~~T and no codepath double-wraps: param '{}': {:?}",
                    decl.params.get(i).map(|p| p.name.as_str()).unwrap_or("?"),
                    resolved,
                );
                resolved
            }).collect();
            let body_ty = state.subst.apply(&body_typed.ty);

            let ret_ty = if let Some(ref ret_ty_expr) = decl.return_type {
                let annotated_ret =
                    type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| spanned(e, decl.span))?;
                coerce_unify(&body_ty, &annotated_ret, &mut state.subst)
                    .map_err(|e| spanned(e, decl.span))?;
                state.subst.apply(&annotated_ret)
            } else {
                strip_own(&body_ty)
            };

            // Use join_types (not unify) to reconcile the inferred fn type with the pre-bound
            // SCC type. This is not a value flow — it's two views of the same function that may
            // differ in Own wrappers (e.g. body infers Int, recursive call bound ~Int from literals).
            let fn_ty = Type::Fn(param_types, Box::new(ret_ty.clone()));
            crate::unify::join_types(&fn_ty, tv, &mut state.subst)
                .map_err(|e| spanned(e, decl.span))?;

            fn_bodies[idx] = Some(body_typed);
        }

        // Generalize against an empty env: all env bindings are either fully-quantified
        // schemes (no free vars) or current-SCC monomorphic bindings whose vars should be
        // generalized. This must change if nested let-polymorphism is added.
        let empty_env = TypeEnv::new();
        for &(idx, ref tv) in &pre_bound {
            let final_ty = state.subst.apply(tv);
            let mut scheme = generalize(&final_ty, &empty_env, &state.subst);
            if let Some(tpm) = saved_type_param_maps.get(&idx) {
                let scheme_var_set: HashSet<TypeVarId> = scheme.vars.iter().copied().collect();
                for (name, &original_id) in tpm {
                    let resolved = state.subst.apply(&Type::Var(original_id));
                    if let Type::Var(final_id) = resolved {
                        if scheme_var_set.contains(&final_id) {
                            scheme.var_names.insert(final_id, name.clone());
                        }
                    }
                }
            }
            state.env.bind_with_def_span(
                fn_decls[idx].name.clone(),
                scheme.clone(),
                crate::types::DefSpan { span: fn_decls[idx].span, source_module: None },
            );
            result_schemes[idx] = Some(scheme);
        }
    }

    // Normalize fn_constraint_requirements
    for requirements in fn_constraint_requirements.values_mut() {
        for (_, type_var) in requirements.iter_mut() {
            let resolved = state.subst.apply(&Type::Var(*type_var));
            if let Type::Var(new_id) = resolved {
                *type_var = new_id;
            }
        }
    }

    // Post-inference instance resolution
    if !trait_method_map.is_empty() || !state.imports.imported_fn_constraints.is_empty() {
        for body in fn_bodies.iter() {
            if let Some(body) = body {
                check_trait_instances(
                    body,
                    trait_method_map,
                    trait_registry,
                    &state.subst,
                    &state.imports.imported_fn_constraints,
                )?;
            }
        }
    }

    Ok((fn_decls, result_schemes, fn_bodies, fn_constraint_requirements, shared_type_vars))
}

/// Phase: Type-check impl method bodies and produce InstanceDefInfo.
///
/// Extracted from `infer_module_inner` to reduce stack frame size.
fn typecheck_impl_methods(
    state: &mut ModuleInferenceState,
    module: &Module,
    module_path: &Option<String>,
    trait_registry: &TraitRegistry,
    trait_method_map: &HashMap<String, TraitId>,
    extern_fns: &[ExternFnInfo],
) -> Result<Vec<InstanceDefInfo>, SpannedTypeError> {
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
            let trait_info = trait_registry.lookup_trait(trait_name).unwrap();
            let tv_id = trait_info.type_var_id;

            let instance = trait_registry
                .find_instance_by_trait_and_span(trait_name, *span)
                .unwrap();
            // For HKT partial application, strip anonymous type var args from the
            // target type so it acts as a partial constructor for substitution.
            // e.g., Named("Result", [Var(e), Var(anon)]) → Named("Result", [Var(e)])
            let resolved_target = if trait_info.type_var_arity > 0 {
                strip_anon_type_args(&instance.target_type, &instance.type_var_ids)
            } else {
                instance.target_type.clone()
            };
            let target_type_name = instance.target_type_name.clone();

            let mut instance_methods = Vec::new();

            let all_intrinsic = methods.iter().all(|m| {
                matches!(&*m.body, Expr::App { func, args, .. }
                    if args.is_empty() && matches!(func.as_ref(), Expr::Var { name, .. } if name == "__krypton_intrinsic"))
            });

            for method in methods {
                let trait_method = trait_info
                    .methods
                    .iter()
                    .find(|m| m.name == method.name)
                    .unwrap();

                let concrete_param_types: Vec<Type> = trait_method
                    .param_types
                    .iter()
                    .map(|t| substitute_type_var(t, tv_id, &resolved_target))
                    .collect();
                let _concrete_ret_type =
                    substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);

                let mut impl_method_tpm: HashMap<String, TypeVarId> =
                    instance.type_var_ids.clone();
                let mut impl_method_tpa = HashMap::new();
                for tv_param in &method.type_params {
                    if !impl_method_tpm.contains_key(&tv_param.name) {
                        impl_method_tpm.insert(tv_param.name.clone(), state.gen.fresh());
                        impl_method_tpa.insert(tv_param.name.clone(), tv_param.arity);
                    }
                }

                if method.params.len() != concrete_param_types.len() {
                    return Err(spanned(
                        TypeError::WrongArity {
                            expected: concrete_param_types.len(),
                            actual: method.params.len(),
                        },
                        *span,
                    ));
                }

                for (i, p) in method.params.iter().enumerate() {
                    if let Some(ref ty_expr) = p.ty {
                        if i < concrete_param_types.len() {
                            let annotated_ty = type_registry::resolve_type_expr(
                                ty_expr,
                                &impl_method_tpm,
                                &impl_method_tpa,
                                &state.registry,
                                ResolutionContext::UserAnnotation,
                                Some(&resolved_target),
                            )
                            .map_err(|e| spanned(e, p.span))?;
                            unify(&annotated_ty, &concrete_param_types[i], &mut state.subst)
                                .map_err(|e| spanned_with_names(e, p.span, &impl_method_tpm))?;
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
                            ResolutionContext::UserAnnotation,
                            Some(&resolved_target),
                        )
                        .map_err(|e| spanned(e, method.span))?;
                    unify(&concrete_ret, &annotated_ret, &mut state.subst)
                        .map_err(|e| {
                            let error = match e {
                                TypeError::WrongArity { .. } => TypeError::Mismatch {
                                    expected: concrete_ret.clone(),
                                    actual: annotated_ret.clone(),
                                },
                                other => other,
                            };
                            spanned_with_names(error, method.span, &impl_method_tpm)
                        })?;
                }

                if all_intrinsic {
                    continue;
                }

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
                let prev_fn_return_type = state.env.fn_return_type.take();
                let concrete_ret_type =
                    substitute_type_var(&trait_method.return_type, tv_id, &resolved_target);
                state.env.fn_return_type = Some(concrete_ret_type);

                let body_typed = {
                    let empty_efn = HashSet::new();
                    let mut ctx = InferenceContext {
                        env: &mut state.env,
                        subst: &mut state.subst,
                        gen: &mut state.gen,
                        registry: Some(&state.registry),
                        recur_params: Some(param_types_inferred.clone()),
                        let_own_spans: Some(&mut state.let_own_spans),
                        lambda_own_captures: Some(&mut state.lambda_own_captures),
                        type_param_map: &impl_method_tpm,
                        type_param_arity: &impl_method_tpa,
                        qualified_modules: &state.qualified_modules,
                        imported_fn_types: &state.imports.imported_fn_types,
                        extern_fn_names: &empty_efn,
                        enclosing_fn_constraints: &[],
                        shadowed_prelude_fns: &state.imports.shadowed_prelude_fns,
                        trait_method_map,
                        self_type: Some(resolved_target.clone()),
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

                let expected_ret_type = state.subst.apply(
                    &substitute_type_var(&trait_method.return_type, tv_id, &resolved_target),
                );
                coerce_unify(&final_ret_type, &expected_ret_type, &mut state.subst)
                    .map_err(|_| spanned_with_names(
                        TypeError::Mismatch {
                            expected: expected_ret_type.clone(),
                            actual: final_ret_type.clone(),
                        },
                        method.span,
                        &impl_method_tpm,
                    ))?;

                let fn_ty = Type::Fn(final_param_types, Box::new(final_ret_type));
                let scheme = TypeScheme {
                    vars: vec![],
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };

                instance_methods.push(typed_ast::InstanceMethod {
                    name: method.name.clone(),
                    params: method.params.iter().map(|p| p.name.clone()).collect(),
                    body: body_typed,
                    scheme,
                });
            }

            let inst_trait_id = trait_registry.lookup_trait(trait_name)
                .map(|ti| TraitId::new(ti.module_path.clone(), ti.name.clone()))
                .unwrap_or_else(|| TraitId::new(module_path.clone(), trait_name.clone()));
            instance_defs.push(InstanceDefInfo {
                trait_name: trait_name.clone(),
                trait_id: inst_trait_id,
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

    Ok(instance_defs)
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
    prelude_tree_paths: &HashSet<String>,
) -> Result<TypedModule, SpannedTypeError> {
    let is_core_module = module_path.as_ref().is_some_and(|p| p.starts_with("core/"));
    let is_prelude_tree = module_path.as_ref()
        .is_some_and(|p| prelude_tree_paths.contains(p));

    let mut state = ModuleInferenceState::new(is_core_module);

    let synthetic_prelude_import = state.build_synthetic_prelude_import(
        is_prelude_tree,
        cache,
        parsed_modules,
    );

    state.process_imports(module, cache, parsed_modules, synthetic_prelude_import.as_ref())?;
    reserve_gen_for_env_schemes(&state.env, &mut state.gen);
    let (extern_fns, extern_java_types) = state.process_local_externs(module)?;
    state.cleanup_prelude_shadows(module);
    state.preregister_type_names(module);
    let constructor_schemes = state.process_local_type_decls(module)?;

    // Phase: trait registration, deriving, impl registration
    let (trait_registry, exported_trait_defs, derived_instance_defs, trait_method_map) =
        process_traits_and_deriving(
            &mut state,
            module,
            cache,
            &module_path,
            is_prelude_tree,
            prelude_tree_paths,
            is_core_module,
        )?;

    // Phase: SCC-based function inference
    let (fn_decls, result_schemes, fn_bodies, fn_constraint_requirements, shared_type_vars) =
        infer_function_bodies(
            &mut state,
            module,
            &extern_fns,
            &trait_registry,
            &trait_method_map,
        )?;

    // Phase: impl method type-checking
    let instance_defs = typecheck_impl_methods(
        &mut state,
        module,
        &module_path,
        &trait_registry,
        &trait_method_map,
        &extern_fns,
    )?;

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
        extern_java_types,
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
        origin: None,
    };
    let param_b = TypedExpr {
        kind: TypedExprKind::Var("__b".to_string()),
        ty: target_type.clone(),
        span,
        origin: None,
    };
    let true_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(true)),
        ty: Type::Bool,
        span,
        origin: None,
    };
    let false_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(false)),
        ty: Type::Bool,
        span,
        origin: None,
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
                        origin: None,
                    };
                    let rhs = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_b.clone()),
                            field: field_name.clone(),
                        },
                        ty: field_ty.clone(),
                        span,
                        origin: None,
                    };
                    let cmp = TypedExpr {
                        kind: TypedExprKind::BinaryOp {
                            op: BinOp::Eq,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        ty: Type::Bool,
                        span,
                        origin: None,
                    };
                    result = TypedExpr {
                        kind: TypedExprKind::If {
                            cond: Box::new(cmp),
                            then_: Box::new(result),
                            else_: Box::new(false_expr()),
                        },
                        ty: Type::Bool,
                        span,
                        origin: None,
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
                                            origin: None,
                                        };
                                        let y = TypedExpr {
                                            kind: TypedExprKind::Var(format!("__y{}", i)),
                                            ty: ft.clone(),
                                            span,
                                            origin: None,
                                        };
                                        let cmp = TypedExpr {
                                            kind: TypedExprKind::BinaryOp {
                                                op: BinOp::Eq,
                                                lhs: Box::new(x),
                                                rhs: Box::new(y),
                                            },
                                            ty: Type::Bool,
                                            span,
                                            origin: None,
                                        };
                                        result = TypedExpr {
                                            kind: TypedExprKind::If {
                                                cond: Box::new(cmp),
                                                then_: Box::new(result),
                                                else_: Box::new(false_expr()),
                                            },
                                            ty: Type::Bool,
                                            span,
                                            origin: None,
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
                        origin: None,
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
                origin: None,
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
    trait_id: Option<TraitId>,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
        origin: None,
    };

    let str_lit = |s: &str| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::Lit(Lit::String(s.to_string())),
            ty: Type::String,
            span,
            origin: None,
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
            origin: None,
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
                    origin: trait_id.clone(),
                }),
                args: vec![expr],
            },
            ty: Type::String,
            span,
            origin: None,
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
                    origin: None,
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
                                origin: None,
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
                origin: None,
            }
        }
    };

    let fn_ty = Type::Fn(vec![target_type.clone()], Box::new(Type::String));
    (body, fn_ty)
}

fn synthesize_hash_body(
    type_info: &crate::type_registry::TypeInfo,
    target_type: &Type,
    span: Span,
    trait_id: Option<TraitId>,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
        origin: None,
    };

    let int_lit = |n: i64| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::Lit(Lit::Int(n)),
            ty: Type::Int,
            span,
            origin: None,
        }
    };

    let hash_call = |expr: TypedExpr| -> TypedExpr {
        let arg_ty = expr.ty.clone();
        TypedExpr {
            kind: TypedExprKind::App {
                func: Box::new(TypedExpr {
                    kind: TypedExprKind::Var("hash".to_string()),
                    ty: Type::Fn(vec![arg_ty], Box::new(Type::Int)),
                    span,
                    origin: trait_id.clone(),
                }),
                args: vec![expr],
            },
            ty: Type::Int,
            span,
            origin: None,
        }
    };

    // 31 * acc + hash(field)
    let combine_hash = |acc: TypedExpr, field_hash: TypedExpr| -> TypedExpr {
        let mul = TypedExpr {
            kind: TypedExprKind::BinaryOp {
                op: BinOp::Mul,
                lhs: Box::new(int_lit(31)),
                rhs: Box::new(acc),
            },
            ty: Type::Int,
            span,
            origin: None,
        };
        TypedExpr {
            kind: TypedExprKind::BinaryOp {
                op: BinOp::Add,
                lhs: Box::new(mul),
                rhs: Box::new(field_hash),
            },
            ty: Type::Int,
            span,
            origin: None,
        }
    };

    let body = match &type_info.kind {
        crate::type_registry::TypeKind::Record { fields } => {
            if fields.is_empty() {
                int_lit(0)
            } else {
                let mut result = {
                    let (field_name, field_ty) = &fields[0];
                    let field_access = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_a.clone()),
                            field: field_name.clone(),
                        },
                        ty: field_ty.clone(),
                        span,
                        origin: None,
                    };
                    hash_call(field_access)
                };
                for (field_name, field_ty) in &fields[1..] {
                    let field_access = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_a.clone()),
                            field: field_name.clone(),
                        },
                        ty: field_ty.clone(),
                        span,
                        origin: None,
                    };
                    result = combine_hash(result, hash_call(field_access));
                }
                result
            }
        }
        crate::type_registry::TypeKind::Sum { variants } => {
            let arms: Vec<TypedMatchArm> = variants
                .iter()
                .enumerate()
                .map(|(idx, variant)| {
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

                    let mut result = hash_call(int_lit(idx as i64));
                    for (i, ft) in variant.fields.iter().enumerate() {
                        let var_expr = TypedExpr {
                            kind: TypedExprKind::Var(format!("__x{}", i)),
                            ty: ft.clone(),
                            span,
                            origin: None,
                        };
                        result = combine_hash(result, hash_call(var_expr));
                    }

                    TypedMatchArm { pattern, body: result }
                })
                .collect();

            TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(param_a),
                    arms,
                },
                ty: Type::Int,
                span,
                origin: None,
            }
        }
    };

    let fn_ty = Type::Fn(vec![target_type.clone()], Box::new(Type::Int));
    (body, fn_ty)
}
