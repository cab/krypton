use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Span, TypeConstraint, TypeDecl, TypeDeclKind, TypeParam};

use crate::trait_registry::TraitRegistry;
use crate::type_registry;
use crate::typed_ast::{
    self, ConstructorKind, ResolvedBindingRef, ResolvedCallableRef, ResolvedConstructorRef,
    ResolvedTraitMethodRef, ResolvedTypeRef, TraitName,
};
use crate::types::{
    BindingSource, ConstructorBindingKind, Substitution, Type, TypeEnv, TypeScheme, TypeVarGen,
    TypeVarId,
};
use crate::unify::{self, SpannedTypeError, TypeError};

pub(crate) fn require_param_vars(tc: &TypeConstraint) -> Result<Vec<&str>, SpannedTypeError> {
    tc.as_param_vars().ok_or_else(|| {
        spanned(
            TypeError::UnsupportedConstraint {
                trait_name: tc.trait_name.clone(),
                reason: "trait constraint arguments must be bare type variables",
            },
            tc.span,
        )
    })
}

pub(crate) fn constructor_names(td: &TypeDecl) -> Vec<String> {
    match &td.kind {
        TypeDeclKind::Sum { variants } => variants.iter().map(|v| v.name.clone()).collect(),
        TypeDeclKind::Record { .. } => vec![td.name.clone()],
    }
}

pub(crate) fn constructor_binding_kind_for_decl(
    td: &TypeDecl,
    constructor_name: &str,
) -> ConstructorBindingKind {
    match &td.kind {
        TypeDeclKind::Record { .. } => ConstructorBindingKind::Record,
        TypeDeclKind::Sum { variants } => {
            if variants
                .iter()
                .any(|variant| variant.name == constructor_name)
            {
                ConstructorBindingKind::Variant
            } else {
                ConstructorBindingKind::Record
            }
        }
    }
}

pub(crate) fn constructor_binding_kind_for_export(
    info: &typed_ast::ExportedTypeInfo,
    constructor_name: &str,
) -> ConstructorBindingKind {
    match &info.kind {
        typed_ast::ExportedTypeKind::Opaque => {
            unreachable!("opaque exported types do not have constructors")
        }
        typed_ast::ExportedTypeKind::Record { .. } => ConstructorBindingKind::Record,
        typed_ast::ExportedTypeKind::Sum { variants } => {
            if variants
                .iter()
                .any(|variant| variant.name == constructor_name)
            {
                ConstructorBindingKind::Variant
            } else {
                ConstructorBindingKind::Record
            }
        }
    }
}
pub(crate) fn retarget_bare_var_owned_arg(
    err: &mut SpannedTypeError,
    raw_param_ty: Option<&Type>,
    arg_ty: &Type,
    subst: &Substitution,
    callee_name: Option<&str>,
    param_index: usize,
) {
    if !matches!(
        &*err.error,
        TypeError::Mismatch { .. }
            | TypeError::OwnershipMismatch { .. }
            | TypeError::QualifierConflict { .. }
    ) {
        return;
    }
    let Some(raw) = raw_param_ty else { return };
    if !matches!(raw, Type::Var(_)) {
        return;
    }
    // Needed when downstream context pins `α := T` before the arg-coerce
    // loop runs, so the pre-check's `walk(raw) == Var` guard misses and the
    // coercion surfaces a plain `Mismatch` we rewrite here.
    if !matches!(unify::walk(arg_ty, subst), Type::Own(_)) {
        return;
    }
    let resolved_arg = subst.apply(arg_ty);
    err.error = Box::new(TypeError::BareTypeVarResourceArg {
        callee_name: callee_name.map(|s| s.to_string()),
        param_index,
        param_ty: raw.clone(),
        arg_ty: resolved_arg,
    });
}

#[derive(Clone)]
pub(crate) struct QualifiedExport {
    pub(crate) local_name: String,
    pub(crate) scheme: TypeScheme,
    pub(crate) resolved_ref: Option<ResolvedBindingRef>,
}

#[derive(Clone)]
pub(crate) struct QualifiedModuleBinding {
    pub(crate) module_path: String,
    pub(crate) exports: HashMap<String, QualifiedExport>,
}

pub(crate) fn imported_binding_ref(
    module_path: impl Into<String>,
    local_name: impl Into<String>,
) -> ResolvedBindingRef {
    ResolvedBindingRef::Callable(ResolvedCallableRef::ImportedFunction {
        qualified_name: typed_ast::QualifiedName::new(module_path.into(), local_name.into()),
        overload_signature: None,
    })
}

pub(crate) fn trait_method_binding_ref(
    trait_name: TraitName,
    method_name: impl Into<String>,
) -> ResolvedBindingRef {
    ResolvedBindingRef::TraitMethod(ResolvedTraitMethodRef {
        trait_name,
        method_name: method_name.into(),
    })
}

pub(crate) fn type_binding_ref(
    module_path: impl Into<String>,
    local_name: impl Into<String>,
) -> ResolvedTypeRef {
    ResolvedTypeRef {
        qualified_name: typed_ast::QualifiedName::new(module_path.into(), local_name.into()),
    }
}

pub(crate) fn constructor_binding_ref(
    type_module_path: impl Into<String>,
    type_name: impl Into<String>,
    constructor_name: impl Into<String>,
    kind: ConstructorKind,
) -> ResolvedBindingRef {
    ResolvedBindingRef::Constructor(ResolvedConstructorRef {
        type_ref: type_binding_ref(type_module_path, type_name),
        constructor_name: constructor_name.into(),
        kind,
    })
}

pub(crate) fn resolved_ref_from_binding_source(
    source: &BindingSource,
) -> Option<ResolvedBindingRef> {
    resolved_ref_from_binding_source_with_overload(source, None)
}

/// Build a `ResolvedBindingRef` for a `BindingSource`, attaching the given
/// `OverloadSignature` when the source is a callable function variant.
/// Call sites that selected an overload winner use this to thread the
/// concrete signature through to IR. `overload` is ignored for non-callable
/// sources (constructors, trait methods, intrinsics).
pub(crate) fn resolved_ref_from_binding_source_with_overload(
    source: &BindingSource,
    overload: Option<typed_ast::OverloadSignature>,
) -> Option<ResolvedBindingRef> {
    match source {
        BindingSource::LocalValue => None,
        BindingSource::TopLevelLocalFunction { qualified_name } => Some(
            ResolvedBindingRef::Callable(ResolvedCallableRef::LocalFunction {
                qualified_name: typed_ast::QualifiedName::new(
                    qualified_name.module_path.clone(),
                    qualified_name.local_name.clone(),
                ),
                overload_signature: overload,
            }),
        ),
        BindingSource::ImportedFunction { qualified_name, .. } => Some(
            ResolvedBindingRef::Callable(ResolvedCallableRef::ImportedFunction {
                qualified_name: typed_ast::QualifiedName::new(
                    qualified_name.module_path.clone(),
                    qualified_name.local_name.clone(),
                ),
                overload_signature: overload,
            }),
        ),
        BindingSource::Constructor {
            type_qualified_name,
            constructor_name,
            kind,
        } => Some(constructor_binding_ref(
            type_qualified_name.module_path.clone(),
            type_qualified_name.local_name.clone(),
            constructor_name.clone(),
            match kind {
                ConstructorBindingKind::Record => ConstructorKind::Record,
                ConstructorBindingKind::Variant => ConstructorKind::Variant,
            },
        )),
        BindingSource::TraitMethod {
            trait_module_path,
            trait_name,
            method_name,
            ..
        } => Some(trait_method_binding_ref(
            TraitName::new(trait_module_path.clone(), trait_name.clone()),
            method_name.clone(),
        )),
        BindingSource::IntrinsicFunction { name } => Some(ResolvedBindingRef::Callable(
            ResolvedCallableRef::Intrinsic { name: name.clone() },
        )),
    }
}

pub(crate) fn is_callable_scheme(scheme: &TypeScheme) -> bool {
    match &scheme.ty {
        Type::Fn(_, _) => true,
        Type::Own(inner) => matches!(inner.as_ref(), Type::Fn(_, _)),
        _ => false,
    }
}

pub(crate) fn qualifier_suggested_usage(
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

pub(crate) fn build_type_param_maps(
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

/// Strip `Own` and `MaybeOwn` wrappers from non-function types.
/// Used at consumption sites (binary ops, if conditions, etc.) where
/// the ownership wrapper is not meaningful.
pub(crate) fn strip_own(ty: &Type) -> Type {
    match ty {
        Type::Own(inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => *inner.clone(),
        Type::MaybeOwn(_, inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => *inner.clone(),
        other => other.clone(),
    }
}

/// Convert `Own(T)` to `MaybeOwn(fresh_q, T)` — defers the ownership decision
/// rather than discarding it. Used when fabricating expected function types
/// for unresolved callees.
pub(crate) fn defer_own(ty: &Type, subst: &mut Substitution) -> Type {
    match ty {
        Type::Own(inner) if !matches!(inner.as_ref(), Type::Fn(_, _)) => {
            let q = subst.fresh_qual();
            Type::MaybeOwn(q, inner.clone())
        }
        Type::MaybeOwn(_, _) => ty.clone(), // preserve existing MaybeOwn
        other => other.clone(),
    }
}

/// Collect free type variables in a type.
pub(crate) fn free_vars(ty: &Type) -> HashSet<TypeVarId> {
    let mut out = HashSet::new();
    free_vars_into(ty, &mut out);
    out
}

pub(crate) fn match_type_with_bindings(
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
        (Type::MaybeOwn(_, inner), other)
        | (other, Type::MaybeOwn(_, inner))
        | (Type::Shape(inner), other)
        | (other, Type::Shape(inner)) => match_type_with_bindings(inner, other, bindings),
        (Type::Fn(lhs_params, lhs_ret), Type::Fn(rhs_params, rhs_ret)) => {
            lhs_params.len() == rhs_params.len()
                && lhs_params
                    .iter()
                    .zip(rhs_params.iter())
                    .all(|((_, lhs), (_, rhs))| match_type_with_bindings(lhs, rhs, bindings))
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

/// Recursive accumulator for `free_vars`.
pub(crate) fn free_vars_into(ty: &Type, out: &mut HashSet<TypeVarId>) {
    match ty {
        Type::Var(id) => {
            out.insert(*id);
        }
        Type::Fn(params, ret) => {
            for (_, p) in params {
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
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            free_vars_into(inner, out)
        }
        Type::Tuple(elems) => {
            for e in elems {
                free_vars_into(e, out);
            }
        }
        _ => {}
    }
}

/// Collect free type variables across all bindings in the environment.
pub(crate) fn free_vars_env(env: &TypeEnv, subst: &Substitution) -> HashSet<TypeVarId> {
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

pub(crate) fn collect_type_expr_var_names(texpr: &krypton_parser::ast::TypeExpr, out: &mut HashSet<String>) {
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
                collect_type_expr_var_names(&param.ty, out);
            }
            collect_type_expr_var_names(ret, out);
        }
        krypton_parser::ast::TypeExpr::Own { inner, .. }
        | krypton_parser::ast::TypeExpr::Shape { inner, .. } => {
            collect_type_expr_var_names(inner, out);
        }
        krypton_parser::ast::TypeExpr::Tuple { elements, .. } => {
            for element in elements {
                collect_type_expr_var_names(element, out);
            }
        }
        krypton_parser::ast::TypeExpr::Named { .. }
        | krypton_parser::ast::TypeExpr::Qualified { .. } => {}
        krypton_parser::ast::TypeExpr::Wildcard { .. } => {}
    }
}

/// Validate wildcards in an impl target type expression.
/// Returns the count of wildcards at the outermost App level.
/// Errors if wildcards are nested or appear outside an App.
pub(crate) fn validate_impl_wildcards(texpr: &krypton_parser::ast::TypeExpr) -> Result<usize, TypeError> {
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
        krypton_parser::ast::TypeExpr::Fn { params, ret, .. } => {
            let mut wildcard_count = 0;
            for param in params {
                match &param.ty {
                    krypton_parser::ast::TypeExpr::Wildcard { .. } => wildcard_count += 1,
                    other => {
                        if contains_wildcard(other) {
                            let span = wildcard_span(other).unwrap_or((0, 0));
                            return Err(TypeError::NestedWildcard { span });
                        }
                    }
                }
            }
            match ret.as_ref() {
                krypton_parser::ast::TypeExpr::Wildcard { .. } => wildcard_count += 1,
                other => {
                    if contains_wildcard(other) {
                        let span = wildcard_span(other).unwrap_or((0, 0));
                        return Err(TypeError::NestedWildcard { span });
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

pub(crate) fn contains_wildcard(texpr: &krypton_parser::ast::TypeExpr) -> bool {
    match texpr {
        krypton_parser::ast::TypeExpr::Wildcard { .. } => true,
        krypton_parser::ast::TypeExpr::App { args, .. } => args.iter().any(contains_wildcard),
        krypton_parser::ast::TypeExpr::Fn { params, ret, .. } => {
            params.iter().any(|p| contains_wildcard(&p.ty)) || contains_wildcard(ret)
        }
        krypton_parser::ast::TypeExpr::Own { inner, .. }
        | krypton_parser::ast::TypeExpr::Shape { inner, .. } => contains_wildcard(inner),
        krypton_parser::ast::TypeExpr::Tuple { elements, .. } => {
            elements.iter().any(contains_wildcard)
        }
        krypton_parser::ast::TypeExpr::Named { .. }
        | krypton_parser::ast::TypeExpr::Var { .. }
        | krypton_parser::ast::TypeExpr::Qualified { .. } => false,
    }
}

pub(crate) fn wildcard_span(texpr: &krypton_parser::ast::TypeExpr) -> Option<krypton_parser::ast::Span> {
    match texpr {
        krypton_parser::ast::TypeExpr::Wildcard { span } => Some(*span),
        krypton_parser::ast::TypeExpr::App { args, .. } => args.iter().find_map(wildcard_span),
        krypton_parser::ast::TypeExpr::Fn { params, ret, .. } => params
            .iter()
            .find_map(|p| wildcard_span(&p.ty))
            .or_else(|| wildcard_span(ret)),
        krypton_parser::ast::TypeExpr::Own { inner, .. }
        | krypton_parser::ast::TypeExpr::Shape { inner, .. } => wildcard_span(inner),
        krypton_parser::ast::TypeExpr::Tuple { elements, .. } => {
            elements.iter().find_map(wildcard_span)
        }
        _ => None,
    }
}

/// Resolve an impl target type expression, handling wildcards by generating
/// fresh anonymous type variables for each `_`.
pub(crate) fn resolve_impl_target(
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
                &krypton_parser::ast::TypeExpr::Named {
                    name: name.clone(),
                    span: (0, 0),
                },
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
        krypton_parser::ast::TypeExpr::Fn { params, ret, .. } => {
            let mut resolved_params: Vec<(crate::types::ParamMode, Type)> = Vec::new();
            for p in params {
                let ty = match &p.ty {
                    krypton_parser::ast::TypeExpr::Wildcard { .. } => Type::Var(gen.fresh()),
                    other => type_registry::resolve_type_expr(
                        other,
                        type_param_map,
                        type_param_arity,
                        registry,
                        type_registry::ResolutionContext::UserAnnotation,
                        None,
                    )?,
                };
                resolved_params.push((p.mode, ty));
            }
            let resolved_ret = match ret.as_ref() {
                krypton_parser::ast::TypeExpr::Wildcard { .. } => Type::Var(gen.fresh()),
                other => type_registry::resolve_type_expr(
                    other,
                    type_param_map,
                    type_param_arity,
                    registry,
                    type_registry::ResolutionContext::UserAnnotation,
                    None,
                )?,
            };
            Ok(Type::Fn(resolved_params, Box::new(resolved_ret)))
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
pub(crate) fn strip_anon_type_args(ty: &Type, type_var_ids: &HashMap<String, TypeVarId>) -> Type {
    let known_var_ids: std::collections::HashSet<TypeVarId> =
        type_var_ids.values().copied().collect();
    match ty {
        Type::Named(name, args) => {
            let kept: Vec<Type> = args
                .iter()
                .filter(|arg| match arg {
                    Type::Var(id) => known_var_ids.contains(id),
                    _ => true,
                })
                .cloned()
                .collect();
            Type::Named(name.clone(), kept)
        }
        Type::Fn(params, ret) => {
            let kept_params: Vec<(crate::types::ParamMode, Type)> = params
                .iter()
                .filter(|(_, p)| match p {
                    Type::Var(id) => known_var_ids.contains(id),
                    _ => true,
                })
                .cloned()
                .collect();
            let kept_ret = match ret.as_ref() {
                Type::Var(id) if !known_var_ids.contains(id) => Box::new(Type::FnHole),
                _ => ret.clone(),
            };
            Type::Fn(kept_params, kept_ret)
        }
        _ => ty.clone(),
    }
}

pub(crate) fn reserve_gen_for_env_schemes(env: &TypeEnv, gen: &mut TypeVarGen) {
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
pub(crate) fn generalize(ty: &Type, env: &TypeEnv, subst: &Substitution) -> TypeScheme {
    let ty = subst.apply(ty);
    let ty_vars = free_vars(&ty);
    let env_vars = free_vars_env(env, subst);
    let mut vars: Vec<TypeVarId> = ty_vars.difference(&env_vars).copied().collect();
    vars.sort();
    TypeScheme {
        vars,
        constraints: Vec::new(),
        ty,
        var_names: HashMap::new(),
    }
}

/// Attach a span to a TypeError, producing a SpannedTypeError.
pub(crate) fn spanned(error: TypeError, span: krypton_parser::ast::Span) -> SpannedTypeError {
    SpannedTypeError {
        error: Box::new(error),
        span,
        note: None,
        secondary_span: None,
        source_file: None,
        var_names: None,
    }
}

/// Like `spanned` but populates var_names from a type_param_map for better error messages.
pub(crate) fn spanned_with_names(
    error: TypeError,
    span: krypton_parser::ast::Span,
    type_param_map: &HashMap<String, TypeVarId>,
) -> SpannedTypeError {
    let var_names: Vec<(TypeVarId, String)> = type_param_map
        .iter()
        .map(|(name, &id)| (id, name.clone()))
        .collect();
    SpannedTypeError {
        error: Box::new(error),
        span,
        note: None,
        secondary_span: None,
        source_file: None,
        var_names: Some(var_names),
    }
}

/// Attach a span and secondary label to a duplicate-instance error from `register_instance`.
pub(crate) fn duplicate_instance_spanned(
    error: TypeError,
    span: krypton_parser::ast::Span,
    existing_span: krypton_parser::ast::Span,
) -> SpannedTypeError {
    SpannedTypeError {
        error: Box::new(error),
        span,
        note: None,
        secondary_span: Some(Box::new(crate::unify::SecondaryLabel {
            span: existing_span,
            message: "first implementation here".into(),
            source_file: None,
        })),
        source_file: None,
        var_names: None,
    }
}

/// Construct a NoInstance error with diagnostic note when a near-miss instance exists.
pub(crate) fn no_instance_error(
    trait_registry: &TraitRegistry,
    trait_name: &TraitName,
    ty: &Type,
    span: Span,
    var_names: &HashMap<TypeVarId, String>,
    cause: crate::type_error::NoInstanceCause,
) -> SpannedTypeError {
    let display_ty = ty.strip_own();
    let mut err = spanned(
        TypeError::NoInstance {
            trait_name: trait_name.local_name.clone(),
            ty: crate::types::format_type_for_error(&display_ty, var_names),
            cause,
        },
        span,
    );
    if let Some(diag) = trait_registry.diagnose_missing_instance(trait_name, ty) {
        err.note = Some(diag.to_note());
    }
    err
}

/// Recursively rewrite type variables according to a remap table. Variables
/// not in the table are left unchanged.
pub(crate) fn remap_type_vars(ty: &Type, remap: &HashMap<TypeVarId, TypeVarId>) -> Type {
    match ty {
        Type::Var(id) => Type::Var(remap.get(id).copied().unwrap_or(*id)),
        Type::Fn(params, ret) => Type::Fn(
            params
                .iter()
                .map(|(m, p)| (*m, remap_type_vars(p, remap)))
                .collect(),
            Box::new(remap_type_vars(ret, remap)),
        ),
        Type::Named(name, args) => Type::Named(
            name.clone(),
            args.iter().map(|a| remap_type_vars(a, remap)).collect(),
        ),
        Type::App(ctor, args) => Type::App(
            Box::new(remap_type_vars(ctor, remap)),
            args.iter().map(|a| remap_type_vars(a, remap)).collect(),
        ),
        Type::Tuple(elems) => {
            Type::Tuple(elems.iter().map(|e| remap_type_vars(e, remap)).collect())
        }
        Type::Own(inner) => Type::Own(Box::new(remap_type_vars(inner, remap))),
        Type::Shape(inner) => Type::Shape(Box::new(remap_type_vars(inner, remap))),
        Type::MaybeOwn(q, inner) => Type::MaybeOwn(*q, Box::new(remap_type_vars(inner, remap))),
        _ => ty.clone(),
    }
}

/// Check if a type is concretely not a function (after walking substitution).
pub(crate) fn is_concrete_non_function(ty: &Type, subst: &Substitution) -> bool {
    let walked = subst.apply(ty);
    match &walked {
        Type::Var(_) | Type::Fn(_, _) => false,
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            is_concrete_non_function(inner, subst)
        }
        _ => true,
    }
}

pub(crate) fn instantiate_scheme_with_types(
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
