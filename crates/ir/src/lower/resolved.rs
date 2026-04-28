// TypedExpr resolved-ref accessors. Free helpers that peel `TypeApp`
// wrappers and project the typechecker's resolved-binding metadata
// (callable, constructor, trait-method, variant) so the lowering
// callers don't have to redo the disambiguation each time.

use krypton_typechecker::typed_ast::{
    self, OverloadSignature, QualifiedName, ResolvedBindingRef, ResolvedCallableRef,
    ResolvedConstructorRef, ResolvedTraitMethodRef, ResolvedVariantRef, TypedExpr, TypedExprKind,
};
use krypton_typechecker::types::{SchemeVarId, Type};

pub(super) fn resolved_ref(expr: &TypedExpr) -> Option<&ResolvedBindingRef> {
    match &expr.kind {
        TypedExprKind::Var(_) => expr.resolved_ref.as_ref(),
        TypedExprKind::TypeApp { expr: inner, .. } => {
            expr.resolved_ref.as_ref().or_else(|| resolved_ref(inner))
        }
        _ => expr.resolved_ref.as_ref(),
    }
}

pub(super) fn resolved_callable_ref(expr: &TypedExpr) -> Option<(&str, &ResolvedCallableRef)> {
    match &expr.kind {
        TypedExprKind::Var(name) => match resolved_ref(expr) {
            Some(ResolvedBindingRef::Callable(callable_ref)) => Some((name.as_str(), callable_ref)),
            _ => None,
        },
        TypedExprKind::TypeApp { expr: inner, .. } => resolved_callable_ref(inner),
        _ => None,
    }
}

pub(super) fn resolved_constructor_ref(expr: &TypedExpr) -> Option<(&str, &ResolvedConstructorRef)> {
    match &expr.kind {
        TypedExprKind::Var(name) => match resolved_ref(expr) {
            Some(ResolvedBindingRef::Constructor(constructor_ref)) => {
                Some((name.as_str(), constructor_ref))
            }
            _ => None,
        },
        TypedExprKind::TypeApp { expr: inner, .. } => resolved_constructor_ref(inner),
        _ => None,
    }
}

pub(super) fn callable_qualified_name(r: &ResolvedCallableRef, _module_path: &str) -> QualifiedName {
    match r {
        ResolvedCallableRef::LocalFunction { qualified_name, .. } => qualified_name.clone(),
        ResolvedCallableRef::ImportedFunction { qualified_name, .. } => qualified_name.clone(),
        ResolvedCallableRef::Intrinsic { name } => {
            QualifiedName::new("__builtin__".to_string(), name.clone())
        }
    }
}

/// Extract the overload signature published by the typechecker, if any.
/// `None` means single-candidate (no ambiguity to resolve). `Some(sig)`
/// means the typechecker picked a specific overload at this call site and
/// IR should match against it via `types_overlap`.
pub(super) fn callable_overload_signature(r: &ResolvedCallableRef) -> Option<&OverloadSignature> {
    match r {
        ResolvedCallableRef::LocalFunction {
            overload_signature, ..
        } => overload_signature.as_ref(),
        ResolvedCallableRef::ImportedFunction {
            overload_signature, ..
        } => overload_signature.as_ref(),
        ResolvedCallableRef::Intrinsic { .. } => None,
    }
}

pub(super) fn resolved_trait_method_ref(expr: &TypedExpr) -> Option<&ResolvedTraitMethodRef> {
    match resolved_ref(expr) {
        Some(ResolvedBindingRef::TraitMethod(trait_ref)) => Some(trait_ref),
        _ => None,
    }
}

/// Extract function name, resolved binding ref, and explicit user type bindings
/// from a call expression, peeling through TypeApp wrappers. Collects the
/// outermost bindings.
pub(super) fn extract_call_info(
    expr: &TypedExpr,
) -> (
    Option<String>,
    Option<ResolvedBindingRef>,
    Vec<(SchemeVarId, Type)>,
) {
    match &expr.kind {
        TypedExprKind::Var(name) => (Some(name.clone()), expr.resolved_ref.clone(), vec![]),
        TypedExprKind::TypeApp {
            expr: inner,
            type_bindings,
        } => {
            let (name, resolved_ref, _) = extract_call_info(inner);
            let resolved_ref = resolved_ref.or_else(|| expr.resolved_ref.clone());
            (name, resolved_ref, type_bindings.clone())
        }
        _ => (None, expr.resolved_ref.clone(), vec![]),
    }
}

pub(super) fn variant_ref_from_constructor(
    constructor_ref: &ResolvedConstructorRef,
) -> Option<ResolvedVariantRef> {
    (constructor_ref.kind == typed_ast::ConstructorKind::Variant).then(|| ResolvedVariantRef {
        type_ref: constructor_ref.type_ref.clone(),
        variant_name: constructor_ref.constructor_name.clone(),
    })
}
