use std::collections::HashSet;

use krypton_parser::ast::Span;

use crate::type_registry::{TypeKind, TypeRegistry};
use crate::typed_ast::{TypedMatchArm, TypedPattern};
use crate::types::Type;
use crate::unify::{SpannedTypeError, TypeError};

pub fn check_exhaustiveness(
    scrutinee_ty: &Type,
    arms: &[TypedMatchArm],
    registry: Option<&TypeRegistry>,
    span: Span,
) -> Result<(), SpannedTypeError> {
    let patterns: Vec<&TypedPattern> = arms.iter().map(|a| &a.pattern).collect();
    check_patterns_exhaustive(scrutinee_ty, &patterns, registry, span)
}

fn check_patterns_exhaustive(
    scrutinee_ty: &Type,
    patterns: &[&TypedPattern],
    registry: Option<&TypeRegistry>,
    span: Span,
) -> Result<(), SpannedTypeError> {
    // If any pattern is a wildcard/var at top level, it's exhaustive
    for pat in patterns {
        if is_catch_all(pat) {
            return Ok(());
        }
    }

    // Resolve the scrutinee type
    match scrutinee_ty {
        Type::Named(name, _) => {
            let registry = match registry {
                Some(r) => r,
                None => return Ok(()), // no registry, can't check
            };
            let type_info = match registry.lookup_type(name) {
                Some(info) => info,
                None => return Ok(()), // unknown type, skip
            };
            match &type_info.kind {
                TypeKind::Sum { variants } => {
                    let all_variants: Vec<&str> =
                        variants.iter().map(|v| v.name.as_str()).collect();

                    // Collect which variants are matched
                    let matched: HashSet<&str> = patterns
                        .iter()
                        .filter_map(|pat| constructor_name(pat))
                        .collect();

                    let missing: Vec<String> = all_variants
                        .iter()
                        .filter(|v| !matched.contains(*v))
                        .map(|v| v.to_string())
                        .collect();

                    if !missing.is_empty() {
                        return Err(SpannedTypeError {
                            error: TypeError::NonExhaustive { missing },
                            span,
                            note: None,
                            secondary_span: None,
                        });
                    }

                    // For each matched variant, check nested sub-patterns
                    for variant_info in variants {
                        if variant_info.fields.is_empty() {
                            continue;
                        }
                        // Collect sub-patterns for this variant
                        let sub_patterns: Vec<&[TypedPattern]> = patterns
                            .iter()
                            .filter_map(|pat| match pat {
                                TypedPattern::Constructor { name, args, .. }
                                    if name == &variant_info.name =>
                                {
                                    Some(args.as_slice())
                                }
                                _ => None,
                            })
                            .collect();

                        if sub_patterns.is_empty() {
                            continue;
                        }

                        // Check each field position for exhaustiveness
                        for (i, field_ty) in variant_info.fields.iter().enumerate() {
                            let field_pats: Vec<&TypedPattern> =
                                sub_patterns.iter().filter_map(|pats| pats.get(i)).collect();

                            check_patterns_exhaustive(field_ty, &field_pats, Some(registry), span)?;
                        }
                    }

                    Ok(())
                }
                TypeKind::Record { .. } => {
                    // Single constructor — any arm matches
                    if patterns.is_empty() {
                        Err(SpannedTypeError {
                            error: TypeError::NonExhaustive {
                                missing: vec![name.clone()],
                            },
                            span,
                            note: None,
                            secondary_span: None,
                        })
                    } else {
                        Ok(())
                    }
                }
            }
        }
        // For primitive types (Int, String, Bool, etc.), require a catch-all
        Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit => {
            // We already checked for catch-all above, so if we're here it's missing
            Err(SpannedTypeError {
                error: TypeError::NonExhaustive {
                    missing: vec!["_".to_string()],
                },
                span,
                note: None,
                secondary_span: None,
            })
        }
        // Type variables, functions, etc. — skip checking
        _ => Ok(()),
    }
}

fn is_catch_all(pattern: &TypedPattern) -> bool {
    matches!(
        pattern,
        TypedPattern::Wildcard { .. } | TypedPattern::Var { .. }
    )
}

fn constructor_name(pattern: &TypedPattern) -> Option<&str> {
    match pattern {
        TypedPattern::Constructor { name, .. } => Some(name.as_str()),
        _ => None,
    }
}
