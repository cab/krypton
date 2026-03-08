use std::collections::HashSet;

use krypton_parser::ast::{MatchArm, Pattern, Span};

use crate::type_registry::{TypeKind, TypeRegistry};
use crate::types::Type;
use crate::unify::{SpannedTypeError, TypeError};

pub fn check_exhaustiveness(
    scrutinee_ty: &Type,
    arms: &[MatchArm],
    registry: Option<&TypeRegistry>,
    span: Span,
) -> Result<(), SpannedTypeError> {
    // If any arm has a wildcard/var pattern at top level, it's exhaustive
    for arm in arms {
        if is_catch_all(&arm.pattern) {
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
                    let matched: HashSet<&str> = arms
                        .iter()
                        .filter_map(|arm| constructor_name(&arm.pattern))
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
                        let sub_patterns: Vec<&[Pattern]> = arms
                            .iter()
                            .filter_map(|arm| match &arm.pattern {
                                Pattern::Constructor { name, args, .. }
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
                            let field_arms: Vec<MatchArm> = sub_patterns
                                .iter()
                                .filter_map(|pats| {
                                    pats.get(i).map(|p| MatchArm {
                                        pattern: p.clone(),
                                        guard: None,
                                        body: arms[0].body.clone(), // body doesn't matter
                                        span,
                                    })
                                })
                                .collect();

                            check_exhaustiveness(field_ty, &field_arms, Some(registry), span)?;
                        }
                    }

                    Ok(())
                }
                TypeKind::Record { .. } => {
                    // Single constructor — any arm matches
                    if arms.is_empty() {
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

fn is_catch_all(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Wildcard { .. } | Pattern::Var { .. })
}

fn constructor_name(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Constructor { name, .. } => Some(name.as_str()),
        _ => None,
    }
}
