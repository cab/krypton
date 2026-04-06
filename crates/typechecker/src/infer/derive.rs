use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Lit, Span};

use crate::trait_registry::TraitRegistry;
use crate::type_registry::TypeInfo;
use crate::typed_ast::{
    ResolvedConstraint, TraitName, TypedExpr, TypedExprKind, TypedMatchArm, TypedPattern,
};
use crate::types::{Type, TypeVarId};

use super::match_type_with_bindings;

pub(super) fn collect_derived_constraints_for_type(
    trait_registry: &TraitRegistry,
    trait_name: &str,
    field_type: &Type,
    local_type_params: &HashMap<TypeVarId, String>,
    deriving_type_name: &str,
    visited: &mut HashSet<(String, String)>,
    constraints: &mut Vec<ResolvedConstraint>,
) -> bool {
    let key = (trait_name.to_string(), format!("{field_type}"));
    if !visited.insert(key) {
        return true;
    }

    let Some(trait_info) = trait_registry.lookup_trait_by_name(trait_name) else {
        // The caller checks trait existence before calling this function,
        // so this can only happen on recursive calls for superclass constraints.
        // If a trait isn't in the registry at this point, the import pipeline is broken.
        panic!(
            "ICE: trait `{trait_name}` not found in registry during deriving constraint collection"
        );
    };

    if let Type::Var(type_var) = field_type {
        if let Some(type_var_name) = local_type_params.get(type_var) {
            if !constraints
                .iter()
                .any(|c| c.trait_name.local_name == trait_name && c.type_var == *type_var_name)
            {
                constraints.push(ResolvedConstraint {
                    trait_name: trait_info.trait_name(),
                    type_var: type_var_name.clone(),
                    span: (0, 0),
                });
            }
            return true;
        }
    }

    // Self-referential: the instance we're currently deriving will satisfy this.
    // Just ensure the type arguments satisfy the trait.
    if let Type::Named(name, args) = field_type {
        if name == deriving_type_name {
            for arg in args {
                if !collect_derived_constraints_for_type(
                    trait_registry,
                    trait_name,
                    arg,
                    local_type_params,
                    deriving_type_name,
                    visited,
                    constraints,
                ) {
                    return false;
                }
            }
            return true;
        }
    }

    let full_trait_name = trait_info.trait_name();
    let Some(instance) = trait_registry.find_instance(&full_trait_name, field_type) else {
        return false;
    };

    if instance.constraints.is_empty() {
        return true;
    }

    let mut bindings = HashMap::new();
    if !match_type_with_bindings(&instance.target_types[0], field_type, &mut bindings) {
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
            &constraint.trait_name.local_name,
            required_type,
            local_type_params,
            deriving_type_name,
            visited,
            constraints,
        ) {
            return false;
        }
    }

    true
}

/// Synthesize an `eq` method body for a derived Eq instance.
pub(super) fn synthesize_eq_body(
    type_info: &TypeInfo,
    target_type: &Type,
    span: Span,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
        resolved_ref: None,
        scope_id: None,
    };
    let param_b = TypedExpr {
        kind: TypedExprKind::Var("__b".to_string()),
        ty: target_type.clone(),
        span,
        resolved_ref: None,
        scope_id: None,
    };
    let true_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(true)),
        ty: Type::Bool,
        span,
        resolved_ref: None,
        scope_id: None,
    };
    let false_expr = || TypedExpr {
        kind: TypedExprKind::Lit(Lit::Bool(false)),
        ty: Type::Bool,
        span,
        resolved_ref: None,
        scope_id: None,
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
                            resolved_type_ref: None,
                        },
                        ty: field_ty.clone(),
                        span,
                        resolved_ref: None,
                        scope_id: None,
                    };
                    let rhs = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_b.clone()),
                            field: field_name.clone(),
                            resolved_type_ref: None,
                        },
                        ty: field_ty.clone(),
                        span,
                        resolved_ref: None,
                        scope_id: None,
                    };
                    let cmp = TypedExpr {
                        kind: TypedExprKind::BinaryOp {
                            op: BinOp::Eq,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                        ty: Type::Bool,
                        span,
                        resolved_ref: None,
                        scope_id: None,
                    };
                    result = TypedExpr {
                        kind: TypedExprKind::If {
                            cond: Box::new(cmp),
                            then_: Box::new(result),
                            else_: Box::new(false_expr()),
                        },
                        ty: Type::Bool,
                        span,
                        resolved_ref: None,
                        scope_id: None,
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
                        resolved_variant_ref: None,
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
                                    resolved_variant_ref: None,
                                };
                                // Compare all payload fields
                                if inner_variant.fields.is_empty() {
                                    TypedMatchArm {
                                        pattern: b_pattern,
                                        guard: None,
                                        body: true_expr(),
                                    }
                                } else {
                                    let mut result = true_expr();
                                    for (i, ft) in inner_variant.fields.iter().enumerate().rev() {
                                        let x = TypedExpr {
                                            kind: TypedExprKind::Var(format!("__x{}", i)),
                                            ty: ft.clone(),
                                            span,
                                            resolved_ref: None,
                                            scope_id: None,
                                        };
                                        let y = TypedExpr {
                                            kind: TypedExprKind::Var(format!("__y{}", i)),
                                            ty: ft.clone(),
                                            span,
                                            resolved_ref: None,
                                            scope_id: None,
                                        };
                                        let cmp = TypedExpr {
                                            kind: TypedExprKind::BinaryOp {
                                                op: BinOp::Eq,
                                                lhs: Box::new(x),
                                                rhs: Box::new(y),
                                            },
                                            ty: Type::Bool,
                                            span,
                                            resolved_ref: None,
                                            scope_id: None,
                                        };
                                        result = TypedExpr {
                                            kind: TypedExprKind::If {
                                                cond: Box::new(cmp),
                                                then_: Box::new(result),
                                                else_: Box::new(false_expr()),
                                            },
                                            ty: Type::Bool,
                                            span,
                                            resolved_ref: None,
                                            scope_id: None,
                                        };
                                    }
                                    TypedMatchArm {
                                        pattern: b_pattern,
                                        guard: None,
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
                                    guard: None,
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
                        resolved_ref: None,
                        scope_id: None,
                    };

                    TypedMatchArm {
                        pattern: a_pattern,
                        guard: None,
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
                resolved_ref: None,
                scope_id: None,
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
pub(super) fn synthesize_show_body(
    type_info: &TypeInfo,
    target_type: &Type,
    span: Span,
    trait_id: Option<TraitName>,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
        resolved_ref: None,
        scope_id: None,
    };

    let str_lit = |s: &str| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::Lit(Lit::String(s.to_string())),
            ty: Type::String,
            span,
            resolved_ref: None,
            scope_id: None,
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
            resolved_ref: None,
            scope_id: None,
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
                    resolved_ref: trait_id
                        .clone()
                        .map(|trait_name| super::trait_method_binding_ref(trait_name, "show")),
                    scope_id: None,
                }),
                args: vec![expr],
            },
            ty: Type::String,
            span,
            resolved_ref: None,
            scope_id: None,
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
                        resolved_type_ref: None,
                    },
                    ty: field_ty.clone(),
                    span,
                    resolved_ref: None,
                    scope_id: None,
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
                        resolved_variant_ref: None,
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
                                resolved_ref: None,
                                scope_id: None,
                            };
                            result = str_concat(result, show_call(var_expr));
                        }
                        str_concat(result, str_lit(")"))
                    };

                    TypedMatchArm { pattern, guard: None, body }
                })
                .collect();

            TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(param_a),
                    arms,
                },
                ty: Type::String,
                span,
                resolved_ref: None,
                scope_id: None,
            }
        }
    };

    let fn_ty = Type::Fn(vec![target_type.clone()], Box::new(Type::String));
    (body, fn_ty)
}

pub(super) fn synthesize_hash_body(
    type_info: &TypeInfo,
    target_type: &Type,
    span: Span,
    trait_id: Option<TraitName>,
) -> (TypedExpr, Type) {
    let param_a = TypedExpr {
        kind: TypedExprKind::Var("__a".to_string()),
        ty: target_type.clone(),
        span,
        resolved_ref: None,
        scope_id: None,
    };

    let int_lit = |n: i64| -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::Lit(Lit::Int(n)),
            ty: Type::Int,
            span,
            resolved_ref: None,
            scope_id: None,
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
                    resolved_ref: trait_id
                        .clone()
                        .map(|trait_name| super::trait_method_binding_ref(trait_name, "hash")),
                    scope_id: None,
                }),
                args: vec![expr],
            },
            ty: Type::Int,
            span,
            resolved_ref: None,
            scope_id: None,
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
            resolved_ref: None,
            scope_id: None,
        };
        TypedExpr {
            kind: TypedExprKind::BinaryOp {
                op: BinOp::Add,
                lhs: Box::new(mul),
                rhs: Box::new(field_hash),
            },
            ty: Type::Int,
            span,
            resolved_ref: None,
            scope_id: None,
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
                            resolved_type_ref: None,
                        },
                        ty: field_ty.clone(),
                        span,
                        resolved_ref: None,
                        scope_id: None,
                    };
                    hash_call(field_access)
                };
                for (field_name, field_ty) in &fields[1..] {
                    let field_access = TypedExpr {
                        kind: TypedExprKind::FieldAccess {
                            expr: Box::new(param_a.clone()),
                            field: field_name.clone(),
                            resolved_type_ref: None,
                        },
                        ty: field_ty.clone(),
                        span,
                        resolved_ref: None,
                        scope_id: None,
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
                        resolved_variant_ref: None,
                    };

                    let mut result = hash_call(int_lit(idx as i64));
                    for (i, ft) in variant.fields.iter().enumerate() {
                        let var_expr = TypedExpr {
                            kind: TypedExprKind::Var(format!("__x{}", i)),
                            ty: ft.clone(),
                            span,
                            resolved_ref: None,
                            scope_id: None,
                        };
                        result = combine_hash(result, hash_call(var_expr));
                    }

                    TypedMatchArm {
                        pattern,
                        guard: None,
                        body: result,
                    }
                })
                .collect();

            TypedExpr {
                kind: TypedExprKind::Match {
                    scrutinee: Box::new(param_a),
                    arms,
                },
                ty: Type::Int,
                span,
                resolved_ref: None,
                scope_id: None,
            }
        }
    };

    let fn_ty = Type::Fn(vec![target_type.clone()], Box::new(Type::Int));
    (body, fn_ty)
}
