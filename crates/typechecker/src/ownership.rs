use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, Expr, FnDecl, Module, Span, TypeExpr};

use crate::type_registry::{TypeKind, TypeRegistry};
use crate::types::{Type, TypeScheme};
use crate::unify::{SpannedTypeError, TypeError};

/// Whether a generic parameter requires unlimited (U) qualifier or is polymorphic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParamQualifier {
    /// Used more than once in the body — caller must not pass affine values.
    RequiresU,
    /// Used at most once — accepts both affine and unlimited values.
    Polymorphic,
}

/// Check if a param has an `own` type annotation.
fn is_own_param(param: &krypton_parser::ast::Param) -> bool {
    matches!(&param.ty, Some(TypeExpr::Own { .. }))
}

/// Check if a type contains `Type::Own` anywhere within it.
fn type_contains_own(ty: &Type) -> bool {
    match ty {
        Type::Own(_) => true,
        Type::Fn(params, ret) => params.iter().any(type_contains_own) || type_contains_own(ret),
        Type::Named(_, args) => args.iter().any(type_contains_own),
        Type::Tuple(elems) => elems.iter().any(type_contains_own),
        _ => false,
    }
}

/// Check if a named type has any field that contains `own`.
fn has_own_field(type_name: &str, registry: &TypeRegistry) -> bool {
    if let Some(info) = registry.lookup_type(type_name) {
        match &info.kind {
            TypeKind::Record { fields } => fields.iter().any(|(_, ty)| type_contains_own(ty)),
            TypeKind::Sum { variants } => variants
                .iter()
                .any(|v| v.fields.iter().any(type_contains_own)),
        }
    } else {
        false
    }
}

fn callee_var_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Var { name, .. } => Some(name.as_str()),
        Expr::TypeApp { expr, .. } => callee_var_name(expr),
        _ => None,
    }
}

/// Count the maximum number of uses of `name` along any single execution path.
fn count_max_uses(expr: &Expr, name: &str, bound: &HashSet<String>) -> usize {
    match expr {
        Expr::Var { name: v, .. } => {
            if v == name && !bound.contains(name) {
                1
            } else {
                0
            }
        }

        Expr::App { func, args, .. } => {
            let mut total = count_max_uses(func, name, bound);
            for a in args {
                total += count_max_uses(a, name, bound);
            }
            total
        }
        Expr::TypeApp { expr, .. } => count_max_uses(expr, name, bound),

        Expr::Let {
            name: let_name,
            value,
            body,
            ..
        } => {
            let v = count_max_uses(value, name, bound);
            if let_name == name {
                // Shadowed — body doesn't count
                v
            } else if let Some(body) = body {
                v + count_max_uses(body, name, bound)
            } else {
                v
            }
        }

        Expr::LetPattern { value, body, .. } => {
            let v = count_max_uses(value, name, bound);
            if let Some(body) = body {
                v + count_max_uses(body, name, bound)
            } else {
                v
            }
        }

        Expr::Do { exprs, .. } => exprs.iter().map(|e| count_max_uses(e, name, bound)).sum(),

        Expr::If {
            cond, then_, else_, ..
        } => {
            let c = count_max_uses(cond, name, bound);
            let t = count_max_uses(then_, name, bound);
            let e = count_max_uses(else_, name, bound);
            c + t.max(e)
        }

        Expr::Match {
            scrutinee, arms, ..
        } => {
            let s = count_max_uses(scrutinee, name, bound);
            let max_arm = arms
                .iter()
                .map(|arm| count_max_uses(&arm.body, name, bound))
                .max()
                .unwrap_or(0);
            s + max_arm
        }

        Expr::BinaryOp { lhs, rhs, .. } => {
            count_max_uses(lhs, name, bound) + count_max_uses(rhs, name, bound)
        }

        Expr::UnaryOp { operand, .. } => count_max_uses(operand, name, bound),

        Expr::Lambda { params, body, .. } => {
            let mut inner_bound = bound.clone();
            for p in params {
                inner_bound.insert(p.name.clone());
            }
            if inner_bound.contains(name) {
                0
            } else {
                // Captured — count as at most 1
                let uses = count_max_uses(body, name, &inner_bound);
                if uses > 0 {
                    1
                } else {
                    0
                }
            }
        }

        Expr::FieldAccess { expr, .. } => count_max_uses(expr, name, bound),

        Expr::StructLit { fields, .. } => fields
            .iter()
            .map(|(_, e)| count_max_uses(e, name, bound))
            .sum(),

        Expr::StructUpdate { base, fields, .. } => {
            let b = count_max_uses(base, name, bound);
            let f: usize = fields
                .iter()
                .map(|(_, e)| count_max_uses(e, name, bound))
                .sum();
            b + f
        }

        Expr::Tuple { elements, .. } => elements
            .iter()
            .map(|e| count_max_uses(e, name, bound))
            .sum(),

        Expr::Recur { args, .. } => args.iter().map(|a| count_max_uses(a, name, bound)).sum(),

        Expr::QuestionMark { expr, .. } => count_max_uses(expr, name, bound),

        Expr::List { elements, .. } => elements
            .iter()
            .map(|e| count_max_uses(e, name, bound))
            .sum(),

        Expr::Lit { .. } => 0,
    }
}

/// Compute qualifier requirements for each function's parameters.
///
/// For each function, returns a Vec<ParamQualifier> parallel to its params.
/// A type-variable-typed param that is used >1 time in the body gets `RequiresU`.
fn compute_fn_qualifiers(
    fn_decls: &[&FnDecl],
    fn_types: &[(String, TypeScheme)],
) -> HashMap<String, Vec<(ParamQualifier, String)>> {
    let type_map: HashMap<&str, &TypeScheme> =
        fn_types.iter().map(|(n, s)| (n.as_str(), s)).collect();

    let mut result = HashMap::new();

    for decl in fn_decls {
        let scheme = match type_map.get(decl.name.as_str()) {
            Some(s) => s,
            None => continue,
        };

        let param_types = match &scheme.ty {
            Type::Fn(params, _) => params,
            _ => continue,
        };

        let quantified: HashSet<_> = scheme.vars.iter().copied().collect();
        let mut qualifiers = Vec::new();

        for (i, param_ty) in param_types.iter().enumerate() {
            // Strip Own wrapper to get the inner type
            let inner = match param_ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };

            // Check if the inner type is a quantified type variable
            let is_type_var = matches!(inner, Type::Var(id) if quantified.contains(id));

            let param_name = decl
                .params
                .get(i)
                .map(|p| p.name.clone())
                .unwrap_or_default();
            if is_type_var {
                if let Some(param) = decl.params.get(i) {
                    let bound = HashSet::new();
                    let uses = count_max_uses(&decl.body, &param.name, &bound);
                    if uses > 1 {
                        qualifiers.push((ParamQualifier::RequiresU, param_name));
                    } else {
                        qualifiers.push((ParamQualifier::Polymorphic, param_name));
                    }
                } else {
                    qualifiers.push((ParamQualifier::Polymorphic, param_name));
                }
            } else {
                qualifiers.push((ParamQualifier::Polymorphic, param_name));
            }
        }

        result.insert(decl.name.clone(), qualifiers);
    }

    result
}

/// Build the set of affine params for a function — params that cannot be passed
/// to unlimited-qualifier positions.
fn build_affine_set(decl: &FnDecl, registry: &TypeRegistry) -> HashSet<String> {
    let mut affine = HashSet::new();
    for param in &decl.params {
        if is_own_param(param) {
            affine.insert(param.name.clone());
            continue;
        }
        // Check if the param type annotation refers to a type with own fields
        if let Some(ref ty_expr) = param.ty {
            if param_type_is_affine(ty_expr, registry) {
                affine.insert(param.name.clone());
            }
        }
    }
    affine
}

/// Check if a type expression refers to an affine type (contains own or is a
/// struct/sum with own fields).
fn param_type_is_affine(ty_expr: &TypeExpr, registry: &TypeRegistry) -> bool {
    match ty_expr {
        TypeExpr::Own { .. } => true,
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => has_own_field(name, registry),
        TypeExpr::App { name, .. } => has_own_field(name, registry),
        TypeExpr::Tuple { elements, .. } => {
            elements.iter().any(|e| param_type_is_affine(e, registry))
        }
        TypeExpr::Fn { .. } => false,
    }
}

/// Affine verification: track `own` bindings and flag double-use as E0101,
/// partial-branch use as E0102, and qualifier mismatches as E0104.
pub fn check_ownership(
    module: &Module,
    fn_types: &[(String, TypeScheme)],
    registry: &TypeRegistry,
    let_own_spans: &HashSet<Span>,
    lambda_own_captures: &HashMap<Span, String>,
    struct_update_info: &HashMap<Span, (String, HashSet<String>)>,
) -> Result<(), SpannedTypeError> {
    // Build map: fn_name -> vec of is_own for each param
    let mut fn_param_info: HashMap<String, Vec<bool>> = HashMap::new();
    for decl in &module.decls {
        if let Decl::DefFn(fn_decl) = decl {
            let own_params: Vec<bool> = fn_decl.params.iter().map(is_own_param).collect();
            fn_param_info.insert(fn_decl.name.clone(), own_params);
        }
    }

    // Collect fn decls
    let fn_decls: Vec<&FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Compute qualifier requirements per function
    let fn_qualifiers = compute_fn_qualifiers(&fn_decls, fn_types);

    for decl in &module.decls {
        if let Decl::DefFn(fn_decl) = decl {
            let affine = build_affine_set(fn_decl, registry);
            check_fn(
                fn_decl,
                &fn_param_info,
                &affine,
                &fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                struct_update_info,
                registry,
            )?;
        }
    }
    Ok(())
}

fn check_fn(
    decl: &FnDecl,
    fn_param_info: &HashMap<String, Vec<bool>>,
    affine: &HashSet<String>,
    fn_qualifiers: &HashMap<String, Vec<(ParamQualifier, String)>>,
    let_own_spans: &HashSet<Span>,
    lambda_own_captures: &HashMap<Span, String>,
    struct_update_info: &HashMap<Span, (String, HashSet<String>)>,
    registry: &TypeRegistry,
) -> Result<(), SpannedTypeError> {
    let mut owned: HashSet<String> = decl
        .params
        .iter()
        .filter(|p| is_own_param(p))
        .map(|p| p.name.clone())
        .collect();

    if owned.is_empty() && affine.is_empty() && let_own_spans.is_empty() {
        return Ok(());
    }

    let mut consumed = HashMap::new();
    let mut partially_consumed = HashMap::new();
    let mut own_fn_notes: HashMap<String, String> = HashMap::new();
    check_expr(
        &decl.body,
        &mut owned,
        &mut consumed,
        &mut partially_consumed,
        fn_param_info,
        affine,
        fn_qualifiers,
        let_own_spans,
        lambda_own_captures,
        &mut own_fn_notes,
        struct_update_info,
        registry,
    )
}

fn check_expr(
    expr: &Expr,
    owned: &mut HashSet<String>,
    consumed: &mut HashMap<String, Span>,
    partially_consumed: &mut HashMap<String, Span>,
    fn_param_info: &HashMap<String, Vec<bool>>,
    affine: &HashSet<String>,
    fn_qualifiers: &HashMap<String, Vec<(ParamQualifier, String)>>,
    let_own_spans: &HashSet<Span>,
    lambda_own_captures: &HashMap<Span, String>,
    own_fn_notes: &mut HashMap<String, String>,
    struct_update_info: &HashMap<Span, (String, HashSet<String>)>,
    registry: &TypeRegistry,
) -> Result<(), SpannedTypeError> {
    match expr {
        Expr::Var { name, span, .. } => {
            if owned.contains(name) {
                if let Some(&first_span) = consumed.get(name) {
                    return Err(SpannedTypeError {
                        error: TypeError::AlreadyMoved { name: name.clone() },
                        span: *span,
                        note: own_fn_notes.get(name).cloned(),
                        secondary_span: Some((first_span, "first use here".into())),
                    });
                }
                if let Some(&branch_span) = partially_consumed.get(name) {
                    return Err(SpannedTypeError {
                        error: TypeError::MovedInBranch { name: name.clone() },
                        span: *span,
                        note: None,
                        secondary_span: Some((branch_span, "consumed here".into())),
                    });
                }
                consumed.insert(name.clone(), *span);
            }
            Ok(())
        }

        Expr::App {
            func, args, span, ..
        } => {
            check_expr(
                func,
                owned,
                consumed,
                partially_consumed,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;
            // Determine which params are non-own (for non-consuming borrow)
            let callee_params = callee_var_name(func).and_then(|name| fn_param_info.get(name));
            // Get qualifier requirements for the callee
            let callee_qualifiers = callee_var_name(func).and_then(|name| fn_qualifiers.get(name));
            for (i, arg) in args.iter().enumerate() {
                // Check qualifier mismatch: affine arg passed to RequiresU param
                if let Expr::Var {
                    name: arg_name,
                    span: arg_span,
                    ..
                } = arg
                {
                    if affine.contains(arg_name) {
                        if let Some(quals) = callee_qualifiers {
                            if let Some((ParamQualifier::RequiresU, param_name)) = quals.get(i) {
                                let callee_name =
                                    callee_var_name(func).unwrap_or("<anonymous>").to_string();
                                return Err(SpannedTypeError {
                                    error: TypeError::QualifierMismatch {
                                        name: arg_name.clone(),
                                        callee: callee_name,
                                        param: param_name.clone(),
                                    },
                                    span: *arg_span,
                                    note: None,
                                    secondary_span: None,
                                });
                            }
                        }
                    }
                }

                let is_non_consuming_borrow = if let Expr::Var { name: arg_name, .. } = arg {
                    owned.contains(arg_name)
                        && callee_params.is_some_and(|params| i < params.len() && !params[i])
                } else {
                    false
                };
                if is_non_consuming_borrow {
                    // Non-consuming borrow: check prior consumption but don't mark consumed
                    if let Expr::Var { name, span, .. } = arg {
                        if let Some(&first_span) = consumed.get(name) {
                            return Err(SpannedTypeError {
                                error: TypeError::AlreadyMoved { name: name.clone() },
                                span: *span,
                                note: None,
                                secondary_span: Some((first_span, "first use here".into())),
                            });
                        }
                        if let Some(&branch_span) = partially_consumed.get(name) {
                            return Err(SpannedTypeError {
                                error: TypeError::MovedInBranch { name: name.clone() },
                                span: *span,
                                note: None,
                                secondary_span: Some((branch_span, "consumed here".into())),
                            });
                        }
                    }
                } else {
                    check_expr(
                        arg,
                        owned,
                        consumed,
                        partially_consumed,
                        fn_param_info,
                        affine,
                        fn_qualifiers,
                        let_own_spans,
                        lambda_own_captures,
                        own_fn_notes,
                        struct_update_info,
                        registry,
                    )?;
                }
            }
            let _ = span;
            Ok(())
        }
        Expr::TypeApp { expr, .. } => check_expr(
            expr,
            owned,
            consumed,
            partially_consumed,
            fn_param_info,
            affine,
            fn_qualifiers,
            let_own_spans,
            lambda_own_captures,
            own_fn_notes,
            struct_update_info,
            registry,
        ),

        Expr::Let {
            name,
            value,
            body,
            span,
            ..
        } => {
            check_expr(
                value,
                owned,
                consumed,
                partially_consumed,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;
            let is_own_let = let_own_spans.contains(span);
            if is_own_let {
                owned.insert(name.clone());
                // Record note for own fn closures
                if let Expr::Lambda { span: lspan, .. } = value.as_ref() {
                    if let Some(cap_name) = lambda_own_captures.get(lspan) {
                        own_fn_notes.insert(
                            name.clone(),
                            format!(
                                "closure is single-use because it captures own value `{}`",
                                cap_name
                            ),
                        );
                    }
                }
            }
            if let Some(body) = body {
                check_expr(
                    body,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
                // Restore owned state after body scope
                if is_own_let {
                    owned.remove(name);
                    consumed.remove(name);
                    partially_consumed.remove(name);
                }
            }
            Ok(())
        }

        Expr::LetPattern { value, body, .. } => {
            check_expr(
                value,
                owned,
                consumed,
                partially_consumed,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;
            if let Some(body) = body {
                check_expr(
                    body,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            }
            Ok(())
        }

        Expr::Do { exprs, .. } => {
            for e in exprs {
                check_expr(
                    e,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            }
            Ok(())
        }

        Expr::If {
            cond, then_, else_, ..
        } => {
            check_expr(
                cond,
                owned,
                consumed,
                partially_consumed,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;
            let before: HashSet<String> = consumed.keys().cloned().collect();
            let mut then_consumed = consumed.clone();
            let mut then_partial = partially_consumed.clone();
            let mut else_consumed = consumed.clone();
            let mut else_partial = partially_consumed.clone();
            check_expr(
                then_,
                owned,
                &mut then_consumed,
                &mut then_partial,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;
            check_expr(
                else_,
                owned,
                &mut else_consumed,
                &mut else_partial,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;

            let then_keys: HashSet<String> = then_consumed.keys().cloned().collect();
            let else_keys: HashSet<String> = else_consumed.keys().cloned().collect();
            let newly_in_then: HashSet<String> = then_keys.difference(&before).cloned().collect();
            let newly_in_else: HashSet<String> = else_keys.difference(&before).cloned().collect();
            let in_all: HashSet<String> = newly_in_then
                .intersection(&newly_in_else)
                .cloned()
                .collect();
            let in_some: HashSet<String> = newly_in_then
                .symmetric_difference(&newly_in_else)
                .cloned()
                .collect();

            for name in &in_all {
                // Pick span from either branch
                if let Some(&span) = then_consumed.get(name) {
                    consumed.insert(name.clone(), span);
                }
            }
            for name in &in_some {
                let span = then_consumed
                    .get(name)
                    .or_else(|| else_consumed.get(name))
                    .copied()
                    .unwrap();
                partially_consumed.insert(name.clone(), span);
            }
            // Merge partial sets from branches
            for (name, span) in then_partial.iter().chain(else_partial.iter()) {
                partially_consumed.entry(name.clone()).or_insert(*span);
            }
            Ok(())
        }

        Expr::Match {
            scrutinee, arms, ..
        } => {
            check_expr(
                scrutinee,
                owned,
                consumed,
                partially_consumed,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;
            let before: HashSet<String> = consumed.keys().cloned().collect();
            let n = arms.len();
            let mut per_arm_new: Vec<HashMap<String, Span>> = Vec::new();
            let mut merged_partial = partially_consumed.clone();

            for arm in arms {
                let mut arm_consumed = consumed.clone();
                let mut arm_partial = partially_consumed.clone();
                check_expr(
                    &arm.body,
                    owned,
                    &mut arm_consumed,
                    &mut arm_partial,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
                let newly: HashMap<String, Span> = arm_consumed
                    .into_iter()
                    .filter(|(k, _)| !before.contains(k))
                    .collect();
                per_arm_new.push(newly);
                for (name, span) in &arm_partial {
                    merged_partial.entry(name.clone()).or_insert(*span);
                }
            }

            // Count how many arms consumed each name
            let all_names: HashSet<String> =
                per_arm_new.iter().flat_map(|s| s.keys().cloned()).collect();
            for name in &all_names {
                let count = per_arm_new.iter().filter(|s| s.contains_key(name)).count();
                if count == n {
                    // Pick span from first arm that has it
                    if let Some(span) = per_arm_new.iter().find_map(|s| s.get(name)).copied() {
                        consumed.insert(name.clone(), span);
                    }
                } else {
                    let span = per_arm_new
                        .iter()
                        .find_map(|s| s.get(name))
                        .copied()
                        .unwrap();
                    merged_partial.insert(name.clone(), span);
                }
            }
            *partially_consumed = merged_partial;
            Ok(())
        }

        Expr::BinaryOp { lhs, rhs, .. } => {
            check_expr(
                lhs,
                owned,
                consumed,
                partially_consumed,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )?;
            check_expr(
                rhs,
                owned,
                consumed,
                partially_consumed,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )
        }

        Expr::UnaryOp { operand, .. } => check_expr(
            operand,
            owned,
            consumed,
            partially_consumed,
            fn_param_info,
            affine,
            fn_qualifiers,
            let_own_spans,
            lambda_own_captures,
            own_fn_notes,
            struct_update_info,
            registry,
        ),

        Expr::Lambda {
            params, body, span, ..
        } => {
            let lambda_params: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
            let captured = free_owned_vars(body, owned, &lambda_params);
            for name in &captured {
                if let Some(&first_span) =
                    consumed.get(name).or_else(|| partially_consumed.get(name))
                {
                    return Err(SpannedTypeError {
                        error: TypeError::CapturedMoved { name: name.clone() },
                        span: *span,
                        note: None,
                        secondary_span: Some((first_span, "consumed here".into())),
                    });
                }
                consumed.insert(name.clone(), *span);
            }
            let mut body_consumed = HashMap::new();
            let mut body_partial = HashMap::new();
            check_expr(
                body,
                owned,
                &mut body_consumed,
                &mut body_partial,
                fn_param_info,
                affine,
                fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                own_fn_notes,
                struct_update_info,
                registry,
            )
        }

        Expr::FieldAccess { expr, .. } => check_expr(
            expr,
            owned,
            consumed,
            partially_consumed,
            fn_param_info,
            affine,
            fn_qualifiers,
            let_own_spans,
            lambda_own_captures,
            own_fn_notes,
            struct_update_info,
            registry,
        ),

        Expr::StructLit { fields, .. } => {
            for (_, field_expr) in fields {
                check_expr(
                    field_expr,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            }
            Ok(())
        }

        Expr::StructUpdate { base, fields, span } => {
            // Check field value exprs first (these may consume owned vars)
            for (_, field_expr) in fields {
                check_expr(
                    field_expr,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            }

            // Determine if base is consumed: only consumed if struct has own fields
            // that are NOT replaced by this update
            let base_consumed =
                if let Some((type_name, updated_fields)) = struct_update_info.get(span) {
                    if let Some(info) = registry.lookup_type(type_name) {
                        if let TypeKind::Record {
                            fields: record_fields,
                        } = &info.kind
                        {
                            record_fields.iter().any(|(fname, fty)| {
                                type_contains_own(fty) && !updated_fields.contains(fname)
                            })
                        } else {
                            true
                        }
                    } else {
                        true
                    }
                } else {
                    true
                };

            if base_consumed {
                check_expr(
                    base,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            } else {
                // Non-consuming: check base isn't already consumed but don't mark it
                if let Expr::Var { name, span, .. } = base.as_ref() {
                    if owned.contains(name) {
                        if let Some(&first_span) = consumed.get(name) {
                            return Err(SpannedTypeError {
                                error: TypeError::AlreadyMoved { name: name.clone() },
                                span: *span,
                                note: None,
                                secondary_span: Some((first_span, "first use here".into())),
                            });
                        }
                        if let Some(&branch_span) = partially_consumed.get(name) {
                            return Err(SpannedTypeError {
                                error: TypeError::MovedInBranch { name: name.clone() },
                                span: *span,
                                note: None,
                                secondary_span: Some((branch_span, "consumed here".into())),
                            });
                        }
                    }
                } else {
                    check_expr(
                        base,
                        owned,
                        consumed,
                        partially_consumed,
                        fn_param_info,
                        affine,
                        fn_qualifiers,
                        let_own_spans,
                        lambda_own_captures,
                        own_fn_notes,
                        struct_update_info,
                        registry,
                    )?;
                }
            }
            Ok(())
        }

        Expr::Tuple { elements, .. } => {
            for e in elements {
                check_expr(
                    e,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            }
            Ok(())
        }

        Expr::Recur { args, .. } => {
            for a in args {
                check_expr(
                    a,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            }
            Ok(())
        }

        Expr::QuestionMark { expr, .. } => check_expr(
            expr,
            owned,
            consumed,
            partially_consumed,
            fn_param_info,
            affine,
            fn_qualifiers,
            let_own_spans,
            lambda_own_captures,
            own_fn_notes,
            struct_update_info,
            registry,
        ),

        Expr::List { elements, .. } => {
            for e in elements {
                check_expr(
                    e,
                    owned,
                    consumed,
                    partially_consumed,
                    fn_param_info,
                    affine,
                    fn_qualifiers,
                    let_own_spans,
                    lambda_own_captures,
                    own_fn_notes,
                    struct_update_info,
                    registry,
                )?;
            }
            Ok(())
        }

        // Lit — no owned vars to consume
        Expr::Lit { .. } => Ok(()),
    }
}

/// Collect free variables in an expression that are in the `owned` set,
/// excluding those in `bound` (lambda params or let-bound names).
fn free_owned_vars(
    expr: &Expr,
    owned: &HashSet<String>,
    bound: &HashSet<String>,
) -> HashSet<String> {
    let mut result = HashSet::new();
    collect_free_owned(expr, owned, bound, &mut result);
    result
}

fn collect_free_owned(
    expr: &Expr,
    owned: &HashSet<String>,
    bound: &HashSet<String>,
    acc: &mut HashSet<String>,
) {
    match expr {
        Expr::Var { name, .. } => {
            if owned.contains(name) && !bound.contains(name) {
                acc.insert(name.clone());
            }
        }
        Expr::App { func, args, .. } => {
            collect_free_owned(func, owned, bound, acc);
            for a in args {
                collect_free_owned(a, owned, bound, acc);
            }
        }
        Expr::TypeApp { expr, .. } => collect_free_owned(expr, owned, bound, acc),
        Expr::Let {
            name, value, body, ..
        } => {
            collect_free_owned(value, owned, bound, acc);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                collect_free_owned(body, owned, &inner_bound, acc);
            }
        }
        Expr::LetPattern { value, body, .. } => {
            collect_free_owned(value, owned, bound, acc);
            if let Some(body) = body {
                collect_free_owned(body, owned, bound, acc);
            }
        }
        Expr::Do { exprs, .. } => {
            for e in exprs {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        Expr::If {
            cond, then_, else_, ..
        } => {
            collect_free_owned(cond, owned, bound, acc);
            collect_free_owned(then_, owned, bound, acc);
            collect_free_owned(else_, owned, bound, acc);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_free_owned(scrutinee, owned, bound, acc);
            for arm in arms {
                collect_free_owned(&arm.body, owned, bound, acc);
            }
        }
        Expr::BinaryOp { lhs, rhs, .. } => {
            collect_free_owned(lhs, owned, bound, acc);
            collect_free_owned(rhs, owned, bound, acc);
        }
        Expr::UnaryOp { operand, .. } => {
            collect_free_owned(operand, owned, bound, acc);
        }
        Expr::Lambda { params, body, .. } => {
            let mut inner_bound = bound.clone();
            for p in params {
                inner_bound.insert(p.name.clone());
            }
            collect_free_owned(body, owned, &inner_bound, acc);
        }
        Expr::FieldAccess { expr, .. } => {
            collect_free_owned(expr, owned, bound, acc);
        }
        Expr::StructLit { fields, .. } => {
            for (_, e) in fields {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        Expr::StructUpdate { base, fields, .. } => {
            collect_free_owned(base, owned, bound, acc);
            for (_, e) in fields {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        Expr::Tuple { elements, .. } => {
            for e in elements {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        Expr::Recur { args, .. } => {
            for a in args {
                collect_free_owned(a, owned, bound, acc);
            }
        }
        Expr::QuestionMark { expr, .. } => {
            collect_free_owned(expr, owned, bound, acc);
        }
        Expr::List { elements, .. } => {
            for e in elements {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        Expr::Lit { .. } => {}
    }
}
