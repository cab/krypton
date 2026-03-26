use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, Expr, FnDecl, Module, Span, TypeExpr};

use crate::type_registry::{TypeKind, TypeRegistry};
use crate::typed_ast::{ParamQualifier, TypedExpr, TypedExprKind, TypedFnDecl, TypedPattern};
use crate::types::{Type, TypeScheme, TypeVarId};
use crate::unify::{SecondaryLabel, SpannedTypeError, TypeError};

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

/// Check if a resolved type is affine (contains own or is a struct/sum with own fields).
fn type_is_affine(ty: &Type, registry: &TypeRegistry) -> bool {
    match ty {
        Type::Own(_) => true,
        Type::Named(name, args) => {
            has_own_field(name, registry) || args.iter().any(|a| type_is_affine(a, registry))
        }
        Type::App(ctor, args) => {
            type_is_affine(ctor, registry) || args.iter().any(|a| type_is_affine(a, registry))
        }
        Type::Tuple(elems) => elems.iter().any(|e| type_is_affine(e, registry)),
        Type::Fn(_, _) => false,
        _ => false,
    }
}

// ── Surface-AST helpers (used only by compute_fn_qualifiers) ───────────────

/// Check if a param has an `own` type annotation.
fn is_own_param(param: &krypton_parser::ast::Param) -> bool {
    matches!(&param.ty, Some(TypeExpr::Own { .. }))
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

/// Recursively collect quantified type variable IDs from a type.
fn collect_quantified_vars(ty: &Type, quantified: &HashSet<TypeVarId>) -> HashSet<TypeVarId> {
    let mut vars = HashSet::new();
    match ty {
        Type::Var(id) if quantified.contains(id) => {
            vars.insert(*id);
        }
        Type::App(ctor, args) => {
            vars.extend(collect_quantified_vars(ctor, quantified));
            for arg in args {
                vars.extend(collect_quantified_vars(arg, quantified));
            }
        }
        Type::Named(_, args) => {
            for arg in args {
                vars.extend(collect_quantified_vars(arg, quantified));
            }
        }
        Type::Own(inner) => {
            vars.extend(collect_quantified_vars(inner, quantified));
        }
        Type::Fn(params, ret) => {
            for p in params {
                vars.extend(collect_quantified_vars(p, quantified));
            }
            vars.extend(collect_quantified_vars(ret, quantified));
        }
        Type::Tuple(elems) => {
            for e in elems {
                vars.extend(collect_quantified_vars(e, quantified));
            }
        }
        _ => {}
    }
    vars
}

/// Compute qualifier requirements for each function's parameters.
/// Stays on surface AST because it needs FnDecl.type_params.
fn compute_fn_qualifiers(
    fn_decls: &[&FnDecl],
    fn_types: &[(String, TypeScheme, Option<crate::typed_ast::TraitName>)],
    shared_type_vars: &HashMap<String, HashSet<String>>,
) -> HashMap<String, Vec<(ParamQualifier, String)>> {
    let type_map: HashMap<&str, &TypeScheme> =
        fn_types.iter().map(|(n, s, _)| (n.as_str(), s)).collect();

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

        let var_id_to_name: HashMap<_, _> = decl
            .type_params
            .iter()
            .zip(scheme.vars.iter())
            .map(|(tp, &id)| (id, tp.name.clone()))
            .collect();

        let fn_shared = shared_type_vars.get(&decl.name);

        let mut qualifiers = Vec::new();

        for (i, param_ty) in param_types.iter().enumerate() {
            let inner = match param_ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };

            let param_name = decl
                .params
                .get(i)
                .map(|p| p.name.clone())
                .unwrap_or_default();

            let found_vars = collect_quantified_vars(inner, &quantified);

            if !found_vars.is_empty() {
                let is_shared = found_vars.iter().any(|id| {
                    fn_shared.is_some_and(|shared_set| {
                        var_id_to_name
                            .get(id)
                            .is_some_and(|name| shared_set.contains(name))
                    })
                });

                if is_shared {
                    qualifiers.push((ParamQualifier::Shared, param_name));
                } else if let Some(param) = decl.params.get(i) {
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

// ── Typed-AST helpers (used by the ownership checker) ──────────────────────

fn callee_var_name(expr: &TypedExpr) -> Option<&str> {
    match &expr.kind {
        TypedExprKind::Var(name) => Some(name.as_str()),
        TypedExprKind::TypeApp { expr, .. } => callee_var_name(expr),
        _ => None,
    }
}

/// Collect owned variable names from a typed pattern (vars where ty is Own).
fn collect_owned_pattern_vars(pattern: &TypedPattern) -> Vec<String> {
    let mut out = Vec::new();
    collect_owned_pattern_vars_inner(pattern, &mut out);
    out
}

fn collect_owned_pattern_vars_inner(pattern: &TypedPattern, out: &mut Vec<String>) {
    match pattern {
        TypedPattern::Var { name, ty, .. } => {
            if matches!(ty, Type::Own(_)) {
                out.push(name.clone());
            }
        }
        TypedPattern::Constructor { args, .. } => {
            for arg in args {
                collect_owned_pattern_vars_inner(arg, out);
            }
        }
        TypedPattern::Tuple { elements, .. } => {
            for elem in elements {
                collect_owned_pattern_vars_inner(elem, out);
            }
        }
        TypedPattern::StructPat { fields, .. } => {
            for (_, pat) in fields {
                collect_owned_pattern_vars_inner(pat, out);
            }
        }
        TypedPattern::Wildcard { .. } | TypedPattern::Lit { .. } => {}
    }
}

/// Collect ALL variable names from a typed pattern (for scoping).
fn collect_pattern_var_names(pattern: &TypedPattern) -> Vec<String> {
    let mut out = Vec::new();
    collect_pattern_var_names_inner(pattern, &mut out);
    out
}

fn collect_pattern_var_names_inner(pattern: &TypedPattern, out: &mut Vec<String>) {
    match pattern {
        TypedPattern::Var { name, .. } => out.push(name.clone()),
        TypedPattern::Constructor { args, .. } => {
            for arg in args {
                collect_pattern_var_names_inner(arg, out);
            }
        }
        TypedPattern::Tuple { elements, .. } => {
            for elem in elements {
                collect_pattern_var_names_inner(elem, out);
            }
        }
        TypedPattern::StructPat { fields, .. } => {
            for (_, pat) in fields {
                collect_pattern_var_names_inner(pat, out);
            }
        }
        TypedPattern::Wildcard { .. } | TypedPattern::Lit { .. } => {}
    }
}

/// Collect free variables in a typed expression that are in the `owned` set.
fn free_owned_vars(
    expr: &TypedExpr,
    owned: &HashSet<String>,
    bound: &HashSet<String>,
) -> HashSet<String> {
    let mut result = HashSet::new();
    collect_free_owned(expr, owned, bound, &mut result);
    result
}

fn collect_free_owned(
    expr: &TypedExpr,
    owned: &HashSet<String>,
    bound: &HashSet<String>,
    acc: &mut HashSet<String>,
) {
    match &expr.kind {
        TypedExprKind::Var(name) => {
            if owned.contains(name) && !bound.contains(name) {
                acc.insert(name.clone());
            }
        }
        TypedExprKind::App { func, args } => {
            collect_free_owned(func, owned, bound, acc);
            for a in args {
                collect_free_owned(a, owned, bound, acc);
            }
        }
        TypedExprKind::TypeApp { expr, .. } => collect_free_owned(expr, owned, bound, acc),
        TypedExprKind::Let { name, value, body } => {
            collect_free_owned(value, owned, bound, acc);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                collect_free_owned(body, owned, &inner_bound, acc);
            }
        }
        TypedExprKind::LetPattern {
            pattern,
            value,
            body,
        } => {
            collect_free_owned(value, owned, bound, acc);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                for name in collect_pattern_var_names(pattern) {
                    inner_bound.insert(name);
                }
                collect_free_owned(body, owned, &inner_bound, acc);
            }
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        TypedExprKind::If { cond, then_, else_ } => {
            collect_free_owned(cond, owned, bound, acc);
            collect_free_owned(then_, owned, bound, acc);
            collect_free_owned(else_, owned, bound, acc);
        }
        TypedExprKind::Match { scrutinee, arms } => {
            collect_free_owned(scrutinee, owned, bound, acc);
            for arm in arms {
                let mut inner_bound = bound.clone();
                for name in collect_pattern_var_names(&arm.pattern) {
                    inner_bound.insert(name);
                }
                collect_free_owned(&arm.body, owned, &inner_bound, acc);
            }
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            collect_free_owned(lhs, owned, bound, acc);
            collect_free_owned(rhs, owned, bound, acc);
        }
        TypedExprKind::UnaryOp { operand, .. } => {
            collect_free_owned(operand, owned, bound, acc);
        }
        TypedExprKind::Lambda { params, body } => {
            let mut inner_bound = bound.clone();
            for p in params {
                inner_bound.insert(p.clone());
            }
            collect_free_owned(body, owned, &inner_bound, acc);
        }
        TypedExprKind::FieldAccess { expr, .. } => {
            collect_free_owned(expr, owned, bound, acc);
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        TypedExprKind::StructUpdate { base, fields } => {
            collect_free_owned(base, owned, bound, acc);
            for (_, e) in fields {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        TypedExprKind::Tuple(elements)
        | TypedExprKind::Recur(elements)
        | TypedExprKind::VecLit(elements) => {
            for e in elements {
                collect_free_owned(e, owned, bound, acc);
            }
        }
        TypedExprKind::QuestionMark { expr, .. } => {
            collect_free_owned(expr, owned, bound, acc);
        }
        TypedExprKind::Lit(_) => {}
    }
}

// ── Ownership checker ──────────────────────────────────────────────────────

/// Result of ownership checking: qualifier info plus actual move locations.
pub struct OwnershipResult {
    pub fn_qualifiers: HashMap<String, Vec<(ParamQualifier, String)>>,
    /// Every actual move: var_span → var_name.
    pub moves: HashMap<Span, String>,
}

/// Affine verification: track `own` bindings and flag double-use as E0101,
/// partial-branch use as E0102, and qualifier mismatches as E0104.
pub fn check_ownership(
    module: &Module,
    typed_fns: &[TypedFnDecl],
    fn_types: &[(String, TypeScheme, Option<crate::typed_ast::TraitName>)],
    registry: &TypeRegistry,
    let_own_spans: &HashSet<Span>,
    lambda_own_captures: &HashMap<Span, String>,
    shared_type_vars: &HashMap<String, HashSet<String>>,
    imported_fn_qualifiers: &HashMap<String, Vec<(ParamQualifier, String)>>,
) -> Result<OwnershipResult, SpannedTypeError> {
    // Build map: fn_name -> vec of is_own for each param
    let mut fn_param_info: HashMap<String, Vec<bool>> = HashMap::new();
    for decl in &module.decls {
        if let Decl::DefFn(fn_decl) = decl {
            let own_params: Vec<bool> = fn_decl.params.iter().map(is_own_param).collect();
            fn_param_info.insert(fn_decl.name.clone(), own_params);
        }
    }
    // Also populate fn_param_info for imported functions from their TypeScheme
    for (name, scheme, _) in fn_types {
        if fn_param_info.contains_key(name) {
            continue;
        }
        if let Type::Fn(params, _) = &scheme.ty {
            let own_params: Vec<bool> = params.iter().map(|t| matches!(t, Type::Own(_))).collect();
            fn_param_info.insert(name.clone(), own_params);
        }
    }

    // Collect surface fn decls (needed for compute_fn_qualifiers)
    let fn_decls: Vec<&FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Build map: fn_name -> param types from type scheme
    let mut fn_scheme_params: HashMap<String, Vec<Type>> = HashMap::new();
    for (name, scheme, _) in fn_types {
        if let Type::Fn(params, _) = &scheme.ty {
            fn_scheme_params.insert(name.clone(), params.clone());
        }
    }

    // Compute qualifier requirements per function (stays on surface AST)
    let mut fn_qualifiers = compute_fn_qualifiers(&fn_decls, fn_types, shared_type_vars);
    for (name, quals) in imported_fn_qualifiers {
        fn_qualifiers
            .entry(name.clone())
            .or_insert_with(|| quals.clone());
    }

    let mut all_moves: HashMap<Span, String> = HashMap::new();

    for typed_fn in typed_fns {
        let fn_moves = check_fn(
            typed_fn,
            &fn_param_info,
            &fn_qualifiers,
            let_own_spans,
            lambda_own_captures,
            registry,
            &fn_scheme_params,
        )?;
        all_moves.extend(fn_moves);
    }
    Ok(OwnershipResult {
        fn_qualifiers,
        moves: all_moves,
    })
}

/// Walks a typed function body tracking affine (single-use) bindings.
///
/// Two parallel maps track call-site requirements:
/// - `fn_param_info`: syntactic — does a parameter carry the `~` qualifier?
/// - `fn_qualifiers`: semantic — computed by `compute_fn_qualifiers` from use-count
///   analysis on the surface AST (which preserves type parameter names needed for
///   the `shared` constraint check). A param is `Unlimited` if it may be called
///   multiple times with the same argument.
///
/// `owned` is the live set of bindings subject to move tracking (grows via let-binding).
/// `affine` is the frozen set of params with affine type (used for qualifier mismatch errors).
struct OwnershipChecker<'a> {
    owned: &'a mut HashSet<String>,
    consumed: HashMap<String, Span>,
    partially_consumed: HashMap<String, Span>,
    moves: HashMap<Span, String>,
    fn_param_info: &'a HashMap<String, Vec<bool>>,
    affine: &'a HashSet<String>,
    fn_qualifiers: &'a HashMap<String, Vec<(ParamQualifier, String)>>,
    let_own_spans: &'a HashSet<Span>,
    lambda_own_captures: &'a HashMap<Span, String>,
    own_fn_notes: &'a mut HashMap<String, String>,
    registry: &'a TypeRegistry,
}

impl<'a> OwnershipChecker<'a> {
    /// Does this expression intrinsically produce an owned value?
    fn is_owned_expr(&self, expr: &TypedExpr) -> bool {
        match &expr.kind {
            TypedExprKind::Lit(_) => true,
            TypedExprKind::Var(name) => {
                self.owned.contains(name) || self.registry.is_constructor(name)
            }
            TypedExprKind::StructLit { .. }
            | TypedExprKind::StructUpdate { .. }
            | TypedExprKind::Tuple(_)
            | TypedExprKind::VecLit(_) => true,
            TypedExprKind::App { func, .. } => {
                if let Some(name) = callee_var_name(func) {
                    self.registry.is_constructor(name)
                } else {
                    false
                }
            }
            TypedExprKind::Lambda { .. } => true,
            TypedExprKind::If { then_, else_, .. } => {
                self.is_owned_expr(then_) && self.is_owned_expr(else_)
            }
            TypedExprKind::Match { arms, .. } => {
                !arms.is_empty() && arms.iter().all(|arm| self.is_owned_expr(&arm.body))
            }
            TypedExprKind::Do(exprs) => exprs.last().is_some_and(|last| self.is_owned_expr(last)),
            TypedExprKind::Let { body, .. } | TypedExprKind::LetPattern { body, .. } => {
                body.as_ref().is_some_and(|b| self.is_owned_expr(b))
            }
            _ => false,
        }
    }

    fn check_not_consumed(
        &self,
        name: &str,
        span: Span,
        note: Option<String>,
    ) -> Result<(), SpannedTypeError> {
        if let Some(&first_span) = self.consumed.get(name) {
            return Err(SpannedTypeError {
                error: TypeError::AlreadyMoved {
                    name: name.to_string(),
                },
                span,
                note,
                secondary_span: Some(SecondaryLabel {
                    span: first_span,
                    message: "first use here".into(),
                    source_file: None,
                }),
                source_file: None,
                var_names: None,
            });
        }
        if let Some(&branch_span) = self.partially_consumed.get(name) {
            return Err(SpannedTypeError {
                error: TypeError::MovedInBranch {
                    name: name.to_string(),
                },
                span,
                note: None,
                secondary_span: Some(SecondaryLabel {
                    span: branch_span,
                    message: "consumed here".into(),
                    source_file: None,
                }),
                source_file: None,
                var_names: None,
            });
        }
        Ok(())
    }

    fn check_exprs(&mut self, exprs: &[TypedExpr]) -> Result<(), SpannedTypeError> {
        for e in exprs {
            self.check_expr(e)?;
        }
        Ok(())
    }

    fn check_branch(
        &mut self,
        expr: &TypedExpr,
    ) -> Result<(HashMap<String, Span>, HashMap<String, Span>), SpannedTypeError> {
        let saved_consumed = self.consumed.clone();
        let saved_partial = self.partially_consumed.clone();
        self.check_expr(expr)?;
        let branch_consumed = std::mem::replace(&mut self.consumed, saved_consumed);
        let branch_partial = std::mem::replace(&mut self.partially_consumed, saved_partial);
        Ok((branch_consumed, branch_partial))
    }

    fn check_expr(&mut self, expr: &TypedExpr) -> Result<(), SpannedTypeError> {
        match &expr.kind {
            TypedExprKind::Var(name) => {
                if self.owned.contains(name) {
                    self.check_not_consumed(name, expr.span, self.own_fn_notes.get(name).cloned())?;
                    self.consumed.insert(name.clone(), expr.span);
                    self.moves.insert(expr.span, name.clone());
                }
                Ok(())
            }

            TypedExprKind::App { func, args } => {
                self.check_expr(func)?;
                let callee_params =
                    callee_var_name(func).and_then(|name| self.fn_param_info.get(name));
                let callee_qualifiers =
                    callee_var_name(func).and_then(|name| self.fn_qualifiers.get(name));
                for (i, arg) in args.iter().enumerate() {
                    // Check qualifier mismatch: affine Var arg passed to RequiresU param
                    if let TypedExprKind::Var(arg_name) = &arg.kind {
                        if self.affine.contains(arg_name) {
                            if let Some(quals) = callee_qualifiers {
                                if let Some((qualifier, param_name)) = quals.get(i) {
                                    if matches!(qualifier, ParamQualifier::RequiresU) {
                                        let callee_name = callee_var_name(func)
                                            .unwrap_or("<anonymous>")
                                            .to_string();
                                        return Err(SpannedTypeError {
                                            error: TypeError::QualifierMismatch {
                                                name: arg_name.clone(),
                                                callee: callee_name,
                                                param: param_name.clone(),
                                            },
                                            span: arg.span,
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

                    // Check qualifier mismatch for non-Var affine arguments
                    if !matches!(&arg.kind, TypedExprKind::Var(_)) {
                        let is_affine_arg = match &arg.kind {
                            TypedExprKind::Lambda { .. } => {
                                // Lambda is affine if it captures owned values (check via its type)
                                self.lambda_own_captures.contains_key(&arg.span)
                                    || matches!(&arg.ty, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)))
                            }
                            _ => false,
                        };
                        if is_affine_arg {
                            if let Some(quals) = callee_qualifiers {
                                if let Some((qualifier, param_name)) = quals.get(i) {
                                    match qualifier {
                                        ParamQualifier::RequiresU | ParamQualifier::Shared => {
                                            let callee_name = callee_var_name(func)
                                                .unwrap_or("<anonymous>")
                                                .to_string();
                                            return Err(SpannedTypeError {
                                                error: TypeError::QualifierMismatch {
                                                    name: "<lambda>".to_string(),
                                                    callee: callee_name,
                                                    param: param_name.clone(),
                                                },
                                                span: arg.span,
                                                note: Some("closure captures an owned (`~`) value, making it single-use".to_string()),
                                                secondary_span: None,
                                                source_file: None,
                                                var_names: None,
                                            });
                                        }
                                        ParamQualifier::Polymorphic => {}
                                    }
                                }
                            }
                        }
                    }

                    let is_non_consuming_borrow = if let TypedExprKind::Var(arg_name) = &arg.kind {
                        self.owned.contains(arg_name)
                            && callee_params.is_some_and(|params| i < params.len() && !params[i])
                    } else {
                        false
                    };
                    if is_non_consuming_borrow {
                        if let TypedExprKind::Var(name) = &arg.kind {
                            self.check_not_consumed(name, arg.span, None)?;
                        }
                    } else {
                        self.check_expr(arg)?;
                    }
                }
                Ok(())
            }

            TypedExprKind::TypeApp { expr, .. } => self.check_expr(expr),

            TypedExprKind::Let { name, value, body } => {
                self.check_expr(value)?;
                // Fabrication guard: let_own_spans marks bindings that resolved to Type::Own.
                // Exempt ~fn closures (closure affinity, not value ownership).
                let is_own_let = self.let_own_spans.contains(&expr.span);
                if is_own_let {
                    let is_own_fn = matches!(&value.ty, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)));
                    if !is_own_fn && !self.is_owned_expr(value) {
                        let t = Type::Named("T".into(), vec![]);
                        return Err(SpannedTypeError {
                            error: TypeError::Mismatch {
                                expected: Type::Own(Box::new(t.clone())),
                                actual: t,
                            },
                            span: expr.span,
                            note: Some(format!(
                                "annotation `~` on `{}` requires an owned value",
                                name
                            )),
                            secondary_span: None,
                            source_file: None,
                            var_names: None,
                        });
                    }
                    self.owned.insert(name.clone());
                    if let TypedExprKind::Lambda { .. } = &value.kind {
                        if let Some(cap_name) = self.lambda_own_captures.get(&value.span) {
                            self.own_fn_notes.insert(
                                name.clone(),
                                format!(
                                    "closure is single-use because it captures `~` value `{}`",
                                    cap_name
                                ),
                            );
                        }
                    }
                }
                if let Some(body) = body {
                    self.check_expr(body)?;
                    if is_own_let {
                        self.owned.remove(name);
                        self.consumed.remove(name);
                        self.partially_consumed.remove(name);
                    }
                }
                Ok(())
            }

            TypedExprKind::LetPattern {
                pattern,
                value,
                body,
            } => {
                self.check_expr(value)?;
                // Fabrication guard for let-pattern
                if self.let_own_spans.contains(&expr.span) {
                    let is_own_fn = matches!(&value.ty, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)));
                    if !is_own_fn && !self.is_owned_expr(value) {
                        let t = Type::Named("T".into(), vec![]);
                        return Err(SpannedTypeError {
                            error: TypeError::Mismatch {
                                expected: Type::Own(Box::new(t.clone())),
                                actual: t,
                            },
                            span: expr.span,
                            note: Some("annotation `~` requires an owned value".into()),
                            secondary_span: None,
                            source_file: None,
                            var_names: None,
                        });
                    }
                }
                // Track pattern-bound owned variables
                let pattern_owned = collect_owned_pattern_vars(pattern);
                for name in &pattern_owned {
                    self.owned.insert(name.clone());
                }
                if let Some(body) = body {
                    self.check_expr(body)?;
                    for name in &pattern_owned {
                        self.owned.remove(name);
                        self.consumed.remove(name);
                        self.partially_consumed.remove(name);
                    }
                }
                Ok(())
            }

            TypedExprKind::Do(exprs) => self.check_exprs(exprs),

            TypedExprKind::If { cond, then_, else_ } => {
                self.check_expr(cond)?;
                let before: HashSet<String> = self.consumed.keys().cloned().collect();
                let (then_consumed, then_partial) = self.check_branch(then_)?;
                let (else_consumed, else_partial) = self.check_branch(else_)?;

                let then_keys: HashSet<String> = then_consumed.keys().cloned().collect();
                let else_keys: HashSet<String> = else_consumed.keys().cloned().collect();
                let newly_in_then: HashSet<String> =
                    then_keys.difference(&before).cloned().collect();
                let newly_in_else: HashSet<String> =
                    else_keys.difference(&before).cloned().collect();
                let in_all: HashSet<String> = newly_in_then
                    .intersection(&newly_in_else)
                    .cloned()
                    .collect();
                let in_some: HashSet<String> = newly_in_then
                    .symmetric_difference(&newly_in_else)
                    .cloned()
                    .collect();

                for name in &in_all {
                    if let Some(&span) = then_consumed.get(name) {
                        self.consumed.insert(name.clone(), span);
                    }
                }
                for name in &in_some {
                    let span = then_consumed
                        .get(name)
                        .or_else(|| else_consumed.get(name))
                        .copied()
                        .unwrap();
                    self.partially_consumed.insert(name.clone(), span);
                }
                for (name, span) in then_partial.iter().chain(else_partial.iter()) {
                    self.partially_consumed.entry(name.clone()).or_insert(*span);
                }
                Ok(())
            }

            TypedExprKind::Match { scrutinee, arms } => {
                self.check_expr(scrutinee)?;
                let before: HashSet<String> = self.consumed.keys().cloned().collect();
                let n = arms.len();
                let mut per_arm_new: Vec<HashMap<String, Span>> = Vec::new();
                let mut merged_partial = self.partially_consumed.clone();

                for arm in arms {
                    // Track pattern-bound owned variables directly from TypedPattern
                    let pattern_owned = collect_owned_pattern_vars(&arm.pattern);
                    for name in &pattern_owned {
                        self.owned.insert(name.clone());
                    }

                    let (arm_consumed, arm_partial) = self.check_branch(&arm.body)?;

                    for name in &pattern_owned {
                        self.owned.remove(name);
                        self.consumed.remove(name);
                        self.partially_consumed.remove(name);
                    }

                    let newly: HashMap<String, Span> = arm_consumed
                        .into_iter()
                        .filter(|(k, _)| !before.contains(k) && !pattern_owned.contains(k))
                        .collect();
                    per_arm_new.push(newly);
                    for (name, span) in &arm_partial {
                        if !pattern_owned.contains(name) {
                            merged_partial.entry(name.clone()).or_insert(*span);
                        }
                    }
                }

                let all_names: HashSet<String> =
                    per_arm_new.iter().flat_map(|s| s.keys().cloned()).collect();
                for name in &all_names {
                    let count = per_arm_new.iter().filter(|s| s.contains_key(name)).count();
                    if count == n {
                        if let Some(span) = per_arm_new.iter().find_map(|s| s.get(name)).copied() {
                            self.consumed.insert(name.clone(), span);
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
                self.partially_consumed = merged_partial;
                Ok(())
            }

            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                self.check_expr(lhs)?;
                self.check_expr(rhs)
            }

            TypedExprKind::UnaryOp { operand, .. } => self.check_expr(operand),

            TypedExprKind::Lambda { params, body } => {
                let lambda_params: HashSet<String> = params.iter().cloned().collect();
                let captured = free_owned_vars(body, self.owned, &lambda_params);
                for name in &captured {
                    if let Some(&first_span) = self
                        .consumed
                        .get(name)
                        .or_else(|| self.partially_consumed.get(name))
                    {
                        return Err(SpannedTypeError {
                            error: TypeError::CapturedMoved { name: name.clone() },
                            span: expr.span,
                            note: None,
                            secondary_span: Some(SecondaryLabel {
                                span: first_span,
                                message: "consumed here".into(),
                                source_file: None,
                            }),
                            source_file: None,
                            var_names: None,
                        });
                    }
                    self.consumed.insert(name.clone(), expr.span);
                    self.moves.insert(expr.span, name.clone());
                }
                let saved_consumed = std::mem::take(&mut self.consumed);
                let saved_partial = std::mem::take(&mut self.partially_consumed);
                let result = self.check_expr(body);
                self.consumed = saved_consumed;
                self.partially_consumed = saved_partial;
                result
            }

            TypedExprKind::FieldAccess { expr: inner, .. } => {
                if let TypedExprKind::Var(name) = &inner.kind {
                    if self.owned.contains(name) {
                        self.check_not_consumed(name, inner.span, None)?;
                        // If field access returns an owned type, consume the base
                        if matches!(&expr.ty, Type::Own(_)) {
                            self.consumed.insert(name.clone(), inner.span);
                            self.moves.insert(inner.span, name.clone());
                        }
                        return Ok(());
                    }
                }
                self.check_expr(inner)
            }

            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    self.check_expr(e)?;
                }
                Ok(())
            }

            TypedExprKind::StructUpdate { base, fields } => {
                for (_, e) in fields {
                    self.check_expr(e)?;
                }

                // Read base type directly from the typed AST
                let base_is_owned = matches!(&base.ty, Type::Own(_));
                let inner_ty = match &base.ty {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };

                let (type_name, base_consumed) = if let Type::Named(name, _) = inner_ty {
                    if let Some(info) = self.registry.lookup_type(name) {
                        if let TypeKind::Record {
                            fields: record_fields,
                        } = &info.kind
                        {
                            let updated_fields: HashSet<&str> =
                                fields.iter().map(|(n, _)| n.as_str()).collect();
                            let has_unreplaced_own = record_fields.iter().any(|(fname, fty)| {
                                type_contains_own(fty) && !updated_fields.contains(fname.as_str())
                            });
                            (Some(name.as_str()), has_unreplaced_own)
                        } else {
                            (Some(name.as_str()), true)
                        }
                    } else {
                        (None, true)
                    }
                } else {
                    (None, true)
                };

                // Fabrication check: shared base with un-replaced owned fields
                if base_consumed && !base_is_owned {
                    if let TypedExprKind::Var(name) = &base.kind {
                        let mut unreplaced: Vec<String> = Vec::new();
                        let mut first_owned_field_ty: Option<Type> = None;
                        if let Some(type_name) = type_name {
                            if let Some(info) = self.registry.lookup_type(type_name) {
                                if let TypeKind::Record {
                                    fields: record_fields,
                                } = &info.kind
                                {
                                    let updated_fields: HashSet<&str> =
                                        fields.iter().map(|(n, _)| n.as_str()).collect();
                                    for (fname, fty) in record_fields {
                                        if type_contains_own(fty)
                                            && !updated_fields.contains(fname.as_str())
                                        {
                                            if first_owned_field_ty.is_none() {
                                                first_owned_field_ty = Some(fty.clone());
                                            }
                                            unreplaced.push(fname.clone());
                                        }
                                    }
                                }
                            }
                        }
                        let (expected_ty, actual_ty) = match first_owned_field_ty {
                            Some(Type::Own(inner)) => (Type::Own(inner.clone()), (*inner).clone()),
                            Some(fty) => (Type::Own(Box::new(fty.clone())), fty),
                            None => {
                                let t = Type::Named("T".into(), vec![]);
                                (Type::Own(Box::new(t.clone())), t)
                            }
                        };
                        return Err(SpannedTypeError {
                            error: TypeError::Mismatch {
                                expected: expected_ty,
                                actual: actual_ty,
                            },
                            span: base.span,
                            note: Some(format!(
                                "struct update on shared `{}` would fabricate owned field(s): {}",
                                name,
                                unreplaced.join(", ")
                            )),
                            secondary_span: None,
                            source_file: None,
                            var_names: None,
                        });
                    }
                    self.check_expr(base)?;
                } else if base_consumed {
                    self.check_expr(base)?;
                } else if let TypedExprKind::Var(name) = &base.kind {
                    if self.owned.contains(name) {
                        self.check_not_consumed(name, base.span, None)?;
                    }
                } else {
                    self.check_expr(base)?;
                }
                Ok(())
            }

            TypedExprKind::Tuple(elements)
            | TypedExprKind::Recur(elements)
            | TypedExprKind::VecLit(elements) => self.check_exprs(elements),
            TypedExprKind::QuestionMark { expr, .. } => self.check_expr(expr),
            TypedExprKind::Lit(_) => Ok(()),
        }
    }
}

fn check_fn(
    typed_fn: &TypedFnDecl,
    fn_param_info: &HashMap<String, Vec<bool>>,
    fn_qualifiers: &HashMap<String, Vec<(ParamQualifier, String)>>,
    let_own_spans: &HashSet<Span>,
    lambda_own_captures: &HashMap<Span, String>,
    registry: &TypeRegistry,
    fn_scheme_params: &HashMap<String, Vec<Type>>,
) -> Result<HashMap<Span, String>, SpannedTypeError> {
    let mut owned: HashSet<String> = HashSet::new();
    let mut affine: HashSet<String> = HashSet::new();

    // Build owned/affine sets from resolved param types
    if let Some(scheme_params) = fn_scheme_params.get(typed_fn.name.as_str()) {
        for (param_name, param_ty) in typed_fn.params.iter().zip(scheme_params.iter()) {
            if matches!(param_ty, Type::Own(_)) || type_is_affine(param_ty, registry) {
                owned.insert(param_name.clone());
                affine.insert(param_name.clone());
            }
        }
    }

    let mut own_fn_notes = HashMap::new();
    let mut checker = OwnershipChecker {
        owned: &mut owned,
        consumed: HashMap::new(),
        partially_consumed: HashMap::new(),
        moves: HashMap::new(),
        fn_param_info,
        affine: &affine,
        fn_qualifiers,
        let_own_spans,
        lambda_own_captures,
        own_fn_notes: &mut own_fn_notes,
        registry,
    };
    checker.check_expr(&typed_fn.body)?;
    Ok(checker.moves)
}
