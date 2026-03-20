use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, Expr, FnDecl, Module, Span, TypeExpr};

use crate::type_registry::{TypeKind, TypeRegistry};
use crate::typed_ast::ParamQualifier;
use crate::types::{Type, TypeScheme, TypeVarId};
use crate::unify::{SecondaryLabel, SpannedTypeError, TypeError};

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
///
/// For each function, returns a Vec<ParamQualifier> parallel to its params.
/// A type-variable-typed param that is used >1 time in the body gets `RequiresU`.
/// Params whose type var has a `shared` bound get `Shared` regardless of body usage.
fn compute_fn_qualifiers(
    fn_decls: &[&FnDecl],
    fn_types: &[(String, TypeScheme, Option<crate::typed_ast::TraitId>)],
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

        // Build type var ID → type param name mapping
        let var_id_to_name: HashMap<_, _> = decl
            .type_params
            .iter()
            .zip(scheme.vars.iter())
            .map(|(tp, &id)| (id, tp.name.clone()))
            .collect();

        let fn_shared = shared_type_vars.get(&decl.name);

        let mut qualifiers = Vec::new();

        for (i, param_ty) in param_types.iter().enumerate() {
            // Strip Own wrapper to get the inner type
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
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } | TypeExpr::Qualified { name, .. } => has_own_field(name, registry),
        TypeExpr::App { name, args, .. } => {
            has_own_field(name, registry) || args.iter().any(|a| param_type_is_affine(a, registry))
        }
        TypeExpr::Tuple { elements, .. } => {
            elements.iter().any(|e| param_type_is_affine(e, registry))
        }
        TypeExpr::Fn { .. } => false,
        TypeExpr::Wildcard { .. } => false,
    }
}

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
    fn_types: &[(String, TypeScheme, Option<crate::typed_ast::TraitId>)],
    registry: &TypeRegistry,
    let_own_spans: &HashSet<Span>,
    lambda_own_captures: &HashMap<Span, String>,
    struct_update_info: &HashMap<Span, (String, HashSet<String>, bool)>,
    shared_type_vars: &HashMap<String, HashSet<String>>,
    imported_fn_qualifiers: &HashMap<String, Vec<(ParamQualifier, String)>>,
    match_arm_owned_vars: &HashMap<Span, Vec<Vec<String>>>,
    field_access_owned: &HashSet<Span>,
) -> Result<OwnershipResult, SpannedTypeError> {
    // Build map: fn_name -> vec of is_own for each param
    let mut fn_param_info: HashMap<String, Vec<bool>> = HashMap::new();
    for decl in &module.decls {
        if let Decl::DefFn(fn_decl) = decl {
            let own_params: Vec<bool> = fn_decl.params.iter().map(is_own_param).collect();
            fn_param_info.insert(fn_decl.name.clone(), own_params);
        }
    }
    // Also populate fn_param_info for imported functions from their TypeScheme,
    // so the non-consuming borrow bypass works for stdlib/imported functions.
    for (name, scheme, _) in fn_types {
        if fn_param_info.contains_key(name) {
            continue; // local definition takes precedence
        }
        if let Type::Fn(params, _) = &scheme.ty {
            let own_params: Vec<bool> = params.iter().map(|t| matches!(t, Type::Own(_))).collect();
            fn_param_info.insert(name.clone(), own_params);
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

    // Build map: fn_name -> param types from type scheme (for fabrication checks)
    let mut fn_scheme_params: HashMap<String, Vec<Type>> = HashMap::new();
    for (name, scheme, _) in fn_types {
        if let Type::Fn(params, _) = &scheme.ty {
            fn_scheme_params.insert(name.clone(), params.clone());
        }
    }

    // Compute qualifier requirements per function
    let mut fn_qualifiers = compute_fn_qualifiers(&fn_decls, fn_types, shared_type_vars);

    // Merge imported qualifiers (local definitions take precedence)
    for (name, quals) in imported_fn_qualifiers {
        fn_qualifiers.entry(name.clone()).or_insert_with(|| quals.clone());
    }

    let mut all_moves: HashMap<Span, String> = HashMap::new();

    for decl in &module.decls {
        if let Decl::DefFn(fn_decl) = decl {
            let affine = build_affine_set(fn_decl, registry);
            let fn_moves = check_fn(
                fn_decl,
                &fn_param_info,
                &affine,
                &fn_qualifiers,
                let_own_spans,
                lambda_own_captures,
                struct_update_info,
                registry,
                &fn_scheme_params,
                match_arm_owned_vars,
                field_access_owned,
            )?;
            all_moves.extend(fn_moves);
        }
    }
    Ok(OwnershipResult {
        fn_qualifiers,
        moves: all_moves,
    })
}

struct OwnershipChecker<'a> {
    owned: &'a mut HashSet<String>,
    consumed: HashMap<String, Span>,
    partially_consumed: HashMap<String, Span>,
    /// Every actual move: var_span → var_name.
    moves: HashMap<Span, String>,
    fn_param_info: &'a HashMap<String, Vec<bool>>,
    affine: &'a HashSet<String>,
    fn_qualifiers: &'a HashMap<String, Vec<(ParamQualifier, String)>>,
    let_own_spans: &'a HashSet<Span>,
    lambda_own_captures: &'a HashMap<Span, String>,
    own_fn_notes: &'a mut HashMap<String, String>,
    struct_update_info: &'a HashMap<Span, (String, HashSet<String>, bool)>,
    registry: &'a TypeRegistry,
    /// Pattern-bound owned variables per match (keyed by match span, per-arm).
    match_arm_owned_vars: &'a HashMap<Span, Vec<Vec<String>>>,
    /// Spans of field access expressions whose result type is `Type::Own(...)`.
    field_access_owned: &'a HashSet<Span>,
}

impl<'a> OwnershipChecker<'a> {
    /// Does this expression intrinsically produce an owned value?
    ///
    /// Uses the ownership pass's `owned` set for variables, syntactic checks
    /// for literals/constructors/aggregates, and the callee's declared return
    /// type for function calls.  Does NOT use resolved types from inference
    /// (those have an `Own` leak through Var binding during unification).
    fn is_owned_expr(&self, expr: &Expr) -> bool {
        match expr {
            // Literals create fresh owned values.
            Expr::Lit { .. } => true,
            // Variables: owned if tracked as owned, or if a nullary constructor.
            Expr::Var { name, .. } => self.owned.contains(name) || self.registry.is_constructor(name),
            // Struct literals, tuples, and list literals create fresh values.
            Expr::StructLit { .. }
            | Expr::StructUpdate { .. }
            | Expr::Tuple { .. }
            | Expr::List { .. } => true,
            // Constructor calls produce owned values.
            Expr::App { func, .. } => {
                if let Some(name) = callee_var_name(func) {
                    self.registry.is_constructor(name)
                } else {
                    false
                }
            }
            // Lambda expressions create fresh closures.
            Expr::Lambda { .. } => true,
            // If: owned when both branches are owned.
            Expr::If { then_, else_, .. } => {
                self.is_owned_expr(then_) && self.is_owned_expr(else_)
            }
            // Match: owned when all arms produce owned values.
            Expr::Match { arms, .. } => {
                !arms.is_empty() && arms.iter().all(|arm| self.is_owned_expr(&arm.body))
            }
            // Block: owned when the last expression is owned.
            Expr::Do { exprs, .. } => {
                exprs.last().is_some_and(|last| self.is_owned_expr(last))
            }
            // Let-in: owned when the body is owned.
            Expr::Let { body, .. } | Expr::LetPattern { body, .. } => {
                body.as_ref().is_some_and(|b| self.is_owned_expr(b))
            }
            // Conservative: other expression forms are not guaranteed owned.
            _ => false,
        }
    }

    /// Check that an owned variable hasn't been consumed or partially consumed.
    fn check_not_consumed(&self, name: &str, span: Span, note: Option<String>) -> Result<(), SpannedTypeError> {
        if let Some(&first_span) = self.consumed.get(name) {
            return Err(SpannedTypeError {
                error: TypeError::AlreadyMoved { name: name.to_string() },
                span,
                note,
                secondary_span: Some(SecondaryLabel { span: first_span, message: "first use here".into(), source_file: None }),
                source_file: None,
                var_names: None,
            });
        }
        if let Some(&branch_span) = self.partially_consumed.get(name) {
            return Err(SpannedTypeError {
                error: TypeError::MovedInBranch { name: name.to_string() },
                span,
                note: None,
                secondary_span: Some(SecondaryLabel { span: branch_span, message: "consumed here".into(), source_file: None }),
                source_file: None,
                var_names: None,
            });
        }
        Ok(())
    }

    /// Check a sequence of expressions.
    fn check_exprs<'e, I>(&mut self, exprs: I) -> Result<(), SpannedTypeError>
    where I: IntoIterator<Item = &'e Expr> {
        for e in exprs { self.check_expr(e)?; }
        Ok(())
    }

    /// Run check_expr on a branch with forked consumed/partially_consumed state.
    /// Returns the branch's consumed and partially_consumed maps.
    fn check_branch(&mut self, expr: &Expr) -> Result<(HashMap<String, Span>, HashMap<String, Span>), SpannedTypeError> {
        let saved_consumed = self.consumed.clone();
        let saved_partial = self.partially_consumed.clone();
        self.check_expr(expr)?;
        let branch_consumed = std::mem::replace(&mut self.consumed, saved_consumed);
        let branch_partial = std::mem::replace(&mut self.partially_consumed, saved_partial);
        Ok((branch_consumed, branch_partial))
    }

    fn check_expr(&mut self, expr: &Expr) -> Result<(), SpannedTypeError> {
        match expr {
            Expr::Var { name, span, .. } => {
                if self.owned.contains(name) {
                    self.check_not_consumed(name, *span, self.own_fn_notes.get(name).cloned())?;
                    self.consumed.insert(name.clone(), *span);
                    self.moves.insert(*span, name.clone());
                }
                Ok(())
            }

            Expr::App {
                func, args, span: _, ..
            } => {
                self.check_expr(func)?;
                let callee_params = callee_var_name(func).and_then(|name| self.fn_param_info.get(name));
                let callee_qualifiers = callee_var_name(func).and_then(|name| self.fn_qualifiers.get(name));
                for (i, arg) in args.iter().enumerate() {
                    // Check qualifier mismatch: affine arg passed to RequiresU param
                    if let Expr::Var {
                        name: arg_name,
                        span: arg_span,
                        ..
                    } = arg
                    {
                        if self.affine.contains(arg_name) {
                            if let Some(quals) = callee_qualifiers {
                                if let Some((qualifier, param_name)) = quals.get(i) {
                                    match qualifier {
                                        ParamQualifier::RequiresU => {
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
                                                source_file: None,
                                                var_names: None,
                                            });
                                        }
                                        ParamQualifier::Shared | ParamQualifier::Polymorphic => {
                                            // Shared: `shared` bound — affine args are non-consuming borrows
                                            // Polymorphic: used <=1 times — accepts both affine and unlimited
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Check qualifier mismatch for non-Var affine arguments
                    // (e.g. lambda capturing ~T passed to RequiresU or Shared param)
                    if !matches!(arg, Expr::Var { .. }) {
                        let is_affine_arg = match arg {
                            Expr::Lambda { span: lspan, .. } => {
                                self.lambda_own_captures.contains_key(lspan)
                            }
                            _ => false,
                        };
                        if is_affine_arg {
                            if let Some(quals) = callee_qualifiers {
                                if let Some((qualifier, param_name)) = quals.get(i) {
                                    match qualifier {
                                        ParamQualifier::RequiresU | ParamQualifier::Shared => {
                                            let callee_name =
                                                callee_var_name(func).unwrap_or("<anonymous>").to_string();
                                            let arg_span = match arg {
                                                Expr::Lambda { span, .. } => *span,
                                                _ => (0, 0),
                                            };
                                            return Err(SpannedTypeError {
                                                error: TypeError::QualifierMismatch {
                                                    name: "<lambda>".to_string(),
                                                    callee: callee_name,
                                                    param: param_name.clone(),
                                                },
                                                span: arg_span,
                                                note: Some("closure captures an owned (`~`) value, making it single-use".to_string()),
                                                secondary_span: None,
                                                source_file: None,
                                                var_names: None,
                                            });
                                        }
                                        ParamQualifier::Polymorphic => {
                                            // Used <=1 times — accepts affine
                                        }
                                    }
                                }
                            }
                        }
                    }

                    let is_non_consuming_borrow = if let Expr::Var { name: arg_name, .. } = arg {
                        self.owned.contains(arg_name)
                            && callee_params.is_some_and(|params| i < params.len() && !params[i])
                    } else {
                        false
                    };
                    if is_non_consuming_borrow {
                        if let Expr::Var { name, span, .. } = arg {
                            self.check_not_consumed(name, *span, None)?;
                        }
                    } else {
                        self.check_expr(arg)?;
                    }
                }
                Ok(())
            }

            Expr::TypeApp { expr, .. } => self.check_expr(expr),

            Expr::Let {
                name,
                ty: ty_ann,
                value,
                body,
                span,
            } => {
                self.check_expr(value)?;
                // Fabrication guard: `let x: ~T = non_owned_val`
                // Exempt ~fn(...) annotations (closure affinity, not value ownership).
                if let Some(TypeExpr::Own { inner, .. }) = ty_ann.as_ref() {
                    if !matches!(inner.as_ref(), TypeExpr::Fn { .. }) {
                        if !self.is_owned_expr(value) {
                            let t = Type::Named("T".into(), vec![]);
                            return Err(SpannedTypeError {
                                error: TypeError::Mismatch {
                                    expected: Type::Own(Box::new(t.clone())),
                                    actual: t,
                                },
                                span: *span,
                                note: Some(format!(
                                    "annotation `~` on `{}` requires an owned value",
                                    name
                                )),
                                secondary_span: None,
                                source_file: None,
                                var_names: None,
                            });
                        }
                    }
                }
                let is_own_let = self.let_own_spans.contains(span);
                if is_own_let {
                    self.owned.insert(name.clone());
                    if let Expr::Lambda { span: lspan, .. } = value.as_ref() {
                        if let Some(cap_name) = self.lambda_own_captures.get(lspan) {
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

            Expr::LetPattern { ty: ty_ann, value, body, span, .. } => {
                self.check_expr(value)?;
                // Fabrication guard for let-pattern annotations
                if let Some(TypeExpr::Own { inner, .. }) = ty_ann.as_ref() {
                    if !matches!(inner.as_ref(), TypeExpr::Fn { .. }) {
                        if !self.is_owned_expr(value) {
                            let t = Type::Named("T".into(), vec![]);
                            return Err(SpannedTypeError {
                                error: TypeError::Mismatch {
                                    expected: Type::Own(Box::new(t.clone())),
                                    actual: t,
                                },
                                span: *span,
                                note: Some("annotation `~` requires an owned value".into()),
                                secondary_span: None,
                                source_file: None,
                                var_names: None,
                            });
                        }
                    }
                }
                if let Some(body) = body {
                    self.check_expr(body)?;
                }
                Ok(())
            }

            Expr::Do { exprs, .. } => self.check_exprs(exprs),

            Expr::If {
                cond, then_, else_, ..
            } => {
                self.check_expr(cond)?;
                let before: HashSet<String> = self.consumed.keys().cloned().collect();
                let (then_consumed, then_partial) = self.check_branch(then_)?;
                let (else_consumed, else_partial) = self.check_branch(else_)?;

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

            Expr::Match {
                scrutinee, arms, span,
            } => {
                self.check_expr(scrutinee)?;
                let before: HashSet<String> = self.consumed.keys().cloned().collect();
                let n = arms.len();
                let mut per_arm_new: Vec<HashMap<String, Span>> = Vec::new();
                let mut merged_partial = self.partially_consumed.clone();

                let per_arm_owned = self.match_arm_owned_vars.get(span);

                for (arm_idx, arm) in arms.iter().enumerate() {
                    // Track pattern-bound owned variables for this arm
                    let pattern_owned: &[String] = per_arm_owned
                        .and_then(|v| v.get(arm_idx))
                        .map(|v| v.as_slice())
                        .unwrap_or(&[]);
                    for name in pattern_owned {
                        self.owned.insert(name.clone());
                    }

                    let (arm_consumed, arm_partial) = self.check_branch(&arm.body)?;

                    // Clean up pattern-bound vars (scoped to this arm)
                    for name in pattern_owned {
                        self.owned.remove(name);
                        self.consumed.remove(name);
                        self.partially_consumed.remove(name);
                    }

                    let newly: HashMap<String, Span> = arm_consumed
                        .into_iter()
                        .filter(|(k, _)| !before.contains(k))
                        .collect();
                    per_arm_new.push(newly);
                    for (name, span) in &arm_partial {
                        merged_partial.entry(name.clone()).or_insert(*span);
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

            Expr::BinaryOp { lhs, rhs, .. } => {
                self.check_expr(lhs)?;
                self.check_expr(rhs)
            }

            Expr::UnaryOp { operand, .. } => self.check_expr(operand),

            Expr::Lambda {
                params, body, span, ..
            } => {
                let lambda_params: HashSet<String> = params.iter().map(|p| p.name.clone()).collect();
                let captured = free_owned_vars(body, self.owned, &lambda_params);
                for name in &captured {
                    if let Some(&first_span) = self
                        .consumed
                        .get(name)
                        .or_else(|| self.partially_consumed.get(name))
                    {
                        return Err(SpannedTypeError {
                            error: TypeError::CapturedMoved { name: name.clone() },
                            span: *span,
                            note: None,
                            secondary_span: Some(SecondaryLabel { span: first_span, message: "consumed here".into(), source_file: None }),
                            source_file: None,
                            var_names: None,
                        });
                    }
                    self.consumed.insert(name.clone(), *span);
                    self.moves.insert(*span, name.clone());
                }
                let saved_consumed = std::mem::take(&mut self.consumed);
                let saved_partial = std::mem::take(&mut self.partially_consumed);
                let result = self.check_expr(body);
                self.consumed = saved_consumed;
                self.partially_consumed = saved_partial;
                result
            }

            Expr::FieldAccess { expr, span, .. } => {
                if let Expr::Var { name, span: var_span, .. } = expr.as_ref() {
                    if self.owned.contains(name) {
                        self.check_not_consumed(name, *var_span, None)?;
                        // If this field access returns an owned type, consume the base
                        if self.field_access_owned.contains(span) {
                            self.consumed.insert(name.clone(), *var_span);
                            self.moves.insert(*var_span, name.clone());
                        }
                        // Otherwise: projection, no consumption
                        return Ok(());
                    }
                }
                self.check_expr(expr)
            }

            Expr::StructLit { fields, .. } => self.check_exprs(fields.iter().map(|(_, e)| e)),

            Expr::StructUpdate { base, fields, span } => {
                self.check_exprs(fields.iter().map(|(_, e)| e))?;

                let (base_consumed, base_is_owned) =
                    if let Some((type_name, updated_fields, base_own)) = self.struct_update_info.get(span) {
                        if let Some(info) = self.registry.lookup_type(type_name) {
                            if let TypeKind::Record {
                                fields: record_fields,
                            } = &info.kind
                            {
                                let has_unreplaced_own = record_fields.iter().any(|(fname, fty)| {
                                    type_contains_own(fty) && !updated_fields.contains(fname)
                                });
                                (has_unreplaced_own, *base_own)
                            } else {
                                (true, *base_own)
                            }
                        } else {
                            (true, *base_own)
                        }
                    } else {
                        (true, false)
                    };

                // If base has un-replaced owned fields and base is not owned, error:
                // struct update on shared base would fabricate owned fields.
                if base_consumed && !base_is_owned {
                    if let Expr::Var { name, span: var_span, .. } = base.as_ref() {
                        // Find un-replaced owned field names for the error message
                        let unreplaced: Vec<String> = if let Some((type_name, updated_fields, _)) = self.struct_update_info.get(span) {
                            if let Some(info) = self.registry.lookup_type(type_name) {
                                if let TypeKind::Record { fields: record_fields } = &info.kind {
                                    record_fields.iter()
                                        .filter(|(fname, fty)| type_contains_own(fty) && !updated_fields.contains(fname))
                                        .map(|(fname, _)| fname.clone())
                                        .collect()
                                } else { vec![] }
                            } else { vec![] }
                        } else { vec![] };
                        let t = Type::Named("T".into(), vec![]);
                        return Err(SpannedTypeError {
                            error: TypeError::Mismatch {
                                expected: Type::Own(Box::new(t.clone())),
                                actual: t,
                            },
                            span: *var_span,
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
                    // Non-Var base expression with fabrication: check the base for moves
                    self.check_expr(base)?;
                } else if base_consumed {
                    // base_is_owned: consume the base (it has un-replaced owned fields)
                    self.check_expr(base)?;
                } else if let Expr::Var { name, span, .. } = base.as_ref() {
                    if self.owned.contains(name) {
                        self.check_not_consumed(name, *span, None)?;
                    }
                } else {
                    self.check_expr(base)?;
                }
                Ok(())
            }

            Expr::Tuple { elements, .. } => self.check_exprs(elements),
            Expr::Recur { args, .. } => self.check_exprs(args),
            Expr::QuestionMark { expr, .. } => self.check_expr(expr),
            Expr::List { elements, .. } => self.check_exprs(elements),
            Expr::Lit { .. } => Ok(()),
        }
    }
}

fn check_fn(
    decl: &FnDecl,
    fn_param_info: &HashMap<String, Vec<bool>>,
    affine: &HashSet<String>,
    fn_qualifiers: &HashMap<String, Vec<(ParamQualifier, String)>>,
    let_own_spans: &HashSet<Span>,
    lambda_own_captures: &HashMap<Span, String>,
    struct_update_info: &HashMap<Span, (String, HashSet<String>, bool)>,
    registry: &TypeRegistry,
    fn_scheme_params: &HashMap<String, Vec<Type>>,
    match_arm_owned_vars: &HashMap<Span, Vec<Vec<String>>>,
    field_access_owned: &HashSet<Span>,
) -> Result<HashMap<Span, String>, SpannedTypeError> {
    let mut owned: HashSet<String> = decl
        .params
        .iter()
        .filter(|p| is_own_param(p))
        .map(|p| p.name.clone())
        .collect();

    // Also track params whose resolved type is Own (inferred ownership).
    // With coerce_unify stripping Own at Var-binding sites, Own only appears
    // in resolved param types when legitimately required (e.g. passed to ~T param).
    if let Some(scheme_params) = fn_scheme_params.get(decl.name.as_str()) {
        for (param, scheme_ty) in decl.params.iter().zip(scheme_params.iter()) {
            if matches!(scheme_ty, Type::Own(_)) {
                owned.insert(param.name.clone());
            }
        }
    }

    // Affine params (containing own types deeper in the type) also need
    // consumption tracking to detect double-use (E0101).
    for name in affine {
        owned.insert(name.clone());
    }

    // Note: we don't short-circuit when owned/affine/let_own_spans are all empty,
    // because fabrication checks run for every call site regardless.

    let mut own_fn_notes = HashMap::new();
    let mut checker = OwnershipChecker {
        owned: &mut owned,
        consumed: HashMap::new(),
        partially_consumed: HashMap::new(),
        moves: HashMap::new(),
        fn_param_info,
        affine,
        fn_qualifiers,
        let_own_spans,
        lambda_own_captures,
        own_fn_notes: &mut own_fn_notes,
        struct_update_info,
        registry,
        match_arm_owned_vars,
        field_access_owned,
    };
    checker.check_expr(&decl.body)?;
    Ok(checker.moves)
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
