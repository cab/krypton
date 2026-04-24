use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Expr, Pattern, Span};

use crate::type_registry;
use crate::typed_ast::{DeferredId, TypedExpr};
use crate::types::{ParamMode, Substitution, Type, TypeEnv, TypeVarGen};
use crate::unify::SpannedTypeError;
use crate::visit::TypedExprVisitor;

use super::expr::InferenceContext;
/// Infer the type of an expression using Algorithm J.
#[tracing::instrument(level = "trace", skip_all)]
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<Type, SpannedTypeError> {
    let empty_tpm = FxHashMap::default();
    let empty_tpa = FxHashMap::default();
    let empty_qm = FxHashMap::default();
    let empty_imported_types = FxHashMap::default();
    let mut deferred = Vec::new();
    let mut deferred_id_counter: u32 = 0;
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
        imported_type_info: &empty_imported_types,
        module_path: "__expr__",
        shadowed_prelude_fns: &[],
        self_type: None,
        deferred_overloads: &mut deferred,
        owning_fn_idx: 0,
        deferred_id_counter: &mut deferred_id_counter,
    };
    ctx.infer_expr_inner(expr, None).map(|te| te.ty)
}

/// Instantiate a field type from the registry by substituting the original
/// type parameter var ids with the concrete type arguments.
pub(crate) fn instantiate_field_type(
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
pub(crate) fn collect_parser_pattern_bindings(pattern: &Pattern) -> Vec<&str> {
    fn collect_inner<'a>(pattern: &'a Pattern, out: &mut Vec<&'a str>) {
        match pattern {
            Pattern::Var { name, .. } => out.push(name.as_str()),
            Pattern::Constructor { args, .. } => {
                for arg in args {
                    collect_inner(arg, out);
                }
            }
            Pattern::Tuple { elements, .. } => {
                for element in elements {
                    collect_inner(element, out);
                }
            }
            Pattern::StructPat { fields, .. } => {
                for (_, field_pattern) in fields {
                    collect_inner(field_pattern, out);
                }
            }
            Pattern::Or { alternatives, .. } => {
                if let Some(first) = alternatives.first() {
                    collect_inner(first, out);
                }
            }
            Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
        }
    }

    let mut out = Vec::new();
    collect_inner(pattern, &mut out);
    out
}

/// Check whether `capture_name` is used in an own-requiring position
/// in the typed body. A capture demands own unless ALL of its occurrences
/// are in known-shared positions: binary-op operands, unary-op operands,
/// field-access bases, or function args where the param type is not `~T`.
fn capture_demands_own(body: &TypedExpr, capture_name: &str, subst: &Substitution) -> bool {
    let mut checker = CaptureDemandChecker {
        capture_name,
        subst,
    };
    checker.visit_expr(body).is_err()
}

/// Returns true if `expr` is `Var(capture_name)`.
fn is_capture(expr: &TypedExpr, capture_name: &str) -> bool {
    use crate::typed_ast::TypedExprKind;
    matches!(&expr.kind, TypedExprKind::Var(name) if name == capture_name)
}

/// Visitor that returns `Err(())` on the first "own-demanding" reference to
/// `capture_name`. Shared positions (binary-op operands, unary-op operands,
/// field-access bases, borrow slots, and non-`~` param positions) suppress
/// the direct check; the visitor still recurses into non-capture
/// sub-expressions of those positions so nested uses are still detected.
struct CaptureDemandChecker<'a> {
    capture_name: &'a str,
    subst: &'a Substitution,
}

impl<'a> TypedExprVisitor for CaptureDemandChecker<'a> {
    type Result = Result<(), ()>;

    fn visit_var(&mut self, name: &str, _expr: &TypedExpr) -> Self::Result {
        if name == self.capture_name {
            Err(())
        } else {
            Ok(())
        }
    }

    fn visit_lit(&mut self, _lit: &krypton_parser::ast::Lit) -> Self::Result {
        Ok(())
    }

    fn visit_binary_op(
        &mut self,
        _op: &krypton_parser::ast::BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        // Direct-capture operand is shared (coerces ~T → T); still recurse
        // into non-capture sub-expressions.
        if !is_capture(lhs, self.capture_name) {
            self.visit_expr(lhs)?;
        }
        if !is_capture(rhs, self.capture_name) {
            self.visit_expr(rhs)?;
        }
        Ok(())
    }

    fn visit_unary_op(
        &mut self,
        _op: &krypton_parser::ast::UnaryOp,
        operand: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        if !is_capture(operand, self.capture_name) {
            self.visit_expr(operand)?;
        }
        Ok(())
    }

    fn visit_field_access(
        &mut self,
        inner: &TypedExpr,
        _field: &str,
        _rt: Option<&crate::typed_ast::ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        if !is_capture(inner, self.capture_name) {
            self.visit_expr(inner)?;
        }
        Ok(())
    }

    fn visit_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        param_modes: &[ParamMode],
        _deferred_id: Option<DeferredId>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        let func_ty = self.subst.apply(&func.ty);
        let fn_params = match &func_ty {
            Type::Fn(p, _) => Some(p.as_slice()),
            Type::Own(inner) => match inner.as_ref() {
                Type::Fn(p, _) => Some(p.as_slice()),
                _ => None,
            },
            _ => None,
        };

        for (i, arg) in args.iter().enumerate() {
            if is_capture(arg, self.capture_name) {
                let mode = param_modes.get(i).copied().unwrap_or(ParamMode::Consume);
                if matches!(mode, ParamMode::Borrow | ParamMode::ObservationalBorrow) {
                    continue;
                }
                let demands = if let Some(params) = fn_params {
                    if let Some((_, pty)) = params.get(i) {
                        let resolved = self.subst.apply(pty);
                        matches!(
                            resolved,
                            Type::Own(_) | Type::Var(_) | Type::Shape(_) | Type::MaybeOwn(_, _)
                        )
                    } else {
                        true
                    }
                } else {
                    true
                };
                if demands {
                    return Err(());
                }
                // Shared arg position — don't recurse into this arg.
            } else {
                self.visit_expr(arg)?;
            }
        }
        self.visit_expr(func)
    }

    // Conservative: struct fields, tuple elements, vec/recur elements all
    // treat a direct capture reference as own-demanding.
    fn visit_struct_lit(
        &mut self,
        _name: &str,
        fields: &[(String, TypedExpr)],
        _rt: Option<&crate::typed_ast::ResolvedTypeRef>,
        _expr: &TypedExpr,
    ) -> Self::Result {
        for (_, val) in fields {
            if is_capture(val, self.capture_name) {
                return Err(());
            }
            self.visit_expr(val)?;
        }
        Ok(())
    }

    fn visit_struct_update(
        &mut self,
        base: &TypedExpr,
        fields: &[(String, TypedExpr)],
        _expr: &TypedExpr,
    ) -> Self::Result {
        self.visit_expr(base)?;
        for (_, val) in fields {
            if is_capture(val, self.capture_name) {
                return Err(());
            }
            self.visit_expr(val)?;
        }
        Ok(())
    }

    fn visit_tuple(&mut self, elements: &[TypedExpr], _expr: &TypedExpr) -> Self::Result {
        for elem in elements {
            if is_capture(elem, self.capture_name) {
                return Err(());
            }
            self.visit_expr(elem)?;
        }
        Ok(())
    }

    fn visit_vec_lit(&mut self, elements: &[TypedExpr], _expr: &TypedExpr) -> Self::Result {
        for elem in elements {
            if is_capture(elem, self.capture_name) {
                return Err(());
            }
            self.visit_expr(elem)?;
        }
        Ok(())
    }

    fn visit_recur(
        &mut self,
        args: &[TypedExpr],
        _modes: &[ParamMode],
        _expr: &TypedExpr,
    ) -> Self::Result {
        for elem in args {
            if is_capture(elem, self.capture_name) {
                return Err(());
            }
            self.visit_expr(elem)?;
        }
        Ok(())
    }
    // Defaults handle: If, Let, Do, Match, Lambda, TypeApp, LetPattern,
    // QuestionMark, Discharge — they recurse into all children.
}

pub(crate) fn first_own_capture(
    body: &Expr,
    params: &FxHashSet<&str>,
    env: &TypeEnv,
    subst: &Substitution,
    typed_body: &TypedExpr,
) -> Option<String> {
    match body {
        Expr::Var { name, .. } => {
            if !params.contains(name.as_str()) {
                if let Some(scheme) = env.lookup(name) {
                    let ty = subst.apply(&scheme.ty);
                    if matches!(ty, Type::Own(_)) && capture_demands_own(typed_body, name, subst) {
                        return Some(name.clone());
                    }
                }
            }
            None
        }
        Expr::App { func, args, .. } => first_own_capture(func, params, env, subst, typed_body)
            .or_else(|| {
                args.iter()
                    .find_map(|a| first_own_capture(a, params, env, subst, typed_body))
            }),
        Expr::TypeApp { expr, .. } => first_own_capture(expr, params, env, subst, typed_body),
        Expr::Let {
            name,
            value,
            body: let_body,
            ..
        } => {
            if let Some(found) = first_own_capture(value, params, env, subst, typed_body) {
                return Some(found);
            }
            if let Some(b) = let_body {
                let mut inner = params.clone();
                inner.insert(name.as_str());
                return first_own_capture(b, &inner, env, subst, typed_body);
            }
            None
        }
        Expr::LetPattern {
            pattern,
            value,
            body,
            ..
        } => first_own_capture(value, params, env, subst, typed_body).or_else(|| {
            body.as_ref().and_then(|b| {
                let mut inner = params.clone();
                for name in collect_parser_pattern_bindings(pattern) {
                    inner.insert(name);
                }
                first_own_capture(b, &inner, env, subst, typed_body)
            })
        }),
        Expr::Do { exprs, .. } => exprs
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst, typed_body)),
        Expr::If {
            cond, then_, else_, ..
        } => first_own_capture(cond, params, env, subst, typed_body)
            .or_else(|| first_own_capture(then_, params, env, subst, typed_body))
            .or_else(|| first_own_capture(else_, params, env, subst, typed_body)),
        Expr::Match {
            scrutinee, arms, ..
        } => first_own_capture(scrutinee, params, env, subst, typed_body).or_else(|| {
            arms.iter().find_map(|arm| {
                let mut inner = params.clone();
                for name in collect_parser_pattern_bindings(&arm.pattern) {
                    inner.insert(name);
                }
                arm.guard
                    .as_ref()
                    .and_then(|guard| first_own_capture(guard, &inner, env, subst, typed_body))
                    .or_else(|| first_own_capture(&arm.body, &inner, env, subst, typed_body))
            })
        }),
        Expr::BinaryOp { lhs, rhs, .. } => first_own_capture(lhs, params, env, subst, typed_body)
            .or_else(|| first_own_capture(rhs, params, env, subst, typed_body)),
        Expr::UnaryOp { operand, .. } => first_own_capture(operand, params, env, subst, typed_body),
        Expr::Lambda {
            params: inner_params,
            body,
            ..
        } => {
            let mut inner = params.clone();
            for p in inner_params {
                inner.insert(p.name.as_str());
            }
            first_own_capture(body, &inner, env, subst, typed_body)
        }
        Expr::FieldAccess { expr, .. } => first_own_capture(expr, params, env, subst, typed_body),
        Expr::StructLit { fields, .. } => fields
            .iter()
            .find_map(|(_, e)| first_own_capture(e, params, env, subst, typed_body)),
        Expr::StructUpdate { base, fields, .. } => {
            first_own_capture(base, params, env, subst, typed_body).or_else(|| {
                fields
                    .iter()
                    .find_map(|(_, e)| first_own_capture(e, params, env, subst, typed_body))
            })
        }
        Expr::Tuple { elements, .. } => elements
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst, typed_body)),
        Expr::Recur { args, .. } => args
            .iter()
            .find_map(|a| first_own_capture(a, params, env, subst, typed_body)),
        Expr::QuestionMark { expr, .. } => first_own_capture(expr, params, env, subst, typed_body),
        Expr::List { elements, .. } => elements
            .iter()
            .find_map(|e| first_own_capture(e, params, env, subst, typed_body)),
        Expr::IfLet {
            pattern,
            scrutinee,
            guard,
            then_,
            else_,
            ..
        } => {
            if let Some(found) = first_own_capture(scrutinee, params, env, subst, typed_body) {
                return Some(found);
            }
            let mut inner = params.clone();
            for name in collect_parser_pattern_bindings(pattern) {
                inner.insert(name);
            }
            if let Some(guard) = guard {
                if let Some(found) = first_own_capture(guard, &inner, env, subst, typed_body) {
                    return Some(found);
                }
            }
            if let Some(found) = first_own_capture(then_, &inner, env, subst, typed_body) {
                return Some(found);
            }
            if let Some(else_) = else_ {
                return first_own_capture(else_, params, env, subst, typed_body);
            }
            None
        }
        Expr::Lit { .. } => None,
    }
}

/// Walk a typed lambda body and return the span of the first `Recur` node
/// that targets THIS lambda. Stops at nested `Lambda` bodies because those
/// rebind `recur` to themselves (the inner lambda's params).
pub(crate) fn find_first_recur_span(body: &TypedExpr) -> Option<Span> {
    RecurFinder.visit_expr(body).err()
}

/// Visitor that returns `Err(span)` on the first `Recur` encountered. Nested
/// lambdas are treated as a hard stop boundary — the body of an inner lambda
/// rebinds `recur` to target that inner lambda, so its recurs don't belong to
/// the outer one we're searching.
struct RecurFinder;

impl TypedExprVisitor for RecurFinder {
    type Result = Result<(), Span>;

    fn visit_recur(
        &mut self,
        _args: &[TypedExpr],
        _modes: &[ParamMode],
        expr: &TypedExpr,
    ) -> Self::Result {
        Err(expr.span)
    }

    fn visit_lambda(
        &mut self,
        _params: &[String],
        _body: &TypedExpr,
        _expr: &TypedExpr,
    ) -> Self::Result {
        Ok(())
    }
}
