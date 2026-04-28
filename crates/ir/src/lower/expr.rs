// `lower_expr` dispatcher and per-`TypedExprKind` lowering. Each branch
// returns a full IR `Expr` (control-flow-shaped); compound subterms route
// through the ANF helpers when their result must be bound to a name. The
// dispatcher itself is the entry point used by every other extraction
// (control, call, dict) when they need to descend into a non-tail subexpr.

use krypton_parser::ast::{BinOp, Lit, UnaryOp};
use krypton_typechecker::typed_ast::{
    self as typed_ast, ResolvedTypeRef, TypedExpr, TypedExprKind, TypedPattern,
};
use krypton_typechecker::types::{SchemeVarId, Type};

use super::ctx::{CloseMode, LetBinding, LoweredValue, LowerCtx};
use super::module_pipeline::{
    callable_overload_signature, callable_qualified_name, convert_lit, extract_vec_element_type,
    resolve_binop, resolve_unaryop, resolved_callable_ref, resolved_constructor_ref,
    resolved_trait_method_ref, strip_own, variant_ref_from_constructor,
};
use super::util::{atom_expr_at, expr_at, simple_at};
use super::LowerError;
use crate::{Atom, Expr, ExprKind, Literal, SimpleExprKind, SwitchBranch};

impl<'a> LowerCtx<'a> {
    // -----------------------------------------------------------------------
    // Expression lowering (produces full Expr trees)
    // -----------------------------------------------------------------------

    pub(super) fn lower_expr(&mut self, expr: &TypedExpr) -> Result<Expr, LowerError> {
        match &expr.kind {
            TypedExprKind::Discharge(inner) => self.lower_discharge(expr, inner),
            TypedExprKind::Lit(lit) => self.lower_lit(expr, lit),
            TypedExprKind::Var(name) => self.lower_var(expr, name),
            TypedExprKind::TypeApp {
                expr: inner,
                type_bindings,
            } => self.lower_type_app(expr, inner, type_bindings),
            TypedExprKind::Let { name, value, body } => {
                self.lower_let_expr(expr, name, value, body.as_deref())
            }
            TypedExprKind::Do(exprs) => self.lower_do(exprs, &expr.ty, expr.scope_id),
            TypedExprKind::If { cond, then_, else_ } => self.lower_if(expr, cond, then_, else_),
            TypedExprKind::App { func, args, .. } => self.lower_app_expr(func, args, &expr.ty),
            TypedExprKind::BinaryOp { op, lhs, rhs } => self.lower_binary_op(expr, op, lhs, rhs),
            TypedExprKind::UnaryOp { op, operand } => self.lower_unary_op(expr, op, operand),
            TypedExprKind::Tuple(elems) => self.lower_tuple(expr, elems),
            TypedExprKind::StructLit {
                name,
                fields,
                resolved_type_ref,
            } => self.lower_struct_lit_expr(name, fields, resolved_type_ref.as_ref(), &expr.ty),
            TypedExprKind::FieldAccess {
                expr: base,
                field,
                resolved_type_ref,
            } => self.lower_field_access(expr, base, field, resolved_type_ref.as_ref()),
            TypedExprKind::StructUpdate { base, fields } => {
                self.lower_struct_update_expr(base, fields, &expr.ty)
            }
            TypedExprKind::Lambda { params, body } => self.lower_lambda_expr(expr, params, body),
            TypedExprKind::Match { scrutinee, arms } => self.lower_match(scrutinee, arms, &expr.ty),
            TypedExprKind::LetPattern {
                pattern,
                value,
                body,
            } => self.lower_let_pattern_expr(expr, pattern, value, body.as_deref()),
            TypedExprKind::Recur { args, .. } => self.lower_recur(expr, args),
            TypedExprKind::QuestionMark {
                expr: inner,
                is_option,
            } => self.lower_question_mark(expr, inner, *is_option),
            TypedExprKind::VecLit(elems) => self.lower_vec_lit(expr, elems),
        }
    }

    #[inline]
    pub(super) fn lower_discharge(&mut self, expr: &TypedExpr, inner: &TypedExpr) -> Result<Expr, LowerError> {
        // Lower inner for ownership discharge, discard, return Unit.
        let (bindings, _atom) = self.lower_to_atom(inner)?;
        let unit_expr = atom_expr_at(expr.span, expr.ty.clone().into(), Atom::Lit(Literal::Unit));
        Ok(Self::wrap_bindings(bindings, unit_expr))
    }

    #[inline]
    pub(super) fn lower_lit(&mut self, expr: &TypedExpr, lit: &Lit) -> Result<Expr, LowerError> {
        Ok(atom_expr_at(
            expr.span,
            expr.ty.clone().into(),
            Atom::Lit(convert_lit(lit)),
        ))
    }

    #[inline]
    pub(super) fn lower_var(&mut self, expr: &TypedExpr, name: &str) -> Result<Expr, LowerError> {
        if let Some((_binding_name, constructor_ref)) = resolved_constructor_ref(expr) {
            match constructor_ref.kind {
                typed_ast::ConstructorKind::Variant => {
                    let variant_ref =
                        variant_ref_from_constructor(constructor_ref).ok_or_else(|| {
                            LowerError::InternalError(format!(
                                "missing variant ref for constructor `{}`",
                                constructor_ref.constructor_name
                            ))
                        })?;
                    let (tag, fields) = self.variant_info(&variant_ref)?;
                    let type_cref = self.type_canonical_ref(&constructor_ref.type_ref);
                    if fields.is_empty() {
                        let var = self.fresh_var();
                        return Ok(expr_at(
                            expr.span,
                            expr.ty.clone().into(),
                            ExprKind::Let {
                                bind: var,
                                ty: expr.ty.clone().into(),
                                value: simple_at(
                                    expr.span,
                                    SimpleExprKind::ConstructVariant {
                                        type_ref: type_cref,
                                        variant: constructor_ref.constructor_name.clone(),
                                        tag,
                                        fields: vec![],
                                    },
                                ),
                                body: Box::new(atom_expr_at(
                                    expr.span,
                                    expr.ty.clone().into(),
                                    Atom::Var(var),
                                )),
                            },
                        ));
                    }
                    let (bindings, simple) = self.lower_variant_constructor_as_value(
                        &constructor_ref.constructor_name,
                        expr,
                        &constructor_ref.type_ref.qualified_name,
                        tag,
                    )?;
                    return Ok(self.wrap_constructor_value(expr, simple, bindings));
                }
                typed_ast::ConstructorKind::Record => {
                    let (bindings, simple) = self.lower_struct_constructor_as_value(
                        &constructor_ref.constructor_name,
                        &constructor_ref.type_ref.qualified_name,
                        expr,
                    )?;
                    return Ok(self.wrap_constructor_value(expr, simple, bindings));
                }
            }
        }
        if let Some(variant_ref) = self.fallback_variant_ref(name) {
            let (tag, fields) = self.variant_info(&variant_ref)?;
            let type_cref = self.type_canonical_ref(&variant_ref.type_ref);
            if fields.is_empty() {
                let var = self.fresh_var();
                return Ok(expr_at(
                    expr.span,
                    expr.ty.clone().into(),
                    ExprKind::Let {
                        bind: var,
                        ty: expr.ty.clone().into(),
                        value: simple_at(
                            expr.span,
                            SimpleExprKind::ConstructVariant {
                                type_ref: type_cref,
                                variant: name.to_string(),
                                tag,
                                fields: vec![],
                            },
                        ),
                        body: Box::new(atom_expr_at(
                            expr.span,
                            expr.ty.clone().into(),
                            Atom::Var(var),
                        )),
                    },
                ));
            }
            let (bindings, simple) = self.lower_variant_constructor_as_value(
                name,
                expr,
                &variant_ref.type_ref.qualified_name,
                tag,
            )?;
            return Ok(self.wrap_constructor_value(expr, simple, bindings));
        }
        if let Some(type_ref) = self.fallback_type_ref(name) {
            let (bindings, simple) =
                self.lower_struct_constructor_as_value(name, &type_ref.qualified_name, expr)?;
            return Ok(self.wrap_constructor_value(expr, simple, bindings));
        }
        if let Some(id) = self.lookup_var(name) {
            Ok(atom_expr_at(
                expr.span,
                expr.ty.clone().into(),
                Atom::Var(id),
            ))
        } else if let Some((_binding_name, callable_ref)) = resolved_callable_ref(expr) {
            let qn = callable_qualified_name(callable_ref, &self.module_path);
            let sig = callable_overload_signature(callable_ref);
            let Some(fn_id) = self.lookup_callable(&qn, sig) else {
                return Err(LowerError::UnresolvedVar(name.to_string()));
            };
            // Top-level function used as value
            let var = self.fresh_var();
            Ok(expr_at(
                expr.span,
                expr.ty.clone().into(),
                ExprKind::Let {
                    bind: var,
                    ty: expr.ty.clone().into(),
                    value: simple_at(
                        expr.span,
                        SimpleExprKind::MakeClosure {
                            func: fn_id,
                            captures: vec![],
                        },
                    ),
                    body: Box::new(atom_expr_at(
                        expr.span,
                        expr.ty.clone().into(),
                        Atom::Var(var),
                    )),
                },
            ))
        } else if let Some(trait_ref) = resolved_trait_method_ref(expr) {
            // Trait method used as value
            let (bindings, simple) = self.lower_trait_method_as_value(
                &trait_ref.trait_name,
                &trait_ref.method_name,
                &expr.ty,
                &[],
            )?;
            Ok(self.wrap_constructor_value(expr, simple, bindings))
        } else {
            Err(LowerError::UnresolvedVar(name.to_string()))
        }
    }

    #[inline]
    pub(super) fn lower_type_app(
        &mut self,
        expr: &TypedExpr,
        inner: &TypedExpr,
        type_bindings: &[(SchemeVarId, Type)],
    ) -> Result<Expr, LowerError> {
        // For trait method values, use the outer (concrete) type from the TypeApp
        if let Some(trait_ref) = resolved_trait_method_ref(expr) {
            let (bindings, simple) = self.lower_trait_method_as_value(
                &trait_ref.trait_name,
                &trait_ref.method_name,
                &expr.ty,
                type_bindings,
            )?;
            return Ok(self.wrap_constructor_value(expr, simple, bindings));
        }
        self.lower_expr(inner)
    }

    #[inline]
    pub(super) fn lower_let_expr(
        &mut self,
        expr: &TypedExpr,
        name: &str,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
    ) -> Result<Expr, LowerError> {
        // Check for shadow_close before pushing the new binding
        let shadow_close = self.auto_close.shadow_closes.get(&expr.span).cloned();
        let old_var = if shadow_close.is_some() {
            self.lookup_var(name)
        } else {
            None
        };

        let bind = self.fresh_var();
        self.var_types.insert(bind, value.ty.clone());

        // Lower value BEFORE pushing the new binding into scope,
        // so that shadowed references (e.g. `let x = x + 1`) resolve
        // to the *old* VarId, not the freshly allocated one.
        let lowered_value = self.try_lower_as_simple(value)?;

        // `let x = v in body` introduces its own lexical scope
        // identified by the ScopeId stamped at scope_ids time.
        let is_scoped = body.is_some();
        if is_scoped {
            self.enter_scope(expr.scope_id);
        }

        if let Some(type_name) = self.resource_type_name(&value.ty) {
            self.bind_resource(name, bind, &type_name);
        } else {
            self.push_var(name, bind);
        }
        let mut body_expr = if let Some(body) = body {
            self.lower_expr(body)?
        } else {
            // Let without body — the value IS the result
            atom_expr_at(value.span, value.ty.clone().into(), Atom::Var(bind))
        };

        if is_scoped {
            body_expr = self.exit_scope(expr.scope_id, body_expr)?;
        }

        // Emit close for the shadowed binding (wraps the body, runs before body)
        if let (Some(binding), Some(old_id)) = (&shadow_close, old_var) {
            body_expr = self.emit_shadow_close(binding, old_id, body_expr)?;
        }

        self.pop_var(name);

        match lowered_value {
            LoweredValue::Simple(bindings, simple) => {
                let let_expr = expr_at(
                    value.span,
                    body_expr.ty.clone(),
                    ExprKind::Let {
                        bind,
                        ty: value.ty.clone().into(),
                        value: simple,
                        body: Box::new(body_expr),
                    },
                );
                Ok(Self::wrap_bindings(bindings, let_expr))
            }
            LoweredValue::Expr(value_expr) => {
                // Value is a compound expression (If, Do, etc.)
                // We need to inline the value expression and bind its result
                Ok(self.inline_compound_let(bind, value.ty.clone(), value_expr, body_expr))
            }
        }
    }

    #[inline]
    pub(super) fn lower_if(
        &mut self,
        expr: &TypedExpr,
        cond: &TypedExpr,
        then_: &TypedExpr,
        else_: &TypedExpr,
    ) -> Result<Expr, LowerError> {
        let result_ty = expr.ty.clone();
        let span = expr.span;
        self.lower_to_atom_then(cond, |ctx, cond_atom| {
            let then_body = ctx.lower_expr(then_)?;
            let else_body = ctx.lower_expr(else_)?;
            Ok(expr_at(
                span,
                result_ty.into(),
                ExprKind::BoolSwitch {
                    scrutinee: cond_atom,
                    true_body: Box::new(then_body),
                    false_body: Box::new(else_body),
                },
            ))
        })
    }

    #[inline]
    pub(super) fn lower_binary_op(
        &mut self,
        expr: &TypedExpr,
        op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
    ) -> Result<Expr, LowerError> {
        match op {
            // Short-circuit: lhs && rhs → switch lhs { 1 -> rhs | _ -> false }
            BinOp::And => self.lower_short_circuit(lhs, rhs, true),
            // Short-circuit: lhs || rhs → switch lhs { 1 -> true | _ -> rhs }
            BinOp::Or => self.lower_short_circuit(lhs, rhs, false),
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.lower_trait_comparison(op, lhs, rhs, &expr.ty)
            }
            _ => {
                let lhs_ty = strip_own(&lhs.ty).clone();
                if let Ok(prim_op) = resolve_binop(op, &lhs_ty) {
                    // Primitive type — keep PrimOp path
                    let result_ty = expr.ty.clone();
                    let span = expr.span;
                    self.lower_to_atom_then(lhs, |ctx, l| {
                        ctx.lower_to_atom_then(rhs, |ctx, r| {
                            let var = ctx.fresh_var();
                            let ty = result_ty;
                            Ok(expr_at(
                                span,
                                ty.clone().into(),
                                ExprKind::Let {
                                    bind: var,
                                    ty: ty.clone().into(),
                                    value: simple_at(
                                        span,
                                        SimpleExprKind::PrimOp {
                                            op: prim_op,
                                            args: vec![l, r],
                                        },
                                    ),
                                    body: Box::new(atom_expr_at(span, ty.into(), Atom::Var(var))),
                                },
                            ))
                        })
                    })
                } else {
                    // User-defined type — trait dispatch
                    self.lower_trait_arithmetic(op, lhs, rhs, &expr.ty)
                }
            }
        }
    }

    #[inline]
    pub(super) fn lower_unary_op(
        &mut self,
        expr: &TypedExpr,
        op: &UnaryOp,
        operand: &TypedExpr,
    ) -> Result<Expr, LowerError> {
        let operand_ty = strip_own(&operand.ty).clone();
        if let Ok(prim_op) = resolve_unaryop(op, &operand_ty) {
            // Primitive type — keep PrimOp path
            let result_ty = expr.ty.clone();
            let span = expr.span;
            self.lower_to_atom_then(operand, |ctx, atom| {
                let var = ctx.fresh_var();
                let ty = result_ty;
                Ok(expr_at(
                    span,
                    ty.clone().into(),
                    ExprKind::Let {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(
                            span,
                            SimpleExprKind::PrimOp {
                                op: prim_op,
                                args: vec![atom],
                            },
                        ),
                        body: Box::new(atom_expr_at(span, ty.into(), Atom::Var(var))),
                    },
                ))
            })
        } else {
            // User-defined type — trait dispatch
            self.lower_trait_unary(op, operand, &expr.ty)
        }
    }

    #[inline]
    pub(super) fn lower_tuple(&mut self, expr: &TypedExpr, elems: &[TypedExpr]) -> Result<Expr, LowerError> {
        let result_ty = expr.ty.clone();
        let span = expr.span;
        self.lower_atoms_then(elems, vec![], |ctx, atoms| {
            let var = ctx.fresh_var();
            let ty = result_ty;
            Ok(expr_at(
                span,
                ty.clone().into(),
                ExprKind::Let {
                    bind: var,
                    ty: ty.clone().into(),
                    value: simple_at(span, SimpleExprKind::MakeTuple { elements: atoms }),
                    body: Box::new(atom_expr_at(span, ty.into(), Atom::Var(var))),
                },
            ))
        })
    }

    #[inline]
    pub(super) fn lower_field_access(
        &mut self,
        expr: &TypedExpr,
        base: &TypedExpr,
        field: &str,
        resolved_type_ref: Option<&ResolvedTypeRef>,
    ) -> Result<Expr, LowerError> {
        let result_ty = expr.ty.clone();
        let base_ty = base.ty.clone();
        let field = field.to_string();
        let span = expr.span;
        let type_ref = resolved_type_ref
            .cloned()
            .or_else(|| self.resolved_type_ref_from_type(&base_ty));
        self.lower_to_atom_then(base, |ctx, base_atom| {
            let type_ref = type_ref.clone().ok_or_else(|| {
                LowerError::InternalError(format!("FieldAccess on non-named type: {:?}", base_ty))
            })?;
            let idx = ctx.field_index(&type_ref, &field)?;
            let var = ctx.fresh_var();
            let ty = result_ty;
            Ok(expr_at(
                span,
                ty.clone().into(),
                ExprKind::Let {
                    bind: var,
                    ty: ty.clone().into(),
                    value: simple_at(
                        span,
                        SimpleExprKind::Project {
                            value: base_atom,
                            field_index: idx,
                        },
                    ),
                    body: Box::new(atom_expr_at(span, ty.into(), Atom::Var(var))),
                },
            ))
        })
    }

    #[inline]
    pub(super) fn lower_lambda_expr(
        &mut self,
        expr: &TypedExpr,
        params: &[String],
        body: &TypedExpr,
    ) -> Result<Expr, LowerError> {
        let (bindings, simple) = self.lower_lambda(params, body, &expr.ty)?;
        let var = self.fresh_var();
        let ty = expr.ty.clone();
        let mut all_bindings = bindings;
        all_bindings.push(LetBinding {
            bind: var,
            ty: ty.clone().into(),
            value: simple,
        });
        let inner = atom_expr_at(expr.span, ty.into(), Atom::Var(var));
        Ok(Self::wrap_bindings(all_bindings, inner))
    }

    #[inline]
    pub(super) fn lower_let_pattern_expr(
        &mut self,
        expr: &TypedExpr,
        pattern: &TypedPattern,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
    ) -> Result<Expr, LowerError> {
        // `let pat = e in body` introduces its own lexical scope for
        // any resource bindings in the pattern + body, identified by
        // the stamped ScopeId.
        let is_scoped = body.is_some();
        if is_scoped {
            self.enter_scope(expr.scope_id);
        }
        let lowered = self.lower_let_pattern(pattern, value, body, &expr.ty)?;
        if is_scoped {
            self.exit_scope(expr.scope_id, lowered)
        } else {
            Ok(lowered)
        }
    }

    #[inline]
    pub(super) fn lower_recur(&mut self, expr: &TypedExpr, args: &[TypedExpr]) -> Result<Expr, LowerError> {
        let (join_name, _join_params) = self.recur_join.clone().ok_or_else(|| {
            LowerError::InternalError("recur outside of a recur-enabled function".to_string())
        })?;
        let result_ty = expr.ty.clone();
        let span = expr.span;
        let recur_close_bindings = self.auto_close.recur_closes.get(&expr.span).cloned();
        self.lower_atoms_then(args, vec![], |ctx, jump_args| {
            let mut jump_expr = expr_at(
                span,
                result_ty.into(),
                ExprKind::Jump {
                    target: join_name,
                    args: jump_args,
                },
            );
            if let Some(ref close_bindings) = recur_close_bindings {
                // Null slots before the back-edge so an exception
                // later in the same iteration doesn't see already
                // closed disposables through the fn-wide handler.
                jump_expr = ctx.emit_close_calls(close_bindings, jump_expr, CloseMode::NullSlot)?;
            }
            Ok(jump_expr)
        })
    }

    #[inline]
    pub(super) fn lower_question_mark(
        &mut self,
        expr: &TypedExpr,
        inner: &TypedExpr,
        is_option: bool,
    ) -> Result<Expr, LowerError> {
        let early_return = self.early_return_join.ok_or_else(|| {
            LowerError::InternalError("? outside of a ?-enabled function".to_string())
        })?;
        let inner_full_ty = inner.ty.clone();
        let inner_stripped_ty = strip_own(&inner.ty).clone();
        let early_close_bindings = self.auto_close.early_returns.get(&expr.span).cloned();
        let span = expr.span;
        self.lower_to_atom_then(inner, |ctx, scrut_atom| {
            let success_var = ctx.fresh_var();
            let switch = if is_option {
                // Option[T]: Some#0(T) | None#1
                let t = match &inner_stripped_ty {
                    Type::Named(_, args) if !args.is_empty() => args[0].clone(),
                    _ => return Err(LowerError::InternalError(format!(
                        "? operator: expected Option/Own(Option) type, got {inner_stripped_ty:?}"
                    ))),
                };
                let wrap_var = ctx.fresh_var();
                let mut none_jump = expr_at(
                    span,
                    inner_full_ty.clone().into(),
                    ExprKind::Jump {
                        target: early_return,
                        args: vec![Atom::Var(wrap_var)],
                    },
                );
                if let Some(ref close_bindings) = early_close_bindings {
                    none_jump =
                        ctx.emit_close_calls(close_bindings, none_jump, CloseMode::Keep)?;
                }
                expr_at(
                    span,
                    t.clone().into(),
                    ExprKind::Switch {
                        scrutinee: scrut_atom,
                        branches: vec![
                            SwitchBranch {
                                tag: 0,
                                bindings: vec![(success_var, t.clone().into())],
                                body: atom_expr_at(span, t.into(), Atom::Var(success_var)),
                            },
                            SwitchBranch {
                                tag: 1,
                                bindings: vec![],
                                body: expr_at(
                                    span,
                                    inner_full_ty.clone().into(),
                                    ExprKind::Let {
                                        bind: wrap_var,
                                        ty: inner_full_ty.clone().into(),
                                        value: simple_at(
                                            span,
                                            SimpleExprKind::ConstructVariant {
                                                type_ref: ctx.type_canonical_ref_for_name("Option"),
                                                variant: "None".to_string(),
                                                tag: 1,
                                                fields: vec![],
                                            },
                                        ),
                                        body: Box::new(none_jump),
                                    },
                                ),
                            },
                        ],
                        default: None,
                    },
                )
            } else {
                // Result[E, T]: Ok#0(T) | Err#1(E)
                let (err_ty, ok_ty) = match &inner_stripped_ty {
                    Type::Named(_, args) if args.len() >= 2 => (args[0].clone(), args[1].clone()),
                    _ => return Err(LowerError::InternalError(format!(
                        "? operator: expected Result type with 2+ type args, got {inner_stripped_ty:?}"
                    ))),
                };
                let err_var = ctx.fresh_var();
                let wrap_var = ctx.fresh_var();
                let mut err_jump = expr_at(
                    span,
                    inner_full_ty.clone().into(),
                    ExprKind::Jump {
                        target: early_return,
                        args: vec![Atom::Var(wrap_var)],
                    },
                );
                if let Some(ref close_bindings) = early_close_bindings {
                    err_jump = ctx.emit_close_calls(close_bindings, err_jump, CloseMode::Keep)?;
                }
                expr_at(
                    span,
                    ok_ty.clone().into(),
                    ExprKind::Switch {
                        scrutinee: scrut_atom,
                        branches: vec![
                            SwitchBranch {
                                tag: 0,
                                bindings: vec![(success_var, ok_ty.clone().into())],
                                body: atom_expr_at(span, ok_ty.into(), Atom::Var(success_var)),
                            },
                            SwitchBranch {
                                tag: 1,
                                bindings: vec![(err_var, err_ty.into())],
                                body: expr_at(
                                    span,
                                    inner_full_ty.clone().into(),
                                    ExprKind::Let {
                                        bind: wrap_var,
                                        ty: inner_full_ty.clone().into(),
                                        value: simple_at(
                                            span,
                                            SimpleExprKind::ConstructVariant {
                                                type_ref: ctx.type_canonical_ref_for_name("Result"),
                                                variant: "Err".to_string(),
                                                tag: 1,
                                                fields: vec![Atom::Var(err_var)],
                                            },
                                        ),
                                        body: Box::new(err_jump),
                                    },
                                ),
                            },
                        ],
                        default: None,
                    },
                )
            };
            Ok(switch)
        })
    }

    #[inline]
    pub(super) fn lower_vec_lit(&mut self, expr: &TypedExpr, elems: &[TypedExpr]) -> Result<Expr, LowerError> {
        let result_ty = expr.ty.clone();
        let element_type = extract_vec_element_type(&expr.ty)?;
        let span = expr.span;
        self.lower_atoms_then(elems, vec![], |ctx, atoms| {
            let var = ctx.fresh_var();
            let ty = result_ty;
            Ok(expr_at(
                span,
                ty.clone().into(),
                ExprKind::Let {
                    bind: var,
                    ty: ty.clone().into(),
                    value: simple_at(
                        span,
                        SimpleExprKind::MakeVec {
                            element_type: element_type.into(),
                            elements: atoms,
                        },
                    ),
                    body: Box::new(atom_expr_at(span, ty.into(), Atom::Var(var))),
                },
            ))
        })
    }

}
