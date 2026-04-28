// Control-flow lowering: `do` blocks, short-circuiting `&&`/`||`, and the
// trait-routed primitive operators (`==`, `<`, `+`, `-`, `~`, …) that
// delegate through trait method dispatch when the operand types aren't
// the built-in primitives that `resolve_binop`/`resolve_unaryop` accept.

use krypton_parser::ast::{BinOp, UnaryOp};
use krypton_typechecker::typed_ast::{ScopeId, TraitName, TypedExpr, TypedExprKind};
use krypton_typechecker::types::Type;

use super::ctx::{LoweredValue, LowerCtx};
use super::op_resolve::strip_own;
use super::util::{atom_expr_at, expr_at, simple_at};
use super::LowerError;
use crate::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExprKind};

impl<'a> LowerCtx<'a> {
    /// Lower a Do block (sequence of expressions).
    /// Processes left-to-right so Let bindings are in scope for subsequent exprs.
    /// The `scope_id` (stamped by the typechecker) identifies the Do's lexical
    /// scope for block-scoped auto-close.
    pub(super) fn lower_do(
        &mut self,
        exprs: &[TypedExpr],
        _result_ty: &Type,
        scope_id: Option<ScopeId>,
    ) -> Result<Expr, LowerError> {
        if exprs.is_empty() {
            return Ok(atom_expr_at(
                (0, 0),
                Type::Unit.into(),
                Atom::Lit(Literal::Unit),
            ));
        }
        self.enter_scope(scope_id);
        let body = self.lower_do_slice(exprs)?;
        self.exit_scope(scope_id, body)
    }

    /// Recursively lower a slice of Do-block expressions.
    pub(super) fn lower_do_slice(&mut self, exprs: &[TypedExpr]) -> Result<Expr, LowerError> {
        if exprs.is_empty() {
            return Ok(atom_expr_at(
                (0, 0),
                Type::Unit.into(),
                Atom::Lit(Literal::Unit),
            ));
        }
        if exprs.len() == 1 {
            // If the single expression is a Let/LetPattern with no body, it's a trailing
            // statement — fall through to the Do-block Let handler which will use the
            // empty rest (→ Unit) as the body.
            if !matches!(
                &exprs[0].kind,
                TypedExprKind::Let { body: None, .. }
                    | TypedExprKind::LetPattern { body: None, .. }
            ) {
                return self.lower_expr(&exprs[0]);
            }
        }

        let expr = &exprs[0];
        let rest = &exprs[1..];

        // Special case: Let { body: None } in a Do block — the body is the rest of the block
        if let TypedExprKind::Let {
            name,
            value,
            body: None,
        } = &expr.kind
        {
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

            if let Some(type_name) = self.resource_type_name(&value.ty) {
                self.bind_resource(name, bind, &type_name);
            } else {
                self.push_var(name, bind);
            }
            let mut body_expr = self.lower_do_slice(rest)?;

            // Emit close for the shadowed binding
            if let (Some(binding), Some(old_id)) = (&shadow_close, old_var) {
                body_expr = self.emit_shadow_close(binding, old_id, body_expr)?;
            }

            self.pop_var(name);

            return match lowered_value {
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
                    Ok(self.inline_compound_let(bind, value.ty.clone(), value_expr, body_expr))
                }
            };
        }

        // Special case: LetPattern { body: None } in a Do block — the body is the rest
        if let TypedExprKind::LetPattern {
            pattern,
            value,
            body: None,
        } = &expr.kind
        {
            if rest.is_empty() {
                return self.lower_let_pattern(pattern, value, None, &Type::Unit);
            }
            let rest_ty = exprs.last().map(|e| e.ty.clone()).unwrap_or(Type::Unit);
            // Synthesize a body that is the rest of the do block as a Do expr
            let rest_body = if rest.len() == 1 {
                rest[0].clone()
            } else {
                TypedExpr {
                    kind: TypedExprKind::Do(rest.to_vec()),
                    ty: rest_ty.clone(),
                    span: rest[0].span,
                    resolved_ref: None,
                    // Synthetic grouping: not its own scope. The enclosing
                    // real Do already owns the scope identity for this slice.
                    scope_id: None,
                }
            };
            return self.lower_let_pattern(pattern, value, Some(&rest_body), &rest_ty);
        }

        // Non-let statement: lower as discarded binding, then continue with rest
        let lowered = self.try_lower_as_simple(expr)?;
        let discard = self.fresh_var();
        let rest_expr = self.lower_do_slice(rest)?;

        match lowered {
            LoweredValue::Simple(bindings, simple) => {
                let let_expr = expr_at(
                    expr.span,
                    rest_expr.ty.clone(),
                    ExprKind::Let {
                        bind: discard,
                        ty: expr.ty.clone().into(),
                        value: simple,
                        body: Box::new(rest_expr),
                    },
                );
                Ok(Self::wrap_bindings(bindings, let_expr))
            }
            LoweredValue::Expr(value_expr) => {
                Ok(self.inline_compound_let(discard, expr.ty.clone(), value_expr, rest_expr))
            }
        }
    }

    /// Lower short-circuit `&&` / `||`.
    ///
    /// `is_and = true`:  `lhs && rhs` → `let v = lhs; switch v { 1 -> rhs | _ -> false }`
    /// `is_and = false`: `lhs || rhs` → `let v = lhs; switch v { 1 -> true | _ -> rhs }`
    ///
    /// LHS is always lowered as a full expression (it may itself be a compound
    /// expression like another `&&`), bound to a var, then used as the Switch
    /// scrutinee. RHS is lowered lazily in the appropriate branch.
    pub(super) fn lower_short_circuit(
        &mut self,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        is_and: bool,
    ) -> Result<Expr, LowerError> {
        let lhs_expr = self.lower_expr(lhs)?;
        let lhs_var = self.fresh_var();

        let (true_branch, false_branch) = if is_and {
            (
                self.lower_expr(rhs)?,
                atom_expr_at(lhs.span, Type::Bool.into(), Atom::Lit(Literal::Bool(false))),
            )
        } else {
            (
                atom_expr_at(lhs.span, Type::Bool.into(), Atom::Lit(Literal::Bool(true))),
                self.lower_expr(rhs)?,
            )
        };

        let switch = expr_at(
            lhs.span,
            Type::Bool.into(),
            ExprKind::BoolSwitch {
                scrutinee: Atom::Var(lhs_var),
                true_body: Box::new(true_branch),
                false_body: Box::new(false_branch),
            },
        );

        // Bind lhs result to lhs_var, then switch on it
        Ok(self.inline_compound_let(lhs_var, Type::Bool, lhs_expr, switch))
    }

    /// Desugar comparison operators to trait method calls (Eq.eq / Ord.lt).
    pub(super) fn lower_trait_comparison(
        &mut self,
        op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let (trait_name, method_name, swap, negate) = match op {
            BinOp::Eq => (TraitName::core_eq(), "eq", false, false),
            BinOp::Neq => (TraitName::core_eq(), "eq", false, true),
            BinOp::Lt => (TraitName::core_ord(), "lt", false, false),
            BinOp::Gt => (TraitName::core_ord(), "lt", true, false),
            BinOp::Le => (TraitName::core_ord(), "lt", true, true),
            BinOp::Ge => (TraitName::core_ord(), "lt", false, true),
            _ => unreachable!(),
        };

        let (lhs_arg, rhs_arg) = if swap { (rhs, lhs) } else { (lhs, rhs) };
        let dict_ty = strip_own(&lhs.ty).clone();

        // Resolve dict BEFORE entering CPS chain
        let (dict_bindings, dict_atom) =
            self.resolve_dict(&trait_name, std::slice::from_ref(&dict_ty))?;

        let result_ty = result_ty.clone();
        let method_name = method_name.to_string();
        // CPS chain for operands; wrap dict_bindings OUTSIDE
        let inner = self.lower_to_atom_then(lhs_arg, |ctx, l| {
            ctx.lower_to_atom_then(rhs_arg, |ctx, r| {
                let var = ctx.fresh_var();
                let call_body = if negate {
                    let neg_var = ctx.fresh_var();
                    expr_at(
                        lhs.span,
                        Type::Bool.into(),
                        ExprKind::Let {
                            bind: neg_var,
                            ty: Type::Bool.into(),
                            value: simple_at(
                                lhs.span,
                                SimpleExprKind::PrimOp {
                                    op: PrimOp::Not,
                                    args: vec![Atom::Var(var)],
                                },
                            ),
                            body: Box::new(atom_expr_at(
                                lhs.span,
                                Type::Bool.into(),
                                Atom::Var(neg_var),
                            )),
                        },
                    )
                } else {
                    atom_expr_at(lhs.span, result_ty.into(), Atom::Var(var))
                };
                Ok(expr_at(
                    lhs.span,
                    call_body.ty.clone(),
                    ExprKind::Let {
                        bind: var,
                        ty: Type::Bool.into(),
                        value: simple_at(
                            lhs.span,
                            SimpleExprKind::TraitCall {
                                trait_name: trait_name.clone(),
                                method_name: method_name.clone(),
                                args: vec![dict_atom.clone(), l, r],
                            },
                        ),
                        body: Box::new(call_body),
                    },
                ))
            })
        })?;
        Ok(Self::wrap_bindings(dict_bindings, inner))
    }

    /// Desugar arithmetic operators on user-defined types to trait method calls.
    pub(super) fn lower_trait_arithmetic(
        &mut self,
        op: &BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let (trait_name, method_name) = match op {
            BinOp::Add => (TraitName::core_semigroup(), "combine"),
            BinOp::Sub => (TraitName::core_sub(), "sub"),
            BinOp::Mul => (TraitName::core_mul(), "mul"),
            BinOp::Div => (TraitName::core_div(), "div"),
            _ => unreachable!(),
        };

        let dict_ty = strip_own(&lhs.ty).clone();

        let (dict_bindings, dict_atom) =
            self.resolve_dict(&trait_name, std::slice::from_ref(&dict_ty))?;

        let result_ty = result_ty.clone();
        let method_name = method_name.to_string();
        let inner = self.lower_to_atom_then(lhs, |ctx, l| {
            ctx.lower_to_atom_then(rhs, |ctx, r| {
                let var = ctx.fresh_var();
                let ty = result_ty;
                Ok(expr_at(
                    lhs.span,
                    ty.clone().into(),
                    ExprKind::Let {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(
                            lhs.span,
                            SimpleExprKind::TraitCall {
                                trait_name: trait_name.clone(),
                                method_name: method_name.clone(),
                                args: vec![dict_atom.clone(), l, r],
                            },
                        ),
                        body: Box::new(atom_expr_at(lhs.span, ty.into(), Atom::Var(var))),
                    },
                ))
            })
        })?;
        Ok(Self::wrap_bindings(dict_bindings, inner))
    }

    /// Desugar unary operators on user-defined types to trait method calls.
    pub(super) fn lower_trait_unary(
        &mut self,
        op: &UnaryOp,
        operand: &TypedExpr,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let (trait_name, method_name) = match op {
            UnaryOp::Neg => (TraitName::core_neg(), "neg"),
            _ => unreachable!(),
        };

        let dict_ty = strip_own(&operand.ty).clone();

        let (dict_bindings, dict_atom) =
            self.resolve_dict(&trait_name, std::slice::from_ref(&dict_ty))?;

        let result_ty = result_ty.clone();
        let method_name = method_name.to_string();
        let inner = self.lower_to_atom_then(operand, |ctx, a| {
            let var = ctx.fresh_var();
            let ty = result_ty;
            Ok(expr_at(
                operand.span,
                ty.clone().into(),
                ExprKind::Let {
                    bind: var,
                    ty: ty.clone().into(),
                    value: simple_at(
                        operand.span,
                        SimpleExprKind::TraitCall {
                            trait_name: trait_name.clone(),
                            method_name: method_name.clone(),
                            args: vec![dict_atom.clone(), a],
                        },
                    ),
                    body: Box::new(atom_expr_at(operand.span, ty.into(), Atom::Var(var))),
                },
            ))
        })?;
        Ok(Self::wrap_bindings(dict_bindings, inner))
    }
}
