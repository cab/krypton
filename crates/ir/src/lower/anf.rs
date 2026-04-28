// ANF (administrative normal form) construction. The methods here are the
// glue between TypedExpr and IR: they bind compound subexpressions to
// fresh `VarId`s and surface either an `Atom` (a name or literal) or a
// `LoweredValue` (a `SimpleExpr` plus prefix bindings, or a full `Expr`
// when the value cannot be inlined into a `Let`).

use krypton_parser::ast::BinOp;
use krypton_typechecker::typed_ast::{self as typed_ast, QualifiedName, TypedExpr, TypedExprKind};
use krypton_typechecker::types::Type;

use super::ctx::{LetBinding, LoweredValue, LowerCtx};
use crate::Type as IrType;
use super::module_pipeline::{
    callable_overload_signature, callable_qualified_name, convert_lit, extract_vec_element_type,
    resolve_binop, resolve_unaryop, resolved_callable_ref, resolved_constructor_ref,
    resolved_trait_method_ref, strip_own, variant_ref_from_constructor,
};
use super::util::{atom_expr_at, expr_at, replace_tail_with_jump, simple_at};
use super::LowerError;
use crate::{
    Atom, CanonicalRef, Expr, ExprKind, FnDef, Literal, LocalSymbolKey, ModulePath, SimpleExpr,
    SimpleExprKind, VarId,
};

impl<'a> LowerCtx<'a> {
    // -----------------------------------------------------------------------
    // ANF helpers
    // -----------------------------------------------------------------------

    /// Wrap a sequence of let-bindings around an inner expression (right fold).
    pub(super) fn wrap_bindings(bindings: Vec<LetBinding>, inner: Expr) -> Expr {
        bindings.into_iter().rev().fold(inner, |body, lb| {
            expr_at(
                lb.value.span,
                body.ty.clone(),
                ExprKind::Let {
                    bind: lb.bind,
                    ty: lb.ty,
                    value: lb.value,
                    body: Box::new(body),
                },
            )
        })
    }

    /// Build `let v = simple in v` and reverse-fold prefix bindings around it.
    /// Used by `Var`/`TypeApp` constructor-ref and trait-method paths that
    /// produce `(Vec<LetBinding>, SimpleExpr)` and want a fresh-var-bound Expr.
    #[inline]
    pub(super) fn wrap_constructor_value(
        &mut self,
        expr: &TypedExpr,
        simple: SimpleExpr,
        bindings: Vec<LetBinding>,
    ) -> Expr {
        let var = self.fresh_var();
        let ty: IrType = expr.ty.clone().into();
        let inner = expr_at(
            expr.span,
            ty.clone(),
            ExprKind::Let {
                bind: var,
                ty: ty.clone(),
                value: simple,
                body: Box::new(atom_expr_at(expr.span, ty, Atom::Var(var))),
            },
        );
        Self::wrap_bindings(bindings, inner)
    }

    /// Lower an expression to an Atom. If already atomic, return it directly.
    /// Otherwise lower to SimpleExpr, bind to a fresh VarId, emit a LetBinding.
    /// For compound expressions (If, Do), returns an error — callers should use
    /// lower_expr + inline_compound_let instead.
    pub(super) fn lower_to_atom(&mut self, expr: &TypedExpr) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        match &expr.kind {
            TypedExprKind::Discharge(inner) => {
                // Evaluate inner (for ownership discharge), discard, return Unit.
                let (bindings, _atom) = self.lower_to_atom(inner)?;
                Ok((bindings, Atom::Lit(Literal::Unit)))
            }
            TypedExprKind::Lit(lit) => Ok((vec![], Atom::Lit(convert_lit(lit)))),
            TypedExprKind::Var(name) => {
                if resolved_constructor_ref(expr).is_some()
                    || self.fallback_variant_ref(name).is_some()
                    || self.fallback_type_ref(name).is_some()
                {
                    let (bindings, simple) = self.lower_to_simple(expr)?;
                    let var = self.fresh_var();
                    let ty = expr.ty.clone();
                    let mut all_bindings = bindings;
                    all_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.into(),
                        value: simple,
                    });
                    return Ok((all_bindings, Atom::Var(var)));
                }
                if let Some(id) = self.lookup_var(name) {
                    Ok((vec![], Atom::Var(id)))
                } else if resolved_callable_ref(expr).is_some() {
                    // Top-level function reference as a value — bind it
                    let (bindings, simple) = self.lower_to_simple(expr)?;
                    let var = self.fresh_var();
                    let ty = expr.ty.clone();
                    let mut all_bindings = bindings;
                    all_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.into(),
                        value: simple,
                    });
                    Ok((all_bindings, Atom::Var(var)))
                } else if resolved_trait_method_ref(expr).is_some() {
                    // Trait method as value — delegate to lower_to_simple
                    let (bindings, simple) = self.lower_to_simple(expr)?;
                    let var = self.fresh_var();
                    let ty = expr.ty.clone();
                    let mut all_bindings = bindings;
                    all_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.into(),
                        value: simple,
                    });
                    Ok((all_bindings, Atom::Var(var)))
                } else {
                    Err(LowerError::UnresolvedVar(name.clone()))
                }
            }
            TypedExprKind::TypeApp {
                expr: inner,
                type_bindings,
            } => {
                // For trait method values, use the outer (concrete) type from the TypeApp
                if let Some(trait_ref) = resolved_trait_method_ref(expr) {
                    let (bindings, simple) = self.lower_trait_method_as_value(
                        &trait_ref.trait_name,
                        &trait_ref.method_name,
                        &expr.ty,
                        type_bindings,
                    )?;
                    let var = self.fresh_var();
                    let ty = expr.ty.clone();
                    let mut all_bindings = bindings;
                    all_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.into(),
                        value: simple,
                    });
                    return Ok((all_bindings, Atom::Var(var)));
                }
                self.lower_to_atom(inner)
            }
            _ => match self.try_lower_as_simple(expr)? {
                LoweredValue::Simple(bindings, simple) => {
                    let var = self.fresh_var();
                    let ty = expr.ty.clone();
                    let mut all_bindings = bindings;
                    all_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.into(),
                        value: simple,
                    });
                    Ok((all_bindings, Atom::Var(var)))
                }
                LoweredValue::Expr(_) => Err(LowerError::CompoundInAtom),
            },
        }
    }

    /// Lower an expression to an atom, then call `cont` with that atom to build the rest.
    /// Handles compound sub-expressions (If, Do, Match, etc.) naturally via join points.
    pub(super) fn lower_to_atom_then<F>(&mut self, expr: &TypedExpr, cont: F) -> Result<Expr, LowerError>
    where
        F: FnOnce(&mut Self, Atom) -> Result<Expr, LowerError>,
    {
        // Fast path: already atomic
        match &expr.kind {
            TypedExprKind::Lit(lit) => return cont(self, Atom::Lit(convert_lit(lit))),
            TypedExprKind::Var(name) => {
                // Variant constructors are lowered through the general value path.
                if resolved_constructor_ref(expr).is_none()
                    && self.fallback_variant_ref(name).is_none()
                {
                    if let Some(id) = self.lookup_var(name) {
                        return cont(self, Atom::Var(id));
                    }
                }
            }
            TypedExprKind::TypeApp { expr: inner, .. } => {
                // For trait method values, fall through to general path
                // which preserves the outer concrete type
                if let TypedExprKind::Var(name) = &inner.kind {
                    if resolved_trait_method_ref(expr).is_some() && self.lookup_var(name).is_none()
                    {
                        // Fall through to try_lower_as_simple
                    } else {
                        return self.lower_to_atom_then(inner, cont);
                    }
                } else {
                    return self.lower_to_atom_then(inner, cont);
                }
            }
            _ => {}
        }
        // General path: try_lower_as_simple
        match self.try_lower_as_simple(expr)? {
            LoweredValue::Simple(bindings, simple) => {
                let var = self.fresh_var();
                if expr.ty.is_never() {
                    let never_ty: IrType = expr.ty.clone().into();
                    let let_expr = expr_at(
                        expr.span,
                        never_ty.clone(),
                        ExprKind::Let {
                            bind: var,
                            ty: never_ty.clone(),
                            value: simple,
                            body: Box::new(atom_expr_at(expr.span, never_ty, Atom::Var(var))),
                        },
                    );
                    return Ok(Self::wrap_bindings(bindings, let_expr));
                }
                let body = cont(self, Atom::Var(var))?;
                let let_expr = expr_at(
                    expr.span,
                    body.ty.clone(),
                    ExprKind::Let {
                        bind: var,
                        ty: expr.ty.clone().into(),
                        value: simple,
                        body: Box::new(body),
                    },
                );
                Ok(Self::wrap_bindings(bindings, let_expr))
            }
            LoweredValue::Expr(compound) => {
                if expr.ty.is_never() {
                    return Ok(compound);
                }
                let var = self.fresh_var();
                let body = cont(self, Atom::Var(var))?;
                Ok(self.inline_compound_let(var, expr.ty.clone(), compound, body))
            }
        }
    }

    /// Lower N expressions to atoms left-to-right, then call `cont` with all atoms.
    pub(super) fn lower_atoms_then<F>(
        &mut self,
        exprs: &[TypedExpr],
        acc: Vec<Atom>,
        cont: F,
    ) -> Result<Expr, LowerError>
    where
        F: FnOnce(&mut Self, Vec<Atom>) -> Result<Expr, LowerError>,
    {
        if exprs.is_empty() {
            return cont(self, acc);
        }
        self.lower_to_atom_then(&exprs[0], |ctx, atom| {
            let mut acc = acc;
            acc.push(atom);
            ctx.lower_atoms_then(&exprs[1..], acc, cont)
        })
    }

    pub(super) fn lower_variant_constructor_as_value(
        &mut self,
        name: &str,
        expr: &TypedExpr,
        type_qn: &QualifiedName,
        tag: u32,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        let (param_types, return_type) = match &expr.ty {
            Type::Fn(param_types, return_type) => {
                let stripped: Vec<krypton_typechecker::types::Type> =
                    param_types.iter().map(|(_, t)| t.clone()).collect();
                (stripped, return_type.as_ref().clone())
            }
            other => {
                return Err(LowerError::InternalError(format!(
                    "constructor value `{name}` has non-function type: {other:?}"
                )))
            }
        };

        let fn_id = self.fresh_fn();
        let lifted_name = format!("ctor${}${}", name, fn_id.0);
        let mut params = Vec::with_capacity(param_types.len());
        let mut field_atoms = Vec::with_capacity(param_types.len());
        for param_ty in param_types {
            let var = self.fresh_var();
            params.push((var, param_ty.clone().into()));
            field_atoms.push(Atom::Var(var));
        }

        let result_var = self.fresh_var();
        let body = expr_at(
            expr.span,
            return_type.clone().into(),
            ExprKind::Let {
                bind: result_var,
                ty: return_type.clone().into(),
                value: simple_at(
                    expr.span,
                    SimpleExprKind::ConstructVariant {
                        type_ref: CanonicalRef {
                            module: ModulePath::new(type_qn.module_path.clone()),
                            symbol: LocalSymbolKey::Type(type_qn.local_name.clone()),
                        },
                        variant: name.to_string(),
                        tag,
                        fields: field_atoms,
                    },
                ),
                body: Box::new(atom_expr_at(
                    expr.span,
                    return_type.clone().into(),
                    Atom::Var(result_var),
                )),
            },
        );

        self.lifted_fns.push(FnDef {
            id: fn_id,
            name: lifted_name.clone(),
            exported_symbol: lifted_name.clone(),
            params,
            return_type: return_type.into(),
            body,
        });
        self.insert_synthetic_fn_id(lifted_name, fn_id);

        Ok((
            vec![],
            simple_at(
                expr.span,
                SimpleExprKind::MakeClosure {
                    func: fn_id,
                    captures: vec![],
                },
            ),
        ))
    }

    /// Lower a struct constructor used as a first-class value (e.g. `let mk = Player`).
    /// Creates a lifted function wrapping `Construct`, returns `MakeClosure`.
    pub(super) fn lower_struct_constructor_as_value(
        &mut self,
        constructor_name: &str,
        type_qn: &QualifiedName,
        expr: &TypedExpr,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        let (param_types, return_type) = match &expr.ty {
            Type::Fn(param_types, return_type) => {
                let stripped: Vec<krypton_typechecker::types::Type> =
                    param_types.iter().map(|(_, t)| t.clone()).collect();
                (stripped, return_type.as_ref().clone())
            }
            other => {
                return Err(LowerError::InternalError(format!(
                    "struct constructor value `{constructor_name}` has non-function type: {other:?}"
                )))
            }
        };

        let fn_id = self.fresh_fn();
        let lifted_name = format!("ctor${}${}", constructor_name, fn_id.0);
        let mut params = Vec::with_capacity(param_types.len());
        let mut field_atoms = Vec::with_capacity(param_types.len());
        for param_ty in param_types {
            let var = self.fresh_var();
            params.push((var, param_ty.clone().into()));
            field_atoms.push(Atom::Var(var));
        }

        let result_var = self.fresh_var();
        let body = expr_at(
            expr.span,
            return_type.clone().into(),
            ExprKind::Let {
                bind: result_var,
                ty: return_type.clone().into(),
                value: simple_at(
                    expr.span,
                    SimpleExprKind::Construct {
                        type_ref: CanonicalRef {
                            module: ModulePath::new(type_qn.module_path.clone()),
                            symbol: LocalSymbolKey::Type(type_qn.local_name.clone()),
                        },
                        fields: field_atoms,
                    },
                ),
                body: Box::new(atom_expr_at(
                    expr.span,
                    return_type.clone().into(),
                    Atom::Var(result_var),
                )),
            },
        );

        self.lifted_fns.push(FnDef {
            id: fn_id,
            name: lifted_name.clone(),
            exported_symbol: lifted_name.clone(),
            params,
            return_type: return_type.into(),
            body,
        });
        self.insert_synthetic_fn_id(lifted_name, fn_id);

        Ok((
            vec![],
            simple_at(
                expr.span,
                SimpleExprKind::MakeClosure {
                    func: fn_id,
                    captures: vec![],
                },
            ),
        ))
    }

    /// Lower an expression to a SimpleExpr (one step of computation).
    /// Returns prefix let-bindings and the SimpleExpr.
    pub(super) fn lower_to_simple(
        &mut self,
        expr: &TypedExpr,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        match &expr.kind {
            TypedExprKind::Discharge(_) | TypedExprKind::Lit(_) => {
                // Atoms — callers should use lower_to_atom instead
                Err(LowerError::InternalError(
                    "lower_to_simple called on Lit/Discharge (use lower_to_atom)".to_string(),
                ))
            }
            TypedExprKind::Var(name) => {
                if let Some((_binding_name, constructor_ref)) = resolved_constructor_ref(expr) {
                    match constructor_ref.kind {
                        typed_ast::ConstructorKind::Variant => {
                            let variant_ref = variant_ref_from_constructor(constructor_ref)
                                .ok_or_else(|| {
                                    LowerError::InternalError(format!(
                                        "missing variant ref for constructor `{}`",
                                        constructor_ref.constructor_name
                                    ))
                                })?;
                            let (tag, fields) = self.variant_info(&variant_ref)?;
                            let type_cref = self.type_canonical_ref(&constructor_ref.type_ref);
                            if fields.is_empty() {
                                return Ok((
                                    vec![],
                                    simple_at(
                                        expr.span,
                                        SimpleExprKind::ConstructVariant {
                                            type_ref: type_cref,
                                            variant: constructor_ref.constructor_name.clone(),
                                            tag,
                                            fields: vec![],
                                        },
                                    ),
                                ));
                            }
                            return self.lower_variant_constructor_as_value(
                                &constructor_ref.constructor_name,
                                expr,
                                &constructor_ref.type_ref.qualified_name,
                                tag,
                            );
                        }
                        typed_ast::ConstructorKind::Record => {
                            return self.lower_struct_constructor_as_value(
                                &constructor_ref.constructor_name,
                                &constructor_ref.type_ref.qualified_name,
                                expr,
                            );
                        }
                    }
                }
                if let Some(variant_ref) = self.fallback_variant_ref(name) {
                    let (tag, fields) = self.variant_info(&variant_ref)?;
                    let type_cref = self.type_canonical_ref(&variant_ref.type_ref);
                    if fields.is_empty() {
                        return Ok((
                            vec![],
                            simple_at(
                                expr.span,
                                SimpleExprKind::ConstructVariant {
                                    type_ref: type_cref,
                                    variant: name.clone(),
                                    tag,
                                    fields: vec![],
                                },
                            ),
                        ));
                    }
                    return self.lower_variant_constructor_as_value(
                        name,
                        expr,
                        &variant_ref.type_ref.qualified_name,
                        tag,
                    );
                }
                if let Some(type_ref) = self.fallback_type_ref(name) {
                    return self.lower_struct_constructor_as_value(
                        name,
                        &type_ref.qualified_name,
                        expr,
                    );
                }
                // Function reference as value — wrap in MakeClosure
                if let Some((_binding_name, callable_ref)) = resolved_callable_ref(expr) {
                    let qn = callable_qualified_name(callable_ref, &self.module_path);
                    let sig = callable_overload_signature(callable_ref);
                    let Some(fn_id) = self.lookup_callable(&qn, sig) else {
                        return Err(LowerError::UnresolvedVar(name.to_string()));
                    };
                    // Functions without trait constraints have no entry
                    let constraints = self.fn_constraints.get(&qn).cloned().unwrap_or_default();
                    if !constraints.is_empty() {
                        return self.lower_constrained_fn_as_value(
                            &qn,
                            fn_id,
                            &constraints,
                            &[],
                            &expr.ty,
                        );
                    }
                    return Ok((
                        vec![],
                        simple_at(
                            expr.span,
                            SimpleExprKind::MakeClosure {
                                func: fn_id,
                                captures: vec![],
                            },
                        ),
                    ));
                }
                // Trait method used as value
                if let Some(trait_ref) = resolved_trait_method_ref(expr) {
                    return self.lower_trait_method_as_value(
                        &trait_ref.trait_name,
                        &trait_ref.method_name,
                        &expr.ty,
                        &[],
                    );
                }
                // Should not reach here for a plain var (those are atoms)
                Err(LowerError::InternalError(format!(
                    "lower_to_simple called on plain Var({name})"
                )))
            }
            TypedExprKind::TypeApp {
                expr: inner,
                type_bindings,
            } => {
                // For trait method values, use the outer (concrete) type from the TypeApp
                if let Some(trait_ref) = resolved_trait_method_ref(expr) {
                    return self.lower_trait_method_as_value(
                        &trait_ref.trait_name,
                        &trait_ref.method_name,
                        &expr.ty,
                        type_bindings,
                    );
                }
                if let Some((_binding_name, callable_ref)) = resolved_callable_ref(expr) {
                    // Constrained function reference with explicit type args
                    let qn = callable_qualified_name(callable_ref, &self.module_path);
                    let sig = callable_overload_signature(callable_ref);
                    if let Some(fn_id) = self.lookup_callable(&qn, sig) {
                        // Functions without trait constraints have no entry
                        let constraints = self.fn_constraints.get(&qn).cloned().unwrap_or_default();
                        if !constraints.is_empty() {
                            return self.lower_constrained_fn_as_value(
                                &qn,
                                fn_id,
                                &constraints,
                                type_bindings,
                                &expr.ty,
                            );
                        }
                    }
                }
                self.lower_to_simple(inner)
            }
            TypedExprKind::BinaryOp {
                op:
                    BinOp::And
                    | BinOp::Or
                    | BinOp::Eq
                    | BinOp::Neq
                    | BinOp::Lt
                    | BinOp::Gt
                    | BinOp::Le
                    | BinOp::Ge,
                ..
            } => Err(LowerError::InternalError(
                "And/Or/comparison ops must be lowered as compound expr".to_string(),
            )),
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let lhs_ty = strip_own(&lhs.ty);
                if let Ok(prim_op) = resolve_binop(op, lhs_ty) {
                    let (mut bindings, lhs_atom) = self.lower_to_atom(lhs)?;
                    let (rhs_bindings, rhs_atom) = self.lower_to_atom(rhs)?;
                    bindings.extend(rhs_bindings);
                    Ok((
                        bindings,
                        simple_at(
                            expr.span,
                            SimpleExprKind::PrimOp {
                                op: prim_op,
                                args: vec![lhs_atom, rhs_atom],
                            },
                        ),
                    ))
                } else {
                    // Non-primitive: needs trait dispatch via lower_expr
                    Err(LowerError::CompoundInAtom)
                }
            }
            TypedExprKind::UnaryOp { op, operand } => {
                let operand_ty = strip_own(&operand.ty);
                if let Ok(prim_op) = resolve_unaryop(op, operand_ty) {
                    let (bindings, atom) = self.lower_to_atom(operand)?;
                    Ok((
                        bindings,
                        simple_at(
                            expr.span,
                            SimpleExprKind::PrimOp {
                                op: prim_op,
                                args: vec![atom],
                            },
                        ),
                    ))
                } else {
                    // Non-primitive: needs trait dispatch via lower_expr
                    Err(LowerError::CompoundInAtom)
                }
            }
            TypedExprKind::App { func, args, .. } => self.lower_app(func, args),
            TypedExprKind::Tuple(elems) => {
                let mut bindings = vec![];
                let mut atoms = vec![];
                for elem in elems {
                    let (bs, atom) = self.lower_to_atom(elem)?;
                    bindings.extend(bs);
                    atoms.push(atom);
                }
                Ok((
                    bindings,
                    simple_at(expr.span, SimpleExprKind::MakeTuple { elements: atoms }),
                ))
            }
            TypedExprKind::StructLit {
                name,
                fields,
                resolved_type_ref,
            } => self.lower_struct_lit(name, fields, resolved_type_ref.as_ref()),
            TypedExprKind::FieldAccess {
                expr: base,
                field,
                resolved_type_ref,
            } => {
                let (bindings, base_atom) = self.lower_to_atom(base)?;
                let type_ref = resolved_type_ref
                    .clone()
                    .or_else(|| self.resolved_type_ref_from_type(&base.ty))
                    .ok_or_else(|| {
                        LowerError::InternalError(format!(
                            "FieldAccess on non-named type: {:?}",
                            base.ty
                        ))
                    })?;
                let idx = self.field_index(&type_ref, field)?;
                Ok((
                    bindings,
                    simple_at(
                        expr.span,
                        SimpleExprKind::Project {
                            value: base_atom,
                            field_index: idx,
                        },
                    ),
                ))
            }
            // Complex expressions that produce full Expr trees rather than SimpleExpr:
            // Wrap them by lowering to Expr, binding the result to a fresh var.
            TypedExprKind::If { .. }
            | TypedExprKind::Let { .. }
            | TypedExprKind::Do(_)
            | TypedExprKind::StructUpdate { .. } => {
                // These produce full Expr trees, not SimpleExpr directly.
                // We need to lower them as Expr and extract the result.
                // This is handled by lower_expr; callers should use lower_to_atom
                // which will create a binding.
                Err(LowerError::InternalError(format!(
                    "lower_to_simple called on compound expr {:?}",
                    std::mem::discriminant(&expr.kind)
                )))
            }
            TypedExprKind::Lambda { params, body } => self.lower_lambda(params, body, &expr.ty),
            TypedExprKind::Match { .. } | TypedExprKind::LetPattern { .. } => {
                // These are compound expressions — must go through lower_expr
                Err(LowerError::InternalError(format!(
                    "lower_to_simple called on compound expr {:?}",
                    std::mem::discriminant(&expr.kind)
                )))
            }
            TypedExprKind::Recur { .. } | TypedExprKind::QuestionMark { .. } => {
                // These are compound expressions — must go through lower_expr
                Err(LowerError::InternalError(format!(
                    "lower_to_simple called on compound expr {:?}",
                    std::mem::discriminant(&expr.kind)
                )))
            }
            TypedExprKind::VecLit(elems) => {
                let mut bindings = vec![];
                let mut atoms = vec![];
                for elem in elems {
                    let (bs, atom) = self.lower_to_atom(elem)?;
                    bindings.extend(bs);
                    atoms.push(atom);
                }
                let element_type = extract_vec_element_type(&expr.ty)?;
                Ok((
                    bindings,
                    simple_at(
                        expr.span,
                        SimpleExprKind::MakeVec {
                            element_type: element_type.into(),
                            elements: atoms,
                        },
                    ),
                ))
            }
        }
    }
    // -----------------------------------------------------------------------
    // Compound expression helpers
    // -----------------------------------------------------------------------

    /// Try to lower a value expression as either a SimpleExpr (for direct Let binding)
    /// or as a full Expr (for compound expressions like If, Do, nested Let, or atoms).
    pub(super) fn try_lower_as_simple(&mut self, expr: &TypedExpr) -> Result<LoweredValue, LowerError> {
        match &expr.kind {
            // Atoms (Lit, Var) produce Simple bindings directly
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {
                let (bindings, atom) = self.lower_to_atom(expr)?;
                Ok(LoweredValue::Simple(
                    bindings,
                    simple_at(expr.span, SimpleExprKind::Atom(atom)),
                ))
            }
            // Compound expressions and short-circuit ops produce Expr trees
            TypedExprKind::If { .. }
            | TypedExprKind::Do(_)
            | TypedExprKind::Let { .. }
            | TypedExprKind::Match { .. }
            | TypedExprKind::LetPattern { .. }
            | TypedExprKind::StructUpdate { .. }
            | TypedExprKind::Recur { .. }
            | TypedExprKind::QuestionMark { .. }
            | TypedExprKind::BinaryOp {
                op: BinOp::And | BinOp::Or,
                ..
            }
            | TypedExprKind::BinaryOp {
                op: BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge,
                ..
            } => {
                let e = self.lower_expr(expr)?;
                Ok(LoweredValue::Expr(e))
            }
            // Everything else can be lowered to SimpleExpr
            _ => match self.lower_to_simple(expr) {
                Ok((bindings, simple)) => Ok(LoweredValue::Simple(bindings, simple)),
                Err(LowerError::CompoundInAtom) => {
                    let e = self.lower_expr(expr)?;
                    Ok(LoweredValue::Expr(e))
                }
                Err(e) => Err(e),
            },
        }
    }

    /// Handle `let x = <compound_expr> in body` where compound_expr produces
    /// a full Expr tree (If, Do, nested Let).
    ///
    /// Lowers to:
    /// ```text
    /// let_join j(x: T) = body
    /// in <compound with tails replaced by jump j(tail_value)>
    /// ```
    pub(super) fn inline_compound_let(
        &mut self,
        bind: VarId,
        bind_ty: Type,
        value_expr: Expr,
        body: Expr,
    ) -> Expr {
        let join_name = self.fresh_var();
        let result_ty = body.ty.clone();
        let rewritten = replace_tail_with_jump(value_expr, join_name);
        expr_at(
            rewritten.span,
            result_ty.clone(),
            ExprKind::LetJoin {
                name: join_name,
                params: vec![(bind, bind_ty.into())],
                join_body: Box::new(body),
                body: Box::new(rewritten),
                is_recur: false,
            },
        )
    }
}
