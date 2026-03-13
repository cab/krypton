use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Expr, Lit, Span, UnaryOp};

use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{TypedExpr, TypedExprKind, TypedMatchArm};
use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{unify, SpannedTypeError, TypeError};

use super::QualifiedModuleBinding;

pub(crate) struct InferenceContext<'a> {
    pub(super) env: &'a mut TypeEnv,
    pub(super) subst: &'a mut Substitution,
    pub(super) gen: &'a mut TypeVarGen,
    pub(super) registry: Option<&'a TypeRegistry>,
    pub(super) recur_params: Option<&'a [Type]>,
    pub(super) let_own_spans: Option<&'a mut HashSet<Span>>,
    pub(super) lambda_own_captures: Option<&'a mut HashMap<Span, String>>,
    pub(super) type_param_map: &'a HashMap<String, TypeVarId>,
    pub(super) type_param_arity: &'a HashMap<String, usize>,
    pub(super) qualified_modules: &'a HashMap<String, QualifiedModuleBinding>,
}

impl<'a> InferenceContext<'a> {
    pub fn unify_spanned(&mut self, t1: &Type, t2: &Type, span: Span) -> Result<(), SpannedTypeError> {
        unify(t1, t2, self.subst).map_err(|e| super::spanned(e, span))
    }

    pub fn resolve_type_expr_spanned(
        &self,
        ty_expr: &krypton_parser::ast::TypeExpr,
        span: Span,
    ) -> Result<Type, SpannedTypeError> {
        let reg = self.registry.ok_or_else(|| {
            super::spanned(
                TypeError::UnsupportedExpr {
                    description: "type expression requires the type registry".to_string(),
                },
                span,
            )
        })?;
        type_registry::resolve_type_expr(ty_expr, self.type_param_map, self.type_param_arity, reg)
            .map_err(|e| super::spanned(e, span))
    }

    pub fn unwrap_own_fn(&self, ty: &Type) -> Type {
        match ty {
            Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)) => *inner.clone(),
            other => other.clone(),
        }
    }

    pub fn extract_fn_params(&self, ty: &Type) -> Option<Vec<Type>> {
        match ty {
            Type::Fn(params, _) => Some(params.clone()),
            Type::Own(inner) => match inner.as_ref() {
                Type::Fn(params, _) => Some(params.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Shared tail for qualified-call paths: infer args with lambda expected-type
    /// propagation, coerce own args, unify, and build `TypedExpr::App`.
    fn infer_call_args_and_unify(
        &mut self,
        func_typed: TypedExpr,
        func_ty: &Type,
        args: &[Expr],
        is_constructor: bool,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let func_param_types = self.extract_fn_params(func_ty);
        let mut args_typed = Vec::new();
        let mut arg_types = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let arg_expected_type = if matches!(a, Expr::Lambda { .. }) {
                func_param_types.as_ref().and_then(|fparams| {
                    fparams
                        .get(i)
                        .map(|expected_arg_ty| self.subst.apply(expected_arg_ty))
                })
            } else {
                None
            };
            let a_typed = self.infer_expr_inner(
                a,
                arg_expected_type.as_ref(),
            )?;
            arg_types.push(a_typed.ty.clone());
            args_typed.push(a_typed);
        }

        let ret_var = Type::Var(self.fresh());
        let coerced_args = if is_constructor {
            arg_types.clone()
        } else {
            super::coerce_own_args(func_ty, &arg_types, self.subst)
        };
        let expected_fn = Type::Fn(coerced_args, Box::new(ret_var.clone()));
        let unwrapped_func_ty = self.unwrap_own_fn(&self.subst.apply(func_ty));
        self.unify_spanned(&unwrapped_func_ty, &expected_fn, span)?;
        let ty = self.subst.apply(&ret_var);
        Ok(TypedExpr {
            kind: TypedExprKind::App {
                func: Box::new(func_typed),
                args: args_typed,
            },
            ty: if is_constructor {
                Type::Own(Box::new(ty))
            } else {
                ty
            },
            span,
        })
    }

    pub fn fresh(&mut self) -> TypeVarId {
        self.gen.fresh()
    }

    pub(crate) fn infer_expr_inner(
        &mut self,
        expr: &Expr,
        expected_type: Option<&Type>,
    ) -> Result<TypedExpr, SpannedTypeError> {
        match expr {
            Expr::Lit { value, span } => {
                let ty = match value {
                    Lit::Int(_) => Type::Int,
                    Lit::Float(_) => Type::Float,
                    Lit::Bool(_) => Type::Bool,
                    Lit::String(_) => Type::String,
                    Lit::Unit => Type::Unit,
                };
                Ok(TypedExpr {
                    kind: TypedExprKind::Lit(value.clone()),
                    ty: Type::Own(Box::new(ty)),
                    span: *span,
                })
            }

            Expr::Var { name, span, .. } => match self.env.lookup(name) {
                Some(scheme) => {
                    let scheme = scheme.clone();
                    let ty = scheme.instantiate(&mut || self.gen.fresh());
                    let ty = if !matches!(&ty, Type::Fn(_, _))
                        && self.registry.is_some_and(|r| r.is_constructor(name))
                    {
                        Type::Own(Box::new(ty))
                    } else {
                        ty
                    };
                    Ok(TypedExpr {
                        kind: TypedExprKind::Var(name.clone()),
                        ty,
                        span: *span,
                    })
                }
                None => {
                    if let Some(binding) = self.qualified_modules.get(name) {
                        Err(super::spanned(
                            TypeError::ModuleQualifierUsedAsValue {
                                qualifier: name.clone(),
                                suggested_usage: super::qualifier_suggested_usage(name, binding),
                            },
                            *span,
                        ))
                    } else {
                        Err(super::spanned(
                            TypeError::UnknownVariable { name: name.clone() },
                            *span,
                        ))
                    }
                }
            },

            Expr::Lambda {
                params, body, span, ..
            } => {
                // Extract expected parameter types from the expected_type if it's a function type.
                let expected_params: Option<&[Type]> = expected_type.and_then(|et| {
                    let unwrapped = match et {
                        Type::Own(inner) => inner.as_ref(),
                        other => other,
                    };
                    match unwrapped {
                        Type::Fn(params, _) => Some(params.as_slice()),
                        _ => None,
                    }
                });
                let mut param_types = Vec::new();
                self.env.push_scope();
                for (i, p) in params.iter().enumerate() {
                    let tv = Type::Var(self.fresh());
                    if let Some(expected) = expected_params {
                        if let Some(expected_ty) = expected.get(i) {
                            let _ = unify(&tv, expected_ty, self.subst);
                        }
                    }
                    param_types.push(tv.clone());
                    self.env.bind(p.name.clone(), TypeScheme::mono(tv));
                }
                // Save and set an independent fn_return_type for this lambda.
                // Lambdas need their own return type so the `?` operator inside
                // a lambda targets the lambda's return, not the enclosing function's.
                let prev_fn_return_type = self.env.fn_return_type.take();
                self.env.fn_return_type = Some(Type::Var(self.fresh()));
                let saved_recur = self.recur_params.take();
                let body_typed = self.infer_expr_inner(body, None)?;
                self.recur_params = saved_recur;
                self.env.fn_return_type = prev_fn_return_type;
                self.env.pop_scope();
                let param_types: Vec<Type> = param_types.iter().map(|t| self.subst.apply(t)).collect();
                let body_ty = self.subst.apply(&body_typed.ty);
                let fn_ty = Type::Fn(param_types, Box::new(body_ty));
                let param_names: HashSet<&str> = params.iter().map(|p| p.name.as_str()).collect();
                let ty = if let Some(cap_name) = super::first_own_capture(body, &param_names, self.env, self.subst) {
                    if let Some(ref mut captures) = self.lambda_own_captures {
                        captures.insert(*span, cap_name);
                    }
                    Type::Own(Box::new(fn_ty))
                } else {
                    fn_ty
                };
                let kind = TypedExprKind::Lambda {
                    params: params.iter().map(|p| p.name.clone()).collect(),
                    body: Box::new(body_typed),
                };
                Ok(TypedExpr {
                    kind,
                    ty,
                    span: *span,
                })
            }

            Expr::App {
                func, args, span, ..
            } => {
                let qualified_call = match (func.as_ref(), args.first()) {
                    (
                        Expr::Var { name: export_name, .. },
                        Some(Expr::Var {
                            name: qualifier, ..
                        }),
                    ) => Some((qualifier.clone(), export_name.clone(), Vec::new())),
                    (
                        Expr::TypeApp {
                            expr,
                            type_args,
                            ..
                        },
                        Some(Expr::Var {
                            name: qualifier, ..
                        }),
                    ) => match expr.as_ref() {
                        Expr::Var { name: export_name, .. } => Some((
                            qualifier.clone(),
                            export_name.clone(),
                            type_args.clone(),
                        )),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((qualifier, export_name, explicit_type_args)) = qualified_call {
                    if self.env.lookup(&qualifier).is_none() {
                        if let Some(binding) = self.qualified_modules.get(&qualifier) {
                            let Some(export) = binding.exports.get(&export_name) else {
                                return Err(super::spanned(
                                    TypeError::UnknownQualifiedExport {
                                        qualifier,
                                        module_path: binding.module_path.clone(),
                                        name: export_name,
                                    },
                                    *span,
                                ));
                            };

                            let is_constructor =
                                self.registry.is_some_and(|r| r.is_constructor(&export_name));
                            let resolved_name = if is_constructor {
                                export_name.clone()
                            } else {
                                export.local_name.clone()
                            };
                            let func_ty = if explicit_type_args.is_empty() {
                                export.scheme.instantiate(&mut || self.gen.fresh())
                            } else {
                                let reg = self.registry.ok_or_else(|| {
                                    super::spanned(
                                        TypeError::UnsupportedExpr {
                                            description:
                                                "explicit type application requires the type registry"
                                                    .to_string(),
                                        },
                                        *span,
                                    )
                                })?;
                                let explicit_types = explicit_type_args
                                    .iter()
                                    .map(|type_arg| {
                                        type_registry::resolve_type_expr(
                                            type_arg,
                                            self.type_param_map,
                                            self.type_param_arity,
                                            reg,
                                        )
                                        .map_err(|e| super::spanned(e, *span))
                                    })
                                    .collect::<Result<Vec<_>, _>>()?;
                                super::instantiate_scheme_with_types(
                                    &export.scheme,
                                    &explicit_types,
                                    *span,
                                    self.gen,
                                )?
                            };
                            let func_typed = TypedExpr {
                                kind: TypedExprKind::Var(resolved_name),
                                ty: func_ty.clone(),
                                span: *span,
                            };
                            let actual_args = &args[1..];
                            return self.infer_call_args_and_unify(
                                func_typed,
                                &func_ty,
                                actual_args,
                                is_constructor,
                                *span,
                            );
                        }
                    }
                }

                if let Expr::FieldAccess {
                    expr: qualifier_expr,
                    field,
                    ..
                } = func.as_ref()
                {
                    if let Expr::Var {
                        name: qualifier, ..
                    } = qualifier_expr.as_ref()
                    {
                        if self.env.lookup(qualifier).is_none() {
                            if let Some(binding) = self.qualified_modules.get(qualifier) {
                                let Some(export) = binding.exports.get(field) else {
                                    return Err(super::spanned(
                                        TypeError::UnknownQualifiedExport {
                                            qualifier: qualifier.clone(),
                                            module_path: binding.module_path.clone(),
                                            name: field.clone(),
                                        },
                                        *span,
                                    ));
                                };
                                let is_constructor =
                                    self.registry.is_some_and(|r| r.is_constructor(field));
                                let resolved_name = if is_constructor {
                                    field.clone()
                                } else {
                                    export.local_name.clone()
                                };
                                let func_ty = export.scheme.instantiate(&mut || self.gen.fresh());
                                let func_typed = TypedExpr {
                                    kind: TypedExprKind::Var(resolved_name),
                                    ty: if is_constructor && !matches!(&func_ty, Type::Fn(_, _))
                                    {
                                        Type::Own(Box::new(func_ty.clone()))
                                    } else {
                                        func_ty.clone()
                                    },
                                    span: *span,
                                };

                                return self.infer_call_args_and_unify(
                                    func_typed,
                                    &func_ty,
                                    args,
                                    is_constructor,
                                    *span,
                                );
                            }
                        }
                    }
                }

                let func_typed = self.infer_expr_inner(func, None)?;
                // Extract expected parameter types from the function signature
                // so we can propagate them into lambda arguments for bidirectional checking.
                let func_param_types: Option<Vec<Type>> = {
                    let resolved_func_ty = self.subst.apply(&func_typed.ty);
                    let unwrapped = match &resolved_func_ty {
                        Type::Own(inner) => inner.as_ref(),
                        other => other,
                    };
                    if let Type::Fn(params, _) = unwrapped {
                        Some(params.clone())
                    } else {
                        None
                    }
                };

                let mut args_typed = Vec::new();
                let mut arg_types = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    // For lambda arguments, resolve the expected parameter type from the
                    // function signature and pass it as expected_type for bidirectional checking.
                    let arg_expected_type = if matches!(a, Expr::Lambda { .. }) {
                        func_param_types.as_ref().and_then(|fparams| {
                            fparams
                                .get(i)
                                .map(|expected_arg_ty| self.subst.apply(expected_arg_ty))
                        })
                    } else {
                        None
                    };
                    let a_typed = self.infer_expr_inner(
                        a,
                        arg_expected_type.as_ref(),
                    )?;
                    let a_ty = a_typed.ty.clone();
                    arg_types.push(a_ty.clone());
                    args_typed.push(a_typed);
                    // Eagerly unify non-lambda args with their expected parameter types.
                    // This resolves generic type variables (e.g., T -> Player) before
                    // we process subsequent lambda arguments that depend on them.
                    if !matches!(a, Expr::Lambda { .. }) {
                        if let Some(ref fparams) = func_param_types {
                            if let Some(expected_param_ty) = fparams.get(i) {
                                let _ = unify(expected_param_ty, &a_ty, self.subst);
                            }
                        }
                    }
                }

                if super::is_concrete_non_function(&func_typed.ty, self.subst) {
                    let actual = self.subst.apply(&func_typed.ty);
                    return Err(super::spanned(TypeError::NotAFunction { actual }, *span));
                }

                let ret_var = Type::Var(self.fresh());
                let is_constructor = if let Expr::Var { name, .. } = func.as_ref() {
                    self.registry.is_some_and(|r| r.is_constructor(name))
                } else {
                    false
                };
                let coerced_args = if is_constructor {
                    arg_types.clone()
                } else {
                    super::coerce_own_args(&func_typed.ty, &arg_types, self.subst)
                };
                let expected_fn = Type::Fn(coerced_args, Box::new(ret_var.clone()));
                let unwrapped_func_ty = self.unwrap_own_fn(&self.subst.apply(&func_typed.ty));
                unify(&unwrapped_func_ty, &expected_fn, self.subst).map_err(|e| {
                    let mut err = super::spanned(e, *span);
                    if matches!(&err.error, TypeError::Mismatch { .. }) {
                        if let Some(ref captures) = self.lambda_own_captures {
                            for arg in args.iter() {
                                if let Expr::Lambda { span: lspan, .. } = arg {
                                    if let Some(cap_name) = captures.get(lspan) {
                                        err.note = Some(format!(
                                            "closure is single-use because it captures own value `{}`",
                                            cap_name
                                        ));
                                        break;
                                    }
                                }
                            }
                        }
                    }
                    err
                })?;
                let ty = self.subst.apply(&ret_var);
                let ty = if is_constructor {
                    Type::Own(Box::new(ty))
                } else {
                    ty
                };
                Ok(TypedExpr {
                    kind: TypedExprKind::App {
                        func: Box::new(func_typed),
                        args: args_typed,
                    },
                    ty,
                    span: *span,
                })
            }

            Expr::TypeApp {
                expr,
                type_args,
                span,
            } => {
                let expr_typed = self.infer_expr_inner(expr, None)?;

                let explicit_types = if let Some(reg) = self.registry {
                    type_args
                        .iter()
                        .map(|type_arg| {
                            type_registry::resolve_type_expr(
                                type_arg,
                                self.type_param_map,
                                self.type_param_arity,
                                reg,
                            )
                            .map_err(|e| super::spanned(e, *span))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                } else {
                    return Err(super::spanned(
                        TypeError::UnsupportedExpr {
                            description: "explicit type application requires the type registry"
                                .to_string(),
                        },
                        *span,
                    ));
                };

                let specialized_ty = match expr.as_ref() {
                    Expr::Var { name, .. } => {
                        let Some(scheme) = self.env.lookup(name).cloned() else {
                            return Err(super::spanned(
                                TypeError::UnknownVariable { name: name.clone() },
                                *span,
                            ));
                        };
                        super::instantiate_scheme_with_types(&scheme, &explicit_types, *span, self.gen)?
                    }
                    _ => {
                        return Err(super::spanned(
                            TypeError::UnsupportedExpr {
                                description:
                                    "explicit type arguments are only supported on named values"
                                        .to_string(),
                            },
                            *span,
                        ))
                    }
                };

                Ok(TypedExpr {
                    kind: TypedExprKind::TypeApp {
                        expr: Box::new(expr_typed),
                    },
                    ty: specialized_ty,
                    span: *span,
                })
            }

            Expr::Let {
                name,
                ty: ty_ann,
                value,
                body,
                span,
            } => {
                let val_typed = self.infer_expr_inner(value, None)?;

                // If there's a type annotation, resolve it and unify with the inferred type
                if let Some(ty_expr) = ty_ann {
                    if self.registry.is_some() {
                        let annotated_ty = self.resolve_type_expr_spanned(ty_expr, *span)?;
                        self.unify_spanned(&val_typed.ty, &annotated_ty, *span)?;
                    }
                }

                let resolved_val = self.subst.apply(&val_typed.ty);
                if matches!(&resolved_val, Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)))
                {
                    if let Some(ref mut los) = self.let_own_spans {
                        los.insert(*span);
                    }
                }
                match body {
                    Some(body) => {
                        let scheme = super::generalize(&val_typed.ty, self.env, self.subst);
                        self.env.push_scope();
                        self.env.bind(name.clone(), scheme);
                        let body_typed = self.infer_expr_inner(body, None)?;
                        self.env.pop_scope();
                        let ty = body_typed.ty.clone();
                        Ok(TypedExpr {
                            kind: TypedExprKind::Let {
                                name: name.clone(),
                                value: Box::new(val_typed),
                                body: Some(Box::new(body_typed)),
                            },
                            ty,
                            span: *span,
                        })
                    }
                    None => {
                        let scheme = super::generalize(&val_typed.ty, self.env, self.subst);
                        self.env.bind(name.clone(), scheme);
                        Ok(TypedExpr {
                            kind: TypedExprKind::Let {
                                name: name.clone(),
                                value: Box::new(val_typed),
                                body: None,
                            },
                            ty: Type::Unit,
                            span: *span,
                        })
                    }
                }
            }

            Expr::If {
                cond,
                then_,
                else_,
                span,
                ..
            } => {
                let cond_typed = self.infer_expr_inner(cond, None)?;
                self.unify_spanned(&cond_typed.ty, &Type::Bool, *span)?;
                let then_typed = self.infer_expr_inner(then_, None)?;
                let else_typed = self.infer_expr_inner(else_, None)?;
                self.unify_spanned(&then_typed.ty, &else_typed.ty, *span)?;
                let ty = self.subst.apply(&then_typed.ty);
                Ok(TypedExpr {
                    kind: TypedExprKind::If {
                        cond: Box::new(cond_typed),
                        then_: Box::new(then_typed),
                        else_: Box::new(else_typed),
                    },
                    ty,
                    span: *span,
                })
            }

            Expr::Do { exprs, span } => {
                self.env.push_scope();
                if exprs.is_empty() {
                    self.env.pop_scope();
                    return Ok(TypedExpr {
                        kind: TypedExprKind::Do(Vec::new()),
                        ty: Type::Unit,
                        span: *span,
                    });
                }
                let mut typed_exprs = Vec::new();
                for e in exprs {
                    typed_exprs.push(self.infer_expr_inner(e, None)?);
                }
                self.env.pop_scope();
                let ty = typed_exprs.last().unwrap().ty.clone();
                Ok(TypedExpr {
                    kind: TypedExprKind::Do(typed_exprs),
                    ty,
                    span: *span,
                })
            }

            Expr::BinaryOp {
                op, lhs, rhs, span, ..
            } => {
                let lhs_typed = self.infer_expr_inner(lhs, None)?;
                let rhs_typed = self.infer_expr_inner(rhs, None)?;
                let ty = match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                        self.unify_spanned(&lhs_typed.ty, &rhs_typed.ty, *span)?;
                        let resolved = super::strip_own(&self.subst.apply(&lhs_typed.ty));
                        match &resolved {
                            Type::Var(_) => {
                                self.unify_spanned(&resolved, &Type::Int, *span)?;
                                Type::Int
                            }
                            _ => resolved,
                        }
                    }
                    BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        self.unify_spanned(&lhs_typed.ty, &rhs_typed.ty, *span)?;
                        let resolved = super::strip_own(&self.subst.apply(&lhs_typed.ty));
                        if let Type::Var(_) = &resolved {
                            self.unify_spanned(&resolved, &Type::Int, *span)?;
                        }
                        Type::Bool
                    }
                    BinOp::And | BinOp::Or => {
                        self.unify_spanned(&lhs_typed.ty, &Type::Bool, *span)?;
                        self.unify_spanned(&rhs_typed.ty, &Type::Bool, *span)?;
                        Type::Bool
                    }
                };
                Ok(TypedExpr {
                    kind: TypedExprKind::BinaryOp {
                        op: op.clone(),
                        lhs: Box::new(lhs_typed),
                        rhs: Box::new(rhs_typed),
                    },
                    ty,
                    span: *span,
                })
            }

            Expr::UnaryOp {
                op, operand, span, ..
            } => {
                let operand_typed = self.infer_expr_inner(operand, None)?;
                let ty = match op {
                    UnaryOp::Neg => {
                        let resolved = super::strip_own(&self.subst.apply(&operand_typed.ty));
                        match &resolved {
                            Type::Var(_) => {
                                self.unify_spanned(&resolved, &Type::Int, *span)?;
                                Type::Int
                            }
                            _ => resolved,
                        }
                    }
                    UnaryOp::Not => {
                        self.unify_spanned(&operand_typed.ty, &Type::Bool, *span)?;
                        Type::Bool
                    }
                };
                Ok(TypedExpr {
                    kind: TypedExprKind::UnaryOp {
                        op: op.clone(),
                        operand: Box::new(operand_typed),
                    },
                    ty,
                    span: *span,
                })
            }

            Expr::Recur { args, span, .. } => {
                let mut typed_args = Vec::new();
                match self.recur_params {
                    Some(params) => {
                        if args.len() != params.len() {
                            return Err(super::spanned(
                                TypeError::WrongArity {
                                    expected: params.len(),
                                    actual: args.len(),
                                },
                                *span,
                            ));
                        }
                        let params_owned: Vec<Type> = params.to_vec();
                        for (a, p) in args.iter().zip(params_owned.iter()) {
                            let a_typed = self.infer_expr_inner(a, None)?;
                            self.unify_spanned(&a_typed.ty, p, *span)?;
                            typed_args.push(a_typed);
                        }
                    }
                    None => {
                        for a in args {
                            let a_typed = self.infer_expr_inner(a, None)?;
                            typed_args.push(a_typed);
                        }
                    }
                }
                let ty = Type::Var(self.fresh());
                Ok(TypedExpr {
                    kind: TypedExprKind::Recur(typed_args),
                    ty,
                    span: *span,
                })
            }

            Expr::FieldAccess {
                expr: target,
                field,
                span,
            } => {
                if let Expr::Var { name: qualifier, .. } = target.as_ref() {
                    if self.env.lookup(qualifier).is_none() {
                        if let Some(binding) = self.qualified_modules.get(qualifier) {
                            let Some(export) = binding.exports.get(field) else {
                                return Err(super::spanned(
                                    TypeError::UnknownQualifiedExport {
                                        qualifier: qualifier.clone(),
                                        module_path: binding.module_path.clone(),
                                        name: field.clone(),
                                    },
                                    *span,
                                ));
                            };
                            let is_constructor = self.registry.is_some_and(|r| r.is_constructor(field));
                            let resolved_name = if is_constructor {
                                field.clone()
                            } else {
                                export.local_name.clone()
                            };
                            let export_ty = export.scheme.instantiate(&mut || self.gen.fresh());
                            let ty = if is_constructor && !matches!(&export_ty, Type::Fn(_, _))
                            {
                                Type::Own(Box::new(export_ty.clone()))
                            } else {
                                export_ty.clone()
                            };
                            return Ok(TypedExpr {
                                kind: TypedExprKind::Var(resolved_name),
                                ty,
                                span: *span,
                            });
                        }
                    }
                }
                let target_typed = self.infer_expr_inner(target, None)?;
                let resolved = self.subst.apply(&target_typed.ty);
                // Unwrap Own wrapper — field access works on the inner type
                let inner_resolved = match &resolved {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                let ty = self.resolve_field_access(inner_resolved, field, *span)?;
                Ok(TypedExpr {
                    kind: TypedExprKind::FieldAccess {
                        expr: Box::new(target_typed),
                        field: field.clone(),
                    },
                    ty,
                    span: *span,
                })
            }

            Expr::StructUpdate { base, fields, span } => {
                let base_typed = self.infer_expr_inner(base, None)?;
                let resolved = self.subst.apply(&base_typed.ty);
                // Unwrap Own wrapper — struct update works on the inner type
                let inner_resolved = match &resolved {
                    Type::Own(inner) => inner.as_ref().clone(),
                    other => other.clone(),
                };
                let typed_fields = self.resolve_struct_update(&inner_resolved, fields, *span)?;
                Ok(TypedExpr {
                    kind: TypedExprKind::StructUpdate {
                        base: Box::new(base_typed),
                        fields: typed_fields,
                    },
                    ty: resolved,
                    span: *span,
                })
            }

            Expr::Match {
                scrutinee,
                arms,
                span,
            } => {
                let scrutinee_typed = self.infer_expr_inner(scrutinee, None)?;
                let scrutinee_ty = self.subst.apply(&scrutinee_typed.ty);
                // Unwrap Own wrapper — match works on the inner type
                let match_ty = match &scrutinee_ty {
                    Type::Own(inner) => inner.as_ref().clone(),
                    other => other.clone(),
                };
                let result_ty = Type::Var(self.fresh());
                let mut typed_arms = Vec::new();
                for arm in arms {
                    self.env.push_scope();
                    let typed_pattern =
                        self.check_pattern(&arm.pattern, &match_ty, *span)?;
                    let body_typed = self.infer_expr_inner(&arm.body, None)?;
                    self.unify_spanned(&result_ty, &body_typed.ty, *span)?;
                    self.env.pop_scope();
                    typed_arms.push(TypedMatchArm {
                        pattern: typed_pattern,
                        body: body_typed,
                    });
                }
                let match_ty = self.subst.apply(&match_ty);
                crate::exhaustiveness::check_exhaustiveness(&match_ty, &typed_arms, self.registry, *span)?;
                let ty = self.subst.apply(&result_ty);
                Ok(TypedExpr {
                    kind: TypedExprKind::Match {
                        scrutinee: Box::new(scrutinee_typed),
                        arms: typed_arms,
                    },
                    ty,
                    span: *span,
                })
            }

            Expr::Tuple { elements, span } => {
                let mut typed_elems = Vec::new();
                for e in elements {
                    typed_elems.push(self.infer_expr_inner(e, None)?);
                }
                let ty = Type::Tuple(typed_elems.iter().map(|te| te.ty.clone()).collect());
                Ok(TypedExpr {
                    kind: TypedExprKind::Tuple(typed_elems),
                    ty,
                    span: *span,
                })
            }

            Expr::LetPattern {
                pattern,
                ty: ty_ann,
                value,
                body,
                span,
            } => {
                let val_typed = self.infer_expr_inner(value, None)?;

                // If there's a type annotation, resolve it and unify with the inferred type
                if let Some(ty_expr) = ty_ann {
                    if self.registry.is_some() {
                        let annotated_ty = self.resolve_type_expr_spanned(ty_expr, *span)?;
                        self.unify_spanned(&val_typed.ty, &annotated_ty, *span)?;
                    }
                }
                match body {
                    Some(body) => {
                        self.env.push_scope();
                        let typed_pattern = self.check_pattern(
                            pattern,
                            &self.subst.apply(&val_typed.ty),
                            *span,
                        )?;
                        let body_typed = self.infer_expr_inner(body, None)?;
                        self.env.pop_scope();
                        let ty = body_typed.ty.clone();
                        Ok(TypedExpr {
                            kind: TypedExprKind::LetPattern {
                                pattern: typed_pattern,
                                value: Box::new(val_typed),
                                body: Some(Box::new(body_typed)),
                            },
                            ty,
                            span: *span,
                        })
                    }
                    None => {
                        let typed_pattern = self.check_pattern(
                            pattern,
                            &self.subst.apply(&val_typed.ty),
                            *span,
                        )?;
                        Ok(TypedExpr {
                            kind: TypedExprKind::LetPattern {
                                pattern: typed_pattern,
                                value: Box::new(val_typed),
                                body: None,
                            },
                            ty: Type::Unit,
                            span: *span,
                        })
                    }
                }
            }

            Expr::StructLit { name, fields, span } => {
                let reg = self.registry
                    .ok_or_else(|| super::spanned(TypeError::UnknownVariable { name: name.clone() }, *span))?;
                let info = reg
                    .lookup_type(name)
                    .ok_or_else(|| super::spanned(TypeError::UnknownVariable { name: name.clone() }, *span))?;
                match &info.kind {
                    type_registry::TypeKind::Record {
                        fields: record_fields,
                    } => {
                        let fresh_args: Vec<Type> = info
                            .type_param_vars
                            .iter()
                            .map(|_| Type::Var(self.fresh()))
                            .collect();
                        let struct_ty = Type::Named(name.clone(), fresh_args.clone());

                        let provided: HashSet<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                        let missing: Vec<String> = record_fields
                            .iter()
                            .filter(|(n, _)| !provided.contains(n.as_str()))
                            .map(|(n, _)| n.clone())
                            .collect();
                        if !missing.is_empty() {
                            return Err(super::spanned(
                                TypeError::MissingFields {
                                    type_name: name.clone(),
                                    fields: missing,
                                },
                                *span,
                            ));
                        }

                        let mut typed_fields = Vec::new();
                        for (field_name, field_expr) in fields {
                            let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                            match record_field {
                                Some((_, expected_ty)) => {
                                    let expected =
                                        super::instantiate_field_type(expected_ty, info, &fresh_args);
                                    let field_typed = self.infer_expr_inner(field_expr, None)?;
                                    self.unify_spanned(&field_typed.ty, &expected, *span)?;
                                    typed_fields.push((field_name.clone(), field_typed));
                                }
                                None => {
                                    return Err(super::spanned(
                                        TypeError::UnknownField {
                                            type_name: name.clone(),
                                            field_name: field_name.clone(),
                                        },
                                        *span,
                                    ));
                                }
                            }
                        }

                        Ok(TypedExpr {
                            kind: TypedExprKind::StructLit {
                                name: name.clone(),
                                fields: typed_fields,
                            },
                            ty: Type::Own(Box::new(struct_ty)),
                            span: *span,
                        })
                    }
                    _ => Err(super::spanned(
                        TypeError::NotAStruct {
                            actual: Type::Named(name.clone(), vec![]),
                        },
                        *span,
                    )),
                }
            }

            Expr::List { elements, span } => {
                // Infer as Vec[a] — [e1, e2, e3] produces Vec[elem_type]
                let elem_var = Type::Var(self.fresh());
                let mut typed_elems = Vec::new();
                for elem in elements {
                    let typed = self.infer_expr_inner(elem, None)?;
                    self.unify_spanned(&self.subst.apply(&typed.ty), &self.subst.apply(&elem_var), *span)?;
                    typed_elems.push(typed);
                }
                let resolved_elem = self.subst.apply(&elem_var);
                Ok(TypedExpr {
                    kind: TypedExprKind::VecLit(typed_elems),
                    ty: Type::Named("Vec".to_string(), vec![resolved_elem]),
                    span: *span,
                })
            }
            Expr::QuestionMark { expr, span } => {
                let inner_typed = self.infer_expr_inner(expr, None)?;
                let inner_ty = self.subst.apply(&inner_typed.ty);
                // Strip Own wrapper for analysis
                let inner_ty_unwrapped = super::strip_own(&inner_ty);

                // Determine what kind of type the inner expr is
                let (is_option, unwrapped_ty) = match &inner_ty_unwrapped {
                    Type::Named(name, args) if name == "Option" && args.len() == 1 => {
                        (true, args[0].clone())
                    }
                    Type::Named(name, args) if name == "Result" && args.len() == 2 => {
                        (false, args[1].clone()) // Result[e, a] → unwraps to a
                    }
                    Type::Var(_) => {
                        // Inner type is unknown — try to constrain it based on return type
                        let fn_ret = self.env.fn_return_type.as_ref().map(|t| self.subst.apply(t));
                        match fn_ret.as_ref().map(super::strip_own) {
                            Some(Type::Named(name, _)) if name == "Option" => {
                                let a = Type::Var(self.fresh());
                                let option_ty = Type::Named("Option".to_string(), vec![a.clone()]);
                                self.unify_spanned(&inner_ty_unwrapped, &option_ty, *span)?;
                                (true, a)
                            }
                            Some(Type::Named(name, _)) if name == "Result" => {
                                let e = Type::Var(self.fresh());
                                let a = Type::Var(self.fresh());
                                let result_ty = Type::Named("Result".to_string(), vec![e, a.clone()]);
                                self.unify_spanned(&inner_ty_unwrapped, &result_ty, *span)?;
                                (false, a)
                            }
                            _ => {
                                // Return type also unknown — default to Result
                                let e = Type::Var(self.fresh());
                                let a = Type::Var(self.fresh());
                                let result_ty = Type::Named("Result".to_string(), vec![e, a.clone()]);
                                self.unify_spanned(&inner_ty_unwrapped, &result_ty, *span)?;
                                (false, a)
                            }
                        }
                    }
                    other => {
                        return Err(super::spanned(
                            TypeError::QuestionMarkBadOperand {
                                actual: other.clone(),
                            },
                            *span,
                        ));
                    }
                };

                // Now check that the function's return type is compatible
                let fn_ret = self.env.fn_return_type.as_ref().map(|t| self.subst.apply(t));
                let fn_ret_unwrapped = fn_ret.map(|t| super::strip_own(&t));

                match &fn_ret_unwrapped {
                    Some(Type::Named(name, args)) if name == "Option" => {
                        if !is_option {
                            return Err(super::spanned(
                                TypeError::QuestionMarkMismatch {
                                    expr_kind: "Result".to_string(),
                                    return_kind: "Option".to_string(),
                                },
                                *span,
                            ));
                        }
                        // Option ? in Option fn — OK. Unify inner type params if needed.
                        let _ = args; // already compatible
                    }
                    Some(Type::Named(name, args)) if name == "Result" => {
                        if is_option {
                            return Err(super::spanned(
                                TypeError::QuestionMarkMismatch {
                                    expr_kind: "Option".to_string(),
                                    return_kind: "Result".to_string(),
                                },
                                *span,
                            ));
                        }
                        // Result ? in Result fn — unify error types
                        if args.len() == 2 {
                            // inner expr is Result[e1, a], fn returns Result[e2, b] → unify e1 = e2
                            let inner_resolved = self.subst.apply(&inner_ty_unwrapped);
                            if let Type::Named(_, inner_args) = &inner_resolved {
                                if inner_args.len() == 2 {
                                    self.unify_spanned(&inner_args[0], &args[0], *span)?;
                                }
                            }
                        }
                    }
                    Some(Type::Var(_)) => {
                        // Return type is still a type var — constrain it
                        if is_option {
                            let b = Type::Var(self.fresh());
                            let option_ret = Type::Named("Option".to_string(), vec![b]);
                            if let Some(ref ret) = self.env.fn_return_type {
                                self.unify_spanned(&self.subst.apply(ret), &option_ret, *span)?;
                            }
                        } else {
                            // Result — unify return type as Result[e, b] with same error type
                            let inner_resolved = self.subst.apply(&inner_ty_unwrapped);
                            let err_ty = if let Type::Named(_, ref iargs) = inner_resolved {
                                if iargs.len() == 2 {
                                    iargs[0].clone()
                                } else {
                                    Type::Var(self.fresh())
                                }
                            } else {
                                Type::Var(self.fresh())
                            };
                            let b = Type::Var(self.fresh());
                            let result_ret = Type::Named("Result".to_string(), vec![err_ty, b]);
                            if let Some(ref ret) = self.env.fn_return_type {
                                self.unify_spanned(&self.subst.apply(ret), &result_ret, *span)?;
                            }
                        }
                    }
                    Some(other) => {
                        return Err(super::spanned(
                            TypeError::QuestionMarkBadReturn {
                                actual: other.clone(),
                            },
                            *span,
                        ));
                    }
                    None => {
                        return Err(super::spanned(
                            TypeError::QuestionMarkBadReturn { actual: Type::Unit },
                            *span,
                        ));
                    }
                }

                let result_ty = self.subst.apply(&unwrapped_ty);
                Ok(TypedExpr {
                    kind: TypedExprKind::QuestionMark {
                        expr: Box::new(inner_typed),
                        is_option,
                    },
                    ty: result_ty,
                    span: *span,
                })
            }
        }
    }

}
