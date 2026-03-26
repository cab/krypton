use krypton_parser::ast::{Expr, Lit, Pattern, Span};

use crate::type_registry;
use crate::typed_ast::{TypedExpr, TypedPattern};
use crate::types::{Type, TypeScheme};
use crate::unify::{SpannedTypeError, TypeError};

use super::expr::InferenceContext;

impl<'a> InferenceContext<'a> {
    /// Check a pattern against an expected type, binding variables in the environment.
    /// Returns a TypedPattern carrying resolved type information.
    ///
    /// `scrutinee_is_owned` controls coercion: when false (shared scrutinee), `~T` fields
    /// are coerced to `T` at binding sites, and `~fn` fields produce an error.
    pub(crate) fn check_pattern(
        &mut self,
        pattern: &Pattern,
        expected: &Type,
        span: Span,
        scrutinee_is_owned: bool,
    ) -> Result<TypedPattern, SpannedTypeError> {
        match pattern {
            Pattern::Wildcard { span: pat_span } => Ok(TypedPattern::Wildcard {
                ty: expected.clone(),
                span: *pat_span,
            }),

            Pattern::Var {
                name,
                span: pat_span,
            } => {
                // Apply shared-scrutinee coercion: ~T -> T (error for ~fn)
                let bind_ty = if !scrutinee_is_owned {
                    match expected {
                        Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)) => {
                            let mut err = super::spanned(
                                TypeError::Mismatch {
                                    expected: expected.clone(),
                                    actual: (**inner).clone(),
                                },
                                span,
                            );
                            err.note = Some(format!(
                                "cannot bind owned function `{}` from a shared container — take ownership of the container first",
                                name
                            ));
                            return Err(err);
                        }
                        Type::Own(inner) => (**inner).clone(),
                        _ => expected.clone(),
                    }
                } else {
                    expected.clone()
                };
                self.env
                    .bind(name.clone(), TypeScheme::mono(bind_ty.clone()));
                Ok(TypedPattern::Var {
                    name: name.clone(),
                    ty: bind_ty,
                    span: *pat_span,
                })
            }

            Pattern::Lit {
                value,
                span: pat_span,
            } => {
                let lit_ty = match value {
                    Lit::Int(_) => Type::Int,
                    Lit::Float(_) => Type::Float,
                    Lit::Bool(_) => Type::Bool,
                    Lit::String(_) => Type::String,
                    Lit::Unit => Type::Unit,
                };
                self.unify_spanned(expected, &lit_ty, span)?;
                Ok(TypedPattern::Lit {
                    value: value.clone(),
                    ty: lit_ty,
                    span: *pat_span,
                })
            }

            Pattern::Constructor {
                name,
                args,
                span: pat_span,
            } => {
                match self.env.lookup(name) {
                    Some(scheme) => {
                        let scheme = scheme.clone();
                        let instantiated = scheme.instantiate(&mut || self.gen.fresh());
                        match instantiated {
                            Type::Fn(param_types, ret_type) => {
                                self.unify_spanned(expected, &ret_type, span)?;
                                if args.len() != param_types.len() {
                                    return Err(super::spanned(
                                        TypeError::WrongArity {
                                            expected: param_types.len(),
                                            actual: args.len(),
                                        },
                                        span,
                                    ));
                                }
                                let mut typed_args = Vec::new();
                                for (arg_pat, param_ty) in args.iter().zip(param_types.iter()) {
                                    let resolved_param = self.subst.apply(param_ty);
                                    typed_args.push(self.check_pattern(
                                        arg_pat,
                                        &resolved_param,
                                        span,
                                        scrutinee_is_owned,
                                    )?);
                                }
                                Ok(TypedPattern::Constructor {
                                    name: name.clone(),
                                    args: typed_args,
                                    ty: expected.clone(),
                                    span: *pat_span,
                                })
                            }
                            _ => {
                                // Nullary variant
                                self.unify_spanned(expected, &instantiated, span)?;
                                if !args.is_empty() {
                                    return Err(super::spanned(
                                        TypeError::WrongArity {
                                            expected: 0,
                                            actual: args.len(),
                                        },
                                        span,
                                    ));
                                }
                                Ok(TypedPattern::Constructor {
                                    name: name.clone(),
                                    args: vec![],
                                    ty: expected.clone(),
                                    span: *pat_span,
                                })
                            }
                        }
                    }
                    None => Err(super::spanned(
                        TypeError::UnknownVariable { name: name.clone() },
                        span,
                    )),
                }
            }

            Pattern::Tuple {
                elements,
                span: pat_span,
            } => {
                let fresh_vars: Vec<Type> =
                    elements.iter().map(|_| Type::Var(self.fresh())).collect();
                self.unify_spanned(expected, &Type::Tuple(fresh_vars.clone()), span)?;
                let mut typed_elems = Vec::new();
                for (elem_pat, fresh_var) in elements.iter().zip(fresh_vars.iter()) {
                    let resolved = self.subst.apply(fresh_var);
                    typed_elems.push(self.check_pattern(
                        elem_pat,
                        &resolved,
                        span,
                        scrutinee_is_owned,
                    )?);
                }
                Ok(TypedPattern::Tuple {
                    elements: typed_elems,
                    ty: expected.clone(),
                    span: *pat_span,
                })
            }

            Pattern::StructPat {
                name,
                fields,
                rest,
                span: pat_span,
            } => {
                let reg = self.registry.ok_or_else(|| {
                    super::spanned(
                        TypeError::NotAStruct {
                            actual: expected.clone(),
                        },
                        span,
                    )
                })?;
                let info = reg.lookup_type(name).ok_or_else(|| {
                    super::spanned(TypeError::UnknownVariable { name: name.clone() }, span)
                })?;
                // Create fresh type args for the struct's type params
                let fresh_args: Vec<Type> = info
                    .type_param_vars
                    .iter()
                    .map(|_| Type::Var(self.fresh()))
                    .collect();
                let struct_ty = Type::Named(name.clone(), fresh_args.clone());
                self.unify_spanned(expected, &struct_ty, span)?;
                match &info.kind {
                    type_registry::TypeKind::Record {
                        fields: record_fields,
                    } => {
                        let mut typed_fields = Vec::new();
                        for (field_name, field_pat) in fields {
                            let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                            match record_field {
                                Some((_, field_ty)) => {
                                    let instantiated =
                                        super::instantiate_field_type(field_ty, info, &fresh_args);
                                    let resolved = self.subst.apply(&instantiated);
                                    let typed_field_pat = self.check_pattern(
                                        field_pat,
                                        &resolved,
                                        span,
                                        scrutinee_is_owned,
                                    )?;
                                    typed_fields.push((field_name.clone(), typed_field_pat));
                                }
                                None => {
                                    return Err(super::spanned(
                                        TypeError::UnknownField {
                                            type_name: name.clone(),
                                            field_name: field_name.clone(),
                                        },
                                        span,
                                    ));
                                }
                            }
                        }
                        Ok(TypedPattern::StructPat {
                            name: name.clone(),
                            fields: typed_fields,
                            rest: *rest,
                            ty: expected.clone(),
                            span: *pat_span,
                        })
                    }
                    _ => Err(super::spanned(
                        TypeError::NotAStruct {
                            actual: expected.clone(),
                        },
                        span,
                    )),
                }
            }
        }
    }

    /// Given a resolved type and a field name, look up the field in the type registry
    /// and return the field's type with type parameters instantiated.
    pub(super) fn resolve_field_access(
        &self,
        resolved_ty: &Type,
        field_name: &str,
        span: Span,
    ) -> Result<Type, SpannedTypeError> {
        match resolved_ty {
            Type::Named(name, type_args) => {
                let registry = self.registry.ok_or_else(|| {
                    super::spanned(
                        TypeError::NotAStruct {
                            actual: resolved_ty.clone(),
                        },
                        span,
                    )
                })?;
                let info = registry.lookup_type(name).ok_or_else(|| {
                    super::spanned(
                        TypeError::NotAStruct {
                            actual: resolved_ty.clone(),
                        },
                        span,
                    )
                })?;
                match &info.kind {
                    type_registry::TypeKind::Record { fields } => {
                        let field_ty = fields.iter().find(|(n, _)| n == field_name);
                        match field_ty {
                            Some((_, ty)) => {
                                let instantiated =
                                    super::instantiate_field_type(ty, info, type_args);
                                Ok(instantiated)
                            }
                            None => Err(super::spanned(
                                TypeError::UnknownField {
                                    type_name: name.clone(),
                                    field_name: field_name.to_string(),
                                },
                                span,
                            )),
                        }
                    }
                    _ => Err(super::spanned(
                        TypeError::NotAStruct {
                            actual: resolved_ty.clone(),
                        },
                        span,
                    )),
                }
            }
            _ => Err(super::spanned(
                TypeError::NotAStruct {
                    actual: resolved_ty.clone(),
                },
                span,
            )),
        }
    }

    /// Validate a struct update expression and return typed field expressions.
    pub(super) fn resolve_struct_update(
        &mut self,
        resolved_ty: &Type,
        fields: &[(String, Expr)],
        span: Span,
    ) -> Result<Vec<(String, TypedExpr)>, SpannedTypeError> {
        match resolved_ty {
            Type::Named(name, type_args) => {
                let reg = self.registry.ok_or_else(|| {
                    super::spanned(
                        TypeError::NotAStruct {
                            actual: resolved_ty.clone(),
                        },
                        span,
                    )
                })?;
                let info = reg.lookup_type(name).ok_or_else(|| {
                    super::spanned(
                        TypeError::NotAStruct {
                            actual: resolved_ty.clone(),
                        },
                        span,
                    )
                })?;
                match &info.kind {
                    type_registry::TypeKind::Record {
                        fields: record_fields,
                    } => {
                        let mut typed_fields = Vec::new();
                        for (field_name, field_expr) in fields {
                            let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                            match record_field {
                                Some((_, expected_ty)) => {
                                    let expected =
                                        super::instantiate_field_type(expected_ty, info, type_args);
                                    let field_typed = self.infer_expr_inner(field_expr, None)?;
                                    self.coerce_unify_spanned(&field_typed.ty, &expected, span)?;
                                    typed_fields.push((field_name.clone(), field_typed));
                                }
                                None => {
                                    return Err(super::spanned(
                                        TypeError::UnknownField {
                                            type_name: name.clone(),
                                            field_name: field_name.clone(),
                                        },
                                        span,
                                    ));
                                }
                            }
                        }
                        Ok(typed_fields)
                    }
                    _ => Err(super::spanned(
                        TypeError::NotAStruct {
                            actual: resolved_ty.clone(),
                        },
                        span,
                    )),
                }
            }
            _ => Err(super::spanned(
                TypeError::NotAStruct {
                    actual: resolved_ty.clone(),
                },
                span,
            )),
        }
    }
}
