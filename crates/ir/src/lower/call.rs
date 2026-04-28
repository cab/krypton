// Function-application and record-construction lowering. Routes regular
// `App`s, struct constructors, and struct-update expressions through dict
// resolution and the ANF helpers, producing either a `SimpleExpr` (with
// prefix bindings) or a fully reduced `Expr` for compound argument paths.

use rustc_hash::FxHashMap;

use krypton_typechecker::typed_ast::{
    self as typed_ast, ResolvedBindingRef, ResolvedTypeRef, TypedExpr,
};
use krypton_typechecker::types::Type;

use super::ctx::{LetBinding, LowerCtx};
use super::resolved::{
    callable_overload_signature, callable_qualified_name, extract_call_info,
    variant_ref_from_constructor,
};
use super::util::{atom_expr_at, expr_at, simple_at};
use super::LowerError;
use crate::{Atom, Expr, ExprKind, SimpleExpr, SimpleExprKind};

impl<'a> LowerCtx<'a> {

    /// Lower a function application.
    pub(super) fn lower_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // Peel TypeApp to get the function name, resolved binding ref, and the
        // user's explicit (TypeVarId, Type) bindings.
        let (func_name, resolved_ref, user_type_bindings) = extract_call_info(func);

        // ANF-normalize all arguments
        let mut bindings = vec![];
        let mut arg_atoms = vec![];
        for arg in args {
            let (bs, atom) = self.lower_to_atom(arg)?;
            bindings.extend(bs);
            arg_atoms.push(atom);
        }

        // Handle trait method dispatch from resolved trait refs.
        if let Some(ResolvedBindingRef::TraitMethod(trait_ref)) = resolved_ref.as_ref() {
            let trait_id = &trait_ref.trait_name;
            let name = &trait_ref.method_name;
            let (dict_tys, resolved_bindings) = self.resolve_dispatch_type_with_bindings(
                trait_id,
                name,
                &func.ty,
                &user_type_bindings,
            )?;
            let (dict_bindings, dict_atom) = self.resolve_dict(trait_id, &dict_tys)?;
            bindings.extend(dict_bindings);

            // Methods without where-clause constraints have no entry
            let method_constraints = self
                .trait_method_constraints
                .get(trait_id)
                .and_then(|mc| mc.get(name.as_str()))
                .cloned()
                .unwrap_or_default();
            let mut method_dict_atoms = Vec::new();
            for (constraint_trait, constraint_tvs) in &method_constraints {
                let concrete_tys: Option<Vec<Type>> = constraint_tvs
                    .iter()
                    .map(|tv| resolved_bindings.get(tv).cloned())
                    .collect();
                if let Some(concrete_tys) = concrete_tys {
                    let (extra_bindings, extra_atom) =
                        self.resolve_dict(constraint_trait, &concrete_tys)?;
                    bindings.extend(extra_bindings);
                    method_dict_atoms.push(extra_atom);
                }
            }

            // Dict is prepended as first argument, then method dicts, then user args
            let mut all_args = vec![dict_atom];
            all_args.extend(method_dict_atoms);
            all_args.extend(arg_atoms);
            return Ok((
                bindings,
                simple_at(
                    func.span,
                    SimpleExprKind::TraitCall {
                        trait_name: trait_id.clone(),
                        method_name: name.clone(),
                        args: all_args,
                    },
                ),
            ));
        }

        if let Some(name) = &func_name {
            if let Some(ResolvedBindingRef::Constructor(constructor_ref)) = resolved_ref.as_ref() {
                match constructor_ref.kind {
                    typed_ast::ConstructorKind::Variant => {
                        let variant_ref = variant_ref_from_constructor(constructor_ref)
                            .ok_or_else(|| {
                                LowerError::InternalError(format!(
                                    "missing variant ref for constructor `{}`",
                                    constructor_ref.constructor_name
                                ))
                            })?;
                        let (tag, _fields) = self.variant_info(&variant_ref)?;
                        return Ok((
                            bindings,
                            simple_at(
                                func.span,
                                SimpleExprKind::ConstructVariant {
                                    type_ref: self.type_canonical_ref(&constructor_ref.type_ref),
                                    variant: constructor_ref.constructor_name.clone(),
                                    tag,
                                    fields: arg_atoms,
                                },
                            ),
                        ));
                    }
                    typed_ast::ConstructorKind::Record => {
                        return Ok((
                            bindings,
                            simple_at(
                                func.span,
                                SimpleExprKind::Construct {
                                    type_ref: self.type_canonical_ref(&constructor_ref.type_ref),
                                    fields: arg_atoms,
                                },
                            ),
                        ));
                    }
                }
            }
            if let Some(variant_ref) = self.fallback_variant_ref(name) {
                let (tag, _fields) = self.variant_info(&variant_ref)?;
                return Ok((
                    bindings,
                    simple_at(
                        func.span,
                        SimpleExprKind::ConstructVariant {
                            type_ref: self.type_canonical_ref(&variant_ref.type_ref),
                            variant: name.clone(),
                            tag,
                            fields: arg_atoms,
                        },
                    ),
                ));
            }
            if let Some(type_ref) = self.fallback_type_ref(name) {
                return Ok((
                    bindings,
                    simple_at(
                        func.span,
                        SimpleExprKind::Construct {
                            type_ref: self.type_canonical_ref(&type_ref),
                            fields: arg_atoms,
                        },
                    ),
                ));
            }

            // Check if it's a resolved top-level/imported function.
            if let Some(ResolvedBindingRef::Callable(callable_ref)) = resolved_ref.as_ref() {
                let qn = callable_qualified_name(callable_ref, &self.module_path);
                let sig = callable_overload_signature(callable_ref);
                let Some(fn_id) = self.lookup_callable(&qn, sig) else {
                    return Err(LowerError::UnresolvedVar(name.clone()));
                };
                // Resolve dict arguments for constrained functions
                let (dict_bindings, dict_atoms) =
                    self.resolve_call_dicts(&qn, args, &user_type_bindings, Some(&func.ty))?;
                bindings.extend(dict_bindings);

                let mut all_args = dict_atoms;
                all_args.extend(arg_atoms);
                return Ok((
                    bindings,
                    simple_at(
                        func.span,
                        SimpleExprKind::Call {
                            func: fn_id,
                            args: all_args,
                        },
                    ),
                ));
            }

            // Local variable with function type — closure call
            if let Some(var_id) = self.lookup_var(name) {
                return Ok((
                    bindings,
                    simple_at(
                        func.span,
                        SimpleExprKind::CallClosure {
                            closure: Atom::Var(var_id),
                            args: arg_atoms,
                        },
                    ),
                ));
            }

            return Err(LowerError::UnresolvedVar(name.clone()));
        }

        // General case: func is a complex expression
        let (func_bindings, func_atom) = self.lower_to_atom(func)?;
        bindings.extend(func_bindings);
        Ok((
            bindings,
            simple_at(
                func.span,
                SimpleExprKind::CallClosure {
                    closure: func_atom,
                    args: arg_atoms,
                },
            ),
        ))
    }

    /// Lower a struct literal.
    pub(super) fn lower_struct_lit(
        &mut self,
        name: &str,
        fields: &[(String, TypedExpr)],
        resolved_type_ref: Option<&ResolvedTypeRef>,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        let type_ref = resolved_type_ref
            .cloned()
            .or_else(|| self.fallback_type_ref(name))
            .ok_or_else(|| LowerError::UnresolvedStruct(name.to_string()))?;
        let canonical_fields = self
            .struct_fields
            .get(&type_ref)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_ref.qualified_name.to_string()))?
            .clone();

        // Build a map of field name → lowered atom
        let mut field_map: FxHashMap<String, Atom> = FxHashMap::default();
        let mut bindings = vec![];
        for (fname, fexpr) in fields {
            let (bs, atom) = self.lower_to_atom(fexpr)?;
            bindings.extend(bs);
            field_map.insert(fname.clone(), atom);
        }

        // Reorder to canonical field order
        let mut ordered_atoms = vec![];
        for (fname, _) in &canonical_fields {
            let atom = field_map.remove(fname).ok_or_else(|| {
                LowerError::UnresolvedField(type_ref.qualified_name.to_string(), fname.clone())
            })?;
            ordered_atoms.push(atom);
        }

        Ok((
            bindings,
            simple_at(
                fields.first().map(|(_, e)| e.span).unwrap_or((0, 0)),
                SimpleExprKind::Construct {
                    type_ref: self.type_canonical_ref(&type_ref),
                    fields: ordered_atoms,
                },
            ),
        ))
    }

    // -----------------------------------------------------------------------
    // CPS-based expression lowering (compound-safe)
    // -----------------------------------------------------------------------

    /// Lower a function application as a full Expr, handling compound args.
    pub(super) fn lower_app_expr(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Peel TypeApp to get function name, resolved binding ref, and the
        // user's explicit (TypeVarId, Type) bindings.
        let (func_name, resolved_ref, user_type_bindings) = extract_call_info(func);

        let result_ty = result_ty.clone();

        // Handle trait method dispatch
        if let Some(ResolvedBindingRef::TraitMethod(trait_ref)) = resolved_ref.as_ref() {
            let trait_id = &trait_ref.trait_name;
            let name = &trait_ref.method_name;
            let (dict_tys, resolved_bindings) = self.resolve_dispatch_type_with_bindings(
                trait_id,
                name,
                &func.ty,
                &user_type_bindings,
            )?;
            let (mut dict_bindings, dict_atom) = self.resolve_dict(trait_id, &dict_tys)?;

            // Methods without where-clause constraints have no entry
            let mut method_dict_atoms = Vec::new();
            let method_constraints = self
                .trait_method_constraints
                .get(trait_id)
                .and_then(|mc| mc.get(name.as_str()))
                .cloned()
                .unwrap_or_default();
            {
                for (constraint_trait, constraint_tvs) in &method_constraints {
                    let concrete_tys: Vec<Type> = constraint_tvs
                        .iter()
                        .map(|tv| {
                            resolved_bindings.get(tv).cloned().ok_or_else(|| {
                                LowerError::InternalError(format!(
                                    "ICE: could not resolve method constraint type var for {}.{}",
                                    trait_id.local_name, name
                                ))
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let (extra_bindings, extra_atom) =
                        self.resolve_dict(constraint_trait, &concrete_tys)?;
                    dict_bindings.extend(extra_bindings);
                    method_dict_atoms.push(extra_atom);
                }
            }

            let trait_id = trait_id.clone();
            let name = name.clone();
            return self.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                let mut all_args = vec![dict_atom];
                all_args.extend(method_dict_atoms);
                all_args.extend(arg_atoms);
                let var = ctx.fresh_var();
                let ty = result_ty;
                let call_expr = expr_at(
                    func.span,
                    ty.clone().into(),
                    ExprKind::Let {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(
                            func.span,
                            SimpleExprKind::TraitCall {
                                trait_name: trait_id,
                                method_name: name,
                                args: all_args,
                            },
                        ),
                        body: Box::new(atom_expr_at(func.span, ty.into(), Atom::Var(var))),
                    },
                );
                Ok(Self::wrap_bindings(dict_bindings, call_expr))
            });
        }

        if let Some(name) = &func_name {
            if let Some(ResolvedBindingRef::Constructor(constructor_ref)) = resolved_ref.as_ref() {
                match constructor_ref.kind {
                    typed_ast::ConstructorKind::Variant => {
                        let variant_ref = variant_ref_from_constructor(constructor_ref)
                            .ok_or_else(|| {
                                LowerError::InternalError(format!(
                                    "missing variant ref for constructor `{}`",
                                    constructor_ref.constructor_name
                                ))
                            })?;
                        let (tag, _fields) = self.variant_info(&variant_ref)?;
                        let variant_name = constructor_ref.constructor_name.clone();
                        let type_cref = self.type_canonical_ref(&constructor_ref.type_ref);
                        return self.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                            let var = ctx.fresh_var();
                            let ty = result_ty.clone();
                            Ok(expr_at(
                                func.span,
                                ty.clone().into(),
                                ExprKind::Let {
                                    bind: var,
                                    ty: ty.clone().into(),
                                    value: simple_at(
                                        func.span,
                                        SimpleExprKind::ConstructVariant {
                                            type_ref: type_cref.clone(),
                                            variant: variant_name.clone(),
                                            tag,
                                            fields: arg_atoms,
                                        },
                                    ),
                                    body: Box::new(atom_expr_at(
                                        func.span,
                                        ty.into(),
                                        Atom::Var(var),
                                    )),
                                },
                            ))
                        });
                    }
                    typed_ast::ConstructorKind::Record => {
                        let type_cref = self.type_canonical_ref(&constructor_ref.type_ref);
                        return self.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                            let var = ctx.fresh_var();
                            let ty = result_ty.clone();
                            Ok(expr_at(
                                func.span,
                                ty.clone().into(),
                                ExprKind::Let {
                                    bind: var,
                                    ty: ty.clone().into(),
                                    value: simple_at(
                                        func.span,
                                        SimpleExprKind::Construct {
                                            type_ref: type_cref.clone(),
                                            fields: arg_atoms,
                                        },
                                    ),
                                    body: Box::new(atom_expr_at(
                                        func.span,
                                        ty.into(),
                                        Atom::Var(var),
                                    )),
                                },
                            ))
                        });
                    }
                }
            }
            if let Some(variant_ref) = self.fallback_variant_ref(name) {
                let (tag, _fields) = self.variant_info(&variant_ref)?;
                let variant_name = name.clone();
                let type_cref = self.type_canonical_ref(&variant_ref.type_ref);
                return self.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                    let var = ctx.fresh_var();
                    let ty = result_ty.clone();
                    Ok(expr_at(
                        func.span,
                        ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                func.span,
                                SimpleExprKind::ConstructVariant {
                                    type_ref: type_cref.clone(),
                                    variant: variant_name.clone(),
                                    tag,
                                    fields: arg_atoms,
                                },
                            ),
                            body: Box::new(atom_expr_at(func.span, ty.into(), Atom::Var(var))),
                        },
                    ))
                });
            }
            if let Some(type_ref) = self.fallback_type_ref(name) {
                let type_cref = self.type_canonical_ref(&type_ref);
                return self.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                    let var = ctx.fresh_var();
                    let ty = result_ty.clone();
                    Ok(expr_at(
                        func.span,
                        ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                func.span,
                                SimpleExprKind::Construct {
                                    type_ref: type_cref.clone(),
                                    fields: arg_atoms,
                                },
                            ),
                            body: Box::new(atom_expr_at(func.span, ty.into(), Atom::Var(var))),
                        },
                    ))
                });
            }

            // Known top-level/imported function
            if let Some(ResolvedBindingRef::Callable(callable_ref)) = resolved_ref.as_ref() {
                let qn = callable_qualified_name(callable_ref, &self.module_path);
                let sig = callable_overload_signature(callable_ref);
                let Some(fn_id) = self.lookup_callable(&qn, sig) else {
                    return Err(LowerError::UnresolvedVar(name.clone()));
                };
                let (dict_bindings, dict_atoms) =
                    self.resolve_call_dicts(&qn, args, &user_type_bindings, Some(&func.ty))?;

                return self.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                    let mut all_args = dict_atoms;
                    all_args.extend(arg_atoms);
                    let var = ctx.fresh_var();
                    let ty = result_ty;
                    let call_expr = expr_at(
                        func.span,
                        ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                func.span,
                                SimpleExprKind::Call {
                                    func: fn_id,
                                    args: all_args,
                                },
                            ),
                            body: Box::new(atom_expr_at(func.span, ty.into(), Atom::Var(var))),
                        },
                    );
                    Ok(Self::wrap_bindings(dict_bindings, call_expr))
                });
            }

            // Local variable — closure call
            if let Some(var_id) = self.lookup_var(name) {
                return self.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                    let var = ctx.fresh_var();
                    let ty = result_ty.clone();
                    Ok(expr_at(
                        func.span,
                        ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                func.span,
                                SimpleExprKind::CallClosure {
                                    closure: Atom::Var(var_id),
                                    args: arg_atoms,
                                },
                            ),
                            body: Box::new(atom_expr_at(func.span, ty.into(), Atom::Var(var))),
                        },
                    ))
                });
            }

            return Err(LowerError::UnresolvedVar(name.clone()));
        }

        // General case: func is a complex expression
        self.lower_to_atom_then(func, |ctx, func_atom| {
            ctx.lower_atoms_then(args, vec![], |ctx, arg_atoms| {
                let var = ctx.fresh_var();
                let ty = result_ty.clone();
                Ok(expr_at(
                    func.span,
                    ty.clone().into(),
                    ExprKind::Let {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(
                            func.span,
                            SimpleExprKind::CallClosure {
                                closure: func_atom.clone(),
                                args: arg_atoms,
                            },
                        ),
                        body: Box::new(atom_expr_at(func.span, ty.into(), Atom::Var(var))),
                    },
                ))
            })
        })
    }

    /// Lower a struct literal as a full Expr, handling compound field values.
    pub(super) fn lower_struct_lit_expr(
        &mut self,
        name: &str,
        fields: &[(String, TypedExpr)],
        resolved_type_ref: Option<&ResolvedTypeRef>,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let type_ref = resolved_type_ref
            .cloned()
            .or_else(|| self.fallback_type_ref(name))
            .ok_or_else(|| LowerError::UnresolvedStruct(name.to_string()))?;
        let canonical_fields = self
            .struct_fields
            .get(&type_ref)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_ref.qualified_name.to_string()))?
            .clone();

        // Reorder field expressions to canonical order
        let field_map: FxHashMap<&str, &TypedExpr> =
            fields.iter().map(|(n, e)| (n.as_str(), e)).collect();
        let mut ordered_exprs = vec![];
        for (fname, _) in &canonical_fields {
            let fexpr = field_map.get(fname.as_str()).ok_or_else(|| {
                LowerError::UnresolvedField(type_ref.qualified_name.to_string(), fname.clone())
            })?;
            ordered_exprs.push((*fexpr).clone());
        }

        let result_ty = result_ty.clone();
        let type_cref = self.type_canonical_ref(&type_ref);
        self.lower_atoms_then(&ordered_exprs, vec![], |ctx, atoms| {
            let var = ctx.fresh_var();
            let ty = result_ty;
            Ok(expr_at(
                ordered_exprs.first().map(|e| e.span).unwrap_or((0, 0)),
                ty.clone().into(),
                ExprKind::Let {
                    bind: var,
                    ty: ty.clone().into(),
                    value: simple_at(
                        ordered_exprs.first().map(|e| e.span).unwrap_or((0, 0)),
                        SimpleExprKind::Construct {
                            type_ref: type_cref,
                            fields: atoms,
                        },
                    ),
                    body: Box::new(atom_expr_at(
                        ordered_exprs.first().map(|e| e.span).unwrap_or((0, 0)),
                        ty.into(),
                        Atom::Var(var),
                    )),
                },
            ))
        })
    }

    /// Lower a struct update expression, handling compound sub-expressions.
    pub(super) fn lower_struct_update_expr(
        &mut self,
        base: &TypedExpr,
        updates: &[(String, TypedExpr)],
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let type_ref = self.resolved_type_ref_from_type(&base.ty).ok_or_else(|| {
            LowerError::InternalError(format!("StructUpdate on non-named type: {:?}", base.ty))
        })?;

        let canonical_fields = self.substituted_struct_fields(&type_ref, &base.ty)?;

        let result_ty = result_ty.clone();
        let update_names: Vec<String> = updates.iter().map(|(n, _)| n.clone()).collect();
        let update_exprs: Vec<TypedExpr> = updates.iter().map(|(_, e)| e.clone()).collect();

        // Lower base first, then update field values
        self.lower_to_atom_then(base, |ctx, base_atom| {
            ctx.lower_atoms_then(&update_exprs, vec![], |ctx, update_atoms| {
                let mut update_map: FxHashMap<String, Atom> =
                    update_names.iter().cloned().zip(update_atoms).collect();

                let mut bindings = vec![];
                let mut field_atoms = vec![];
                for (i, (fname, fty)) in canonical_fields.iter().enumerate() {
                    if let Some(atom) = update_map.remove(fname) {
                        field_atoms.push(atom);
                    } else {
                        let proj_var = ctx.fresh_var();
                        bindings.push(LetBinding {
                            bind: proj_var,
                            ty: fty.clone().into(),
                            value: simple_at(
                                base.span,
                                SimpleExprKind::Project {
                                    value: base_atom.clone(),
                                    field_index: i,
                                },
                            ),
                        });
                        field_atoms.push(Atom::Var(proj_var));
                    }
                }

                let construct_var = ctx.fresh_var();
                let type_cref = ctx.type_canonical_ref(&type_ref);
                bindings.push(LetBinding {
                    bind: construct_var,
                    ty: result_ty.clone().into(),
                    value: simple_at(
                        base.span,
                        SimpleExprKind::Construct {
                            type_ref: type_cref,
                            fields: field_atoms,
                        },
                    ),
                });

                let inner = atom_expr_at(base.span, result_ty.into(), Atom::Var(construct_var));
                Ok(Self::wrap_bindings(bindings, inner))
            })
        })
    }

}
