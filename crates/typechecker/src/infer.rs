use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Decl, Expr, Lit, Module, Pattern, Span, UnaryOp};

use crate::scc;
use crate::type_registry::{self, TypeRegistry};
use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{unify, SpannedTypeError, TypeError};

/// Result of type inference for a module.
pub struct ModuleTypeInfo {
    pub fn_types: Vec<(String, TypeScheme)>,
    /// Maps each lambda's span (start, end) to its (param_types, return_type).
    pub lambda_types: HashMap<Span, (Vec<Type>, Type)>,
}

/// Collect free type variables in a type.
fn free_vars(ty: &Type) -> HashSet<TypeVarId> {
    match ty {
        Type::Var(id) => {
            let mut s = HashSet::new();
            s.insert(*id);
            s
        }
        Type::Fn(params, ret) => {
            let mut s = HashSet::new();
            for p in params {
                s.extend(free_vars(p));
            }
            s.extend(free_vars(ret));
            s
        }
        Type::Named(_, args) => {
            let mut s = HashSet::new();
            for a in args {
                s.extend(free_vars(a));
            }
            s
        }
        Type::Own(inner) => free_vars(inner),
        Type::Tuple(elems) => {
            let mut s = HashSet::new();
            for e in elems {
                s.extend(free_vars(e));
            }
            s
        }
        _ => HashSet::new(),
    }
}

/// Collect free type variables across all bindings in the environment.
fn free_vars_env(env: &TypeEnv, subst: &Substitution) -> HashSet<TypeVarId> {
    let mut s = HashSet::new();
    env.for_each_scheme(|scheme| {
        let applied = subst.apply_scheme(scheme);
        let fv = free_vars(&applied.ty);
        // Remove quantified vars
        for v in &fv {
            if !applied.vars.contains(v) {
                s.insert(*v);
            }
        }
    });
    s
}

/// Generalize a type into a type scheme by quantifying over variables
/// free in the type but not free in the environment.
fn generalize(ty: &Type, env: &TypeEnv, subst: &Substitution) -> TypeScheme {
    let ty = subst.apply(ty);
    let ty_vars = free_vars(&ty);
    let env_vars = free_vars_env(env, subst);
    let mut vars: Vec<TypeVarId> = ty_vars.difference(&env_vars).copied().collect();
    vars.sort();
    TypeScheme { vars, ty }
}

/// Attach a span to a TypeError, producing a SpannedTypeError.
fn spanned(error: TypeError, span: krypton_parser::ast::Span) -> SpannedTypeError {
    SpannedTypeError { error, span }
}

/// Check if a type is concretely not a function (after walking substitution).
fn is_concrete_non_function(ty: &Type, subst: &Substitution) -> bool {
    let walked = subst.apply(ty);
    !matches!(walked, Type::Var(_) | Type::Fn(_, _))
}

/// Infer the type of an expression using Algorithm J.
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<Type, SpannedTypeError> {
    infer_expr_inner(expr, env, subst, gen, None, None)
}

/// Infer the type of an expression, with optional access to the type registry
/// for struct field access and update operations.
fn infer_expr_inner(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    mut lambda_types: Option<&mut HashMap<Span, (Vec<Type>, Type)>>,
) -> Result<Type, SpannedTypeError> {
    match expr {
        Expr::Lit { value, .. } => match value {
            Lit::Int(_) => Ok(Type::Int),
            Lit::Float(_) => Ok(Type::Float),
            Lit::Bool(_) => Ok(Type::Bool),
            Lit::String(_) => Ok(Type::String),
            Lit::Unit => Ok(Type::Unit),
        },

        Expr::Var { name, span, .. } => match env.lookup(name) {
            Some(scheme) => {
                let scheme = scheme.clone();
                Ok(scheme.instantiate(&mut || gen.fresh()))
            }
            None => Err(spanned(
                TypeError::UnknownVariable { name: name.clone() },
                *span,
            )),
        },

        Expr::Lambda { params, body, span, .. } => {
            let mut param_types = Vec::new();
            env.push_scope();
            for p in params {
                let tv = Type::Var(gen.fresh());
                param_types.push(tv.clone());
                env.bind(p.name.clone(), TypeScheme::mono(tv));
            }
            let body_ty = infer_expr_inner(body, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            env.pop_scope();
            let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
            let body_ty = subst.apply(&body_ty);
            if let Some(lt) = lambda_types {
                lt.insert(*span, (param_types.clone(), body_ty.clone()));
            }
            Ok(Type::Fn(param_types, Box::new(body_ty)))
        }

        Expr::App {
            func, args, span, ..
        } => {
            let func_ty = infer_expr_inner(func, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            let mut arg_types = Vec::new();
            for a in args {
                arg_types.push(infer_expr_inner(a, env, subst, gen, registry, lambda_types.as_deref_mut())?);
            }

            // Check if the function type is concretely not a function
            if is_concrete_non_function(&func_ty, subst) {
                let actual = subst.apply(&func_ty);
                return Err(spanned(TypeError::NotAFunction { actual }, *span));
            }

            let ret_var = Type::Var(gen.fresh());
            let expected_fn = Type::Fn(arg_types, Box::new(ret_var.clone()));
            unify(&func_ty, &expected_fn, subst)
                .map_err(|e| spanned(e, *span))?;
            Ok(subst.apply(&ret_var))
        }

        Expr::Let {
            name,
            value,
            body,
            ..
        } => {
            let val_ty = infer_expr_inner(value, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            match body {
                Some(body) => {
                    let scheme = generalize(&val_ty, env, subst);
                    env.push_scope();
                    env.bind(name.clone(), scheme);
                    let body_ty = infer_expr_inner(body, env, subst, gen, registry, lambda_types)?;
                    env.pop_scope();
                    Ok(body_ty)
                }
                None => {
                    // Statement form in a do block — generalize for let-polymorphism
                    let scheme = generalize(&val_ty, env, subst);
                    env.bind(name.clone(), scheme);
                    Ok(Type::Unit)
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
            let cond_ty = infer_expr_inner(cond, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            unify(&cond_ty, &Type::Bool, subst)
                .map_err(|e| spanned(e, *span))?;
            let then_ty = infer_expr_inner(then_, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            let else_ty = infer_expr_inner(else_, env, subst, gen, registry, lambda_types)?;
            unify(&then_ty, &else_ty, subst)
                .map_err(|e| spanned(e, *span))?;
            Ok(subst.apply(&then_ty))
        }

        Expr::Do { exprs, .. } => {
            env.push_scope();
            if exprs.is_empty() {
                env.pop_scope();
                return Ok(Type::Unit);
            }
            let mut last_ty = Type::Unit;
            for e in exprs {
                last_ty = infer_expr_inner(e, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            }
            env.pop_scope();
            Ok(last_ty)
        }

        Expr::BinaryOp {
            op, lhs, rhs, span, ..
        } => {
            let lhs_ty = infer_expr_inner(lhs, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            let rhs_ty = infer_expr_inner(rhs, env, subst, gen, registry, lambda_types)?;
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                    unify(&lhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    unify(&rhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    Ok(Type::Int)
                }
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                    unify(&lhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    unify(&rhs_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    Ok(Type::Bool)
                }
            }
        }

        Expr::UnaryOp {
            op, operand, span, ..
        } => {
            let operand_ty = infer_expr_inner(operand, env, subst, gen, registry, lambda_types)?;
            match op {
                UnaryOp::Neg => {
                    unify(&operand_ty, &Type::Int, subst)
                        .map_err(|e| spanned(e, *span))?;
                    Ok(Type::Int)
                }
            }
        }

        Expr::Recur { args, .. } => {
            // Infer arg types for unification side effects; return fresh var
            // that will be unified via the enclosing if-else branches.
            for a in args {
                infer_expr_inner(a, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            }
            Ok(Type::Var(gen.fresh()))
        }

        Expr::FieldAccess { expr: target, field, span } => {
            let target_ty = infer_expr_inner(target, env, subst, gen, registry, lambda_types)?;
            let resolved = subst.apply(&target_ty);
            resolve_field_access(&resolved, field, *span, registry)
        }

        Expr::StructUpdate { base, fields, span } => {
            let base_ty = infer_expr_inner(base, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            let resolved = subst.apply(&base_ty);
            resolve_struct_update(&resolved, fields, *span, env, subst, gen, registry, lambda_types)?;
            Ok(resolved)
        }

        Expr::Match { scrutinee, arms, span } => {
            let scrutinee_ty = infer_expr_inner(scrutinee, env, subst, gen, registry, lambda_types.as_deref_mut())?;
            let result_ty = Type::Var(gen.fresh());
            for arm in arms {
                env.push_scope();
                check_pattern(&arm.pattern, &subst.apply(&scrutinee_ty), env, subst, gen, registry, *span)?;
                let body_ty = infer_expr_inner(&arm.body, env, subst, gen, registry, lambda_types.as_deref_mut())?;
                unify(&result_ty, &body_ty, subst).map_err(|e| spanned(e, *span))?;
                env.pop_scope();
            }
            crate::exhaustiveness::check_exhaustiveness(
                &subst.apply(&scrutinee_ty),
                arms,
                registry,
                *span,
            )?;
            Ok(subst.apply(&result_ty))
        }

        // Unsupported expression forms return a fresh type variable for now
        _ => Ok(Type::Var(gen.fresh())),
    }
}

/// Check a pattern against an expected type, binding variables in the environment.
fn check_pattern(
    pattern: &Pattern,
    expected: &Type,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    span: krypton_parser::ast::Span,
) -> Result<(), SpannedTypeError> {
    match pattern {
        Pattern::Wildcard { .. } => Ok(()),

        Pattern::Var { name, .. } => {
            env.bind(name.clone(), TypeScheme::mono(expected.clone()));
            Ok(())
        }

        Pattern::Lit { value, .. } => {
            let lit_ty = match value {
                Lit::Int(_) => Type::Int,
                Lit::Float(_) => Type::Float,
                Lit::Bool(_) => Type::Bool,
                Lit::String(_) => Type::String,
                Lit::Unit => Type::Unit,
            };
            unify(expected, &lit_ty, subst).map_err(|e| spanned(e, span))
        }

        Pattern::Constructor { name, args, .. } => {
            match env.lookup(name) {
                Some(scheme) => {
                    let scheme = scheme.clone();
                    let instantiated = scheme.instantiate(&mut || gen.fresh());
                    match instantiated {
                        Type::Fn(param_types, ret_type) => {
                            unify(expected, &ret_type, subst).map_err(|e| spanned(e, span))?;
                            if args.len() != param_types.len() {
                                return Err(spanned(
                                    TypeError::WrongArity {
                                        expected: param_types.len(),
                                        actual: args.len(),
                                    },
                                    span,
                                ));
                            }
                            for (arg_pat, param_ty) in args.iter().zip(param_types.iter()) {
                                let resolved_param = subst.apply(param_ty);
                                check_pattern(arg_pat, &resolved_param, env, subst, gen, registry, span)?;
                            }
                            Ok(())
                        }
                        _ => {
                            // Nullary variant
                            unify(expected, &instantiated, subst).map_err(|e| spanned(e, span))?;
                            if !args.is_empty() {
                                return Err(spanned(
                                    TypeError::WrongArity {
                                        expected: 0,
                                        actual: args.len(),
                                    },
                                    span,
                                ));
                            }
                            Ok(())
                        }
                    }
                }
                None => Err(spanned(
                    TypeError::UnknownVariable { name: name.clone() },
                    span,
                )),
            }
        }

        Pattern::Tuple { elements, .. } => {
            let fresh_vars: Vec<Type> = elements.iter().map(|_| Type::Var(gen.fresh())).collect();
            unify(expected, &Type::Tuple(fresh_vars.clone()), subst).map_err(|e| spanned(e, span))?;
            for (elem_pat, fresh_var) in elements.iter().zip(fresh_vars.iter()) {
                let resolved = subst.apply(fresh_var);
                check_pattern(elem_pat, &resolved, env, subst, gen, registry, span)?;
            }
            Ok(())
        }

        Pattern::StructPat { name, fields, .. } => {
            let reg = registry.ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: expected.clone() }, span)
            })?;
            let info = reg.lookup_type(name).ok_or_else(|| {
                spanned(TypeError::UnknownVariable { name: name.clone() }, span)
            })?;
            // Create fresh type args for the struct's type params
            let fresh_args: Vec<Type> = info.type_param_vars.iter().map(|_| Type::Var(gen.fresh())).collect();
            let struct_ty = Type::Named(name.clone(), fresh_args.clone());
            unify(expected, &struct_ty, subst).map_err(|e| spanned(e, span))?;
            match &info.kind {
                type_registry::TypeKind::Record { fields: record_fields } => {
                    for (field_name, field_pat) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, field_ty)) => {
                                let instantiated = instantiate_field_type(field_ty, info, &fresh_args);
                                let resolved = subst.apply(&instantiated);
                                check_pattern(field_pat, &resolved, env, subst, gen, registry, span)?;
                            }
                            None => {
                                return Err(spanned(
                                    TypeError::UnknownField {
                                        type_name: name.clone(),
                                        field_name: field_name.clone(),
                                    },
                                    span,
                                ));
                            }
                        }
                    }
                    Ok(())
                }
                _ => Err(spanned(
                    TypeError::NotAStruct { actual: expected.clone() },
                    span,
                )),
            }
        }
    }
}

/// Given a resolved type and a field name, look up the field in the type registry
/// and return the field's type with type parameters instantiated.
fn resolve_field_access(
    resolved_ty: &Type,
    field_name: &str,
    span: krypton_parser::ast::Span,
    registry: Option<&TypeRegistry>,
) -> Result<Type, SpannedTypeError> {
    match resolved_ty {
        Type::Named(name, type_args) => {
            let registry = registry.ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            let info = registry.lookup_type(name).ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            match &info.kind {
                type_registry::TypeKind::Record { fields } => {
                    let field_ty = fields.iter().find(|(n, _)| n == field_name);
                    match field_ty {
                        Some((_, ty)) => {
                            let instantiated = instantiate_field_type(ty, info, type_args);
                            Ok(instantiated)
                        }
                        None => Err(spanned(
                            TypeError::UnknownField {
                                type_name: name.clone(),
                                field_name: field_name.to_string(),
                            },
                            span,
                        )),
                    }
                }
                _ => Err(spanned(
                    TypeError::NotAStruct { actual: resolved_ty.clone() },
                    span,
                )),
            }
        }
        _ => Err(spanned(
            TypeError::NotAStruct { actual: resolved_ty.clone() },
            span,
        )),
    }
}

/// Instantiate a field type from the registry by substituting the original
/// type parameter var ids with the concrete type arguments.
fn instantiate_field_type(
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

/// Validate a struct update expression.
fn resolve_struct_update(
    resolved_ty: &Type,
    fields: &[(String, Expr)],
    span: krypton_parser::ast::Span,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
    registry: Option<&TypeRegistry>,
    mut lambda_types: Option<&mut HashMap<Span, (Vec<Type>, Type)>>,
) -> Result<(), SpannedTypeError> {
    match resolved_ty {
        Type::Named(name, type_args) => {
            let reg = registry.ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            let info = reg.lookup_type(name).ok_or_else(|| {
                spanned(TypeError::NotAStruct { actual: resolved_ty.clone() }, span)
            })?;
            match &info.kind {
                type_registry::TypeKind::Record { fields: record_fields } => {
                    for (field_name, field_expr) in fields {
                        let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                        match record_field {
                            Some((_, expected_ty)) => {
                                let expected = instantiate_field_type(expected_ty, info, type_args);
                                let actual_ty = infer_expr_inner(field_expr, env, subst, gen, registry, lambda_types.as_deref_mut())?;
                                unify(&actual_ty, &expected, subst)
                                    .map_err(|e| spanned(e, span))?;
                            }
                            None => {
                                return Err(spanned(
                                    TypeError::UnknownField {
                                        type_name: name.clone(),
                                        field_name: field_name.clone(),
                                    },
                                    span,
                                ));
                            }
                        }
                    }
                    Ok(())
                }
                _ => Err(spanned(
                    TypeError::NotAStruct { actual: resolved_ty.clone() },
                    span,
                )),
            }
        }
        _ => Err(spanned(
            TypeError::NotAStruct { actual: resolved_ty.clone() },
            span,
        )),
    }
}

/// Format an inferred type for display, renaming type variables to a, b, c, ...
/// and wrapping polymorphic types in `forall`.
pub fn display_type(ty: &Type, subst: &Substitution, env: &TypeEnv) -> String {
    let scheme = generalize(ty, env, subst);
    format!("{}", scheme)
}

/// Infer types for all top-level definitions in a module.
///
/// Uses SCC (strongly connected component) analysis to process definitions
/// in dependency order. Functions within the same SCC are inferred together
/// as a mutually recursive group, then generalized before later SCCs see them.
pub fn infer_module(module: &Module) -> Result<ModuleTypeInfo, SpannedTypeError> {
    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();
    let mut registry = TypeRegistry::new();
    let mut lambda_types: HashMap<Span, (Vec<Type>, Type)> = HashMap::new();

    // First pass: process all DefType declarations
    let mut constructor_schemes: Vec<(String, TypeScheme)> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            let constructors =
                type_registry::process_type_decl(type_decl, &mut registry, &mut gen)
                    .map_err(|e| spanned(e, type_decl.span))?;
            for (name, scheme) in constructors {
                env.bind(name.clone(), scheme.clone());
                constructor_schemes.push((name, scheme));
            }
        }
    }

    // Collect DefFn declarations
    let fn_decls: Vec<&krypton_parser::ast::FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Build dependency graph and compute SCCs in topological order
    let adj = scc::build_dependency_graph(&fn_decls);
    let sccs = scc::tarjan_scc(&adj);

    // Store results indexed by declaration order
    let mut result_schemes: Vec<Option<TypeScheme>> = vec![None; fn_decls.len()];

    // Process each SCC in topological order (dependencies first)
    for component in &sccs {
        // Bind each name in the SCC to a fresh type variable (monomorphic within SCC)
        let mut pre_bound: Vec<(usize, Type)> = Vec::new();
        for &idx in component {
            let tv = Type::Var(gen.fresh());
            env.bind(fn_decls[idx].name.clone(), TypeScheme::mono(tv.clone()));
            pre_bound.push((idx, tv));
        }

        // Infer all bodies in the SCC
        for &(idx, ref tv) in &pre_bound {
            let decl = fn_decls[idx];
            env.push_scope();
            let mut param_types = Vec::new();
            for p in &decl.params {
                let ptv = Type::Var(gen.fresh());
                param_types.push(ptv.clone());
                env.bind(p.name.clone(), TypeScheme::mono(ptv));
            }
            let body_ty = infer_expr_inner(&decl.body, &mut env, &mut subst, &mut gen, Some(&registry), Some(&mut lambda_types))?;
            env.pop_scope();

            let param_types: Vec<Type> = param_types.iter().map(|t| subst.apply(t)).collect();
            let body_ty = subst.apply(&body_ty);
            let fn_ty = Type::Fn(param_types, Box::new(body_ty));
            unify(tv, &fn_ty, &mut subst)
                .map_err(|e| spanned(e, decl.span))?;
        }

        // Generalize all types in the SCC and update env with polymorphic schemes
        let empty_env = TypeEnv::new();
        for &(idx, ref tv) in &pre_bound {
            let final_ty = subst.apply(tv);
            let scheme = generalize(&final_ty, &empty_env, &subst);
            env.bind(fn_decls[idx].name.clone(), scheme.clone());
            result_schemes[idx] = Some(scheme);
        }
    }

    // Collect results: constructors first, then functions in declaration order
    let mut results: Vec<(String, TypeScheme)> = constructor_schemes;
    results.extend(
        fn_decls
            .iter()
            .enumerate()
            .map(|(i, d)| (d.name.clone(), result_schemes[i].clone().unwrap())),
    );

    // Apply final substitution to lambda types
    let lambda_types = lambda_types
        .into_iter()
        .map(|(span, (params, ret))| {
            let params = params.iter().map(|t| subst.apply(t)).collect();
            let ret = subst.apply(&ret);
            (span, (params, ret))
        })
        .collect();

    Ok(ModuleTypeInfo {
        fn_types: results,
        lambda_types,
    })
}
