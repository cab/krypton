// Algorithm J type inference implementation
// Core type checking engine for alang

use crate::builtins::is_primitive_type;
use crate::environment::{Environment, TypeDeclInfo, TypeDeclKind};
use crate::error::TypeError;
use crate::substitution::Substitution;
use crate::types::{InferType, PrimitiveType, TypeScheme, TypeVar};
use crate::unification::unify;
use alang_parser::ast::{Decl, Expr, Program, Type as AstType};

/// Typed program output
#[derive(Debug, Clone)]
pub struct TypedProgram {
    pub decls: Vec<TypedDecl>,
}

/// Typed declaration
#[derive(Debug, Clone)]
pub enum TypedDecl {
    Type,
    Def { name: String, ty: InferType },
}

/// Main entry point: type check a program
/// Phase 1: Collect type declarations
/// Phase 2: Type check function definitions
pub fn typecheck_program(program: &Program) -> Result<TypedProgram, Vec<TypeError>> {
    let mut env = Environment::new();
    let mut errors = Vec::new();

    // Phase 1: Collect type declarations
    for decl in &program.decls {
        if let Err(e) = collect_type_decl(&mut env, decl) {
            errors.push(e);
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    // Phase 2: Type check function definitions
    let mut typed_decls = Vec::new();
    for decl in &program.decls {
        match typecheck_decl(&mut env, decl) {
            Ok(typed) => typed_decls.push(typed),
            Err(e) => errors.push(e),
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    Ok(TypedProgram {
        decls: typed_decls,
    })
}

/// Phase 1: Collect type declarations (build type environment)
fn collect_type_decl(env: &mut Environment, decl: &Decl) -> Result<(), TypeError> {
    match decl {
        Decl::Type { name, params, body, .. } => {
            let decl_id = env.fresh_decl_id();

            // Convert AST TypeBody to TypeDeclKind
            let kind = match body {
                alang_parser::TypeBody::Struct(fields) => {
                    let mut infer_fields = Vec::new();
                    for field in fields {
                        let ty = ast_type_to_infer_type(env, &field.ty)?;
                        infer_fields.push((field.name.clone(), ty));
                    }
                    TypeDeclKind::Struct {
                        fields: infer_fields,
                    }
                }
                alang_parser::TypeBody::Sum(_variants) => {
                    // TODO: Implement sum type collection
                    TypeDeclKind::Sum { variants: vec![] }
                }
                alang_parser::TypeBody::Alias(ty) => {
                    let target = ast_type_to_infer_type(env, ty)?;
                    TypeDeclKind::Alias { target }
                }
            };

            let info = TypeDeclInfo {
                decl_id,
                params: params.clone(),
                kind,
            };

            env.add_type_decl(name.clone(), info);
            Ok(())
        }
        Decl::Def { .. } => Ok(()), // Skip functions in phase 1
    }
}

/// Phase 2: Type check declarations
fn typecheck_decl(env: &mut Environment, decl: &Decl) -> Result<TypedDecl, TypeError> {
    match decl {
        Decl::Type { .. } => {
            // Already processed in phase 1
            Ok(TypedDecl::Type)
        }
        Decl::Def {
            name,
            type_params,
            params,
            return_type,
            body,
            ..
        } => {
            env.push_scope();

            // TODO: Handle type parameters properly
            // For now, create fresh variables for them
            for _param_name in type_params {
                let _ = env.fresh_var();
            }

            // Infer parameter types
            let mut param_types = Vec::new();
            for param in params {
                let param_ty = match &param.ty {
                    Some(ast_ty) => ast_type_to_infer_type(env, ast_ty)?,
                    None => InferType::Var(env.fresh_var()),
                };

                let final_ty = if param.is_move {
                    InferType::Move(Box::new(param_ty))
                } else {
                    param_ty
                };

                // Bind parameter in environment
                env.bind(
                    param.name.clone(),
                    TypeScheme {
                        forall: vec![],
                        ty: final_ty.clone(),
                    },
                );

                param_types.push(final_ty);
            }

            // Infer body type
            let (body_ty, body_subst) = infer_expr(env, body)?;

            // Check return type if specified
            let ret_ty = match return_type {
                Some(ast_ty) => {
                    let expected = ast_type_to_infer_type(env, ast_ty)?;
                    let subst = unify(&expected, &body_ty, body.span())?;
                    body_subst.apply(&subst.apply(&expected))
                }
                None => body_ty,
            };

            // Build function type
            let fn_ty = InferType::Function {
                params: param_types.iter().map(|p| body_subst.apply(p)).collect(),
                ret: Box::new(ret_ty.clone()),
            };

            env.pop_scope();

            // Create type scheme (no generalization for now)
            let scheme = TypeScheme {
                forall: vec![],
                ty: fn_ty.clone(),
            };

            // Bind function in environment
            env.bind(name.clone(), scheme);

            Ok(TypedDecl::Def {
                name: name.clone(),
                ty: fn_ty,
            })
        }
    }
}

/// Infer the type of an expression (core Algorithm J)
/// Returns (inferred type, substitution)
fn infer_expr(env: &mut Environment, expr: &Expr) -> Result<(InferType, Substitution), TypeError> {
    match expr {
        // Literals
        Expr::Int(_, _) => Ok((
            InferType::Primitive(PrimitiveType::Int),
            Substitution::new(),
        )),
        Expr::Float(_, _) => Ok((
            InferType::Primitive(PrimitiveType::Float),
            Substitution::new(),
        )),
        Expr::String(_, _) => Ok((
            InferType::Primitive(PrimitiveType::String),
            Substitution::new(),
        )),
        Expr::Bool(_, _) => Ok((
            InferType::Primitive(PrimitiveType::Bool),
            Substitution::new(),
        )),
        Expr::Unit(_) => Ok((
            InferType::Primitive(PrimitiveType::Unit),
            Substitution::new(),
        )),

        // Variable lookup
        Expr::Var(name, span) => match env.lookup(name).cloned() {
            Some(scheme) => {
                // Instantiate type scheme (replace ∀ variables with fresh ones)
                let ty = instantiate(env, &scheme);
                Ok((ty, Substitution::new()))
            }
            None => Err(TypeError::unknown_variable(name, span.clone())),
        },

        // Function call: (f arg1 arg2 ...)
        Expr::Call(func, args, span) => {
            // Infer function type
            let (func_ty, mut subst) = infer_expr(env, func)?;

            // Infer argument types
            let mut arg_types = Vec::new();
            for arg in args {
                let (arg_ty, arg_subst) = infer_expr(env, arg)?;
                subst = subst.compose(&arg_subst);
                arg_types.push(subst.apply(&arg_ty));
            }

            // Create fresh type variable for return type
            let ret_var = env.fresh_var();
            let ret_ty = InferType::Var(ret_var);

            // Expected function type: (arg1, arg2, ...) -> ret_var
            let expected_fn_ty = InferType::Function {
                params: arg_types,
                ret: Box::new(ret_ty.clone()),
            };

            // Unify with actual function type
            let func_ty = subst.apply(&func_ty);
            let call_subst = unify(&expected_fn_ty, &func_ty, span)?;
            subst = subst.compose(&call_subst);

            Ok((subst.apply(&ret_ty), subst))
        }

        // Function/closure: (fn [x y] body)
        Expr::Function(params, body, _span) => {
            env.push_scope();

            // Create fresh variables for parameters
            let mut param_types = Vec::new();
            for param in params {
                let param_ty = match &param.ty {
                    Some(ast_ty) => ast_type_to_infer_type(env, ast_ty)?,
                    None => InferType::Var(env.fresh_var()),
                };

                let final_ty = if param.is_move {
                    InferType::Move(Box::new(param_ty))
                } else {
                    param_ty
                };

                env.bind(
                    param.name.clone(),
                    TypeScheme {
                        forall: vec![],
                        ty: final_ty.clone(),
                    },
                );
                param_types.push(final_ty);
            }

            // Infer body type
            let (body_ty, subst) = infer_expr(env, body)?;

            env.pop_scope();

            let fn_ty = InferType::Function {
                params: param_types.iter().map(|p| subst.apply(p)).collect(),
                ret: Box::new(body_ty),
            };

            Ok((fn_ty, subst))
        }

        // Let binding: (let [x e1] [y e2] ... body)
        Expr::Let(bindings, body, _span) => {
            env.push_scope();

            let mut subst = Substitution::new();

            for binding in bindings {
                // Infer binding value type
                let (val_ty, val_subst) = infer_expr(env, &binding.value)?;
                subst = subst.compose(&val_subst);

                let val_ty = subst.apply(&val_ty);

                // Check against annotation if present
                let final_ty = match &binding.ty {
                    Some(ast_ty) => {
                        let expected = ast_type_to_infer_type(env, ast_ty)?;
                        let check_subst = unify(&expected, &val_ty, binding.value.span())?;
                        subst = subst.compose(&check_subst);
                        subst.apply(&expected)
                    }
                    None => val_ty,
                };

                // Generalize let-binding (unless it's ^move)
                let scheme = if final_ty.is_move() {
                    TypeScheme {
                        forall: vec![],
                        ty: final_ty,
                    }
                } else {
                    generalize(env, &final_ty)
                };

                env.bind(binding.name.clone(), scheme);
            }

            // Infer body type
            let (body_ty, body_subst) = infer_expr(env, body)?;
            subst = subst.compose(&body_subst);

            env.pop_scope();

            Ok((body_ty, subst))
        }

        // If expression: (if cond then else)
        Expr::If(cond, then_expr, else_expr, span) => {
            // Condition must be Bool
            let (cond_ty, mut subst) = infer_expr(env, cond)?;
            let bool_ty = InferType::Primitive(PrimitiveType::Bool);
            let cond_subst = unify(&bool_ty, &cond_ty, cond.span())?;
            subst = subst.compose(&cond_subst);

            // Both branches must have same type
            let (then_ty, then_subst) = infer_expr(env, then_expr)?;
            subst = subst.compose(&then_subst);

            let (else_ty, else_subst) = infer_expr(env, else_expr)?;
            subst = subst.compose(&else_subst);

            let branch_subst = unify(&subst.apply(&then_ty), &subst.apply(&else_ty), span)?;
            subst = subst.compose(&branch_subst);

            Ok((subst.apply(&then_ty), subst))
        }

        // Pattern matching: TODO in Phase 3
        Expr::Match(_, _, span) => {
            // Stub: return Unit for now
            Err(TypeError {
                code: crate::error::ErrorCode::UnknownType,
                message: "Match expressions not yet implemented".to_string(),
                primary_span: span.clone(),
                labels: vec![(span.clone(), "TODO: implement pattern matching".to_string())],
                notes: vec![],
            })
        }

        // Struct construction: TODO in Phase 3
        Expr::StructLit(_, _, span) => {
            Err(TypeError {
                code: crate::error::ErrorCode::UnknownType,
                message: "Struct literals not yet implemented".to_string(),
                primary_span: span.clone(),
                labels: vec![(span.clone(), "TODO: implement struct construction".to_string())],
                notes: vec![],
            })
        }

        // Field access: TODO in Phase 3
        Expr::FieldAccess(_, _, span) => {
            Err(TypeError {
                code: crate::error::ErrorCode::UnknownType,
                message: "Field access not yet implemented".to_string(),
                primary_span: span.clone(),
                labels: vec![(span.clone(), "TODO: implement field access".to_string())],
                notes: vec![],
            })
        }
    }
}

/// Generalize a type: ∀ free variables not in environment
fn generalize(env: &Environment, ty: &InferType) -> TypeScheme {
    let env_vars = env.free_vars();
    let ty_vars = ty.free_vars();

    let mut quantified: Vec<TypeVar> = ty_vars
        .iter()
        .filter(|v| !env_vars.contains(v))
        .copied()
        .collect();

    // Sort for deterministic output
    quantified.sort();

    TypeScheme {
        forall: quantified,
        ty: ty.clone(),
    }
}

/// Instantiate a type scheme with fresh variables
fn instantiate(env: &mut Environment, scheme: &TypeScheme) -> InferType {
    if scheme.forall.is_empty() {
        return scheme.ty.clone();
    }

    // Create substitution mapping quantified vars to fresh vars
    let mut subst = Substitution::new();
    for var in &scheme.forall {
        let fresh = env.fresh_var();
        subst.insert(*var, InferType::Var(fresh));
    }

    subst.apply(&scheme.ty)
}

/// Convert AST type to internal InferType
fn ast_type_to_infer_type(env: &Environment, ast_ty: &AstType) -> Result<InferType, TypeError> {
    match ast_ty {
        AstType::Named(name) => {
            // Check if it's a primitive
            if let Some(prim) = is_primitive_type(name) {
                return Ok(InferType::Primitive(prim));
            }

            // Look up nominal type
            let info = env.lookup_type(name).ok_or_else(|| {
                TypeError::unknown_type(name, alang_parser::ast::Span { start: 0, end: 0 })
            })?;

            Ok(InferType::Nominal {
                name: name.clone(),
                decl_id: info.decl_id,
                type_args: vec![],
            })
        }

        AstType::Generic(name, args) => {
            let info = env.lookup_type(name).ok_or_else(|| {
                TypeError::unknown_type(name, alang_parser::ast::Span { start: 0, end: 0 })
            })?;

            let infer_args: Result<Vec<_>, _> = args
                .iter()
                .map(|arg| ast_type_to_infer_type(env, arg))
                .collect();

            Ok(InferType::Nominal {
                name: name.clone(),
                decl_id: info.decl_id,
                type_args: infer_args?,
            })
        }

        AstType::Function(params, ret) => {
            let param_types: Result<Vec<_>, _> = params
                .iter()
                .map(|p| ast_type_to_infer_type(env, p))
                .collect();

            let ret_type = ast_type_to_infer_type(env, ret)?;

            Ok(InferType::Function {
                params: param_types?,
                ret: Box::new(ret_type),
            })
        }

        AstType::Move(inner) => {
            let inner_ty = ast_type_to_infer_type(env, inner)?;
            Ok(InferType::Move(Box::new(inner_ty)))
        }

        AstType::Tuple(types) => {
            let infer_types: Result<Vec<_>, _> = types
                .iter()
                .map(|t| ast_type_to_infer_type(env, t))
                .collect();
            Ok(InferType::Tuple(infer_types?))
        }
    }
}
