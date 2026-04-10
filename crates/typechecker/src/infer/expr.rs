use std::collections::{HashMap, HashSet};

use krypton_parser::ast::Visibility;
use krypton_parser::ast::{BinOp, Expr, Lit, MatchArm, Param, Pattern, Span, TypeExpr, UnaryOp};

use crate::type_registry::{self, ResolutionContext, TypeRegistry};
use crate::typed_ast::{ResolvedTypeRef, TypedExpr, TypedExprKind, TypedMatchArm};
use crate::types::{Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId};
use crate::unify::{coerce_unify, join_types, unify, SecondaryLabel, SpannedTypeError, TypeError};

use super::QualifiedModuleBinding;

pub(crate) struct InferenceContext<'a> {
    pub(super) env: &'a mut TypeEnv,
    pub(super) subst: &'a mut Substitution,
    pub(super) gen: &'a mut TypeVarGen,
    pub(super) registry: Option<&'a TypeRegistry>,
    pub(super) recur_params: Option<Vec<Type>>,
    pub(super) let_own_spans: Option<&'a mut HashSet<Span>>,
    pub(super) lambda_own_captures: Option<&'a mut HashMap<Span, String>>,
    pub(super) type_param_map: &'a HashMap<String, TypeVarId>,
    pub(super) type_param_arity: &'a HashMap<String, usize>,
    pub(super) qualified_modules: &'a HashMap<String, QualifiedModuleBinding>,
    pub(super) imported_type_info: &'a HashMap<String, (String, Visibility)>,
    pub(super) module_path: &'a str,
    pub(super) shadowed_prelude_fns: &'a [(String, String)],
    pub(super) self_type: Option<Type>,
}

impl<'a> InferenceContext<'a> {
    pub fn unify_spanned(
        &mut self,
        t1: &Type,
        t2: &Type,
        span: Span,
    ) -> Result<(), SpannedTypeError> {
        unify(t1, t2, self.subst).map_err(|e| super::spanned(e, span))
    }

    pub fn coerce_unify_spanned(
        &mut self,
        actual: &Type,
        expected: &Type,
        span: Span,
    ) -> Result<(), SpannedTypeError> {
        coerce_unify(actual, expected, self.subst).map_err(|e| super::spanned(e, span))
    }

    fn add_shadowed_prelude_note(&self, err: &mut SpannedTypeError, is_ufcs: bool) {
        if err.note.is_some() || !is_ufcs || self.shadowed_prelude_fns.is_empty() {
            return;
        }
        if matches!(
            &*err.error,
            TypeError::Mismatch { .. }
                | TypeError::FnCapabilityMismatch { .. }
                | TypeError::ParamModeMismatch { .. }
        ) {
            let shadows: Vec<String> = self
                .shadowed_prelude_fns
                .iter()
                .map(|(name, module)| format!("`{name}` from {module}"))
                .collect();
            err.note = Some(format!(
                "{} {} shadowed by an explicit import - this may affect the types flowing through the method chain",
                shadows.join(", "),
                if shadows.len() == 1 { "is" } else { "are" },
            ));
        }
    }

    pub fn join_types_spanned(
        &mut self,
        a: &Type,
        b: &Type,
        span: Span,
    ) -> Result<(), SpannedTypeError> {
        join_types(a, b, self.subst).map_err(|e| super::spanned(e, span))
    }

    /// Given a list of branch types (already joined), resolve the final type:
    /// preserves Own only if ALL branches are Own.
    fn resolve_join_ownership(&self, branch_types: &[Type]) -> Type {
        let all_own = branch_types.iter().all(|t| {
            let resolved = self.subst.apply(t);
            matches!(&resolved, Type::Own(_))
        });
        let resolved = self.subst.apply(&branch_types[0]);
        if all_own {
            resolved
        } else {
            super::strip_own(&resolved)
        }
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
        type_registry::resolve_type_expr(
            ty_expr,
            self.type_param_map,
            self.type_param_arity,
            reg,
            ResolutionContext::UserAnnotation,
            self.self_type.as_ref(),
        )
        .map_err(|e| e.enrich_unknown_type_with_env(self.env))
        .map_err(|e| super::spanned(e, span))
    }

    pub fn unwrap_own_fn(&self, ty: &Type) -> Type {
        match ty {
            Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)) => *inner.clone(),
            other => other.clone(),
        }
    }

    /// Bidirectional constructor synthesis predicate (disposable.md §"Literal
    /// and constructor synthesis"). Constructors synthesize bare `T` unless
    /// the expected context walks to `Own(T)`, in which case they target `~T`
    /// directly. `MaybeOwn` on expected is ignored at synthesis time — it only
    /// appears during deferred unification, long after this check.
    fn expected_wants_own(&self, expected: Option<&Type>) -> bool {
        match expected.map(|t| self.subst.apply(t)) {
            Some(Type::Own(_)) => true,
            _ => false,
        }
    }

    pub fn extract_fn_params(&self, ty: &Type) -> Option<Vec<Type>> {
        match ty {
            Type::Fn(params, _) => Some(params.iter().map(|(_, t)| t.clone()).collect()),
            Type::Own(inner) => match inner.as_ref() {
                Type::Fn(params, _) => Some(params.iter().map(|(_, t)| t.clone()).collect()),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn resolved_type_ref_for_name(&self, name: &str) -> Option<ResolvedTypeRef> {
        let registry = self.registry?;
        let canonical_name = registry.canonical_name(name);
        let source_module = self
            .imported_type_info
            .get(canonical_name)
            .map(|(module_path, _)| module_path.as_str())
            .unwrap_or(self.module_path);
        Some(super::type_binding_ref(
            source_module.to_string(),
            canonical_name.to_string(),
        ))
    }

    pub(super) fn resolved_type_ref_for_type(&self, ty: &Type) -> Option<ResolvedTypeRef> {
        match ty {
            Type::Named(name, _) => self.resolved_type_ref_for_name(name),
            Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
                self.resolved_type_ref_for_type(inner)
            }
            _ => None,
        }
    }

    /// Shared tail for qualified-call paths: infer args with parameter expected-type
    /// propagation, coerce own args, unify, and build `TypedExpr::App`.
    // TODO: consolidate with Expr::App per-arg coerce_unify logic
    fn infer_call_args_and_unify(
        &mut self,
        func_typed: TypedExpr,
        func_ty: &Type,
        args: &[Expr],
        is_constructor: bool,
        expected_type: Option<&Type>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let func_param_types = self.extract_fn_params(func_ty);
        let callee_name = match &func_typed.kind {
            TypedExprKind::Var(name) => Some(name.as_str()),
            _ => None,
        };
        let mut args_typed = Vec::new();
        let mut arg_types = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let arg_expected_type = func_param_types.as_ref().and_then(|fparams| {
                fparams
                    .get(i)
                    .map(|expected_arg_ty| self.subst.apply(expected_arg_ty))
            });
            let a_typed = self
                .infer_expr_inner(a, arg_expected_type.as_ref())
                .map_err(|mut err| {
                    if err.secondary_span.is_none() && matches!(a, Expr::Lambda { .. }) {
                        if let Some(cname) = callee_name {
                            if let Some(def) = self.env.get_def_span(cname) {
                                let resolved_fn_ty = self.subst.apply(func_ty);
                                err.secondary_span = Some(Box::new(SecondaryLabel {
                                    span: def.span,
                                    message: format!(
                                        "`{cname}` defined here, expects {}",
                                        resolved_fn_ty.renumber_for_display()
                                    ),
                                    source_file: def.source_module.clone(),
                                }));
                            }
                        }
                    }
                    err
                })?;
            arg_types.push(a_typed.ty.clone());
            args_typed.push(a_typed);
        }

        let ret_var = Type::Var(self.fresh());

        // Resolve function type and extract params + return for per-arg coerce_unify
        let resolved_func = self.subst.apply(func_ty);
        let unwrapped = self.unwrap_own_fn(&resolved_func);
        match &unwrapped {
            Type::Fn(param_types, ret_type) => {
                if param_types.len() != arg_types.len() {
                    return Err(super::spanned(
                        TypeError::WrongArity {
                            expected: param_types.len(),
                            actual: arg_types.len(),
                        },
                        span,
                    ));
                }
                // Per-arg coerce_unify: directional, catches fabrication structurally
                for (i, (arg_ty, (_, param_ty))) in
                    arg_types.iter().zip(param_types.iter()).enumerate()
                {
                    coerce_unify(arg_ty, param_ty, self.subst).map_err(|e| {
                        let mut err = super::spanned(e, span);
                        if matches!(&*err.error, TypeError::OwnershipMismatch { .. }) {
                            if let Some(cname) = callee_name {
                                let note = if let Some(Expr::Var { name: arg_name, .. }) = args.get(i) {
                                    format!("`{cname}` requires an owned argument, but `{arg_name}` is not owned")
                                } else {
                                    format!("`{cname}` requires an owned argument at position {}", i + 1)
                                };
                                err.note = Some(note);
                            }
                        }
                        if err.secondary_span.is_none() {
                            if let Some(cname) = callee_name {
                                if let Some(def) = self.env.get_def_span(cname) {
                                    let resolved_fn_ty = self.subst.apply(func_ty);
                                    err.secondary_span = Some(Box::new(SecondaryLabel {
                                        span: def.span,
                                        message: format!("`{cname}` defined here, expects {}", resolved_fn_ty.renumber_for_display()),
                                        source_file: def.source_module.clone(),
                                    }));
                                }
                            }
                        }
                        err
                    })?;
                }
                // Propagate return type — plain unify preserves Own from resolved type
                unify(ret_type, &ret_var, self.subst).map_err(|e| super::spanned(e, span))?;
            }
            _ => {
                if super::is_concrete_non_function(func_ty, self.subst) {
                    let actual = self.subst.apply(func_ty);
                    return Err(super::spanned(TypeError::NotAFunction { actual }, span));
                }
                // Function type not yet resolved — defer ownership on args rather than stripping.
                // MaybeOwn preserves the possibility of ~T being needed once the callee resolves.
                let deferred_args: Vec<Type> = arg_types
                    .iter()
                    .map(|t| super::defer_own(t, self.subst))
                    .collect();
                let expected_fn = Type::fn_consuming(deferred_args, ret_var.clone());
                unify(&unwrapped, &expected_fn, self.subst).map_err(|e| super::spanned(e, span))?;
            }
        }

        let ty = self.subst.apply(&ret_var);
        let wrap = is_constructor && self.expected_wants_own(expected_type);
        Ok(TypedExpr {
            kind: TypedExprKind::App {
                func: Box::new(func_typed),
                args: args_typed,
            },
            ty: if wrap { Type::Own(Box::new(ty)) } else { ty },
            span,
            resolved_ref: None,
            scope_id: None,
        })
    }

    pub fn fresh(&mut self) -> TypeVarId {
        self.gen.fresh()
    }

    // ── Expr::App dispatch paths ─────────────────────────────────────────

    /// Path 1: Qualified module call via Var syntax — `receiver.fn(args...)` where
    /// `receiver` is a module qualifier not bound in the local env.
    fn infer_qualified_var_call(
        &mut self,
        func: &Expr,
        args: &[Expr],
        expected_type: Option<&Type>,
        span: Span,
    ) -> Option<Result<TypedExpr, SpannedTypeError>> {
        let qualified_call = match (func, args.first()) {
            (
                Expr::Var {
                    name: export_name, ..
                },
                Some(Expr::Var {
                    name: qualifier, ..
                }),
            ) => Some((qualifier.clone(), export_name.clone(), Vec::new())),
            (
                Expr::TypeApp {
                    expr, type_args, ..
                },
                Some(Expr::Var {
                    name: qualifier, ..
                }),
            ) => match expr.as_ref() {
                Expr::Var {
                    name: export_name, ..
                } => Some((qualifier.clone(), export_name.clone(), type_args.clone())),
                _ => None,
            },
            _ => None,
        };
        let (qualifier, export_name, explicit_type_args) = qualified_call?;
        if self.env.lookup(&qualifier).is_some() {
            return None;
        }
        let binding = self.qualified_modules.get(&qualifier)?;
        Some(self.infer_qualified_var_call_inner(
            binding,
            &qualifier,
            &export_name,
            &explicit_type_args,
            args,
            expected_type,
            span,
        ))
    }

    fn infer_qualified_var_call_inner(
        &mut self,
        binding: &super::QualifiedModuleBinding,
        qualifier: &str,
        export_name: &str,
        explicit_type_args: &[TypeExpr],
        args: &[Expr],
        expected_type: Option<&Type>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let Some(export) = binding.exports.get(export_name) else {
            return Err(super::spanned(
                TypeError::UnknownQualifiedExport {
                    qualifier: qualifier.to_string(),
                    module_path: binding.module_path.clone(),
                    name: export_name.to_string(),
                },
                span,
            ));
        };

        let is_constructor = self.registry.is_some_and(|r| r.is_constructor(export_name));
        let resolved_name = if is_constructor {
            export_name.to_string()
        } else {
            export.local_name.clone()
        };
        let func_ty = if explicit_type_args.is_empty() {
            export.scheme.instantiate(&mut || self.gen.fresh())
        } else {
            let reg = self.registry.ok_or_else(|| {
                super::spanned(
                    TypeError::UnsupportedExpr {
                        description: "explicit type application requires the type registry"
                            .to_string(),
                    },
                    span,
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
                        ResolutionContext::UserAnnotation,
                        self.self_type.as_ref(),
                    )
                    .map_err(|e| super::spanned(e, span))
                })
                .collect::<Result<Vec<_>, _>>()?;
            super::instantiate_scheme_with_types(&export.scheme, &explicit_types, span, self.gen)?
        };
        let func_typed = TypedExpr {
            kind: TypedExprKind::Var(resolved_name),
            ty: func_ty.clone(),
            span,
            resolved_ref: export.resolved_ref.clone(),
            scope_id: None,
        };
        let actual_args = &args[1..];
        self.infer_call_args_and_unify(
            func_typed,
            &func_ty,
            actual_args,
            is_constructor,
            expected_type,
            span,
        )
    }

    /// Path 3: Qualified module call via field-access syntax — `Module.fn(args...)`.
    fn infer_qualified_field_call(
        &mut self,
        func: &Expr,
        args: &[Expr],
        expected_type: Option<&Type>,
        span: Span,
    ) -> Option<Result<TypedExpr, SpannedTypeError>> {
        let Expr::FieldAccess {
            expr: qualifier_expr,
            field,
            ..
        } = func
        else {
            return None;
        };
        let Expr::Var {
            name: qualifier, ..
        } = qualifier_expr.as_ref()
        else {
            return None;
        };
        if self.env.lookup(qualifier).is_some() {
            return None;
        }
        let binding = self.qualified_modules.get(qualifier)?;
        let Some(export) = binding.exports.get(field) else {
            return Some(Err(super::spanned(
                TypeError::UnknownQualifiedExport {
                    qualifier: qualifier.clone(),
                    module_path: binding.module_path.clone(),
                    name: field.clone(),
                },
                span,
            )));
        };
        let is_constructor = self.registry.is_some_and(|r| r.is_constructor(field));
        let resolved_name = if is_constructor {
            field.clone()
        } else {
            export.local_name.clone()
        };
        let func_ty = export.scheme.instantiate(&mut || self.gen.fresh());
        let wrap_nullary = is_constructor
            && !matches!(&func_ty, Type::Fn(_, _))
            && self.expected_wants_own(expected_type);
        let func_typed = TypedExpr {
            kind: TypedExprKind::Var(resolved_name),
            ty: if wrap_nullary {
                Type::Own(Box::new(func_ty.clone()))
            } else {
                func_ty.clone()
            },
            span,
            resolved_ref: export.resolved_ref.clone(),
            scope_id: None,
        };

        Some(self.infer_call_args_and_unify(
            func_typed,
            &func_ty,
            args,
            is_constructor,
            expected_type,
            span,
        ))
    }

    /// Path 4: General HM function application — infer func, infer args with
    /// bidirectional lambda propagation, per-arg coerce_unify, return type unify.
    fn infer_general_call(
        &mut self,
        func: &Expr,
        args: &[Expr],
        is_ufcs: bool,
        expected_type: Option<&Type>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let func_typed = self.infer_expr_inner(func, None)?;
        let is_constructor = if let Expr::Var { name, .. } = func {
            self.registry.is_some_and(|r| r.is_constructor(name))
        } else {
            false
        };

        // Let the expected result type steer polymorphic callee instantiation
        // before argument inference. For `identity(buf) : ~String`, this pins
        // `a = ~String` before the parameter expectation is propagated to
        // `buf`. Constructors are handled by bidirectional synthesis below:
        // their bare return type is wrapped when the expected type wants `~T`.
        if !is_constructor {
            if let Some(expected) = expected_type {
                let resolved_func_ty = self.subst.apply(&func_typed.ty);
                let unwrapped = self.unwrap_own_fn(&resolved_func_ty);
                if let Type::Fn(_, ret_type) = &unwrapped {
                    coerce_unify(ret_type, expected, self.subst).map_err(|e| {
                        let mut err = super::spanned(e, span);
                        self.add_shadowed_prelude_note(&mut err, is_ufcs);
                        err
                    })?;
                }
            }
        }

        // Extract expected parameter types from the function signature so we can
        // propagate them into argument inference for bidirectional checking.
        let func_param_types: Option<Vec<Type>> = {
            let resolved_func_ty = self.subst.apply(&func_typed.ty);
            let unwrapped = match &resolved_func_ty {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            if let Type::Fn(params, _) = unwrapped {
                Some(params.iter().map(|(_, t)| t.clone()).collect())
            } else {
                None
            }
        };

        let callee_name = if let Expr::Var { name, .. } = func {
            Some(name.as_str())
        } else {
            None
        };

        let mut args_typed = Vec::new();
        let mut arg_types = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let arg_expected_type = func_param_types.as_ref().and_then(|fparams| {
                fparams
                    .get(i)
                    .map(|expected_arg_ty| self.subst.apply(expected_arg_ty))
            });
            let a_typed = self
                .infer_expr_inner(a, arg_expected_type.as_ref())
                .map_err(|mut err| {
                    if err.secondary_span.is_none() && matches!(a, Expr::Lambda { .. }) {
                        if let Some(cname) = callee_name {
                            if let Some(def) = self.env.get_def_span(cname) {
                                let resolved_fn_ty = self.subst.apply(&func_typed.ty);
                                err.secondary_span = Some(Box::new(SecondaryLabel {
                                    span: def.span,
                                    message: format!(
                                        "`{cname}` defined here, expects {}",
                                        resolved_fn_ty.renumber_for_display()
                                    ),
                                    source_file: def.source_module.clone(),
                                }));
                            }
                        }
                    }
                    err
                })?;
            let a_ty = a_typed.ty.clone();
            arg_types.push(a_ty.clone());
            args_typed.push(a_typed);
            // Eagerly unify non-lambda args with their expected parameter types.
            // This resolves generic type variables (e.g., T -> Player) before
            // we process subsequent lambda arguments that depend on them.
            if !matches!(a, Expr::Lambda { .. }) {
                if let Some(ref fparams) = func_param_types {
                    if let Some(expected_param_ty) = fparams.get(i) {
                        // Best-effort early resolution to help subsequent lambda args
                        // infer correctly. The formal per-arg coerce_unify below catches
                        // any actual type mismatch with full error context.
                        let _ = coerce_unify(&a_ty, expected_param_ty, self.subst);
                    }
                }
            }
        }

        let ret_var = Type::Var(self.fresh());

        // Resolve function type and extract params + return for per-arg coerce_unify
        let resolved_func = self.subst.apply(&func_typed.ty);
        let unwrapped = self.unwrap_own_fn(&resolved_func);
        match &unwrapped {
            Type::Fn(param_types, ret_type) => {
                if param_types.len() != arg_types.len() {
                    return Err(super::spanned(
                        TypeError::WrongArity {
                            expected: param_types.len(),
                            actual: arg_types.len(),
                        },
                        span,
                    ));
                }
                // Per-arg coerce_unify: directional, catches fabrication structurally
                for (i, (arg_ty, (_, param_ty))) in
                    arg_types.iter().zip(param_types.iter()).enumerate()
                {
                    coerce_unify(arg_ty, param_ty, self.subst).map_err(|e| {
                        let mut err = super::spanned(e, span);
                        // Add ownership-specific notes
                        if matches!(&*err.error, TypeError::OwnershipMismatch { .. }) {
                            if let Some(cname) = callee_name {
                                let note = if let Some(Expr::Var { name: arg_name, .. }) = args.get(i) {
                                    format!("`{cname}` requires an owned argument, but `{arg_name}` is not owned")
                                } else {
                                    format!("`{cname}` requires an owned argument at position {}", i + 1)
                                };
                                err.note = Some(note);
                            }
                        }
                        if matches!(
                            &*err.error,
                            TypeError::Mismatch { .. }
                                | TypeError::FnCapabilityMismatch { .. }
                                | TypeError::ParamModeMismatch { .. }
                        ) {
                            if let Some(ref captures) = self.lambda_own_captures {
                                for arg in args.iter() {
                                    if let Expr::Lambda { span: lspan, .. } = arg {
                                        if let Some(cap_name) = captures.get(lspan) {
                                            err.note = Some(format!(
                                                "closure is single-use because it captures `~` value `{}`",
                                                cap_name
                                            ));
                                            break;
                                        }
                                    }
                                }
                            }
                            self.add_shadowed_prelude_note(&mut err, is_ufcs);
                        }
                        if err.secondary_span.is_none() {
                            if let Some(cname) = callee_name {
                                if let Some(def) = self.env.get_def_span(cname) {
                                    let resolved_fn_ty = self.subst.apply(&func_typed.ty);
                                    err.secondary_span = Some(Box::new(SecondaryLabel {
                                        span: def.span,
                                        message: format!("`{cname}` defined here, expects {}", resolved_fn_ty.renumber_for_display()),
                                        source_file: def.source_module.clone(),
                                    }));
                                }
                            }
                        }
                        err
                    })?;
                }
                // Propagate return type — plain unify preserves Own from resolved type
                unify(ret_type, &ret_var, self.subst).map_err(|e| super::spanned(e, span))?;
            }
            _ => {
                if super::is_concrete_non_function(&func_typed.ty, self.subst) {
                    let actual = self.subst.apply(&func_typed.ty);
                    return Err(super::spanned(TypeError::NotAFunction { actual }, span));
                }
                // Function type not yet resolved — defer ownership on args rather than stripping.
                // MaybeOwn preserves the possibility of ~T being needed once the callee resolves.
                let deferred_args: Vec<Type> = arg_types
                    .iter()
                    .map(|t| super::defer_own(t, self.subst))
                    .collect();
                let expected_fn = Type::fn_consuming(deferred_args, ret_var.clone());
                unify(&unwrapped, &expected_fn, self.subst).map_err(|e| super::spanned(e, span))?;
            }
        }

        let ty = self.subst.apply(&ret_var);
        let ty = if is_constructor && self.expected_wants_own(expected_type) {
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
            span,
            resolved_ref: None,
            scope_id: None,
        })
    }

    // ── Extracted match-arm helpers ─────────────────────────────────────

    fn infer_lambda(
        &mut self,
        params: &[Param],
        body: &Expr,
        span: Span,
        expected_type: Option<&Type>,
    ) -> Result<TypedExpr, SpannedTypeError> {
        // Extract expected parameter types from the expected_type if it's a function type.
        let expected_params: Option<&[(crate::types::ParamMode, Type)]> =
            expected_type.and_then(|et| {
                let unwrapped = match et {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                match unwrapped {
                    Type::Fn(params, _) => Some(params.as_slice()),
                    _ => None,
                }
            });
        let expected_return: Option<Type> = expected_type.and_then(|et| {
            let unwrapped = match et {
                Type::Own(inner) => inner.as_ref(),
                other => other,
            };
            match unwrapped {
                Type::Fn(_, ret) => Some(ret.as_ref().clone()),
                _ => None,
            }
        });
        let mut seen_params = HashSet::new();
        for p in params.iter() {
            if !seen_params.insert(&p.name) {
                return Err(super::spanned(
                    TypeError::DuplicateParam {
                        name: p.name.clone(),
                    },
                    p.span,
                ));
            }
        }

        let mut param_types = Vec::new();
        self.env.push_scope();
        for (i, p) in params.iter().enumerate() {
            let tv = Type::Var(self.fresh());
            if let Some(expected) = expected_params {
                if let Some((_, expected_ty)) = expected.get(i) {
                    unify(&tv, expected_ty, self.subst).map_err(|e| super::spanned(e, p.span))?;
                }
            }
            param_types.push(tv.clone());
            self.env.bind(p.name.clone(), TypeScheme::mono(tv));
        }
        // Save and set an independent fn_return_type for this lambda.
        // Lambdas need their own return type so the `?` operator inside
        // a lambda targets the lambda's return, not the enclosing function's.
        let prev_fn_return_type = self.env.fn_return_type.take();
        let fn_ret_expected = expected_return.unwrap_or_else(|| Type::Var(self.fresh()));
        self.env.fn_return_type = Some(fn_ret_expected.clone());
        let saved_recur = self.recur_params.take();
        self.recur_params = Some(param_types.clone());
        let body_typed = self.infer_expr_inner(body, Some(&fn_ret_expected))?;
        self.recur_params = saved_recur;
        self.env.fn_return_type = prev_fn_return_type;
        self.env.pop_scope();
        let param_types: Vec<Type> = param_types.iter().map(|t| self.subst.apply(t)).collect();
        let body_ty = self.subst.apply(&body_typed.ty);
        let fn_params: Vec<(crate::types::ParamMode, Type)> = params
            .iter()
            .zip(param_types)
            .map(|(p, ty)| (p.mode, ty))
            .collect();
        let fn_ty = Type::Fn(fn_params, Box::new(body_ty));
        let param_names: HashSet<&str> = params.iter().map(|p| p.name.as_str()).collect();
        let ty = if let Some(cap_name) =
            super::first_own_capture(body, &param_names, self.env, self.subst, &body_typed)
        {
            if let Some(ref mut captures) = self.lambda_own_captures {
                captures.insert(span, cap_name);
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
            span,
            resolved_ref: None,
            scope_id: None,
        })
    }

    fn infer_type_app(
        &mut self,
        expr: &Expr,
        type_args: &[TypeExpr],
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
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
                        ResolutionContext::UserAnnotation,
                        self.self_type.as_ref(),
                    )
                    .map_err(|e| super::spanned(e, span))
                })
                .collect::<Result<Vec<_>, _>>()?
        } else {
            return Err(super::spanned(
                TypeError::UnsupportedExpr {
                    description: "explicit type application requires the type registry".to_string(),
                },
                span,
            ));
        };

        let specialized_ty = match expr {
            Expr::Var { name, .. } => {
                let Some(scheme) = self.env.lookup(name).cloned() else {
                    return Err(super::spanned(
                        TypeError::UnknownVariable { name: name.clone() },
                        span,
                    ));
                };
                super::instantiate_scheme_with_types(&scheme, &explicit_types, span, self.gen)?
            }
            _ => {
                return Err(super::spanned(
                    TypeError::UnsupportedExpr {
                        description: "explicit type arguments are only supported on named values"
                            .to_string(),
                    },
                    span,
                ))
            }
        };

        let resolved_ref = expr_typed.resolved_ref.clone();
        Ok(TypedExpr {
            kind: TypedExprKind::TypeApp {
                expr: Box::new(expr_typed),
                type_args: explicit_types,
            },
            ty: specialized_ty,
            span,
            resolved_ref,
            scope_id: None,
        })
    }

    fn infer_let(
        &mut self,
        name: &str,
        ty_ann: Option<&TypeExpr>,
        value: &Expr,
        body: Option<&Expr>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let snap = self.subst.push_qual_scope();

        let result: Result<(TypedExpr, Type), SpannedTypeError> = (|| {
            // Resolve the annotation *before* inferring the RHS so that the
            // annotation type can steer bidirectional constructor synthesis
            // (disposable.md §"Literal and constructor synthesis"). Without
            // this, a `let x: List[Int] = Cons(1, Nil)` would synthesize
            // `~List[Int]` from the constructor and then need to drop — but
            // the `~T → T` drop coercion no longer exists.
            let resolved_ann: Option<Type> = if let Some(ty_expr) = ty_ann {
                if self.registry.is_some() {
                    Some(self.resolve_type_expr_spanned(ty_expr, span)?)
                } else {
                    None
                }
            } else {
                None
            };
            let val_typed = self.infer_expr_inner(value, resolved_ann.as_ref())?;

            // Unify the RHS against the annotation (already resolved above).
            // With bidirectional synthesis feeding the annotation in as expected,
            // this coerce_unify is a no-op for constructor RHS in the common case
            // and remains the safety net for non-constructor flows.
            let binding_ty = if let Some(annotated_ty) = resolved_ann {
                coerce_unify(&val_typed.ty, &annotated_ty, self.subst).map_err(|e| {
                    let mut err = super::spanned(e, span);
                    if matches!(
                        &*err.error,
                        TypeError::Mismatch { .. }
                            | TypeError::FnCapabilityMismatch { .. }
                            | TypeError::ParamModeMismatch { .. }
                    ) {
                        if let Expr::Lambda { span: lspan, .. } = value {
                            if let Some(ref captures) = self.lambda_own_captures {
                                if let Some(cap_name) = captures.get(lspan) {
                                    err.note = Some(format!(
                                        "closure is single-use because it captures `~` value `{}`",
                                        cap_name
                                    ));
                                }
                            }
                        }
                    }
                    err
                })?;
                annotated_ty
            } else {
                val_typed.ty.clone()
            };

            // Monomorphism restriction: don't generalize let bindings whose
            // generalized type variables are constrained by traits (e.g. Mul, Add).
            // Without this, IR lowering receives unresolved dict references.
            let scheme = {
                let tentative = super::generalize(&binding_ty, self.env, self.subst);
                if tentative.vars.is_empty() {
                    tentative
                } else {
                    let gen_vars: HashSet<TypeVarId> = tentative.vars.iter().copied().collect();
                    let has_trait_constraints =
                        collect_trait_constraints_on_vars(&val_typed, self.subst, &gen_vars);
                    if has_trait_constraints {
                        TypeScheme::mono(self.subst.apply(&binding_ty))
                    } else {
                        tentative
                    }
                }
            };

            let typed_expr = match body {
                Some(body) => {
                    self.env.push_scope();
                    self.env.bind(name.to_string(), scheme);
                    let body_result = self.infer_expr_inner(body, None);
                    self.env.pop_scope(); // always pops, even on error
                    let body_typed = body_result?;
                    let ty = body_typed.ty.clone();
                    TypedExpr {
                        kind: TypedExprKind::Let {
                            name: name.to_string(),
                            value: Box::new(val_typed),
                            body: Some(Box::new(body_typed)),
                        },
                        ty,
                        span,
                        resolved_ref: None,
                        scope_id: None,
                    }
                }
                None => {
                    self.env.bind(name.to_string(), scheme);
                    TypedExpr {
                        kind: TypedExprKind::Let {
                            name: name.to_string(),
                            value: Box::new(val_typed),
                            body: None,
                        },
                        ty: Type::Unit,
                        span,
                        resolved_ref: None,
                        scope_id: None,
                    }
                }
            };
            Ok((typed_expr, binding_ty))
        })();

        match &result {
            Ok(_) => self.subst.commit_qual_scope(snap),
            Err(_) => self.subst.rollback_qual_scope(snap),
        }
        let (typed_expr, binding_ty) = result?;

        // Post-commit: qualifiers are resolved, check for Own types
        let resolved_val = self.subst.apply(&binding_ty);
        if matches!(&resolved_val, Type::Own(_)) {
            if let Some(ref mut los) = self.let_own_spans {
                los.insert(span);
            }
        }
        Ok(typed_expr)
    }

    fn infer_binary_op(
        &mut self,
        op: &BinOp,
        lhs: &Expr,
        rhs: &Expr,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let lhs_typed = self.infer_expr_inner(lhs, None)?;
        let rhs_typed = self.infer_expr_inner(rhs, None)?;
        let ty = match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                self.join_types_spanned(&lhs_typed.ty, &rhs_typed.ty, span)?;
                super::strip_own(&self.subst.apply(&lhs_typed.ty))
            }
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                self.join_types_spanned(&lhs_typed.ty, &rhs_typed.ty, span)?;
                Type::Bool
            }
            BinOp::And | BinOp::Or => {
                self.coerce_unify_spanned(&lhs_typed.ty, &Type::Bool, span)?;
                self.coerce_unify_spanned(&rhs_typed.ty, &Type::Bool, span)?;
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
            span,
            resolved_ref: None,
            scope_id: None,
        })
    }

    fn infer_field_access(
        &mut self,
        target: &Expr,
        field: &str,
        expected_type: Option<&Type>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        if let Expr::Var {
            name: qualifier, ..
        } = target
        {
            if self.env.lookup(qualifier).is_none() {
                if let Some(binding) = self.qualified_modules.get(qualifier) {
                    let Some(export) = binding.exports.get(field) else {
                        return Err(super::spanned(
                            TypeError::UnknownQualifiedExport {
                                qualifier: qualifier.clone(),
                                module_path: binding.module_path.clone(),
                                name: field.to_string(),
                            },
                            span,
                        ));
                    };
                    let is_constructor = self.registry.is_some_and(|r| r.is_constructor(field));
                    let resolved_name = if is_constructor {
                        field.to_string()
                    } else {
                        export.local_name.clone()
                    };
                    let export_ty = export.scheme.instantiate(&mut || self.gen.fresh());
                    let ty = if is_constructor
                        && !matches!(&export_ty, Type::Fn(_, _))
                        && self.expected_wants_own(expected_type)
                    {
                        Type::Own(Box::new(export_ty.clone()))
                    } else {
                        export_ty.clone()
                    };
                    return Ok(TypedExpr {
                        kind: TypedExprKind::Var(resolved_name),
                        ty,
                        span,
                        resolved_ref: export.resolved_ref.clone(),
                        scope_id: None,
                    });
                }
            }
        }
        let target_typed = self.infer_expr_inner(target, None)?;
        let resolved = self.subst.apply(&target_typed.ty);
        let base_is_owned = matches!(&resolved, Type::Own(_) | Type::Shape(_) | Type::MaybeOwn(_, _));
        // Unwrap Own/MaybeOwn/Shape wrapper — field access works on the inner type
        let inner_resolved = match &resolved {
            Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => inner.as_ref(),
            other => other,
        };
        let field_ty = self.resolve_field_access(inner_resolved, field, span)?;
        // Apply coercion: shared base strips ~T from non-fn fields, errors on ~fn
        let ty = if !base_is_owned {
            match &field_ty {
                Type::Own(inner) if matches!(inner.as_ref(), Type::Fn(_, _)) => {
                    let mut err = super::spanned(
                        TypeError::Mismatch {
                            expected: field_ty.clone(),
                            actual: (**inner).clone(),
                        },
                        span,
                    );
                    err.note = Some(format!(
                        "cannot access owned function field `{}` from a shared struct — take ownership of the struct first",
                        field
                    ));
                    return Err(err);
                }
                Type::Own(inner) => (**inner).clone(),
                _ => field_ty,
            }
        } else {
            field_ty
        };
        Ok(TypedExpr {
            kind: TypedExprKind::FieldAccess {
                expr: Box::new(target_typed),
                field: field.to_string(),
                resolved_type_ref: self.resolved_type_ref_for_type(inner_resolved),
            },
            ty,
            span,
            resolved_ref: None,
            scope_id: None,
        })
    }

    fn infer_match(
        &mut self,
        scrutinee: &Expr,
        arms: &[MatchArm],
        expected_type: Option<&Type>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let scrutinee_typed = self.infer_expr_inner(scrutinee, None)?;
        let scrutinee_ty = self.subst.apply(&scrutinee_typed.ty);
        let scrutinee_is_owned =
            matches!(&scrutinee_ty, Type::Own(_) | Type::Shape(_) | Type::MaybeOwn(_, _));
        // Unwrap Own/MaybeOwn/Shape wrapper — match works on the inner type
        let match_ty = match &scrutinee_ty {
            Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
                inner.as_ref().clone()
            }
            other => other.clone(),
        };
        let mut result_ty: Option<Type> = None;
        let mut branch_types = Vec::new();
        let mut typed_arms = Vec::new();
        for arm in arms {
            self.env.push_scope();
            let typed_pattern =
                self.check_pattern(&arm.pattern, &match_ty, span, scrutinee_is_owned)?;
            let typed_guard = if let Some(guard_expr) = &arm.guard {
                let guard_typed = self.infer_expr_inner(guard_expr, None)?;
                self.unify_spanned(&guard_typed.ty, &Type::Bool, guard_typed.span)?;
                Some(Box::new(guard_typed))
            } else {
                None
            };
            let body_typed = self.infer_expr_inner(&arm.body, expected_type)?;
            match &result_ty {
                None => {
                    result_ty = Some(body_typed.ty.clone());
                }
                Some(prev) => {
                    let prev_resolved = self.subst.apply(prev);
                    self.join_types_spanned(&prev_resolved, &body_typed.ty, span)?;
                    result_ty = Some(prev_resolved);
                }
            }
            branch_types.push(body_typed.ty.clone());
            self.env.pop_scope();
            typed_arms.push(TypedMatchArm {
                pattern: typed_pattern,
                guard: typed_guard,
                body: body_typed,
            });
        }
        let match_ty = self.subst.apply(&match_ty);
        crate::exhaustiveness::check_exhaustiveness(&match_ty, &typed_arms, self.registry, span)?;
        let ty = if branch_types.is_empty() {
            Type::Unit
        } else {
            self.resolve_join_ownership(&branch_types)
        };
        Ok(TypedExpr {
            kind: TypedExprKind::Match {
                scrutinee: Box::new(scrutinee_typed),
                arms: typed_arms,
            },
            ty,
            span,
            resolved_ref: None,
            scope_id: None,
        })
    }

    fn infer_let_pattern(
        &mut self,
        pattern: &Pattern,
        ty_ann: Option<&TypeExpr>,
        value: &Expr,
        body: Option<&Expr>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        // Resolve an annotation before inferring the RHS so constructors inside
        // the RHS can synthesize directly to the annotated form.
        let resolved_ann: Option<Type> = if let Some(ty_expr) = ty_ann {
            if self.registry.is_some() {
                Some(self.resolve_type_expr_spanned(ty_expr, span)?)
            } else {
                None
            }
        } else {
            None
        };
        let val_typed = self.infer_expr_inner(value, resolved_ann.as_ref())?;

        let binding_ty = if let Some(annotated_ty) = resolved_ann {
            self.coerce_unify_spanned(&val_typed.ty, &annotated_ty, span)?;
            annotated_ty
        } else {
            self.subst.apply(&val_typed.ty)
        };

        // For let-patterns, only apply shared-scrutinee coercion when the
        // RHS is a plain variable with a non-owned type (i.e., destructuring
        // a shared parameter). For all other RHS expressions (function calls,
        // constructors, tuples, etc.), the value is freshly produced and inner
        // `~T` fields should be preserved.
        let scrutinee_is_owned = match value {
            Expr::Var { .. } => matches!(&binding_ty, Type::Own(_)),
            _ => true,
        };
        match body {
            Some(body) => {
                self.env.push_scope();
                let typed_pattern =
                    self.check_pattern(pattern, &binding_ty, span, scrutinee_is_owned)?;
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
                    span,
                    resolved_ref: None,
                    scope_id: None,
                })
            }
            None => {
                let typed_pattern =
                    self.check_pattern(pattern, &binding_ty, span, scrutinee_is_owned)?;
                Ok(TypedExpr {
                    kind: TypedExprKind::LetPattern {
                        pattern: typed_pattern,
                        value: Box::new(val_typed),
                        body: None,
                    },
                    ty: Type::Unit,
                    span,
                    resolved_ref: None,
                    scope_id: None,
                })
            }
        }
    }

    fn infer_struct_lit(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        expected_type: Option<&Type>,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let reg = self.registry.ok_or_else(|| {
            super::spanned(
                TypeError::UnknownVariable {
                    name: name.to_string(),
                },
                span,
            )
        })?;
        let info = reg.lookup_type(name).ok_or_else(|| {
            super::spanned(
                TypeError::UnknownVariable {
                    name: name.to_string(),
                },
                span,
            )
        })?;
        match &info.kind {
            type_registry::TypeKind::Record {
                fields: record_fields,
            } => {
                let fresh_args: Vec<Type> = info
                    .type_param_vars
                    .iter()
                    .map(|_| Type::Var(self.fresh()))
                    .collect();
                let struct_ty = Type::Named(info.name.clone(), fresh_args.clone());
                let resolved_type_ref = self.resolved_type_ref_for_name(&info.name);

                let provided: HashSet<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                let missing: Vec<String> = record_fields
                    .iter()
                    .filter(|(n, _)| !provided.contains(n.as_str()))
                    .map(|(n, _)| n.clone())
                    .collect();
                if !missing.is_empty() {
                    return Err(super::spanned(
                        TypeError::MissingFields {
                            type_name: name.to_string(),
                            fields: missing,
                        },
                        span,
                    ));
                }

                let mut typed_fields = Vec::new();
                for (field_name, field_expr) in fields {
                    let record_field = record_fields.iter().find(|(n, _)| n == field_name);
                    match record_field {
                        Some((_, expected_ty)) => {
                            let expected =
                                super::instantiate_field_type(expected_ty, info, &fresh_args);
                            let field_typed = self.infer_expr_inner(field_expr, Some(&expected))?;
                            self.coerce_unify_spanned(&field_typed.ty, &expected, span)?;
                            typed_fields.push((field_name.clone(), field_typed));
                        }
                        None => {
                            return Err(super::spanned(
                                TypeError::UnknownField {
                                    type_name: name.to_string(),
                                    field_name: field_name.clone(),
                                },
                                span,
                            ));
                        }
                    }
                }

                let result_ty = if self.expected_wants_own(expected_type) {
                    Type::Own(Box::new(struct_ty))
                } else {
                    struct_ty
                };
                Ok(TypedExpr {
                    kind: TypedExprKind::StructLit {
                        name: name.to_string(),
                        fields: typed_fields,
                        resolved_type_ref,
                    },
                    ty: result_ty,
                    span,
                    resolved_ref: None,
                    scope_id: None,
                })
            }
            _ => Err(super::spanned(
                TypeError::NotAStruct {
                    actual: Type::Named(name.to_string(), vec![]),
                },
                span,
            )),
        }
    }

    fn infer_question_mark(
        &mut self,
        expr: &Expr,
        span: Span,
    ) -> Result<TypedExpr, SpannedTypeError> {
        let inner_typed = self.infer_expr_inner(expr, None)?;
        let inner_ty = self.subst.apply(&inner_typed.ty);
        // strip_own: structural — we need to read the Option/Result shape of
        // the operand regardless of whether it is wrapped in `~`. This is not
        // a data-level drop; the wrapper is preserved in the value flow.
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
                let fn_ret = self
                    .env
                    .fn_return_type
                    .as_ref()
                    .map(|t| self.subst.apply(t));
                // strip_own: structural — peek through `~` to inspect the
                // enclosing fn return shape (Option vs Result) for unification
                // steering only. The actual return type is unchanged.
                match fn_ret.as_ref().map(super::strip_own) {
                    Some(Type::Named(name, _)) if name == "Option" => {
                        let a = Type::Var(self.fresh());
                        let option_ty = Type::Named("Option".to_string(), vec![a.clone()]);
                        self.unify_spanned(&inner_ty_unwrapped, &option_ty, span)?;
                        (true, a)
                    }
                    Some(Type::Named(name, _)) if name == "Result" => {
                        let e = Type::Var(self.fresh());
                        let a = Type::Var(self.fresh());
                        let result_ty = Type::Named("Result".to_string(), vec![e, a.clone()]);
                        self.unify_spanned(&inner_ty_unwrapped, &result_ty, span)?;
                        (false, a)
                    }
                    _ => {
                        // Return type also unknown — default to Result
                        let e = Type::Var(self.fresh());
                        let a = Type::Var(self.fresh());
                        let result_ty = Type::Named("Result".to_string(), vec![e, a.clone()]);
                        self.unify_spanned(&inner_ty_unwrapped, &result_ty, span)?;
                        (false, a)
                    }
                }
            }
            other => {
                return Err(super::spanned(
                    TypeError::QuestionMarkBadOperand {
                        actual: other.clone(),
                    },
                    span,
                ));
            }
        };

        // Now check that the function's return type is compatible
        let fn_ret = self
            .env
            .fn_return_type
            .as_ref()
            .map(|t| self.subst.apply(t));
        // strip_own: structural — same rationale as above; we are reading the
        // enclosing fn's return shape to validate `?`, not dropping ownership
        // from a value flow.
        let fn_ret_unwrapped = fn_ret.map(|t| super::strip_own(&t));

        match &fn_ret_unwrapped {
            Some(Type::Named(name, args)) if name == "Option" => {
                if !is_option {
                    return Err(super::spanned(
                        TypeError::QuestionMarkMismatch {
                            expr_kind: "Result".to_string(),
                            return_kind: "Option".to_string(),
                        },
                        span,
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
                        span,
                    ));
                }
                // Result ? in Result fn — unify error types
                if args.len() == 2 {
                    // inner expr is Result[e1, a], fn returns Result[e2, b] → unify e1 = e2
                    let inner_resolved = self.subst.apply(&inner_ty_unwrapped);
                    if let Type::Named(_, inner_args) = &inner_resolved {
                        if inner_args.len() == 2 {
                            self.unify_spanned(&inner_args[0], &args[0], span)?;
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
                        self.unify_spanned(&self.subst.apply(ret), &option_ret, span)?;
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
                        self.unify_spanned(&self.subst.apply(ret), &result_ret, span)?;
                    }
                }
            }
            Some(other) => {
                return Err(super::spanned(
                    TypeError::QuestionMarkBadReturn {
                        actual: other.clone(),
                    },
                    span,
                ));
            }
            None => {
                return Err(super::spanned(
                    TypeError::QuestionMarkBadReturn { actual: Type::Unit },
                    span,
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
            span,
            resolved_ref: None,
            scope_id: None,
        })
    }

    pub(crate) fn infer_expr_inner(
        &mut self,
        expr: &Expr,
        expected_type: Option<&Type>,
    ) -> Result<TypedExpr, SpannedTypeError> {
        match expr {
            Expr::Lit { value, span } => {
                // Literals always synthesize bare `T`. The five literal types
                // (Int, Float, Bool, String, Unit) are all primitives that
                // cannot implement Disposable, so `~T` on a literal is never
                // semantically meaningful — there is no resource to track.
                // This is unconditional, regardless of the expected context:
                // a `let x: ~Int = 1` is rejected at the binding site by the
                // (intentionally absent) `T → ~T` coercion.
                let ty = match value {
                    Lit::Int(_) => Type::Int,
                    Lit::Float(_) => Type::Float,
                    Lit::Bool(_) => Type::Bool,
                    Lit::String(_) => Type::String,
                    Lit::Unit => Type::Unit,
                };
                Ok(TypedExpr {
                    kind: TypedExprKind::Lit(value.clone()),
                    ty,
                    span: *span,
                    resolved_ref: None,
                    scope_id: None,
                })
            }

            Expr::Var { name, span, .. } => match self.env.lookup_entry(name) {
                Some(entry) => {
                    let scheme = entry.scheme.clone();
                    let ty = scheme.instantiate(&mut || self.gen.fresh());
                    let ty = if !matches!(&ty, Type::Fn(_, _))
                        && self.registry.is_some_and(|r| r.is_constructor(name))
                        && self.expected_wants_own(expected_type)
                    {
                        Type::Own(Box::new(ty))
                    } else {
                        ty
                    };
                    let resolved_ref = super::resolved_ref_from_binding_source(&entry.source);
                    Ok(TypedExpr {
                        kind: TypedExprKind::Var(name.clone()),
                        ty,
                        span: *span,
                        resolved_ref,
                        scope_id: None,
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
            } => self.infer_lambda(params, body, *span, expected_type),

            Expr::App {
                func,
                args,
                is_ufcs,
                span,
                ..
            } => {
                // Dispatch: qualified Mod.fn → qualified field access
                //         → UFCS overload resolution → general HM application
                if let Some(result) =
                    self.infer_qualified_var_call(func, args, expected_type, *span)
                {
                    return result;
                }
                if let Some(result) =
                    self.infer_qualified_field_call(func, args, expected_type, *span)
                {
                    return result;
                }
                self.infer_general_call(func, args, *is_ufcs, expected_type, *span)
            }

            Expr::TypeApp {
                expr,
                type_args,
                span,
            } => self.infer_type_app(expr, type_args, *span),

            Expr::Let {
                name,
                ty: ty_ann,
                value,
                body,
                span,
            } => self.infer_let(name, ty_ann.as_ref(), value, body.as_deref(), *span),

            Expr::If {
                cond,
                then_,
                else_,
                span,
                ..
            } => {
                let cond_typed = self.infer_expr_inner(cond, None)?;
                self.coerce_unify_spanned(&cond_typed.ty, &Type::Bool, *span)?;
                let then_typed = self.infer_expr_inner(then_, expected_type)?;
                let else_typed = self.infer_expr_inner(else_, expected_type)?;
                self.join_types_spanned(&then_typed.ty, &else_typed.ty, *span)?;
                let ty =
                    self.resolve_join_ownership(&[then_typed.ty.clone(), else_typed.ty.clone()]);
                Ok(TypedExpr {
                    kind: TypedExprKind::If {
                        cond: Box::new(cond_typed),
                        then_: Box::new(then_typed),
                        else_: Box::new(else_typed),
                    },
                    ty,
                    span: *span,
                    resolved_ref: None,
                    scope_id: None,
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
                        resolved_ref: None,
                        scope_id: None,
                    });
                }
                let mut typed_exprs = Vec::new();
                for (idx, e) in exprs.iter().enumerate() {
                    let expr_expected = if idx + 1 == exprs.len() {
                        expected_type
                    } else {
                        None
                    };
                    typed_exprs.push(self.infer_expr_inner(e, expr_expected)?);
                }
                self.env.pop_scope();
                let ty = typed_exprs.last().unwrap().ty.clone();
                Ok(TypedExpr {
                    kind: TypedExprKind::Do(typed_exprs),
                    ty,
                    span: *span,
                    resolved_ref: None,
                    scope_id: None,
                })
            }

            Expr::BinaryOp {
                op, lhs, rhs, span, ..
            } => self.infer_binary_op(op, lhs, rhs, *span),

            Expr::UnaryOp {
                op, operand, span, ..
            } => {
                let operand_typed = self.infer_expr_inner(operand, None)?;
                let ty = match op {
                    UnaryOp::Neg => super::strip_own(&self.subst.apply(&operand_typed.ty)),
                    UnaryOp::Not => {
                        self.coerce_unify_spanned(&operand_typed.ty, &Type::Bool, *span)?;
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
                    resolved_ref: None,
                    scope_id: None,
                })
            }

            Expr::Recur { args, span, .. } => {
                let mut typed_args = Vec::new();
                match &self.recur_params {
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
                            let a_typed = self.infer_expr_inner(a, Some(p))?;
                            self.coerce_unify_spanned(&a_typed.ty, p, *span)?;
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
                    resolved_ref: None,
                    scope_id: None,
                })
            }

            Expr::FieldAccess {
                expr: target,
                field,
                span,
            } => self.infer_field_access(target, field, expected_type, *span),

            Expr::StructUpdate { base, fields, span } => {
                let base_typed = self.infer_expr_inner(base, None)?;
                let resolved = self.subst.apply(&base_typed.ty);
                // Unwrap Own/MaybeOwn/Shape wrapper — struct update works on the inner type
                let inner_resolved = match &resolved {
                    Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
                        inner.as_ref().clone()
                    }
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
                    resolved_ref: None,
                    scope_id: None,
                })
            }

            Expr::Match {
                scrutinee,
                arms,
                span,
            } => self.infer_match(scrutinee, arms, expected_type, *span),

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
                    resolved_ref: None,
                    scope_id: None,
                })
            }

            Expr::LetPattern {
                pattern,
                ty: ty_ann,
                value,
                body,
                span,
            } => self.infer_let_pattern(pattern, ty_ann.as_ref(), value, body.as_deref(), *span),

            Expr::StructLit { name, fields, span } => {
                self.infer_struct_lit(name, fields, expected_type, *span)
            }

            Expr::List { elements, span } => {
                // Infer as Vec[a] — [e1, e2, e3] produces Vec[elem_type]
                let elem_var = Type::Var(self.fresh());
                let mut typed_elems = Vec::new();
                for elem in elements {
                    let typed = self.infer_expr_inner(elem, None)?;
                    self.join_types_spanned(
                        &self.subst.apply(&typed.ty),
                        &self.subst.apply(&elem_var),
                        *span,
                    )?;
                    typed_elems.push(typed);
                }
                let resolved_elem = self.subst.apply(&elem_var);
                Ok(TypedExpr {
                    kind: TypedExprKind::VecLit(typed_elems),
                    ty: Type::Named("Vec".to_string(), vec![resolved_elem]),
                    span: *span,
                    resolved_ref: None,
                    scope_id: None,
                })
            }
            Expr::QuestionMark { expr, span } => self.infer_question_mark(expr, *span),
        }
    }
}

/// Check whether any of the given generalized type variables are constrained
/// by trait-dispatched operations (binary ops like +, *, ==, or trait method calls).
/// Used by the monomorphism restriction to prevent generalizing such bindings.
fn collect_trait_constraints_on_vars(
    expr: &TypedExpr,
    subst: &Substitution,
    generalized_vars: &HashSet<TypeVarId>,
) -> bool {
    let mut stack: Vec<&TypedExpr> = vec![expr];
    while let Some(e) = stack.pop() {
        match &e.kind {
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let is_trait_op = !matches!(op, BinOp::And | BinOp::Or);
                if is_trait_op {
                    let lhs_ty = subst.apply(&lhs.ty);
                    if let Type::Var(v) = super::strip_own(&lhs_ty) {
                        if generalized_vars.contains(&v) {
                            return true;
                        }
                    }
                }
                stack.push(lhs);
                stack.push(rhs);
            }
            TypedExprKind::App { func, args }
                if matches!(
                    func.resolved_ref,
                    Some(crate::typed_ast::ResolvedBindingRef::TraitMethod(_))
                ) =>
            {
                for arg in args {
                    let arg_ty = subst.apply(&arg.ty);
                    if let Type::Var(v) = super::strip_own(&arg_ty) {
                        if generalized_vars.contains(&v) {
                            return true;
                        }
                    }
                }
                stack.push(func);
                stack.extend(args.iter());
            }
            TypedExprKind::App { func, args } => {
                stack.push(func);
                stack.extend(args.iter());
            }
            TypedExprKind::Lambda { body, .. } => stack.push(body),
            TypedExprKind::Let { value, body, .. } => {
                stack.push(value);
                if let Some(b) = body {
                    stack.push(b);
                }
            }
            TypedExprKind::If { cond, then_, else_ } => {
                stack.push(cond);
                stack.push(then_);
                stack.push(else_);
            }
            TypedExprKind::Do(exprs) => stack.extend(exprs.iter()),
            TypedExprKind::Match { scrutinee, arms } => {
                stack.push(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        stack.push(guard);
                    }
                    stack.push(&arm.body);
                }
            }
            TypedExprKind::Tuple(es) | TypedExprKind::VecLit(es) | TypedExprKind::Recur(es) => {
                stack.extend(es.iter())
            }
            TypedExprKind::FieldAccess { expr, .. }
            | TypedExprKind::TypeApp { expr, .. }
            | TypedExprKind::UnaryOp { operand: expr, .. }
            | TypedExprKind::QuestionMark { expr, .. } => stack.push(expr),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    stack.push(e);
                }
            }
            TypedExprKind::StructUpdate { base, fields } => {
                stack.push(base);
                for (_, e) in fields {
                    stack.push(e);
                }
            }
            TypedExprKind::LetPattern { value, body, .. } => {
                stack.push(value);
                if let Some(b) = body {
                    stack.push(b);
                }
            }
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }
    false
}
