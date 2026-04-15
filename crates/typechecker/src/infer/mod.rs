use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{
    Decl, Expr, ExternMethod, ExternTarget, FnDecl, Module, Pattern, Span, TypeConstraint,
    TypeDecl, TypeDeclKind, TypeParam, Visibility,
};

use crate::overload::{fn_param_types, types_overlap};
use crate::scc;
use crate::trait_registry::{InstanceInfo, TraitInfo, TraitMethod, TraitRegistry};
use crate::type_registry::{self, ResolutionContext, TypeRegistry};
use crate::typed_ast::{
    self, ConstructorKind, ExportedTraitDef, ExportedTraitMethod, ExternFnInfo, ExternTraitInfo,
    ExternTraitMethodInfo, ExternTypeInfo, InstanceDefInfo, ResolvedBindingRef,
    ResolvedCallableRef, ResolvedConstraint, ResolvedConstructorRef, ResolvedTraitMethodRef,
    ResolvedTypeRef, StructDecl, SumDecl, TraitDefInfo, TraitName, TypedExpr, TypedFnDecl,
    TypedModule,
};
use crate::types::{
    type_to_canonical_name, BindingSource, ConstructorBindingKind, ParamMode, Substitution, Type,
    TypeEnv, TypeScheme, TypeVarGen, TypeVarId,
};
use crate::unify::{self, coerce_unify, unify, SecondaryLabel, SpannedTypeError, TypeError};

/// Error from `infer_module`, bundling the error with enough context
/// to render diagnostics against the correct file.
#[derive(Debug)]
pub enum InferError {
    /// A type error, possibly from an imported module.
    TypeError {
        error: SpannedTypeError,
        /// (module_path, source_text) for the module where the error originated.
        /// `None` means the error is in the root/user file.
        error_source: Option<(String, String)>,
    },
    /// Parse errors in an imported module — rendered via the parser's own diagnostics.
    ModuleParseError {
        path: String,
        source: String,
        errors: Vec<krypton_parser::diagnostics::ParseError>,
    },
}

impl InferError {
    /// Get the `SpannedTypeError` if this is a type error, or `None` for parse errors.
    pub fn type_error(&self) -> Option<&SpannedTypeError> {
        match self {
            InferError::TypeError { error, .. } => Some(error),
            InferError::ModuleParseError { .. } => None,
        }
    }
}

mod checks;
mod derive;
mod display;
mod expr;
mod fork;
mod helpers;
mod imports;
mod pattern;
mod resolve_multi;
mod resolve_overloads;

pub use display::display_type;
pub(super) use display::{build_type_param_map, leading_type_var, substitute_type_var};
pub(super) use fork::{check_fork, ForkCommit};
pub(super) use helpers::*;

pub(crate) use expr::InferenceContext;

/// Infer the type of an expression using Algorithm J.
#[tracing::instrument(level = "trace", skip_all)]
pub fn infer_expr(
    expr: &Expr,
    env: &mut TypeEnv,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) -> Result<Type, SpannedTypeError> {
    let empty_tpm = HashMap::new();
    let empty_tpa = HashMap::new();
    let empty_qm = HashMap::new();
    let empty_imported_types = HashMap::new();
    let mut deferred = Vec::new();
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
    };
    ctx.infer_expr_inner(expr, None).map(|te| te.ty)
}

/// Instantiate a field type from the registry by substituting the original
/// type parameter var ids with the concrete type arguments.
pub(super) fn instantiate_field_type(
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
    use crate::typed_ast::TypedExprKind;

    /// Returns true if `expr` is `Var(capture_name)`.
    fn is_capture(expr: &TypedExpr, capture_name: &str) -> bool {
        matches!(&expr.kind, TypedExprKind::Var(name) if name == capture_name)
    }

    match &body.kind {
        // A bare capture var in a non-shared position demands own
        // (e.g. return position, let-binding value, etc.)
        TypedExprKind::Var(name) if name == capture_name => true,
        TypedExprKind::Var(_) | TypedExprKind::Lit(_) => false,

        // Binary-op operands are shared: coerces ~T → T
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            // If the capture is a direct operand, it's shared — skip it.
            // Only recurse into non-capture sub-expressions.
            (!is_capture(lhs, capture_name) && capture_demands_own(lhs, capture_name, subst))
                || (!is_capture(rhs, capture_name) && capture_demands_own(rhs, capture_name, subst))
        }
        // Unary-op operand is shared
        TypedExprKind::UnaryOp { operand, .. } => {
            !is_capture(operand, capture_name) && capture_demands_own(operand, capture_name, subst)
        }
        // Field-access base is shared
        TypedExprKind::FieldAccess { expr, .. } => {
            !is_capture(expr, capture_name) && capture_demands_own(expr, capture_name, subst)
        }

        // Function application: check param types and modes to decide shared vs own
        TypedExprKind::App { func, args, param_modes } => {
            let func_ty = subst.apply(&func.ty);
            let fn_params = match &func_ty {
                Type::Fn(p, _) => Some(p.as_slice()),
                Type::Own(inner) => match inner.as_ref() {
                    Type::Fn(p, _) => Some(p.as_slice()),
                    _ => None,
                },
                _ => None,
            };

            for (i, arg) in args.iter().enumerate() {
                if is_capture(arg, capture_name) {
                    // Check param mode first: borrow slots never demand own
                    let mode = param_modes.get(i).copied().unwrap_or(ParamMode::Consume);
                    if matches!(mode, ParamMode::Borrow | ParamMode::ObservationalBorrow) {
                        // Borrow slot — capture is not consumed, doesn't force ~fn
                        continue;
                    }
                    // Determine if this arg position demands own
                    let demands = if let Some(params) = fn_params {
                        if let Some((_, pty)) = params.get(i) {
                            let resolved = subst.apply(pty);
                            matches!(resolved, Type::Own(_) | Type::Var(_) | Type::Shape(_) | Type::MaybeOwn(_, _))
                        } else {
                            true // conservative: can't determine param type
                        }
                    } else {
                        true // conservative: can't resolve func type
                    };
                    if demands {
                        return true;
                    }
                    // Shared arg position — don't recurse into this arg
                } else if capture_demands_own(arg, capture_name, subst) {
                    return true;
                }
            }
            capture_demands_own(func, capture_name, subst)
        }

        // Nodes that just recurse into children
        TypedExprKind::If { cond, then_, else_ } => {
            capture_demands_own(cond, capture_name, subst)
                || capture_demands_own(then_, capture_name, subst)
                || capture_demands_own(else_, capture_name, subst)
        }
        TypedExprKind::Let { value, body, .. } => {
            capture_demands_own(value, capture_name, subst)
                || body
                    .as_ref()
                    .is_some_and(|b| capture_demands_own(b, capture_name, subst))
        }
        TypedExprKind::Do(exprs) => exprs
            .iter()
            .any(|e| capture_demands_own(e, capture_name, subst)),
        TypedExprKind::Match { scrutinee, arms } => {
            capture_demands_own(scrutinee, capture_name, subst)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|g| capture_demands_own(g, capture_name, subst))
                        || capture_demands_own(&arm.body, capture_name, subst)
                })
        }
        TypedExprKind::Lambda { body, .. } => capture_demands_own(body, capture_name, subst),
        TypedExprKind::TypeApp { expr, .. } => capture_demands_own(expr, capture_name, subst),
        // Conservative: struct fields, tuple elements, vec/recur elements
        // all treated as own-requiring when the capture appears directly
        TypedExprKind::StructLit { fields, .. } => fields.iter().any(|(_, val)| {
            is_capture(val, capture_name) || capture_demands_own(val, capture_name, subst)
        }),
        TypedExprKind::StructUpdate { base, fields } => {
            capture_demands_own(base, capture_name, subst)
                || fields.iter().any(|(_, val)| {
                    is_capture(val, capture_name) || capture_demands_own(val, capture_name, subst)
                })
        }
        TypedExprKind::Tuple(elements) | TypedExprKind::VecLit(elements) => {
            elements.iter().any(|elem| {
                is_capture(elem, capture_name) || capture_demands_own(elem, capture_name, subst)
            })
        }
        TypedExprKind::Recur { args, .. } => args.iter().any(|elem| {
            is_capture(elem, capture_name) || capture_demands_own(elem, capture_name, subst)
        }),
        TypedExprKind::LetPattern { value, body, .. } => {
            capture_demands_own(value, capture_name, subst)
                || body
                    .as_ref()
                    .is_some_and(|b| capture_demands_own(b, capture_name, subst))
        }
        TypedExprKind::QuestionMark { expr, .. } => capture_demands_own(expr, capture_name, subst),
        TypedExprKind::Discharge(inner) => capture_demands_own(inner, capture_name, subst),
    }
}

pub(super) fn first_own_capture(
    body: &Expr,
    params: &HashSet<&str>,
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
        Expr::Lit { .. } => None,
    }
}

/// Walk a typed lambda body and return the span of the first `Recur` node
/// that targets THIS lambda. Stops at nested `Lambda` bodies because those
/// rebind `recur` to themselves (the inner lambda's params).
pub(super) fn find_first_recur_span(body: &TypedExpr) -> Option<Span> {
    use crate::typed_ast::TypedExprKind as K;
    match &body.kind {
        K::Recur { .. } => Some(body.span),
        K::Lambda { .. } => None,
        K::Lit(_) | K::Var(_) => None,
        K::App { func, args, .. } => find_first_recur_span(func)
            .or_else(|| args.iter().find_map(find_first_recur_span)),
        K::TypeApp { expr, .. } => find_first_recur_span(expr),
        K::If { cond, then_, else_ } => find_first_recur_span(cond)
            .or_else(|| find_first_recur_span(then_))
            .or_else(|| find_first_recur_span(else_)),
        K::Let { value, body, .. } => find_first_recur_span(value)
            .or_else(|| body.as_deref().and_then(find_first_recur_span)),
        K::Do(exprs) => exprs.iter().find_map(find_first_recur_span),
        K::Match { scrutinee, arms } => find_first_recur_span(scrutinee).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_deref()
                    .and_then(find_first_recur_span)
                    .or_else(|| find_first_recur_span(&arm.body))
            })
        }),
        K::FieldAccess { expr, .. } => find_first_recur_span(expr),
        K::Tuple(elems) | K::VecLit(elems) => elems.iter().find_map(find_first_recur_span),
        K::BinaryOp { lhs, rhs, .. } => {
            find_first_recur_span(lhs).or_else(|| find_first_recur_span(rhs))
        }
        K::UnaryOp { operand, .. } => find_first_recur_span(operand),
        K::StructLit { fields, .. } => fields.iter().find_map(|(_, v)| find_first_recur_span(v)),
        K::StructUpdate { base, fields } => find_first_recur_span(base)
            .or_else(|| fields.iter().find_map(|(_, v)| find_first_recur_span(v))),
        K::LetPattern { value, body, .. } => find_first_recur_span(value)
            .or_else(|| body.as_deref().and_then(find_first_recur_span)),
        K::QuestionMark { expr, .. } => find_first_recur_span(expr),
        K::Discharge(inner) => find_first_recur_span(inner),
    }
}

/// Result of processing extern methods: function info for codegen + dict requirements.
pub(super) struct ExternMethodsResult {
    pub(super) extern_fns: Vec<ExternFnInfo>,
    pub(super) bindings: Vec<ExternBindingInfo>,
    /// Dict requirements for extern functions with `where` clauses.
    pub(super) fn_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
}

#[derive(Clone)]
pub(super) struct ExternBindingInfo {
    pub(super) name: String,
    pub(super) scheme: TypeScheme,
    pub(super) visibility: Visibility,
    pub(super) def_span: Span,
}

/// Extern trait declaration collected during extern processing,
/// to be registered as a real trait in the trait registration phase.
pub(super) struct PendingExternTrait {
    pub(super) name: String,
    pub(super) java_interface: String,
    pub(super) type_params: Vec<String>,
    pub(super) methods: Vec<ExternMethod>,
    pub(super) span: Span,
}

/// Process extern methods from an `extern "class" { ... }` block, binding their
/// types into the environment and returning `ExternFnInfo` entries for codegen.
// Extern method processing — each arg reflects a distinct lexical input from
// the surface `extern` declaration (target language, env, gen, registry, trait
// lookup, type-param map/arity/names, alias). Bundling them into a struct
// would just be a namespace shim, since this is only called from a couple of
// extern-loading sites and shares no fields with anything else.
#[allow(clippy::too_many_arguments)]
fn process_extern_methods(
    class_name: &str,
    target: &ExternTarget,
    methods: &[ExternMethod],
    env: &mut TypeEnv,
    gen: &mut TypeVarGen,
    registry: &TypeRegistry,
    trait_name_lookup: &HashMap<String, TraitName>,
    module_path_str: &str,
    span: Span,
    type_param_map: Option<&HashMap<String, TypeVarId>>,
    type_param_arity: Option<&HashMap<String, usize>>,
    type_param_names: Option<&[String]>,
    alias_name: Option<&str>,
) -> Result<ExternMethodsResult, SpannedTypeError> {
    let empty_map = HashMap::new();
    let empty_arity = HashMap::new();
    let resolve_map = type_param_map.unwrap_or(&empty_map);
    let resolve_arity = type_param_arity.unwrap_or(&empty_arity);
    // Collect type param vars for scheme quantification in declaration order
    let base_scheme_vars: Vec<TypeVarId> = match (type_param_names, type_param_map) {
        (Some(names), Some(map)) => names.iter().filter_map(|n| map.get(n).copied()).collect(),
        _ => vec![],
    };
    let mut extern_fns = Vec::new();
    let mut bindings = Vec::new();
    let mut fn_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> = HashMap::new();
    for method in methods {
        let bind_name = &method.name;

        let mut scheme_vars = base_scheme_vars.clone();

        // Build method-level type param map (merged with block-level)
        let mut method_resolve_map;
        let mut method_resolve_arity;
        let effective_resolve_map: &HashMap<String, TypeVarId>;
        let effective_resolve_arity: &HashMap<String, usize>;
        if !method.type_params.is_empty() {
            method_resolve_map = resolve_map.clone();
            method_resolve_arity = resolve_arity.clone();
            for tp_name in &method.type_params {
                let fresh = gen.fresh();
                method_resolve_map.insert(tp_name.clone(), fresh);
                method_resolve_arity.insert(tp_name.clone(), 0);
                scheme_vars.push(fresh);
            }
            effective_resolve_map = &method_resolve_map;
            effective_resolve_arity = &method_resolve_arity;
        } else {
            effective_resolve_map = resolve_map;
            effective_resolve_arity = resolve_arity;
        }

        let mut param_types = Vec::new();
        for (_, ty_expr) in &method.params {
            let resolved = type_registry::resolve_type_expr(
                ty_expr,
                effective_resolve_map,
                effective_resolve_arity,
                registry,
                ResolutionContext::UserAnnotation,
                None,
            )
            .map_err(|e| spanned(e, span))?;
            param_types.push(resolved);
        }

        let return_type = type_registry::resolve_type_expr(
            &method.return_type,
            effective_resolve_map,
            effective_resolve_arity,
            registry,
            ResolutionContext::UserAnnotation,
            None,
        )
        .map_err(|e| spanned(e, span))?;
        let ret = return_type.clone();

        // Validate @nullable: return type must be Option[T]
        if method.nullable {
            let is_option = matches!(&ret, Type::Named(n, _) if n == "Option");
            if !is_option {
                return Err(spanned(
                    TypeError::InvalidNullableReturn {
                        name: bind_name.clone(),
                        actual_return_type: ret.clone(),
                    },
                    method.span,
                ));
            }
        }

        // Validate @throws: return type must be Result[String, T]
        if method.throws {
            let is_result_string = matches!(&ret, Type::Named(n, args) if n == "Result" && args.len() == 2 && args[0] == Type::String);
            if !is_result_string {
                return Err(spanned(
                    TypeError::InvalidThrowsReturn {
                        name: bind_name.clone(),
                        actual_return_type: ret.clone(),
                    },
                    method.span,
                ));
            }
        }

        // Validate @instance / @constructor
        if method.instance && method.constructor {
            return Err(spanned(
                TypeError::InstanceConstructorConflict {
                    name: bind_name.clone(),
                },
                method.span,
            ));
        }

        if (method.instance || method.constructor) && matches!(target, ExternTarget::Js) {
            return Err(spanned(
                TypeError::InstanceConstructorOnJsTarget {
                    name: bind_name.clone(),
                },
                method.span,
            ));
        }

        if method.constructor {
            if let Some(alias) = alias_name {
                // Return type must be Own(Named(alias, _)), possibly wrapped in
                // Result[String, _] for @throws or Option[_] for @nullable.
                let inner_ret = if method.throws {
                    // Result[String, ~Alias] → check the second type arg
                    match &ret {
                        Type::Named(n, args) if n == "Result" && args.len() == 2 => &args[1],
                        _ => &ret,
                    }
                } else if method.nullable {
                    // Option[~Alias] → check the inner type
                    match &ret {
                        Type::Named(n, args) if n == "Option" && args.len() == 1 => &args[0],
                        _ => &ret,
                    }
                } else {
                    &ret
                };
                let is_own_alias = matches!(inner_ret, Type::Own(inner) if matches!(inner.as_ref(), Type::Named(n, _) if n == alias));
                if !is_own_alias {
                    return Err(spanned(
                        TypeError::InvalidConstructorReturn {
                            name: bind_name.clone(),
                            expected_type: alias.to_string(),
                            actual_return_type: ret.clone(),
                        },
                        method.span,
                    ));
                }
                // First param must NOT be the extern type
                if let Some((_, _first_ty)) = method.params.first() {
                    let first_resolved = &param_types[0];
                    let matches_alias = matches!(first_resolved, Type::Named(n, _) if n == alias)
                        || matches!(first_resolved, Type::Own(inner) if matches!(inner.as_ref(), Type::Named(n, _) if n == alias));
                    if matches_alias {
                        return Err(spanned(
                            TypeError::ConstructorWithSelf {
                                name: bind_name.clone(),
                            },
                            method.span,
                        ));
                    }
                }
            }
        }

        if method.instance {
            if let Some(alias) = alias_name {
                // First param must be the extern type
                let first_matches = if let Some(first_resolved) = param_types.first() {
                    matches!(first_resolved, Type::Named(n, _) if n == alias)
                        || matches!(first_resolved, Type::Own(inner) if matches!(inner.as_ref(), Type::Named(n, _) if n == alias))
                } else {
                    false
                };
                if !first_matches {
                    return Err(spanned(
                        TypeError::InvalidInstanceFirstParam {
                            name: bind_name.clone(),
                            expected_type: alias.to_string(),
                        },
                        method.span,
                    ));
                }
            }
        }

        // Build where clause dict requirements before TypeScheme construction
        // so constraints are embedded in the scheme.
        let mut requirements = Vec::new();
        if !method.where_clauses.is_empty() {
            for constraint in &method.where_clauses {
                let tv_names = require_param_vars(constraint)?;
                let type_vars: Vec<TypeVarId> = tv_names
                    .iter()
                    .filter_map(|n| effective_resolve_map.get(*n).copied())
                    .collect();
                if !type_vars.is_empty() && type_vars.len() == tv_names.len() {
                    let tn = trait_name_lookup
                        .get(&constraint.trait_name)
                        .cloned()
                        .unwrap_or_else(|| {
                            TraitName::new(
                                module_path_str.to_string(),
                                constraint.trait_name.clone(),
                            )
                        });
                    requirements.push((tn, type_vars));
                }
            }
            if !requirements.is_empty() {
                fn_constraints.insert(bind_name.clone(), requirements.clone());
            }
        }

        let fn_ty = Type::fn_consuming(param_types.clone(), ret);
        let scheme = if scheme_vars.is_empty() {
            TypeScheme::mono(fn_ty)
        } else {
            TypeScheme {
                vars: scheme_vars,
                constraints: requirements.clone(),
                ty: fn_ty,
                var_names: HashMap::new(),
            }
        };
        env.bind_top_level_function(
            bind_name.clone(),
            scheme.clone(),
            module_path_str.to_string(),
            bind_name.clone(),
        );
        bindings.push(ExternBindingInfo {
            name: bind_name.clone(),
            scheme,
            visibility: method.visibility,
            def_span: method.span,
        });

        // Store concrete types for codegen — resolve with the type param map
        // so container types like Vec[a] resolve to Named("Vec", [Var(a)])
        // rather than being erased entirely to a bare Var. The type args
        // (which map to Var) will be erased to Object by JVM codegen, matching
        // Java's own type erasure behavior.
        let mut concrete_params = Vec::new();
        for (_, ty_expr) in &method.params {
            let resolved = type_registry::resolve_type_expr(
                ty_expr,
                effective_resolve_map,
                effective_resolve_arity,
                registry,
                ResolutionContext::UserAnnotation,
                None,
            )
            .map_err(|e| spanned(e, span))?;
            concrete_params.push(resolved);
        }
        let codegen_return = type_registry::resolve_type_expr(
            &method.return_type,
            effective_resolve_map,
            effective_resolve_arity,
            registry,
            ResolutionContext::UserAnnotation,
            None,
        )
        .map_err(|e| spanned(e, span))?;
        extern_fns.push(ExternFnInfo {
            name: bind_name.clone(),
            declaring_module_path: module_path_str.to_string(),
            span: method.span,
            module_path: class_name.to_string(),
            target: target.clone(),
            nullable: method.nullable,
            throws: method.throws,
            instance: method.instance,
            constructor: method.constructor,
            param_types: concrete_params,
            return_type: codegen_return,
            constraints: requirements,
        });
    }
    Ok(ExternMethodsResult {
        extern_fns,
        bindings,
        fn_constraints,
    })
}

/// Infer types for all top-level definitions in a module.
///
/// Returns a `Vec<TypedModule>` containing the main module (first)
/// followed by any imported modules discovered during inference.
///
/// `root_module_path` is the module path for the root file (e.g., `Some("hello")` for `hello.kr`).
///
/// Uses SCC (strongly connected component) analysis to process definitions
/// in dependency order. Functions within the same SCC are inferred together
/// as a mutually recursive group, then generalized before later SCCs see them.
#[tracing::instrument(skip(module, resolver), fields(decls = module.decls.len()))]
pub fn infer_module(
    module: &Module,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
    root_module_path: String,
    target: krypton_parser::ast::CompileTarget,
) -> Result<
    (
        Vec<TypedModule>,
        Vec<crate::module_interface::ModuleInterface>,
    ),
    Vec<InferError>,
> {
    use krypton_modules::module_graph;
    use krypton_modules::stdlib_loader::StdlibLoader;

    // Filter root module by platform before anything else
    let mut module = module.clone();
    krypton_parser::platform::filter_by_platform(&mut module, target);
    let module = &module;

    // Build the module graph (resolves, parses, toposorts all imports + prelude)
    let graph = module_graph::build_module_graph(module, resolver, target).map_err(|e| {
        vec![match e {
            module_graph::ModuleGraphError::ParseError {
                path,
                source,
                errors,
            } => InferError::ModuleParseError {
                path,
                source,
                errors,
            },
            other => InferError::TypeError {
                error: map_graph_error(other),
                error_source: None,
            },
        }]
    })?;

    let mut cache: HashMap<String, TypedModule> = HashMap::new();
    let mut interface_cache: HashMap<String, crate::module_interface::ModuleInterface> =
        HashMap::new();

    // Type-check each dependency in topological order
    for resolved in &graph.modules {
        if !cache.contains_key(&resolved.path) {
            let mut dep_paths: Vec<String> =
                crate::module_interface::collect_direct_deps(&resolved.module)
                    .iter()
                    .map(|p| p.0.clone())
                    .collect();
            if !graph.prelude_tree_paths.contains(&resolved.path) {
                dep_paths.push("prelude".to_string());
            }
            let typed = infer_module_inner(
                &resolved.module,
                &interface_cache,
                resolved.path.clone(),
                &graph.prelude_tree_paths,
            )
            .map_err(|errors| {
                // Re-resolve source for the failing module (error path only)
                let source_text = StdlibLoader::get_source(&resolved.path)
                    .map(|s| s.to_string())
                    .or_else(|| resolver.resolve(&resolved.path));
                let error_source = source_text.map(|s| (resolved.path.clone(), s));
                errors
                    .into_iter()
                    .map(|mut e| {
                        if e.source_file.is_none() {
                            e.source_file = Some(resolved.path.clone());
                        }
                        InferError::TypeError {
                            error: e,
                            error_source: error_source.clone(),
                        }
                    })
                    .collect::<Vec<_>>()
            })?;
            let mut typed = typed;
            // Attach source text for diagnostic rendering of downstream codegen errors
            typed.module_source = StdlibLoader::get_source(&resolved.path)
                .map(|s| s.to_string())
                .or_else(|| resolver.resolve(&resolved.path));
            // Extract interface for downstream modules
            let iface = crate::module_interface::extract_interface(&typed, &dep_paths);
            interface_cache.insert(resolved.path.clone(), iface);
            cache.insert(resolved.path.clone(), typed);
        }
    }

    // Compute root direct deps before root_module_path is moved.
    let mut root_dep_paths: Vec<String> = crate::module_interface::collect_direct_deps(module)
        .iter()
        .map(|p| p.0.clone())
        .collect();
    if !graph.prelude_tree_paths.contains(&root_module_path) {
        root_dep_paths.push("prelude".to_string());
    }

    // Type-check the root module
    let main = infer_module_inner(
        module,
        &interface_cache,
        root_module_path,
        &graph.prelude_tree_paths,
    )
    .map_err(|errors| {
        errors
            .into_iter()
            .map(|e| InferError::TypeError {
                error: e,
                error_source: None,
            })
            .collect::<Vec<_>>()
    })?;

    let root_iface = crate::module_interface::extract_interface(&main, &root_dep_paths);

    let mut result = vec![main];
    // Collect cached imported modules in topological order (dependencies first)
    for resolved in &graph.modules {
        if let Some(typed) = cache.remove(&resolved.path) {
            result.push(typed);
        }
    }

    // Collect all interfaces: root first, then deps in topological order
    let mut interfaces = vec![root_iface];
    for resolved in &graph.modules {
        if let Some(iface) = interface_cache.remove(&resolved.path) {
            interfaces.push(iface);
        }
    }

    Ok((result, interfaces))
}

/// Convert a non-parse `ModuleGraphError` into a `SpannedTypeError`.
/// ParseError is handled separately as `InferError::ModuleParseError`.
fn map_graph_error(e: krypton_modules::module_graph::ModuleGraphError) -> SpannedTypeError {
    use krypton_modules::module_graph::ModuleGraphError;
    match e {
        ModuleGraphError::CircularImport { cycle, span } => {
            spanned(TypeError::CircularImport { cycle }, span)
        }
        ModuleGraphError::UnknownModule { path, span } => {
            spanned(TypeError::UnknownModule { path }, span)
        }
        ModuleGraphError::BareImport { path, span } => {
            spanned(TypeError::BareImport { path }, span)
        }
        ModuleGraphError::ParseError { .. } => {
            unreachable!("ParseError is handled directly as InferError::ModuleParseError")
        }
    }
}

/// Return the main `TypedModule` from `infer_module` result (for backward compatibility).
pub fn infer_module_single(
    module: &Module,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<TypedModule, Vec<InferError>> {
    let (mut modules, _) = infer_module(
        module,
        resolver,
        "main".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )?;
    Ok(modules.remove(0))
}

/// Grouped import state: the maps that must stay in sync when binding/shadowing imports.
pub(crate) struct ImportContext {
    pub(super) imported_fn_types: Vec<typed_ast::ImportedFn>,
    /// Index: function name → indices into `imported_fn_types` for O(1) name lookups.
    imported_fn_index: HashMap<String, Vec<usize>>,
    pub(super) imported_type_info: HashMap<String, (String, Visibility)>,
    pub(super) imported_fn_qualifiers: HashMap<String, Vec<(typed_ast::ParamQualifier, String)>>,
    /// Prelude functions that were shadowed by explicit imports: (name, source_module)
    pub(super) shadowed_prelude_fns: Vec<(String, String)>,
}

impl ImportContext {
    fn new() -> Self {
        ImportContext {
            imported_fn_types: Vec::new(),
            imported_fn_index: HashMap::new(),
            imported_type_info: HashMap::new(),
            imported_fn_qualifiers: HashMap::new(),
            shadowed_prelude_fns: Vec::new(),
        }
    }

    /// Push into imported_fn_types and update the index.
    fn push_fn(&mut self, entry: typed_ast::ImportedFn) {
        let idx = self.imported_fn_types.len();
        self.imported_fn_index
            .entry(entry.name.clone())
            .or_default()
            .push(idx);
        self.imported_fn_types.push(entry);
    }

    fn remove_prelude_entries(&mut self, name: &str) {
        let shadowed: Vec<_> = self
            .get_by_name(name)
            .filter(|f| f.is_prelude)
            .map(|f| (f.name.clone(), f.qualified_name.module_path.clone()))
            .collect();
        if shadowed.is_empty() {
            return;
        }
        self.shadowed_prelude_fns.extend(shadowed);
        self.imported_fn_types
            .retain(|f| f.name != name || !f.is_prelude);
        self.rebuild_index();
    }

    /// Rebuild the entire index (called after retain, which is rare).
    fn rebuild_index(&mut self) {
        self.imported_fn_index.clear();
        for (i, f) in self.imported_fn_types.iter().enumerate() {
            self.imported_fn_index
                .entry(f.name.clone())
                .or_default()
                .push(i);
        }
    }

    /// Get all imported functions with the given name.
    fn get_by_name(&self, name: &str) -> impl Iterator<Item = &typed_ast::ImportedFn> {
        let indices = self.imported_fn_index.get(name);
        indices
            .into_iter()
            .flat_map(|idxs| idxs.iter())
            .map(|&i| &self.imported_fn_types[i])
    }

    /// Check if any imported function has the given name.
    fn contains_name(&self, name: &str) -> bool {
        self.imported_fn_index.contains_key(name)
    }

    /// Register imported-function metadata and compute its canonical binding source.
    /// Returns an error if the same name is already imported from a different
    /// (non-prelude) module. The user must alias one import to resolve the conflict.
    fn register_import_binding(
        &mut self,
        b: ImportBinding,
    ) -> Result<BindingSource, SpannedTypeError> {
        let ImportBinding {
            name,
            scheme,
            origin,
            source_module,
            original_name,
            is_prelude,
            span,
        } = b;
        let same_symbol_as_prelude = !is_prelude
            && self.get_by_name(&name).any(|existing| {
                existing.is_prelude
                    && existing.qualified_name.module_path == source_module
                    && existing.qualified_name.local_name == original_name
            });

        // Explicit import shadows only actual prelude entries for the same name.
        if !is_prelude {
            self.remove_prelude_entries(&name);
        }

        // Importing the original prelude export directly should keep behaving like
        // prelude-origin shadowing for later local-definition checks.
        let effective_is_prelude = is_prelude || same_symbol_as_prelude;

        // Check same-name imports from different modules for overload compatibility.
        let same_name: Vec<_> = self.get_by_name(&name).collect();
        for existing in same_name {
            if existing.qualified_name.module_path != source_module {
                let existing_params = crate::overload::fn_param_types(&existing.scheme.ty);
                let new_params = crate::overload::fn_param_types(&scheme.ty);

                match (existing_params, new_params) {
                    (Some(ep), Some(np)) => {
                        if ep.len() != np.len() {
                            return Err(spanned(
                                TypeError::ImportOverloadArityMismatch {
                                    name: name.clone(),
                                    arities: vec![
                                        (existing.qualified_name.module_path.clone(), ep.len()),
                                        (source_module.clone(), np.len()),
                                    ],
                                },
                                span,
                            ));
                        }
                        if crate::overload::types_overlap(&ep, &np) {
                            return Err(spanned(
                                TypeError::DuplicateImport {
                                    name: name.clone(),
                                    modules: vec![
                                        existing.qualified_name.module_path.clone(),
                                        source_module.clone(),
                                    ],
                                    signatures: vec![
                                        format!("{}", existing.scheme),
                                        format!("{}", scheme),
                                    ],
                                },
                                span,
                            ));
                        }
                    }
                    _ => {
                        return Err(spanned(
                            TypeError::DuplicateImport {
                                name: name.clone(),
                                modules: vec![
                                    existing.qualified_name.module_path.clone(),
                                    source_module.clone(),
                                ],
                                signatures: vec![
                                    format!("{}", existing.scheme),
                                    format!("{}", scheme),
                                ],
                            },
                            span,
                        ));
                    }
                }
            }
        }

        let binding_source = if let Some(trait_name) = &origin {
            BindingSource::TraitMethod {
                trait_module_path: trait_name.module_path.clone(),
                trait_name: trait_name.local_name.clone(),
                method_name: original_name.clone(),
                is_prelude: effective_is_prelude,
            }
        } else {
            BindingSource::ImportedFunction {
                qualified_name: crate::types::BindingQualifiedName {
                    module_path: source_module.clone(),
                    local_name: original_name.clone(),
                },
                is_prelude: effective_is_prelude,
            }
        };
        self.push_fn(typed_ast::ImportedFn {
            name: name.clone(),
            scheme,
            origin,
            qualified_name: typed_ast::QualifiedName::new(source_module, original_name),
            is_prelude: effective_is_prelude,
        });
        Ok(binding_source)
    }

    /// Atomically bind an imported function: env + fn_types + provenance.
    fn bind_import(
        &mut self,
        env: &mut TypeEnv,
        b: ImportBinding,
    ) -> Result<BindingSource, SpannedTypeError> {
        let name = b.name.clone();
        let scheme = b.scheme.clone();
        let is_prelude_import = b.is_prelude;
        let already_bound = env.lookup(&name).is_some();
        let binding_source = self.register_import_binding(b)?;
        if !already_bound {
            env.bind_with_source(name, scheme, binding_source.clone());
        } else {
            let existing_is_prelude = env
                .lookup_entry(&name)
                .map(|e| match &e.source {
                    BindingSource::ImportedFunction { is_prelude, .. } => *is_prelude,
                    BindingSource::TraitMethod { is_prelude, .. } => *is_prelude,
                    _ => false,
                })
                .unwrap_or(false);

            if existing_is_prelude && !is_prelude_import {
                // Full by-name prelude eviction: the prelude is always processed
                // before user imports (prepended via .chain() in process_imports),
                // so at this point every existing overload candidate is
                // prelude-sourced.  Clearing them is correct — subsequent user
                // imports of the same name will build a fresh overload set via
                // the else branch below.
                if let Some(entry) = env.lookup_entry_mut(&name) {
                    entry.scheme = scheme;
                    entry.source = binding_source.clone();
                    entry.overload_candidates = None;
                }
            } else {
                // Only create overload candidates when the same name is imported
                // from genuinely different source modules (validated as non-overlapping
                // by register_import_binding). Trait method re-imports from the same
                // module should not create overloads.
                let distinct_modules: std::collections::HashSet<&str> = self
                    .get_by_name(&name)
                    .map(|f| f.qualified_name.module_path.as_str())
                    .collect();
                if distinct_modules.len() > 1 {
                    if let Some(entry) = env.lookup_entry_mut(&name) {
                        entry.add_overload_candidate(scheme, binding_source.clone());
                    }
                }
            }
        }
        Ok(binding_source)
    }

    /// Bind a hidden (qualified) function: fn_types + provenance, no env bind.
    fn bind_hidden_fn(
        &mut self,
        name: String,
        scheme: TypeScheme,
        origin: Option<TraitName>,
        provenance: (String, String),
        is_prelude: bool,
    ) {
        self.push_fn(typed_ast::ImportedFn {
            name,
            scheme,
            origin,
            qualified_name: typed_ast::QualifiedName::new(provenance.0, provenance.1),
            is_prelude,
        });
    }

    // Imported constructor binding takes one arg per distinct surface attribute
    // (binding name, scheme, defining type info, kind, prelude flag); a wrapping
    // struct here would just be a namespace shim for one call site.
    #[allow(clippy::too_many_arguments)]
    fn bind_imported_constructor(
        &mut self,
        env: &mut TypeEnv,
        binding_name: String,
        scheme: TypeScheme,
        type_module_path: String,
        type_name: String,
        constructor_name: String,
        kind: ConstructorBindingKind,
        is_prelude: bool,
    ) {
        self.push_fn(typed_ast::ImportedFn {
            name: binding_name.clone(),
            scheme: scheme.clone(),
            origin: None,
            qualified_name: typed_ast::QualifiedName::new(
                type_module_path.clone(),
                constructor_name.clone(),
            ),
            is_prelude,
        });
        env.bind_constructor(
            binding_name,
            scheme,
            type_module_path,
            type_name,
            constructor_name,
            kind,
        );
    }

    fn bind_hidden_constructor(
        &mut self,
        name: String,
        scheme: TypeScheme,
        type_module_path: String,
        constructor_name: String,
        is_prelude: bool,
    ) {
        self.push_fn(typed_ast::ImportedFn {
            name,
            scheme,
            origin: None,
            qualified_name: typed_ast::QualifiedName::new(type_module_path, constructor_name),
            is_prelude,
        });
    }

    /// Bind type info for an imported type.
    fn bind_type_info(
        &mut self,
        name: String,
        canonical_name: Option<String>,
        source: String,
        vis: Visibility,
    ) {
        self.imported_type_info.insert(name, (source.clone(), vis));
        if let Some(canonical_name) = canonical_name {
            self.imported_type_info
                .entry(canonical_name)
                .or_insert((source, vis));
        }
    }

    fn remove_prelude_fn(&mut self, name: &str) {
        let shadowed: Vec<_> = self
            .get_by_name(name)
            .filter(|f| f.is_prelude)
            .map(|f| (f.name.clone(), f.qualified_name.module_path.clone()))
            .collect();
        if shadowed.is_empty() {
            return;
        }
        self.shadowed_prelude_fns.extend(shadowed);
        self.imported_fn_types
            .retain(|f| f.name != name || !f.is_prelude);
        self.rebuild_index();
    }
}

/// Result of `infer_function_bodies`: fn decls, schemes, typed bodies,
/// constraint requirements.
type InferFunctionBodiesResult<'a> = (
    Vec<&'a krypton_parser::ast::FnDecl>,
    Vec<Option<TypeScheme>>,
    Vec<Option<TypedExpr>>,
    HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
);

/// Result of `process_traits_and_deriving`: trait registry, exported defs,
/// extern trait infos, derived/imported instance defs, and trait method map.
type TraitsAndDerivingResult = (
    TraitRegistry,
    Vec<ExportedTraitDef>,
    Vec<ExternTraitInfo>,
    Vec<InstanceDefInfo>,
    Vec<InstanceDefInfo>,
    HashMap<String, TraitName>,
);

/// Result of processing a module's local extern declarations.
type LocalExternResult = (
    Vec<ExternFnInfo>,
    Vec<ExternTypeInfo>,
    Vec<ExternBindingInfo>,
    HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
    Vec<PendingExternTrait>,
);

/// All inputs needed to register an imported function binding.
/// Bundled to keep `register_import_binding`/`bind_import` arity manageable —
/// every field is a distinct lexical input from the surface import statement.
pub(super) struct ImportBinding {
    pub(super) name: String,
    pub(super) scheme: TypeScheme,
    pub(super) origin: Option<TraitName>,
    pub(super) source_module: String,
    pub(super) original_name: String,
    pub(super) is_prelude: bool,
    pub(super) span: Span,
}

/// State accumulated during the bootstrap phases of module inference
/// (env setup, import processing, extern loading, type registration).
/// Consumed by `assemble_typed_module` at the end.
pub(crate) struct ModuleInferenceState {
    // Core inference state
    pub(super) env: TypeEnv,
    pub(super) subst: Substitution,
    pub(super) gen: TypeVarGen,
    pub(super) registry: TypeRegistry,
    pub(super) let_own_spans: HashSet<Span>,
    pub(super) lambda_own_captures: HashMap<Span, String>,
    // Import accumulation
    pub(super) imports: ImportContext,
    pub(super) imported_trait_defs: Vec<ExportedTraitDef>,
    pub(super) imported_trait_names: HashSet<String>,
    pub(super) trait_aliases: Vec<(String, TraitName)>,
    pub(super) qualified_modules: HashMap<String, QualifiedModuleBinding>,
    // Re-export state
    pub(super) reexported_fn_types: Vec<typed_ast::ExportedFn>,
    pub(super) reexported_type_names: Vec<String>,
    pub(super) reexported_type_visibility: HashMap<String, Visibility>,
    pub(super) reexported_trait_defs: Vec<ExportedTraitDef>,
    // Prelude tracking
    pub(super) prelude_imported_names: HashSet<String>,
}

impl ModuleInferenceState {
    fn new(is_core_module: bool) -> Self {
        let mut env = TypeEnv::new();
        let mut gen = TypeVarGen::new();
        let mut registry = TypeRegistry::new();
        registry.register_builtins(&mut gen);

        crate::intrinsics::register_intrinsics(&mut env, &mut gen, is_core_module);

        ModuleInferenceState {
            env,
            subst: Substitution::new(),
            gen,
            registry,
            let_own_spans: HashSet::new(),
            lambda_own_captures: HashMap::new(),
            imports: ImportContext::new(),
            imported_trait_defs: Vec::new(),
            imported_trait_names: HashSet::new(),
            trait_aliases: Vec::new(),
            qualified_modules: HashMap::new(),
            reexported_fn_types: Vec::new(),
            reexported_type_names: Vec::new(),
            reexported_type_visibility: HashMap::new(),
            reexported_trait_defs: Vec::new(),
            prelude_imported_names: HashSet::new(),
        }
    }

    fn process_local_externs(
        &mut self,
        module: &Module,
        mod_path: &str,
    ) -> Result<LocalExternResult, SpannedTypeError> {
        let mut extern_fns: Vec<ExternFnInfo> = Vec::new();
        let mut extern_types: Vec<ExternTypeInfo> = Vec::new();
        let mut extern_bindings: Vec<ExternBindingInfo> = Vec::new();
        let mut extern_fn_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> =
            HashMap::new();
        let mut pending_extern_traits: Vec<PendingExternTrait> = Vec::new();

        // Build trait name lookup from imported trait defs
        let mut trait_name_lookup: HashMap<String, TraitName> = HashMap::new();
        for td in &self.imported_trait_defs {
            trait_name_lookup.insert(
                td.name.clone(),
                TraitName::new(td.module_path.clone(), td.name.clone()),
            );
        }

        for decl in &module.decls {
            if let Decl::Extern {
                target,
                module_path,
                alias,
                is_trait,
                type_params,
                lifts,
                methods,
                span,
                ..
            } = decl
            {
                // Extern traits are collected for registration in the trait phase
                if *is_trait {
                    if matches!(target, ExternTarget::Js) {
                        return Err(spanned(
                            TypeError::ExternTraitOnJsTarget {
                                name: alias.clone().unwrap_or_default(),
                            },
                            *span,
                        ));
                    }
                    if let Some(name) = alias {
                        pending_extern_traits.push(PendingExternTrait {
                            name: name.clone(),
                            java_interface: module_path.clone(),
                            type_params: type_params.clone(),
                            methods: methods.clone(),
                            span: *span,
                        });
                    }
                    continue;
                }

                // Register type binding if `as Name[params]` is present
                let mut tp_map: Option<HashMap<String, TypeVarId>> = None;
                let mut tp_arity: Option<HashMap<String, usize>> = None;
                if let Some(name) = alias {
                    // Check if already registered (e.g. Vec is a builtin)
                    let type_param_vars = if let Some(existing) = self.registry.lookup_type(name) {
                        existing.type_param_vars.clone()
                    } else {
                        let vars: Vec<_> = type_params.iter().map(|_| self.gen.fresh()).collect();
                        self.registry
                            .register_type(crate::type_registry::TypeInfo {
                                name: name.clone(),
                                type_params: type_params.clone(),
                                type_param_vars: vars.clone(),
                                kind: crate::type_registry::TypeKind::Record { fields: vec![] },
                                lifts: lifts.clone(),
                                is_prelude: false,
                            })
                            .map_err(|e| spanned(e, *span))?;
                        vars
                    };
                    self.registry.mark_user_visible(name);
                    extern_types.push(ExternTypeInfo {
                        krypton_name: name.clone(),
                        host_module: module_path.clone(),
                        target: target.clone(),
                        lifts: lifts.clone(),
                    });

                    // Build type_param_map for method resolution
                    if !type_params.is_empty() {
                        let (map, arity) =
                            build_type_param_map(type_params, &type_param_vars, name);
                        tp_map = Some(map);
                        tp_arity = Some(arity);
                    }
                }

                {
                    let tp_names = type_params.as_slice();
                    let result = process_extern_methods(
                        module_path,
                        target,
                        methods,
                        &mut self.env,
                        &mut self.gen,
                        &self.registry,
                        &trait_name_lookup,
                        mod_path,
                        *span,
                        tp_map.as_ref(),
                        tp_arity.as_ref(),
                        if tp_map.is_some() {
                            Some(tp_names)
                        } else {
                            None
                        },
                        alias.as_deref(),
                    )?;

                    for (name, reqs) in result.fn_constraints {
                        extern_fn_constraints.insert(name, reqs);
                    }
                    extern_bindings.extend(result.bindings);
                    extern_fns.extend(result.extern_fns);
                }
            }
        }
        Ok((
            extern_fns,
            extern_types,
            extern_bindings,
            extern_fn_constraints,
            pending_extern_traits,
        ))
    }

    fn cleanup_prelude_shadows(&mut self, module: &Module) {
        for decl in &module.decls {
            match decl {
                Decl::Extern { methods, .. } => {
                    for m in methods {
                        self.imports.remove_prelude_fn(&m.name);
                    }
                }
                Decl::DefFn(f) => {
                    self.imports.remove_prelude_fn(&f.name);
                }
                _ => {}
            }
        }
    }

    fn resolve_fn_param_types_for_overlap(&self, f: &FnDecl) -> Option<Vec<Type>> {
        resolve_fn_param_types_for_overlap(f, &self.registry)
    }

    fn check_duplicate_function_names(&self, module: &Module) -> Result<(), SpannedTypeError> {
        // Collect all extern method names (same name across targets is fine)
        let mut extern_names: HashSet<&str> = HashSet::new();
        for decl in &module.decls {
            if let Decl::Extern { methods, .. } = decl {
                for m in methods {
                    extern_names.insert(&m.name);
                }
            }
        }
        // Group DefFn by name
        let mut groups: HashMap<&str, Vec<&FnDecl>> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if extern_names.contains(f.name.as_str()) {
                    return Err(spanned(
                        TypeError::DuplicateFunction {
                            name: f.name.clone(),
                        },
                        f.span,
                    ));
                }
                groups.entry(&f.name).or_default().push(f);
            }
        }
        // Check each group with >1 definition for valid overloading
        for (name, fns) in &groups {
            if fns.len() <= 1 {
                continue;
            }
            let last_span = fns.last().unwrap().span;
            // All defs must have type annotations on all params
            let param_types: Vec<Vec<Type>> = {
                let mut pts = Vec::new();
                for f in fns {
                    match self.resolve_fn_param_types_for_overlap(f) {
                        Some(tys) => pts.push(tys),
                        None => {
                            return Err(spanned(
                                TypeError::LocalOverloadMissingAnnotation {
                                    name: name.to_string(),
                                },
                                last_span,
                            ));
                        }
                    }
                }
                pts
            };
            // All arities must match
            let arities: Vec<usize> = param_types.iter().map(|p| p.len()).collect();
            if arities.iter().any(|a| *a != arities[0]) {
                return Err(spanned(
                    TypeError::LocalOverloadArityMismatch {
                        name: name.to_string(),
                        arities,
                    },
                    last_span,
                ));
            }
            // Pairwise overlap check
            for i in 0..param_types.len() {
                for j in (i + 1)..param_types.len() {
                    if types_overlap(&param_types[i], &param_types[j]) {
                        return Err(spanned(
                            TypeError::LocalOverloadOverlap {
                                name: name.to_string(),
                            },
                            fns[j].span,
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    fn check_explicit_import_shadows(&self, module: &Module) -> Result<(), SpannedTypeError> {
        for decl in &module.decls {
            match decl {
                Decl::DefFn(f) => {
                    let non_prelude_imports: Vec<_> = self
                        .imports
                        .get_by_name(&f.name)
                        .filter(|imp| !imp.is_prelude)
                        .collect();
                    if non_prelude_imports.is_empty() {
                        continue;
                    }
                    // Try to resolve local param types for overload checking
                    let local_params = match self.resolve_fn_param_types_for_overlap(f) {
                        Some(params) => params,
                        None => {
                            // Unannotated — keep current error behavior
                            let imp = &non_prelude_imports[0];
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: f.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                f.span,
                            ));
                        }
                    };
                    for imp in &non_prelude_imports {
                        let imp_params = match fn_param_types(&imp.scheme.ty) {
                            Some(params) => params,
                            None => {
                                // Import is not a function — conflict
                                return Err(spanned(
                                    TypeError::DefinitionConflictsWithImport {
                                        def_name: f.name.clone(),
                                        source_module: imp.qualified_name.module_path.clone(),
                                    },
                                    f.span,
                                ));
                            }
                        };
                        if imp_params.len() != local_params.len() {
                            return Err(spanned(
                                TypeError::ImportOverloadArityMismatch {
                                    name: f.name.clone(),
                                    arities: vec![
                                        ("(local)".to_string(), local_params.len()),
                                        (
                                            imp.qualified_name.module_path.clone(),
                                            imp_params.len(),
                                        ),
                                    ],
                                },
                                f.span,
                            ));
                        }
                        if types_overlap(&local_params, &imp_params) {
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: f.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                f.span,
                            ));
                        }
                    }
                }
                Decl::Extern { methods, .. } => {
                    for m in methods {
                        if let Some(imp) = self
                            .imports
                            .get_by_name(&m.name)
                            .find(|imp| !imp.is_prelude)
                        {
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: m.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                m.span,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn preregister_type_names(&mut self, module: &Module) {
        for decl in &module.decls {
            if let Decl::DefType(type_decl) = decl {
                self.registry.register_name(&type_decl.name);
                self.registry.mark_user_visible(&type_decl.name);
            }
        }
    }

    fn process_local_type_decls(
        &mut self,
        module: &Module,
        module_path: &str,
    ) -> Result<Vec<(String, TypeScheme)>, SpannedTypeError> {
        let mut constructor_schemes: Vec<(String, TypeScheme)> = Vec::new();
        for decl in &module.decls {
            if let Decl::DefType(type_decl) = decl {
                if let Some(existing) = self.registry.lookup_type(&type_decl.name) {
                    if existing.is_prelude {
                        if let crate::type_registry::TypeKind::Sum { variants } = &existing.kind {
                            for v in variants {
                                self.env.unbind(&v.name);
                            }
                        }
                        self.imports.imported_type_info.remove(&type_decl.name);
                    }
                }

                let constructors =
                    type_registry::process_type_decl(type_decl, &mut self.registry, &mut self.gen)
                        .map_err(|e| spanned(e, type_decl.span))?;

                // E0109: value-position uses of resource-carrying types
                // inside record field / variant payload annotations must be
                // spelled `~T`. Walk per-field TypeExpr spans so the error
                // points at the offending annotation rather than the whole
                // type declaration.
                if let Some(info) = self.registry.lookup_type(&type_decl.name) {
                    match (&type_decl.kind, &info.kind) {
                        (
                            krypton_parser::ast::TypeDeclKind::Record { fields: ast_fields },
                            crate::type_registry::TypeKind::Record { fields: info_fields },
                        ) => {
                            for ((_, ast_ty), (_, resolved_ty)) in
                                ast_fields.iter().zip(info_fields.iter())
                            {
                                crate::ownership::check_no_bare_resource_use(
                                    resolved_ty,
                                    &self.registry,
                                    ast_ty.span(),
                                    crate::type_error::BareResourceContext::RecordField,
                                )?;
                            }
                        }
                        (
                            krypton_parser::ast::TypeDeclKind::Sum { variants: ast_variants },
                            crate::type_registry::TypeKind::Sum { variants: info_variants },
                        ) => {
                            for (ast_v, info_v) in
                                ast_variants.iter().zip(info_variants.iter())
                            {
                                for (ast_ty, resolved_ty) in
                                    ast_v.fields.iter().zip(info_v.fields.iter())
                                {
                                    crate::ownership::check_no_bare_resource_use(
                                        resolved_ty,
                                        &self.registry,
                                        ast_ty.span(),
                                        crate::type_error::BareResourceContext::VariantPayload,
                                    )?;
                                }
                            }
                        }
                        _ => {}
                    }
                }

                for (name, scheme) in constructors {
                    // Value-namespace check: a constructor may not collide with
                    // another local constructor of a *different* type. Prelude
                    // constructors are shadowable and therefore skipped.
                    if let Some(existing) = self.env.lookup_entry(&name) {
                        if let BindingSource::Constructor {
                            type_qualified_name,
                            ..
                        } = &existing.source
                        {
                            if type_qualified_name.local_name != type_decl.name {
                                let existing_is_prelude = self
                                    .registry
                                    .lookup_type(&type_qualified_name.local_name)
                                    .is_some_and(|t| t.is_prelude);
                                if !existing_is_prelude {
                                    return Err(spanned(
                                        TypeError::DuplicateConstructor {
                                            name: name.clone(),
                                            first_type: type_qualified_name.local_name.clone(),
                                            second_type: type_decl.name.clone(),
                                        },
                                        type_decl.span,
                                    ));
                                }
                            }
                        }
                    }
                    self.env.bind_constructor(
                        name.clone(),
                        scheme.clone(),
                        module_path.to_string(),
                        type_decl.name.clone(),
                        name.clone(),
                        constructor_binding_kind_for_decl(type_decl, &name),
                    );
                    constructor_schemes.push((name, scheme));
                }
            }
        }
        Ok(constructor_schemes)
    }

    /// Assemble the final TypedModule from accumulated state and inference-phase outputs.
    ///
    /// Extracted from `infer_module_inner` specifically to reduce that function's
    /// stack frame size — bundling the args into a struct here would risk pushing
    /// the inputs back onto the caller's frame and undoing that optimization, so
    /// the wide signature is intentional.
    #[allow(clippy::too_many_arguments)]
    fn assemble_typed_module(
        self,
        module: &Module,
        module_path: String,
        fn_decls: &[&krypton_parser::ast::FnDecl],
        result_schemes: Vec<Option<TypeScheme>>,
        fn_bodies: Vec<Option<TypedExpr>>,
        instance_defs: Vec<InstanceDefInfo>,
        derived_instance_defs: Vec<InstanceDefInfo>,
        _imported_instance_defs: Vec<InstanceDefInfo>,
        fn_constraint_requirements: &mut HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
        _trait_method_map: &HashMap<String, TraitName>,
        trait_registry: &TraitRegistry,
        exported_trait_defs: Vec<ExportedTraitDef>,
        extern_fns: Vec<ExternFnInfo>,
        extern_types: Vec<ExternTypeInfo>,
        extern_traits: Vec<ExternTraitInfo>,
        extern_bindings: Vec<ExternBindingInfo>,
        constructor_schemes: Vec<(String, TypeScheme)>,
        interface_cache: &HashMap<String, crate::module_interface::ModuleInterface>,
    ) -> Result<TypedModule, Vec<SpannedTypeError>> {
        let mut instance_defs = instance_defs;
        instance_defs.extend(derived_instance_defs);

        let mut results: Vec<typed_ast::FnTypeEntry> = self
            .imports
            .imported_fn_types
            .into_iter()
            .map(|f| typed_ast::FnTypeEntry {
                name: f.name,
                scheme: f.scheme,
                origin: f.origin,
                qualified_name: f.qualified_name,
            })
            .collect();
        results.extend(
            constructor_schemes
                .iter()
                .map(|(n, s)| typed_ast::FnTypeEntry {
                    name: n.clone(),
                    scheme: s.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        n.clone(),
                    ),
                }),
        );
        results.extend(
            extern_bindings
                .iter()
                .map(|binding| typed_ast::FnTypeEntry {
                    name: binding.name.clone(),
                    scheme: binding.scheme.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        binding.name.clone(),
                    ),
                }),
        );
        results.extend(
            fn_decls
                .iter()
                .enumerate()
                .map(|(i, d)| typed_ast::FnTypeEntry {
                    name: d.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        d.name.clone(),
                    ),
                }),
        );
        // Add instance method types to the flat list for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(
                    &inst.trait_name.local_name,
                    &inst.target_type_name,
                    &m.name,
                );
                results.push(typed_ast::FnTypeEntry {
                    name: qualified.clone(),
                    scheme: m.scheme.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        qualified,
                    ),
                });
            }
        }

        // Build exported_fn_types: the public API surface for downstream importers.
        // Includes pub (transparent) constructors, pub local functions, pub extern methods,
        // and instance methods.
        // Does NOT include imported functions.
        let mut exported_fn_types: Vec<typed_ast::ExportedFn> = Vec::new();

        // 1. Constructors for pub (transparent) types only
        for (cname, scheme) in &constructor_schemes {
            let is_pub_open = module.decls.iter().any(|d| {
                if let Decl::DefType(td) = d {
                    matches!(td.visibility, Visibility::Pub)
                        && constructor_names(td).contains(cname)
                } else {
                    false
                }
            });
            if is_pub_open {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: cname.clone(),
                    scheme: scheme.clone(),
                    origin: None,
                    def_span: None,
                    qualified_name: None,
                });
            }
        }

        // 2. Local pub function declarations
        for (i, decl) in fn_decls.iter().enumerate() {
            if matches!(decl.visibility, Visibility::Pub) {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: decl.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    def_span: Some(decl.span),
                    qualified_name: None,
                });
            }
        }

        // 3. Local pub extern methods
        for binding in &extern_bindings {
            if matches!(binding.visibility, Visibility::Pub) {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: binding.name.clone(),
                    scheme: binding.scheme.clone(),
                    origin: None,
                    def_span: Some(binding.def_span),
                    qualified_name: None,
                });
            }
        }

        let mut functions: Vec<TypedFnDecl> = Vec::new();
        let mut fn_bodies = fn_bodies;
        for (i, decl) in fn_decls.iter().enumerate() {
            let mut body = fn_bodies[i].take().unwrap();
            typed_ast::apply_subst(&mut body, &self.subst);
            functions.push(TypedFnDecl {
                name: decl.name.clone(),
                visibility: decl.visibility,
                params: decl
                    .params
                    .iter()
                    .map(|p| crate::typed_ast::TypedParam {
                        name: p.name.clone(),
                        mode: p.mode,
                    })
                    .collect(),
                body,
                close_self_type: None,
                fn_scope_id: crate::typed_ast::ScopeId(u32::MAX),
            });
        }
        // Build temporary flat list of instance method bodies for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(
                    &inst.trait_name.local_name,
                    &inst.target_type_name,
                    &m.name,
                );
                let close_self_type =
                    if inst.trait_name.local_name == "Disposable" && m.name == "dispose" {
                        Some(inst.target_type_name.clone())
                    } else {
                        None
                    };
                functions.push(TypedFnDecl {
                    name: qualified,
                    visibility: Visibility::Pub,
                    params: m.params.clone(),
                    body: m.body.clone(),
                    close_self_type,
                    fn_scope_id: crate::typed_ast::ScopeId(u32::MAX),
                });
            }
        }

        let fn_schemes: HashMap<String, TypeScheme> = results
            .iter()
            .map(|e| (e.name.clone(), e.scheme.clone()))
            .collect();
        let mut validation_errors: Vec<SpannedTypeError> = Vec::new();
        for func in &functions {
            let current_requirements = fn_schemes
                .get(&func.name)
                .map(|s| s.constraints.as_slice())
                .unwrap_or(&[]);
            // Monomorphic functions have no type variables
            let func_var_names = fn_schemes
                .get(&func.name)
                .map(|s| &s.var_names)
                .cloned()
                .unwrap_or_default();
            if let Err(e) = checks::check_constrained_function_refs(
                &func.body,
                current_requirements,
                &fn_schemes,
                trait_registry,
                &func_var_names,
            ) {
                validation_errors.push(e);
            }
        }

        // fn_schemes already includes imported function schemes with constraints embedded

        // Detect implicit trait constraints from body and merge into fn_constraint_requirements
        for func in &functions {
            let mut fn_type_param_vars: HashSet<TypeVarId> = HashSet::new();
            if let Some(scheme) = fn_schemes.get(&func.name) {
                if let Type::Fn(param_types, ret_ty) = &scheme.ty {
                    for (_, pty) in param_types.iter() {
                        for v in free_vars(pty) {
                            fn_type_param_vars.insert(v);
                        }
                    }
                    for v in free_vars(ret_ty) {
                        fn_type_param_vars.insert(v);
                    }
                }
            }
            let mut constraints = Vec::new();
            checks::detect_trait_constraints(
                &func.body,
                trait_registry,
                &self.subst,
                &fn_type_param_vars,
                &fn_schemes,
                &mut constraints,
            );
            if !constraints.is_empty() {
                constraints.sort();
                constraints.dedup();
                // Merge into fn_constraint_requirements (dedup by trait+var)
                let existing = fn_constraint_requirements
                    .entry(func.name.clone())
                    .or_default();
                for (trait_name, type_vars) in constraints {
                    if !existing
                        .iter()
                        .any(|(t, v)| t == &trait_name && *v == type_vars)
                    {
                        existing.push((trait_name, type_vars));
                    }
                }
            }
        }

        // Fold final constraints into TypeSchemes in fn_types (results) so they
        // propagate to importers via exported_fn_types without a side-channel map.
        for entry in &mut results {
            if let Some(reqs) = fn_constraint_requirements.get(&entry.name) {
                if entry.scheme.constraints.is_empty() && !reqs.is_empty() {
                    entry.scheme.constraints = reqs.clone();
                }
            }
        }
        // Also update exported_fn_types (built earlier from result_schemes)
        for ef in &mut exported_fn_types {
            if let Some(reqs) = fn_constraint_requirements.get(&ef.name) {
                if ef.scheme.constraints.is_empty() && !reqs.is_empty() {
                    ef.scheme.constraints = reqs.clone();
                }
            }
        }

        let mut trait_defs = Vec::new();
        for info in trait_registry.traits().values() {
            let is_imported = self.imported_trait_names.contains(&info.name);
            let method_info: Vec<(String, usize)> = info
                .methods
                .iter()
                .map(|m| (m.name.clone(), m.param_types.len()))
                .collect();
            let method_tc_types: HashMap<String, (Vec<(crate::types::ParamMode, Type)>, Type)> =
                info.methods
                    .iter()
                    .map(|m| {
                        (
                            m.name.clone(),
                            (m.param_types.clone(), m.return_type.clone()),
                        )
                    })
                    .collect();
            let method_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> = info
                .methods
                .iter()
                .filter(|m| !m.constraints.is_empty())
                .map(|m| (m.name.clone(), m.constraints.clone()))
                .collect();
            trait_defs.push(TraitDefInfo {
                name: info.name.clone(),
                trait_id: TraitName::new(info.module_path.clone(), info.name.clone()),
                methods: method_info,
                is_imported,
                type_var_id: info.type_var_id,
                type_var_ids: info.type_var_ids.clone(),
                method_tc_types,
                method_constraints,
            });
        }

        // Convert FnTypeEntry to tuple format for ownership/auto_close APIs
        let results_tuples: Vec<(String, TypeScheme, Option<TraitName>)> = results
            .iter()
            .map(|e| (e.name.clone(), e.scheme.clone(), e.origin.clone()))
            .collect();

        let (ownership_result, ownership_errors) = crate::ownership::check_ownership(
            module,
            &functions,
            &results_tuples,
            &self.registry,
            &self.let_own_spans,
            &self.lambda_own_captures,
            &self.imports.imported_fn_qualifiers,
        );
        let has_ownership_errors = !ownership_errors.is_empty();
        validation_errors.extend(ownership_errors);

        // Filter to exported functions only for cross-module propagation
        let exported_names: HashSet<&str> = exported_fn_types
            .iter()
            .map(|ef| ef.name.as_str())
            .collect();
        let exported_fn_qualifiers: HashMap<_, _> = ownership_result
            .fn_qualifiers
            .into_iter()
            .filter(|(name, _)| exported_names.contains(name.as_str()))
            .collect();

        // Stamp ScopeIds on every typed function body before analysis/lowering.
        // Both auto_close and ir::lower rely on scope identity being stable and
        // unique — ScopeIds replace the fragile span-based lookup.
        crate::scope_ids::stamp_functions(&mut functions);

        // Only run auto_close if ownership checking passed — auto_close depends on
        // complete ownership results and may encounter unexpected types otherwise.
        let auto_close = if !has_ownership_errors {
            let (auto_close, auto_close_errors) = crate::auto_close::compute_auto_close(
                &functions,
                &results_tuples,
                trait_registry,
                &ownership_result.moves,
            );
            validation_errors.extend(auto_close_errors);
            auto_close
        } else {
            crate::typed_ast::AutoCloseInfo::default()
        };

        if !validation_errors.is_empty() {
            validation_errors.sort_by_key(|e| e.span);
            return Err(validation_errors);
        }

        let struct_decls: Vec<_> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Record { fields } => Some(StructDecl {
                        name: td.name.clone(),
                        type_params: td.type_params.clone(),
                        fields: fields.clone(),
                        qualified_name: typed_ast::QualifiedName::new(
                            module_path.to_string(),
                            td.name.clone(),
                        ),
                    }),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let sum_decls: Vec<SumDecl> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Sum { variants } => Some(SumDecl {
                        name: td.name.clone(),
                        type_params: td.type_params.clone(),
                        variants: variants.clone(),
                        qualified_name: typed_ast::QualifiedName::new(
                            module_path.to_string(),
                            td.name.clone(),
                        ),
                    }),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let _local_type_names: HashSet<String> = module
            .decls
            .iter()
            .filter_map(|d| {
                if let Decl::DefType(td) = d {
                    Some(td.name.clone())
                } else {
                    None
                }
            })
            .collect();
        let mut type_visibility: HashMap<String, Visibility> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                type_visibility.insert(td.name.clone(), td.visibility);
            }
            if let Decl::Extern {
                alias: Some(name),
                alias_visibility,
                is_trait: false,
                ..
            } = decl
            {
                type_visibility.insert(
                    name.clone(),
                    alias_visibility.unwrap_or(Visibility::Private),
                );
            }
        }

        let mut exported_trait_defs = exported_trait_defs;
        exported_trait_defs.extend(self.reexported_trait_defs);

        // Build exported_type_infos from fully-resolved TypeInfo in the registry.
        // This allows importers to register types without re-resolving from AST.
        let mut exported_type_infos: HashMap<String, typed_ast::ExportedTypeInfo> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                if matches!(td.visibility, Visibility::Private) {
                    continue;
                }
                if let Some(type_info) = self.registry.lookup_type(&td.name) {
                    let kind = match &type_info.kind {
                        crate::type_registry::TypeKind::Record { fields } => {
                            typed_ast::ExportedTypeKind::Record {
                                fields: fields.clone(),
                            }
                        }
                        crate::type_registry::TypeKind::Sum { variants } => {
                            typed_ast::ExportedTypeKind::Sum {
                                variants: variants
                                    .iter()
                                    .map(|v| typed_ast::ExportedVariantInfo {
                                        name: v.name.clone(),
                                        fields: v.fields.clone(),
                                    })
                                    .collect(),
                            }
                        }
                    };
                    exported_type_infos.insert(
                        td.name.clone(),
                        typed_ast::ExportedTypeInfo {
                            name: td.name.clone(),
                            source_module: module_path.to_string(),
                            type_params: td.type_params.clone(),
                            type_param_vars: type_info.type_param_vars.clone(),
                            kind,
                            lifts: type_info.lifts.clone(),
                        },
                    );
                }
            }
        }

        // Include extern type aliases in exported_type_infos so they flow
        // through the interface like any other type — consumers register
        // them uniformly via register_type_from_export.
        for decl in &module.decls {
            if let Decl::Extern {
                alias: Some(name),
                is_trait: false,
                ..
            } = decl
            {
                if exported_type_infos.contains_key(name) {
                    continue;
                }
                if let Some(type_info) = self.registry.lookup_type(name) {
                    exported_type_infos.insert(
                        name.clone(),
                        typed_ast::ExportedTypeInfo {
                            name: name.clone(),
                            source_module: module_path.to_string(),
                            type_params: type_info.type_params.clone(),
                            type_param_vars: type_info.type_param_vars.clone(),
                            kind: typed_ast::ExportedTypeKind::Opaque,
                            lifts: type_info.lifts.clone(),
                        },
                    );
                }
            }
        }

        // Include imported types (sum and record) in exported_type_infos so
        // IR lowering can resolve them without AST fallback.
        for (type_name, (source_path, _vis)) in &self.imports.imported_type_info {
            if exported_type_infos.contains_key(type_name) {
                continue;
            }
            if let Some(iface) = interface_cache.get(source_path.as_str()) {
                if let Some(ts) = iface.exported_types.iter().find(|t| t.name == *type_name) {
                    let export =
                        crate::module_interface::type_summary_to_export_info(ts, source_path);
                    exported_type_infos.insert(type_name.clone(), export);
                }
            }
        }

        let fn_types_by_name: HashMap<String, usize> = results
            .iter()
            .enumerate()
            .map(|(i, e)| (e.name.clone(), i))
            .collect();

        Ok(TypedModule {
            module_path,
            fn_types: results,
            fn_types_by_name,
            exported_fn_types,
            functions,
            trait_defs,
            instance_defs,
            extern_fns,
            extern_types,
            extern_traits,
            struct_decls,
            sum_decls,
            type_visibility,
            reexported_fn_types: self.reexported_fn_types,
            reexported_type_names: self.reexported_type_names,
            reexported_type_visibility: self.reexported_type_visibility,
            exported_trait_defs,
            exported_type_infos,
            auto_close,
            exported_fn_qualifiers,
            module_source: None,
        })
    }
}

/// Phase: Register traits (imported + local), process deriving, register impl instances.
/// Returns (trait_registry, exported_trait_defs, derived_instance_defs, imported_instance_defs, trait_method_map).
///
/// Extracted from `infer_module_inner` so its locals are deallocated before the
/// SCC function inference phase, reducing peak stack usage.
fn process_traits_and_deriving(
    state: &mut ModuleInferenceState,
    module: &Module,
    interface_cache: &HashMap<String, crate::module_interface::ModuleInterface>,
    module_path: &str,
    is_core_module: bool,
    pending_extern_traits: Vec<PendingExternTrait>,
) -> Result<TraitsAndDerivingResult, SpannedTypeError> {
    let mut trait_registry = TraitRegistry::new();

    // Phase 1: Import instances from cached modules via orphan-rule lookup
    let imported_instance_defs = import_cached_instances(
        &mut trait_registry,
        &state.imports.imported_type_info,
        &state.imported_trait_defs,
        interface_cache,
    );

    // Phase 2: Register imported trait definitions
    register_imported_trait_defs(
        &mut trait_registry,
        &state.imported_trait_defs,
        &mut state.gen,
        &state.prelude_imported_names,
    );

    // Phase 2b: Register trait aliases from imports
    for (alias, canonical) in &state.trait_aliases {
        trait_registry.register_trait_alias(alias.clone(), canonical.clone());
    }

    // Phase 2c: Register extern traits (Java interfaces exposed as Krypton traits)
    let (extern_trait_exported_defs, extern_trait_infos) = register_extern_traits(
        state,
        &mut trait_registry,
        pending_extern_traits,
        module_path,
    )?;

    // Phase 3: Process local DefTrait declarations
    let mut exported_trait_defs =
        register_local_traits(state, &mut trait_registry, module, module_path)?;
    exported_trait_defs.extend(extern_trait_exported_defs);

    // Phase 4: Process DefImpl declarations (register instances). User
    // impls are registered before the deriving pass so that derivings can
    // satisfy their field-constraint obligations against local impls.
    // E.g. `type Conn { s: ~Sock, l: ~Log } deriving (Disposable)` needs
    // `impl Disposable[Sock]` and `impl Disposable[Log]` visible when the
    // derivation is checked. The hard-error on duplicate impls still
    // triggers: `DerivingConflictsWithImpl` is detected at the top of
    // `process_deriving` by scanning `module.decls` directly.
    register_impl_instances(state, &mut trait_registry, module, module_path)?;

    // Phase 5: Deriving pass
    let derived_instance_defs =
        process_deriving(&mut trait_registry, module, &state.registry, module_path)?;

    // Compute trait_method_map between phases 5 and 6, with collision detection
    let mut trait_method_map: HashMap<String, TraitName> = HashMap::new();
    for (method_name, trait_id, is_prelude) in trait_registry.trait_method_names() {
        if let Some(existing) = trait_method_map.get(&method_name) {
            let existing_is_prelude = trait_registry
                .lookup_trait(existing)
                .is_some_and(|info| info.is_prelude);
            if !existing_is_prelude && !is_prelude {
                // Two non-prelude traits with same method name — check overlap
                let existing_params = trait_method_param_types(&trait_registry, existing, &method_name);
                let new_params = trait_method_param_types(&trait_registry, &trait_id, &method_name);
                let overlaps = match (&existing_params, &new_params) {
                    (Some(a), Some(b)) => {
                        if a.len() != b.len() {
                            true // arity mismatch
                        } else {
                            types_overlap(a, b)
                        }
                    }
                    _ => true, // can't resolve → assume overlap
                };
                if overlaps {
                    return Err(spanned(
                        TypeError::TraitMethodCollision {
                            method_name: method_name.clone(),
                            trait1: existing.local_name.clone(),
                            trait2: trait_id.local_name.clone(),
                        },
                        (0, 0),
                    ));
                }
                // Non-overlapping — first wins for trait_method_map
            } else if existing_is_prelude && !is_prelude {
                // Local shadows prelude
                trait_method_map.insert(method_name, trait_id);
            }
            // If existing is not prelude and new is prelude → skip (local wins)
            // If both prelude → keep existing (prelude is curated, first wins)
        } else {
            trait_method_map.insert(method_name, trait_id);
        }
    }

    // Phase 6: Conflict and reserved-name checks
    check_trait_name_conflicts(module, &trait_method_map, &trait_registry, &state.registry, is_core_module)?;

    Ok((
        trait_registry,
        exported_trait_defs,
        extern_trait_infos,
        derived_instance_defs,
        imported_instance_defs,
        trait_method_map,
    ))
}

/// Phase 1: Import instances from cached modules via orphan-rule lookup.
fn import_cached_instances(
    trait_registry: &mut TraitRegistry,
    imported_type_info: &HashMap<String, (String, Visibility)>,
    imported_trait_defs: &[ExportedTraitDef],
    interface_cache: &HashMap<String, crate::module_interface::ModuleInterface>,
) -> Vec<InstanceDefInfo> {
    let mut imported_instance_defs = Vec::new();
    // Structural instance lookup: for each type/trait in scope, look up instances
    // in the defining module. The orphan rule guarantees instances live in the
    // module defining the type or the trait.
    let mut source_modules: HashSet<&str> = HashSet::new();
    for (source_path, _) in imported_type_info.values() {
        source_modules.insert(source_path.as_str());
    }
    // Include modules that define imported traits (covers core modules
    // providing instances for builtin types like Int, Bool, etc.)
    for td in imported_trait_defs {
        source_modules.insert(td.module_path.as_str());
    }
    // Vec is a language-level builtin (array literal syntax []),
    // so always include its defining module for instance resolution.
    source_modules.insert("core/vec");

    let mut seen_instances: HashSet<(TraitName, Vec<Type>)> = HashSet::new();
    for mod_path in &source_modules {
        if let Some(iface) = interface_cache.get(*mod_path) {
            for inst_summary in &iface.exported_instances {
                let key = (
                    inst_summary.trait_name.clone(),
                    inst_summary.target_types.clone(),
                );
                if seen_instances.insert(key) {
                    let instance = InstanceInfo {
                        trait_name: inst_summary.trait_name.clone(),
                        target_types: inst_summary.target_types.clone(),
                        target_type_name: inst_summary.target_type_name.clone(),
                        type_var_ids: inst_summary.type_var_ids.clone(),
                        constraints: inst_summary.constraints.clone(),
                        span: (0, 0),
                        is_builtin: false,
                    };
                    match trait_registry.register_instance(instance) {
                        Ok(()) => {}
                        Err(boxed) => match *boxed {
                            (TypeError::DuplicateInstance { .. }, _) => {
                                // Expected: same instance imported via multiple transitive paths
                            }
                            (e, span) => {
                                panic!("ICE: unexpected error registering imported instance: {e:?} at {span:?}")
                            }
                        },
                    }
                    imported_instance_defs.push(
                        crate::module_interface::instance_summary_to_def_info(inst_summary),
                    );
                }
            }
        }
    }
    imported_instance_defs
}

/// Phase 2: Register trait definitions imported from other modules.
fn register_imported_trait_defs(
    trait_registry: &mut TraitRegistry,
    imported_trait_defs: &[ExportedTraitDef],
    gen: &mut TypeVarGen,
    prelude_imported_names: &HashSet<String>,
) {
    // Register trait definitions imported from other modules
    for trait_def in imported_trait_defs {
        // Skip if this exact trait (same TraitName) is already registered
        let trait_id = TraitName::new(trait_def.module_path.clone(), trait_def.name.clone());
        if trait_registry.lookup_trait(&trait_id).is_some() {
            continue;
        }

        // Build remap table covering primary + all secondary trait type vars.
        // The source module uses its own TypeVarId namespace; we allocate fresh
        // ids in the local namespace so that imported method types unify cleanly.
        let new_tv_id = gen.fresh();
        let mut new_type_var_ids: Vec<TypeVarId> = Vec::with_capacity(trait_def.type_var_ids.len());
        new_type_var_ids.push(new_tv_id);
        let mut remap: HashMap<TypeVarId, TypeVarId> = HashMap::new();
        if let Some(&primary_old) = trait_def.type_var_ids.first() {
            remap.insert(primary_old, new_tv_id);
        } else {
            remap.insert(trait_def.type_var_id, new_tv_id);
        }
        for &old_id in trait_def.type_var_ids.iter().skip(1) {
            let new_id = gen.fresh();
            remap.insert(old_id, new_id);
            new_type_var_ids.push(new_id);
        }

        let mut trait_methods = Vec::new();
        for method in &trait_def.methods {
            let param_types: Vec<(crate::types::ParamMode, Type)> = method
                .param_types
                .iter()
                .map(|(m, t)| (*m, remap_type_vars(t, &remap)))
                .collect();
            let return_type = remap_type_vars(&method.return_type, &remap);

            // Method constraints use the method's own type vars (not the trait's),
            // so they don't need remapping.
            trait_methods.push(TraitMethod {
                name: method.name.clone(),
                param_types,
                return_type,
                constraints: method.constraints.clone(),
            });
        }

        let is_prelude = prelude_imported_names.contains(&trait_def.name);
        let superclass_names: Vec<TraitName> = trait_def.superclasses.clone();
        // register_trait checks for bare-name collisions and returns AmbiguousTraitName
        // if two different modules define traits with the same bare name
        if let Err(_e) = trait_registry.register_trait(TraitInfo {
            name: trait_def.name.clone(),
            module_path: trait_def.module_path.clone(),
            type_var: trait_def.type_var.clone(),
            type_var_id: new_tv_id,
            type_var_ids: new_type_var_ids,
            type_var_names: trait_def.type_var_names.clone(),
            type_var_arity: trait_def.type_var_arity,
            superclasses: superclass_names,
            methods: trait_methods,
            span: (0, 0),
            is_prelude,
        }) {
            // For now, silently skip traits that collide — aliasing will resolve this
            continue;
        }
    }
}

/// Phase 2c: Register extern traits (Java interfaces exposed as Krypton traits).
///
/// Each `extern java "..." as trait Name[a] { ... }` is registered as a real trait
/// in the TraitRegistry. Methods are bound into the environment via `bind_trait_method`,
/// making them callable like any other trait method.
fn register_extern_traits(
    state: &mut ModuleInferenceState,
    trait_registry: &mut TraitRegistry,
    pending: Vec<PendingExternTrait>,
    module_path: &str,
) -> Result<(Vec<ExportedTraitDef>, Vec<ExternTraitInfo>), SpannedTypeError> {
    let mut exported_defs = Vec::new();
    let mut extern_trait_infos = Vec::new();

    let empty_tp_arity: HashMap<String, usize> = HashMap::new();

    for ext in pending {
        // Allocate fresh type var for the trait's type parameter
        if ext.type_params.is_empty() {
            return Err(spanned(
                TypeError::WrongArity {
                    expected: 1,
                    actual: 0,
                },
                ext.span,
            ));
        }

        let tv_id = state.gen.fresh();
        let type_var_name = ext.type_params[0].clone();

        // Build type param map for resolving method types
        let mut tp_map = HashMap::new();
        tp_map.insert(type_var_name.clone(), tv_id);
        // Additional type params (rare but supported)
        let mut all_tv_ids = vec![tv_id];
        for tp in &ext.type_params[1..] {
            let id = state.gen.fresh();
            tp_map.insert(tp.clone(), id);
            all_tv_ids.push(id);
        }

        let trait_name = TraitName::new(module_path.to_string(), ext.name.clone());
        let mut trait_methods = Vec::new();
        let mut exported_methods = Vec::new();
        let mut extern_method_infos = Vec::new();

        for method in &ext.methods {
            // Validate: no @nullable or @throws on trait methods
            if method.nullable {
                return Err(spanned(
                    TypeError::InvalidNullableReturn {
                        name: method.name.clone(),
                        actual_return_type: Type::Named("Unit".to_string(), vec![]),
                    },
                    method.span,
                ));
            }
            if method.throws {
                return Err(spanned(
                    TypeError::InvalidThrowsReturn {
                        name: method.name.clone(),
                        actual_return_type: Type::Named("Unit".to_string(), vec![]),
                    },
                    method.span,
                ));
            }

            // Resolve param types using the trait's type param map
            let mut param_types = Vec::new();
            for (_param_name, ty_expr) in &method.params {
                let ty = type_registry::resolve_type_expr(
                    ty_expr,
                    &tp_map,
                    &empty_tp_arity,
                    &state.registry,
                    ResolutionContext::UserAnnotation,
                    None,
                )
                .map_err(|e| spanned(e, method.span))?;
                param_types.push(ty);
            }

            let return_type = type_registry::resolve_type_expr(
                &method.return_type,
                &tp_map,
                &empty_tp_arity,
                &state.registry,
                ResolutionContext::UserAnnotation,
                None,
            )
            .map_err(|e| spanned(e, method.span))?;

            // Build TypeScheme for the method: forall [tv_id]. param_types -> return_type
            let fn_type = Type::fn_consuming(param_types.clone(), return_type.clone());
            let var_names: HashMap<TypeVarId, String> = all_tv_ids
                .iter()
                .zip(ext.type_params.iter())
                .map(|(id, name)| (*id, name.clone()))
                .collect();
            let scheme = TypeScheme {
                vars: all_tv_ids.clone(),
                constraints: vec![],
                ty: fn_type,
                var_names,
            };

            // Bind the method into the type environment
            state.env.bind_trait_method(
                method.name.clone(),
                scheme,
                module_path.to_string(),
                ext.name.clone(),
                method.name.clone(),
                false,
            );

            // Collect param types excluding self for the extern trait method info.
            // Only remove the *first* param matching the trait type var (the self
            // param) — later params with the same type should be kept.
            let self_index = param_types
                .iter()
                .position(|t| matches!(t, Type::Var(id) if *id == tv_id));
            let non_self_param_types: Vec<Type> = param_types
                .iter()
                .enumerate()
                .filter(|(i, _)| Some(*i) != self_index)
                .map(|(_, t)| t.clone())
                .collect();

            // Extern trait methods are currently mode-erased to `Consume`:
            // the parser's `ExternMethod` has no per-param mode field, so
            // every extern trait parameter lands in the trait registry as
            // `ParamMode::Consume`. The witness-side exact-mode check in
            // `typecheck_impl_methods` therefore enforces `Consume` on every
            // Krypton-side impl of an extern trait, which matches the only
            // shape a user can currently declare. Widening extern method
            // modes is a follow-up.
            let param_types_with_modes: Vec<(crate::types::ParamMode, Type)> = param_types
                .iter()
                .cloned()
                .map(|t| (crate::types::ParamMode::Consume, t))
                .collect();

            trait_methods.push(TraitMethod {
                name: method.name.clone(),
                param_types: param_types_with_modes.clone(),
                return_type: return_type.clone(),
                constraints: vec![],
            });

            exported_methods.push(ExportedTraitMethod {
                name: method.name.clone(),
                param_types: param_types_with_modes.clone(),
                return_type: return_type.clone(),
                constraints: vec![],
            });

            extern_method_infos.push(ExternTraitMethodInfo {
                name: method.name.clone(),
                param_types: non_self_param_types,
                return_type: return_type.clone(),
            });
        }

        // Register in the trait registry
        trait_registry
            .register_trait(TraitInfo {
                name: ext.name.clone(),
                module_path: module_path.to_string(),
                type_var: type_var_name.clone(),
                type_var_id: tv_id,
                type_var_ids: all_tv_ids.clone(),
                type_var_names: ext.type_params.clone(),
                type_var_arity: 0,
                superclasses: vec![],
                methods: trait_methods,
                span: ext.span,
                is_prelude: false,
            })
            .map_err(|e| spanned(e, ext.span))?;

        exported_defs.push(ExportedTraitDef {
            visibility: Visibility::Pub,
            name: ext.name.clone(),
            module_path: module_path.to_string(),
            type_var: type_var_name,
            type_var_id: tv_id,
            type_var_ids: all_tv_ids,
            type_var_names: ext.type_params.clone(),
            type_var_arity: 0,
            superclasses: vec![],
            methods: exported_methods,
        });

        extern_trait_infos.push(ExternTraitInfo {
            trait_name,
            java_interface: ext.java_interface,
            methods: extern_method_infos,
        });
    }

    Ok((exported_defs, extern_trait_infos))
}

/// Phase 3: Process local DefTrait declarations.
fn register_local_traits(
    state: &mut ModuleInferenceState,
    trait_registry: &mut TraitRegistry,
    module: &Module,
    module_path: &str,
) -> Result<Vec<ExportedTraitDef>, SpannedTypeError> {
    // Process DefTrait declarations
    let mut exported_trait_defs: Vec<ExportedTraitDef> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefTrait {
            visibility,
            name,
            type_params: trait_type_params,
            superclasses,
            methods,
            span,
            ..
        } = decl
        {
            // Type-namespace check: `name` must not already exist as a type
            // (or type alias) in this module. Prelude types are shadowable.
            if let Some(existing_type) = state.registry.lookup_type(name) {
                if !existing_type.is_prelude {
                    return Err(spanned(
                        TypeError::TypeTraitNameConflict { name: name.clone() },
                        *span,
                    ));
                }
            }
            // Type-namespace check: `name` must not already be declared as a
            // trait in this module. Prelude traits are shadowable.
            if let Some(existing_trait) = trait_registry.lookup_trait_by_name(name) {
                if !existing_trait.is_prelude {
                    return Err(spanned(
                        TypeError::DuplicateTrait { name: name.clone() },
                        *span,
                    ));
                }
            }
            // Index the first trait type parameter for arity/InstanceInfo but
            // register ALL trait type parameters in the method resolution
            // environment so multi-parameter trait method bodies can reference
            // `b`, `c`, etc.
            let type_param = &trait_type_params[0];
            let tv_id = state.gen.fresh();
            let type_var_arity = type_param.arity;
            let mut type_param_map = HashMap::new();
            let mut type_param_arity = HashMap::new();
            type_param_map.insert(type_param.name.clone(), tv_id);
            type_param_arity.insert(type_param.name.clone(), type_param.arity);
            // Track ALL trait type parameter ids in declaration order so the
            // multi-param resolution pass can freshen each one at call sites.
            let mut trait_all_tv_ids: Vec<TypeVarId> = vec![tv_id];
            let mut trait_all_tv_names: Vec<String> = vec![type_param.name.clone()];
            for extra in trait_type_params.iter().skip(1) {
                let extra_id = state.gen.fresh();
                type_param_map.insert(extra.name.clone(), extra_id);
                type_param_arity.insert(extra.name.clone(), extra.arity);
                trait_all_tv_ids.push(extra_id);
                trait_all_tv_names.push(extra.name.clone());
            }

            // Check that all trait methods have explicit return type annotations
            for method in methods {
                if method.return_type.is_none() {
                    return Err(spanned(
                        TypeError::MissingTraitMethodAnnotation {
                            trait_name: name.clone(),
                            method_name: method.name.clone(),
                        },
                        method.span,
                    ));
                }
            }

            let mut trait_methods = Vec::new();
            let mut exported_methods = Vec::new();
            for method in methods {
                let mut method_type_param_map = type_param_map.clone();
                let mut method_type_param_arity = type_param_arity.clone();
                let mut method_tv_ids = Vec::new();
                for tv_param in &method.type_params {
                    if !method_type_param_map.contains_key(&tv_param.name) {
                        let mv_id = state.gen.fresh();
                        method_type_param_map.insert(tv_param.name.clone(), mv_id);
                        method_type_param_arity.insert(tv_param.name.clone(), tv_param.arity);
                        method_tv_ids.push(mv_id);
                    }
                }

                let mut param_types = Vec::new();
                let mut param_modes: Vec<crate::types::ParamMode> = Vec::new();
                for p in &method.params {
                    param_modes.push(p.mode);
                    if let Some(ref ty_expr) = p.ty {
                        param_types.push(
                            type_registry::resolve_type_expr(
                                ty_expr,
                                &method_type_param_map,
                                &method_type_param_arity,
                                &state.registry,
                                ResolutionContext::UserAnnotation,
                                None,
                            )
                            .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                            .map_err(|e| spanned(e, method.span))?,
                        );
                    } else {
                        param_types.push(Type::Var(state.gen.fresh()));
                    }
                }
                let return_type = if let Some(ref ret_expr) = method.return_type {
                    type_registry::resolve_type_expr(
                        ret_expr,
                        &method_type_param_map,
                        &method_type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, method.span))?
                } else {
                    Type::Var(state.gen.fresh())
                };

                // Shape-var cap: at most 6 `shape` variables per trait
                // method. The cap exists to protect the compiler from
                // wedging on cartesian-product enumeration (2^N forks per
                // method body); 6 → 64 forks. `shape` is a def-site
                // polymorphism mechanism and real use cases past N=2 are
                // unknown, so 6 is a sanity bound, not a user restriction.
                // Enforced at trait registration so every impl path sees
                // a well-formed method.
                {
                    let mut shape_vars: Vec<TypeVarId> = Vec::new();
                    let mut seen: std::collections::HashSet<TypeVarId> =
                        std::collections::HashSet::new();
                    for pt in &param_types {
                        for v in crate::types::collect_shape_vars(pt) {
                            if seen.insert(v) {
                                shape_vars.push(v);
                            }
                        }
                    }
                    for v in crate::types::collect_shape_vars(&return_type) {
                        if seen.insert(v) {
                            shape_vars.push(v);
                        }
                    }
                    if shape_vars.len() > 6 {
                        return Err(spanned(
                            TypeError::TooManyShapeParameters {
                                trait_name: name.clone(),
                                method_name: method.name.clone(),
                                count: shape_vars.len(),
                            },
                            method.span,
                        ));
                    }
                }

                let fn_ty = Type::Fn(
                    param_modes
                        .iter()
                        .copied()
                        .zip(param_types.iter().cloned())
                        .collect(),
                    Box::new(return_type.clone()),
                );
                // Include ALL trait type parameter ids (not just the primary) so
                // `scheme.instantiate()` freshens secondary trait params at every
                // call site. Without this, `b` in `Convert[a, b]` would leak across
                // call sites and the multi-param solver would never see fresh ids.
                let mut all_vars = trait_all_tv_ids.clone();
                all_vars.extend_from_slice(&method_tv_ids);
                let scheme = TypeScheme {
                    vars: all_vars,
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };
                state.env.bind_trait_method(
                    method.name.clone(),
                    scheme,
                    module_path.to_string(),
                    name.clone(),
                    method.name.clone(),
                    false,
                );

                // Resolve method-level where constraints
                let mut method_constraints: Vec<(TraitName, Vec<TypeVarId>)> = Vec::new();
                for constraint in &method.constraints {
                    let tv_names = require_param_vars(constraint)?;
                    let tvs: Vec<TypeVarId> = tv_names
                        .iter()
                        .filter_map(|n| method_type_param_map.get(*n).copied())
                        .collect();
                    if tvs.len() == tv_names.len() && !tvs.is_empty() {
                        // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
                        // Validation deferred to instance resolution phase.
                        let tn = trait_registry
                            .lookup_trait_by_name(&constraint.trait_name)
                            .map(|ti| ti.trait_name())
                            .unwrap_or_else(|| {
                                TraitName::new(
                                    module_path.to_string(),
                                    constraint.trait_name.clone(),
                                )
                            });
                        method_constraints.push((tn, tvs));
                    }
                }

                let param_types_with_modes: Vec<(crate::types::ParamMode, Type)> = param_modes
                    .iter()
                    .copied()
                    .zip(param_types.iter().cloned())
                    .collect();

                exported_methods.push(ExportedTraitMethod {
                    name: method.name.clone(),
                    param_types: param_types_with_modes.clone(),
                    return_type: return_type.clone(),
                    constraints: method_constraints.clone(),
                });

                trait_methods.push(TraitMethod {
                    name: method.name.clone(),
                    param_types: param_types_with_modes,
                    return_type,
                    constraints: method_constraints,
                });
            }

            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
            // Validation deferred to instance resolution phase.
            for sc in superclasses {
                require_param_vars(sc)?;
            }
            let superclass_names: Vec<TraitName> = superclasses
                .iter()
                .map(|sc| {
                    trait_registry
                        .lookup_trait_by_name(&sc.trait_name)
                        .map(|ti| ti.trait_name())
                        .unwrap_or_else(|| {
                            TraitName::new(module_path.to_string(), sc.trait_name.clone())
                        })
                })
                .collect();
            trait_registry
                .register_trait(TraitInfo {
                    name: name.clone(),
                    module_path: module_path.to_string(),
                    type_var: type_param.name.clone(),
                    type_var_id: tv_id,
                    type_var_ids: trait_all_tv_ids.clone(),
                    type_var_names: trait_all_tv_names.clone(),
                    type_var_arity,
                    superclasses: superclass_names.clone(),
                    methods: trait_methods,
                    span: *span,
                    is_prelude: false,
                })
                .map_err(|e| spanned(e, *span))?;

            exported_trait_defs.push(ExportedTraitDef {
                visibility: *visibility,
                name: name.clone(),
                module_path: module_path.to_string(),
                type_var: type_param.name.clone(),
                type_var_id: tv_id,
                type_var_ids: trait_all_tv_ids,
                type_var_names: trait_all_tv_names,
                type_var_arity,
                superclasses: superclass_names,
                methods: exported_methods,
            });
        }
    }
    Ok(exported_trait_defs)
}

/// Phase 4: Process deriving declarations.
fn process_deriving(
    trait_registry: &mut TraitRegistry,
    module: &Module,
    registry: &TypeRegistry,
    module_path: &str,
) -> Result<Vec<InstanceDefInfo>, SpannedTypeError> {
    // Deriving pass
    let mut derived_instance_defs: Vec<InstanceDefInfo> = Vec::new();
    for decl in &module.decls {
        if let Decl::DefType(type_decl) = decl {
            if type_decl.deriving.is_empty() {
                continue;
            }
            let type_info = registry.lookup_type(&type_decl.name).unwrap();

            for trait_name in &type_decl.deriving {
                if trait_registry.lookup_trait_by_name(trait_name).is_none() {
                    return Err(spanned(
                        TypeError::UnknownTrait {
                            name: trait_name.clone(),
                        },
                        type_decl.span,
                    ));
                }

                let field_types: Vec<&Type> = match &type_info.kind {
                    crate::type_registry::TypeKind::Record { fields } => {
                        fields.iter().map(|(_, ty)| ty).collect()
                    }
                    crate::type_registry::TypeKind::Sum { variants } => {
                        variants.iter().flat_map(|v| v.fields.iter()).collect()
                    }
                };

                let derived_type_var_ids: HashMap<String, TypeVarId> = type_decl
                    .type_params
                    .iter()
                    .cloned()
                    .zip(type_info.type_param_vars.iter().copied())
                    .collect();
                let local_type_params: HashMap<TypeVarId, String> = derived_type_var_ids
                    .iter()
                    .map(|(name, id)| (*id, name.clone()))
                    .collect();
                let mut derived_constraints: Vec<ResolvedConstraint> = Vec::new();
                let mut visited_constraints: HashSet<(String, String)> = HashSet::new();

                for ft in &field_types {
                    // Disposable: only owned fields contribute constraints;
                    // plain fields are skipped entirely — the derived dispose
                    // body binds them but does nothing with them.
                    let check_ty: &Type = if trait_name == "Disposable" {
                        match ft {
                            Type::Own(inner) => inner.as_ref(),
                            _ => continue,
                        }
                    } else {
                        ft
                    };
                    if !derive::collect_derived_constraints_for_type(
                        trait_registry,
                        trait_name,
                        check_ty,
                        &local_type_params,
                        &type_decl.name,
                        &mut visited_constraints,
                        &mut derived_constraints,
                    ) {
                        return Err(spanned(
                            TypeError::CannotDerive {
                                trait_name: trait_name.clone(),
                                type_name: type_decl.name.clone(),
                                field_type: format!("{}", check_ty),
                            },
                            type_decl.span,
                        ));
                    }
                }

                let type_args: Vec<Type> = type_info
                    .type_param_vars
                    .iter()
                    .map(|&v| Type::Var(v))
                    .collect();
                let target_type = Type::Named(type_decl.name.clone(), type_args);
                let target_type_name = type_decl.name.clone();

                let method_name = match trait_name.as_str() {
                    "Eq" => "eq",
                    "Show" => "show",
                    "Hash" => "hash",
                    "Disposable" => "dispose",
                    _ => continue,
                };

                // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
                // Validation deferred to instance resolution phase.
                let derive_full_trait_name = trait_registry
                    .lookup_trait_by_name(trait_name)
                    .map(|ti| ti.trait_name())
                    .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));
                // A hand-written `impl Trait[T]` for the same (trait, type)
                // conflicts with the `deriving` clause. `register_impl_instances`
                // has already populated the instance table, so we can query it
                // directly — this uses the same unification-based equality as
                // `register_instance` and correctly handles `Own`/`Shape`
                // wrapper stripping and arity. The default error
                // (`DuplicateInstance` fired from `register_instance` below)
                // points at the impl's span and uses generic wording — emit
                // a targeted diagnostic at the `deriving` clause instead so
                // the user sees "remove the deriving or the impl".
                if trait_registry
                    .find_instance_multi(&derive_full_trait_name, &[target_type.clone()])
                    .is_some()
                {
                    return Err(spanned(
                        TypeError::DerivingConflictsWithImpl {
                            trait_name: trait_name.clone(),
                            type_name: type_decl.name.clone(),
                        },
                        type_decl.span,
                    ));
                }

                let instance = InstanceInfo {
                    trait_name: derive_full_trait_name.clone(),
                    target_types: vec![target_type.clone()],
                    target_type_name: target_type_name.clone(),
                    type_var_ids: derived_type_var_ids.clone(),
                    constraints: derived_constraints.clone(),
                    span: type_decl.span,
                    is_builtin: false,
                };
                trait_registry
                    .register_instance(instance)
                    .map_err(|boxed| {
                        let (e, existing_span) = *boxed;
                        duplicate_instance_spanned(e, type_decl.span, existing_span)
                    })?;

                let syn_span: Span = (0, 0);
                let trait_id_for_synth = Some(derive_full_trait_name.clone());
                let (body, fn_ty) = match trait_name.as_str() {
                    "Eq" => derive::synthesize_eq_body(type_info, &target_type, syn_span),
                    "Show" => derive::synthesize_show_body(
                        type_info,
                        &target_type,
                        syn_span,
                        trait_id_for_synth.clone(),
                    ),
                    "Hash" => derive::synthesize_hash_body(
                        type_info,
                        &target_type,
                        syn_span,
                        trait_id_for_synth.clone(),
                    ),
                    "Disposable" => derive::synthesize_dispose_body(
                        type_info,
                        &target_type,
                        syn_span,
                        trait_id_for_synth.clone(),
                    ),
                    _ => continue,
                };

                let mk_param = |n: &str| crate::typed_ast::TypedParam {
                    name: n.to_string(),
                    mode: crate::types::ParamMode::Consume,
                };
                let params: Vec<crate::typed_ast::TypedParam> = match trait_name.as_str() {
                    "Eq" => vec![mk_param("__a"), mk_param("__b")],
                    "Show" | "Hash" | "Disposable" => vec![mk_param("__a")],
                    _ => vec![],
                };

                let scheme = TypeScheme {
                    vars: vec![],
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };

                derived_instance_defs.push(InstanceDefInfo {
                    trait_name: derive_full_trait_name.clone(),
                    target_type_name,
                    target_types: vec![target_type],
                    type_var_ids: derived_type_var_ids.clone(),
                    constraints: derived_constraints.clone(),
                    methods: vec![typed_ast::InstanceMethod {
                        name: method_name.to_string(),
                        params,
                        body,
                        scheme,
                        constraint_pairs: vec![],
                    }],
                    is_intrinsic: false,
                });
            }
        }

        // Extern type deriving
        if let Decl::Extern {
            alias: Some(name),
            deriving,
            is_trait: false,
            span,
            ..
        } = decl
        {
            for trait_name in deriving {
                if trait_name != "Disposable" {
                    return Err(spanned(
                        TypeError::CannotDerive {
                            trait_name: trait_name.clone(),
                            type_name: name.clone(),
                            field_type: name.clone(),
                        },
                        *span,
                    ));
                }

                let type_info = registry.lookup_type(name).unwrap();
                let type_args: Vec<Type> = type_info
                    .type_param_vars
                    .iter()
                    .map(|&v| Type::Var(v))
                    .collect();
                let target_type = Type::Named(name.clone(), type_args);

                let derive_full_trait_name = trait_registry
                    .lookup_trait_by_name(trait_name)
                    .map(|ti| ti.trait_name())
                    .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));

                if trait_registry
                    .find_instance_multi(&derive_full_trait_name, &[target_type.clone()])
                    .is_some()
                {
                    return Err(spanned(
                        TypeError::DerivingConflictsWithImpl {
                            trait_name: trait_name.clone(),
                            type_name: name.clone(),
                        },
                        *span,
                    ));
                }

                let instance = InstanceInfo {
                    trait_name: derive_full_trait_name.clone(),
                    target_types: vec![target_type.clone()],
                    target_type_name: name.clone(),
                    type_var_ids: HashMap::new(),
                    constraints: vec![],
                    span: *span,
                    is_builtin: false,
                };
                trait_registry
                    .register_instance(instance)
                    .map_err(|boxed| {
                        let (e, existing_span) = *boxed;
                        duplicate_instance_spanned(e, *span, existing_span)
                    })?;

                let syn_span: Span = (0, 0);
                let (body, fn_ty) =
                    derive::synthesize_extern_dispose_body(&target_type, syn_span);

                let mk_param = |n: &str| crate::typed_ast::TypedParam {
                    name: n.to_string(),
                    mode: crate::types::ParamMode::Consume,
                };

                let scheme = TypeScheme {
                    vars: vec![],
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };

                derived_instance_defs.push(InstanceDefInfo {
                    trait_name: derive_full_trait_name,
                    target_type_name: name.clone(),
                    target_types: vec![target_type],
                    type_var_ids: HashMap::new(),
                    constraints: vec![],
                    methods: vec![typed_ast::InstanceMethod {
                        name: "dispose".to_string(),
                        params: vec![mk_param("__a")],
                        body,
                        scheme,
                        constraint_pairs: vec![],
                    }],
                    is_intrinsic: false,
                });
            }
        }
    }
    Ok(derived_instance_defs)
}

/// Resolve parser `TypeConstraint`s (bare string trait names) to `ResolvedConstraint`s
/// using the trait registry to look up the full `TraitName`.
// TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
// Validation deferred to instance resolution phase.
fn resolve_constraints(
    constraints: &[TypeConstraint],
    trait_registry: &TraitRegistry,
    module_path: &str,
) -> Result<Vec<ResolvedConstraint>, SpannedTypeError> {
    constraints
        .iter()
        .map(|tc| {
            let tv_names = require_param_vars(tc)?;
            Ok(ResolvedConstraint {
                trait_name: trait_registry
                    .lookup_trait_by_name(&tc.trait_name)
                    .map(|ti| ti.trait_name())
                    .unwrap_or_else(|| {
                        TraitName::new(module_path.to_string(), tc.trait_name.clone())
                    }),
                type_vars: tv_names.iter().map(|s| s.to_string()).collect(),
                span: tc.span,
            })
        })
        .collect()
}

/// Phase 5: Process DefImpl declarations (register instances).
fn register_impl_instances(
    state: &mut ModuleInferenceState,
    trait_registry: &mut TraitRegistry,
    module: &Module,
    module_path: &str,
) -> Result<(), SpannedTypeError> {
    // Collect locally-defined trait names for orphan check
    let local_trait_names: HashSet<String> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefTrait { name, .. } => Some(name.clone()),
            // Extern traits (`extern java "..." as trait Foo[a]`) are local trait definitions
            // and should be treated as such for the orphan check.
            Decl::Extern {
                is_trait: true,
                alias: Some(name),
                ..
            } => Some(name.clone()),
            _ => None,
        })
        .collect();

    // Process DefImpl declarations (register instances)
    for decl in &module.decls {
        if let Decl::DefImpl {
            trait_name,
            type_args,
            type_params,
            type_constraints,
            methods,
            span,
            ..
        } = decl
        {
            // Compute total wildcard count across all type args.
            let mut wildcard_count = 0usize;
            for arg in type_args {
                wildcard_count += validate_impl_wildcards(arg).map_err(|e| spanned(e, *span))?;
            }

            let type_param_map: HashMap<String, TypeVarId> = if !type_params.is_empty() {
                type_params
                    .iter()
                    .map(|tp| (tp.name.clone(), state.gen.fresh()))
                    .collect()
            } else {
                let mut impl_type_param_names = HashSet::new();
                for arg in type_args {
                    collect_type_expr_var_names(arg, &mut impl_type_param_names);
                }
                for constraint in type_constraints {
                    let tv_names = require_param_vars(constraint)?;
                    for n in tv_names {
                        impl_type_param_names.insert(n.to_string());
                    }
                }
                let mut sorted_names: Vec<_> = impl_type_param_names.into_iter().collect();
                sorted_names.sort();
                sorted_names
                    .into_iter()
                    .map(|name| (name, state.gen.fresh()))
                    .collect()
            };
            let type_param_arity: HashMap<String, usize> = HashMap::new();

            // Resolve each type argument into a concrete `Type`.
            let mut resolved_targets: Vec<Type> = Vec::with_capacity(type_args.len());
            for arg in type_args {
                let arg_wildcards = validate_impl_wildcards(arg).map_err(|e| spanned(e, *span))?;
                let resolved = if arg_wildcards > 0 {
                    resolve_impl_target(
                        arg,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        &mut state.gen,
                    )
                    .map_err(|e| spanned(e, *span))?
                } else {
                    type_registry::resolve_type_expr(
                        arg,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, *span))?
                };
                resolved_targets.push(resolved);
            }

            // D.2: reject `impl Disposable[<fn type>]` before orphan/well-formedness
            // so the user sees a targeted diagnostic. `~fn` is structurally Linear
            // and consumed by calling it; no separate `dispose` step exists.
            if trait_name == "Disposable" {
                for rt in &resolved_targets {
                    let inner = match rt {
                        Type::Own(inner) => inner.as_ref(),
                        other => other,
                    };
                    if matches!(inner, Type::Fn(_, _)) {
                        return Err(spanned(
                            TypeError::InvalidDisposableInstance {
                                ty: format!("{}", rt),
                            },
                            *span,
                        ));
                    }
                }
            }

            // Classify each arg for orphan checking: determine whether the arg's
            // head-type is locally defined, and collect a list of modules that
            // were consulted so we can report them in a helpful error message.
            let trait_is_local = local_trait_names.contains(trait_name);
            let mut any_arg_is_local = false;
            let mut modules_checked: Vec<String> = Vec::new();
            if trait_is_local {
                modules_checked.push(module_path.to_string());
                any_arg_is_local = true; // trait locality alone satisfies the rule
            }
            // Also validate well-formedness per arg (unknown type, owned type).
            for rt in &resolved_targets {
                match rt {
                    Type::Named(name, _) => {
                        if state.registry.lookup_type(name).is_none() {
                            return Err(spanned(
                                TypeError::OrphanInstance {
                                    trait_name: trait_name.clone(),
                                    ty: name.clone(),
                                    modules_checked: modules_checked.clone(),
                                },
                                *span,
                            ));
                        }
                        if let Some((src, _)) = state.imports.imported_type_info.get(name) {
                            modules_checked.push(src.clone());
                        } else {
                            modules_checked.push(module_path.to_string());
                            any_arg_is_local = true;
                        }
                    }
                    Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit => {
                        modules_checked.push("<builtin>".to_string());
                    }
                    Type::Fn(_, _) | Type::Tuple(_) => {
                        // Fn / Tuple types are structural — they have no defining
                        // module and cannot satisfy the orphan rule on their own.
                        modules_checked.push("<structural>".to_string());
                    }
                    Type::Var(_) => {
                        // Type parameters carry no locality information.
                    }
                    Type::Own(inner) => {
                        return Err(spanned(
                            TypeError::OwnedTypeImpl {
                                trait_name: trait_name.clone(),
                                ty: format!("{}", inner),
                            },
                            *span,
                        ));
                    }
                    other => {
                        return Err(spanned(
                            TypeError::OrphanInstance {
                                trait_name: trait_name.clone(),
                                ty: format!("{}", other),
                                modules_checked: modules_checked.clone(),
                            },
                            *span,
                        ));
                    }
                }
            }

            // Final orphan check: either the trait is local, or at least one type
            // argument has its head type defined locally.
            let joined_display = {
                let names: std::collections::HashMap<crate::types::TypeVarId, &str> =
                    type_param_map
                        .iter()
                        .map(|(n, &id)| (id, n.as_str()))
                        .collect();
                resolved_targets
                    .iter()
                    .map(|rt| {
                        if type_param_map.is_empty() {
                            format!("{}", rt.renumber_for_display())
                        } else {
                            crate::types::format_type_with_var_map(rt, &names)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            if !trait_is_local && !any_arg_is_local {
                return Err(spanned(
                    TypeError::OrphanInstance {
                        trait_name: trait_name.clone(),
                        ty: joined_display.clone(),
                        modules_checked: modules_checked.clone(),
                    },
                    *span,
                ));
            }

            // Compute `target_name` for KindMismatch and InvalidImpl error messages
            // (still keyed on the first type argument for single-HK traits).
            let target_name = match &resolved_targets[0] {
                Type::Named(name, _) => name.clone(),
                Type::Int => "Int".to_string(),
                Type::Float => "Float".to_string(),
                Type::Bool => "Bool".to_string(),
                Type::String => "String".to_string(),
                Type::Unit => "Unit".to_string(),
                _ => format!("{}", resolved_targets[0]),
            };
            let target_display_name = joined_display.clone();

            for constraint in type_constraints {
                if trait_registry
                    .lookup_trait_by_name(&constraint.trait_name)
                    .is_none()
                {
                    return Err(spanned(
                        TypeError::UnknownTrait {
                            name: constraint.trait_name.clone(),
                        },
                        constraint.span,
                    ));
                }
            }

            if let Some(trait_info) = trait_registry.lookup_trait_by_name(trait_name) {
                let expected_arity = trait_info.type_var_arity;
                if expected_arity > 0 {
                    if wildcard_count > 0 {
                        if wildcard_count != expected_arity {
                            return Err(spanned(
                                TypeError::KindMismatch {
                                    type_name: target_name.clone(),
                                    expected_arity,
                                    actual_arity: wildcard_count,
                                },
                                *span,
                            ));
                        }
                    } else {
                        let actual_arity = state.registry.expected_arity(&target_name).unwrap_or(0);
                        if actual_arity != expected_arity {
                            return Err(spanned(
                                TypeError::KindMismatch {
                                    type_name: target_name.clone(),
                                    expected_arity,
                                    actual_arity,
                                },
                                *span,
                            ));
                        }
                    }
                }

                let expected_methods: HashSet<&str> =
                    trait_info.methods.iter().map(|m| m.name.as_str()).collect();
                let actual_methods: HashSet<&str> =
                    methods.iter().map(|m| m.name.as_str()).collect();
                let missing_methods: Vec<String> = trait_info
                    .methods
                    .iter()
                    .filter(|m| !actual_methods.contains(m.name.as_str()))
                    .map(|m| m.name.clone())
                    .collect();
                let extra_methods: Vec<String> = methods
                    .iter()
                    .filter(|m| !expected_methods.contains(m.name.as_str()))
                    .map(|m| m.name.clone())
                    .collect();
                if !missing_methods.is_empty() || !extra_methods.is_empty() {
                    return Err(spanned_with_names(
                        TypeError::InvalidImpl {
                            trait_name: trait_name.clone(),
                            target_type: target_display_name.clone(),
                            missing_methods,
                            extra_methods,
                        },
                        *span,
                        &type_param_map,
                    ));
                }
            }

            let target_type_name = resolved_targets
                .iter()
                .map(type_to_canonical_name)
                .collect::<Vec<_>>()
                .join("$$");
            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
            // Validation deferred to instance resolution phase.
            let impl_full_trait_name = trait_registry
                .lookup_trait_by_name(trait_name)
                .map(|ti| ti.trait_name())
                .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));
            let resolved_constraints =
                resolve_constraints(type_constraints, trait_registry, module_path)?;
            let instance = InstanceInfo {
                trait_name: impl_full_trait_name,
                target_types: resolved_targets,
                target_type_name,
                type_var_ids: type_param_map.clone(),
                constraints: resolved_constraints,
                span: *span,
                is_builtin: false,
            };

            trait_registry
                .check_superclasses(&instance)
                .map_err(|e| spanned(e, *span))?;

            trait_registry
                .register_instance(instance)
                .map_err(|boxed| {
                    let (e, existing_span) = *boxed;
                    duplicate_instance_spanned(e, *span, existing_span)
                })?;
        }
    }
    Ok(())
}

fn resolve_fn_param_types_for_overlap(f: &FnDecl, registry: &TypeRegistry) -> Option<Vec<Type>> {
    let type_exprs: Vec<&krypton_parser::ast::TypeExpr> = f
        .params
        .iter()
        .map(|p| p.ty.as_ref())
        .collect::<Option<Vec<_>>>()?;

    let mut gen = TypeVarGen::new();
    let mut type_param_map = HashMap::new();
    let mut type_param_arity = HashMap::new();
    for tp in &f.type_params {
        let id = gen.fresh();
        type_param_map.insert(tp.name.clone(), id);
        type_param_arity.insert(tp.name.clone(), tp.arity);
    }

    let mut types = Vec::new();
    for texpr in type_exprs {
        match type_registry::resolve_type_expr(
            texpr,
            &type_param_map,
            &type_param_arity,
            registry,
            ResolutionContext::UserAnnotation,
            None,
        ) {
            Ok(ty) => types.push(ty),
            Err(_) => return None,
        }
    }
    Some(types)
}

fn trait_method_param_types(
    trait_registry: &TraitRegistry,
    trait_name: &TraitName,
    method_name: &str,
) -> Option<Vec<Type>> {
    let info = trait_registry.lookup_trait(trait_name)?;
    let method = info.methods.iter().find(|m| m.name == method_name)?;
    Some(method.param_types.iter().map(|(_, ty)| ty.clone()).collect())
}

/// Phase 6: Check for trait method name conflicts and reserved name usage.
fn check_trait_name_conflicts(
    module: &Module,
    trait_method_map: &HashMap<String, TraitName>,
    trait_registry: &TraitRegistry,
    type_registry: &TypeRegistry,
    is_core_module: bool,
) -> Result<(), SpannedTypeError> {
    // Check for top-level def names conflicting with trait method names
    {
        let has_trait_usage = module
            .decls
            .iter()
            .any(|d| matches!(d, Decl::DefTrait { .. } | Decl::DefImpl { .. }))
            || module.decls.iter().any(|d| {
                if let Decl::DefType(td) = d {
                    !td.deriving.is_empty()
                } else {
                    false
                }
            });

        let mut user_trait_methods: HashMap<String, (String, Span)> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefTrait { name, methods, .. } = decl {
                for method in methods {
                    user_trait_methods.insert(method.name.clone(), (name.clone(), method.span));
                }
            }
        }
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if let Some((trait_name, method_span)) = user_trait_methods.get(&f.name) {
                    // Try overlap check: resolve free fn params and trait method params
                    let should_error = if let Some(fn_params) = resolve_fn_param_types_for_overlap(f, type_registry) {
                        if let Some(trait_info) = trait_registry.lookup_trait_by_name(trait_name) {
                            if let Some(method) = trait_info.methods.iter().find(|m| m.name == f.name) {
                                let method_params: Vec<Type> = method.param_types.iter().map(|(_, ty)| ty.clone()).collect();
                                if fn_params.len() != method_params.len() {
                                    true // arity mismatch
                                } else {
                                    types_overlap(&fn_params, &method_params)
                                }
                            } else {
                                true
                            }
                        } else {
                            true
                        }
                    } else {
                        true // unannotated → can't prove non-overlap
                    };
                    if should_error {
                        return Err(SpannedTypeError {
                            error: Box::new(TypeError::DefinitionConflictsWithTraitMethod {
                                def_name: f.name.clone(),
                                trait_name: trait_name.clone(),
                            }),
                            span: f.span,
                            note: None,
                            secondary_span: Some(Box::new(crate::unify::SecondaryLabel {
                                span: *method_span,
                                message: "trait method defined here".into(),
                                source_file: None,
                            })),
                            source_file: None,
                            var_names: None,
                        });
                    }
                }
                if !user_trait_methods.contains_key(&f.name) && has_trait_usage {
                    if let Some(trait_id) = trait_method_map.get(&f.name) {
                        // Try overlap check for imported trait method
                        let should_error = if let Some(fn_params) = resolve_fn_param_types_for_overlap(f, type_registry) {
                            if let Some(method_params) = trait_method_param_types(trait_registry, trait_id, &f.name) {
                                if fn_params.len() != method_params.len() {
                                    true // arity mismatch
                                } else {
                                    types_overlap(&fn_params, &method_params)
                                }
                            } else {
                                true
                            }
                        } else {
                            true // unannotated → can't prove non-overlap
                        };
                        if should_error {
                            return Err(SpannedTypeError {
                                error: Box::new(TypeError::DefinitionConflictsWithTraitMethod {
                                    def_name: f.name.clone(),
                                    trait_name: trait_id.local_name.clone(),
                                }),
                                span: f.span,
                                note: None,
                                secondary_span: None,
                                source_file: None,
                                var_names: None,
                            });
                        }
                    }
                }
            }
        }
    }

    // Reject user-defined functions with reserved __krypton_ prefix
    if !is_core_module {
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if f.name.starts_with("__krypton_") {
                    return Err(spanned(
                        TypeError::ReservedName {
                            name: f.name.clone(),
                        },
                        f.span,
                    ));
                }
            }
        }
    }

    Ok(())
}

/// Phase: SCC-based function body inference.
/// Returns (fn_decls, result_schemes, fn_bodies, fn_constraint_requirements).
///
/// Extracted from `infer_module_inner` so that earlier phase locals are deallocated
/// before the deep `infer_expr_inner` recursion.
fn infer_function_bodies<'a>(
    state: &mut ModuleInferenceState,
    module: &'a Module,
    _extern_fns: &[ExternFnInfo],
    trait_registry: &TraitRegistry,
    trait_method_map: &HashMap<String, TraitName>,
    mod_path: &str,
) -> Result<InferFunctionBodiesResult<'a>, SpannedTypeError> {
    let fn_decls: Vec<&krypton_parser::ast::FnDecl> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::DefFn(f) => Some(f),
            _ => None,
        })
        .collect();

    // Check that pub functions have full type annotations
    for decl in &fn_decls {
        if matches!(decl.visibility, Visibility::Pub) {
            let mut missing = Vec::new();
            for p in &decl.params {
                if p.ty.is_none() {
                    missing.push(format!("parameter `{}`", p.name));
                }
            }
            if decl.return_type.is_none() {
                missing.push("return type".to_string());
            }
            if !missing.is_empty() {
                return Err(spanned(
                    TypeError::MissingPubAnnotation {
                        fn_name: decl.name.clone(),
                        missing,
                    },
                    decl.span,
                ));
            }
        }
    }

    let adj = scc::build_dependency_graph(&fn_decls);
    let sccs = scc::tarjan_scc(&adj);

    let mut result_schemes: Vec<Option<TypeScheme>> = vec![None; fn_decls.len()];
    let mut fn_bodies: Vec<Option<TypedExpr>> = vec![None; fn_decls.len()];
    let mut fn_constraint_requirements: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> =
        HashMap::new();
    let mut saved_type_param_maps: HashMap<usize, HashMap<String, TypeVarId>> = HashMap::new();

    for component in &sccs {
        let mut deferred_overloads: Vec<expr::DeferredOverload> = Vec::new();
        let mut pre_bound: Vec<(usize, Type)> = Vec::new();
        for &idx in component {
            let tv = Type::Var(state.gen.fresh());
            state.env.bind_top_level_function(
                fn_decls[idx].name.clone(),
                TypeScheme::mono(tv.clone()),
                mod_path.to_string(),
                fn_decls[idx].name.clone(),
            );
            pre_bound.push((idx, tv));
        }

        let qual_snap = state.subst.push_qual_scope();
        let scc_result: Result<(), SpannedTypeError> = (|| {
            for &(idx, ref tv) in &pre_bound {
                let decl = fn_decls[idx];
                state.env.push_scope();

                let (type_param_map, type_param_arity) =
                    build_type_param_maps(&decl.type_params, &mut state.gen);
                saved_type_param_maps.insert(idx, type_param_map.clone());
                if !decl.constraints.is_empty() {
                    for constraint in &decl.constraints {
                        if trait_registry
                            .lookup_trait_by_name(&constraint.trait_name)
                            .is_none()
                        {
                            return Err(spanned(
                                TypeError::UnknownTrait {
                                    name: constraint.trait_name.clone(),
                                },
                                constraint.span,
                            ));
                        }
                    }

                    let requirements: Vec<(TraitName, Vec<TypeVarId>)> = decl
                        .constraints
                        .iter()
                        .map(|constraint| {
                            let tv_names = require_param_vars(constraint)?;
                            let tvs: Vec<TypeVarId> = tv_names
                                .iter()
                                .filter_map(|n| type_param_map.get(*n).copied())
                                .collect();
                            if tvs.len() != tv_names.len() || tvs.is_empty() {
                                return Ok(None);
                            }
                            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
                            // Validation deferred to instance resolution phase.
                            let tn = trait_registry
                                .lookup_trait_by_name(&constraint.trait_name)
                                .map(|ti| ti.trait_name())
                                .unwrap_or_else(|| {
                                    TraitName::new(
                                        mod_path.to_string(),
                                        constraint.trait_name.clone(),
                                    )
                                });
                            Ok(Some((tn, tvs)))
                        })
                        .collect::<Result<Vec<Option<_>>, SpannedTypeError>>()?
                        .into_iter()
                        .flatten()
                        .collect();
                    if !requirements.is_empty() {
                        fn_constraint_requirements.insert(decl.name.clone(), requirements);
                    }
                }

                let mut seen_params = HashSet::new();
                for p in &decl.params {
                    if !seen_params.insert(&p.name) {
                        return Err(spanned(
                            TypeError::DuplicateParam {
                                name: p.name.clone(),
                            },
                            p.span,
                        ));
                    }
                }

                let mut param_types = Vec::new();
                for p in &decl.params {
                    let ptv = Type::Var(state.gen.fresh());
                    if let Some(ref ty_expr) = p.ty {
                        let annotated_ty = type_registry::resolve_type_expr(
                            ty_expr,
                            &type_param_map,
                            &type_param_arity,
                            &state.registry,
                            ResolutionContext::UserAnnotation,
                            None,
                        )
                        .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                        .map_err(|e| spanned(e, decl.span))?;
                        // E0109: Consume-mode params with a bare
                        // resource-carrying type must be spelled `~T`.
                        // Borrow modes encode `&` via the mode, not the
                        // type, so the bare spelling is legal there.
                        if matches!(p.mode, crate::types::ParamMode::Consume) {
                            crate::ownership::check_no_bare_resource_use(
                                &annotated_ty,
                                &state.registry,
                                ty_expr.span(),
                                crate::type_error::BareResourceContext::ParamConsume,
                            )?;
                        }
                        unify(&ptv, &annotated_ty, &mut state.subst)
                            .map_err(|e| spanned(e, decl.span))?;
                    }
                    param_types.push(ptv.clone());
                    state.env.bind(p.name.clone(), TypeScheme::mono(ptv));
                }
                let prev_fn_return_type = state.env.fn_return_type.take();
                if let Some(ref ret_ty_expr) = decl.return_type {
                    let resolved_ret = type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, decl.span))?;
                    // E0109: return types are always value positions.
                    crate::ownership::check_no_bare_resource_use(
                        &resolved_ret,
                        &state.registry,
                        ret_ty_expr.span(),
                        crate::type_error::BareResourceContext::Return,
                    )?;
                    state.env.fn_return_type = Some(resolved_ret);
                } else {
                    state.env.fn_return_type = Some(Type::Var(state.gen.fresh()));
                }

                let body_typed = {
                    // Clone the resolved return type so we can pass it as the
                    // bidirectional `expected_type` to the body inference without
                    // keeping an immutable borrow of state.env alongside the
                    // mutable borrow that InferenceContext requires.
                    let fn_ret_expected = state.env.fn_return_type.clone();
                    let mut ctx = InferenceContext {
                        env: &mut state.env,
                        subst: &mut state.subst,
                        gen: &mut state.gen,
                        registry: Some(&state.registry),
                        recur_params: Some(
                            decl.params
                                .iter()
                                .zip(&param_types)
                                .map(|(p, t)| (p.mode, t.clone()))
                                .collect(),
                        ),
                        let_own_spans: Some(&mut state.let_own_spans),
                        lambda_own_captures: Some(&mut state.lambda_own_captures),
                        type_param_map: &type_param_map,
                        type_param_arity: &type_param_arity,
                        qualified_modules: &state.qualified_modules,
                        imported_type_info: &state.imports.imported_type_info,
                        module_path: mod_path,
                        shadowed_prelude_fns: &state.imports.shadowed_prelude_fns,
                        self_type: None,
                        deferred_overloads: &mut deferred_overloads,
                        owning_fn_idx: idx,
                    };
                    ctx.infer_expr_inner(&decl.body, fn_ret_expected.as_ref())?
                };
                state.env.fn_return_type = prev_fn_return_type;
                state.env.pop_scope();

                let param_types: Vec<Type> = param_types.iter().enumerate().map(|(i, t)| {
                let resolved = state.subst.apply(t);
                debug_assert!(
                    !matches!(&resolved, Type::Own(ref inner) if matches!(inner.as_ref(), Type::Own(_))),
                    "Own(Own(_)) should never arise — parser rejects ~~T and no codepath double-wraps: param '{}': {:?}",
                    decl.params.get(i).map(|p| p.name.as_str()).unwrap_or("?"),
                    resolved,
                );
                resolved
            }).collect();
                let body_ty = state.subst.apply(&body_typed.ty);

                let ret_ty = if let Some(ref ret_ty_expr) = decl.return_type {
                    let annotated_ret = type_registry::resolve_type_expr(
                        ret_ty_expr,
                        &type_param_map,
                        &type_param_arity,
                        &state.registry,
                        ResolutionContext::UserAnnotation,
                        None,
                    )
                    .map_err(|e| e.enrich_unknown_type_with_env(&state.env))
                    .map_err(|e| spanned(e, decl.span))?;
                    coerce_unify(&body_ty, &annotated_ret, &mut state.subst, Some(&state.registry)).map_err(|e| {
                        if let TypeError::InfiniteType { ref var, ref ty } = e {
                            if crate::type_error::is_own_wrapper_of(*var, ty) {
                                let var_names: Vec<(TypeVarId, String)> = type_param_map
                                    .iter()
                                    .map(|(name, &id)| (id, name.clone()))
                                    .collect();
                                let body_span = match &body_typed.kind {
                                    crate::typed_ast::TypedExprKind::Do(exprs) => {
                                        exprs.last().map_or(body_typed.span, |e| e.span)
                                    }
                                    _ => body_typed.span,
                                };
                                return SpannedTypeError {
                                    error: Box::new(e),
                                    span: body_span,
                                    note: None,
                                    secondary_span: Some(Box::new(SecondaryLabel {
                                        span: ret_ty_expr.span(),
                                        message: "return type declared here".to_string(),
                                        source_file: None,
                                    })),
                                    source_file: None,
                                    var_names: Some(var_names),
                                };
                            }
                        }
                        let mut err = spanned(e, decl.span);
                        if matches!(
                            &*err.error,
                            TypeError::Mismatch { .. }
                                | TypeError::FnCapabilityMismatch { .. }
                                | TypeError::ParamModeMismatch { .. }
                        ) {
                            let terminal = match &body_typed.kind {
                                crate::typed_ast::TypedExprKind::Do(exprs) => {
                                    exprs.last().unwrap_or(&body_typed)
                                }
                                _ => &body_typed,
                            };
                            if let crate::typed_ast::TypedExprKind::Lambda { .. } = &terminal.kind {
                                if let Some(cap_name) =
                                    state.lambda_own_captures.get(&terminal.span)
                                {
                                    err.note = Some(format!(
                                        "closure is single-use because it captures `~` value `{}`",
                                        cap_name
                                    ));
                                }
                            }
                        }
                        err
                    })?;
                    state.subst.apply(&annotated_ret)
                } else {
                    // Preserve `Own` in inferred return types — a body that produces
                    // `~T` should yield a `-> ~T` function. The previous `strip_own`
                    // here silently dropped ownership for inferred returns.
                    body_ty.clone()
                };

                // Use join_types (not unify) to reconcile the inferred fn type with the pre-bound
                // SCC type. This is not a value flow — it's two views of the same function that may
                // differ in Own wrappers (e.g. body infers Int, recursive call bound ~Int from literals).
                let fn_params: Vec<(crate::types::ParamMode, Type)> = decl
                    .params
                    .iter()
                    .zip(param_types.into_iter())
                    .map(|(p, t)| (p.mode, t))
                    .collect();
                let fn_ty = Type::Fn(fn_params, Box::new(ret_ty.clone()));
                crate::unify::join_types(&fn_ty, tv, &mut state.subst, Some(&state.registry))
                    .map_err(|e| spanned(e, decl.span))?;

                fn_bodies[idx] = Some(body_typed);
            }
            Ok(())
        })();
        match &scc_result {
            Ok(()) => state.subst.commit_qual_scope(qual_snap),
            Err(_) => state.subst.rollback_qual_scope(qual_snap),
        }
        scc_result?;

        // Eagerly resolve multi-parameter trait method calls before
        // generalization. Pinning secondary trait params (e.g. `?b = String`)
        // here ensures they don't get quantified into a function's scheme.
        //
        // Build the per-function set of "protected" type vars — the vars
        // bound by each function's declared `[a, b, ...]` type parameters.
        // These must stay abstract through generalization so declared
        // `where` constraints on polymorphic functions are forwarded to
        // callers rather than eagerly pinned to a matching instance.
        let protected_type_vars: Vec<HashSet<TypeVarId>> = (0..fn_bodies.len())
            .map(|idx| {
                saved_type_param_maps
                    .get(&idx)
                    .map(|m| m.values().copied().collect())
                    .unwrap_or_default()
            })
            .collect();
        resolve_multi::resolve_multi_param_constraints(
            &fn_bodies,
            &protected_type_vars,
            trait_registry,
            &mut state.subst,
            &mut state.gen,
        );

        resolve_overloads::resolve_deferred_overloads(
            &mut deferred_overloads,
            &mut fn_bodies,
            &mut state.subst,
            &mut state.gen,
        )?;

        // Generalize against an empty env: all env bindings are either fully-quantified
        // schemes (no free vars) or current-SCC monomorphic bindings whose vars should be
        // generalized. This must change if nested let-polymorphism is added.
        let empty_env = TypeEnv::new();
        for &(idx, ref tv) in &pre_bound {
            let final_ty = state.subst.apply(tv);
            let mut scheme = generalize(&final_ty, &empty_env, &state.subst);
            if let Some(tpm) = saved_type_param_maps.get(&idx) {
                let scheme_var_set: HashSet<TypeVarId> = scheme.vars.iter().copied().collect();
                for (name, &original_id) in tpm {
                    let resolved = state.subst.apply(&Type::Var(original_id));
                    if let Type::Var(final_id) = resolved {
                        if scheme_var_set.contains(&final_id) {
                            scheme.var_names.insert(final_id, name.clone());
                        }
                    }
                }
            }
            let local_source = BindingSource::TopLevelLocalFunction {
                qualified_name: crate::types::BindingQualifiedName {
                    module_path: mod_path.to_string(),
                    local_name: fn_decls[idx].name.clone(),
                },
            };
            let fn_name = fn_decls[idx].name.clone();
            // Check if this name has multiple definitions in this SCC or
            // already has overload candidates (from imports).
            let is_overloaded = pre_bound.iter().filter(|(i, _)| fn_decls[*i].name == fn_name).count() > 1
                || state.env.lookup_entry(&fn_name).is_some_and(|e| e.overload_candidates.is_some());
            if is_overloaded {
                if let Some(existing) = state.env.lookup_entry_mut(&fn_name) {
                    existing.add_overload_candidate(scheme.clone(), local_source);
                } else {
                    state.env.bind_with_source_and_def_span(
                        fn_name,
                        scheme.clone(),
                        local_source,
                        crate::types::DefSpan {
                            span: fn_decls[idx].span,
                            source_module: None,
                        },
                    );
                }
            } else {
                state.env.bind_with_source_and_def_span(
                    fn_name,
                    scheme.clone(),
                    local_source,
                    crate::types::DefSpan {
                        span: fn_decls[idx].span,
                        source_module: None,
                    },
                );
            }
            result_schemes[idx] = Some(scheme);
        }
    }

    // Normalize fn_constraint_requirements
    for requirements in fn_constraint_requirements.values_mut() {
        for (_, type_vars) in requirements.iter_mut() {
            for type_var in type_vars.iter_mut() {
                let resolved = state.subst.apply(&Type::Var(*type_var));
                if let Type::Var(new_id) = resolved {
                    *type_var = new_id;
                }
            }
        }
    }

    // Fold constraints into TypeSchemes so they propagate via normal import mechanisms
    for (idx, decl) in fn_decls.iter().enumerate() {
        if let Some(scheme) = &mut result_schemes[idx] {
            if let Some(reqs) = fn_constraint_requirements.get(&decl.name) {
                scheme.constraints = reqs.clone();
            }
        }
    }

    // Validate explicit trait bounds: fn_decl bodies must not use trait methods on type vars
    // unless the corresponding bound is declared in a `where` clause.
    for (idx, decl) in fn_decls.iter().enumerate() {
        if let Some(body) = &fn_bodies[idx] {
            let mut fn_type_param_vars: HashSet<TypeVarId> = HashSet::new();
            if let Some(scheme) = &result_schemes[idx] {
                if let Type::Fn(param_types, ret_ty) = &scheme.ty {
                    for (_, pty) in param_types.iter() {
                        for v in free_vars(pty) {
                            fn_type_param_vars.insert(v);
                        }
                    }
                    for v in free_vars(ret_ty) {
                        fn_type_param_vars.insert(v);
                    }
                }
            }
            if fn_type_param_vars.is_empty() {
                continue;
            }
            // Functions without explicit constraints have no entry
            let declared = fn_constraint_requirements
                .get(decl.name.as_str())
                .cloned()
                .unwrap_or_default();
            // Functions without explicit constraints have no entry
            let type_var_names: HashMap<TypeVarId, String> = saved_type_param_maps
                .get(&idx)
                .map(|tpm| tpm.iter().map(|(name, &id)| (id, name.clone())).collect())
                .unwrap_or_default();
            checks::validate_trait_constraints(
                body,
                trait_registry,
                &state.subst,
                &fn_type_param_vars,
                &declared,
                &decl.name,
                &type_var_names,
            )?;
        }
    }

    // Post-inference instance resolution
    // Build fn_schemes map for bind_type_vars resolution (constraints are in TypeSchemes)
    let mut fn_schemes_map: HashMap<String, TypeScheme> = HashMap::new();
    for (decl, scheme) in fn_decls.iter().zip(result_schemes.iter()) {
        if let Some(scheme) = scheme {
            fn_schemes_map.insert(decl.name.clone(), scheme.clone());
        }
    }
    for imp in &state.imports.imported_fn_types {
        fn_schemes_map
            .entry(imp.name.clone())
            .or_insert_with(|| imp.scheme.clone());
    }
    let has_constraints = fn_schemes_map.values().any(|s| !s.constraints.is_empty());
    if !trait_method_map.is_empty() || has_constraints {
        for (body, scheme) in fn_bodies.iter().zip(result_schemes.iter()) {
            if let Some(body) = body {
                // Monomorphic functions have no type variables
                let fn_type_vars: HashSet<TypeVarId> = scheme
                    .as_ref()
                    .map(|s| s.vars.iter().copied().collect())
                    .unwrap_or_default();
                // Monomorphic functions have no type variables
                let scheme_var_names = scheme
                    .as_ref()
                    .map(|s| &s.var_names)
                    .cloned()
                    .unwrap_or_default();
                checks::check_trait_instances(
                    body,
                    trait_registry,
                    &state.subst,
                    &fn_schemes_map,
                    &fn_type_vars,
                    &scheme_var_names,
                )?;
            }
        }
    }

    Ok((
        fn_decls,
        result_schemes,
        fn_bodies,
        fn_constraint_requirements,
    ))
}

/// Phase: Type-check impl method bodies and produce InstanceDefInfo.
///
/// Extracted from `infer_module_inner` to reduce stack frame size.
fn typecheck_impl_methods(
    state: &mut ModuleInferenceState,
    module: &Module,
    module_path: &str,
    trait_registry: &TraitRegistry,
    _trait_method_map: &HashMap<String, TraitName>,
    _extern_fns: &[ExternFnInfo],
) -> Result<Vec<InstanceDefInfo>, SpannedTypeError> {
    let mut instance_defs: Vec<InstanceDefInfo> = Vec::new();

    for decl in &module.decls {
        if let Decl::DefImpl {
            trait_name,
            type_args: _,
            methods,
            span,
            ..
        } = decl
        {
            let trait_info = trait_registry.lookup_trait_by_name(trait_name).unwrap();
            let impl_trait_name = trait_info.trait_name();
            let tv_id = trait_info.type_var_id;

            let instance = trait_registry
                .find_instance_by_trait_and_span(&impl_trait_name, *span)
                .unwrap();
            // For HKT partial application, strip anonymous type var args from the
            // target type so it acts as a partial constructor for substitution.
            // e.g., Named("Result", [Var(e), Var(anon)]) → Named("Result", [Var(e)])
            //
            // Non-HK multi-param traits (e.g. `Convert[a, b]`) also hit this path:
            // we take position 0 as the primary dispatch type and rely on the
            // dictionary-passing layer to carry the full tuple. The additional
            // positions are not consulted here because trait method substitution
            // only ever binds the primary type variable. Multi-parameter HK traits
            // (arity > 0 **and** more than one target type) are not expressible in
            // current Krypton.
            debug_assert!(
                !(trait_info.type_var_arity > 0 && instance.target_types.len() > 1),
                "multi-parameter HK trait method resolution not yet supported \
                 (trait {}, instance has {} target types)",
                trait_name,
                instance.target_types.len()
            );
            let resolved_target = if trait_info.type_var_arity > 0 {
                strip_anon_type_args(&instance.target_types[0], &instance.type_var_ids)
            } else {
                instance.target_types[0].clone()
            };
            let target_type_name = instance.target_type_name.clone();

            let mut instance_methods = Vec::new();

            let all_intrinsic = methods.iter().all(|m| {
                matches!(&*m.body, Expr::App { func, args, .. }
                    if args.is_empty() && matches!(func.as_ref(), Expr::Var { name, .. } if name == "__krypton_intrinsic"))
            });

            for method in methods {
                let trait_method = trait_info
                    .methods
                    .iter()
                    .find(|m| m.name == method.name)
                    .unwrap();

                // Shape-polymorphic dual-check: when a trait method signature
                // mentions `shape a`, the impl body must typecheck for every
                // legal value form of `a` (plain and owned). Collect the shape
                // variables — both the trait primary (`tv_id`) and any
                // secondary trait / method vars that appear inside a `Shape(_)`
                // wrapper — so we can enumerate forks below.
                let shape_vars: Vec<TypeVarId> = {
                    let mut out: Vec<TypeVarId> = Vec::new();
                    let mut seen: HashSet<TypeVarId> = HashSet::new();
                    for (_, pt) in &trait_method.param_types {
                        for v in crate::types::collect_shape_vars(pt) {
                            if seen.insert(v) {
                                out.push(v);
                            }
                        }
                    }
                    for v in crate::types::collect_shape_vars(&trait_method.return_type) {
                        if seen.insert(v) {
                            out.push(v);
                        }
                    }
                    out
                };

                // For each shape variable, determine its candidate bindings.
                // tv_id defaults to `resolved_target` when concrete; otherwise
                // the trait primary is free and we fork on (plain, owned).
                // Non-tv_id shape vars (secondary trait vars or method vars
                // appearing in shape positions) always fork on (plain, owned).
                #[derive(Clone)]
                enum ShapeCandidate {
                    Concrete(Type),
                    Plain,
                    Owned,
                }
                let resolved_target_is_concrete = free_vars(&resolved_target).is_empty();
                let mut per_var_candidates: Vec<(TypeVarId, Vec<ShapeCandidate>)> = Vec::new();
                for &sv in &shape_vars {
                    if sv == tv_id && resolved_target_is_concrete {
                        per_var_candidates
                            .push((sv, vec![ShapeCandidate::Concrete(resolved_target.clone())]));
                    } else {
                        per_var_candidates
                            .push((sv, vec![ShapeCandidate::Plain, ShapeCandidate::Owned]));
                    }
                }

                // Cartesian product over shape var candidate sets. Empty shape
                // vars means a single fork with no overrides; all shape vars
                // concrete mono gives a single fork too — both reuse the
                // existing single-check code path.
                let mut combos: Vec<Vec<(TypeVarId, ShapeCandidate)>> = vec![vec![]];
                for (sv, cands) in &per_var_candidates {
                    let mut next: Vec<Vec<(TypeVarId, ShapeCandidate)>> =
                        Vec::with_capacity(combos.len() * cands.len());
                    for c in cands {
                        for existing in &combos {
                            let mut row = existing.clone();
                            row.push((*sv, c.clone()));
                            next.push(row);
                        }
                    }
                    combos = next;
                }
                debug_assert!(combos.len() <= 64, "shape cap is 6 → at most 64 forks");

                // Track the committed fork's typed output so the post-loop
                // bookkeeping can push it into `instance_methods`. The first
                // successful fork wins; later forks are validation-only —
                // their typed ASTs are discarded and any ownership metadata
                // they wrote to `state.let_own_spans` / `state.lambda_own_captures`
                // is rolled back so the committed fork's metadata is not
                // unioned with later forks. After the loop, the committed
                // fork's captured metadata is restored.
                let mut committed: Option<ForkCommit> = None;
                let mut committed_metadata: Option<(
                    HashSet<Span>,
                    HashMap<Span, String>,
                )> = None;
                let mut dual_check_failure: Option<(String, SpannedTypeError)> = None;
                let is_multi_fork = combos.len() > 1;
                let pre_loop_let_own_spans = state.let_own_spans.clone();
                let pre_loop_lambda_own_captures = state.lambda_own_captures.clone();

                for combo in &combos {
                    // Per-fork freshening + shape-var overrides. Each fork
                    // allocates its own fresh vars so the subst map grows
                    // monotonically but fork reasoning stays independent.
                    let mut fork_overrides: HashMap<TypeVarId, Type> = HashMap::new();
                    let mut form_label_parts: Vec<String> = Vec::new();
                    let shape_var_names = &trait_info.type_var_names;
                    for (sv, cand) in combo {
                        let replacement = match cand {
                            ShapeCandidate::Concrete(t) => t.clone(),
                            ShapeCandidate::Plain => Type::Var(state.gen.fresh()),
                            ShapeCandidate::Owned => {
                                Type::Own(Box::new(Type::Var(state.gen.fresh())))
                            }
                        };
                        let name = trait_info
                            .type_var_ids
                            .iter()
                            .position(|id| id == sv)
                            .and_then(|idx| shape_var_names.get(idx).cloned())
                            .unwrap_or_else(|| format!("{}", sv));
                        let form = match cand {
                            ShapeCandidate::Concrete(t) => format!("{} = {}", name, t),
                            ShapeCandidate::Plain => format!("{} = T (plain)", name),
                            ShapeCandidate::Owned => format!("{} = ~T (owned)", name),
                        };
                        form_label_parts.push(form);
                        fork_overrides.insert(*sv, replacement);
                    }
                    // Always ensure tv_id is substituted; mono cases put it
                    // into fork_overrides directly, generic non-shape cases
                    // fall through to `resolved_target`.
                    fork_overrides
                        .entry(tv_id)
                        .or_insert_with(|| resolved_target.clone());
                    let form_label = if form_label_parts.is_empty() {
                        String::new()
                    } else {
                        form_label_parts.join(", ")
                    };

                    // Freshen trait's secondary/method vars that are NOT shape
                    // vars (those are handled above via fork_overrides).
                    let mut extra_subst: HashMap<TypeVarId, Type> = HashMap::new();
                    for (_, pt) in &trait_method.param_types {
                        for v in free_vars(pt) {
                            if v != tv_id && !fork_overrides.contains_key(&v) {
                                extra_subst
                                    .entry(v)
                                    .or_insert_with(|| Type::Var(state.gen.fresh()));
                            }
                        }
                    }
                    for v in free_vars(&trait_method.return_type) {
                        if v != tv_id && !fork_overrides.contains_key(&v) {
                            extra_subst
                                .entry(v)
                                .or_insert_with(|| Type::Var(state.gen.fresh()));
                        }
                    }
                    let fork_apply = |ty: &Type| -> Type {
                        let mut out = ty.clone();
                        for (old_id, new_ty) in &extra_subst {
                            out = substitute_type_var(&out, *old_id, new_ty);
                        }
                        for (old_id, new_ty) in &fork_overrides {
                            out = substitute_type_var(&out, *old_id, new_ty);
                        }
                        out
                    };

                    let fork_result = check_fork(
                        state,
                        module_path,
                        trait_registry,
                        trait_name,
                        method,
                        trait_method,
                        instance,
                        &resolved_target,
                        all_intrinsic,
                        *span,
                        &fork_apply,
                    );
                    match fork_result {
                        Ok(result) => {
                            if committed.is_none() && !all_intrinsic {
                                committed = Some(
                                    result.expect(
                                        "non-intrinsic check_fork must yield Some(ForkCommit)",
                                    ),
                                );
                                // Capture the committed fork's post-inference
                                // metadata so we can restore it after all
                                // validation forks finish.
                                committed_metadata = Some((
                                    state.let_own_spans.clone(),
                                    state.lambda_own_captures.clone(),
                                ));
                            }
                        }
                        Err(err_with_label) => {
                            if dual_check_failure.is_none() {
                                dual_check_failure = Some((form_label, err_with_label));
                            }
                        }
                    }
                    // Roll back to pre-loop metadata so the next fork runs
                    // against a clean slate and later forks cannot leak
                    // per-span metadata into the committed fork's AST.
                    state.let_own_spans = pre_loop_let_own_spans.clone();
                    state.lambda_own_captures = pre_loop_lambda_own_captures.clone();
                }

                // Restore the committed fork's metadata so downstream
                // ownership checking reads exactly what the committed fork
                // observed.
                if let Some((spans, caps)) = committed_metadata {
                    state.let_own_spans = spans;
                    state.lambda_own_captures = caps;
                }

                if let Some((failing_form, inner_err)) = dual_check_failure {
                    if is_multi_fork {
                        return Err(spanned(
                            TypeError::ShapeImplDualCheckFailure {
                                trait_name: trait_name.clone(),
                                method_name: method.name.clone(),
                                failing_form,
                                inner: inner_err.error,
                            },
                            method.span,
                        ));
                    } else {
                        return Err(inner_err);
                    }
                }

                if all_intrinsic {
                    continue;
                }

                let ForkCommit {
                    body_typed,
                    method_constraint_pairs,
                    fn_ty,
                } = committed.expect(
                    "check_fork returned no error and no commit for non-intrinsic impl",
                );
                let scheme = TypeScheme {
                    vars: vec![],
                    constraints: Vec::new(),
                    ty: fn_ty,
                    var_names: HashMap::new(),
                };
                instance_methods.push(typed_ast::InstanceMethod {
                    name: method.name.clone(),
                    params: method
                        .params
                        .iter()
                        .map(|p| crate::typed_ast::TypedParam {
                            name: p.name.clone(),
                            mode: p.mode,
                        })
                        .collect(),
                    body: body_typed,
                    scheme,
                    constraint_pairs: method_constraint_pairs,
                });
            }

            // TraitName synthesis: trait may not be registered yet (forward reference or self-reference).
            // Validation deferred to instance resolution phase.
            let inst_trait_name = trait_registry
                .lookup_trait_by_name(trait_name)
                .map(|ti| ti.trait_name())
                .unwrap_or_else(|| TraitName::new(module_path.to_string(), trait_name.clone()));
            // Preserve the full multi-param tuple; only the first is used for
            // resolution today, but downstream IR must see the real shape.
            let full_target_types = instance.target_types.clone();
            instance_defs.push(InstanceDefInfo {
                trait_name: inst_trait_name,
                target_type_name,
                target_types: full_target_types,
                type_var_ids: instance.type_var_ids.clone(),
                constraints: instance.constraints.clone(),
                methods: instance_methods,
                is_intrinsic: all_intrinsic,
            });
        }
    }

    Ok(instance_defs)
}


/// Internal per-module inference with pre-resolved module cache.
///
/// The module graph has already been resolved and toposorted by `infer_module`.
/// Import declarations look up module interfaces from `interface_cache` and typed
/// results from `cache` — no recursive resolution or cycle detection needed.
///
/// Pipeline phases:
///  1. Initialize state (env, registry, intrinsics)
///  2. Build synthetic prelude import
///  3. Process imports (types, fns, traits, re-exports)
///  4. Reserve type var generator past imported schemes
///  5. Process local extern declarations
///  6. Clean up prelude shadows
///  7. Pre-register local type names
///  8. Process local type declarations
///  9. Register traits (imported + local)
/// 10. Process deriving declarations
/// 11. Process impl blocks
/// 12. SCC-based function inference
/// 13. Post-inference instance resolution
/// 14. Impl method type-checking
/// 15. Assemble TypedModule
pub(crate) fn infer_module_inner(
    module: &Module,
    interface_cache: &HashMap<String, crate::module_interface::ModuleInterface>,
    module_path: String,
    prelude_tree_paths: &HashSet<String>,
) -> Result<TypedModule, Vec<SpannedTypeError>> {
    let is_core_module = module_path.starts_with("core/");
    let is_prelude_tree = prelude_tree_paths.contains(&module_path);

    let mut state = ModuleInferenceState::new(is_core_module);

    let synthetic_prelude_import =
        state.build_synthetic_prelude_import(is_prelude_tree, interface_cache);

    state
        .process_imports(module, interface_cache, synthetic_prelude_import.as_ref())
        .map_err(|e| vec![e])?;
    reserve_gen_for_env_schemes(&state.env, &mut state.gen);
    let (extern_fns, extern_types, extern_bindings, extern_fn_constraints, pending_extern_traits) =
        state
            .process_local_externs(module, &module_path)
            .map_err(|e| vec![e])?;
    state.cleanup_prelude_shadows(module);
    state
        .check_explicit_import_shadows(module)
        .map_err(|e| vec![e])?;
    state
        .check_duplicate_function_names(module)
        .map_err(|e| vec![e])?;
    state.preregister_type_names(module);
    let constructor_schemes = state
        .process_local_type_decls(module, &module_path)
        .map_err(|e| vec![e])?;

    // Phase: trait registration, deriving, impl registration
    let (
        trait_registry,
        exported_trait_defs,
        extern_traits,
        derived_instance_defs,
        imported_instance_defs,
        trait_method_map,
    ) = process_traits_and_deriving(
        &mut state,
        module,
        interface_cache,
        &module_path,
        is_core_module,
        pending_extern_traits,
    )
    .map_err(|e| vec![e])?;

    // Phase: SCC-based function inference
    let (fn_decls, result_schemes, fn_bodies, mut fn_constraint_requirements) =
        infer_function_bodies(
            &mut state,
            module,
            &extern_fns,
            &trait_registry,
            &trait_method_map,
            &module_path,
        )
        .map_err(|e| vec![e])?;

    // Merge extern function where-clause dict requirements
    for (name, reqs) in extern_fn_constraints {
        fn_constraint_requirements.entry(name).or_insert(reqs);
    }

    // Phase: impl method type-checking
    let instance_defs = typecheck_impl_methods(
        &mut state,
        module,
        &module_path,
        &trait_registry,
        &trait_method_map,
        &extern_fns,
    )
    .map_err(|e| vec![e])?;

    state.assemble_typed_module(
        module,
        module_path,
        &fn_decls,
        result_schemes,
        fn_bodies,
        instance_defs,
        derived_instance_defs,
        imported_instance_defs,
        &mut fn_constraint_requirements,
        &trait_method_map,
        &trait_registry,
        exported_trait_defs,
        extern_fns,
        extern_types,
        extern_traits,
        extern_bindings,
        constructor_schemes,
        interface_cache,
    )
}
