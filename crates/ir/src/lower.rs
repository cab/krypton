use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{BinOp, Lit, UnaryOp};
use krypton_typechecker::typed_ast::{
    ExportedTypeKind, FnTypeEntry, TraitId, TypedExpr, TypedExprKind, TypedFnDecl, TypedModule,
};
use krypton_typechecker::types::{Type, TypeScheme, TypeVarGen, TypeVarId};

use crate::{
    Atom, Expr, ExprKind, FnDef, FnId, Literal, Module, PrimOp, SimpleExpr, StructDef,
    SumTypeDef, SwitchBranch, VarId, VariantDef,
};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum LowerError {
    NotYetLowered(String),
    UnresolvedVar(String),
    UnresolvedStruct(String),
    UnresolvedField(String, String),
    UnsupportedOp(String),
    InternalError(String),
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::NotYetLowered(s) => write!(f, "not yet lowered: {s}"),
            LowerError::UnresolvedVar(s) => write!(f, "unresolved variable: {s}"),
            LowerError::UnresolvedStruct(s) => write!(f, "unresolved struct: {s}"),
            LowerError::UnresolvedField(t, field) => {
                write!(f, "unresolved field {field} on {t}")
            }
            LowerError::UnsupportedOp(s) => write!(f, "unsupported op: {s}"),
            LowerError::InternalError(s) => write!(f, "internal error: {s}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Helper: intermediate let-binding produced during ANF normalization
// ---------------------------------------------------------------------------

struct LetBinding {
    bind: VarId,
    ty: Type,
    value: SimpleExpr,
}

/// Extracted info about a parameterized trait instance (for dict construction).
#[derive(Clone)]
struct ParamInstanceInfo {
    trait_name: String,
    target_type: Type,
    type_var_ids: HashMap<String, TypeVarId>,
    constraints: Vec<(String, String)>, // (trait_name, type_var_name)
}

// ---------------------------------------------------------------------------
// Free variable analysis (on TypedExpr, before IR lowering)
// ---------------------------------------------------------------------------

/// Walk a TypedExpr tree and collect variable names that are referenced but not
/// bound locally (by Let, Lambda, or LetPattern). Returns deduplicated names in
/// stable (first-seen) order.
fn free_vars(expr: &TypedExpr, bound: &HashSet<String>) -> Vec<String> {
    let mut free = Vec::new();
    let mut seen = HashSet::new();
    free_vars_inner(expr, bound, &mut free, &mut seen);
    free
}

fn free_vars_inner(
    expr: &TypedExpr,
    bound: &HashSet<String>,
    free: &mut Vec<String>,
    seen: &mut HashSet<String>,
) {
    match &expr.kind {
        TypedExprKind::Lit(_) => {}
        TypedExprKind::Var(name) => {
            if !bound.contains(name) && seen.insert(name.clone()) {
                free.push(name.clone());
            }
        }
        TypedExprKind::App { func, args } => {
            free_vars_inner(func, bound, free, seen);
            for a in args {
                free_vars_inner(a, bound, free, seen);
            }
        }
        TypedExprKind::TypeApp { expr: inner, .. } => {
            free_vars_inner(inner, bound, free, seen);
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            free_vars_inner(lhs, bound, free, seen);
            free_vars_inner(rhs, bound, free, seen);
        }
        TypedExprKind::UnaryOp { operand, .. } => {
            free_vars_inner(operand, bound, free, seen);
        }
        TypedExprKind::If { cond, then_, else_ } => {
            free_vars_inner(cond, bound, free, seen);
            free_vars_inner(then_, bound, free, seen);
            free_vars_inner(else_, bound, free, seen);
        }
        TypedExprKind::Let {
            name,
            value,
            body,
            ..
        } => {
            free_vars_inner(value, bound, free, seen);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                free_vars_inner(body, &inner_bound, free, seen);
            }
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs {
                free_vars_inner(e, bound, free, seen);
            }
        }
        TypedExprKind::Lambda { params, body } => {
            let mut inner_bound = bound.clone();
            for p in params {
                inner_bound.insert(p.clone());
            }
            free_vars_inner(body, &inner_bound, free, seen);
        }
        TypedExprKind::Match { scrutinee, arms } => {
            free_vars_inner(scrutinee, bound, free, seen);
            for arm in arms {
                let mut inner_bound = bound.clone();
                collect_pattern_bindings(&arm.pattern, &mut inner_bound);
                free_vars_inner(&arm.body, &inner_bound, free, seen);
            }
        }
        TypedExprKind::FieldAccess { expr: inner, .. } => {
            free_vars_inner(inner, bound, free, seen);
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, fexpr) in fields {
                free_vars_inner(fexpr, bound, free, seen);
            }
        }
        TypedExprKind::StructUpdate { base, fields } => {
            free_vars_inner(base, bound, free, seen);
            for (_, fexpr) in fields {
                free_vars_inner(fexpr, bound, free, seen);
            }
        }
        TypedExprKind::Tuple(elems) | TypedExprKind::VecLit(elems) => {
            for e in elems {
                free_vars_inner(e, bound, free, seen);
            }
        }
        TypedExprKind::Recur(args) => {
            for a in args {
                free_vars_inner(a, bound, free, seen);
            }
        }
        TypedExprKind::QuestionMark { expr: inner, .. } => {
            free_vars_inner(inner, bound, free, seen);
        }
        TypedExprKind::LetPattern {
            pattern,
            value,
            body,
            ..
        } => {
            free_vars_inner(value, bound, free, seen);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                collect_pattern_bindings(pattern, &mut inner_bound);
                free_vars_inner(body, &inner_bound, free, seen);
            }
        }
    }
}

/// Collect all variable names bound by a pattern.
fn collect_pattern_bindings(
    pattern: &krypton_typechecker::typed_ast::TypedPattern,
    bound: &mut HashSet<String>,
) {
    use krypton_typechecker::typed_ast::TypedPattern;
    match pattern {
        TypedPattern::Var { name, .. } => {
            bound.insert(name.clone());
        }
        TypedPattern::Constructor { args, .. } => {
            for p in args {
                collect_pattern_bindings(p, bound);
            }
        }
        TypedPattern::Tuple { elements, .. } => {
            for p in elements {
                collect_pattern_bindings(p, bound);
            }
        }
        TypedPattern::StructPat { fields, .. } => {
            for (_, p) in fields {
                collect_pattern_bindings(p, bound);
            }
        }
        TypedPattern::Wildcard { .. } | TypedPattern::Lit { .. } => {}
    }
}

// ---------------------------------------------------------------------------
// Lowering context
// ---------------------------------------------------------------------------

struct LowerCtx {
    next_var: u32,
    next_fn: u32,
    /// For generating TypeVarIds for private type definitions
    type_var_gen: TypeVarGen,
    /// name → stack of VarIds (supports nested scopes)
    var_scope: HashMap<String, Vec<VarId>>,
    /// top-level function name → FnId
    fn_ids: HashMap<String, FnId>,
    /// struct name → ordered fields with resolved types
    struct_fields: HashMap<String, Vec<(String, Type)>>,
    /// variant name → (type_name, tag, field_types)
    sum_variants: HashMap<String, (String, u32, Vec<Type>)>,
    /// Cached type_params for private types (avoids double build_type_param_map)
    private_type_params: HashMap<String, Vec<TypeVarId>>,
    /// fn_name → [(trait_name, TypeVarId)] — required trait dicts
    fn_constraints: HashMap<String, Vec<(String, TypeVarId)>>,
    /// (trait_name, TypeVarId) → VarId — dict param variables for the current function
    dict_params: HashMap<(String, TypeVarId), VarId>,
    /// fn_name → TypeScheme for resolving type var bindings at call sites
    fn_schemes: HashMap<String, TypeScheme>,
    /// Instance defs for parameterized dict resolution:
    /// (trait_name, target_type, type_var_ids, constraints)
    param_instances: Vec<ParamInstanceInfo>,
    /// trait_name → (type_var_id, method_name → (param_types, return_type))
    trait_method_types: HashMap<String, (TypeVarId, HashMap<String, (Vec<Type>, Type)>)>,
    /// Recursion depth counter for dict resolution (cycle detection)
    dict_depth: u32,
    /// Lifted lambda definitions accumulated during lowering
    lifted_fns: Vec<FnDef>,
}

impl LowerCtx {
    fn fresh_var(&mut self) -> VarId {
        let id = VarId(self.next_var);
        self.next_var += 1;
        id
    }

    fn fresh_fn(&mut self) -> FnId {
        let id = FnId(self.next_fn);
        self.next_fn += 1;
        id
    }

    fn push_var(&mut self, name: &str, id: VarId) {
        self.var_scope
            .entry(name.to_string())
            .or_default()
            .push(id);
    }

    fn pop_var(&mut self, name: &str) {
        if let Some(stack) = self.var_scope.get_mut(name) {
            stack.pop();
            if stack.is_empty() {
                self.var_scope.remove(name);
            }
        }
    }

    fn lookup_var(&self, name: &str) -> Option<VarId> {
        self.var_scope.get(name).and_then(|s| s.last().copied())
    }

    fn lookup_fn(&self, name: &str) -> Option<FnId> {
        self.fn_ids.get(name).copied()
    }

    fn field_index(&self, type_name: &str, field_name: &str) -> Result<usize, LowerError> {
        let fields = self
            .struct_fields
            .get(type_name)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_name.to_string()))?;
        fields
            .iter()
            .position(|(n, _)| n == field_name)
            .ok_or_else(|| {
                LowerError::UnresolvedField(type_name.to_string(), field_name.to_string())
            })
    }

    // -----------------------------------------------------------------------
    // ANF helpers
    // -----------------------------------------------------------------------

    /// Wrap a sequence of let-bindings around an inner expression (right fold).
    fn wrap_bindings(bindings: Vec<LetBinding>, inner: Expr) -> Expr {
        bindings.into_iter().rev().fold(inner, |body, lb| Expr {
            ty: body.ty.clone(),
            kind: ExprKind::Let {
                bind: lb.bind,
                ty: lb.ty,
                value: lb.value,
                body: Box::new(body),
            },
        })
    }

    /// Lower an expression to an Atom. If already atomic, return it directly.
    /// Otherwise lower to SimpleExpr, bind to a fresh VarId, emit a LetBinding.
    /// For compound expressions (If, Do), returns an error — callers should use
    /// lower_expr + inline_compound_let instead.
    fn lower_to_atom(
        &mut self,
        expr: &TypedExpr,
    ) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        match &expr.kind {
            TypedExprKind::Lit(lit) => Ok((vec![], Atom::Lit(convert_lit(lit)))),
            TypedExprKind::Var(name) => {
                // Check if it's a nullary variant constructor
                if let Some((_, _, ref fields)) = self.sum_variants.get(name.as_str()) {
                    if fields.is_empty() {
                        // Nullary constructor — need to bind to a let
                        let (bindings, simple) = self.lower_to_simple(expr)?;
                        let var = self.fresh_var();
                        let ty = expr.ty.clone();
                        let mut all_bindings = bindings;
                        all_bindings.push(LetBinding {
                            bind: var,
                            ty,
                            value: simple,
                        });
                        return Ok((all_bindings, Atom::Var(var)));
                    }
                }
                if let Some(id) = self.lookup_var(name) {
                    Ok((vec![], Atom::Var(id)))
                } else if self.lookup_fn(name).is_some() {
                    // Top-level function reference as a value — bind it
                    let (bindings, simple) = self.lower_to_simple(expr)?;
                    let var = self.fresh_var();
                    let ty = expr.ty.clone();
                    let mut all_bindings = bindings;
                    all_bindings.push(LetBinding {
                        bind: var,
                        ty,
                        value: simple,
                    });
                    Ok((all_bindings, Atom::Var(var)))
                } else {
                    Err(LowerError::UnresolvedVar(name.clone()))
                }
            }
            TypedExprKind::TypeApp { expr: inner, .. } => self.lower_to_atom(inner),
            _ => match self.try_lower_as_simple(expr)? {
                LoweredValue::Simple(bindings, simple) => {
                    let var = self.fresh_var();
                    let ty = expr.ty.clone();
                    let mut all_bindings = bindings;
                    all_bindings.push(LetBinding {
                        bind: var,
                        ty,
                        value: simple,
                    });
                    Ok((all_bindings, Atom::Var(var)))
                }
                LoweredValue::Expr(_) => {
                    // Compound expression in atom position (e.g. `(if b {1} else {2}) + 3`).
                    // This is rare in real code. We can't express it as flat let-bindings.
                    // Report as not-yet-lowered for now; proper handling requires
                    // restructuring callers to use join points.
                    Err(LowerError::InternalError(format!(
                        "compound expression in atom position not yet supported: {:?}",
                        std::mem::discriminant(&expr.kind)
                    )))
                }
            },
        }
    }

    /// Lower an expression to a SimpleExpr (one step of computation).
    /// Returns prefix let-bindings and the SimpleExpr.
    fn lower_to_simple(
        &mut self,
        expr: &TypedExpr,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        match &expr.kind {
            TypedExprKind::Lit(_) => {
                // Lits are atoms — callers should use lower_to_atom instead
                Err(LowerError::InternalError(
                    "lower_to_simple called on Lit (use lower_to_atom)".to_string(),
                ))
            }
            TypedExprKind::Var(name) => {
                // Nullary variant constructor
                if let Some((type_name, tag, fields)) =
                    self.sum_variants.get(name.as_str()).cloned()
                {
                    if fields.is_empty() {
                        return Ok((
                            vec![],
                            SimpleExpr::ConstructVariant {
                                type_name,
                                variant: name.clone(),
                                tag,
                                fields: vec![],
                            },
                        ));
                    }
                }
                // Function reference as value — wrap in MakeClosure with no captures
                if let Some(fn_id) = self.lookup_fn(name) {
                    return Ok((
                        vec![],
                        SimpleExpr::MakeClosure {
                            func: fn_id,
                            captures: vec![],
                        },
                    ));
                }
                // Should not reach here for a plain var (those are atoms)
                Err(LowerError::InternalError(format!(
                    "lower_to_simple called on plain Var({name})"
                )))
            }
            TypedExprKind::TypeApp { expr: inner, .. } => self.lower_to_simple(inner),
            TypedExprKind::BinaryOp {
                op: BinOp::And | BinOp::Or,
                ..
            } => Err(LowerError::InternalError(
                "And/Or must be lowered as compound expr (short-circuit)".to_string(),
            )),
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let (mut bindings, lhs_atom) = self.lower_to_atom(lhs)?;
                let (rhs_bindings, rhs_atom) = self.lower_to_atom(rhs)?;
                bindings.extend(rhs_bindings);
                let prim_op = resolve_binop(op, &lhs.ty)?;
                Ok((
                    bindings,
                    SimpleExpr::PrimOp {
                        op: prim_op,
                        args: vec![lhs_atom, rhs_atom],
                    },
                ))
            }
            TypedExprKind::UnaryOp { op, operand } => {
                let (bindings, atom) = self.lower_to_atom(operand)?;
                let prim_op = resolve_unaryop(op, &operand.ty)?;
                Ok((
                    bindings,
                    SimpleExpr::PrimOp {
                        op: prim_op,
                        args: vec![atom],
                    },
                ))
            }
            TypedExprKind::App { func, args } => self.lower_app(func, args),
            TypedExprKind::Tuple(elems) => {
                let mut bindings = vec![];
                let mut atoms = vec![];
                for elem in elems {
                    let (bs, atom) = self.lower_to_atom(elem)?;
                    bindings.extend(bs);
                    atoms.push(atom);
                }
                Ok((bindings, SimpleExpr::MakeTuple { elements: atoms }))
            }
            TypedExprKind::StructLit { name, fields } => {
                self.lower_struct_lit(name, fields)
            }
            TypedExprKind::FieldAccess { expr: base, field } => {
                let (bindings, base_atom) = self.lower_to_atom(base)?;
                let type_name = type_name_of(&base.ty).ok_or_else(|| {
                    LowerError::InternalError(format!(
                        "FieldAccess on non-named type: {:?}",
                        base.ty
                    ))
                })?;
                let idx = self.field_index(&type_name, field)?;
                Ok((
                    bindings,
                    SimpleExpr::Project {
                        value: base_atom,
                        field_index: idx,
                    },
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
            TypedExprKind::Lambda { params, body } => {
                self.lower_lambda(params, body, &expr.ty)
            }
            TypedExprKind::Match { .. } => {
                Err(LowerError::NotYetLowered("Match".to_string()))
            }
            TypedExprKind::Recur(_) => {
                Err(LowerError::NotYetLowered("Recur".to_string()))
            }
            TypedExprKind::QuestionMark { .. } => {
                Err(LowerError::NotYetLowered("QuestionMark".to_string()))
            }
            TypedExprKind::LetPattern { .. } => {
                Err(LowerError::NotYetLowered("LetPattern".to_string()))
            }
            TypedExprKind::VecLit(_) => {
                Err(LowerError::NotYetLowered("VecLit".to_string()))
            }
        }
    }

    // -----------------------------------------------------------------------
    // Expression lowering (produces full Expr trees)
    // -----------------------------------------------------------------------

    fn lower_expr(&mut self, expr: &TypedExpr) -> Result<Expr, LowerError> {
        match &expr.kind {
            TypedExprKind::Lit(lit) => Ok(Expr {
                kind: ExprKind::Atom(Atom::Lit(convert_lit(lit))),
                ty: expr.ty.clone(),
            }),

            TypedExprKind::Var(name) => {
                // Nullary variant constructor
                if let Some((type_name, tag, fields)) =
                    self.sum_variants.get(name.as_str()).cloned()
                {
                    if fields.is_empty() {
                        let var = self.fresh_var();
                        return Ok(Expr {
                            ty: expr.ty.clone(),
                            kind: ExprKind::Let {
                                bind: var,
                                ty: expr.ty.clone(),
                                value: SimpleExpr::ConstructVariant {
                                    type_name,
                                    variant: name.clone(),
                                    tag,
                                    fields: vec![],
                                },
                                body: Box::new(Expr {
                                    ty: expr.ty.clone(),
                                    kind: ExprKind::Atom(Atom::Var(var)),
                                }),
                            },
                        });
                    }
                }
                if let Some(id) = self.lookup_var(name) {
                    Ok(Expr {
                        kind: ExprKind::Atom(Atom::Var(id)),
                        ty: expr.ty.clone(),
                    })
                } else if let Some(fn_id) = self.lookup_fn(name) {
                    // Top-level function used as value
                    let var = self.fresh_var();
                    Ok(Expr {
                        ty: expr.ty.clone(),
                        kind: ExprKind::Let {
                            bind: var,
                            ty: expr.ty.clone(),
                            value: SimpleExpr::MakeClosure {
                                func: fn_id,
                                captures: vec![],
                            },
                            body: Box::new(Expr {
                                ty: expr.ty.clone(),
                                kind: ExprKind::Atom(Atom::Var(var)),
                            }),
                        },
                    })
                } else {
                    Err(LowerError::UnresolvedVar(name.clone()))
                }
            }

            TypedExprKind::TypeApp { expr: inner, .. } => self.lower_expr(inner),

            TypedExprKind::Let { name, value, body } => {
                let bind = self.fresh_var();
                self.push_var(name, bind);

                // Try to lower value as a SimpleExpr directly
                let lowered_value = self.try_lower_as_simple(value)?;
                let body_expr = if let Some(body) = body {
                    self.lower_expr(body)?
                } else {
                    // Let without body — the value IS the result
                    Expr {
                        ty: value.ty.clone(),
                        kind: ExprKind::Atom(Atom::Var(bind)),
                    }
                };

                self.pop_var(name);

                match lowered_value {
                    LoweredValue::Simple(bindings, simple) => {
                        let let_expr = Expr {
                            ty: body_expr.ty.clone(),
                            kind: ExprKind::Let {
                                bind,
                                ty: value.ty.clone(),
                                value: simple,
                                body: Box::new(body_expr),
                            },
                        };
                        Ok(Self::wrap_bindings(bindings, let_expr))
                    }
                    LoweredValue::Expr(value_expr) => {
                        // Value is a compound expression (If, Do, etc.)
                        // We need to inline the value expression and bind its result
                        Ok(self.inline_compound_let(bind, value.ty.clone(), value_expr, body_expr))
                    }
                }
            }

            TypedExprKind::Do(exprs) => self.lower_do(exprs, &expr.ty),

            TypedExprKind::If { cond, then_, else_ } => {
                let (bindings, cond_atom) = self.lower_to_atom(cond)?;
                let then_body = self.lower_expr(then_)?;
                let else_body = self.lower_expr(else_)?;

                let switch = Expr {
                    ty: expr.ty.clone(),
                    kind: ExprKind::Switch {
                        scrutinee: cond_atom,
                        branches: vec![SwitchBranch {
                            tag: 1, // true
                            bindings: vec![],
                            body: then_body,
                        }],
                        default: Some(Box::new(else_body)),
                    },
                };
                Ok(Self::wrap_bindings(bindings, switch))
            }

            TypedExprKind::App { func, args } => {
                let (mut bindings, simple) = self.lower_app(func, args)?;
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone(),
                    value: simple,
                });
                let inner = Expr {
                    ty: ty.clone(),
                    kind: ExprKind::Atom(Atom::Var(var)),
                };
                Ok(Self::wrap_bindings(bindings, inner))
            }

            // Short-circuit: lhs && rhs → switch lhs { 1 -> rhs | _ -> false }
            TypedExprKind::BinaryOp {
                op: BinOp::And,
                lhs,
                rhs,
            } => self.lower_short_circuit(lhs, rhs, true),

            // Short-circuit: lhs || rhs → switch lhs { 1 -> true | _ -> rhs }
            TypedExprKind::BinaryOp {
                op: BinOp::Or,
                lhs,
                rhs,
            } => self.lower_short_circuit(lhs, rhs, false),

            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let (mut bindings, lhs_atom) = self.lower_to_atom(lhs)?;
                let (rhs_bindings, rhs_atom) = self.lower_to_atom(rhs)?;
                bindings.extend(rhs_bindings);
                let prim_op = resolve_binop(op, &lhs.ty)?;
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone(),
                    value: SimpleExpr::PrimOp {
                        op: prim_op,
                        args: vec![lhs_atom, rhs_atom],
                    },
                });
                let inner = Expr {
                    ty,
                    kind: ExprKind::Atom(Atom::Var(var)),
                };
                Ok(Self::wrap_bindings(bindings, inner))
            }

            TypedExprKind::UnaryOp { op, operand } => {
                let (mut bindings, atom) = self.lower_to_atom(operand)?;
                let prim_op = resolve_unaryop(op, &operand.ty)?;
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone(),
                    value: SimpleExpr::PrimOp {
                        op: prim_op,
                        args: vec![atom],
                    },
                });
                let inner = Expr {
                    ty,
                    kind: ExprKind::Atom(Atom::Var(var)),
                };
                Ok(Self::wrap_bindings(bindings, inner))
            }

            TypedExprKind::Tuple(elems) => {
                let mut bindings = vec![];
                let mut atoms = vec![];
                for elem in elems {
                    let (bs, atom) = self.lower_to_atom(elem)?;
                    bindings.extend(bs);
                    atoms.push(atom);
                }
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone(),
                    value: SimpleExpr::MakeTuple { elements: atoms },
                });
                let inner = Expr {
                    ty,
                    kind: ExprKind::Atom(Atom::Var(var)),
                };
                Ok(Self::wrap_bindings(bindings, inner))
            }

            TypedExprKind::StructLit { name, fields } => {
                let (mut bindings, simple) = self.lower_struct_lit(name, fields)?;
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone(),
                    value: simple,
                });
                let inner = Expr {
                    ty,
                    kind: ExprKind::Atom(Atom::Var(var)),
                };
                Ok(Self::wrap_bindings(bindings, inner))
            }

            TypedExprKind::FieldAccess { expr: base, field } => {
                let (mut bindings, base_atom) = self.lower_to_atom(base)?;
                let type_name = type_name_of(&base.ty).ok_or_else(|| {
                    LowerError::InternalError(format!(
                        "FieldAccess on non-named type: {:?}",
                        base.ty
                    ))
                })?;
                let idx = self.field_index(&type_name, field)?;
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone(),
                    value: SimpleExpr::Project {
                        value: base_atom,
                        field_index: idx,
                    },
                });
                let inner = Expr {
                    ty,
                    kind: ExprKind::Atom(Atom::Var(var)),
                };
                Ok(Self::wrap_bindings(bindings, inner))
            }

            TypedExprKind::StructUpdate { base, fields } => {
                self.lower_struct_update(base, fields, &expr.ty)
            }

            TypedExprKind::Lambda { params, body } => {
                let (bindings, simple) = self.lower_lambda(params, body, &expr.ty)?;
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                let mut all_bindings = bindings;
                all_bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone(),
                    value: simple,
                });
                let inner = Expr {
                    kind: ExprKind::Atom(Atom::Var(var)),
                    ty,
                };
                Ok(Self::wrap_bindings(all_bindings, inner))
            }
            TypedExprKind::Match { .. } => {
                Err(LowerError::NotYetLowered("Match".to_string()))
            }
            TypedExprKind::Recur(_) => {
                Err(LowerError::NotYetLowered("Recur".to_string()))
            }
            TypedExprKind::QuestionMark { .. } => {
                Err(LowerError::NotYetLowered("QuestionMark".to_string()))
            }
            TypedExprKind::LetPattern { .. } => {
                Err(LowerError::NotYetLowered("LetPattern".to_string()))
            }
            TypedExprKind::VecLit(_) => {
                Err(LowerError::NotYetLowered("VecLit".to_string()))
            }
        }
    }

    // -----------------------------------------------------------------------
    // Compound expression helpers
    // -----------------------------------------------------------------------

    /// Try to lower a value expression as either a SimpleExpr (for direct Let binding)
    /// or as a full Expr (for compound expressions like If, Do, nested Let, or atoms).
    fn try_lower_as_simple(
        &mut self,
        expr: &TypedExpr,
    ) -> Result<LoweredValue, LowerError> {
        match &expr.kind {
            // Atoms, compound expressions, and short-circuit ops produce Expr trees
            TypedExprKind::Lit(_)
            | TypedExprKind::Var(_)
            | TypedExprKind::If { .. }
            | TypedExprKind::Do(_)
            | TypedExprKind::Let { .. }
            | TypedExprKind::StructUpdate { .. }
            | TypedExprKind::BinaryOp {
                op: BinOp::And | BinOp::Or,
                ..
            } => {
                let e = self.lower_expr(expr)?;
                Ok(LoweredValue::Expr(e))
            }
            // Everything else can be lowered to SimpleExpr
            _ => {
                let (bindings, simple) = self.lower_to_simple(expr)?;
                Ok(LoweredValue::Simple(bindings, simple))
            }
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
    fn inline_compound_let(
        &mut self,
        bind: VarId,
        bind_ty: Type,
        value_expr: Expr,
        body: Expr,
    ) -> Expr {
        let join_name = self.fresh_var();
        let result_ty = body.ty.clone();
        let rewritten = self.replace_tail_with_jump(value_expr, join_name);
        Expr {
            ty: result_ty.clone(),
            kind: ExprKind::LetJoin {
                name: join_name,
                params: vec![(bind, bind_ty)],
                join_body: Box::new(body),
                body: Box::new(rewritten),
            },
        }
    }

    /// Replace tail positions of an expression with `jump target(tail_value)`.
    fn replace_tail_with_jump(&self, expr: Expr, target: VarId) -> Expr {
        let result_ty = expr.ty.clone();
        match expr.kind {
            ExprKind::Atom(atom) => Expr {
                ty: result_ty,
                kind: ExprKind::Jump {
                    target,
                    args: vec![atom],
                },
            },
            ExprKind::Let {
                bind,
                ty,
                value,
                body,
            } => {
                let new_body = self.replace_tail_with_jump(*body, target);
                Expr {
                    ty: result_ty,
                    kind: ExprKind::Let {
                        bind,
                        ty,
                        value,
                        body: Box::new(new_body),
                    },
                }
            }
            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                let new_branches: Vec<_> = branches
                    .into_iter()
                    .map(|b| SwitchBranch {
                        tag: b.tag,
                        bindings: b.bindings,
                        body: self.replace_tail_with_jump(b.body, target),
                    })
                    .collect();
                let new_default = default
                    .map(|d| Box::new(self.replace_tail_with_jump(*d, target)));
                Expr {
                    ty: result_ty,
                    kind: ExprKind::Switch {
                        scrutinee,
                        branches: new_branches,
                        default: new_default,
                    },
                }
            }
            ExprKind::LetJoin {
                name,
                params,
                join_body,
                body: join_scope,
            } => {
                let new_join_body = self.replace_tail_with_jump(*join_body, target);
                let new_scope = self.replace_tail_with_jump(*join_scope, target);
                Expr {
                    ty: result_ty,
                    kind: ExprKind::LetJoin {
                        name,
                        params,
                        join_body: Box::new(new_join_body),
                        body: Box::new(new_scope),
                    },
                }
            }
            // Jump and LetRec shouldn't appear as compound value tails
            _ => expr,
        }
    }

    /// Lower a Do block (sequence of expressions).
    /// Processes left-to-right so Let bindings are in scope for subsequent exprs.
    fn lower_do(&mut self, exprs: &[TypedExpr], _result_ty: &Type) -> Result<Expr, LowerError> {
        if exprs.is_empty() {
            return Ok(Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                ty: Type::Unit,
            });
        }
        self.lower_do_slice(exprs)
    }

    /// Recursively lower a slice of Do-block expressions.
    fn lower_do_slice(&mut self, exprs: &[TypedExpr]) -> Result<Expr, LowerError> {
        if exprs.len() == 1 {
            return self.lower_expr(&exprs[0]);
        }

        let expr = &exprs[0];
        let rest = &exprs[1..];

        // Special case: Let { body: None } in a Do block — the body is the rest of the block
        if let TypedExprKind::Let { name, value, body: None } = &expr.kind {
            let bind = self.fresh_var();
            self.push_var(name, bind);

            let lowered_value = self.try_lower_as_simple(value)?;
            let body_expr = self.lower_do_slice(rest)?;

            self.pop_var(name);

            return match lowered_value {
                LoweredValue::Simple(bindings, simple) => {
                    let let_expr = Expr {
                        ty: body_expr.ty.clone(),
                        kind: ExprKind::Let {
                            bind,
                            ty: value.ty.clone(),
                            value: simple,
                            body: Box::new(body_expr),
                        },
                    };
                    Ok(Self::wrap_bindings(bindings, let_expr))
                }
                LoweredValue::Expr(value_expr) => {
                    Ok(self.inline_compound_let(bind, value.ty.clone(), value_expr, body_expr))
                }
            };
        }

        // Non-let statement: lower as discarded binding, then continue with rest
        let lowered = self.try_lower_as_simple(expr)?;
        let discard = self.fresh_var();
        let rest_expr = self.lower_do_slice(rest)?;

        match lowered {
            LoweredValue::Simple(bindings, simple) => {
                let let_expr = Expr {
                    ty: rest_expr.ty.clone(),
                    kind: ExprKind::Let {
                        bind: discard,
                        ty: expr.ty.clone(),
                        value: simple,
                        body: Box::new(rest_expr),
                    },
                };
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
    fn lower_short_circuit(
        &mut self,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        is_and: bool,
    ) -> Result<Expr, LowerError> {
        let lhs_expr = self.lower_expr(lhs)?;
        let lhs_var = self.fresh_var();

        let (true_branch, false_branch) = if is_and {
            (self.lower_expr(rhs)?, Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Bool(false))),
                ty: Type::Bool,
            })
        } else {
            (Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Bool(true))),
                ty: Type::Bool,
            }, self.lower_expr(rhs)?)
        };

        let switch = Expr {
            ty: Type::Bool,
            kind: ExprKind::Switch {
                scrutinee: Atom::Var(lhs_var),
                branches: vec![SwitchBranch {
                    tag: 1,
                    bindings: vec![],
                    body: true_branch,
                }],
                default: Some(Box::new(false_branch)),
            },
        };

        // Bind lhs result to lhs_var, then switch on it
        Ok(self.inline_compound_let(lhs_var, Type::Bool, lhs_expr, switch))
    }

    /// Lower a function application.
    fn lower_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // Peel TypeApp to get the function name, origin, and type args
        let (func_name, origin, type_args) = extract_call_info(func);

        // ANF-normalize all arguments
        let mut bindings = vec![];
        let mut arg_atoms = vec![];
        for arg in args {
            let (bs, atom) = self.lower_to_atom(arg)?;
            bindings.extend(bs);
            arg_atoms.push(atom);
        }

        // Handle trait method dispatch (origin-tagged calls)
        if let Some(ref trait_id) = origin {
            if let Some(ref name) = func_name {
                if let Some(fn_id) = self.lookup_fn(name) {
                    // Resolve the dispatch type from trait method type patterns
                    let dict_ty = self.resolve_trait_dispatch_type(
                        &trait_id.name,
                        name,
                        args,
                        &type_args,
                        func,
                    );
                    if let Some(dict_ty) = dict_ty {
                        let (dict_bindings, dict_atom) =
                            self.resolve_dict(&trait_id.name, &dict_ty)?;
                        bindings.extend(dict_bindings);

                        // Dict is prepended as first argument
                        let mut all_args = vec![dict_atom];
                        all_args.extend(arg_atoms);
                        return Ok((bindings, SimpleExpr::Call { func: fn_id, args: all_args }));
                    }
                    return Err(LowerError::InternalError(format!(
                        "could not resolve trait dispatch type for {}.{}",
                        trait_id.name, name
                    )));
                }
            }
        }

        if let Some(name) = &func_name {
            // Check if it's a variant constructor
            if let Some((type_name, tag, _fields)) = self.sum_variants.get(name.as_str()).cloned()
            {
                return Ok((
                    bindings,
                    SimpleExpr::ConstructVariant {
                        type_name,
                        variant: name.clone(),
                        tag,
                        fields: arg_atoms,
                    },
                ));
            }

            // Check if it's a known top-level function
            if let Some(fn_id) = self.lookup_fn(name) {
                // Resolve dict arguments for constrained functions
                let (dict_bindings, dict_atoms) =
                    self.resolve_call_dicts(name, args, &type_args)?;
                bindings.extend(dict_bindings);

                let mut all_args = dict_atoms;
                all_args.extend(arg_atoms);
                return Ok((bindings, SimpleExpr::Call { func: fn_id, args: all_args }));
            }

            // Local variable with function type — closure call
            if let Some(var_id) = self.lookup_var(name) {
                return Ok((
                    bindings,
                    SimpleExpr::CallClosure {
                        closure: Atom::Var(var_id),
                        args: arg_atoms,
                    },
                ));
            }

            return Err(LowerError::UnresolvedVar(name.clone()));
        }

        // General case: func is a complex expression
        let (func_bindings, func_atom) = self.lower_to_atom(func)?;
        bindings.extend(func_bindings);
        Ok((
            bindings,
            SimpleExpr::CallClosure {
                closure: func_atom,
                args: arg_atoms,
            },
        ))
    }

    /// Lower a struct literal.
    fn lower_struct_lit(
        &mut self,
        name: &str,
        fields: &[(String, TypedExpr)],
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        let canonical_fields = self
            .struct_fields
            .get(name)
            .ok_or_else(|| LowerError::UnresolvedStruct(name.to_string()))?
            .clone();

        // Build a map of field name → lowered atom
        let mut field_map: HashMap<String, Atom> = HashMap::new();
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
                LowerError::UnresolvedField(name.to_string(), fname.clone())
            })?;
            ordered_atoms.push(atom);
        }

        Ok((
            bindings,
            SimpleExpr::Construct {
                type_name: name.to_string(),
                fields: ordered_atoms,
            },
        ))
    }

    /// Lower a struct update expression.
    fn lower_struct_update(
        &mut self,
        base: &TypedExpr,
        updates: &[(String, TypedExpr)],
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let type_name = type_name_of(&base.ty).ok_or_else(|| {
            LowerError::InternalError(format!(
                "StructUpdate on non-named type: {:?}",
                base.ty
            ))
        })?;

        let canonical_fields = self
            .struct_fields
            .get(&type_name)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_name.clone()))?
            .clone();

        // Lower base expression to atom
        let (mut all_bindings, base_atom) = self.lower_to_atom(base)?;

        // Lower update expressions
        let mut update_map: HashMap<String, Atom> = HashMap::new();
        for (fname, fexpr) in updates {
            let (bs, atom) = self.lower_to_atom(fexpr)?;
            all_bindings.extend(bs);
            update_map.insert(fname.clone(), atom);
        }

        // For each field: use updated value if present, otherwise Project from base
        let mut field_atoms = vec![];
        for (i, (fname, fty)) in canonical_fields.iter().enumerate() {
            if let Some(atom) = update_map.remove(fname) {
                field_atoms.push(atom);
            } else {
                // Project unchanged field from base
                let proj_var = self.fresh_var();
                all_bindings.push(LetBinding {
                    bind: proj_var,
                    ty: fty.clone(),
                    value: SimpleExpr::Project {
                        value: base_atom.clone(),
                        field_index: i,
                    },
                });
                field_atoms.push(Atom::Var(proj_var));
            }
        }

        // Construct the new struct
        let construct_var = self.fresh_var();
        all_bindings.push(LetBinding {
            bind: construct_var,
            ty: result_ty.clone(),
            value: SimpleExpr::Construct {
                type_name,
                fields: field_atoms,
            },
        });

        let inner = Expr {
            ty: result_ty.clone(),
            kind: ExprKind::Atom(Atom::Var(construct_var)),
        };
        Ok(Self::wrap_bindings(all_bindings, inner))
    }

    // -----------------------------------------------------------------------
    // Dict resolution
    // -----------------------------------------------------------------------

    /// Resolve a trait dictionary for a given trait and concrete type.
    /// Returns let-bindings and an atom referencing the dict value.
    fn resolve_dict(
        &mut self,
        trait_name: &str,
        ty: &Type,
    ) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        const MAX_DICT_DEPTH: u32 = 64;
        if self.dict_depth >= MAX_DICT_DEPTH {
            return Err(LowerError::InternalError(format!(
                "dict resolution depth exceeded for {trait_name}[{ty}]"
            )));
        }
        self.dict_depth += 1;
        let result = self.resolve_dict_inner(trait_name, ty);
        self.dict_depth -= 1;
        result
    }

    fn resolve_dict_inner(
        &mut self,
        trait_name: &str,
        ty: &Type,
    ) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        let ty = strip_own(ty);

        // Strategy 1: Type variable — look up dict param
        if let Some(var_id) = self.lookup_dict_var(trait_name, ty) {
            return Ok((vec![], Atom::Var(var_id)));
        }

        // Strategy 2: Check for parameterized instance with where-constraints
        if let Some(result) = self.try_resolve_parameterized_dict(trait_name, ty)? {
            return Ok(result);
        }

        // Strategy 3: Concrete singleton dict
        let var = self.fresh_var();
        Ok((
            vec![LetBinding {
                bind: var,
                ty: Type::Named("Dict".to_string(), vec![]),
                value: SimpleExpr::GetDict {
                    trait_name: trait_name.to_string(),
                    ty: ty.clone(),
                },
            }],
            Atom::Var(var),
        ))
    }

    /// Look up a dict param VarId for a type variable.
    fn lookup_dict_var(&self, trait_name: &str, ty: &Type) -> Option<VarId> {
        match ty {
            Type::Var(id) => self
                .dict_params
                .get(&(trait_name.to_string(), *id))
                .copied(),
            _ => None,
        }
    }

    /// Try to resolve a parameterized instance dict (e.g., Show[Option[a]] where a: Show).
    fn try_resolve_parameterized_dict(
        &mut self,
        trait_name: &str,
        ty: &Type,
    ) -> Result<Option<(Vec<LetBinding>, Atom)>, LowerError> {
        // Find a matching instance with constraints, keeping the bindings
        let matching = self.param_instances.iter().find_map(|inst| {
            if inst.trait_name != trait_name {
                return None;
            }
            let mut bindings = HashMap::new();
            if bind_type_vars(&inst.target_type, ty, &mut bindings) {
                Some((inst.clone(), bindings))
            } else {
                None
            }
        });

        let Some((inst, type_bindings)) = matching else {
            return Ok(None);
        };

        // Resolve sub-dicts for each constraint
        let mut all_bindings = vec![];
        let mut sub_dict_atoms = vec![];
        for (constraint_trait, constraint_type_var) in &inst.constraints {
            if let Some(&type_var_id) = inst.type_var_ids.get(constraint_type_var) {
                let sub_type = type_bindings
                    .get(&type_var_id)
                    .cloned()
                    .unwrap_or(Type::Var(type_var_id));
                let (bs, atom) = self.resolve_dict(constraint_trait, &sub_type)?;
                all_bindings.extend(bs);
                sub_dict_atoms.push(atom);
            }
        }

        let var = self.fresh_var();
        all_bindings.push(LetBinding {
            bind: var,
            ty: Type::Named("Dict".to_string(), vec![]),
            value: SimpleExpr::MakeDict {
                trait_name: trait_name.to_string(),
                ty: ty.clone(),
                sub_dicts: sub_dict_atoms,
            },
        });
        Ok(Some((all_bindings, Atom::Var(var))))
    }

    /// Resolve dict arguments for a call to a constrained function.
    /// Returns let-bindings and dict atom args to prepend.
    fn resolve_call_dicts(
        &mut self,
        name: &str,
        args: &[TypedExpr],
        type_args: &[Type],
    ) -> Result<(Vec<LetBinding>, Vec<Atom>), LowerError> {
        let constraints = match self.fn_constraints.get(name) {
            Some(c) if !c.is_empty() => c.clone(),
            _ => return Ok((vec![], vec![])),
        };

        // Get the function's type scheme to extract param type patterns
        let scheme = self.fn_schemes.get(name).cloned();

        // Build type var bindings from type_args and argument types
        let mut type_bindings: HashMap<TypeVarId, Type> = HashMap::new();

        if let Some(ref scheme) = scheme {
            // Bind from explicit type args
            for (var_id, ty) in scheme.vars.iter().zip(type_args.iter()) {
                type_bindings.insert(*var_id, ty.clone());
            }

            // Bind from argument types matched against param patterns
            if let Type::Fn(ref param_patterns, _) = scheme.ty {
                for (pattern, arg) in param_patterns.iter().zip(args.iter()) {
                    bind_type_vars(pattern, &arg.ty, &mut type_bindings);
                }
            }
        }

        let mut all_bindings = vec![];
        let mut dict_atoms = vec![];

        for (trait_name, type_var_id) in &constraints {
            let concrete_ty = type_bindings
                .get(type_var_id)
                .cloned()
                .unwrap_or(Type::Var(*type_var_id));
            let (bs, atom) = self.resolve_dict(trait_name, &concrete_ty)?;
            all_bindings.extend(bs);
            dict_atoms.push(atom);
        }

        Ok((all_bindings, dict_atoms))
    }

    /// Resolve the dispatch type for a trait method call.
    /// Uses trait_defs to get the method's param type patterns, then binds
    /// type vars from the actual args to determine the concrete dispatch type.
    fn resolve_trait_dispatch_type(
        &self,
        trait_name: &str,
        method_name: &str,
        args: &[TypedExpr],
        type_args: &[Type],
        func: &TypedExpr,
    ) -> Option<Type> {
        // Find the trait's type var and method types
        let (type_var_id, method_types) = self.trait_method_types.get(trait_name)?;
        let type_var_id = *type_var_id;

        // Get method type patterns
        let (param_patterns, ret_pattern) = method_types.get(method_name)?;

        let mut bindings = HashMap::new();

        // Bind from params
        for (pattern, arg) in param_patterns.iter().zip(args.iter()) {
            bind_type_vars(pattern, &arg.ty, &mut bindings);
        }

        // Bind from return type
        let actual_ret = match &func.ty {
            Type::Fn(_, ret) => ret.as_ref().clone(),
            other => other.clone(),
        };
        bind_type_vars(ret_pattern, &actual_ret, &mut bindings);

        // Bind from explicit type application
        if !type_args.is_empty() {
            bindings.entry(type_var_id).or_insert_with(|| type_args[0].clone());
        }

        bindings.get(&type_var_id).cloned()
    }

    // -----------------------------------------------------------------------
    // Lambda lifting (closure conversion)
    // -----------------------------------------------------------------------

    fn lower_lambda(
        &mut self,
        params: &[String],
        body: &TypedExpr,
        lambda_ty: &Type,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // 1. Extract param types and return type from the lambda's function type
        //    Unwrap Own(...) wrapper if present (ownership-annotated lambdas)
        let unwrapped_ty = match lambda_ty {
            Type::Own(inner) => inner.as_ref(),
            other => other,
        };
        let (param_types, return_type) = match unwrapped_ty {
            Type::Fn(param_tys, ret_ty) => (param_tys.clone(), ret_ty.as_ref().clone()),
            other => {
                return Err(LowerError::InternalError(format!(
                    "lambda has non-function type: {other:?}"
                )))
            }
        };

        // 2. Compute free variables (names not bound by lambda params)
        let param_set: HashSet<String> = params.iter().cloned().collect();
        let fv_names = free_vars(body, &param_set);

        // 3. Resolve each free var name to its current VarId — these are capture atoms
        let mut capture_params = vec![];
        let mut capture_atoms = vec![];
        let bindings = vec![];
        for name in &fv_names {
            if let Some(var_id) = self.lookup_var(name) {
                capture_atoms.push(Atom::Var(var_id));
                // We don't know the exact type of the captured var, but we can
                // look it up from the body's free var usage. Use a placeholder
                // that will be filled in when we allocate the capture param.
                capture_params.push((name.clone(), var_id));
            }
            // If the name isn't in var_scope, it's a top-level function —
            // not a capture (will be resolved by fn_ids during body lowering)
        }

        // 4. Collect dict captures: all enclosing dict_params
        let saved_dict_params = self.dict_params.clone();
        let mut dict_capture_atoms = vec![];
        let mut dict_capture_keys = vec![];
        for ((trait_name, type_var_id), var_id) in &saved_dict_params {
            dict_capture_atoms.push(Atom::Var(*var_id));
            dict_capture_keys.push((trait_name.clone(), *type_var_id));
        }

        // 5. Allocate a fresh FnId for the lifted function
        let fn_id = self.fresh_fn();
        let debug_name = format!("lambda${}", fn_id.0);

        // 6. Build the lifted FnDef
        // Params: captures ++ dict_captures ++ lambda_params
        let mut lifted_params = vec![];

        // Capture params — allocate new VarIds for the lifted fn's scope
        let mut capture_var_mappings = vec![];
        for (name, old_var_id) in &capture_params {
            let new_var = self.fresh_var();
            // Look up the type by finding what type the old var has.
            // We need to get this from the var_scope context. Since we can't
            // easily recover the type, we'll use a generic approach:
            // scan the body/context. For simplicity, use Type::Var since the
            // type info is already embedded in the TypedExpr.
            // Actually, we need to get the type from somewhere. Let's lower_to_atom
            // the captured var to find its type... but we just need the IR type.
            // The simplest approach: since we know the VarId, we don't have the type
            // directly. But in ANF IR, types on let-bindings carry the type.
            // Let's just use a placeholder — the body lowering will produce the right types.
            // We'll derive the type from the atom by re-checking. For now, just use
            // a type var since the IR types are mostly for documentation/pretty printing.
            let _ty = Type::Var(self.type_var_gen.fresh()); // placeholder for capture type
            capture_var_mappings.push((name.clone(), new_var, *old_var_id));
        }

        // Dict capture params — allocate new VarIds
        let mut new_dict_params = HashMap::new();
        let mut dict_var_mappings = vec![];
        for key in &dict_capture_keys {
            let new_var = self.fresh_var();
            new_dict_params.insert(key.clone(), new_var);
            dict_var_mappings.push((key.clone(), new_var));
        }

        // Lambda params — allocate new VarIds
        let mut lambda_var_mappings = vec![];
        for (i, param_name) in params.iter().enumerate() {
            let new_var = self.fresh_var();
            let ty = param_types.get(i).cloned().unwrap_or(Type::Unit);
            lambda_var_mappings.push((param_name.clone(), new_var, ty));
        }

        // Build the param list for the lifted FnDef
        for (_, new_var, _) in &capture_var_mappings {
            // Use a generic type for captures — not critical for correctness
            lifted_params.push((*new_var, Type::Var(self.type_var_gen.fresh())));
        }
        for (_, new_var) in &dict_var_mappings {
            lifted_params.push((*new_var, Type::Named("Dict".to_string(), vec![])));
        }
        for (_, new_var, ty) in &lambda_var_mappings {
            lifted_params.push((*new_var, ty.clone()));
        }

        // Push capture params and lambda params into var_scope
        for (name, new_var, _) in &capture_var_mappings {
            self.push_var(name, *new_var);
        }
        for (name, new_var, _) in &lambda_var_mappings {
            self.push_var(name, *new_var);
        }

        // Set dict_params to the captured dicts (mapped to new VarIds)
        let old_dict_params = std::mem::replace(&mut self.dict_params, new_dict_params);

        // Lower body
        let lowered_body = self.lower_expr(body)?;

        // Pop all from var_scope, restore dict_params
        for (name, _, _) in lambda_var_mappings.iter().rev() {
            self.pop_var(name);
        }
        for (name, _, _) in capture_var_mappings.iter().rev() {
            self.pop_var(name);
        }
        self.dict_params = old_dict_params;

        // 7. Push FnDef onto lifted_fns
        self.lifted_fns.push(FnDef {
            id: fn_id,
            debug_name: debug_name.clone(),
            params: lifted_params,
            return_type,
            body: lowered_body,
        });

        // 8. Register in fn_ids for fn_names resolution
        self.fn_ids.insert(debug_name, fn_id);

        // 9. Return MakeClosure with capture atoms
        let mut all_captures = capture_atoms;
        all_captures.extend(dict_capture_atoms);

        Ok((bindings, SimpleExpr::MakeClosure {
            func: fn_id,
            captures: all_captures,
        }))
    }

    // -----------------------------------------------------------------------
    // Function lowering
    // -----------------------------------------------------------------------

    fn lower_fn(
        &mut self,
        decl: &TypedFnDecl,
        fn_types: &[FnTypeEntry],
    ) -> Result<FnDef, LowerError> {
        let fn_id = self
            .fn_ids
            .get(&decl.name)
            .copied()
            .ok_or_else(|| LowerError::InternalError(format!("no FnId for {}", decl.name)))?;

        // Get param types from fn_types
        let (param_types, return_type) = get_fn_param_types(&decl.name, fn_types)?;

        // Clear dict_params from any previous function
        self.dict_params.clear();

        // Prepend dict params for constrained functions
        let mut params = vec![];
        if let Some(constraints) = self.fn_constraints.get(&decl.name).cloned() {
            for (trait_name, type_var_id) in &constraints {
                let var = self.fresh_var();
                self.dict_params
                    .insert((trait_name.clone(), *type_var_id), var);
                params.push((var, Type::Named("Dict".to_string(), vec![])));
            }
        }

        // Allocate VarIds for regular params
        for (i, param_name) in decl.params.iter().enumerate() {
            let var = self.fresh_var();
            let ty = param_types
                .get(i)
                .cloned()
                .unwrap_or(Type::Unit);
            self.push_var(param_name, var);
            params.push((var, ty));
        }

        let body = self.lower_expr(&decl.body)?;

        // Pop params
        for param_name in decl.params.iter().rev() {
            self.pop_var(param_name);
        }

        Ok(FnDef {
            id: fn_id,
            debug_name: decl.name.clone(),
            params,
            return_type,
            body,
        })
    }
}

/// Result of trying to lower a value expression.
enum LoweredValue {
    /// A SimpleExpr with prefix bindings (for atomic/call/primop values).
    Simple(Vec<LetBinding>, SimpleExpr),
    /// A full Expr tree (for If, Do, nested Let).
    Expr(Expr),
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn lower_module(typed: &TypedModule, module_name: &str) -> Result<Module, LowerError> {
    // Build fn_constraints from both local and imported requirements
    let mut fn_constraints: HashMap<String, Vec<(String, TypeVarId)>> = HashMap::new();
    for (name, reqs) in &typed.fn_constraint_requirements {
        fn_constraints.insert(name.clone(), reqs.clone());
    }
    for (name, reqs) in &typed.imported_fn_constraint_requirements {
        fn_constraints.entry(name.clone()).or_insert_with(|| reqs.clone());
    }

    // Build fn_schemes from fn_types
    let mut fn_schemes: HashMap<String, TypeScheme> = HashMap::new();
    for entry in &typed.fn_types {
        fn_schemes.insert(entry.name.clone(), entry.scheme.clone());
    }

    let mut ctx = LowerCtx {
        next_var: 0,
        next_fn: 0,
        type_var_gen: TypeVarGen::new(),
        var_scope: HashMap::new(),
        fn_ids: HashMap::new(),
        struct_fields: HashMap::new(),
        sum_variants: HashMap::new(),
        private_type_params: HashMap::new(),
        fn_constraints,
        dict_params: HashMap::new(),
        fn_schemes,
        param_instances: typed
            .instance_defs
            .iter()
            .filter(|inst| !inst.constraints.is_empty())
            .map(|inst| ParamInstanceInfo {
                trait_name: inst.trait_name.clone(),
                target_type: inst.target_type.clone(),
                type_var_ids: inst.type_var_ids.clone(),
                constraints: inst
                    .constraints
                    .iter()
                    .map(|c| (c.trait_name.clone(), c.type_var.clone()))
                    .collect(),
            })
            .collect(),
        trait_method_types: typed
            .trait_defs
            .iter()
            .map(|t| {
                (
                    t.name.clone(),
                    (t.type_var_id, t.method_tc_types.clone()),
                )
            })
            .collect(),
        dict_depth: 0,
        lifted_fns: vec![],
    };

    // 1. Build struct_fields from exported_type_infos (has resolved Types + real TypeVarIds)
    for (name, info) in &typed.exported_type_infos {
        if let ExportedTypeKind::Record { fields } = &info.kind {
            ctx.struct_fields.insert(name.clone(), fields.clone());
        }
    }
    // Fallback: private structs not in exported_type_infos
    for decl in &typed.struct_decls {
        if !ctx.struct_fields.contains_key(&decl.name) {
            let type_param_map = build_type_param_map(&decl.type_params, &mut ctx.type_var_gen);
            let ordered_params: Vec<TypeVarId> = decl
                .type_params
                .iter()
                .map(|name| type_param_map[name])
                .collect();
            ctx.private_type_params
                .insert(decl.name.clone(), ordered_params);
            let fields: Vec<(String, Type)> = decl
                .fields
                .iter()
                .map(|(fname, texpr)| {
                    let ty = resolve_type_expr_simple(texpr, &type_param_map);
                    (fname.clone(), ty)
                })
                .collect();
            ctx.struct_fields.insert(decl.name.clone(), fields);
        }
    }

    // 2. Build sum_variants from exported_type_infos
    for (name, info) in &typed.exported_type_infos {
        if let ExportedTypeKind::Sum { variants } = &info.kind {
            for (tag, variant) in variants.iter().enumerate() {
                ctx.sum_variants.insert(
                    variant.name.clone(),
                    (name.clone(), tag as u32, variant.fields.clone()),
                );
            }
        }
    }
    // Fallback: private sum types
    for decl in &typed.sum_decls {
        let already = decl
            .variants
            .iter()
            .any(|v| ctx.sum_variants.contains_key(&v.name));
        if !already {
            let type_param_map = build_type_param_map(&decl.type_params, &mut ctx.type_var_gen);
            let ordered_params: Vec<TypeVarId> = decl
                .type_params
                .iter()
                .map(|name| type_param_map[name])
                .collect();
            ctx.private_type_params
                .insert(decl.name.clone(), ordered_params);
            for (tag, variant) in decl.variants.iter().enumerate() {
                let fields: Vec<Type> = variant
                    .fields
                    .iter()
                    .map(|texpr| resolve_type_expr_simple(texpr, &type_param_map))
                    .collect();
                ctx.sum_variants.insert(
                    variant.name.clone(),
                    (decl.name.clone(), tag as u32, fields),
                );
            }
        }
    }

    // 3. Allocate FnIds for all known functions
    // Local function definitions
    for decl in &typed.functions {
        let fn_id = ctx.fresh_fn();
        ctx.fn_ids.insert(decl.name.clone(), fn_id);
    }
    // Extern functions
    for ext in &typed.extern_fns {
        if !ctx.fn_ids.contains_key(&ext.name) {
            let fn_id = ctx.fresh_fn();
            ctx.fn_ids.insert(ext.name.clone(), fn_id);
        }
    }
    for ext in &typed.imported_extern_fns {
        if !ctx.fn_ids.contains_key(&ext.name) {
            let fn_id = ctx.fresh_fn();
            ctx.fn_ids.insert(ext.name.clone(), fn_id);
        }
    }
    // Imported functions (from fn_types entries with provenance)
    for entry in &typed.fn_types {
        if !ctx.fn_ids.contains_key(&entry.name) {
            let fn_id = ctx.fresh_fn();
            ctx.fn_ids.insert(entry.name.clone(), fn_id);
        }
    }

    // 4. Lower struct definitions (skip imported types)
    let structs: Vec<StructDef> = typed
        .struct_decls
        .iter()
        .filter(|decl| !typed.type_provenance.contains_key(&decl.name))
        .map(|decl| {
            let (type_params, fields) =
                if let Some(info) = typed.exported_type_infos.get(&decl.name) {
                    let fields =
                        ctx.struct_fields.get(&decl.name).cloned().unwrap_or_default();
                    (info.type_param_vars.clone(), fields)
                } else {
                    // Private type — reuse cached TypeVarIds from step 1
                    let type_params = ctx
                        .private_type_params
                        .get(&decl.name)
                        .cloned()
                        .unwrap_or_default();
                    let fields =
                        ctx.struct_fields.get(&decl.name).cloned().unwrap_or_default();
                    (type_params, fields)
                };
            StructDef {
                name: decl.name.clone(),
                type_params,
                fields,
            }
        })
        .collect();

    // 5. Lower sum type definitions (skip imported types)
    let sum_types: Vec<SumTypeDef> = typed
        .sum_decls
        .iter()
        .filter(|decl| !typed.type_provenance.contains_key(&decl.name))
        .map(|decl| {
            let type_params =
                if let Some(info) = typed.exported_type_infos.get(&decl.name) {
                    info.type_param_vars.clone()
                } else {
                    // Reuse cached TypeVarIds from step 2
                    ctx.private_type_params
                        .get(&decl.name)
                        .cloned()
                        .unwrap_or_default()
                };
            let variants = decl
                .variants
                .iter()
                .enumerate()
                .map(|(tag, v)| {
                    let fields = ctx
                        .sum_variants
                        .get(&v.name)
                        .map(|(_, _, f)| f.clone())
                        .unwrap_or_default();
                    VariantDef {
                        name: v.name.clone(),
                        tag: tag as u32,
                        fields,
                    }
                })
                .collect();
            SumTypeDef {
                name: decl.name.clone(),
                type_params,
                variants,
            }
        })
        .collect();

    // 6. Lower functions
    let mut functions = vec![];
    for decl in &typed.functions {
        let fn_def = ctx.lower_fn(decl, &typed.fn_types)?;
        functions.push(fn_def);
    }

    // 6b. Append lifted lambdas
    functions.extend(ctx.lifted_fns.drain(..));

    // 7. Build fn_names lookup (includes lifted lambdas registered in fn_ids)
    let mut fn_names = HashMap::new();
    for (name, &id) in &ctx.fn_ids {
        fn_names.insert(id, name.clone());
    }

    // 8. Build extern_fn_types for non-local functions, prepending Dict
    //    params for constrained functions and trait methods to match the
    //    IR calling convention.
    let local_names: std::collections::HashSet<&str> =
        typed.functions.iter().map(|d| d.name.as_str()).collect();
    let mut extern_fn_types = HashMap::new();
    for entry in &typed.fn_types {
        if !local_names.contains(entry.name.as_str()) {
            if let Some(&fn_id) = ctx.fn_ids.get(&entry.name) {
                let ty = if entry.origin.is_some() {
                    // Trait methods always take a Dict as first arg
                    prepend_n_dicts(1, &entry.scheme.ty)
                } else {
                    // Regular constrained functions get Dict per constraint
                    prepend_dict_params(
                        &entry.name,
                        &ctx.fn_constraints,
                        &entry.scheme.ty,
                    )
                };
                extern_fn_types.insert(fn_id, ty);
            }
        }
    }

    Ok(Module {
        name: module_name.to_string(),
        structs,
        sum_types,
        functions,
        fn_names,
        extern_fn_types,
    })
}

// ---------------------------------------------------------------------------
// Free helper functions
// ---------------------------------------------------------------------------

/// Extract function name, origin, and type_args from a call expression,
/// peeling through TypeApp wrappers. Collects the outermost type_args.
fn extract_call_info(expr: &TypedExpr) -> (Option<String>, Option<TraitId>, Vec<Type>) {
    match &expr.kind {
        TypedExprKind::Var(name) => (Some(name.clone()), expr.origin.clone(), vec![]),
        TypedExprKind::TypeApp {
            expr: inner,
            type_args,
        } => {
            let (name, origin, _) = extract_call_info(inner);
            // Use origin from inner if present, else from this node
            let origin = origin.or_else(|| expr.origin.clone());
            (name, origin, type_args.clone())
        }
        _ => (None, expr.origin.clone(), vec![]),
    }
}

/// Convert a parser Lit to an IR Literal.
fn convert_lit(lit: &Lit) -> Literal {
    match lit {
        Lit::Int(n) => Literal::Int(*n),
        Lit::Float(f) => Literal::Float(*f),
        Lit::Bool(b) => Literal::Bool(*b),
        Lit::String(s) => Literal::String(s.clone()),
        Lit::Unit => Literal::Unit,
    }
}

/// Extract the type name from a Type::Named, stripping Own wrappers.
fn type_name_of(ty: &Type) -> Option<String> {
    match ty {
        Type::Named(name, _) => Some(name.clone()),
        Type::Own(inner) => type_name_of(inner),
        _ => None,
    }
}

/// Strip Own wrappers to get the underlying type for operation resolution.
fn strip_own(ty: &Type) -> &Type {
    match ty {
        Type::Own(inner) => strip_own(inner),
        other => other,
    }
}

/// Resolve BinOp + operand type to PrimOp.
fn resolve_binop(op: &BinOp, operand_ty: &Type) -> Result<PrimOp, LowerError> {
    let operand_ty = strip_own(operand_ty);
    match (op, operand_ty) {
        (BinOp::Add, Type::Int) => Ok(PrimOp::AddInt),
        (BinOp::Add, Type::Float) => Ok(PrimOp::AddFloat),
        (BinOp::Add, Type::String) => Ok(PrimOp::ConcatString),
        (BinOp::Sub, Type::Int) => Ok(PrimOp::SubInt),
        (BinOp::Sub, Type::Float) => Ok(PrimOp::SubFloat),
        (BinOp::Mul, Type::Int) => Ok(PrimOp::MulInt),
        (BinOp::Mul, Type::Float) => Ok(PrimOp::MulFloat),
        (BinOp::Div, Type::Int) => Ok(PrimOp::DivInt),
        (BinOp::Div, Type::Float) => Ok(PrimOp::DivFloat),
        (BinOp::Eq, Type::Int) => Ok(PrimOp::EqInt),
        (BinOp::Eq, Type::Float) => Ok(PrimOp::EqFloat),
        (BinOp::Eq, Type::String) => Ok(PrimOp::EqString),
        (BinOp::Eq, Type::Bool) => Ok(PrimOp::EqInt), // bools represented as 0/1 ints
        (BinOp::Neq, Type::Int) => Ok(PrimOp::NeqInt),
        (BinOp::Neq, Type::Float) => Ok(PrimOp::NeqFloat),
        (BinOp::Neq, Type::String) => Ok(PrimOp::NeqString),
        (BinOp::Neq, Type::Bool) => Ok(PrimOp::NeqInt), // bools represented as 0/1 ints
        (BinOp::Lt, Type::Int) => Ok(PrimOp::LtInt),
        (BinOp::Lt, Type::Float) => Ok(PrimOp::LtFloat),
        (BinOp::Le, Type::Int) => Ok(PrimOp::LeInt),
        (BinOp::Le, Type::Float) => Ok(PrimOp::LeFloat),
        (BinOp::Gt, Type::Int) => Ok(PrimOp::GtInt),
        (BinOp::Gt, Type::Float) => Ok(PrimOp::GtFloat),
        (BinOp::Ge, Type::Int) => Ok(PrimOp::GeInt),
        (BinOp::Ge, Type::Float) => Ok(PrimOp::GeFloat),
        // And/Or handled as Switch in lower_expr (short-circuit semantics)
        _ => Err(LowerError::UnsupportedOp(format!(
            "{op:?} on {operand_ty:?}"
        ))),
    }
}

/// Resolve UnaryOp + operand type to PrimOp.
fn resolve_unaryop(op: &UnaryOp, operand_ty: &Type) -> Result<PrimOp, LowerError> {
    let operand_ty = strip_own(operand_ty);
    match (op, operand_ty) {
        (UnaryOp::Neg, Type::Int) => Ok(PrimOp::NegInt),
        (UnaryOp::Neg, Type::Float) => Ok(PrimOp::NegFloat),
        (UnaryOp::Not, _) => Ok(PrimOp::Not),
        _ => Err(LowerError::UnsupportedOp(format!(
            "{op:?} on {operand_ty:?}"
        ))),
    }
}

/// Get parameter types and return type for a function from fn_types.
fn get_fn_param_types(
    name: &str,
    fn_types: &[FnTypeEntry],
) -> Result<(Vec<Type>, Type), LowerError> {
    for entry in fn_types {
        if entry.name == name {
            match &entry.scheme.ty {
                Type::Fn(params, ret) => return Ok((params.clone(), *ret.clone())),
                other => return Ok((vec![], other.clone())),
            }
        }
    }
    Err(LowerError::InternalError(format!(
        "no fn_types entry for function '{name}'"
    )))
}

/// Build a TypeVarId map from type parameter names using a shared TypeVarGen.
fn build_type_param_map(
    type_params: &[String],
    gen: &mut TypeVarGen,
) -> HashMap<String, TypeVarId> {
    type_params
        .iter()
        .map(|name| (name.clone(), gen.fresh()))
        .collect()
}

/// Simple TypeExpr → Type conversion for private types.
fn resolve_type_expr_simple(
    texpr: &krypton_parser::ast::TypeExpr,
    type_param_map: &HashMap<String, TypeVarId>,
) -> Type {
    use krypton_parser::ast::TypeExpr;
    match texpr {
        TypeExpr::Named { name, .. } => match name.as_str() {
            "Int" => Type::Int,
            "Float" => Type::Float,
            "Bool" => Type::Bool,
            "String" => Type::String,
            "Unit" => Type::Unit,
            _ => Type::Named(name.clone(), vec![]),
        },
        TypeExpr::Var { name, .. } => {
            if let Some(&id) = type_param_map.get(name) {
                Type::Var(id)
            } else {
                Type::Named(name.clone(), vec![])
            }
        }
        TypeExpr::App { name, args, .. } => {
            // Check if the name is a type variable
            if let Some(&id) = type_param_map.get(name) {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_simple(a, type_param_map))
                    .collect();
                Type::App(Box::new(Type::Var(id)), resolved_args)
            } else {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_simple(a, type_param_map))
                    .collect();
                Type::Named(name.clone(), resolved_args)
            }
        }
        TypeExpr::Fn { params, ret, .. } => {
            let param_types: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_simple(p, type_param_map))
                .collect();
            let ret_type = resolve_type_expr_simple(ret, type_param_map);
            Type::Fn(param_types, Box::new(ret_type))
        }
        TypeExpr::Own { inner, .. } => {
            Type::Own(Box::new(resolve_type_expr_simple(inner, type_param_map)))
        }
        TypeExpr::Tuple { elements, .. } => {
            let elem_types: Vec<Type> = elements
                .iter()
                .map(|e| resolve_type_expr_simple(e, type_param_map))
                .collect();
            Type::Tuple(elem_types)
        }
        TypeExpr::Wildcard { .. } | TypeExpr::Qualified { .. } => Type::Unit,
    }
}

/// Match a type pattern against a concrete type to bind type variables.
/// Ported from codegen's `bind_type_vars` (calls.rs).
fn bind_type_vars(pattern: &Type, actual: &Type, bindings: &mut HashMap<TypeVarId, Type>) -> bool {
    match (pattern, actual) {
        (Type::Var(id), _) => {
            bindings.entry(*id).or_insert_with(|| actual.clone());
            true
        }
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) => {
            p_name == a_name
                && p_args.len() == a_args.len()
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
            p_params.len() == a_params.len()
                && p_params
                    .iter()
                    .zip(a_params.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
                && bind_type_vars(p_ret, a_ret, bindings)
        }
        (Type::Tuple(p_elems), Type::Tuple(a_elems)) => {
            p_elems.len() == a_elems.len()
                && p_elems
                    .iter()
                    .zip(a_elems.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        (Type::Own(p), Type::Own(a)) => bind_type_vars(p, a, bindings),
        (Type::Own(p), a) | (a, Type::Own(p)) => bind_type_vars(p, a, bindings),
        (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
            bind_type_vars(p_ctor, a_ctor, bindings)
                && p_args.len() == a_args.len()
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        _ => pattern == actual,
    }
}

/// Prepend N Dict params to a function type.
fn prepend_n_dicts(n: usize, ty: &Type) -> Type {
    if n == 0 {
        return ty.clone();
    }
    match ty {
        Type::Fn(params, ret) => {
            let mut new_params = vec![Type::Named("Dict".to_string(), vec![]); n];
            new_params.extend(params.iter().cloned());
            Type::Fn(new_params, ret.clone())
        }
        other => other.clone(),
    }
}

/// Prepend Dict params to a function type if it has trait constraints.
fn prepend_dict_params(
    name: &str,
    fn_constraints: &HashMap<String, Vec<(String, TypeVarId)>>,
    ty: &Type,
) -> Type {
    let dict_count = fn_constraints
        .get(name)
        .map(|c| c.len())
        .unwrap_or(0);
    prepend_n_dicts(dict_count, ty)
}

