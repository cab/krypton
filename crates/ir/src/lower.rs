use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use krypton_parser::ast::{BinOp, Lit, Span, UnaryOp};
use krypton_typechecker::link_context::LinkContext;
use krypton_typechecker::typed_ast::{
    self as typed_ast, AutoCloseBinding, AutoCloseInfo, ExportedTypeKind, FnTypeEntry,
    QualifiedName, ResolvedBindingRef, ResolvedCallableRef, ResolvedConstructorRef,
    ResolvedTraitMethodRef, ResolvedTypeRef, ResolvedVariantRef, TraitName, TypedExpr,
    TypedExprKind, TypedFnDecl, TypedMatchArm, TypedModule, TypedPattern,
};
use krypton_typechecker::types::{self as types, Type, TypeScheme, TypeVarGen, TypeVarId};

use crate::Type as IrType;
use crate::pass::IrPass;
use crate::{
    Atom, CanonicalRef, Expr, ExprKind, ExternCallKind, ExternFnDef, ExternTarget, ExternTraitBridge,
    ExternTraitDef, ExternTraitMethodDef, ExternTypeDef, FinallyClose, FnDef, FnId, FnIdentity,
    ImportedFnDef, InstanceDef, Literal, LocalSymbolKey, Module, ModulePath, PrimOp, SimpleExpr,
    SimpleExprKind, StructDef, SumTypeDef, SwitchBranch, TraitDef, TraitMethodDef, VarId,
    VariantDef,
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
    CompoundInAtom,
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
            LowerError::CompoundInAtom => write!(f, "compound expression in atom position"),
            LowerError::InternalError(s) => write!(f, "internal error: {s}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Helper: intermediate let-binding produced during ANF normalization
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct LetBinding {
    bind: VarId,
    ty: IrType,
    value: SimpleExpr,
}

/// Extracted info about a parameterized trait instance (for dict construction).
#[derive(Clone)]
struct ParamInstanceInfo {
    trait_name: TraitName,
    target_type: Type,
    type_var_ids: HashMap<String, TypeVarId>,
    constraints: Vec<(TraitName, String)>, // (trait_name, type_var_name)
    source_module: String,                 // module defining this instance
    target_type_name: String,              // for building CanonicalRef
}

/// Source info for all instances (concrete and parameterized), used to
/// resolve instance CanonicalRefs during GetDict emission.
struct InstanceSourceInfo {
    trait_name: TraitName,
    target_type: Type,            // TC type (may contain type vars)
    target_type_name: String,     // type_to_canonical_name output
    source_module: String,
}

// ---------------------------------------------------------------------------
// Pattern match compilation types
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct ClausePayload {
    guard: Option<Box<TypedExpr>>,
    body: TypedExpr,
}

/// A clause in the pattern matrix: a structural row plus shared RHS payload.
#[derive(Clone)]
struct Clause {
    patterns: Vec<TypedPattern>,
    payload: Rc<ClausePayload>,
    /// Bindings accumulated during specialization for Var patterns that were
    /// expanded to wildcards. Each entry is (name, scrutinee_atom, type).
    extra_bindings: Vec<(String, Atom, Type)>,
}

impl Clause {
    fn guard(&self) -> Option<&TypedExpr> {
        self.payload.guard.as_deref()
    }

    fn body(&self) -> &TypedExpr {
        &self.payload.body
    }

    fn span(&self) -> Span {
        self.payload.body.span
    }
}

/// What kind of head constructors appear in a column.
enum ColumnKind {
    Constructor,
    Literal,
    Tuple(usize),
    Struct(String),
}

/// Check if a pattern is a wildcard or variable (always matches).
fn is_wildcard_or_var(pat: &TypedPattern) -> bool {
    matches!(
        pat,
        TypedPattern::Wildcard { .. }
            | TypedPattern::Var { .. }
            | TypedPattern::Lit {
                value: Lit::Unit,
                ..
            }
    )
}

/// Flatten or-patterns in a specific column, expanding each clause with an Or pattern
/// into multiple clauses (one per alternative). All other columns are preserved.
fn flatten_or_at_column(clauses: Vec<Clause>, col: usize) -> Vec<Clause> {
    let mut result = Vec::new();
    for clause in clauses {
        if col < clause.patterns.len() {
            if let TypedPattern::Or { alternatives, .. } = &clause.patterns[col] {
                for alt in alternatives {
                    let mut new_pats = clause.patterns.clone();
                    new_pats[col] = alt.clone();
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                continue;
            }
        }
        result.push(clause);
    }
    result
}

/// Get the type annotation from a pattern.
fn pattern_type(pat: &TypedPattern) -> Type {
    match pat {
        TypedPattern::Wildcard { ty, .. }
        | TypedPattern::Var { ty, .. }
        | TypedPattern::Constructor { ty, .. }
        | TypedPattern::Lit { ty, .. }
        | TypedPattern::Tuple { ty, .. }
        | TypedPattern::Or { ty, .. }
        | TypedPattern::StructPat { ty, .. } => ty.clone(),
    }
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
            name, value, body, ..
        } => {
            free_vars_inner(value, bound, free, seen);
            if let Some(body) = body {
                let mut inner_bound = bound.clone();
                inner_bound.insert(name.clone());
                free_vars_inner(body, &inner_bound, free, seen);
            }
        }
        TypedExprKind::Do(exprs) => {
            let mut do_bound = bound.clone();
            for e in exprs {
                free_vars_inner(e, &do_bound, free, seen);
                // Let with no body introduces a binding for subsequent exprs
                if let TypedExprKind::Let {
                    name, body: None, ..
                } = &e.kind
                {
                    do_bound.insert(name.clone());
                }
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
                if let Some(guard) = &arm.guard {
                    free_vars_inner(guard, &inner_bound, free, seen);
                }
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
        TypedPattern::Or { alternatives, .. } => {
            if let Some(first) = alternatives.first() {
                collect_pattern_bindings(first, bound);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Expression-kind detection (on TypedExpr, before IR lowering)
// ---------------------------------------------------------------------------

/// Walk a TypedExpr tree and return true if any node matches the predicate.
fn contains_expr_kind(expr: &TypedExpr, pred: &dyn Fn(&TypedExprKind) -> bool) -> bool {
    if pred(&expr.kind) {
        return true;
    }
    match &expr.kind {
        TypedExprKind::Lit(_) | TypedExprKind::Var(_) => false,
        TypedExprKind::App { func, args } => {
            contains_expr_kind(func, pred) || args.iter().any(|a| contains_expr_kind(a, pred))
        }
        TypedExprKind::TypeApp { expr: inner, .. }
        | TypedExprKind::UnaryOp { operand: inner, .. }
        | TypedExprKind::FieldAccess { expr: inner, .. }
        | TypedExprKind::QuestionMark { expr: inner, .. } => contains_expr_kind(inner, pred),
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            contains_expr_kind(lhs, pred) || contains_expr_kind(rhs, pred)
        }
        TypedExprKind::If { cond, then_, else_ } => {
            contains_expr_kind(cond, pred)
                || contains_expr_kind(then_, pred)
                || contains_expr_kind(else_, pred)
        }
        TypedExprKind::Let { value, body, .. } => {
            contains_expr_kind(value, pred)
                || body
                    .as_deref()
                    .map_or(false, |b| contains_expr_kind(b, pred))
        }
        TypedExprKind::Do(exprs) => exprs.iter().any(|e| contains_expr_kind(e, pred)),
        TypedExprKind::Lambda { .. } => false, // don't cross lambda boundaries
        TypedExprKind::Match { scrutinee, arms } => {
            contains_expr_kind(scrutinee, pred)
                || arms.iter().any(|a| contains_expr_kind(&a.body, pred))
        }
        TypedExprKind::StructLit { fields, .. } => {
            fields.iter().any(|(_, e)| contains_expr_kind(e, pred))
        }
        TypedExprKind::StructUpdate { base, fields } => {
            contains_expr_kind(base, pred)
                || fields.iter().any(|(_, e)| contains_expr_kind(e, pred))
        }
        TypedExprKind::Tuple(elems) | TypedExprKind::VecLit(elems) => {
            elems.iter().any(|e| contains_expr_kind(e, pred))
        }
        TypedExprKind::Recur(args) => args.iter().any(|a| contains_expr_kind(a, pred)),
        TypedExprKind::LetPattern { value, body, .. } => {
            contains_expr_kind(value, pred)
                || body
                    .as_deref()
                    .map_or(false, |b| contains_expr_kind(b, pred))
        }
    }
}

fn contains_recur(expr: &TypedExpr) -> bool {
    contains_expr_kind(expr, &|kind| matches!(kind, TypedExprKind::Recur(_)))
}

fn contains_question_mark(expr: &TypedExpr) -> bool {
    contains_expr_kind(expr, &|kind| {
        matches!(kind, TypedExprKind::QuestionMark { .. })
    })
}

// ---------------------------------------------------------------------------
// Referenced-var collection (on lowered IR Expr)
// ---------------------------------------------------------------------------

/// Collect all VarIds referenced in an IR expression tree.
fn referenced_vars_in_expr(expr: &Expr) -> HashSet<VarId> {
    let mut vars = HashSet::new();
    referenced_vars_walk(expr, &mut vars);
    vars
}

fn referenced_vars_walk(expr: &Expr, vars: &mut HashSet<VarId>) {
    match &expr.kind {
        ExprKind::Atom(atom) => referenced_vars_atom(atom, vars),
        ExprKind::Let {
            bind: _,
            ty: _,
            value,
            body,
        } => {
            referenced_vars_simple(value, vars);
            referenced_vars_walk(body, vars);
        }
        ExprKind::LetRec { bindings, body } => {
            for (_, _, _, captures) in bindings {
                for atom in captures {
                    referenced_vars_atom(atom, vars);
                }
            }
            referenced_vars_walk(body, vars);
        }
        ExprKind::LetJoin {
            name: _,
            params: _,
            join_body,
            body,
            is_recur: _,
        } => {
            referenced_vars_walk(join_body, vars);
            referenced_vars_walk(body, vars);
        }
        ExprKind::Jump { target: _, args } => {
            for atom in args {
                referenced_vars_atom(atom, vars);
            }
        }
        ExprKind::BoolSwitch {
            scrutinee,
            true_body,
            false_body,
        } => {
            referenced_vars_atom(scrutinee, vars);
            referenced_vars_walk(true_body, vars);
            referenced_vars_walk(false_body, vars);
        }
        ExprKind::Switch {
            scrutinee,
            branches,
            default,
        } => {
            referenced_vars_atom(scrutinee, vars);
            for branch in branches {
                referenced_vars_walk(&branch.body, vars);
            }
            if let Some(d) = default {
                referenced_vars_walk(d, vars);
            }
        }
    }
}

fn referenced_vars_simple(simple: &SimpleExpr, vars: &mut HashSet<VarId>) {
    match &simple.kind {
        SimpleExprKind::Call { func: _, args } | SimpleExprKind::TraitCall { args, .. } => {
            for atom in args {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::CallClosure { closure, args } => {
            referenced_vars_atom(closure, vars);
            for atom in args {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::MakeClosure { func: _, captures } => {
            for atom in captures {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::Construct {
            type_ref: _,
            fields,
        } => {
            for atom in fields {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::ConstructVariant { fields, .. } => {
            for atom in fields {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::Project { value, .. } => referenced_vars_atom(value, vars),
        SimpleExprKind::Tag { value } => referenced_vars_atom(value, vars),
        SimpleExprKind::MakeTuple { elements } => {
            for atom in elements {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::TupleProject { value, .. } => referenced_vars_atom(value, vars),
        SimpleExprKind::PrimOp { op: _, args } => {
            for atom in args {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::GetDict { .. } => {}
        SimpleExprKind::MakeDict { sub_dicts, .. } => {
            for atom in sub_dicts {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::MakeVec { elements, .. } => {
            for atom in elements {
                referenced_vars_atom(atom, vars);
            }
        }
        SimpleExprKind::Atom(atom) => referenced_vars_atom(atom, vars),
    }
}

fn referenced_vars_atom(atom: &Atom, vars: &mut HashSet<VarId>) {
    if let Atom::Var(id) = atom {
        vars.insert(*id);
    }
}

/// Pre-resolved auto-close info for a single binding.
struct ResolvedClose {
    trait_name: TraitName,
    binding_var: VarId,
    dict_bindings: Vec<LetBinding>,
    dict_atom: Atom,
}

fn expr_at(span: Span, ty: IrType, kind: ExprKind) -> Expr {
    Expr::new(span, ty, kind)
}

fn atom_expr_at(span: Span, ty: IrType, atom: Atom) -> Expr {
    Expr::new(span, ty, ExprKind::Atom(atom))
}

fn simple_at(span: Span, kind: SimpleExprKind) -> SimpleExpr {
    SimpleExpr::new(span, kind)
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
    /// Canonical qualified name → FnId for resolved callable lookup.
    callable_ids: HashMap<QualifiedName, FnId>,
    /// Resolved type ref → ordered fields with resolved types
    struct_fields: HashMap<ResolvedTypeRef, Vec<(String, Type)>>,
    /// Resolved variant ref → (tag, field_types)
    sum_variants: HashMap<ResolvedVariantRef, (u32, Vec<Type>)>,
    /// Cached type_params for private types (avoids double build_type_param_map)
    private_type_params: HashMap<String, Vec<TypeVarId>>,
    /// qualified name → [(trait_name, TypeVarId)] — required trait dicts
    fn_constraints: HashMap<QualifiedName, Vec<(TraitName, TypeVarId)>>,
    /// (trait_name, TypeVarId) → VarId — dict param variables for the current function
    dict_params: HashMap<(TraitName, TypeVarId), VarId>,
    /// qualified name → TypeScheme for resolving type var bindings at call sites
    fn_schemes: HashMap<QualifiedName, TypeScheme>,
    /// Instance defs for parameterized dict resolution:
    /// (trait_name, target_type, type_var_ids, constraints)
    param_instances: Vec<ParamInstanceInfo>,
    /// trait_name → (type_var_id, method_name → (param_types, return_type))
    trait_method_types: HashMap<TraitName, (TypeVarId, HashMap<String, (Vec<Type>, Type)>)>,
    /// trait_name → (method_name → Vec<(TraitName, TypeVarId)>) for method-level where constraints
    trait_method_constraints: HashMap<TraitName, HashMap<String, Vec<(TraitName, TypeVarId)>>>,
    /// Recursion depth counter for dict resolution (cycle detection)
    dict_depth: u32,
    /// Lifted lambda definitions accumulated during lowering
    lifted_fns: Vec<FnDef>,
    /// VarId → Type, populated at binding sites for capture type lookups
    var_types: HashMap<VarId, Type>,
    /// Join point for `recur` jumps in the current function
    recur_join: Option<(VarId, Vec<VarId>)>,
    /// Join point for `?` early returns in the current function
    early_return_join: Option<VarId>,
    /// Auto-close info from the typechecker
    auto_close: AutoCloseInfo,
    /// Names to track for fn_exit auto-close resolution; latest VarId per name
    fn_exit_track: HashSet<String>,
    /// Most recent VarId for tracked fn_exit names (survives pop_var)
    fn_exit_vars: HashMap<String, VarId>,
    /// Accumulated fn_exit_closes for the module (fn_name → resources to close on unwind)
    fn_exit_closes: HashMap<String, Vec<FinallyClose>>,
    /// Module path of the module being lowered (for filtering local dict refs).
    module_path: String,
    /// All known instances with source module and target type info,
    /// for resolving instance CanonicalRefs during GetDict/MakeDict emission.
    all_instances: Vec<InstanceSourceInfo>,
    /// (trait_local_name, canonical_type_name) → index into all_instances.
    /// Fast path for exact-match instance resolution; parameterized instances
    /// fall through to the linear structural scan.
    instance_exact_index: HashMap<(String, String), usize>,
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

    /// Build a CanonicalRef for a type from its ResolvedTypeRef.
    fn type_canonical_ref(&self, type_ref: &ResolvedTypeRef) -> CanonicalRef {
        CanonicalRef {
            module: ModulePath::new(type_ref.qualified_name.module_path.clone()),
            symbol: LocalSymbolKey::Type(type_ref.qualified_name.local_name.clone()),
        }
    }

    /// Build a CanonicalRef for a type from module_path + local_name.
    fn type_canonical_ref_from_parts(&self, module_path: &str, local_name: &str) -> CanonicalRef {
        CanonicalRef {
            module: ModulePath::new(module_path),
            symbol: LocalSymbolKey::Type(local_name.to_string()),
        }
    }

    /// Build a CanonicalRef for a type from its bare local name,
    /// looking up the defining module from sum_variants/struct_fields.
    fn type_canonical_ref_for_name(&self, local_name: &str) -> CanonicalRef {
        // Try sum_variants
        for variant_ref in self.sum_variants.keys() {
            if variant_ref.type_ref.qualified_name.local_name == local_name {
                return self.type_canonical_ref(&variant_ref.type_ref);
            }
        }
        // Try struct_fields
        for type_ref in self.struct_fields.keys() {
            if type_ref.qualified_name.local_name == local_name {
                return self.type_canonical_ref(type_ref);
            }
        }
        panic!(
            "ICE: type '{}' not found in sum_variants or struct_fields",
            local_name
        )
    }

    /// Build a CanonicalRef for an instance from trait + type info.
    /// Resolve the CanonicalRef for an instance given a trait and concrete target type.
    /// First tries exact match by canonical type name, then structural match via
    /// bind_type_vars (for parameterized instances like `Convert[(a) -> Int]`).
    fn instance_canonical_ref(
        &self,
        trait_name: &TraitName,
        target_type: &Type,
    ) -> CanonicalRef {
        let ir_type: IrType = target_type.clone().into();
        let canonical_name = crate::canonical_type_name(&ir_type);

        // Fast path: exact match via pre-built index
        let key = (trait_name.local_name.clone(), canonical_name.clone());
        let matched = if let Some(&idx) = self.instance_exact_index.get(&key) {
            &self.all_instances[idx]
        } else {
            // Slow path: structural match for parameterized instances
            self.all_instances
                .iter()
                .filter(|info| info.trait_name == *trait_name)
                .find(|info| {
                    let mut bindings = HashMap::new();
                    bind_type_vars(&info.target_type, target_type, &mut bindings)
                })
                .unwrap_or_else(|| {
                    panic!(
                        "ICE: no instance source for {}[{}] — \
                         all_instances should contain all local + imported instances",
                        trait_name.local_name, canonical_name
                    )
                })
        };

        CanonicalRef {
            module: ModulePath::new(matched.source_module.clone()),
            symbol: LocalSymbolKey::Instance {
                trait_name: trait_name.local_name.clone(),
                target_type: matched.target_type_name.clone(),
            },
        }
    }

    fn push_var(&mut self, name: &str, id: VarId) {
        self.var_scope.entry(name.to_string()).or_default().push(id);
        if self.fn_exit_track.contains(name) {
            self.fn_exit_vars.insert(name.to_string(), id);
        }
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

    fn lookup_callable(&self, qn: &QualifiedName) -> Option<FnId> {
        self.callable_ids.get(qn).copied()
    }

    /// Emit close() calls for a list of AutoCloseBindings, wrapping `inner`.
    /// Resolves variable names and dicts from current scope.
    fn emit_close_calls(
        &mut self,
        bindings: &[AutoCloseBinding],
        inner: Expr,
    ) -> Result<Expr, LowerError> {
        let resolved = self.resolve_close_bindings(bindings)?;
        self.emit_resolved_close_calls(&resolved, inner)
    }

    /// Emit a close call for a shadowed binding, wrapping `body`.
    fn emit_shadow_close(
        &mut self,
        binding: &AutoCloseBinding,
        old_var: VarId,
        body: Expr,
    ) -> Result<Expr, LowerError> {
        let dict_ty = Type::Named(binding.type_name.clone(), vec![]);
        let trait_name = TraitName::core_resource();
        let (dict_bindings, dict_atom) = self.resolve_dict(&trait_name, &dict_ty)?;
        let unit_var = self.fresh_var();
        let close_expr = expr_at(
            body.span,
            body.ty.clone(),
            ExprKind::Let {
                bind: unit_var,
                ty: Type::Unit.into(),
                value: simple_at(
                    body.span,
                    SimpleExprKind::TraitCall {
                        trait_name,
                        method_name: "close".to_string(),
                        args: vec![dict_atom, Atom::Var(old_var)],
                    },
                ),
                body: Box::new(body),
            },
        );
        Ok(Self::wrap_bindings(dict_bindings, close_expr))
    }

    /// Pre-resolve AutoCloseBindings to VarIds and dict info.
    /// Checks both current var_scope and fn_exit_vars for variable lookup.
    fn resolve_close_bindings(
        &mut self,
        bindings: &[AutoCloseBinding],
    ) -> Result<Vec<ResolvedClose>, LowerError> {
        let trait_name = TraitName::core_resource();
        let mut resolved = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let binding_var = self
                .lookup_var(&binding.name)
                .or_else(|| self.fn_exit_vars.get(&binding.name).copied())
                .ok_or_else(|| {
                    LowerError::InternalError(format!(
                        "auto-close: variable '{}' not in scope",
                        binding.name
                    ))
                })?;
            let dict_ty = Type::Named(binding.type_name.clone(), vec![]);
            let (dict_bindings, dict_atom) = self.resolve_dict(&trait_name, &dict_ty)?;
            resolved.push(ResolvedClose {
                trait_name: trait_name.clone(),
                binding_var,
                dict_bindings,
                dict_atom,
            });
        }
        Ok(resolved)
    }

    /// Emit close calls from pre-resolved info, wrapping `inner`.
    fn emit_resolved_close_calls(
        &mut self,
        resolved: &[ResolvedClose],
        inner: Expr,
    ) -> Result<Expr, LowerError> {
        let mut result = inner;
        // Process in reverse: first binding becomes outermost let, so it's evaluated (closed) first — LIFO order
        for rc in resolved.iter().rev() {
            let unit_var = self.fresh_var();
            let close_expr = expr_at(
                result.span,
                result.ty.clone(),
                ExprKind::Let {
                    bind: unit_var,
                    ty: Type::Unit.into(),
                    value: simple_at(
                        result.span,
                        SimpleExprKind::TraitCall {
                            trait_name: rc.trait_name.clone(),
                            method_name: "close".to_string(),
                            args: vec![rc.dict_atom.clone(), Atom::Var(rc.binding_var)],
                        },
                    ),
                    body: Box::new(result),
                },
            );
            result = Self::wrap_bindings(rc.dict_bindings.clone(), close_expr);
        }
        Ok(result)
    }

    /// Walk tail positions of an expression and wrap each terminal Atom with close calls.
    fn wrap_tail_with_closes(
        &mut self,
        expr: Expr,
        resolved: &[ResolvedClose],
    ) -> Result<Expr, LowerError> {
        match expr.kind {
            ExprKind::Atom(_) => self.emit_resolved_close_calls(resolved, expr),
            ExprKind::Let {
                bind,
                ty,
                value,
                body,
            } => {
                let new_body = self.wrap_tail_with_closes(*body, resolved)?;
                Ok(expr_at(
                    value.span,
                    new_body.ty.clone(),
                    ExprKind::Let {
                        bind,
                        ty,
                        value,
                        body: Box::new(new_body),
                    },
                ))
            }
            ExprKind::LetRec {
                bindings: rec_bindings,
                body,
            } => {
                let new_body = self.wrap_tail_with_closes(*body, resolved)?;
                Ok(expr_at(
                    new_body.span,
                    new_body.ty.clone(),
                    ExprKind::LetRec {
                        bindings: rec_bindings,
                        body: Box::new(new_body),
                    },
                ))
            }
            ExprKind::LetJoin {
                name,
                params,
                join_body,
                body,
                is_recur,
            } => {
                let new_join_body = self.wrap_tail_with_closes(*join_body, resolved)?;
                let new_body = self.wrap_tail_with_closes(*body, resolved)?;
                Ok(expr_at(
                    new_body.span,
                    new_body.ty.clone(),
                    ExprKind::LetJoin {
                        name,
                        params,
                        join_body: Box::new(new_join_body),
                        body: Box::new(new_body),
                        is_recur,
                    },
                ))
            }
            ExprKind::BoolSwitch {
                scrutinee,
                true_body,
                false_body,
            } => {
                let new_true = self.wrap_tail_with_closes(*true_body, resolved)?;
                let new_false = self.wrap_tail_with_closes(*false_body, resolved)?;
                Ok(expr_at(
                    new_true.span,
                    new_true.ty.clone(),
                    ExprKind::BoolSwitch {
                        scrutinee,
                        true_body: Box::new(new_true),
                        false_body: Box::new(new_false),
                    },
                ))
            }
            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                let new_branches = branches
                    .into_iter()
                    .map(|br| {
                        let new_body = self.wrap_tail_with_closes(br.body, resolved)?;
                        Ok(SwitchBranch {
                            tag: br.tag,
                            bindings: br.bindings,
                            body: new_body,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                let new_default = match default {
                    Some(d) => Some(Box::new(self.wrap_tail_with_closes(*d, resolved)?)),
                    None => None,
                };
                let ty = new_branches
                    .first()
                    .map(|b| b.body.ty.clone())
                    .or_else(|| new_default.as_ref().map(|d| d.ty.clone()))
                    .ok_or_else(|| LowerError::InternalError(
                        "switch expression has no arms and no default".to_string(),
                    ))?;
                let span = new_branches
                    .first()
                    .map(|b| b.body.span)
                    .or_else(|| new_default.as_ref().map(|d| d.span))
                    .unwrap_or((0, 0));
                Ok(expr_at(
                    span,
                    ty,
                    ExprKind::Switch {
                        scrutinee,
                        branches: new_branches,
                        default: new_default,
                    },
                ))
            }
            ExprKind::Jump { .. } => {
                // Jump targets handle their own cleanup
                Ok(expr)
            }
        }
    }

    fn field_index(
        &self,
        type_ref: &ResolvedTypeRef,
        field_name: &str,
    ) -> Result<usize, LowerError> {
        let fields = self
            .struct_fields
            .get(type_ref)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_ref.qualified_name.to_string()))?;
        fields
            .iter()
            .position(|(n, _)| n == field_name)
            .ok_or_else(|| {
                LowerError::UnresolvedField(
                    type_ref.qualified_name.to_string(),
                    field_name.to_string(),
                )
            })
    }

    fn variant_info(
        &self,
        variant_ref: &ResolvedVariantRef,
    ) -> Result<(u32, Vec<Type>), LowerError> {
        self.sum_variants.get(variant_ref).cloned().ok_or_else(|| {
            LowerError::InternalError(format!(
                "unknown variant ref in lowering: {}.{}",
                variant_ref.type_ref.qualified_name, variant_ref.variant_name
            ))
        })
    }

    fn fallback_type_ref(&self, type_name: &str) -> Option<ResolvedTypeRef> {
        self.struct_fields
            .keys()
            .find(|type_ref| type_ref.qualified_name.local_name == type_name)
            .cloned()
            .or_else(|| {
                self.sum_variants.keys().find_map(|variant_ref| {
                    (variant_ref.type_ref.qualified_name.local_name == type_name)
                        .then(|| variant_ref.type_ref.clone())
                })
            })
    }

    fn fallback_variant_ref(&self, variant_name: &str) -> Option<ResolvedVariantRef> {
        self.sum_variants
            .keys()
            .find(|variant_ref| variant_ref.variant_name == variant_name)
            .cloned()
    }

    fn resolved_type_ref_from_type(&self, ty: &Type) -> Option<ResolvedTypeRef> {
        match ty {
            Type::Named(name, _) => self.fallback_type_ref(name),
            Type::Own(inner) => self.resolved_type_ref_from_type(inner),
            _ => None,
        }
    }

    // -----------------------------------------------------------------------
    // ANF helpers
    // -----------------------------------------------------------------------

    /// Wrap a sequence of let-bindings around an inner expression (right fold).
    fn wrap_bindings(bindings: Vec<LetBinding>, inner: Expr) -> Expr {
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

    /// Lower an expression to an Atom. If already atomic, return it directly.
    /// Otherwise lower to SimpleExpr, bind to a fresh VarId, emit a LetBinding.
    /// For compound expressions (If, Do), returns an error — callers should use
    /// lower_expr + inline_compound_let instead.
    fn lower_to_atom(&mut self, expr: &TypedExpr) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        match &expr.kind {
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
                type_args,
            } => {
                // For trait method values, use the outer (concrete) type from the TypeApp
                if let Some(trait_ref) = resolved_trait_method_ref(expr) {
                    let (bindings, simple) = self.lower_trait_method_as_value(
                        &trait_ref.trait_name,
                        &trait_ref.method_name,
                        &expr.ty,
                        type_args,
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
    fn lower_to_atom_then<F>(&mut self, expr: &TypedExpr, cont: F) -> Result<Expr, LowerError>
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
                let var = self.fresh_var();
                let body = cont(self, Atom::Var(var))?;
                Ok(self.inline_compound_let(var, expr.ty.clone(), compound, body))
            }
        }
    }

    /// Lower N expressions to atoms left-to-right, then call `cont` with all atoms.
    fn lower_atoms_then<F>(
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

    fn lower_variant_constructor_as_value(
        &mut self,
        name: &str,
        expr: &TypedExpr,
        type_qn: &QualifiedName,
        tag: u32,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        let (param_types, return_type) = match &expr.ty {
            Type::Fn(param_types, return_type) => {
                (param_types.clone(), return_type.as_ref().clone())
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
            params,
            return_type: return_type.into(),
            body,
        });
        self.fn_ids.insert(lifted_name, fn_id);

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
    fn lower_struct_constructor_as_value(
        &mut self,
        constructor_name: &str,
        type_qn: &QualifiedName,
        expr: &TypedExpr,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        let (param_types, return_type) = match &expr.ty {
            Type::Fn(param_types, return_type) => {
                (param_types.clone(), return_type.as_ref().clone())
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
            params,
            return_type: return_type.into(),
            body,
        });
        self.fn_ids.insert(lifted_name, fn_id);

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
                            let type_cref =
                                self.type_canonical_ref(&constructor_ref.type_ref);
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
                    let type_cref =
                        self.type_canonical_ref(&variant_ref.type_ref);
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
                    let Some(fn_id) = self.lookup_callable(&qn) else {
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
                type_args,
            } => {
                // For trait method values, use the outer (concrete) type from the TypeApp
                if let Some(trait_ref) = resolved_trait_method_ref(expr) {
                    return self.lower_trait_method_as_value(
                        &trait_ref.trait_name,
                        &trait_ref.method_name,
                        &expr.ty,
                        type_args,
                    );
                }
                if let Some((_binding_name, callable_ref)) = resolved_callable_ref(expr) {
                    // Constrained function reference with explicit type args
                    let qn = callable_qualified_name(callable_ref, &self.module_path);
                    if let Some(fn_id) = self.lookup_callable(&qn) {
                        // Functions without trait constraints have no entry
                        let constraints = self.fn_constraints.get(&qn).cloned().unwrap_or_default();
                        if !constraints.is_empty() {
                            return self.lower_constrained_fn_as_value(
                                &qn,
                                fn_id,
                                &constraints,
                                type_args,
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
            TypedExprKind::App { func, args } => self.lower_app(func, args),
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
            TypedExprKind::Recur(_) | TypedExprKind::QuestionMark { .. } => {
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
    // Expression lowering (produces full Expr trees)
    // -----------------------------------------------------------------------

    fn lower_expr(&mut self, expr: &TypedExpr) -> Result<Expr, LowerError> {
        match &expr.kind {
            TypedExprKind::Lit(lit) => Ok(atom_expr_at(
                expr.span,
                expr.ty.clone().into(),
                Atom::Lit(convert_lit(lit)),
            )),

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
                            let type_cref =
                                self.type_canonical_ref(&constructor_ref.type_ref);
                            if fields.is_empty() {
                                let var = self.fresh_var();
                                return Ok(expr_at(
                                    expr.span,
                                    expr.ty.clone().into(),
                                    ExprKind::Let {
                                        bind: var,
                                        ty: expr.ty.clone().into(),
                                        value: simple_at(
                                            expr.span,
                                            SimpleExprKind::ConstructVariant {
                                                type_ref: type_cref,
                                                variant: constructor_ref.constructor_name.clone(),
                                                tag,
                                                fields: vec![],
                                            },
                                        ),
                                        body: Box::new(atom_expr_at(
                                            expr.span,
                                            expr.ty.clone().into(),
                                            Atom::Var(var),
                                        )),
                                    },
                                ));
                            }
                            let (bindings, simple) = self.lower_variant_constructor_as_value(
                                &constructor_ref.constructor_name,
                                expr,
                                &constructor_ref.type_ref.qualified_name,
                                tag,
                            )?;
                            let var = self.fresh_var();
                            let mut result = expr_at(
                                expr.span,
                                expr.ty.clone().into(),
                                ExprKind::Let {
                                    bind: var,
                                    ty: expr.ty.clone().into(),
                                    value: simple,
                                    body: Box::new(atom_expr_at(
                                        expr.span,
                                        expr.ty.clone().into(),
                                        Atom::Var(var),
                                    )),
                                },
                            );
                            for b in bindings.into_iter().rev() {
                                result = expr_at(
                                    b.value.span,
                                    result.ty.clone(),
                                    ExprKind::Let {
                                        bind: b.bind,
                                        ty: b.ty,
                                        value: b.value,
                                        body: Box::new(result),
                                    },
                                );
                            }
                            return Ok(result);
                        }
                        typed_ast::ConstructorKind::Record => {
                            let (bindings, simple) = self.lower_struct_constructor_as_value(
                                &constructor_ref.constructor_name,
                                &constructor_ref.type_ref.qualified_name,
                                expr,
                            )?;
                            let var = self.fresh_var();
                            let mut result = expr_at(
                                expr.span,
                                expr.ty.clone().into(),
                                ExprKind::Let {
                                    bind: var,
                                    ty: expr.ty.clone().into(),
                                    value: simple,
                                    body: Box::new(atom_expr_at(
                                        expr.span,
                                        expr.ty.clone().into(),
                                        Atom::Var(var),
                                    )),
                                },
                            );
                            for b in bindings.into_iter().rev() {
                                result = expr_at(
                                    b.value.span,
                                    result.ty.clone(),
                                    ExprKind::Let {
                                        bind: b.bind,
                                        ty: b.ty,
                                        value: b.value,
                                        body: Box::new(result),
                                    },
                                );
                            }
                            return Ok(result);
                        }
                    }
                }
                if let Some(variant_ref) = self.fallback_variant_ref(name) {
                    let (tag, fields) = self.variant_info(&variant_ref)?;
                    let type_cref = self.type_canonical_ref(&variant_ref.type_ref);
                    if fields.is_empty() {
                        let var = self.fresh_var();
                        return Ok(expr_at(
                            expr.span,
                            expr.ty.clone().into(),
                            ExprKind::Let {
                                bind: var,
                                ty: expr.ty.clone().into(),
                                value: simple_at(
                                    expr.span,
                                    SimpleExprKind::ConstructVariant {
                                        type_ref: type_cref,
                                        variant: name.clone(),
                                        tag,
                                        fields: vec![],
                                    },
                                ),
                                body: Box::new(atom_expr_at(
                                    expr.span,
                                    expr.ty.clone().into(),
                                    Atom::Var(var),
                                )),
                            },
                        ));
                    }
                    let (bindings, simple) =
                        self.lower_variant_constructor_as_value(name, expr, &variant_ref.type_ref.qualified_name, tag)?;
                    let var = self.fresh_var();
                    let mut result = expr_at(
                        expr.span,
                        expr.ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: expr.ty.clone().into(),
                            value: simple,
                            body: Box::new(atom_expr_at(
                                expr.span,
                                expr.ty.clone().into(),
                                Atom::Var(var),
                            )),
                        },
                    );
                    for b in bindings.into_iter().rev() {
                        result = expr_at(
                            b.value.span,
                            result.ty.clone(),
                            ExprKind::Let {
                                bind: b.bind,
                                ty: b.ty,
                                value: b.value,
                                body: Box::new(result),
                            },
                        );
                    }
                    return Ok(result);
                }
                if let Some(type_ref) = self.fallback_type_ref(name) {
                    let (bindings, simple) = self.lower_struct_constructor_as_value(
                        name,
                        &type_ref.qualified_name,
                        expr,
                    )?;
                    let var = self.fresh_var();
                    let mut result = expr_at(
                        expr.span,
                        expr.ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: expr.ty.clone().into(),
                            value: simple,
                            body: Box::new(atom_expr_at(
                                expr.span,
                                expr.ty.clone().into(),
                                Atom::Var(var),
                            )),
                        },
                    );
                    for b in bindings.into_iter().rev() {
                        result = expr_at(
                            b.value.span,
                            result.ty.clone(),
                            ExprKind::Let {
                                bind: b.bind,
                                ty: b.ty,
                                value: b.value,
                                body: Box::new(result),
                            },
                        );
                    }
                    return Ok(result);
                }
                if let Some(id) = self.lookup_var(name) {
                    Ok(atom_expr_at(
                        expr.span,
                        expr.ty.clone().into(),
                        Atom::Var(id),
                    ))
                } else if let Some((_binding_name, callable_ref)) = resolved_callable_ref(expr) {
                    let qn = callable_qualified_name(callable_ref, &self.module_path);
                    let Some(fn_id) = self.lookup_callable(&qn) else {
                        return Err(LowerError::UnresolvedVar(name.to_string()));
                    };
                    // Top-level function used as value
                    let var = self.fresh_var();
                    Ok(expr_at(
                        expr.span,
                        expr.ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: expr.ty.clone().into(),
                            value: simple_at(
                                expr.span,
                                SimpleExprKind::MakeClosure {
                                    func: fn_id,
                                    captures: vec![],
                                },
                            ),
                            body: Box::new(atom_expr_at(
                                expr.span,
                                expr.ty.clone().into(),
                                Atom::Var(var),
                            )),
                        },
                    ))
                } else if let Some(trait_ref) = resolved_trait_method_ref(expr) {
                    // Trait method used as value
                    let (bindings, simple) = self.lower_trait_method_as_value(
                        &trait_ref.trait_name,
                        &trait_ref.method_name,
                        &expr.ty,
                        &[],
                    )?;
                    let var = self.fresh_var();
                    let mut result = expr_at(
                        expr.span,
                        expr.ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: expr.ty.clone().into(),
                            value: simple,
                            body: Box::new(atom_expr_at(
                                expr.span,
                                expr.ty.clone().into(),
                                Atom::Var(var),
                            )),
                        },
                    );
                    // Wrap dict bindings
                    for b in bindings.into_iter().rev() {
                        result = expr_at(
                            b.value.span,
                            result.ty.clone(),
                            ExprKind::Let {
                                bind: b.bind,
                                ty: b.ty,
                                value: b.value,
                                body: Box::new(result),
                            },
                        );
                    }
                    Ok(result)
                } else {
                    Err(LowerError::UnresolvedVar(name.clone()))
                }
            }

            TypedExprKind::TypeApp {
                expr: inner,
                type_args,
            } => {
                // For trait method values, use the outer (concrete) type from the TypeApp
                if let Some(trait_ref) = resolved_trait_method_ref(expr) {
                    let (bindings, simple) = self.lower_trait_method_as_value(
                        &trait_ref.trait_name,
                        &trait_ref.method_name,
                        &expr.ty,
                        type_args,
                    )?;
                    let var = self.fresh_var();
                    let mut result = expr_at(
                        expr.span,
                        expr.ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: expr.ty.clone().into(),
                            value: simple,
                            body: Box::new(atom_expr_at(
                                expr.span,
                                expr.ty.clone().into(),
                                Atom::Var(var),
                            )),
                        },
                    );
                    for b in bindings.into_iter().rev() {
                        result = expr_at(
                            b.value.span,
                            result.ty.clone(),
                            ExprKind::Let {
                                bind: b.bind,
                                ty: b.ty,
                                value: b.value,
                                body: Box::new(result),
                            },
                        );
                    }
                    return Ok(result);
                }
                self.lower_expr(inner)
            }

            TypedExprKind::Let { name, value, body } => {
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

                self.push_var(name, bind);
                let mut body_expr = if let Some(body) = body {
                    self.lower_expr(body)?
                } else {
                    // Let without body — the value IS the result
                    atom_expr_at(value.span, value.ty.clone().into(), Atom::Var(bind))
                };

                // Emit close for the shadowed binding (wraps the body, runs before body)
                if let (Some(binding), Some(old_id)) = (&shadow_close, old_var) {
                    body_expr = self.emit_shadow_close(binding, old_id, body_expr)?;
                }

                self.pop_var(name);

                match lowered_value {
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
                        // Value is a compound expression (If, Do, etc.)
                        // We need to inline the value expression and bind its result
                        Ok(self.inline_compound_let(bind, value.ty.clone(), value_expr, body_expr))
                    }
                }
            }

            TypedExprKind::Do(exprs) => self.lower_do(exprs, &expr.ty),

            TypedExprKind::If { cond, then_, else_ } => {
                let result_ty = expr.ty.clone();
                self.lower_to_atom_then(cond, |ctx, cond_atom| {
                    let then_body = ctx.lower_expr(then_)?;
                    let else_body = ctx.lower_expr(else_)?;
                    Ok(expr_at(
                        expr.span,
                        result_ty.into(),
                        ExprKind::BoolSwitch {
                            scrutinee: cond_atom,
                            true_body: Box::new(then_body),
                            false_body: Box::new(else_body),
                        },
                    ))
                })
            }

            TypedExprKind::App { func, args } => self.lower_app_expr(func, args, &expr.ty),

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

            TypedExprKind::BinaryOp {
                op: op @ (BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge),
                lhs,
                rhs,
            } => self.lower_trait_comparison(op, lhs, rhs, &expr.ty),

            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let lhs_ty = strip_own(&lhs.ty).clone();
                if let Ok(prim_op) = resolve_binop(op, &lhs_ty) {
                    // Primitive type — keep PrimOp path
                    let result_ty = expr.ty.clone();
                    self.lower_to_atom_then(lhs, |ctx, l| {
                        ctx.lower_to_atom_then(rhs, |ctx, r| {
                            let var = ctx.fresh_var();
                            let ty = result_ty;
                            Ok(expr_at(
                                expr.span,
                                ty.clone().into(),
                                ExprKind::Let {
                                    bind: var,
                                    ty: ty.clone().into(),
                                    value: simple_at(
                                        expr.span,
                                        SimpleExprKind::PrimOp {
                                            op: prim_op,
                                            args: vec![l, r],
                                        },
                                    ),
                                    body: Box::new(atom_expr_at(
                                        expr.span,
                                        ty.into(),
                                        Atom::Var(var),
                                    )),
                                },
                            ))
                        })
                    })
                } else {
                    // User-defined type — trait dispatch
                    self.lower_trait_arithmetic(op, lhs, rhs, &expr.ty)
                }
            }

            TypedExprKind::UnaryOp { op, operand } => {
                let operand_ty = strip_own(&operand.ty).clone();
                if let Ok(prim_op) = resolve_unaryop(op, &operand_ty) {
                    // Primitive type — keep PrimOp path
                    let result_ty = expr.ty.clone();
                    self.lower_to_atom_then(operand, |ctx, atom| {
                        let var = ctx.fresh_var();
                        let ty = result_ty;
                        Ok(expr_at(
                            expr.span,
                            ty.clone().into(),
                            ExprKind::Let {
                                bind: var,
                                ty: ty.clone().into(),
                                value: simple_at(
                                    expr.span,
                                    SimpleExprKind::PrimOp {
                                        op: prim_op,
                                        args: vec![atom],
                                    },
                                ),
                                body: Box::new(atom_expr_at(expr.span, ty.into(), Atom::Var(var))),
                            },
                        ))
                    })
                } else {
                    // User-defined type — trait dispatch
                    self.lower_trait_unary(op, operand, &expr.ty)
                }
            }

            TypedExprKind::Tuple(elems) => {
                let result_ty = expr.ty.clone();
                self.lower_atoms_then(elems, vec![], |ctx, atoms| {
                    let var = ctx.fresh_var();
                    let ty = result_ty;
                    Ok(expr_at(
                        expr.span,
                        ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                expr.span,
                                SimpleExprKind::MakeTuple { elements: atoms },
                            ),
                            body: Box::new(atom_expr_at(expr.span, ty.into(), Atom::Var(var))),
                        },
                    ))
                })
            }

            TypedExprKind::StructLit {
                name,
                fields,
                resolved_type_ref,
            } => self.lower_struct_lit_expr(name, fields, resolved_type_ref.as_ref(), &expr.ty),

            TypedExprKind::FieldAccess {
                expr: base,
                field,
                resolved_type_ref,
            } => {
                let result_ty = expr.ty.clone();
                let base_ty = base.ty.clone();
                let field = field.clone();
                let type_ref = resolved_type_ref
                    .clone()
                    .or_else(|| self.resolved_type_ref_from_type(&base_ty));
                self.lower_to_atom_then(base, |ctx, base_atom| {
                    let type_ref = type_ref.clone().ok_or_else(|| {
                        LowerError::InternalError(format!(
                            "FieldAccess on non-named type: {:?}",
                            base_ty
                        ))
                    })?;
                    let idx = ctx.field_index(&type_ref, &field)?;
                    let var = ctx.fresh_var();
                    let ty = result_ty;
                    Ok(expr_at(
                        expr.span,
                        ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                expr.span,
                                SimpleExprKind::Project {
                                    value: base_atom,
                                    field_index: idx,
                                },
                            ),
                            body: Box::new(atom_expr_at(expr.span, ty.into(), Atom::Var(var))),
                        },
                    ))
                })
            }

            TypedExprKind::StructUpdate { base, fields } => {
                self.lower_struct_update_expr(base, fields, &expr.ty)
            }

            TypedExprKind::Lambda { params, body } => {
                let (bindings, simple) = self.lower_lambda(params, body, &expr.ty)?;
                let var = self.fresh_var();
                let ty = expr.ty.clone();
                let mut all_bindings = bindings;
                all_bindings.push(LetBinding {
                    bind: var,
                    ty: ty.clone().into(),
                    value: simple,
                });
                let inner = atom_expr_at(expr.span, ty.into(), Atom::Var(var));
                Ok(Self::wrap_bindings(all_bindings, inner))
            }
            TypedExprKind::Match { scrutinee, arms } => self.lower_match(scrutinee, arms, &expr.ty),

            TypedExprKind::LetPattern {
                pattern,
                value,
                body,
            } => self.lower_let_pattern(pattern, value, body.as_deref(), &expr.ty),

            TypedExprKind::Recur(args) => {
                let (join_name, _join_params) = self.recur_join.clone().ok_or_else(|| {
                    LowerError::InternalError(
                        "recur outside of a recur-enabled function".to_string(),
                    )
                })?;
                let result_ty = expr.ty.clone();
                let recur_close_bindings = self.auto_close.recur_closes.get(&expr.span).cloned();
                self.lower_atoms_then(args, vec![], |ctx, jump_args| {
                    let mut jump_expr = expr_at(
                        expr.span,
                        result_ty.into(),
                        ExprKind::Jump {
                            target: join_name,
                            args: jump_args,
                        },
                    );
                    if let Some(ref close_bindings) = recur_close_bindings {
                        jump_expr = ctx.emit_close_calls(close_bindings, jump_expr)?;
                    }
                    Ok(jump_expr)
                })
            }

            TypedExprKind::QuestionMark {
                expr: inner,
                is_option,
            } => {
                let early_return = self.early_return_join.ok_or_else(|| {
                    LowerError::InternalError("? outside of a ?-enabled function".to_string())
                })?;
                let is_option = *is_option;
                let inner_full_ty = inner.ty.clone();
                let inner_stripped_ty = strip_own(&inner.ty).clone();
                let early_close_bindings = self.auto_close.early_returns.get(&expr.span).cloned();
                self.lower_to_atom_then(inner, |ctx, scrut_atom| {
                    let success_var = ctx.fresh_var();
                    let switch = if is_option {
                        // Option[T]: Some#0(T) | None#1
                        let t = match &inner_stripped_ty {
                            Type::Named(_, args) if !args.is_empty() => args[0].clone(),
                            _ => return Err(LowerError::InternalError(format!(
                                "? operator: expected Option/Own(Option) type, got {inner_stripped_ty:?}"
                            ))),
                        };
                        let wrap_var = ctx.fresh_var();
                        let mut none_jump = expr_at(
                            expr.span,
                            inner_full_ty.clone().into(),
                            ExprKind::Jump {
                                target: early_return,
                                args: vec![Atom::Var(wrap_var)],
                            },
                        );
                        if let Some(ref close_bindings) = early_close_bindings {
                            none_jump = ctx.emit_close_calls(close_bindings, none_jump)?;
                        }
                        expr_at(
                            expr.span,
                            t.clone().into(),
                            ExprKind::Switch {
                                scrutinee: scrut_atom,
                                branches: vec![
                                    SwitchBranch {
                                        tag: 0,
                                        bindings: vec![(success_var, t.clone().into())],
                                        body: atom_expr_at(
                                            expr.span,
                                            t.into(),
                                            Atom::Var(success_var),
                                        ),
                                    },
                                    SwitchBranch {
                                        tag: 1,
                                        bindings: vec![],
                                        body: expr_at(
                                            expr.span,
                                            inner_full_ty.clone().into(),
                                            ExprKind::Let {
                                                bind: wrap_var,
                                                ty: inner_full_ty.clone().into(),
                                                value: simple_at(
                                                    expr.span,
                                                    SimpleExprKind::ConstructVariant {
                                                        type_ref: ctx.type_canonical_ref_for_name("Option"),
                                                        variant: "None".to_string(),
                                                        tag: 1,
                                                        fields: vec![],
                                                    },
                                                ),
                                                body: Box::new(none_jump),
                                            },
                                        ),
                                    },
                                ],
                                default: None,
                            },
                        )
                    } else {
                        // Result[E, T]: Ok#0(T) | Err#1(E)
                        let (err_ty, ok_ty) = match &inner_stripped_ty {
                            Type::Named(_, args) if args.len() >= 2 => {
                                (args[0].clone(), args[1].clone())
                            }
                            _ => return Err(LowerError::InternalError(format!(
                                "? operator: expected Result type with 2+ type args, got {inner_stripped_ty:?}"
                            ))),
                        };
                        let err_var = ctx.fresh_var();
                        let wrap_var = ctx.fresh_var();
                        let mut err_jump = expr_at(
                            expr.span,
                            inner_full_ty.clone().into(),
                            ExprKind::Jump {
                                target: early_return,
                                args: vec![Atom::Var(wrap_var)],
                            },
                        );
                        if let Some(ref close_bindings) = early_close_bindings {
                            err_jump = ctx.emit_close_calls(close_bindings, err_jump)?;
                        }
                        expr_at(
                            expr.span,
                            ok_ty.clone().into(),
                            ExprKind::Switch {
                                scrutinee: scrut_atom,
                                branches: vec![
                                    SwitchBranch {
                                        tag: 0,
                                        bindings: vec![(success_var, ok_ty.clone().into())],
                                        body: atom_expr_at(
                                            expr.span,
                                            ok_ty.into(),
                                            Atom::Var(success_var),
                                        ),
                                    },
                                    SwitchBranch {
                                        tag: 1,
                                        bindings: vec![(err_var, err_ty.into())],
                                        body: expr_at(
                                            expr.span,
                                            inner_full_ty.clone().into(),
                                            ExprKind::Let {
                                                bind: wrap_var,
                                                ty: inner_full_ty.clone().into(),
                                                value: simple_at(
                                                    expr.span,
                                                    SimpleExprKind::ConstructVariant {
                                                        type_ref: ctx.type_canonical_ref_for_name("Result"),
                                                        variant: "Err".to_string(),
                                                        tag: 1,
                                                        fields: vec![Atom::Var(err_var)],
                                                    },
                                                ),
                                                body: Box::new(err_jump),
                                            },
                                        ),
                                    },
                                ],
                                default: None,
                            },
                        )
                    };
                    Ok(switch)
                })
            }

            TypedExprKind::VecLit(elems) => {
                let result_ty = expr.ty.clone();
                let element_type = extract_vec_element_type(&expr.ty)?;
                self.lower_atoms_then(elems, vec![], |ctx, atoms| {
                    let var = ctx.fresh_var();
                    let ty = result_ty;
                    Ok(expr_at(
                        expr.span,
                        ty.clone().into(),
                        ExprKind::Let {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                expr.span,
                                SimpleExprKind::MakeVec {
                                    element_type: element_type.into(),
                                    elements: atoms,
                                },
                            ),
                            body: Box::new(atom_expr_at(expr.span, ty.into(), Atom::Var(var))),
                        },
                    ))
                })
            }
        }
    }

    // -----------------------------------------------------------------------
    // Compound expression helpers
    // -----------------------------------------------------------------------

    /// Try to lower a value expression as either a SimpleExpr (for direct Let binding)
    /// or as a full Expr (for compound expressions like If, Do, nested Let, or atoms).
    fn try_lower_as_simple(&mut self, expr: &TypedExpr) -> Result<LoweredValue, LowerError> {
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
            | TypedExprKind::Recur(_)
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
    fn inline_compound_let(
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

    // -----------------------------------------------------------------------
    // Pattern match compilation (clause-matrix algorithm)
    // -----------------------------------------------------------------------

    /// Lower a match expression into a Switch decision tree.
    fn lower_match(
        &mut self,
        scrutinee: &TypedExpr,
        arms: &[TypedMatchArm],
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let result_ty = result_ty.clone();
        let arms = arms.to_vec();
        self.lower_to_atom_then(scrutinee, |ctx, scrut_atom| {
            let clauses: Vec<Clause> = arms
                .iter()
                .flat_map(|arm| {
                    let payload = Rc::new(ClausePayload {
                        guard: arm.guard.clone(),
                        body: arm.body.clone(),
                    });
                    match &arm.pattern {
                        TypedPattern::Or { alternatives, .. } => alternatives
                            .iter()
                            .map(|alt| Clause {
                                patterns: vec![alt.clone()],
                                payload: Rc::clone(&payload),
                                extra_bindings: vec![],
                            })
                            .collect::<Vec<_>>(),
                        _ => vec![Clause {
                            patterns: vec![arm.pattern.clone()],
                            payload,
                            extra_bindings: vec![],
                        }],
                    }
                })
                .collect();
            ctx.compile_clauses(vec![scrut_atom], clauses, &result_ty)
        })
    }

    /// Lower a let-pattern binding as an irrefutable single-arm match.
    fn lower_let_pattern(
        &mut self,
        pattern: &TypedPattern,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let result_ty = result_ty.clone();
        let pattern = pattern.clone();
        let body_expr = if let Some(body) = body {
            body.clone()
        } else {
            TypedExpr {
                kind: TypedExprKind::Lit(Lit::Unit),
                ty: Type::Unit,
                span: (0, 0),
                resolved_ref: None,
            }
        };

        self.lower_to_atom_then(value, |ctx, val_atom| {
            let clause = Clause {
                patterns: vec![pattern],
                payload: Rc::new(ClausePayload {
                    guard: None,
                    body: body_expr,
                }),
                extra_bindings: vec![],
            };
            ctx.compile_clauses(vec![val_atom], vec![clause], &result_ty)
        })
    }

    /// Core clause-matrix compilation.
    ///
    /// `scrutinees` - atoms to match against (one per column)
    /// `clauses` - rows of patterns + body
    /// `result_ty` - type of the overall match expression
    fn compile_clauses(
        &mut self,
        scrutinees: Vec<Atom>,
        clauses: Vec<Clause>,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Base case: no clauses — unreachable (typechecker ensures exhaustiveness)
        if clauses.is_empty() {
            // Emit a unit atom as a placeholder for unreachable code
            return Ok(atom_expr_at(
                (0, 0),
                result_ty.clone().into(),
                Atom::Lit(Literal::Unit),
            ));
        }

        // Base case: first row is all wildcards/vars — it matches
        if clauses[0].patterns.iter().all(is_wildcard_or_var) {
            if clauses[0].guard().is_some() {
                return self.compile_guarded_clause(scrutinees, clauses, result_ty);
            }
            return self.bind_and_lower_body(&scrutinees, &clauses[0]);
        }

        // Pick the first column with a non-wildcard pattern
        let col = self.pick_column(&clauses);

        // Flatten any or-patterns at the picked column before classification
        let clauses = flatten_or_at_column(clauses, col);

        // Determine what kind of head constructors appear in this column
        let head_kind = self.classify_column(&clauses, col);

        match head_kind {
            ColumnKind::Constructor => {
                self.compile_constructor_column(&scrutinees, clauses, col, result_ty)
            }
            ColumnKind::Literal => {
                self.compile_literal_column(&scrutinees, clauses, col, result_ty)
            }
            ColumnKind::Tuple(arity) => {
                self.compile_tuple_column(&scrutinees, clauses, col, result_ty, arity)
            }
            ColumnKind::Struct(name) => {
                self.compile_struct_column(&scrutinees, clauses, col, result_ty, &name)
            }
        }
    }

    /// Bind variables from an all-wildcard/var row, then lower the body.
    fn bind_and_lower_body(
        &mut self,
        scrutinees: &[Atom],
        clause: &Clause,
    ) -> Result<Expr, LowerError> {
        let mut bound_names = Vec::new();
        let mut lit_bindings: Vec<LetBinding> = Vec::new();

        // First, bind extra_bindings accumulated from specialization of Var patterns
        for (name, atom, ty) in &clause.extra_bindings {
            match atom {
                Atom::Var(id) => {
                    self.var_types.insert(*id, ty.clone());
                    self.push_var(name, *id);
                    bound_names.push(name.clone());
                }
                Atom::Lit(lit) => {
                    let var = self.fresh_var();
                    self.var_types.insert(var, ty.clone());
                    self.push_var(name, var);
                    bound_names.push(name.clone());
                    lit_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(
                            clause.span(),
                            SimpleExprKind::Atom(crate::Atom::Lit(lit.clone())),
                        ),
                    });
                }
            }
        }

        // Push variable bindings from the remaining pattern row
        for (pat, scrut) in clause.patterns.iter().zip(scrutinees.iter()) {
            if let TypedPattern::Var { name, ty, .. } = pat {
                match scrut {
                    Atom::Var(scrut_id) => {
                        self.var_types.insert(*scrut_id, ty.clone());
                        self.push_var(name, *scrut_id);
                        bound_names.push(name.clone());
                    }
                    Atom::Lit(lit) => {
                        let var = self.fresh_var();
                        self.var_types.insert(var, ty.clone());
                        self.push_var(name, var);
                        bound_names.push(name.clone());
                        lit_bindings.push(LetBinding {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                clause.span(),
                                SimpleExprKind::Atom(crate::Atom::Lit(lit.clone())),
                            ),
                        });
                    }
                }
            }
        }

        let body_expr = self.lower_expr(clause.body())?;

        // Pop variable bindings
        for name in bound_names.iter().rev() {
            self.pop_var(name);
        }

        // Wrap with literal bindings if any
        if lit_bindings.is_empty() {
            Ok(body_expr)
        } else {
            Ok(Self::wrap_bindings(lit_bindings, body_expr))
        }
    }

    /// Compile a guarded clause: bind vars, evaluate guard, BoolSwitch to body or fallthrough.
    fn compile_guarded_clause(
        &mut self,
        scrutinees: Vec<Atom>,
        clauses: Vec<Clause>,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Extract what we need from the first clause before splitting the vec
        let mut clauses = clauses;
        let first = clauses.remove(0);
        let span = first.span();
        let payload = Rc::clone(&first.payload);
        let extra_bindings = first.extra_bindings;
        let patterns = first.patterns;
        let remaining = clauses; // rest after removing first

        // Bind variables (same logic as bind_and_lower_body)
        let mut bound_names = Vec::new();
        let mut lit_bindings: Vec<LetBinding> = Vec::new();

        for (name, atom, ty) in &extra_bindings {
            match atom {
                Atom::Var(id) => {
                    self.var_types.insert(*id, ty.clone());
                    self.push_var(name, *id);
                    bound_names.push(name.clone());
                }
                Atom::Lit(lit) => {
                    let var = self.fresh_var();
                    self.var_types.insert(var, ty.clone());
                    self.push_var(name, var);
                    bound_names.push(name.clone());
                    lit_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(
                            span,
                            SimpleExprKind::Atom(crate::Atom::Lit(lit.clone())),
                        ),
                    });
                }
            }
        }

        for (pat, scrut) in patterns.iter().zip(scrutinees.iter()) {
            if let TypedPattern::Var { name, ty, .. } = pat {
                match scrut {
                    Atom::Var(scrut_id) => {
                        self.var_types.insert(*scrut_id, ty.clone());
                        self.push_var(name, *scrut_id);
                        bound_names.push(name.clone());
                    }
                    Atom::Lit(lit) => {
                        let var = self.fresh_var();
                        self.var_types.insert(var, ty.clone());
                        self.push_var(name, var);
                        bound_names.push(name.clone());
                        lit_bindings.push(LetBinding {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                span,
                                SimpleExprKind::Atom(crate::Atom::Lit(lit.clone())),
                            ),
                        });
                    }
                }
            }
        }

        // Lower guard via lower_to_atom_then so complex guards get bound to a temp var
        let result_ty_clone = result_ty.clone();
        let guard_typed = payload
            .guard
            .as_deref()
            .expect("guarded clause must have a guard");
        let payload_for_body = Rc::clone(&payload);
        let guard_and_branches = self.lower_to_atom_then(guard_typed, move |ctx, guard_atom| {
            let body_expr = ctx.lower_expr(&payload_for_body.body)?;

            // Pop variable bindings before compiling fallthrough
            for name in bound_names.iter().rev() {
                ctx.pop_var(name);
            }

            let fallthrough = ctx.compile_clauses(scrutinees, remaining, &result_ty_clone)?;

            Ok(Expr {
                kind: ExprKind::BoolSwitch {
                    scrutinee: guard_atom,
                    true_body: Box::new(body_expr),
                    false_body: Box::new(fallthrough),
                },
                ty: result_ty_clone.clone().into(),
                span,
            })
        })?;

        if lit_bindings.is_empty() {
            Ok(guard_and_branches)
        } else {
            Ok(Self::wrap_bindings(lit_bindings, guard_and_branches))
        }
    }

    /// Pick the first column that has a non-wildcard/var pattern.
    fn pick_column(&self, clauses: &[Clause]) -> usize {
        let ncols = clauses[0].patterns.len();
        for col in 0..ncols {
            for clause in clauses {
                if !is_wildcard_or_var(&clause.patterns[col]) {
                    return col;
                }
            }
        }
        0 // fallback (shouldn't happen — handled by all-wildcards base case)
    }

    /// Classify what kind of patterns appear in a column.
    fn classify_column(&self, clauses: &[Clause], col: usize) -> ColumnKind {
        for clause in clauses {
            match &clause.patterns[col] {
                TypedPattern::Constructor { .. } => return ColumnKind::Constructor,
                TypedPattern::Lit { .. } => return ColumnKind::Literal,
                TypedPattern::Tuple { elements, .. } => return ColumnKind::Tuple(elements.len()),
                TypedPattern::StructPat { name, .. } => return ColumnKind::Struct(name.clone()),
                TypedPattern::Wildcard { .. } | TypedPattern::Var { .. } => continue,
                TypedPattern::Or { .. } => continue, // flattened before reaching here
            }
        }
        // All wildcards — shouldn't happen since we chose a non-wildcard column
        ColumnKind::Constructor
    }

    /// Compile a column with constructor patterns into a Switch.
    fn compile_constructor_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Collect all constructor heads that appear
        let mut seen_tags: Vec<(String, u32, Vec<Type>)> = Vec::new();
        let mut seen_names: HashSet<String> = HashSet::new();
        for clause in &clauses {
            if let TypedPattern::Constructor {
                name,
                resolved_variant_ref,
                ..
            } = &clause.patterns[col]
            {
                if seen_names.insert(name.clone()) {
                    let variant_ref = resolved_variant_ref
                        .clone()
                        .or_else(|| self.fallback_variant_ref(name))
                        .ok_or_else(|| {
                            LowerError::InternalError(format!(
                                "unknown variant ref in pattern: {name}"
                            ))
                        })?;
                    let (tag, field_types) = self.variant_info(&variant_ref)?;
                    seen_tags.push((name.clone(), tag, field_types));
                }
            }
        }

        let scrut = scrutinees[col].clone();
        let mut branches = Vec::new();

        for (ctor_name, tag, field_types) in &seen_tags {
            // Create fresh bindings for variant fields
            let mut field_bindings = Vec::new();
            let mut field_atoms = Vec::new();
            for ft in field_types {
                let v = self.fresh_var();
                self.var_types.insert(v, ft.clone());
                field_bindings.push((v, ft.clone()));
                field_atoms.push(Atom::Var(v));
            }

            // Specialize the clause matrix for this constructor
            let specialized =
                self.specialize_for_constructor(&clauses, col, ctor_name, field_types, &scrut);

            // Build new scrutinee list: replace col with field atoms
            let mut new_scrutinees = Vec::new();
            for (i, s) in scrutinees.iter().enumerate() {
                if i == col {
                    new_scrutinees.extend(field_atoms.clone());
                } else {
                    new_scrutinees.push(s.clone());
                }
            }

            let body = self.compile_clauses(new_scrutinees, specialized, result_ty)?;

            // Use concrete types updated during lowering, not abstract field types
            let concrete_bindings: Vec<(VarId, Type)> = field_bindings
                .iter()
                .map(|(v, abstract_t)| {
                    (
                        *v,
                        self.var_types
                            .get(v)
                            .cloned()
                            .unwrap_or_else(|| abstract_t.clone()),
                    )
                })
                .collect();

            branches.push(SwitchBranch {
                tag: *tag,
                bindings: concrete_bindings
                    .into_iter()
                    .map(|(v, t)| (v, t.into()))
                    .collect(),
                body,
            });
        }

        // Default matrix: rows with wildcard/var at col, remove that column
        let default_clauses = self.default_matrix(&clauses, col, &scrut);
        let default = if default_clauses.is_empty() {
            None
        } else {
            let mut new_scrutinees: Vec<Atom> = Vec::new();
            for (i, s) in scrutinees.iter().enumerate() {
                if i != col {
                    new_scrutinees.push(s.clone());
                }
            }
            Some(Box::new(self.compile_clauses(
                new_scrutinees,
                default_clauses,
                result_ty,
            )?))
        };

        Ok(expr_at(
            clauses[0].span(),
            result_ty.clone().into(),
            ExprKind::Switch {
                scrutinee: scrut,
                branches,
                default,
            },
        ))
    }

    /// Compile a column with literal patterns into chained equality checks.
    fn compile_literal_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let scrut = scrutinees[col].clone();

        // Collect distinct literals
        let mut lit_values: Vec<Lit> = Vec::new();
        for clause in &clauses {
            if let TypedPattern::Lit { value, .. } = &clause.patterns[col] {
                if !lit_values.iter().any(|l| l == value) {
                    lit_values.push(value.clone());
                }
            }
        }

        // Build from the bottom up: start with default, then chain if-else for each literal
        let default_clauses = self.default_matrix(&clauses, col, &scrut);
        let mut new_scrutinees_for_default: Vec<Atom> = Vec::new();
        for (i, s) in scrutinees.iter().enumerate() {
            if i != col {
                new_scrutinees_for_default.push(s.clone());
            }
        }

        let mut result = if default_clauses.is_empty() {
            // Unreachable
            atom_expr_at((0, 0), result_ty.clone().into(), Atom::Lit(Literal::Unit))
        } else {
            self.compile_clauses(
                new_scrutinees_for_default.clone(),
                default_clauses,
                result_ty,
            )?
        };

        // Chain literals in reverse order so the first literal tested is the first one encountered
        for lit in lit_values.iter().rev() {
            let specialized = self.specialize_for_literal(&clauses, col, lit, &scrut);
            // Literals have no sub-patterns, so just remove the column
            let mut new_scrutinees: Vec<Atom> = Vec::new();
            for (i, s) in scrutinees.iter().enumerate() {
                if i != col {
                    new_scrutinees.push(s.clone());
                }
            }
            let then_body = self.compile_clauses(new_scrutinees, specialized, result_ty)?;

            // Emit: let eq = EqInt(scrut, lit_val) in switch eq { 1 -> then | _ -> else }
            let eq_op = self.eq_op_for_lit(lit)?;
            let lit_atom = Atom::Lit(convert_lit(lit));
            let eq_var = self.fresh_var();

            result = expr_at(
                then_body.span,
                result_ty.clone().into(),
                ExprKind::Let {
                    bind: eq_var,
                    ty: Type::Bool.into(),
                    value: simple_at(
                        then_body.span,
                        SimpleExprKind::PrimOp {
                            op: eq_op,
                            args: vec![scrut.clone(), lit_atom],
                        },
                    ),
                    body: Box::new(expr_at(
                        then_body.span,
                        result_ty.clone().into(),
                        ExprKind::BoolSwitch {
                            scrutinee: Atom::Var(eq_var),
                            true_body: Box::new(then_body),
                            false_body: Box::new(result),
                        },
                    )),
                },
            );
        }

        Ok(result)
    }

    /// Compile a column with tuple patterns — expand with projections, no Switch needed.
    fn compile_tuple_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
        arity: usize,
    ) -> Result<Expr, LowerError> {
        let scrut = scrutinees[col].clone();

        // Get the scrutinee type for fallback in tuple_element_type
        let scrut_ty = if let Atom::Var(id) = &scrut {
            self.var_types
                .get(id)
                .cloned()
                .unwrap_or_else(|| pattern_type(&clauses[0].patterns[col]))
        } else {
            pattern_type(&clauses[0].patterns[col])
        };

        // Project each element
        let mut proj_vars = Vec::new();
        let mut proj_bindings = Vec::new();
        for i in 0..arity {
            let elem_ty = self.tuple_element_type(&clauses, col, i, &scrut_ty);
            let v = self.fresh_var();
            self.var_types.insert(v, elem_ty.clone());
            proj_bindings.push(LetBinding {
                bind: v,
                ty: elem_ty.into(),
                value: simple_at(
                    clauses[0].span(),
                    SimpleExprKind::TupleProject {
                        value: scrut.clone(),
                        index: i,
                    },
                ),
            });
            proj_vars.push(Atom::Var(v));
        }

        // Expand columns: replace col with element sub-patterns
        let expanded: Vec<Clause> = clauses
            .into_iter()
            .map(|c| self.expand_tuple_clause(c, col, arity, &scrut))
            .collect();

        // Build new scrutinee list
        let mut new_scrutinees = Vec::new();
        for (i, s) in scrutinees.iter().enumerate() {
            if i == col {
                new_scrutinees.extend(proj_vars.clone());
            } else {
                new_scrutinees.push(s.clone());
            }
        }

        let body = self.compile_clauses(new_scrutinees, expanded, result_ty)?;
        Ok(Self::wrap_bindings(proj_bindings, body))
    }

    /// Compile a column with struct patterns — expand with field projections.
    fn compile_struct_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
        struct_name: &str,
    ) -> Result<Expr, LowerError> {
        let scrut = scrutinees[col].clone();
        let type_ref = clauses
            .iter()
            .find_map(|clause| match &clause.patterns[col] {
                TypedPattern::StructPat {
                    resolved_type_ref, ..
                } => resolved_type_ref.clone(),
                _ => None,
            })
            .or_else(|| self.fallback_type_ref(struct_name))
            .ok_or_else(|| LowerError::UnresolvedStruct(struct_name.to_string()))?;

        let canonical_fields = self
            .struct_fields
            .get(&type_ref)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_ref.qualified_name.to_string()))?
            .clone();

        // Project each field
        let mut proj_vars = Vec::new();
        let mut proj_bindings = Vec::new();
        for (i, (_, fty)) in canonical_fields.iter().enumerate() {
            let v = self.fresh_var();
            self.var_types.insert(v, fty.clone());
            proj_bindings.push(LetBinding {
                bind: v,
                ty: fty.clone().into(),
                value: simple_at(
                    clauses[0].span(),
                    SimpleExprKind::Project {
                        value: scrut.clone(),
                        field_index: i,
                    },
                ),
            });
            proj_vars.push(Atom::Var(v));
        }

        // Expand columns: replace col with field sub-patterns in canonical order
        let expanded: Vec<Clause> = clauses
            .into_iter()
            .map(|c| self.expand_struct_clause(c, col, &canonical_fields, &scrut))
            .collect();

        let mut new_scrutinees = Vec::new();
        for (i, s) in scrutinees.iter().enumerate() {
            if i == col {
                new_scrutinees.extend(proj_vars.clone());
            } else {
                new_scrutinees.push(s.clone());
            }
        }

        let body = self.compile_clauses(new_scrutinees, expanded, result_ty)?;
        Ok(Self::wrap_bindings(proj_bindings, body))
    }

    /// Specialize clause matrix for a given constructor.
    fn specialize_for_constructor(
        &self,
        clauses: &[Clause],
        col: usize,
        ctor_name: &str,
        field_types: &[Type],
        scrut_at_col: &Atom,
    ) -> Vec<Clause> {
        let mut result = Vec::new();
        for clause in clauses {
            match &clause.patterns[col] {
                TypedPattern::Constructor { name, args, .. } if name == ctor_name => {
                    // Replace column with sub-patterns
                    let mut new_pats = Vec::new();
                    for (i, p) in clause.patterns.iter().enumerate() {
                        if i == col {
                            new_pats.extend(args.clone());
                        } else {
                            new_pats.push(p.clone());
                        }
                    }
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Wildcard { span, .. } => {
                    // Expand wildcard to `arity` wildcards with correct field types
                    let mut new_pats = Vec::new();
                    for (i, p) in clause.patterns.iter().enumerate() {
                        if i == col {
                            for ft in field_types {
                                new_pats.push(TypedPattern::Wildcard {
                                    ty: ft.clone(),
                                    span: *span,
                                });
                            }
                        } else {
                            new_pats.push(p.clone());
                        }
                    }
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Var { name, ty, span } => {
                    // Expand to wildcards but record binding for the whole scrutinee
                    let mut new_pats = Vec::new();
                    for (i, p) in clause.patterns.iter().enumerate() {
                        if i == col {
                            for ft in field_types {
                                new_pats.push(TypedPattern::Wildcard {
                                    ty: ft.clone(),
                                    span: *span,
                                });
                            }
                        } else {
                            new_pats.push(p.clone());
                        }
                    }
                    let mut extra = clause.extra_bindings.clone();
                    extra.push((name.clone(), scrut_at_col.clone(), ty.clone()));
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: extra,
                    });
                }
                _ => {
                    // Different constructor — skip this row
                }
            }
        }
        result
    }

    /// Specialize clause matrix for a given literal value.
    fn specialize_for_literal(
        &self,
        clauses: &[Clause],
        col: usize,
        lit: &Lit,
        scrut_at_col: &Atom,
    ) -> Vec<Clause> {
        let mut result = Vec::new();
        for clause in clauses {
            match &clause.patterns[col] {
                TypedPattern::Lit { value, .. } if value == lit => {
                    // Literals have no sub-patterns; just remove the column
                    let new_pats: Vec<_> = clause
                        .patterns
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != col)
                        .map(|(_, p)| p.clone())
                        .collect();
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Wildcard { .. } => {
                    let new_pats: Vec<_> = clause
                        .patterns
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != col)
                        .map(|(_, p)| p.clone())
                        .collect();
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Var { name, ty, .. } => {
                    let new_pats: Vec<_> = clause
                        .patterns
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != col)
                        .map(|(_, p)| p.clone())
                        .collect();
                    let mut extra = clause.extra_bindings.clone();
                    extra.push((name.clone(), scrut_at_col.clone(), ty.clone()));
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: extra,
                    });
                }
                _ => {}
            }
        }
        result
    }

    /// Default matrix: keep rows with wildcard/var at col, remove that column.
    fn default_matrix(&self, clauses: &[Clause], col: usize, scrut_at_col: &Atom) -> Vec<Clause> {
        let mut result = Vec::new();
        for clause in clauses {
            let pat = &clause.patterns[col];
            if is_wildcard_or_var(pat) {
                let new_pats: Vec<_> = clause
                    .patterns
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != col)
                    .map(|(_, p)| p.clone())
                    .collect();
                let mut extra = clause.extra_bindings.clone();
                if let TypedPattern::Var { name, ty, .. } = pat {
                    extra.push((name.clone(), scrut_at_col.clone(), ty.clone()));
                }
                result.push(Clause {
                    patterns: new_pats,
                    payload: Rc::clone(&clause.payload),
                    extra_bindings: extra,
                });
            }
        }
        result
    }

    /// Expand a clause's tuple pattern at `col` into element sub-patterns.
    fn expand_tuple_clause(
        &self,
        clause: Clause,
        col: usize,
        arity: usize,
        scrut_at_col: &Atom,
    ) -> Clause {
        let mut new_pats = Vec::new();
        let mut extra = clause.extra_bindings;
        for (i, p) in clause.patterns.into_iter().enumerate() {
            if i == col {
                match p {
                    TypedPattern::Tuple { elements, .. } => {
                        new_pats.extend(elements);
                    }
                    TypedPattern::Var { name, ty, span } => {
                        extra.push((name, scrut_at_col.clone(), ty.clone()));
                        for _ in 0..arity {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: ty.clone(),
                                span,
                            });
                        }
                    }
                    TypedPattern::Wildcard { ty, span } => {
                        for _ in 0..arity {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: ty.clone(),
                                span,
                            });
                        }
                    }
                    _ => {
                        // Shouldn't happen
                        new_pats.push(p);
                    }
                }
            } else {
                new_pats.push(p);
            }
        }
        Clause {
            patterns: new_pats,
            payload: clause.payload,
            extra_bindings: extra,
        }
    }

    /// Expand a clause's struct pattern at `col` into field sub-patterns (canonical order).
    fn expand_struct_clause(
        &self,
        clause: Clause,
        col: usize,
        canonical_fields: &[(String, Type)],
        scrut_at_col: &Atom,
    ) -> Clause {
        let mut new_pats = Vec::new();
        let mut extra = clause.extra_bindings;
        for (i, p) in clause.patterns.into_iter().enumerate() {
            if i == col {
                match p {
                    TypedPattern::StructPat { fields, span, .. } => {
                        let field_map: HashMap<String, TypedPattern> = fields.into_iter().collect();
                        for (fname, fty) in canonical_fields {
                            if let Some(fp) = field_map.get(fname) {
                                new_pats.push(fp.clone());
                            } else {
                                new_pats.push(TypedPattern::Wildcard {
                                    ty: fty.clone(),
                                    span,
                                });
                            }
                        }
                    }
                    TypedPattern::Var { name, ty, span } => {
                        extra.push((name, scrut_at_col.clone(), ty));
                        for (_, fty) in canonical_fields {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: fty.clone(),
                                span,
                            });
                        }
                    }
                    TypedPattern::Wildcard { ty: _, span } => {
                        for (_, fty) in canonical_fields {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: fty.clone(),
                                span,
                            });
                        }
                    }
                    _ => {
                        new_pats.push(p);
                    }
                }
            } else {
                new_pats.push(p);
            }
        }
        Clause {
            patterns: new_pats,
            payload: clause.payload,
            extra_bindings: extra,
        }
    }

    /// Get the type of a tuple element from the patterns in a column.
    fn tuple_element_type(
        &self,
        clauses: &[Clause],
        col: usize,
        index: usize,
        scrut_ty: &Type,
    ) -> Type {
        for clause in clauses {
            if let TypedPattern::Tuple { elements, .. } = &clause.patterns[col] {
                if let Some(elem) = elements.get(index) {
                    return pattern_type(elem);
                }
            }
        }
        // Fallback: extract from scrutinee type
        if let Type::Tuple(elems) = scrut_ty {
            if let Some(ty) = elems.get(index) {
                return ty.clone();
            }
        }
        Type::Unit
    }

    /// Get the equality PrimOp for a literal pattern.
    fn eq_op_for_lit(&self, lit: &Lit) -> Result<PrimOp, LowerError> {
        match lit {
            Lit::Int(_) => Ok(PrimOp::EqInt),
            Lit::Float(_) => Ok(PrimOp::EqFloat),
            Lit::Bool(_) => Ok(PrimOp::EqInt), // booleans compared as ints
            Lit::String(_) => Ok(PrimOp::EqString),
            Lit::Unit => Err(LowerError::UnsupportedOp(
                "matching on Unit literal".to_string(),
            )),
        }
    }

    /// Lower a Do block (sequence of expressions).
    /// Processes left-to-right so Let bindings are in scope for subsequent exprs.
    fn lower_do(&mut self, exprs: &[TypedExpr], _result_ty: &Type) -> Result<Expr, LowerError> {
        if exprs.is_empty() {
            return Ok(atom_expr_at(
                (0, 0),
                Type::Unit.into(),
                Atom::Lit(Literal::Unit),
            ));
        }
        self.lower_do_slice(exprs)
    }

    /// Recursively lower a slice of Do-block expressions.
    fn lower_do_slice(&mut self, exprs: &[TypedExpr]) -> Result<Expr, LowerError> {
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

            self.push_var(name, bind);
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
    fn lower_short_circuit(
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
    fn lower_trait_comparison(
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
        let (dict_bindings, dict_atom) = self.resolve_dict(&trait_name, &dict_ty)?;

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
    fn lower_trait_arithmetic(
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

        let (dict_bindings, dict_atom) = self.resolve_dict(&trait_name, &dict_ty)?;

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
    fn lower_trait_unary(
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

        let (dict_bindings, dict_atom) = self.resolve_dict(&trait_name, &dict_ty)?;

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

    /// Look up the dict param VarId for a given trait name (bare name match).
    fn lookup_dict_param(&self, trait_name: &str) -> Result<VarId, LowerError> {
        for ((t, _), var_id) in &self.dict_params {
            if t.local_name == trait_name {
                return Ok(*var_id);
            }
        }
        Err(LowerError::UnresolvedVar(format!(
            "trait_dict: no dict param for trait {trait_name}"
        )))
    }

    /// Lower a function application.
    fn lower_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // Peel TypeApp to get the function name, resolved binding ref, and type args
        let (func_name, resolved_ref, type_args) = extract_call_info(func);

        // Intercept trait_dict(TraitName) intrinsic: resolve to the dict param
        // for the named trait from the enclosing function's where-constraints.
        if func_name.as_deref() == Some("trait_dict") {
            if let Some(arg) = args.first() {
                if let TypedExprKind::Var(trait_name) = &arg.kind {
                    let var_id = self.lookup_dict_param(trait_name)?;
                    return Ok((
                        vec![],
                        simple_at(arg.span, SimpleExprKind::Atom(Atom::Var(var_id))),
                    ));
                }
            }
        }

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
            let (dict_ty, type_bindings) =
                self.resolve_dispatch_type_with_bindings(trait_id, name, &func.ty, &type_args)?;
            let (dict_bindings, dict_atom) = self.resolve_dict(trait_id, &dict_ty)?;
            bindings.extend(dict_bindings);

            // Methods without where-clause constraints have no entry
            let method_constraints = self
                .trait_method_constraints
                .get(trait_id)
                .and_then(|mc| mc.get(name.as_str()))
                .cloned()
                .unwrap_or_default();
            let mut method_dict_atoms = Vec::new();
            for (constraint_trait, constraint_tv) in &method_constraints {
                if let Some(concrete_ty) = type_bindings.get(constraint_tv) {
                    let (extra_bindings, extra_atom) =
                        self.resolve_dict(constraint_trait, concrete_ty)?;
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
                let Some(fn_id) = self.lookup_callable(&qn) else {
                    return Err(LowerError::UnresolvedVar(name.clone()));
                };
                // Resolve dict arguments for constrained functions
                let (dict_bindings, dict_atoms) = self.resolve_call_dicts(&qn, args, &type_args)?;
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
    fn lower_struct_lit(
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
    fn lower_app_expr(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Peel TypeApp to get function name, resolved binding ref, and type args
        let (func_name, resolved_ref, type_args) = extract_call_info(func);

        // Intercept trait_dict(TraitName) intrinsic
        if func_name.as_deref() == Some("trait_dict") {
            if let Some(arg) = args.first() {
                if let TypedExprKind::Var(trait_name) = &arg.kind {
                    let var_id = self.lookup_dict_param(trait_name)?;
                    return Ok(atom_expr_at(
                        arg.span,
                        result_ty.clone().into(),
                        Atom::Var(var_id),
                    ));
                }
            }
        }

        let result_ty = result_ty.clone();

        // Handle trait method dispatch
        if let Some(ResolvedBindingRef::TraitMethod(trait_ref)) = resolved_ref.as_ref() {
            let trait_id = &trait_ref.trait_name;
            let name = &trait_ref.method_name;
            let (dict_ty, type_bindings) =
                self.resolve_dispatch_type_with_bindings(trait_id, name, &func.ty, &type_args)?;
            let (mut dict_bindings, dict_atom) = self.resolve_dict(trait_id, &dict_ty)?;

            // Methods without where-clause constraints have no entry
            let mut method_dict_atoms = Vec::new();
            let method_constraints = self
                .trait_method_constraints
                .get(trait_id)
                .and_then(|mc| mc.get(name.as_str()))
                .cloned()
                .unwrap_or_default();
            {
                for (constraint_trait, constraint_tv) in &method_constraints {
                    let concrete_ty = type_bindings.get(constraint_tv).ok_or_else(|| {
                        LowerError::InternalError(format!(
                            "ICE: could not resolve method constraint type var for {}.{}",
                            trait_id.local_name, name
                        ))
                    })?;
                    let (extra_bindings, extra_atom) =
                        self.resolve_dict(constraint_trait, concrete_ty)?;
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
                let Some(fn_id) = self.lookup_callable(&qn) else {
                    return Err(LowerError::UnresolvedVar(name.clone()));
                };
                let (dict_bindings, dict_atoms) = self.resolve_call_dicts(&qn, args, &type_args)?;

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
    fn lower_struct_lit_expr(
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
        let field_map: HashMap<&str, &TypedExpr> =
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
    fn lower_struct_update_expr(
        &mut self,
        base: &TypedExpr,
        updates: &[(String, TypedExpr)],
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let type_ref = self.resolved_type_ref_from_type(&base.ty).ok_or_else(|| {
            LowerError::InternalError(format!("StructUpdate on non-named type: {:?}", base.ty))
        })?;

        let canonical_fields = self
            .struct_fields
            .get(&type_ref)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_ref.qualified_name.to_string()))?
            .clone();

        let result_ty = result_ty.clone();
        let update_names: Vec<String> = updates.iter().map(|(n, _)| n.clone()).collect();
        let update_exprs: Vec<TypedExpr> = updates.iter().map(|(_, e)| e.clone()).collect();

        // Lower base first, then update field values
        self.lower_to_atom_then(base, |ctx, base_atom| {
            ctx.lower_atoms_then(&update_exprs, vec![], |ctx, update_atoms| {
                let mut update_map: HashMap<String, Atom> =
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

    // -----------------------------------------------------------------------
    // Dict resolution
    // -----------------------------------------------------------------------

    /// Resolve a trait dictionary for a given trait and concrete type.
    /// Returns let-bindings and an atom referencing the dict value.
    fn resolve_dict(
        &mut self,
        trait_name: &TraitName,
        ty: &Type,
    ) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        const MAX_DICT_DEPTH: u32 = 64;
        if self.dict_depth >= MAX_DICT_DEPTH {
            return Err(LowerError::InternalError(format!(
                "dict resolution depth exceeded for {}[{ty}]",
                trait_name.local_name
            )));
        }
        self.dict_depth += 1;
        let result = self.resolve_dict_inner(trait_name, ty);
        self.dict_depth -= 1;
        result
    }

    fn resolve_dict_inner(
        &mut self,
        trait_name: &TraitName,
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
                ty: IrType::Dict {
                    trait_name: trait_name.clone(),
                    target: Box::new(ty.clone().into()),
                },
                value: simple_at(
                    (0, 0),
                    SimpleExprKind::GetDict {
                        instance_ref: self.instance_canonical_ref(trait_name, ty),
                        trait_name: trait_name.clone(),
                        ty: ty.clone().into(),
                    },
                ),
            }],
            Atom::Var(var),
        ))
    }

    /// Look up a dict param VarId for a type variable.
    fn lookup_dict_var(&self, trait_name: &TraitName, ty: &Type) -> Option<VarId> {
        match ty {
            Type::Var(id) => {
                // Exact match first
                if let Some(&var_id) = self.dict_params.get(&(trait_name.clone(), *id)) {
                    return Some(var_id);
                }
                // Single-match heuristic: fresh instantiation TypeVarIds may differ from
                // enclosing constraint's. Sound when exactly one dict param exists for this trait.
                let matches: Vec<_> = self
                    .dict_params
                    .iter()
                    .filter(|((tn, _), _)| tn == trait_name)
                    .collect();
                if matches.len() == 1 {
                    Some(*matches[0].1)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Try to resolve a parameterized instance dict (e.g., Show[Option[a]] where a: Show).
    fn try_resolve_parameterized_dict(
        &mut self,
        trait_name: &TraitName,
        ty: &Type,
    ) -> Result<Option<(Vec<LetBinding>, Atom)>, LowerError> {
        // Find a matching instance with constraints, keeping the bindings
        let matching = self.param_instances.iter().find_map(|inst| {
            if &inst.trait_name != trait_name {
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
            ty: IrType::Dict {
                trait_name: trait_name.clone(),
                target: Box::new(ty.clone().into()),
            },
            value: simple_at(
                (0, 0),
                SimpleExprKind::MakeDict {
                    instance_ref: CanonicalRef {
                        module: ModulePath::new(inst.source_module.clone()),
                        symbol: LocalSymbolKey::Instance {
                            trait_name: inst.trait_name.local_name.clone(),
                            target_type: inst.target_type_name.clone(),
                        },
                    },
                    trait_name: trait_name.clone(),
                    ty: ty.clone().into(),
                    sub_dicts: sub_dict_atoms,
                },
            ),
        });
        Ok(Some((all_bindings, Atom::Var(var))))
    }

    /// Resolve dict arguments for a call to a constrained function.
    /// Returns let-bindings and dict atom args to prepend.
    fn resolve_call_dicts(
        &mut self,
        qn: &QualifiedName,
        args: &[TypedExpr],
        type_args: &[Type],
    ) -> Result<(Vec<LetBinding>, Vec<Atom>), LowerError> {
        let constraints = match self.fn_constraints.get(qn) {
            Some(c) if !c.is_empty() => c.clone(),
            _ => return Ok((vec![], vec![])),
        };

        // Get the function's type scheme to extract param type patterns
        let scheme = self.fn_schemes.get(qn).cloned();

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

    /// Resolve the dispatch type for a trait method from its concrete (fully-specialized) type.
    /// Matches the method's type patterns (params + return) against `concrete_method_ty`
    /// to bind the trait's type variable.
    /// Resolve the dispatch type for a trait method, returning the trait's dispatch type
    /// and full type var bindings (including method-level type vars).
    /// Matches the method's type patterns against the concrete expression type,
    /// with explicit type args as fallback for phantom type vars (trait type var
    /// not appearing in the method signature, e.g. `name() -> String` on `Test[e]`).
    fn resolve_dispatch_type(
        &self,
        trait_name: &TraitName,
        method_name: &str,
        concrete_method_ty: &Type,
        type_args: &[Type],
    ) -> Result<Type, LowerError> {
        let (dispatch_ty, _bindings) = self.resolve_dispatch_type_with_bindings(
            trait_name,
            method_name,
            concrete_method_ty,
            type_args,
        )?;
        Ok(dispatch_ty)
    }

    fn resolve_dispatch_type_with_bindings(
        &self,
        trait_name: &TraitName,
        method_name: &str,
        concrete_method_ty: &Type,
        type_args: &[Type],
    ) -> Result<(Type, HashMap<TypeVarId, Type>), LowerError> {
        let (type_var_id, method_types) =
            self.trait_method_types.get(trait_name).ok_or_else(|| {
                LowerError::InternalError(format!(
                    "ICE: no trait_method_types for trait {}",
                    trait_name.local_name
                ))
            })?;
        let type_var_id = *type_var_id;

        let (param_patterns, ret_pattern) = method_types.get(method_name).ok_or_else(|| {
            LowerError::InternalError(format!(
                "ICE: no method type patterns for {}.{}",
                trait_name.local_name, method_name
            ))
        })?;

        let mut bindings = HashMap::new();

        // Bind from explicit type application (authoritative when present)
        if !type_args.is_empty() {
            bindings
                .entry(type_var_id)
                .or_insert_with(|| type_args[0].clone());
        }

        // Bind from matching the method signature against the concrete type
        let pattern_fn_ty = Type::Fn(param_patterns.clone(), Box::new(ret_pattern.clone()));
        let concrete = strip_own(concrete_method_ty);
        bind_type_vars(&pattern_fn_ty, concrete, &mut bindings);

        // For zero-arg methods, the concrete type IS the return type (not wrapped in Fn)
        if param_patterns.is_empty() {
            bind_type_vars(ret_pattern, concrete, &mut bindings);
        }

        let dispatch_ty = bindings.get(&type_var_id).cloned().ok_or_else(|| {
            LowerError::InternalError(format!(
                "ICE: could not resolve dispatch type var for {}.{}",
                trait_name.local_name, method_name
            ))
        })?;

        Ok((dispatch_ty, bindings))
    }

    /// Lower a constrained function reference used as a value (not directly called).
    /// Creates a wrapper function that captures resolved dicts and forwards to the original fn.
    fn lower_constrained_fn_as_value(
        &mut self,
        qn: &QualifiedName,
        fn_id: FnId,
        constraints: &[(TraitName, TypeVarId)],
        type_args: &[Type],
        expr_ty: &Type,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // Build type var bindings from type_args and expression type
        let mut type_bindings: HashMap<TypeVarId, Type> = HashMap::new();

        if let Some(scheme) = self.fn_schemes.get(qn).cloned() {
            // Bind from explicit type args
            for (var_id, ty) in scheme.vars.iter().zip(type_args.iter()) {
                type_bindings.insert(*var_id, ty.clone());
            }
            // Bind from matching scheme type against expression type
            let concrete = strip_own(expr_ty);
            bind_type_vars(&scheme.ty, concrete, &mut type_bindings);
        }

        // Resolve dicts for each constraint
        let mut all_bindings = vec![];
        let mut dict_atoms = vec![];
        for (trait_name, type_var_id) in constraints {
            let concrete_ty = type_bindings
                .get(type_var_id)
                .cloned()
                .unwrap_or(Type::Var(*type_var_id));
            let (bs, atom) = self.resolve_dict(trait_name, &concrete_ty)?;
            all_bindings.extend(bs);
            dict_atoms.push(atom);
        }

        // Extract user param types from expr_ty
        let unwrapped = strip_own(expr_ty);
        let (user_param_types, return_type) = match unwrapped {
            Type::Fn(params, ret) => (params.clone(), ret.as_ref().clone()),
            other => (vec![], other.clone()),
        };

        // Allocate wrapper function
        let wrapper_fn_id = self.fresh_fn();
        let wrapper_name = format!("fn_ref${}", wrapper_fn_id.0);

        // Dict capture params
        let mut dict_capture_vars = vec![];
        let mut lifted_params = vec![];
        for (trait_name, type_var_id) in constraints {
            let var = self.fresh_var();
            dict_capture_vars.push(var);
            let concrete_ty = type_bindings
                .get(type_var_id)
                .cloned()
                .unwrap_or(Type::Var(*type_var_id));
            lifted_params.push((
                var,
                IrType::Dict {
                    trait_name: trait_name.clone(),
                    target: Box::new(concrete_ty.into()),
                },
            ));
        }

        // User params
        let mut user_param_vars = vec![];
        for ty in &user_param_types {
            let var = self.fresh_var();
            user_param_vars.push(var);
            lifted_params.push((var, ty.clone().into()));
        }

        // Build body: Call fn_id(dict_captures..., user_params...)
        let mut call_args: Vec<Atom> = dict_capture_vars.iter().map(|v| Atom::Var(*v)).collect();
        for var in &user_param_vars {
            call_args.push(Atom::Var(*var));
        }

        let result_var = self.fresh_var();
        let body = expr_at(
            (0, 0),
            return_type.clone().into(),
            ExprKind::Let {
                bind: result_var,
                ty: return_type.clone().into(),
                value: simple_at(
                    (0, 0),
                    SimpleExprKind::Call {
                        func: fn_id,
                        args: call_args,
                    },
                ),
                body: Box::new(atom_expr_at(
                    (0, 0),
                    return_type.clone().into(),
                    Atom::Var(result_var),
                )),
            },
        );

        // Push lifted FnDef
        self.lifted_fns.push(FnDef {
            id: wrapper_fn_id,
            name: wrapper_name.clone(),
            params: lifted_params,
            return_type: return_type.into(),
            body,
        });
        self.fn_ids.insert(wrapper_name, wrapper_fn_id);

        // Return MakeClosure capturing the dicts
        Ok((
            all_bindings,
            simple_at(
                (0, 0),
                SimpleExprKind::MakeClosure {
                    func: wrapper_fn_id,
                    captures: dict_atoms,
                },
            ),
        ))
    }

    /// Lower a trait method reference used as a value (not directly called).
    /// Creates a wrapper function that captures the dict and forwards to the dispatch FnId.
    fn lower_trait_method_as_value(
        &mut self,
        trait_name: &TraitName,
        method_name: &str,
        expr_ty: &Type,
        type_args: &[Type],
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // 1. Resolve the dispatch type
        let dispatch_ty =
            self.resolve_dispatch_type(trait_name, method_name, expr_ty, type_args)?;

        // 2. Resolve the dict
        let (dict_bindings, dict_atom) = self.resolve_dict(trait_name, &dispatch_ty)?;

        // 3. Extract user param types from expr_ty
        let unwrapped = strip_own(expr_ty);
        let (user_param_types, return_type) = match unwrapped {
            Type::Fn(params, ret) => (params.clone(), ret.as_ref().clone()),
            other => (vec![], other.clone()),
        };

        // 4. Allocate wrapper function
        let wrapper_fn_id = self.fresh_fn();
        let wrapper_name = format!("trait_ref${}", wrapper_fn_id.0);

        // Dict capture param
        let dict_capture_var = self.fresh_var();
        let dict_ty_ir = IrType::Dict {
            trait_name: trait_name.clone(),
            target: Box::new(dispatch_ty.clone().into()),
        };

        // User params
        let mut user_param_vars = vec![];
        let mut lifted_params = vec![(dict_capture_var, dict_ty_ir)];
        for ty in &user_param_types {
            let var = self.fresh_var();
            user_param_vars.push(var);
            lifted_params.push((var, ty.clone().into()));
        }

        // 5. Build body: TraitCall trait_name.method_name(dict_capture_var, user_params...)
        let mut call_args = vec![Atom::Var(dict_capture_var)];
        for var in &user_param_vars {
            call_args.push(Atom::Var(*var));
        }

        let result_var = self.fresh_var();
        let body = expr_at(
            (0, 0),
            return_type.clone().into(),
            ExprKind::Let {
                bind: result_var,
                ty: return_type.clone().into(),
                value: simple_at(
                    (0, 0),
                    SimpleExprKind::TraitCall {
                        trait_name: trait_name.clone(),
                        method_name: method_name.to_string(),
                        args: call_args,
                    },
                ),
                body: Box::new(atom_expr_at(
                    (0, 0),
                    return_type.clone().into(),
                    Atom::Var(result_var),
                )),
            },
        );

        // 6. Push lifted FnDef
        self.lifted_fns.push(FnDef {
            id: wrapper_fn_id,
            name: wrapper_name.clone(),
            params: lifted_params,
            return_type: return_type.into(),
            body,
        });
        self.fn_ids.insert(wrapper_name, wrapper_fn_id);

        // 7. Return MakeClosure capturing the dict
        Ok((
            dict_bindings,
            simple_at(
                (0, 0),
                SimpleExprKind::MakeClosure {
                    func: wrapper_fn_id,
                    captures: vec![dict_atom],
                },
            ),
        ))
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

        // 3. Resolve each free var to its current VarId
        let mut capture_params = vec![];
        let mut capture_atoms = vec![];
        for name in &fv_names {
            if let Some(var_id) = self.lookup_var(name) {
                capture_atoms.push(Atom::Var(var_id));
                capture_params.push((name.clone(), var_id));
            }
            // Names not in var_scope are top-level functions, not captures
        }

        // 4. Collect dict captures (sorted for deterministic output)
        let saved_dict_params = self.dict_params.clone();
        let mut dict_entries: Vec<_> = saved_dict_params.iter().collect();
        dict_entries.sort_by_key(|((trait_name, tv_id), _)| (trait_name.clone(), *tv_id));
        let mut dict_capture_atoms = vec![];
        let mut dict_capture_keys = vec![];
        for ((trait_name, type_var_id), var_id) in &dict_entries {
            dict_capture_atoms.push(Atom::Var(**var_id));
            dict_capture_keys.push(((*trait_name).clone(), *type_var_id));
        }

        // 5. Allocate a fresh FnId for the lifted function
        let fn_id = self.fresh_fn();
        let name = format!("lambda${}", fn_id.0);

        // 6. Allocate new VarIds for the lifted fn's scope

        // Capture params — look up real types from var_types
        let mut capture_var_mappings = vec![];
        for (name, old_var_id) in &capture_params {
            let new_var = self.fresh_var();
            let ty = self
                .var_types
                .get(old_var_id)
                .cloned()
                .unwrap_or_else(|| Type::Var(self.type_var_gen.fresh()));
            capture_var_mappings.push((name.clone(), new_var, *old_var_id, ty));
        }

        // Dict capture params — allocate new VarIds
        let mut new_dict_params: HashMap<(TraitName, TypeVarId), VarId> = HashMap::new();
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
            let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                eprintln!(
                    "ICE: lambda param {} has no type (param_types len={})",
                    i,
                    param_types.len()
                );
                Type::Unit
            });
            lambda_var_mappings.push((param_name.clone(), new_var, ty));
        }

        // Push capture params and lambda params into var_scope
        for (name, new_var, _, ty) in &capture_var_mappings {
            self.var_types.insert(*new_var, ty.clone());
            self.push_var(name, *new_var);
        }
        for (name, new_var, ty) in &lambda_var_mappings {
            self.var_types.insert(*new_var, ty.clone());
            self.push_var(name, *new_var);
        }

        // Set dict_params to the captured dicts (mapped to new VarIds)
        let old_dict_params = std::mem::replace(&mut self.dict_params, new_dict_params);

        // Save and clear recur/early-return join points — these belong to the
        // enclosing function and must not leak into the lifted lambda.
        let old_recur_join = self.recur_join.take();
        let old_early_return_join = self.early_return_join.take();

        // Set up recur join point if the lambda body contains recur
        let has_recur = contains_recur(body);
        let recur_join_info = if has_recur {
            let join_name = self.fresh_var();
            let mut join_param_vars = vec![];
            for (param_name, _, ty) in &lambda_var_mappings {
                let join_var = self.fresh_var();
                self.var_types.insert(join_var, ty.clone());
                self.push_var(param_name, join_var);
                join_param_vars.push(join_var);
            }
            self.recur_join = Some((join_name, join_param_vars.clone()));
            Some((join_name, join_param_vars))
        } else {
            None
        };

        // Lower body
        let mut lowered_body = self.lower_expr(body)?;

        // Pop recur join params (they shadow lambda params)
        if recur_join_info.is_some() {
            for (name, _, _) in lambda_var_mappings.iter().rev() {
                self.pop_var(name);
            }
        }
        self.recur_join = None;

        // Pop all from var_scope, restore dict_params and join points
        for (name, _, _) in lambda_var_mappings.iter().rev() {
            self.pop_var(name);
        }
        for (name, _, _, _) in capture_var_mappings.iter().rev() {
            self.pop_var(name);
        }
        self.dict_params = old_dict_params;
        self.recur_join = old_recur_join;
        self.early_return_join = old_early_return_join;

        // 7. Filter dict captures to only those actually used in the body
        let used_vars = referenced_vars_in_expr(&lowered_body);
        let dict_var_mappings: Vec<_> = dict_var_mappings
            .into_iter()
            .filter(|(_, new_var)| used_vars.contains(new_var))
            .collect();
        let dict_capture_atoms: Vec<_> = dict_entries
            .iter()
            .filter(|((trait_name, tv_id), _)| {
                dict_var_mappings
                    .iter()
                    .any(|((tn, tid), _)| tn == trait_name && tid == tv_id)
            })
            .map(|(_, var_id)| Atom::Var(**var_id))
            .collect();

        // 8. Build the param list: captures ++ filtered dict captures ++ lambda params
        let mut lifted_params = vec![];
        for (_, new_var, _, ty) in &capture_var_mappings {
            lifted_params.push((*new_var, ty.clone().into()));
        }
        for (key, new_var) in &dict_var_mappings {
            lifted_params.push((
                *new_var,
                IrType::Dict {
                    trait_name: key.0.clone(),
                    target: Box::new(IrType::Var(key.1)),
                },
            ));
        }
        for (_, new_var, ty) in &lambda_var_mappings {
            lifted_params.push((*new_var, ty.clone().into()));
        }

        // 9. Wrap body with recur join if needed
        if let Some((join_name, join_param_vars)) = recur_join_info {
            let join_params: Vec<(VarId, IrType)> = join_param_vars
                .iter()
                .enumerate()
                .map(|(i, &v)| {
                    let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                        panic!("ICE: recur join: param_types index {i} out of range (len={})", param_types.len())
                    });
                    (v, ty.into())
                })
                .collect();
            let original_atoms: Vec<Atom> = lambda_var_mappings
                .iter()
                .map(|(_, new_var, _)| Atom::Var(*new_var))
                .collect();
            let body_span = lowered_body.span;
            lowered_body = expr_at(
                body_span,
                return_type.clone().into(),
                ExprKind::LetJoin {
                    name: join_name,
                    params: join_params,
                    join_body: Box::new(lowered_body),
                    body: Box::new(expr_at(
                        body_span,
                        return_type.clone().into(),
                        ExprKind::Jump {
                            target: join_name,
                            args: original_atoms,
                        },
                    )),
                    is_recur: true,
                },
            );
        }

        // 10. Push FnDef onto lifted_fns
        let lowered_body_span = lowered_body.span;
        self.lifted_fns.push(FnDef {
            id: fn_id,
            name: name.clone(),
            params: lifted_params,
            return_type: return_type.into(),
            body: lowered_body,
        });

        // 10. Register in fn_ids for fn_names resolution
        self.fn_ids.insert(name, fn_id);

        // 11. Return MakeClosure with capture atoms
        let mut all_captures = capture_atoms;
        all_captures.extend(dict_capture_atoms);

        Ok((
            vec![],
            simple_at(
                lowered_body_span,
                SimpleExprKind::MakeClosure {
                    func: fn_id,
                    captures: all_captures,
                },
            ),
        ))
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
        let fn_qn = QualifiedName::new(self.module_path.clone(), decl.name.clone());
        if let Some(constraints) = self.fn_constraints.get(&fn_qn).cloned() {
            for (trait_name, type_var_id) in &constraints {
                let var = self.fresh_var();
                self.dict_params
                    .insert((trait_name.clone(), *type_var_id), var);
                params.push((
                    var,
                    IrType::Dict {
                        trait_name: trait_name.clone(),
                        target: Box::new(IrType::Var(*type_var_id)),
                    },
                ));
            }
        }

        // Allocate VarIds for regular params
        let mut regular_param_vars = vec![];
        for (i, param_name) in decl.params.iter().enumerate() {
            let var = self.fresh_var();
            let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                eprintln!(
                    "ICE: fn param {} has no type (param_types len={})",
                    i,
                    param_types.len()
                );
                Type::Unit
            });
            self.var_types.insert(var, ty.clone());
            self.push_var(param_name, var);
            params.push((var, ty.into()));
            regular_param_vars.push(var);
        }

        let has_recur = contains_recur(&decl.body);
        let has_qm = contains_question_mark(&decl.body);

        // Set up recur join point if needed
        let recur_join_info = if has_recur {
            let join_name = self.fresh_var();
            let mut join_param_vars = vec![];
            for (i, param_name) in decl.params.iter().enumerate() {
                let join_var = self.fresh_var();
                let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                    panic!("ICE: recur join: param_types index {i} out of range (len={})", param_types.len())
                });
                self.var_types.insert(join_var, ty);
                // Shadow the original param with the join param
                self.push_var(param_name, join_var);
                join_param_vars.push(join_var);
            }
            self.recur_join = Some((join_name, join_param_vars.clone()));
            Some((join_name, join_param_vars))
        } else {
            None
        };

        // Set up early return join point if needed
        let early_return_info = if has_qm {
            let join_name = self.fresh_var();
            let result_var = self.fresh_var();
            self.early_return_join = Some(join_name);
            Some((join_name, result_var))
        } else {
            None
        };

        // Set up fn_exit tracking so push_var records VarIds for auto-close bindings
        let prev_track = std::mem::take(&mut self.fn_exit_track);
        let prev_vars = std::mem::take(&mut self.fn_exit_vars);
        if let Some(close_bindings) = self.auto_close.fn_exits.get(&decl.name) {
            for binding in close_bindings {
                self.fn_exit_track.insert(binding.name.clone());
            }
        }

        let mut body = self.lower_expr(&decl.body)?;

        // Wrap fn_exit close calls at tail positions (vars resolved via fn_exit_vars)
        if let Some(close_bindings) = self.auto_close.fn_exits.get(&decl.name).cloned() {
            let resolved = self.resolve_close_bindings(&close_bindings)?;
            body = self.wrap_tail_with_closes(body, &resolved)?;

            // Record fn_exit_closes for codegen (exception table finally handlers).
            // close_bindings and resolved are in the same order (1:1 correspondence).
            let finally_closes: Vec<FinallyClose> = close_bindings
                .iter()
                .zip(resolved.iter())
                .map(|(binding, rc)| FinallyClose {
                    resource_var: rc.binding_var,
                    type_name: binding.type_name.clone(),
                })
                .collect();
            self.fn_exit_closes
                .insert(decl.name.clone(), finally_closes);
        }

        // Restore tracking state
        self.fn_exit_track = prev_track;
        self.fn_exit_vars = prev_vars;

        // Pop recur join params (they were pushed on top of regular params)
        if recur_join_info.is_some() {
            for param_name in decl.params.iter().rev() {
                self.pop_var(param_name);
            }
        }
        self.recur_join = None;
        self.early_return_join = None;

        // Pop regular params
        for param_name in decl.params.iter().rev() {
            self.pop_var(param_name);
        }

        // Wrap body with early return join if needed
        if let Some((join_name, result_var)) = early_return_info {
            body = expr_at(
                body.span,
                return_type.clone().into(),
                ExprKind::LetJoin {
                    name: join_name,
                    params: vec![(result_var, return_type.clone().into())],
                    join_body: Box::new(atom_expr_at(
                        body.span,
                        return_type.clone().into(),
                        Atom::Var(result_var),
                    )),
                    body: Box::new(body),
                    is_recur: false,
                },
            );
        }

        // Wrap body with recur join if needed
        if let Some((join_name, join_param_vars)) = recur_join_info {
            let join_params: Vec<(VarId, Type)> = join_param_vars
                .iter()
                .enumerate()
                .map(|(i, &v)| {
                    let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                        panic!("ICE: recur join: param_types index {i} out of range (len={})", param_types.len())
                    });
                    (v, ty)
                })
                .collect();
            // Original param atoms for the initial jump
            let original_atoms: Vec<Atom> =
                regular_param_vars.iter().map(|&v| Atom::Var(v)).collect();
            let body_span = body.span;
            body = expr_at(
                body_span,
                return_type.clone().into(),
                ExprKind::LetJoin {
                    name: join_name,
                    params: join_params
                        .into_iter()
                        .map(|(v, t)| (v, t.into()))
                        .collect(),
                    join_body: Box::new(body),
                    body: Box::new(expr_at(
                        body_span,
                        return_type.clone().into(),
                        ExprKind::Jump {
                            target: join_name,
                            args: original_atoms,
                        },
                    )),
                    is_recur: true,
                },
            );
        }

        Ok(FnDef {
            id: fn_id,
            name: decl.name.clone(),
            params,
            return_type: return_type.into(),
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

/// Lower a `TypedModule` to an IR `Module`.
///
/// Each IR module is a self-contained compilation unit: local definitions plus
/// cross-module metadata (imported_structs, imported_sum_types, imported_extern_fns,
/// imported_extern_types, imported_instances). The codegen compiles each module
/// independently without access to other modules' IR.
///
/// `imported_instances` provides instance defs from other modules needed for
/// cross-module dict-passing resolution during lowering.
/// `imported_extern_fns` provides extern fn declarations from other modules
/// needed for FnId allocation (so calls to imported externs can be resolved).
pub fn lower_module(
    typed: &TypedModule,
    module_name: &str,
    link_view: &krypton_typechecker::link_context::ModuleLinkView,
) -> Result<Module, LowerError> {
    // Build fn_constraints from TypeScheme constraints (embedded during inference)
    let mut fn_constraints: HashMap<QualifiedName, Vec<(TraitName, TypeVarId)>> = HashMap::new();
    for entry in &typed.fn_types {
        if !entry.scheme.constraints.is_empty() {
            fn_constraints.insert(
                entry.qualified_name.clone(),
                entry.scheme.constraints.clone(),
            );
        }
    }

    // Include extern function constraints so dict-passing works for extern calls.
    for ext in &typed.extern_fns {
        if !ext.constraints.is_empty() {
            fn_constraints.insert(
                QualifiedName::new(typed.module_path.clone(), ext.name.clone()),
                ext.constraints.clone(),
            );
        }
    }

    // Add instance method constraints so lower_fn prepends dict params.
    // Combines impl-head constraints + method-level constraints per method.
    for inst in &typed.instance_defs {
        let impl_constraint_pairs: Vec<(TraitName, TypeVarId)> = inst
            .constraints
            .iter()
            .filter_map(|c| {
                inst.type_var_ids
                    .get(&c.type_var)
                    .map(|&tv| (c.trait_name.clone(), tv))
            })
            .collect();
        for m in &inst.methods {
            let mut all_constraints = impl_constraint_pairs.clone();
            all_constraints.extend(m.constraint_pairs.iter().cloned());
            if all_constraints.is_empty() {
                continue;
            }
            let mangled = typed_ast::mangled_method_name(
                &inst.trait_name.local_name,
                &inst.target_type_name,
                &m.name,
            );
            fn_constraints
                .entry(QualifiedName::new(typed.module_path.clone(), mangled))
                .or_insert_with(|| all_constraints);
        }
    }

    // Build fn_schemes from fn_types
    let mut fn_schemes: HashMap<QualifiedName, TypeScheme> = HashMap::new();
    for entry in &typed.fn_types {
        fn_schemes.insert(entry.qualified_name.clone(), entry.scheme.clone());
    }
    // Also add extern fn schemes so resolve_call_dicts can match type args.
    for ext in &typed.extern_fns {
        if !ext.constraints.is_empty() {
            let vars: Vec<TypeVarId> = ext.constraints.iter().map(|(_, tv)| *tv).collect();
            let fn_ty = krypton_typechecker::types::Type::Fn(
                ext.param_types.clone(),
                Box::new(ext.return_type.clone()),
            );
            fn_schemes.insert(
                QualifiedName::new(typed.module_path.clone(), ext.name.clone()),
                TypeScheme {
                    vars,
                    constraints: ext.constraints.clone(),
                    ty: fn_ty,
                    var_names: HashMap::new(),
                },
            );
        }
    }

    let mut ctx = LowerCtx {
        next_var: 0,
        next_fn: 0,
        type_var_gen: TypeVarGen::new(),
        var_scope: HashMap::new(),
        fn_ids: HashMap::new(),
        callable_ids: HashMap::new(),
        struct_fields: HashMap::new(),
        sum_variants: HashMap::new(),
        private_type_params: HashMap::new(),
        fn_constraints,
        dict_params: HashMap::new(),
        fn_schemes,
        module_path: typed.module_path.clone(),
        param_instances: {
            let local_param = typed
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
                    source_module: typed.module_path.clone(),
                    target_type_name: inst.target_type_name.clone(),
                });
            let imported_param = link_view
                .all_instances()
                .into_iter()
                .filter(|(path, _)| path.as_str() != typed.module_path)
                .filter(|(_, inst)| !inst.constraints.is_empty())
                .map(|(path, inst)| ParamInstanceInfo {
                    trait_name: inst.trait_name.clone(),
                    target_type: inst.target_type.clone(),
                    type_var_ids: inst.type_var_ids.clone(),
                    constraints: inst
                        .constraints
                        .iter()
                        .map(|c| (c.trait_name.clone(), c.type_var.clone()))
                        .collect(),
                    source_module: path.as_str().to_string(),
                    target_type_name: inst.target_type_name.clone(),
                });
            local_param.chain(imported_param).collect()
        },
        trait_method_types: typed
            .trait_defs
            .iter()
            .map(|t| {
                (
                    t.trait_id.clone(),
                    (t.type_var_id, t.method_tc_types.clone()),
                )
            })
            .collect(),
        trait_method_constraints: typed
            .trait_defs
            .iter()
            .filter(|t| !t.method_constraints.is_empty())
            .map(|t| (t.trait_id.clone(), t.method_constraints.clone()))
            .collect(),
        dict_depth: 0,
        lifted_fns: vec![],
        var_types: HashMap::new(),
        recur_join: None,
        early_return_join: None,
        auto_close: typed.auto_close.clone(),
        fn_exit_track: HashSet::new(),
        fn_exit_vars: HashMap::new(),
        fn_exit_closes: HashMap::new(),
        all_instances: {
            let mut infos = Vec::new();
            for inst in &typed.instance_defs {
                infos.push(InstanceSourceInfo {
                    trait_name: inst.trait_name.clone(),
                    target_type: inst.target_type.clone(),
                    target_type_name: inst.target_type_name.clone(),
                    source_module: typed.module_path.clone(),
                });
            }
            for (path, inst) in link_view.all_instances() {
                if path.as_str() != typed.module_path {
                    infos.push(InstanceSourceInfo {
                        trait_name: inst.trait_name.clone(),
                        target_type: inst.target_type.clone(),
                        target_type_name: inst.target_type_name.clone(),
                        source_module: path.as_str().to_string(),
                    });
                }
            }
            infos
        },
        instance_exact_index: HashMap::new(), // populated below
    };
    // Build exact-match index for instance resolution
    for (i, info) in ctx.all_instances.iter().enumerate() {
        let key = (info.trait_name.local_name.clone(), info.target_type_name.clone());
        ctx.instance_exact_index.entry(key).or_insert(i);
    }

    // 1. Build struct_fields from exported_type_infos (has resolved Types + real TypeVarIds)
    //    Sort by name for deterministic TypeVarId allocation order.
    let mut sorted_type_infos: Vec<_> = typed.exported_type_infos.iter().collect();
    sorted_type_infos.sort_by_key(|(name, _)| name.as_str());
    for (name, info) in &sorted_type_infos {
        let type_ref = typed_ast::ResolvedTypeRef {
            qualified_name: QualifiedName::new(info.source_module.clone(), (*name).clone()),
        };
        if let ExportedTypeKind::Record { fields } = &info.kind {
            ctx.struct_fields.insert(type_ref, fields.clone());
        }
    }
    // Fallback: private structs not in exported_type_infos
    for decl in &typed.struct_decls {
        let type_ref = typed_ast::ResolvedTypeRef {
            qualified_name: decl.qualified_name.clone(),
        };
        if !ctx.struct_fields.contains_key(&type_ref) {
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
            ctx.struct_fields.insert(type_ref, fields);
        }
    }

    // 2. Build sum_variants from exported_type_infos
    for (name, info) in &sorted_type_infos {
        if let ExportedTypeKind::Sum { variants } = &info.kind {
            let type_ref = typed_ast::ResolvedTypeRef {
                qualified_name: QualifiedName::new(info.source_module.clone(), (*name).clone()),
            };
            for (tag, variant) in variants.iter().enumerate() {
                ctx.sum_variants.insert(
                    typed_ast::ResolvedVariantRef {
                        type_ref: type_ref.clone(),
                        variant_name: variant.name.clone(),
                    },
                    (tag as u32, variant.fields.clone()),
                );
            }
        }
    }
    // Fallback: private sum types
    for decl in &typed.sum_decls {
        let already = decl.variants.iter().any(|v| {
            ctx.sum_variants
                .contains_key(&typed_ast::ResolvedVariantRef {
                    type_ref: typed_ast::ResolvedTypeRef {
                        qualified_name: decl.qualified_name.clone(),
                    },
                    variant_name: v.name.clone(),
                })
        });
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
                    typed_ast::ResolvedVariantRef {
                        type_ref: typed_ast::ResolvedTypeRef {
                            qualified_name: decl.qualified_name.clone(),
                        },
                        variant_name: variant.name.clone(),
                    },
                    (tag as u32, fields),
                );
            }
        }
    }

    // 3. Allocate FnIds for all known functions
    // Local function definitions
    for decl in &typed.functions {
        let fn_id = ctx.fresh_fn();
        ctx.fn_ids.insert(decl.name.clone(), fn_id);
        ctx.callable_ids.insert(
            QualifiedName::new(typed.module_path.clone(), decl.name.clone()),
            fn_id,
        );
    }
    // Extern functions (local)
    for ext in &typed.extern_fns {
        if !ctx.fn_ids.contains_key(&ext.name) {
            let fn_id = ctx.fresh_fn();
            ctx.fn_ids.insert(ext.name.clone(), fn_id);
            ctx.callable_ids.insert(
                QualifiedName::new(ext.declaring_module_path.clone(), ext.name.clone()),
                fn_id,
            );
        }
    }
    // Imported functions (from fn_types entries with provenance)
    for entry in &typed.fn_types {
        // Nullary constructors have Type::Named, not Type::Fn.
        // They lower to ConstructVariant, never produce FnDefs.
        if !matches!(entry.scheme.ty, Type::Fn(..)) {
            continue;
        }
        if !ctx.fn_ids.contains_key(&entry.name) {
            let fn_id = ctx.fresh_fn();
            ctx.fn_ids.insert(entry.name.clone(), fn_id);
            ctx.callable_ids.insert(entry.qualified_name.clone(), fn_id);
        } else if !ctx.callable_ids.contains_key(&entry.qualified_name) {
            // The binding name already has a FnId (e.g., from an extern declaration).
            // Ensure the canonical qualified_name also maps to the same FnId.
            let fn_id = ctx.fn_ids[&entry.name];
            ctx.callable_ids.insert(entry.qualified_name.clone(), fn_id);
        }
    }

    // 3b. Register compiler intrinsics
    for &name in crate::COMPILER_INTRINSICS {
        if !ctx.fn_ids.contains_key(name) {
            let fn_id = ctx.fresh_fn();
            ctx.fn_ids.insert(name.to_string(), fn_id);
            ctx.callable_ids.insert(
                QualifiedName::new("__builtin__".to_string(), name.to_string()),
                fn_id,
            );
        }
    }

    // 4. Lower struct definitions (skip imported types)
    let structs: Vec<StructDef> = typed
        .struct_decls
        .iter()
        .filter(|decl| decl.qualified_name.module_path == typed.module_path)
        .map(|decl| {
            let (type_params, fields) =
                if let Some(info) = typed.exported_type_infos.get(&decl.name) {
                    let type_ref = typed_ast::ResolvedTypeRef {
                        qualified_name: QualifiedName::new(
                            info.source_module.clone(),
                            decl.name.clone(),
                        ),
                    };
                    // Struct with no fields has empty field list
                    let fields = ctx
                        .struct_fields
                        .get(&type_ref)
                        .cloned()
                        .unwrap_or_default();
                    (info.type_param_vars.clone(), fields)
                } else {
                    // Private type — reuse cached TypeVarIds from step 1
                    // Types without type parameters have no entry
                    let type_params = ctx
                        .private_type_params
                        .get(&decl.name)
                        .cloned()
                        .unwrap_or_default();
                    let type_ref = typed_ast::ResolvedTypeRef {
                        qualified_name: decl.qualified_name.clone(),
                    };
                    // Struct with no fields has empty field list
                    let fields = ctx
                        .struct_fields
                        .get(&type_ref)
                        .cloned()
                        .unwrap_or_default();
                    (type_params, fields)
                };
            StructDef {
                name: decl.name.clone(),
                type_params,
                fields: fields.into_iter().map(|(n, t)| (n, t.into())).collect(),
            }
        })
        .collect();

    // 5. Lower sum type definitions (skip imported types)
    let sum_types: Vec<SumTypeDef> = typed
        .sum_decls
        .iter()
        .filter(|decl| decl.qualified_name.module_path == typed.module_path)
        .map(|decl| {
            let type_params = if let Some(info) = typed.exported_type_infos.get(&decl.name) {
                info.type_param_vars.clone()
            } else {
                // Types without type parameters have no entry
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
                    let variant_ref = typed_ast::ResolvedVariantRef {
                        type_ref: typed_ast::ResolvedTypeRef {
                            qualified_name: decl.qualified_name.clone(),
                        },
                        variant_name: v.name.clone(),
                    };
                    // Variant with no payload fields has empty field list
                    let fields = ctx
                        .sum_variants
                        .get(&variant_ref)
                        .map(|(_, f)| f.clone())
                        .unwrap_or_default();
                    VariantDef {
                        name: v.name.clone(),
                        tag: tag as u32,
                        fields: fields.into_iter().map(|t| t.into()).collect(),
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

    // 7. Build fn_identities lookup (includes lifted lambdas registered in fn_ids)
    let callable_by_id: HashMap<FnId, &QualifiedName> = ctx
        .callable_ids
        .iter()
        .map(|(qn, &fid)| (fid, qn))
        .collect();
    let mut fn_identities = HashMap::new();
    for (name, &id) in &ctx.fn_ids {
        if let Some(existing) = fn_identities.get(&id) {
            let existing_name: &str = match existing {
                FnIdentity::Local { name } => name,
                FnIdentity::Imported { local_alias, .. } => local_alias,
                FnIdentity::Extern { name, .. } => name,
                FnIdentity::Intrinsic { name } => name,
            };
            assert_eq!(
                existing_name, name,
                "ICE: FnId {:?} maps to both '{}' and '{}'",
                id, existing_name, name
            );
            continue;
        }
        // Determine identity variant
        let identity = if crate::COMPILER_INTRINSICS.contains(&name.as_str()) {
            FnIdentity::Intrinsic { name: name.clone() }
        } else if let Some(qn) = callable_by_id.get(&id) {
            if qn.module_path == "__builtin__" {
                FnIdentity::Intrinsic { name: name.clone() }
            } else if qn.module_path == ctx.module_path {
                FnIdentity::Local { name: name.clone() }
            } else {
                FnIdentity::Imported {
                    canonical: CanonicalRef {
                        module: ModulePath::new(qn.module_path.clone()),
                        symbol: LocalSymbolKey::Function(qn.local_name.clone()),
                    },
                    local_alias: name.clone(),
                }
            }
        } else {
            // Not in callable_ids: lifted synthetics (lambda$, ctor$, fn_ref$, trait_ref$).
            FnIdentity::Local { name: name.clone() }
        };
        fn_identities.insert(id, identity);
    }

    // 8. Build extern_fns from local definitions only.
    //    Cross-module extern fns are in module.imported_extern_fns.
    //    Build a lookup from trait_name → extern trait info for bridge params.
    let extern_trait_lookup: HashMap<&krypton_typechecker::typed_ast::TraitName, &krypton_typechecker::typed_ast::ExternTraitInfo> =
        typed.extern_traits.iter().map(|et| (&et.trait_name, et)).collect();
    // Build a lookup from function name → constraints for bridge detection.
    let mut fn_constraints_by_name: HashMap<&str, &[(krypton_typechecker::typed_ast::TraitName, krypton_typechecker::types::TypeVarId)]> =
        typed.fn_types.iter()
            .filter(|e| !e.scheme.constraints.is_empty())
            .map(|e| (e.name.as_str(), e.scheme.constraints.as_slice()))
            .collect();
    // Also include extern function constraints so bridge_params is correctly populated.
    for ext in &typed.extern_fns {
        if !ext.constraints.is_empty() {
            fn_constraints_by_name.entry(ext.name.as_str()).or_insert(ext.constraints.as_slice());
        }
    }
    let mut extern_fns = vec![];
    for ext in &typed.extern_fns {
        if let Some(&fn_id) = ctx.fn_ids.get(&ext.name) {
            let ir_target = match &ext.target {
                krypton_parser::ast::ExternTarget::Java => ExternTarget::Java {
                    class: ext.module_path.clone(),
                },
                krypton_parser::ast::ExternTarget::Js => ExternTarget::Js {
                    module: ext.module_path.clone(),
                },
            };
            // Build bridge_params: for each parameter, check if it corresponds to
            // a type variable constrained by an extern trait in this function's where-clause.
            let fn_constraints = fn_constraints_by_name.get(ext.name.as_str()).copied().unwrap_or(&[]);
            let bridge_params = ext.param_types.iter().map(|param_ty| {
                if let krypton_typechecker::types::Type::Var(tv_id) = param_ty {
                    // Check if this type var has an extern trait constraint
                    for (trait_name, constrained_tv) in fn_constraints {
                        if *constrained_tv == *tv_id {
                            if let Some(et_info) = extern_trait_lookup.get(trait_name) {
                                return Some(ExternTraitBridge {
                                    trait_name: trait_name.clone(),
                                    java_interface: et_info.java_interface.clone(),
                                });
                            }
                        }
                    }
                }
                None
            }).collect();
            let call_kind = if ext.constructor {
                ExternCallKind::Constructor
            } else if ext.instance {
                ExternCallKind::Instance
            } else {
                ExternCallKind::Static
            };
            extern_fns.push(ExternFnDef {
                id: fn_id,
                name: ext.name.clone(),
                declaring_module_path: ext.declaring_module_path.clone(),
                span: ext.span,
                target: ir_target,
                nullable: ext.nullable,
                throws: ext.throws,
                call_kind,
                param_types: ext.param_types.iter().cloned().map(Into::into).collect(),
                return_type: ext.return_type.clone().into(),
                bridge_params,
            });
        }
    }

    // 9. Build extern_traits from local definitions.
    let extern_traits: Vec<ExternTraitDef> = typed.extern_traits.iter().map(|et| {
        ExternTraitDef {
            trait_name: et.trait_name.clone(),
            java_interface: et.java_interface.clone(),
            methods: et.methods.iter().map(|m| {
                ExternTraitMethodDef {
                    name: m.name.clone(),
                    param_types: m.param_types.iter().cloned().map(Into::into).collect(),
                    return_type: m.return_type.clone().into(),
                }
            }).collect(),
        }
    }).collect();

    // 10. Build extern_types from local definitions only (JVM targets only).
    //     Cross-module extern types are in module.imported_extern_types.
    let mut extern_types = vec![];
    for info in &typed.extern_types {
        if info.target == krypton_parser::ast::ExternTarget::Java {
            extern_types.push(ExternTypeDef {
                name: info.krypton_name.clone(),
                target: ExternTarget::Java {
                    class: info.host_module.clone(),
                },
            });
        }
    }

    // 11. Build imported_fns from fn_types entries with provenance.
    //     Trait methods (origin.is_some()) are dispatched via TraitCall, never
    //     via Call, so they are not imported as regular functions.
    //     Deduplicate by (name, source_module): constructors can appear in
    //     fn_types from both exported_fn_types and type processing paths.
    let mut imported_fns = vec![];
    let mut imported_fn_seen: HashSet<(String, String)> = HashSet::new();
    for entry in &typed.fn_types {
        if entry.origin.is_some() {
            continue;
        }
        // Nullary constructors lower to ConstructVariant, not imported function calls.
        if !matches!(entry.scheme.ty, Type::Fn(..)) {
            continue;
        }
        if entry.qualified_name.module_path != typed.module_path {
            let key = (entry.name.clone(), entry.qualified_name.module_path.clone());
            if !imported_fn_seen.insert(key) {
                continue;
            }
            if let Some(&fn_id) = ctx.callable_ids.get(&entry.qualified_name) {
                let Type::Fn(param_types, ret) = &entry.scheme.ty else {
                    unreachable!()
                };
                imported_fns.push(ImportedFnDef {
                    id: fn_id,
                    name: entry.name.clone(),
                    source_module: entry.qualified_name.module_path.clone(),
                    original_name: entry.qualified_name.local_name.clone(),
                    param_types: param_types.iter().cloned().map(Into::into).collect(),
                    return_type: (**ret).clone().into(),
                });
            }
        }
    }

    // 12. Build trait definitions from typed_module trait_defs
    let mut traits = vec![];
    for trait_def in &typed.trait_defs {
        let methods = trait_def
            .methods
            .iter()
            .map(|(method_name, param_count)| {
                let (param_types, return_type) = trait_def
                    .method_tc_types
                    .get(method_name)
                    .cloned()
                    .ok_or_else(|| LowerError::InternalError(format!(
                        "trait method {method_name} has no type info in method_tc_types"
                    )))?;
                let method_constraint_count = trait_def
                    .method_constraints
                    .get(method_name)
                    .map(|c| c.len())
                    .unwrap_or(0);
                Ok(TraitMethodDef {
                    name: method_name.clone(),
                    param_count: *param_count + method_constraint_count,
                    param_types: param_types.into_iter().map(Into::into).collect(),
                    return_type: return_type.into(),
                })
            })
            .collect::<Result<Vec<_>, LowerError>>()?;
        traits.push(TraitDef {
            name: trait_def.name.clone(),
            trait_name: trait_def.trait_id.clone(),
            type_var: trait_def.type_var_id,
            methods,
            is_imported: trait_def.is_imported,
        });
    }
    traits.sort_by(|a, b| a.name.cmp(&b.name));

    // 13. Build instance definitions from typed_module instance_defs (local + imported)
    let mut instances = vec![];
    // Instance method FnIds are looked up by mangled name (Trait$$Type$$method).
    // For local instances, all methods must have FnIds (allocated during step 3).
    // For imported instances, methods may not be present (they're defined elsewhere).
    let lower_instance = |inst: &krypton_typechecker::typed_ast::InstanceDefInfo,
                          is_imported: bool,
                          ctx: &LowerCtx| {
        let method_fn_ids = if is_imported {
            inst.methods
                .iter()
                .filter_map(|m| {
                    let mangled = typed_ast::mangled_method_name(
                        &inst.trait_name.local_name,
                        &inst.target_type_name,
                        &m.name,
                    );
                    ctx.fn_ids
                        .get(&mangled as &str)
                        .map(|&fn_id| (m.name.clone(), fn_id))
                })
                .collect()
        } else {
            inst.methods
                .iter()
                .map(|m| {
                    let mangled = typed_ast::mangled_method_name(
                        &inst.trait_name.local_name,
                        &inst.target_type_name,
                        &m.name,
                    );
                    let fn_id = ctx
                        .fn_ids
                        .get(&mangled as &str)
                        .unwrap_or_else(|| panic!("ICE: no FnId for instance method {mangled}"));
                    (m.name.clone(), *fn_id)
                })
                .collect()
        };
        let sub_dict_requirements = inst
            .constraints
            .iter()
            .filter_map(|c| {
                inst.type_var_ids
                    .get(&c.type_var)
                    .map(|&tv| (c.trait_name.clone(), tv))
            })
            .collect();
        InstanceDef {
            trait_name: inst.trait_name.clone(),
            target_type: inst.target_type.clone().into(),
            target_type_name: inst.target_type_name.clone(),
            method_fn_ids,
            sub_dict_requirements,
            is_intrinsic: inst.is_intrinsic,
            is_imported,
        }
    };
    for inst in &typed.instance_defs {
        instances.push(lower_instance(inst, false, &ctx));
    }
    // Collect tuple arities from all FnDefs
    let mut tuple_arities = std::collections::BTreeSet::new();
    for func in &functions {
        collect_tuple_arities_from_fn(func, &mut tuple_arities);
    }

    let module = Module {
        name: module_name.to_string(),
        structs,
        sum_types,
        functions,
        fn_identities,
        extern_fns,
        extern_types,
        extern_traits,
        imported_fns,
        traits,
        instances,
        tuple_arities,
        module_path: ModulePath::new(typed.module_path.clone()),
        fn_dict_requirements: {
            // Reconstruct string-keyed dict requirements for codegen:
            // fn_types entries use binding name, instance methods use mangled name.
            let mut reqs: HashMap<String, Vec<(TraitName, TypeVarId)>> = HashMap::new();
            for entry in &typed.fn_types {
                if !entry.scheme.constraints.is_empty() {
                    reqs.insert(entry.name.clone(), entry.scheme.constraints.clone());
                }
            }
            // Also include extern function constraints.
            for ext in &typed.extern_fns {
                if !ext.constraints.is_empty() {
                    reqs.entry(ext.name.clone()).or_insert_with(|| ext.constraints.clone());
                }
            }
            for (qn, v) in &ctx.fn_constraints {
                // Instance method mangled names are local to this module
                if qn.module_path == typed.module_path && !reqs.contains_key(&qn.local_name) {
                    reqs.insert(qn.local_name.clone(), v.clone());
                }
            }
            reqs
        },
        fn_exit_closes: ctx.fn_exit_closes,
    };

    crate::lint::LintPass
        .run(module)
        .map_err(|e| LowerError::InternalError(format!("{}: {}", e.pass, e.message)))
}

// ---------------------------------------------------------------------------
// Free helper functions
// ---------------------------------------------------------------------------

/// Replace tail positions of an expression with `jump target(tail_value)`.
fn replace_tail_with_jump(expr: Expr, target: VarId) -> Expr {
    let span = expr.span;
    let result_ty = expr.ty.clone();
    match expr.kind {
        ExprKind::Atom(atom) => expr_at(
            span,
            result_ty,
            ExprKind::Jump {
                target,
                args: vec![atom],
            },
        ),
        ExprKind::Let {
            bind,
            ty,
            value,
            body,
        } => {
            let new_body = replace_tail_with_jump(*body, target);
            expr_at(
                span,
                result_ty,
                ExprKind::Let {
                    bind,
                    ty,
                    value,
                    body: Box::new(new_body),
                },
            )
        }
        ExprKind::BoolSwitch {
            scrutinee,
            true_body,
            false_body,
        } => expr_at(
            span,
            result_ty,
            ExprKind::BoolSwitch {
                scrutinee,
                true_body: Box::new(replace_tail_with_jump(*true_body, target)),
                false_body: Box::new(replace_tail_with_jump(*false_body, target)),
            },
        ),
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
                    body: replace_tail_with_jump(b.body, target),
                })
                .collect();
            let new_default = default.map(|d| Box::new(replace_tail_with_jump(*d, target)));
            expr_at(
                span,
                result_ty,
                ExprKind::Switch {
                    scrutinee,
                    branches: new_branches,
                    default: new_default,
                },
            )
        }
        ExprKind::LetJoin {
            name,
            params,
            join_body,
            body: join_scope,
            is_recur,
        } => {
            let new_join_body = replace_tail_with_jump(*join_body, target);
            let new_scope = replace_tail_with_jump(*join_scope, target);
            expr_at(
                span,
                result_ty,
                ExprKind::LetJoin {
                    name,
                    params,
                    join_body: Box::new(new_join_body),
                    body: Box::new(new_scope),
                    is_recur,
                },
            )
        }
        // Jump and LetRec shouldn't appear as compound value tails
        _ => expr,
    }
}

fn resolved_ref(expr: &TypedExpr) -> Option<&ResolvedBindingRef> {
    match &expr.kind {
        TypedExprKind::Var(_) => expr.resolved_ref.as_ref(),
        TypedExprKind::TypeApp { expr: inner, .. } => {
            expr.resolved_ref.as_ref().or_else(|| resolved_ref(inner))
        }
        _ => expr.resolved_ref.as_ref(),
    }
}

fn resolved_callable_ref(expr: &TypedExpr) -> Option<(&str, &ResolvedCallableRef)> {
    match &expr.kind {
        TypedExprKind::Var(name) => match resolved_ref(expr) {
            Some(ResolvedBindingRef::Callable(callable_ref)) => Some((name.as_str(), callable_ref)),
            _ => None,
        },
        TypedExprKind::TypeApp { expr: inner, .. } => resolved_callable_ref(inner),
        _ => None,
    }
}

fn resolved_constructor_ref(expr: &TypedExpr) -> Option<(&str, &ResolvedConstructorRef)> {
    match &expr.kind {
        TypedExprKind::Var(name) => match resolved_ref(expr) {
            Some(ResolvedBindingRef::Constructor(constructor_ref)) => {
                Some((name.as_str(), constructor_ref))
            }
            _ => None,
        },
        TypedExprKind::TypeApp { expr: inner, .. } => resolved_constructor_ref(inner),
        _ => None,
    }
}

fn callable_qualified_name(r: &ResolvedCallableRef, _module_path: &str) -> QualifiedName {
    match r {
        ResolvedCallableRef::LocalFunction { qualified_name } => qualified_name.clone(),
        ResolvedCallableRef::ImportedFunction { qualified_name } => qualified_name.clone(),
        ResolvedCallableRef::Intrinsic { name } => {
            QualifiedName::new("__builtin__".to_string(), name.clone())
        }
    }
}

fn resolved_trait_method_ref(expr: &TypedExpr) -> Option<&ResolvedTraitMethodRef> {
    match resolved_ref(expr) {
        Some(ResolvedBindingRef::TraitMethod(trait_ref)) => Some(trait_ref),
        _ => None,
    }
}

/// Extract function name, resolved binding ref, and type_args from a call expression,
/// peeling through TypeApp wrappers. Collects the outermost type_args.
fn extract_call_info(expr: &TypedExpr) -> (Option<String>, Option<ResolvedBindingRef>, Vec<Type>) {
    match &expr.kind {
        TypedExprKind::Var(name) => (Some(name.clone()), expr.resolved_ref.clone(), vec![]),
        TypedExprKind::TypeApp {
            expr: inner,
            type_args,
        } => {
            let (name, resolved_ref, _) = extract_call_info(inner);
            let resolved_ref = resolved_ref.or_else(|| expr.resolved_ref.clone());
            (name, resolved_ref, type_args.clone())
        }
        _ => (None, expr.resolved_ref.clone(), vec![]),
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

fn variant_ref_from_constructor(
    constructor_ref: &ResolvedConstructorRef,
) -> Option<ResolvedVariantRef> {
    (constructor_ref.kind == typed_ast::ConstructorKind::Variant).then(|| ResolvedVariantRef {
        type_ref: constructor_ref.type_ref.clone(),
        variant_name: constructor_ref.constructor_name.clone(),
    })
}

/// Extract the element type from a Vec type (Named or Own(Named)).
fn extract_vec_element_type(ty: &Type) -> Result<Type, LowerError> {
    let named = match ty {
        Type::Named(_, args) => args,
        Type::Own(inner) => match inner.as_ref() {
            Type::Named(_, args) => args,
            other => {
                return Err(LowerError::InternalError(format!(
                    "Vec element type: expected Own(Named), got Own({other:?})"
                )))
            }
        },
        other => {
            return Err(LowerError::InternalError(format!(
                "Vec element type: expected Named or Own(Named), got {other:?}"
            )))
        }
    };
    named.first().cloned().ok_or_else(|| {
        LowerError::InternalError(format!("Vec type has no type args: {ty:?}"))
    })
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
        // Comparison ops (Eq/Neq/Lt/Le/Gt/Ge) are desugared to trait calls in lower_trait_comparison.
        // And/Or handled as Switch in lower_expr (short-circuit semantics).
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
        (Type::Var(id), _) => match bindings.get(id) {
            Some(existing) => existing == actual,
            None => {
                bindings.insert(*id, actual.clone());
                true
            }
        },
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
        (Type::Own(p), a) => bind_type_vars(p, a, bindings),
        (a, Type::Own(p)) => bind_type_vars(a, p, bindings),
        (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
            bind_type_vars(p_ctor, a_ctor, bindings)
                && p_args.len() == a_args.len()
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        // HKT cross-arm: App(Var(f), [a]) vs Named("Box", [Int])
        (Type::App(p_ctor, p_args), Type::Named(a_name, a_args)) => {
            p_args.len() == a_args.len()
                && bind_type_vars(p_ctor, &Type::Named(a_name.clone(), Vec::new()), bindings)
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        // HKT cross-arm: App(Var(f), [a]) vs Fn([Int], Int)
        (Type::App(p_ctor, p_args), Type::Fn(a_params, a_ret))
            if types::decompose_fn_for_app(a_params, a_ret, p_args.len()).is_some() =>
        {
            let (ctor_fn, remaining) =
                types::decompose_fn_for_app(a_params, a_ret, p_args.len()).unwrap();
            bind_type_vars(p_ctor, &ctor_fn, bindings)
                && remaining.len() == p_args.len()
                && p_args
                    .iter()
                    .zip(remaining.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        _ => pattern == actual,
    }
}

// ---------------------------------------------------------------------------
// Tuple arity collection
// ---------------------------------------------------------------------------

fn collect_tuple_arities_from_fn(func: &FnDef, arities: &mut std::collections::BTreeSet<usize>) {
    for (_, ty) in &func.params {
        collect_tuple_arities_from_type(ty, arities);
    }
    collect_tuple_arities_from_type(&func.return_type, arities);
    collect_tuple_arities_from_expr(&func.body, arities);
}

fn collect_tuple_arities_from_type(ty: &IrType, arities: &mut std::collections::BTreeSet<usize>) {
    match ty {
        IrType::Tuple(elems) => {
            arities.insert(elems.len());
            for e in elems {
                collect_tuple_arities_from_type(e, arities);
            }
        }
        IrType::Fn(params, ret) => {
            for p in params {
                collect_tuple_arities_from_type(p, arities);
            }
            collect_tuple_arities_from_type(ret, arities);
        }
        IrType::Named(_, args) => {
            for a in args {
                collect_tuple_arities_from_type(a, arities);
            }
        }
        IrType::Own(inner) => collect_tuple_arities_from_type(inner, arities),
        IrType::Dict { target, .. } => collect_tuple_arities_from_type(target, arities),
        _ => {}
    }
}

fn collect_tuple_arities_from_expr(expr: &Expr, arities: &mut std::collections::BTreeSet<usize>) {
    collect_tuple_arities_from_type(&expr.ty, arities);
    match &expr.kind {
        ExprKind::Let {
            ty, value, body, ..
        } => {
            collect_tuple_arities_from_type(ty, arities);
            collect_tuple_arities_from_simple(value, arities);
            collect_tuple_arities_from_expr(body, arities);
        }
        ExprKind::LetRec { bindings, body } => {
            for (_, ty, _, _) in bindings {
                collect_tuple_arities_from_type(ty, arities);
            }
            collect_tuple_arities_from_expr(body, arities);
        }
        ExprKind::LetJoin {
            params,
            join_body,
            body,
            ..
        } => {
            for (_, ty) in params {
                collect_tuple_arities_from_type(ty, arities);
            }
            collect_tuple_arities_from_expr(join_body, arities);
            collect_tuple_arities_from_expr(body, arities);
        }
        ExprKind::BoolSwitch {
            true_body,
            false_body,
            ..
        } => {
            collect_tuple_arities_from_expr(true_body, arities);
            collect_tuple_arities_from_expr(false_body, arities);
        }
        ExprKind::Switch {
            branches, default, ..
        } => {
            for branch in branches {
                for (_, ty) in &branch.bindings {
                    collect_tuple_arities_from_type(ty, arities);
                }
                collect_tuple_arities_from_expr(&branch.body, arities);
            }
            if let Some(d) = default {
                collect_tuple_arities_from_expr(d, arities);
            }
        }
        ExprKind::Jump { .. } | ExprKind::Atom(_) => {}
    }
}

fn collect_tuple_arities_from_simple(
    expr: &SimpleExpr,
    arities: &mut std::collections::BTreeSet<usize>,
) {
    match &expr.kind {
        SimpleExprKind::MakeTuple { elements } => {
            arities.insert(elements.len());
        }
        SimpleExprKind::MakeVec { element_type, .. } => {
            collect_tuple_arities_from_type(element_type, arities);
        }
        _ => {}
    }
}

/// Lower all typed modules to IR and collect their source texts.
///
/// The first module is treated as the root: its IR name is set to `root_name`,
/// while subsequent modules keep their `module_path`.
///
/// Returns `(ir_modules, module_sources)` where `module_sources` maps
/// `module_path → source_text` for error rendering during codegen.
pub fn lower_all(
    typed_modules: &[TypedModule],
    root_name: &str,
    link_ctx: &LinkContext,
) -> Result<(Vec<Module>, HashMap<String, String>), LowerError> {
    let root_module_path = typed_modules
        .first()
        .map(|tm| tm.module_path.as_str())
        .unwrap_or("");

    let mut ir_modules = Vec::with_capacity(typed_modules.len());
    let mut module_sources: HashMap<String, String> = HashMap::new();

    for tm in typed_modules {
        let is_root = tm.module_path == root_module_path;
        let mod_name = if is_root { root_name } else { &tm.module_path };
        let view = link_ctx
            .view_for(&krypton_typechecker::module_interface::ModulePath::new(
                &tm.module_path,
            ))
            .unwrap_or_else(|| {
                panic!("ICE: no LinkContext view for module '{}'", tm.module_path)
            });
        let ir = lower_module(tm, mod_name, &view)?;
        ir_modules.push(ir);
        if let Some(src) = &tm.module_source {
            module_sources.insert(tm.module_path.clone(), src.clone());
        }
    }

    Ok((ir_modules, module_sources))
}
