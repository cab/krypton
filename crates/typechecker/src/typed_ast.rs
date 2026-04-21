use rustc_hash::FxHashMap;
use std::fmt;
use std::ops::Deref;

use crate::types::{SchemeVarId, Substitution, Type, TypeScheme, TypeVarId};
use krypton_parser::ast::{BinOp, Lit, ParamMode, Span, TypeExpr, UnaryOp, Variant, Visibility};

/// Whether a generic parameter requires unlimited (U) qualifier or is polymorphic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamQualifier {
    /// Used more than once in the body — caller must not pass affine values.
    RequiresU,
    /// Used at most once — accepts both affine and unlimited values.
    Polymorphic,
}

/// Module-qualified name: always carries the defining module's path and the bare local name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct QualifiedName {
    /// Module path, e.g., "core/semigroup".
    pub module_path: String,
    /// Bare local name, e.g., "Semigroup".
    pub local_name: String,
}

impl QualifiedName {
    pub fn new(module_path: String, local_name: String) -> Self {
        assert!(
            !module_path.is_empty(),
            "ICE: QualifiedName created with empty module_path for `{local_name}`"
        );
        QualifiedName {
            module_path,
            local_name,
        }
    }

    pub fn display_name(&self) -> &str {
        &self.local_name
    }
}

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.module_path, self.local_name)
    }
}

/// Module-qualified trait identity (newtype over QualifiedName for type safety).
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TraitName(pub QualifiedName);

impl TraitName {
    pub fn new(module_path: String, name: String) -> Self {
        TraitName(QualifiedName::new(module_path, name))
    }

    pub fn display_name(&self) -> &str {
        self.0.display_name()
    }

    // Core trait constructors
    pub fn core_eq() -> Self {
        TraitName::new("core/eq".into(), "Eq".into())
    }
    pub fn core_ord() -> Self {
        TraitName::new("core/ord".into(), "Ord".into())
    }
    pub fn core_semigroup() -> Self {
        TraitName::new("core/semigroup".into(), "Semigroup".into())
    }
    pub fn core_sub() -> Self {
        TraitName::new("core/sub".into(), "Sub".into())
    }
    pub fn core_mul() -> Self {
        TraitName::new("core/mul".into(), "Mul".into())
    }
    pub fn core_div() -> Self {
        TraitName::new("core/div".into(), "Div".into())
    }
    pub fn core_neg() -> Self {
        TraitName::new("core/neg".into(), "Neg".into())
    }
    pub fn core_disposable() -> Self {
        TraitName::new("core/disposable".into(), "Disposable".into())
    }
}

impl Deref for TraitName {
    type Target = QualifiedName;
    fn deref(&self) -> &QualifiedName {
        &self.0
    }
}

impl fmt::Display for TraitName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

/// Internal: imported function with full provenance.
#[derive(Debug, Clone)]
pub struct ImportedFn {
    pub name: String,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
    pub qualified_name: QualifiedName,
    pub is_prelude: bool,
}

/// Canonical signature of a winning overload candidate.
///
/// Populated only when an overload set had more than one candidate and a
/// specific one was selected at a call site. `None` on `ResolvedCallableRef`
/// means "no overload was involved" — IR/codegen can take the fast,
/// name-keyed path. When set, `param_types` are stripped of `ParamMode` and
/// have the committed `Substitution` applied (polymorphic type vars
/// preserved); IR uses `crate::overload::types_overlap` to match this
/// signature against each known overload's signature to pick the FnId.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OverloadSignature {
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedCallableRef {
    LocalFunction {
        qualified_name: QualifiedName,
        overload_signature: Option<OverloadSignature>,
    },
    ImportedFunction {
        qualified_name: QualifiedName,
        overload_signature: Option<OverloadSignature>,
    },
    Intrinsic {
        name: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedTraitMethodRef {
    pub trait_name: TraitName,
    pub method_name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstructorKind {
    Record,
    Variant,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResolvedTypeRef {
    pub qualified_name: QualifiedName,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResolvedConstructorRef {
    pub type_ref: ResolvedTypeRef,
    pub constructor_name: String,
    pub kind: ConstructorKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResolvedVariantRef {
    pub type_ref: ResolvedTypeRef,
    pub variant_name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedBindingRef {
    Callable(ResolvedCallableRef),
    Constructor(ResolvedConstructorRef),
    TraitMethod(ResolvedTraitMethodRef),
}

/// Entry in fn_types — local or imported function visible in a module.
#[derive(Debug, Clone)]
pub struct FnTypeEntry {
    pub name: String,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
    pub qualified_name: QualifiedName,
}

#[derive(Debug, Clone)]
pub struct AutoCloseBinding {
    pub name: String,
    pub type_name: String,
}

#[derive(Debug, Clone, Default)]
pub struct AutoCloseInfo {
    /// Shadow point: let_span → old binding to close before new binding takes effect
    pub shadow_closes: FxHashMap<Span, AutoCloseBinding>,
    /// QuestionMark early return: qm_span → bindings to close before early return (LIFO order)
    pub early_returns: FxHashMap<Span, Vec<AutoCloseBinding>>,
    /// Recur back-edge: recur_span → bindings to close before jumping back (LIFO order)
    pub recur_closes: FxHashMap<Span, Vec<AutoCloseBinding>>,
    /// Move/consumption sites: arg_span → consumed bindings
    pub consumptions: FxHashMap<Span, Vec<AutoCloseBinding>>,
    /// Block scope exits: scope_id → bindings to close at that scope's tail,
    /// in LIFO order (reverse of declaration order).
    pub scope_exits: FxHashMap<ScopeId, Vec<AutoCloseBinding>>,
}

#[derive(Debug, Clone)]
pub enum TypedPattern {
    Wildcard {
        ty: Type,
        span: Span,
    },
    Var {
        name: String,
        ty: Type,
        span: Span,
    },
    Constructor {
        name: String,
        args: Vec<TypedPattern>,
        ty: Type,
        span: Span,
        resolved_variant_ref: Option<ResolvedVariantRef>,
    },
    Lit {
        value: Lit,
        ty: Type,
        span: Span,
    },
    Tuple {
        elements: Vec<TypedPattern>,
        ty: Type,
        span: Span,
    },
    StructPat {
        name: String,
        fields: Vec<(String, TypedPattern)>,
        rest: bool,
        ty: Type,
        span: Span,
        resolved_type_ref: Option<ResolvedTypeRef>,
    },
    Or {
        alternatives: Vec<TypedPattern>,
        ty: Type,
        span: Span,
    },
}

/// Unique identity for a lexical scope node (Do / Let{body:Some} /
/// LetPattern{body:Some} / function body). Allocated by `scope_ids`
/// pre-pass and consumed by both auto-close analysis and IR lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(pub u32);

impl fmt::Display for ScopeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "scope#{}", self.0)
    }
}

/// Unique identity for an `App` node whose overload resolution was deferred.
/// Stamped directly on the `App` variant of `TypedExprKind`, so only `App`
/// nodes can carry this marker — a compile-time guarantee that non-call
/// expressions never end up in the deferred-overloads work queue. The
/// post-inference patcher matches on this id instead of relying on span
/// uniqueness (desugaring that copies spans would otherwise break lookup).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeferredId(pub u32);

#[derive(Debug, Clone)]
pub struct TypedExpr {
    pub kind: TypedExprKind,
    pub ty: Type,
    pub span: Span,
    /// Set for resolved callable/trait bindings that survived lookup.
    /// Local/body-local variables leave this as None.
    pub resolved_ref: Option<ResolvedBindingRef>,
    /// Unique scope identity, `Some` only on Do, Let{body:Some},
    /// LetPattern{body:Some}, and function body / Lambda body nodes.
    /// Stamped by the `scope_ids` pre-pass.
    pub scope_id: Option<ScopeId>,
}

#[derive(Debug, Clone)]
pub enum TypedExprKind {
    Lit(Lit),
    Var(String),
    App {
        func: Box<TypedExpr>,
        args: Vec<TypedExpr>,
        param_modes: Vec<ParamMode>,
        /// `Some` while overload resolution is deferred to the post-inference
        /// pass. Cleared to `None` by the patcher once a winning candidate is
        /// committed — any `Some(_)` surviving the pass indicates a bug.
        deferred_id: Option<DeferredId>,
    },
    TypeApp {
        expr: Box<TypedExpr>,
        /// Explicit user-supplied bindings, each keyed by a canonical
        /// (unfreshened) scheme variable. IR consumers apply these directly,
        /// without positional re-derivation against a trait/scheme's
        /// type-var list. `SchemeVarId` witnesses that the ID is a scheme
        /// parameter, so a freshened `TypeVarId` can't be passed by mistake.
        type_bindings: Vec<(SchemeVarId, Type)>,
    },
    If {
        cond: Box<TypedExpr>,
        then_: Box<TypedExpr>,
        else_: Box<TypedExpr>,
    },
    Let {
        name: String,
        value: Box<TypedExpr>,
        body: Option<Box<TypedExpr>>,
    },
    Do(Vec<TypedExpr>),
    Match {
        scrutinee: Box<TypedExpr>,
        arms: Vec<TypedMatchArm>,
    },
    Lambda {
        params: Vec<String>,
        body: Box<TypedExpr>,
    },
    FieldAccess {
        expr: Box<TypedExpr>,
        field: String,
        resolved_type_ref: Option<ResolvedTypeRef>,
    },
    Recur {
        args: Vec<TypedExpr>,
        param_modes: Vec<crate::types::ParamMode>,
    },
    Tuple(Vec<TypedExpr>),
    BinaryOp {
        op: BinOp,
        lhs: Box<TypedExpr>,
        rhs: Box<TypedExpr>,
    },
    UnaryOp {
        op: UnaryOp,
        operand: Box<TypedExpr>,
    },
    StructLit {
        name: String,
        fields: Vec<(String, TypedExpr)>,
        resolved_type_ref: Option<ResolvedTypeRef>,
    },
    StructUpdate {
        base: Box<TypedExpr>,
        fields: Vec<(String, TypedExpr)>,
    },
    LetPattern {
        pattern: TypedPattern,
        value: Box<TypedExpr>,
        body: Option<Box<TypedExpr>>,
    },
    QuestionMark {
        expr: Box<TypedExpr>,
        is_option: bool, // true=Option, false=Result
    },
    VecLit(Vec<TypedExpr>),
    /// Compiler-only node: consumes an owned value and produces Unit.
    /// Used by derived extern dispose to discharge linearity without destructuring.
    Discharge(Box<TypedExpr>),
}

#[derive(Debug, Clone)]
pub struct TypedMatchArm {
    pub pattern: TypedPattern,
    pub guard: Option<Box<TypedExpr>>,
    pub body: TypedExpr,
}

#[derive(Debug, Clone)]
pub struct TypedParam {
    pub name: String,
    pub mode: crate::types::ParamMode,
}

#[derive(Debug, Clone)]
pub struct TypedFnDecl {
    pub name: String,
    pub visibility: Visibility,
    pub params: Vec<TypedParam>,
    pub body: TypedExpr,
    /// For Disposable dispose impl methods, the target type name (e.g., "Handle").
    /// Used by auto-close to skip the self parameter and avoid infinite recursion.
    pub close_self_type: Option<String>,
    /// Identity of the function-level lexical scope. Owns the fn parameters
    /// and is the parent of the body's own scope (if the body is a Do/Let).
    /// Allocated by `scope_ids::stamp_functions`. The sentinel `ScopeId(u32::MAX)`
    /// is used at construction time before stamping.
    pub fn_scope_id: ScopeId,
    /// Definition span (start, end) of the `fun` declaration. Used as the
    /// stable sort key that decides which overload sibling keeps the bare
    /// mangled symbol.
    pub def_span: Span,
    /// Final mangled wire-format name used by codegen. Stamped at typechecking
    /// time from the same shared mangler used for `ExportedFnSummary` so
    /// IR/codegen cannot disagree. For non-overloaded fns this equals `name`.
    pub exported_symbol: String,
}

/// A function exported from a module's public API, with optional definition span.
#[derive(Debug, Clone)]
pub struct ExportedFn {
    pub name: String,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
    pub def_span: Option<Span>,
    /// For re-exports, the original defining module + local name.
    /// `None` for locally-defined exports.
    pub qualified_name: Option<QualifiedName>,
}

pub struct TraitDefInfo {
    pub name: String,
    pub trait_id: TraitName,
    pub methods: Vec<(String, usize)>, // (method_name, param_count)
    pub is_imported: bool,
    pub type_var_id: TypeVarId,
    /// All trait type parameter ids in declaration order. For single-parameter
    /// traits this has length 1 (`type_var_ids[0] == type_var_id`); for
    /// multi-parameter traits it carries all params.
    pub type_var_ids: Vec<TypeVarId>,
    pub method_tc_types: FxHashMap<String, (Vec<(crate::types::ParamMode, Type)>, Type)>, // name -> (param_types, return_type)
    /// Method-level constraints: method_name -> Vec<(TraitName, Vec<TypeVarId>)>
    pub method_constraints: FxHashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
    /// Direct superclasses with resolved type arguments over this trait's own
    /// `type_var_ids` (always in the local TypeVarId namespace — for imported
    /// traits, the args are remapped at import time, not core's originals).
    pub superclasses: Vec<(TraitName, Vec<Type>)>,
}

#[derive(Clone)]
pub struct ExportedTraitDef {
    pub visibility: Visibility,
    pub name: String,
    pub module_path: String,
    pub type_var: String,
    pub type_var_id: TypeVarId,
    /// All trait type parameter ids in declaration order. `type_var_ids[0] == type_var_id`.
    /// Length 1 for single-parameter traits, N for multi-parameter traits.
    pub type_var_ids: Vec<TypeVarId>,
    /// Names parallel to `type_var_ids`.
    pub type_var_names: Vec<String>,
    /// 0 = kind *, 1 = * -> *, etc.
    pub type_var_arity: usize,
    /// Superclass constraints as resolved type arguments over this trait's
    /// own `type_var_ids`. See `TraitInfo.superclasses` for the shape rationale.
    pub superclasses: Vec<(TraitName, Vec<crate::types::Type>)>,
    pub methods: Vec<ExportedTraitMethod>,
}

#[derive(Clone)]
pub struct ExportedTraitMethod {
    pub name: String,
    pub param_types: Vec<(crate::types::ParamMode, Type)>,
    pub return_type: Type,
    /// Method-level constraints on method's own type parameters.
    /// TypeVarIds here are the method's own vars (not the trait's type param), so they don't
    /// need remapping during import (only the trait's type var is remapped).
    pub constraints: Vec<(TraitName, Vec<TypeVarId>)>,
}

#[derive(Clone)]
pub struct InstanceMethod {
    pub name: String,            // original method name, e.g. "show"
    pub params: Vec<TypedParam>, // parameter names + modes
    pub body: TypedExpr,         // typed method body
    pub scheme: TypeScheme,      // type scheme for the method
    /// Method-level constraints as resolved (TraitName, Vec<TypeVarId>) pairs for IR lowering.
    pub constraint_pairs: Vec<(TraitName, Vec<TypeVarId>)>,
}

/// A type constraint with its trait name already resolved to a full TraitName.
/// `type_vars` has length 1 for single-parameter trait constraints and N for
/// multi-parameter trait constraints (e.g. `Convert[a, b]` → `type_vars = ["a", "b"]`).
#[derive(Clone, Debug)]
pub struct ResolvedConstraint {
    pub trait_name: TraitName,
    pub type_vars: Vec<String>,
    pub span: Span,
}

#[derive(Clone)]
pub struct InstanceDefInfo {
    pub trait_name: TraitName,
    /// Joined display form of the type arguments (e.g., `"Int, String"`).
    pub target_type_name: String,
    /// Type arguments. Length 1 for single-parameter traits, N for multi-parameter.
    pub target_types: Vec<Type>,
    pub type_var_ids: FxHashMap<String, TypeVarId>,
    pub constraints: Vec<ResolvedConstraint>,
    pub methods: Vec<InstanceMethod>,
    pub is_intrinsic: bool, // true when all method bodies are intrinsic()
}

#[derive(Clone)]
pub struct ExternFnInfo {
    pub name: String,
    pub declaring_module_path: String,
    pub span: Span,
    pub module_path: String,
    pub target: krypton_parser::ast::ExternTarget,
    pub nullable: bool,
    pub throws: bool,
    pub instance: bool,
    pub constructor: bool,
    pub param_types: Vec<Type>,
    pub return_type: Type,
    pub constraints: Vec<(TraitName, Vec<TypeVarId>)>,
}

#[derive(Debug, Clone)]
pub struct ExternTypeInfo {
    pub krypton_name: String,
    pub host_module: String,
    pub target: krypton_parser::ast::ExternTarget,
    pub lifts: Option<krypton_parser::ast::Lifts>,
}

#[derive(Debug, Clone)]
pub struct ExternTraitInfo {
    pub trait_name: TraitName,
    pub java_interface: String,
    pub methods: Vec<ExternTraitMethodInfo>,
}

#[derive(Debug, Clone)]
pub struct ExternTraitMethodInfo {
    pub name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// Pre-resolved type registration for an exported type.
/// Carries fully-resolved `Type` values so importers don't need to re-resolve
/// from raw AST (which would require transitive type dependencies in the consumer's registry).
#[derive(Clone, Debug)]
pub struct ExportedTypeInfo {
    pub name: String,
    pub source_module: String,
    pub type_params: Vec<String>,
    /// Original TypeVarIds corresponding to type_params (1:1 mapping).
    pub type_param_vars: Vec<TypeVarId>,
    pub kind: ExportedTypeKind,
    pub lifts: Option<krypton_parser::ast::Lifts>,
}

#[derive(Clone, Debug)]
pub enum ExportedTypeKind {
    Opaque,
    Record { fields: Vec<(String, Type)> },
    Sum { variants: Vec<ExportedVariantInfo> },
}

#[derive(Clone, Debug)]
pub struct ExportedVariantInfo {
    pub name: String,
    pub fields: Vec<Type>,
}

impl TypedPattern {
    pub fn span(&self) -> Span {
        match self {
            TypedPattern::Wildcard { span, .. }
            | TypedPattern::Var { span, .. }
            | TypedPattern::Constructor { span, .. }
            | TypedPattern::Lit { span, .. }
            | TypedPattern::Tuple { span, .. }
            | TypedPattern::StructPat { span, .. }
            | TypedPattern::Or { span, .. } => *span,
        }
    }
}

pub struct StructDecl {
    pub name: String,
    pub type_params: Vec<String>,
    pub fields: Vec<(String, TypeExpr)>,
    pub qualified_name: QualifiedName,
}

pub struct SumDecl {
    pub name: String,
    pub type_params: Vec<String>,
    pub variants: Vec<Variant>,
    pub qualified_name: QualifiedName,
}

pub struct TypedModule {
    pub module_path: String,
    pub fn_types: Vec<FnTypeEntry>,
    /// Index: function name → index into `fn_types`, for O(1) provenance lookups.
    /// Name-keyed is deliberate: this is only used to look up the module's
    /// `main`, which is not permitted to be overloaded. For other functions —
    /// which may be overloaded — scan `fn_types` directly or dispatch via the
    /// typed-AST resolved_ref.
    pub fn_types_by_name: FxHashMap<String, usize>,
    /// Public API: only locally-defined pub functions, pub (transparent) constructors,
    /// and trait instance methods. Used by downstream importers.
    pub exported_fn_types: Vec<ExportedFn>,
    pub functions: Vec<TypedFnDecl>,
    pub trait_defs: Vec<TraitDefInfo>,
    pub instance_defs: Vec<InstanceDefInfo>,
    pub extern_fns: Vec<ExternFnInfo>,
    /// Extern type bindings (krypton name, host module path, target).
    pub extern_types: Vec<ExternTypeInfo>,
    /// Extern trait definitions (Java interfaces exposed as Krypton traits).
    pub extern_traits: Vec<ExternTraitInfo>,
    pub struct_decls: Vec<StructDecl>,
    pub sum_decls: Vec<SumDecl>,
    /// Maps type_name → visibility for types declared in this module.
    pub type_visibility: FxHashMap<String, Visibility>,
    /// Functions re-exported via `pub use` — these become part of this module's public API.
    pub reexported_fn_types: Vec<ExportedFn>,
    /// Type names re-exported via `pub use`.
    pub reexported_type_names: Vec<String>,
    /// Maps re-exported type name → original visibility (preserves pub/opaque distinction).
    pub reexported_type_visibility: FxHashMap<String, Visibility>,
    /// Trait definitions exported for cross-module use.
    pub exported_trait_defs: Vec<ExportedTraitDef>,
    /// Pre-resolved type registrations for exported types.
    /// Used by importers to register types without re-resolving from AST.
    pub exported_type_infos: FxHashMap<String, ExportedTypeInfo>,
    /// Auto-close info for Disposable bindings.
    pub auto_close: AutoCloseInfo,
    /// Pre-computed per-param qualifier info for exported functions.
    /// Downstream modules use this for cross-module ownership checking.
    pub exported_fn_qualifiers: FxHashMap<String, Vec<(ParamQualifier, String)>>,
    /// Source text of this module (for diagnostic rendering of codegen errors).
    pub module_source: Option<String>,
}

impl TypedModule {
    /// Get the source module path for a type by searching struct/sum declarations.
    pub fn type_origin(&self, name: &str) -> Option<&str> {
        if let Some(info) = self.exported_type_infos.get(name) {
            return Some(info.source_module.as_str());
        }
        self.struct_decls
            .iter()
            .find(|d| d.name == name)
            .map(|d| d.qualified_name.module_path.as_str())
            .or_else(|| {
                self.sum_decls
                    .iter()
                    .find(|d| d.name == name)
                    .map(|d| d.qualified_name.module_path.as_str())
            })
    }
}

/// Build the JVM-mangled name for a trait instance method.
pub fn mangled_method_name(trait_name: &str, target_type_name: &str, method_name: &str) -> String {
    format!("{}$${}$${}", trait_name, target_type_name, method_name)
}

pub fn apply_subst_pattern(pat: &mut TypedPattern, subst: &Substitution) {
    match pat {
        TypedPattern::Wildcard { ty, .. } => *ty = subst.apply(ty),
        TypedPattern::Var { ty, .. } => *ty = subst.apply(ty),
        TypedPattern::Lit { ty, .. } => *ty = subst.apply(ty),
        TypedPattern::Constructor { args, ty, .. } => {
            *ty = subst.apply(ty);
            for arg in args {
                apply_subst_pattern(arg, subst);
            }
        }
        TypedPattern::Tuple { elements, ty, .. } => {
            *ty = subst.apply(ty);
            for elem in elements {
                apply_subst_pattern(elem, subst);
            }
        }
        TypedPattern::StructPat { fields, ty, .. } => {
            *ty = subst.apply(ty);
            for (_, field_pat) in fields {
                apply_subst_pattern(field_pat, subst);
            }
        }
        TypedPattern::Or {
            alternatives, ty, ..
        } => {
            *ty = subst.apply(ty);
            for alt in alternatives {
                apply_subst_pattern(alt, subst);
            }
        }
    }
}

pub fn apply_subst(expr: &mut TypedExpr, subst: &Substitution) {
    let mut work: Vec<&mut TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        expr.ty = subst.apply(&expr.ty);
        match &mut expr.kind {
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
            TypedExprKind::App { func, args, .. } => {
                work.push(func);
                work.extend(args.iter_mut());
            }
            TypedExprKind::TypeApp { expr, .. } => work.push(expr),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. } => {
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::Do(exprs) => work.extend(exprs.iter_mut()),
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms {
                    apply_subst_pattern(&mut arm.pattern, subst);
                    if let Some(guard) = &mut arm.guard {
                        work.push(guard);
                    }
                    work.push(&mut arm.body);
                }
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::Recur { args, .. } => {
                work.extend(args.iter_mut());
            }
            TypedExprKind::Tuple(args) | TypedExprKind::VecLit(args) => {
                work.extend(args.iter_mut());
            }
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::StructUpdate { base, fields } => {
                work.push(base);
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::LetPattern {
                pattern,
                value,
                body,
            } => {
                apply_subst_pattern(pattern, subst);
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::Discharge(inner) => work.push(inner),
        }
    }
}
