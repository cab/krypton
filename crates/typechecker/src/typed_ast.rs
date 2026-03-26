use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;

use crate::types::{Substitution, Type, TypeScheme, TypeVarId};
use krypton_parser::ast::{BinOp, Lit, Span, TypeExpr, UnaryOp, Variant, Visibility};

/// Whether a generic parameter requires unlimited (U) qualifier or is polymorphic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParamQualifier {
    /// Used more than once in the body — caller must not pass affine values.
    RequiresU,
    /// Used at most once — accepts both affine and unlimited values.
    Polymorphic,
    /// Declared `shared` — accepts affine args without consuming them.
    Shared,
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
    pub fn core_resource() -> Self {
        TraitName::new("core/resource".into(), "Resource".into())
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
    /// Function end: fn_name → bindings to close (LIFO order)
    pub fn_exits: HashMap<String, Vec<AutoCloseBinding>>,
    /// Shadow point: let_span → old binding to close before new binding takes effect
    pub shadow_closes: HashMap<Span, AutoCloseBinding>,
    /// QuestionMark early return: qm_span → bindings to close before early return (LIFO order)
    pub early_returns: HashMap<Span, Vec<AutoCloseBinding>>,
    /// Recur back-edge: recur_span → bindings to close before jumping back (LIFO order)
    pub recur_closes: HashMap<Span, Vec<AutoCloseBinding>>,
    /// Move/consumption sites: arg_span → consumed bindings
    pub consumptions: HashMap<Span, Vec<AutoCloseBinding>>,
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
    },
}

#[derive(Debug, Clone)]
pub struct TypedExpr {
    pub kind: TypedExprKind,
    pub ty: Type,
    pub span: Span,
    /// Set for trait method references; used by codegen to dispatch to the correct trait.
    pub origin: Option<TraitName>,
}

#[derive(Debug, Clone)]
pub enum TypedExprKind {
    Lit(Lit),
    Var(String),
    App {
        func: Box<TypedExpr>,
        args: Vec<TypedExpr>,
    },
    TypeApp {
        expr: Box<TypedExpr>,
        type_args: Vec<Type>,
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
    },
    Recur(Vec<TypedExpr>),
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
}

#[derive(Debug, Clone)]
pub struct TypedMatchArm {
    pub pattern: TypedPattern,
    pub body: TypedExpr,
}

#[derive(Debug, Clone)]
pub struct TypedFnDecl {
    pub name: String,
    pub visibility: Visibility,
    pub params: Vec<String>,
    pub body: TypedExpr,
    /// For Resource close impl methods, the target type name (e.g., "Handle").
    /// Used by auto-close to skip the self parameter and avoid infinite recursion.
    pub close_self_type: Option<String>,
}

/// A function exported from a module's public API, with optional definition span.
#[derive(Debug, Clone)]
pub struct ExportedFn {
    pub name: String,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
    pub def_span: Option<Span>,
}

pub struct TraitDefInfo {
    pub name: String,
    pub trait_id: TraitName,
    pub methods: Vec<(String, usize)>, // (method_name, param_count)
    pub is_imported: bool,
    pub type_var_id: TypeVarId,
    pub method_tc_types: HashMap<String, (Vec<Type>, Type)>, // name -> (param_types, return_type)
}

#[derive(Clone)]
pub struct ExportedTraitDef {
    pub visibility: Visibility,
    pub name: String,
    pub module_path: String,
    pub type_var: String,
    pub type_var_id: TypeVarId,
    /// 0 = kind *, 1 = * -> *, etc.
    pub type_var_arity: usize,
    pub superclasses: Vec<TraitName>,
    pub methods: Vec<ExportedTraitMethod>,
}

#[derive(Clone)]
pub struct ExportedTraitMethod {
    pub name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

#[derive(Clone)]
pub struct InstanceMethod {
    pub name: String,        // original method name, e.g. "show"
    pub params: Vec<String>, // parameter names
    pub body: TypedExpr,     // typed method body
    pub scheme: TypeScheme,  // type scheme for the method
}

/// A type constraint with its trait name already resolved to a full TraitName.
#[derive(Clone, Debug)]
pub struct ResolvedConstraint {
    pub trait_name: TraitName,
    pub type_var: String,
    pub span: Span,
}

#[derive(Clone)]
pub struct InstanceDefInfo {
    pub trait_name: TraitName,
    pub target_type_name: String,
    pub target_type: Type,
    pub type_var_ids: HashMap<String, TypeVarId>,
    pub constraints: Vec<ResolvedConstraint>,
    pub methods: Vec<InstanceMethod>,
    pub subdict_traits: Vec<(String, usize)>, // (trait_name, type_param_index) for parameterized instances
    pub is_intrinsic: bool,                   // true when all method bodies are intrinsic()
    pub is_derived: bool, // true when generated by `deriving` (no mangled FnId registration)
}

#[derive(Clone)]
pub struct ExternFnInfo {
    pub name: String,
    pub module_path: String,
    pub target: krypton_parser::ast::ExternTarget,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct ExternTypeInfo {
    pub krypton_name: String,
    pub host_module: String,
    pub target: krypton_parser::ast::ExternTarget,
}

/// Pre-resolved type registration for an exported type.
/// Carries fully-resolved `Type` values so importers don't need to re-resolve
/// from raw AST (which would require transitive type dependencies in the consumer's registry).
#[derive(Clone, Debug)]
pub struct ExportedTypeInfo {
    pub name: String,
    pub type_params: Vec<String>,
    /// Original TypeVarIds corresponding to type_params (1:1 mapping).
    pub type_param_vars: Vec<TypeVarId>,
    pub kind: ExportedTypeKind,
}

#[derive(Clone, Debug)]
pub enum ExportedTypeKind {
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
            | TypedPattern::StructPat { span, .. } => *span,
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
    /// Public API: only locally-defined pub functions, pub (transparent) constructors,
    /// and trait instance methods. Used by downstream importers.
    pub exported_fn_types: Vec<ExportedFn>,
    pub functions: Vec<TypedFnDecl>,
    pub trait_defs: Vec<TraitDefInfo>,
    pub instance_defs: Vec<InstanceDefInfo>,
    /// Instance definitions imported from dependency modules.
    pub imported_instance_defs: Vec<InstanceDefInfo>,
    pub fn_constraint_requirements: HashMap<String, Vec<(TraitName, TypeVarId)>>,
    /// TypeVarId-based constraint requirements inherited from imported modules.
    pub imported_fn_constraint_requirements: HashMap<String, Vec<(TraitName, TypeVarId)>>,
    pub extern_fns: Vec<ExternFnInfo>,
    pub imported_extern_fns: Vec<ExternFnInfo>,
    /// Extern type bindings (krypton name, host module path, target).
    pub extern_types: Vec<ExternTypeInfo>,
    pub imported_extern_types: Vec<ExternTypeInfo>,
    pub struct_decls: Vec<StructDecl>,
    pub sum_decls: Vec<SumDecl>,
    /// Maps type_name → visibility for types declared in this module.
    pub type_visibility: HashMap<String, Visibility>,
    /// Functions re-exported via `pub use` — these become part of this module's public API.
    pub reexported_fn_types: Vec<ExportedFn>,
    /// Type names re-exported via `pub use`.
    pub reexported_type_names: Vec<String>,
    /// Maps re-exported type name → original visibility (preserves pub/opaque distinction).
    pub reexported_type_visibility: HashMap<String, Visibility>,
    /// Trait definitions exported for cross-module use.
    pub exported_trait_defs: Vec<ExportedTraitDef>,
    /// Pre-resolved type registrations for exported types.
    /// Used by importers to register types without re-resolving from AST.
    pub exported_type_infos: HashMap<String, ExportedTypeInfo>,
    /// Auto-close info for Resource bindings.
    pub auto_close: AutoCloseInfo,
    /// Pre-computed per-param qualifier info for exported functions.
    /// Downstream modules use this for cross-module ownership checking.
    pub exported_fn_qualifiers: HashMap<String, Vec<(ParamQualifier, String)>>,
    /// Source text of this module (for diagnostic rendering of codegen errors).
    pub module_source: Option<String>,
}

impl TypedModule {
    /// Get the source module path for a type by searching struct/sum declarations.
    pub fn type_origin(&self, name: &str) -> Option<&str> {
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
    }
}

pub fn apply_subst(expr: &mut TypedExpr, subst: &Substitution) {
    let mut work: Vec<&mut TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        expr.ty = subst.apply(&expr.ty);
        match &mut expr.kind {
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
            TypedExprKind::App { func, args } => {
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
                    work.push(&mut arm.body);
                }
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::Recur(args)
            | TypedExprKind::Tuple(args)
            | TypedExprKind::VecLit(args) => {
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
        }
    }
}
