use std::collections::HashMap;

use crate::types::{Substitution, Type, TypeScheme};
use krypton_parser::ast::{BinOp, Lit, Span, TypeConstraint, TypeExpr, UnaryOp, Variant, Visibility};

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
}

#[derive(Debug, Clone)]
pub enum TypedExprKind {
    Lit(Lit),
    Var(String),
    App {
        func: Box<TypedExpr>,
        args: Vec<TypedExpr>,
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
}

pub struct TraitDefInfo {
    pub name: String,
    pub methods: Vec<(String, usize)>, // (method_name, param_count)
    pub is_imported: bool,
}

#[derive(Clone)]
pub struct ExportedTraitDef {
    pub visibility: Visibility,
    pub name: String,
    pub type_var: String,
    pub type_var_id: u32,
    /// 0 = kind *, 1 = * -> *, etc.
    pub type_var_arity: usize,
    pub superclasses: Vec<String>,
    pub methods: Vec<ExportedTraitMethod>,
}

#[derive(Clone)]
pub struct ExportedTraitMethod {
    pub name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

#[derive(Clone)]
pub struct InstanceDefInfo {
    pub trait_name: String,
    pub target_type_name: String,
    pub target_type: Type,
    pub type_var_ids: HashMap<String, u32>,
    pub constraints: Vec<TypeConstraint>,
    pub qualified_method_names: Vec<(String, String)>, // (method_name, qualified_name)
    pub subdict_traits: Vec<(String, usize)>, // (trait_name, type_param_index) for parameterized instances
    pub is_intrinsic: bool,                   // true when all method bodies are intrinsic()
}

#[derive(Clone)]
pub struct ExternFnInfo {
    pub name: String,
    pub java_class: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

pub struct TypedModule {
    pub module_path: Option<String>,
    pub fn_types: Vec<(String, TypeScheme)>,
    pub functions: Vec<TypedFnDecl>,
    pub trait_defs: Vec<TraitDefInfo>,
    pub instance_defs: Vec<InstanceDefInfo>,
    pub fn_constraints: HashMap<String, Vec<(String, usize)>>,
    pub fn_constraint_requirements: HashMap<String, Vec<(String, u32)>>,
    /// Constraints inherited from imported modules (e.g., `println` requires `Show`).
    pub imported_fn_constraints: HashMap<String, Vec<(String, usize)>>,
    pub trait_method_map: HashMap<String, String>,
    pub extern_fns: Vec<ExternFnInfo>,
    pub imported_extern_fns: Vec<ExternFnInfo>,
    pub struct_decls: Vec<(String, Vec<(String, TypeExpr)>)>,
    pub sum_decls: Vec<(String, Vec<String>, Vec<Variant>)>,
    /// Maps local_name → (module_path, original_name) for imported functions.
    /// Used by codegen to emit cross-module `invokestatic` calls.
    pub fn_provenance: HashMap<String, (String, String)>,
    /// Maps type_name → source_module_path for types originating from other modules.
    /// Used by codegen to qualify type class names (e.g., `core/list/List`).
    pub type_provenance: HashMap<String, String>,
    /// Maps type_name → visibility for types declared in this module.
    pub type_visibility: HashMap<String, Visibility>,
    /// Functions re-exported via `pub use` — these become part of this module's public API.
    pub reexported_fn_types: Vec<(String, TypeScheme)>,
    /// Type names re-exported via `pub use`.
    pub reexported_type_names: Vec<String>,
    /// Maps re-exported type name → original visibility (preserves pub/pub open distinction).
    pub reexported_type_visibility: HashMap<String, Visibility>,
    /// Trait definitions exported for cross-module use.
    pub exported_trait_defs: Vec<ExportedTraitDef>,
    /// Auto-close info for Resource bindings.
    pub auto_close: AutoCloseInfo,
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
