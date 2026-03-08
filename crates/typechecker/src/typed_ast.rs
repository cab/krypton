use std::collections::HashMap;

use crate::types::{Substitution, Type, TypeScheme};
use krypton_parser::ast::{BinOp, Lit, Pattern, Span, UnaryOp};

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
        pattern: Pattern,
        value: Box<TypedExpr>,
        body: Option<Box<TypedExpr>>,
    },
    QuestionMark {
        expr: Box<TypedExpr>,
        is_option: bool, // true=Option, false=Result
    },
}

#[derive(Debug, Clone)]
pub struct TypedMatchArm {
    pub pattern: Pattern,
    pub body: TypedExpr,
}

#[derive(Debug, Clone)]
pub struct TypedFnDecl {
    pub name: String,
    pub params: Vec<String>,
    pub body: TypedExpr,
}

pub struct TraitDefInfo {
    pub name: String,
    pub methods: Vec<(String, usize)>, // (method_name, param_count)
}

pub struct InstanceDefInfo {
    pub trait_name: String,
    pub target_type_name: String,
    pub target_type: Type,
    pub qualified_method_names: Vec<(String, String)>, // (method_name, qualified_name)
    pub subdict_traits: Vec<(String, usize)>, // (trait_name, type_param_index) for parameterized instances
}

pub struct ExternFnInfo {
    pub name: String,
    pub java_class: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

pub struct TypedModule {
    pub fn_types: Vec<(String, TypeScheme)>,
    pub functions: Vec<TypedFnDecl>,
    pub trait_defs: Vec<TraitDefInfo>,
    pub instance_defs: Vec<InstanceDefInfo>,
    pub fn_constraints: HashMap<String, Vec<String>>,
    pub trait_method_map: HashMap<String, String>,
    pub extern_fns: Vec<ExternFnInfo>,
}

pub fn apply_subst(expr: &mut TypedExpr, subst: &Substitution) {
    expr.ty = subst.apply(&expr.ty);
    match &mut expr.kind {
        TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        TypedExprKind::App { func, args } => {
            apply_subst(func, subst);
            for arg in args {
                apply_subst(arg, subst);
            }
        }
        TypedExprKind::If { cond, then_, else_ } => {
            apply_subst(cond, subst);
            apply_subst(then_, subst);
            apply_subst(else_, subst);
        }
        TypedExprKind::Let { value, body, .. } => {
            apply_subst(value, subst);
            if let Some(body) = body {
                apply_subst(body, subst);
            }
        }
        TypedExprKind::Do(exprs) => {
            for e in exprs {
                apply_subst(e, subst);
            }
        }
        TypedExprKind::Match { scrutinee, arms } => {
            apply_subst(scrutinee, subst);
            for arm in arms {
                apply_subst(&mut arm.body, subst);
            }
        }
        TypedExprKind::Lambda { body, .. } => {
            apply_subst(body, subst);
        }
        TypedExprKind::FieldAccess { expr, .. } => {
            apply_subst(expr, subst);
        }
        TypedExprKind::Recur(args) => {
            for arg in args {
                apply_subst(arg, subst);
            }
        }
        TypedExprKind::Tuple(elems) => {
            for e in elems {
                apply_subst(e, subst);
            }
        }
        TypedExprKind::BinaryOp { lhs, rhs, .. } => {
            apply_subst(lhs, subst);
            apply_subst(rhs, subst);
        }
        TypedExprKind::UnaryOp { operand, .. } => {
            apply_subst(operand, subst);
        }
        TypedExprKind::StructLit { fields, .. } => {
            for (_, e) in fields {
                apply_subst(e, subst);
            }
        }
        TypedExprKind::StructUpdate { base, fields } => {
            apply_subst(base, subst);
            for (_, e) in fields {
                apply_subst(e, subst);
            }
        }
        TypedExprKind::LetPattern { value, body, .. } => {
            apply_subst(value, subst);
            if let Some(body) = body {
                apply_subst(body, subst);
            }
        }
        TypedExprKind::QuestionMark { expr, .. } => {
            apply_subst(expr, subst);
        }
    }
}
