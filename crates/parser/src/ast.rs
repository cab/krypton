use serde::Serialize;

/// Byte offset span: (start, end).
pub type Span = (usize, usize);

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Decl {
    DefFn(FnDecl),
    DefType(TypeDecl),
    DefTrait {
        name: String,
        type_var: String,
        superclasses: Vec<String>,
        methods: Vec<FnDecl>,
        span: Span,
    },
    DefImpl {
        trait_name: String,
        target_type: TypeExpr,
        type_constraints: Vec<TypeConstraint>,
        methods: Vec<FnDecl>,
        span: Span,
    },
    Import {
        path: String,
        names: Vec<String>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TypeDecl {
    pub name: String,
    pub type_params: Vec<String>,
    pub kind: TypeDeclKind,
    pub deriving: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum TypeDeclKind {
    Record { fields: Vec<(String, TypeExpr)> },
    Sum { variants: Vec<Variant> },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Variant {
    pub name: String,
    pub fields: Vec<TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct FnDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub constraints: Vec<TypeConstraint>,
    pub return_type: Option<TypeExpr>,
    pub body: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Param {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TypeConstraint {
    pub type_var: String,
    pub trait_name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Expr {
    Lit {
        value: Lit,
        span: Span,
    },
    Var {
        name: String,
        span: Span,
    },
    App {
        func: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
    },
    If {
        cond: Box<Expr>,
        then_: Box<Expr>,
        else_: Box<Expr>,
        span: Span,
    },
    Let {
        name: String,
        value: Box<Expr>,
        body: Option<Box<Expr>>,
        span: Span,
    },
    Do {
        exprs: Vec<Expr>,
        span: Span,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        span: Span,
    },
    Lambda {
        params: Vec<Param>,
        return_type: Option<TypeExpr>,
        body: Box<Expr>,
        span: Span,
    },
    FieldAccess {
        expr: Box<Expr>,
        field: String,
        span: Span,
    },
    Recur {
        args: Vec<Expr>,
        span: Span,
    },
    Receive {
        arms: Vec<MatchArm>,
        timeout: Option<Timeout>,
        span: Span,
    },
    Send {
        target: Box<Expr>,
        message: Box<Expr>,
        span: Span,
    },
    Spawn {
        func: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
    },
    Self_ {
        span: Span,
    },
    QuestionMark {
        expr: Box<Expr>,
        span: Span,
    },
    List {
        elements: Vec<Expr>,
        span: Span,
    },
    Tuple {
        elements: Vec<Expr>,
        span: Span,
    },
    BinaryOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: Span,
    },
    UnaryOp {
        op: UnaryOp,
        operand: Box<Expr>,
        span: Span,
    },
    StructLit {
        name: String,
        fields: Vec<(String, Expr)>,
        span: Span,
    },
    StructUpdate {
        base: Box<Expr>,
        fields: Vec<(String, Expr)>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Timeout {
    pub duration: Box<Expr>,
    pub body: Box<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum UnaryOp {
    Neg,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Pattern {
    Wildcard {
        span: Span,
    },
    Var {
        name: String,
        span: Span,
    },
    Constructor {
        name: String,
        args: Vec<Pattern>,
        span: Span,
    },
    Lit {
        value: Lit,
        span: Span,
    },
    Tuple {
        elements: Vec<Pattern>,
        span: Span,
    },
    StructPat {
        name: String,
        fields: Vec<(String, Pattern)>,
        rest: bool,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum TypeExpr {
    Named {
        name: String,
        span: Span,
    },
    Var {
        name: String,
        span: Span,
    },
    App {
        name: String,
        args: Vec<TypeExpr>,
        span: Span,
    },
    Fn {
        params: Vec<TypeExpr>,
        ret: Box<TypeExpr>,
        span: Span,
    },
    Own {
        inner: Box<TypeExpr>,
        span: Span,
    },
    Tuple {
        elements: Vec<TypeExpr>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Lit {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Unit,
}
