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
        visibility: Visibility,
        name: String,
        type_param: TypeParam,
        superclasses: Vec<String>,
        methods: Vec<FnDecl>,
        span: Span,
    },
    DefImpl {
        trait_name: String,
        target_type: TypeExpr,
        type_params: Vec<TypeParam>,
        type_constraints: Vec<TypeConstraint>,
        methods: Vec<FnDecl>,
        span: Span,
    },
    Import {
        is_pub: bool,
        path: String,
        names: Vec<ImportName>,
        span: Span,
    },
    Extern {
        target: ExternTarget,
        module_path: String,
        alias: Option<String>,
        alias_visibility: Option<Visibility>,
        type_params: Vec<String>,
        methods: Vec<ExternMethod>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ImportName {
    pub name: String,
    pub alias: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub enum Visibility {
    Private,
    Pub,
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ExternMethod {
    pub nullable: bool,
    pub visibility: Visibility,
    pub name: String,
    pub type_params: Vec<String>,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub where_clauses: Vec<TypeConstraint>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ExternTarget {
    Java,
    Js,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TypeDecl {
    pub name: String,
    pub visibility: Visibility,
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
    pub visibility: Visibility,
    pub type_params: Vec<TypeParam>,
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

/// Type parameter supporting higher-kinded types.
/// `a` has arity 0 (kind *), `f[_]` has arity 1 (kind * -> *), etc.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TypeParam {
    pub name: String,
    /// Number of kind holes: 0 for `a` (kind *), 1 for `f[_]`, 2 for `f[_, _]`, etc.
    pub arity: usize,
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
        is_ufcs: bool,
        span: Span,
    },
    TypeApp {
        expr: Box<Expr>,
        type_args: Vec<TypeExpr>,
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
        ty: Option<TypeExpr>,
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
    LetPattern {
        pattern: Pattern,
        ty: Option<TypeExpr>,
        value: Box<Expr>,
        body: Option<Box<Expr>>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Box<Expr>>,
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
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum UnaryOp {
    Neg,
    Not,
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
    Or {
        alternatives: Vec<Pattern>,
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
    Qualified {
        module: String,
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
    Wildcard {
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
