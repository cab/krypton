use serde::Serialize;

/// Byte offset span: (start, end).
pub type Span = (usize, usize);

/// Compile target for platform-conditional declarations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum CompileTarget {
    Jvm,
    Js,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Module {
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Decl {
    DefFn(FnDecl),
    DefType(TypeDecl),
    DefTrait {
        platform: Option<Vec<CompileTarget>>,
        visibility: Visibility,
        name: String,
        type_params: Vec<TypeParam>,
        superclasses: Vec<TypeConstraint>,
        methods: Vec<FnDecl>,
        doc: Option<String>,
        span: Span,
    },
    DefImpl {
        platform: Option<Vec<CompileTarget>>,
        trait_name: String,
        type_args: Vec<TypeExpr>,
        type_params: Vec<TypeParam>,
        type_constraints: Vec<TypeConstraint>,
        methods: Vec<FnDecl>,
        doc: Option<String>,
        span: Span,
    },
    Import {
        platform: Option<Vec<CompileTarget>>,
        is_pub: bool,
        path: String,
        names: Vec<ImportName>,
        span: Span,
    },
    Extern {
        platform: Option<Vec<CompileTarget>>,
        target: ExternTarget,
        module_path: String,
        alias: Option<String>,
        alias_visibility: Option<Visibility>,
        is_trait: bool,
        type_params: Vec<String>,
        lifts: Option<Lifts>,
        methods: Vec<ExternMethod>,
        deriving: Vec<String>,
        doc: Option<String>,
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
    pub throws: bool,
    pub instance: bool,
    pub constructor: bool,
    pub visibility: Visibility,
    pub name: String,
    pub type_params: Vec<String>,
    pub params: Vec<(String, TypeExpr)>,
    pub return_type: TypeExpr,
    pub where_clauses: Vec<TypeConstraint>,
    pub doc: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Lifts {
    Always,
    Never,
    Params(Vec<String>),
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ExternTarget {
    Java,
    Js,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct TypeDecl {
    pub platform: Option<Vec<CompileTarget>>,
    pub name: String,
    pub visibility: Visibility,
    pub type_params: Vec<String>,
    pub kind: TypeDeclKind,
    pub deriving: Vec<String>,
    pub doc: Option<String>,
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
    pub platform: Option<Vec<CompileTarget>>,
    pub name: String,
    pub visibility: Visibility,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub constraints: Vec<TypeConstraint>,
    pub return_type: Option<TypeExpr>,
    pub body: Box<Expr>,
    pub doc: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum ParamMode {
    Consume,
    Borrow,
    ObservationalBorrow,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Param {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub mode: ParamMode,
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
    pub trait_name: String,
    /// All type arguments to the trait, in order. Length >= 1. Single-parameter
    /// constraints (`a: Show`) have `type_args = [Var("a")]`.
    pub type_args: Vec<TypeExpr>,
    pub span: Span,
}

impl TypeConstraint {
    /// Returns the single type variable name bound by this constraint, if it
    /// is single-parameter and the type argument is a bare identifier.
    pub fn as_single_param_var(&self) -> Option<&str> {
        match self.type_args.as_slice() {
            [TypeExpr::Var { name, .. }] => Some(name.as_str()),
            _ => None,
        }
    }

    /// Returns all type variable names bound by this constraint, if every
    /// type argument is a bare identifier. Length is always `type_args.len()`
    /// on success. Returns `None` if any argument is not a bare type variable
    /// (e.g. a nested type constructor like `Array[a]`).
    pub fn as_param_vars(&self) -> Option<Vec<&str>> {
        self.type_args
            .iter()
            .map(|ta| match ta {
                TypeExpr::Var { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect()
    }
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
    IfLet {
        pattern: Pattern,
        scrutinee: Box<Expr>,
        guard: Option<Box<Expr>>,
        then_: Box<Expr>,
        else_: Option<Box<Expr>>,
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
pub struct FnTypeParam {
    pub mode: ParamMode,
    pub ty: TypeExpr,
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
        params: Vec<FnTypeParam>,
        ret: Box<TypeExpr>,
        span: Span,
    },
    Own {
        inner: Box<TypeExpr>,
        span: Span,
    },
    Shape {
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

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named { span, .. }
            | TypeExpr::Var { span, .. }
            | TypeExpr::Qualified { span, .. }
            | TypeExpr::App { span, .. }
            | TypeExpr::Fn { span, .. }
            | TypeExpr::Own { span, .. }
            | TypeExpr::Shape { span, .. }
            | TypeExpr::Tuple { span, .. }
            | TypeExpr::Wildcard { span } => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Lit {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Unit,
}
