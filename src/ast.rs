// Abstract Syntax Tree definitions for alang
// Implements the S-expression grammar from spec/types.md

use std::fmt;

/// Source location information for error reporting
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }
}

/// Top-level declaration
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    /// Type declaration: (type Name [params] body)
    Type {
        name: String,
        params: Vec<String>,
        body: TypeBody,
        span: Span,
    },
    /// Function definition: (def name [params] body)
    Def {
        name: String,
        type_params: Vec<String>,
        params: Vec<Param>,
        return_type: Option<Type>,
        body: Expr,
        span: Span,
    },
}

/// Type declaration body
#[derive(Debug, Clone, PartialEq)]
pub enum TypeBody {
    /// Struct: (struct [field1 type1] [field2 type2] ...)
    Struct(Vec<Field>),
    /// Sum type: (| variant1 variant2 ...)
    Sum(Vec<Variant>),
    /// Alias: type
    Alias(Type),
}

/// Struct field: [name type]
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub name: String,
    pub ty: Type,
}

/// Sum type variant
#[derive(Debug, Clone, PartialEq)]
pub enum Variant {
    /// Unit variant: Name
    Unit(String),
    /// Tuple variant: (Name type1 type2 ...)
    Tuple(String, Vec<Type>),
    /// Struct variant: (Name [field1 type1] [field2 type2] ...)
    Struct(String, Vec<Field>),
}

/// Type expression
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// Named type: Int, String, Point, etc.
    Named(String),
    /// Generic instantiation: (Option Int), (Map String Int)
    Generic(String, Vec<Type>),
    /// Function type: (fn (arg1 arg2) return)
    Function(Vec<Type>, Box<Type>),
    /// Affine type: (^move Buffer)
    Move(Box<Type>),
    /// Tuple type: (Int String Bool)
    Tuple(Vec<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Named(name) => write!(f, "{}", name),
            Type::Generic(name, args) => {
                write!(f, "{}[", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, "]")
            }
            Type::Function(params, ret) => {
                write!(f, "fn(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, ") -> {}", ret)
            }
            Type::Move(inner) => write!(f, "^move {}", inner),
            Type::Tuple(types) => {
                write!(f, "(")?;
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ty)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Function parameter
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: Option<Type>,
    pub is_move: bool,
}

/// Expression
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// Integer literal: 42
    Int(i64, Span),
    /// Float literal: 3.14
    Float(f64, Span),
    /// String literal: "hello"
    String(String, Span),
    /// Boolean literal: true, false
    Bool(bool, Span),
    /// Unit literal: ()
    Unit(Span),
    /// Variable: x, foo, bar
    Var(String, Span),
    /// Function call: (f arg1 arg2)
    Call(Box<Expr>, Vec<Expr>, Span),
    /// Function/closure: (fn [x y] body)
    Function(Vec<Param>, Box<Expr>, Span),
    /// Let binding: (let [x e1] [y e2] body)
    Let(Vec<Binding>, Box<Expr>, Span),
    /// Conditional: (if cond then else)
    If(Box<Expr>, Box<Expr>, Box<Expr>, Span),
    /// Pattern match: (match scrutinee (pattern body) ...)
    Match(Box<Expr>, Vec<MatchBranch>, Span),
    /// Struct construction: (Point x: 1 y: 2)
    StructLit(String, Vec<(String, Expr)>, Span),
    /// Field access: (. obj field)
    FieldAccess(Box<Expr>, String, Span),
}

impl Expr {
    pub fn span(&self) -> &Span {
        match self {
            Expr::Int(_, s) => s,
            Expr::Float(_, s) => s,
            Expr::String(_, s) => s,
            Expr::Bool(_, s) => s,
            Expr::Unit(s) => s,
            Expr::Var(_, s) => s,
            Expr::Call(_, _, s) => s,
            Expr::Function(_, _, s) => s,
            Expr::Let(_, _, s) => s,
            Expr::If(_, _, _, s) => s,
            Expr::Match(_, _, s) => s,
            Expr::StructLit(_, _, s) => s,
            Expr::FieldAccess(_, _, s) => s,
        }
    }
}

/// Let binding: [name expr]
#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr,
}

/// Match branch: (pattern body)
#[derive(Debug, Clone, PartialEq)]
pub struct MatchBranch {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

/// Pattern for pattern matching
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// Wildcard: _
    Wildcard,
    /// Variable binding: x
    Var(String),
    /// Integer literal: 42
    Int(i64),
    /// String literal: "hello"
    String(String),
    /// Boolean literal: true
    Bool(bool),
    /// Unit: ()
    Unit,
    /// Constructor: (Some x), (Cons head tail)
    Constructor(String, Vec<Pattern>),
    /// Struct pattern: (Point x: px y: py)
    Struct(String, Vec<(String, Pattern)>),
    /// Tuple pattern: (x y z)
    Tuple(Vec<Pattern>),
}

/// Program is a sequence of declarations
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub decls: Vec<Decl>,
}
