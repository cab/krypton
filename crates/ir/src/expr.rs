use crate::{FnId, Type, VarId};

/// An IR expression. Every expression carries a `Type`.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// Bind the result of a simple expression.
    /// `let x: T = value in body`
    Let {
        bind: VarId,
        ty: Type,
        value: SimpleExpr,
        body: Box<Expr>,
    },

    /// Mutually recursive bindings (all RHS must be closures).
    /// Each `LetRec` is one strongly connected component.
    LetRec {
        bindings: Vec<(VarId, Type, FnId, Vec<Atom>)>,
        body: Box<Expr>,
    },

    /// Define a join point (local continuation).
    /// All uses of `name` must be saturated `Jump`s in tail position within `body`.
    LetJoin {
        name: VarId,
        params: Vec<(VarId, Type)>,
        join_body: Box<Expr>,
        body: Box<Expr>,
        is_recur: bool,
    },

    /// Tail call to a join point.
    Jump {
        target: VarId,
        args: Vec<Atom>,
    },

    /// Multi-way branch on a constructor tag.
    Switch {
        scrutinee: Atom,
        branches: Vec<SwitchBranch>,
        default: Option<Box<Expr>>,
    },

    /// Terminal: produce a value.
    Atom(Atom),
}

#[derive(Debug, Clone)]
pub struct SwitchBranch {
    pub tag: u32,
    pub bindings: Vec<(VarId, Type)>,
    pub body: Expr,
}

/// One step of computation. Appears only as the RHS of a `Let` binding.
#[derive(Debug, Clone)]
pub enum SimpleExpr {
    /// Direct call to a known function.
    Call { func: FnId, args: Vec<Atom> },

    /// Indirect call through a closure value.
    CallClosure { closure: Atom, args: Vec<Atom> },

    /// Allocate a closure: a top-level function + captured values.
    MakeClosure { func: FnId, captures: Vec<Atom> },

    /// Construct a struct value.
    Construct {
        type_name: String,
        fields: Vec<Atom>,
    },

    /// Construct a sum type variant.
    ConstructVariant {
        type_name: String,
        variant: String,
        tag: u32,
        fields: Vec<Atom>,
    },

    /// Access a struct field by index.
    Project { value: Atom, field_index: usize },

    /// Extract the tag of a sum type value.
    Tag { value: Atom },

    /// Construct a tuple.
    MakeTuple { elements: Vec<Atom> },

    /// Access a tuple element by index.
    TupleProject { value: Atom, index: usize },

    /// Primitive operation (fully resolved, no overloading).
    PrimOp { op: PrimOp, args: Vec<Atom> },

    /// Reference a singleton trait dictionary (concrete type, no type vars).
    GetDict { trait_name: String, ty: Type },

    /// Construct a parameterized trait dictionary from sub-dicts.
    MakeDict {
        trait_name: String,
        ty: Type,
        sub_dicts: Vec<Atom>,
    },

    /// Construct a Vec from elements.
    MakeVec { element_type: Type, elements: Vec<Atom> },

    /// A trivial atom (used for binding literal scrutinees to variables).
    Atom(Atom),
}

/// Trivial values — no computation, no side effects.
#[derive(Debug, Clone)]
pub enum Atom {
    Var(VarId),
    Lit(Literal),
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Unit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimOp {
    // Integer arithmetic
    AddInt,
    SubInt,
    MulInt,
    DivInt,
    ModInt,
    NegInt,

    // Float arithmetic
    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    NegFloat,

    // Integer comparison
    EqInt,
    NeqInt,
    LtInt,
    LeInt,
    GtInt,
    GeInt,

    // Float comparison
    EqFloat,
    NeqFloat,
    LtFloat,
    LeFloat,
    GtFloat,
    GeFloat,

    // Boolean
    Not,
    And,
    Or,

    // String
    EqString,
    NeqString,
    ConcatString,

    // Conversions
    IntToFloat,
    FloatToInt,
    IntToString,
    FloatToString,
    BoolToString,
}
