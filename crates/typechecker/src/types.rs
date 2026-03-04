// Internal type representation for type inference
// Implements Algorithm J type inference from spec/types.md

use std::collections::HashSet;
use std::fmt;

/// Type variable - fresh variable generated during inference
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVar(pub u32);

/// Declaration ID - uniquely identifies a type declaration
/// Used for nominal type equality checking
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeclId(pub u32);

/// Primitive types in the language
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    Int,
    Float,
    String,
    Bool,
    Unit,
    Never,
}

/// Internal type representation used during type inference
/// Separate from AST Type to handle fresh variables and substitutions
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InferType {
    /// Primitive types: Int, String, Bool, Unit, Never
    Primitive(PrimitiveType),

    /// Type variable (fresh variable for unknowns)
    Var(TypeVar),

    /// Nominal type (declared struct/sum)
    /// Contains type name, unique declaration ID, and type arguments
    Nominal {
        name: String,
        decl_id: DeclId,
        type_args: Vec<InferType>,
    },

    /// Function type: (arg types) -> return type
    Function {
        params: Vec<InferType>,
        ret: Box<InferType>,
    },

    /// Affine type: ^move T
    /// Values that must be used at most once
    Move(Box<InferType>),

    /// Tuple type
    Tuple(Vec<InferType>),
}

/// Type scheme for let-generalization: ∀ a b c. Type
/// Represents polymorphic types
#[derive(Debug, Clone)]
pub struct TypeScheme {
    /// Bound type variables (the ∀ quantified variables)
    pub forall: Vec<TypeVar>,
    /// The type itself
    pub ty: InferType,
}

impl InferType {
    /// Get all free type variables in a type
    /// Used for let-generalization and occurs check
    pub fn free_vars(&self) -> HashSet<TypeVar> {
        match self {
            InferType::Var(v) => {
                let mut set = HashSet::new();
                set.insert(*v);
                set
            }
            InferType::Function { params, ret } => {
                let mut vars = HashSet::new();
                for p in params {
                    vars.extend(p.free_vars());
                }
                vars.extend(ret.free_vars());
                vars
            }
            InferType::Nominal { type_args, .. } => {
                let mut vars = HashSet::new();
                for arg in type_args {
                    vars.extend(arg.free_vars());
                }
                vars
            }
            InferType::Move(inner) => inner.free_vars(),
            InferType::Tuple(types) => {
                let mut vars = HashSet::new();
                for t in types {
                    vars.extend(t.free_vars());
                }
                vars
            }
            InferType::Primitive(_) => HashSet::new(),
        }
    }

    /// Check if this is a move type
    pub fn is_move(&self) -> bool {
        matches!(self, InferType::Move(_))
    }
}

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "'{}", (b'a' + (self.0 % 26) as u8) as char)?;
        if self.0 >= 26 {
            write!(f, "{}", self.0 / 26)?;
        }
        Ok(())
    }
}

impl fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimitiveType::Int => write!(f, "Int"),
            PrimitiveType::Float => write!(f, "Float"),
            PrimitiveType::String => write!(f, "String"),
            PrimitiveType::Bool => write!(f, "Bool"),
            PrimitiveType::Unit => write!(f, "Unit"),
            PrimitiveType::Never => write!(f, "Never"),
        }
    }
}

impl fmt::Display for InferType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InferType::Primitive(p) => write!(f, "{}", p),
            InferType::Var(v) => write!(f, "{}", v),
            InferType::Nominal { name, type_args, .. } => {
                write!(f, "{}", name)?;
                if !type_args.is_empty() {
                    write!(f, "[")?;
                    for (i, arg) in type_args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            InferType::Function { params, ret } => {
                write!(f, "fn(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, ") -> {}", ret)
            }
            InferType::Move(inner) => write!(f, "^move {}", inner),
            InferType::Tuple(types) => {
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

impl fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.forall.is_empty() {
            write!(f, "∀")?;
            for (i, var) in self.forall.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{}", var)?;
            }
            write!(f, ". ")?;
        }
        write!(f, "{}", self.ty)
    }
}
