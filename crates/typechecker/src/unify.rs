use krypton_parser::ast::Span;

use crate::types::{Substitution, Type, TypeVarId};
use std::fmt;

/// Error codes for type errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeErrorCode {
    E0001, // Type mismatch
    E0003, // Unknown variable
    E0004, // Not a function
    E0005, // Wrong arity
    E0007, // Infinite type
}

impl fmt::Display for TypeErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeErrorCode::E0001 => write!(f, "E0001"),
            TypeErrorCode::E0003 => write!(f, "E0003"),
            TypeErrorCode::E0004 => write!(f, "E0004"),
            TypeErrorCode::E0005 => write!(f, "E0005"),
            TypeErrorCode::E0007 => write!(f, "E0007"),
        }
    }
}

/// Errors that can occur during type unification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    Mismatch { expected: Type, actual: Type },
    InfiniteType { var: TypeVarId, ty: Type },
    WrongArity { expected: usize, actual: usize },
    UnknownVariable { name: String },
    NotAFunction { actual: Type },
}

impl TypeError {
    /// Return the error code for this error.
    pub fn error_code(&self) -> TypeErrorCode {
        match self {
            TypeError::Mismatch { .. } => TypeErrorCode::E0001,
            TypeError::UnknownVariable { .. } => TypeErrorCode::E0003,
            TypeError::NotAFunction { .. } => TypeErrorCode::E0004,
            TypeError::WrongArity { .. } => TypeErrorCode::E0005,
            TypeError::InfiniteType { .. } => TypeErrorCode::E0007,
        }
    }

    /// Return optional help text for this error.
    pub fn help(&self) -> Option<String> {
        match self {
            TypeError::Mismatch { .. } => None,
            TypeError::UnknownVariable { name } => {
                Some(format!("did you mean to define `{}` first?", name))
            }
            TypeError::NotAFunction { actual } => {
                Some(format!("the expression has type `{}`, which is not callable", actual))
            }
            TypeError::WrongArity { expected, .. } => {
                Some(format!("this function expects {} argument(s)", expected))
            }
            TypeError::InfiniteType { .. } => {
                Some("this creates a type that contains itself".to_string())
            }
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Mismatch { expected, actual } => {
                write!(f, "type mismatch: expected {}, found {}", expected, actual)
            }
            TypeError::InfiniteType { var, ty } => {
                write!(f, "infinite type: variable {} occurs in {}", var, ty)
            }
            TypeError::WrongArity { expected, actual } => {
                write!(
                    f,
                    "wrong arity: expected {} arguments, found {}",
                    expected, actual
                )
            }
            TypeError::UnknownVariable { name } => {
                write!(f, "unknown variable: {}", name)
            }
            TypeError::NotAFunction { actual } => {
                write!(f, "not a function: type {} is not callable", actual)
            }
        }
    }
}

/// A type error paired with the source span where it occurred.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedTypeError {
    pub error: TypeError,
    pub span: Span,
}

impl fmt::Display for SpannedTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} [{}]", self.error, self.error.error_code())
    }
}

impl std::error::Error for TypeError {}

/// Resolve type variable chains through the substitution.
fn walk(ty: &Type, subst: &Substitution) -> Type {
    match ty {
        Type::Var(id) => match subst.get(*id) {
            Some(t) => walk(t, subst),
            None => ty.clone(),
        },
        _ => ty.clone(),
    }
}

/// Check if a type variable occurs in a type (after applying the substitution).
fn occurs_in(var: TypeVarId, ty: &Type, subst: &Substitution) -> bool {
    let ty = walk(ty, subst);
    match &ty {
        Type::Var(id) => *id == var,
        Type::Fn(params, ret) => {
            params.iter().any(|p| occurs_in(var, p, subst)) || occurs_in(var, ret, subst)
        }
        Type::Named(_, args) => args.iter().any(|a| occurs_in(var, a, subst)),
        Type::Own(inner) => occurs_in(var, inner, subst),
        Type::Tuple(elems) => elems.iter().any(|e| occurs_in(var, e, subst)),
        _ => false,
    }
}

/// Unify two types, mutating the substitution in place.
pub fn unify(t1: &Type, t2: &Type, subst: &mut Substitution) -> Result<(), TypeError> {
    let t1 = walk(t1, subst);
    let t2 = walk(t2, subst);

    match (&t1, &t2) {
        // Same type variables
        (Type::Var(a), Type::Var(b)) if a == b => Ok(()),

        // Bind type variable
        (Type::Var(a), _) => {
            if occurs_in(*a, &t2, subst) {
                return Err(TypeError::InfiniteType { var: *a, ty: t2 });
            }
            subst.insert(*a, t2);
            Ok(())
        }
        (_, Type::Var(b)) => {
            if occurs_in(*b, &t1, subst) {
                return Err(TypeError::InfiniteType { var: *b, ty: t1 });
            }
            subst.insert(*b, t1);
            Ok(())
        }

        // Primitives
        (Type::Int, Type::Int)
        | (Type::Float, Type::Float)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Unit, Type::Unit) => Ok(()),

        // Function types
        (Type::Fn(p1, r1), Type::Fn(p2, r2)) => {
            if p1.len() != p2.len() {
                return Err(TypeError::WrongArity {
                    expected: p1.len(),
                    actual: p2.len(),
                });
            }
            for (a, b) in p1.iter().zip(p2.iter()) {
                unify(a, b, subst)?;
            }
            unify(r1, r2, subst)
        }

        // Named types
        (Type::Named(n1, args1), Type::Named(n2, args2)) => {
            if n1 != n2 {
                return Err(TypeError::Mismatch {
                    expected: t1,
                    actual: t2,
                });
            }
            if args1.len() != args2.len() {
                return Err(TypeError::WrongArity {
                    expected: args1.len(),
                    actual: args2.len(),
                });
            }
            for (a, b) in args1.iter().zip(args2.iter()) {
                unify(a, b, subst)?;
            }
            Ok(())
        }

        // Own types
        (Type::Own(a), Type::Own(b)) => unify(a, b, subst),

        // Tuple types
        (Type::Tuple(e1), Type::Tuple(e2)) => {
            if e1.len() != e2.len() {
                return Err(TypeError::WrongArity {
                    expected: e1.len(),
                    actual: e2.len(),
                });
            }
            for (a, b) in e1.iter().zip(e2.iter()) {
                unify(a, b, subst)?;
            }
            Ok(())
        }

        // Mismatch
        _ => Err(TypeError::Mismatch {
            expected: t1,
            actual: t2,
        }),
    }
}
