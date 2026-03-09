use krypton_parser::ast::Span;

use crate::types::{Substitution, Type, TypeVarId};
use std::fmt;

/// Error codes for type errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeErrorCode {
    E0001, // Type mismatch
    E0002, // Duplicate type
    E0003, // Unknown variable
    E0004, // Not a function
    E0005, // Wrong arity
    E0006, // Non-exhaustive match
    E0007, // Infinite type
    E0008, // Unknown field
    E0009, // Missing fields
    E0010, // Not a struct
    E0101, // Value already moved
    E0102, // Value may have been moved in a branch
    E0103, // Capture of moved value
    E0104, // Qualifier mismatch
    E0301, // No trait instance
    E0302, // Orphan / duplicate instance
    E0303, // Missing superclass instance
    E0304, // Cannot derive trait (field missing required instance)
    E0305, // Definition conflicts with trait method
    E0011, // Unknown type
    E0401, // ? in function not returning Result or Option
    E0402, // ? on non-Result/Option
    E0403, // ? cross-use (Option in Result context or vice versa)
    E0501, // Unknown module
    E0502, // Circular import
}

impl fmt::Display for TypeErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeErrorCode::E0001 => write!(f, "E0001"),
            TypeErrorCode::E0002 => write!(f, "E0002"),
            TypeErrorCode::E0003 => write!(f, "E0003"),
            TypeErrorCode::E0004 => write!(f, "E0004"),
            TypeErrorCode::E0005 => write!(f, "E0005"),
            TypeErrorCode::E0006 => write!(f, "E0006"),
            TypeErrorCode::E0007 => write!(f, "E0007"),
            TypeErrorCode::E0008 => write!(f, "E0008"),
            TypeErrorCode::E0009 => write!(f, "E0009"),
            TypeErrorCode::E0010 => write!(f, "E0010"),
            TypeErrorCode::E0101 => write!(f, "E0101"),
            TypeErrorCode::E0102 => write!(f, "E0102"),
            TypeErrorCode::E0103 => write!(f, "E0103"),
            TypeErrorCode::E0104 => write!(f, "E0104"),
            TypeErrorCode::E0301 => write!(f, "E0301"),
            TypeErrorCode::E0302 => write!(f, "E0302"),
            TypeErrorCode::E0303 => write!(f, "E0303"),
            TypeErrorCode::E0304 => write!(f, "E0304"),
            TypeErrorCode::E0305 => write!(f, "E0305"),
            TypeErrorCode::E0011 => write!(f, "E0011"),
            TypeErrorCode::E0401 => write!(f, "E0401"),
            TypeErrorCode::E0402 => write!(f, "E0402"),
            TypeErrorCode::E0403 => write!(f, "E0403"),
            TypeErrorCode::E0501 => write!(f, "E0501"),
            TypeErrorCode::E0502 => write!(f, "E0502"),
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
    DuplicateType { name: String },
    UnknownField { type_name: String, field_name: String },
    MissingFields { type_name: String, fields: Vec<String> },
    NotAStruct { actual: Type },
    NonExhaustive { missing: Vec<String> },
    AlreadyMoved { name: String },
    MovedInBranch { name: String },
    CapturedMoved { name: String },
    QualifierMismatch { name: String, callee: String, param: String },
    UnsupportedExpr { description: String },
    NoInstance { trait_name: String, ty: String, required_by: Option<String> },
    OrphanInstance { trait_name: String, ty: String },
    CannotDerive { trait_name: String, type_name: String, field_type: String },
    DefinitionConflictsWithTraitMethod { def_name: String, trait_name: String },
    UnknownType { name: String, suggestion: Option<String> },
    QuestionMarkBadReturn { actual: Type },
    QuestionMarkBadOperand { actual: Type },
    QuestionMarkMismatch { expr_kind: String, return_kind: String },
    UnknownModule { path: String },
    CircularImport { cycle: Vec<String> },
}

impl TypeError {
    /// Return the error code for this error.
    pub fn error_code(&self) -> TypeErrorCode {
        match self {
            TypeError::Mismatch { .. } => TypeErrorCode::E0001,
            TypeError::DuplicateType { .. } => TypeErrorCode::E0002,
            TypeError::UnknownVariable { .. } => TypeErrorCode::E0003,
            TypeError::NotAFunction { .. } => TypeErrorCode::E0004,
            TypeError::WrongArity { .. } => TypeErrorCode::E0005,
            TypeError::InfiniteType { .. } => TypeErrorCode::E0007,
            TypeError::UnknownField { .. } => TypeErrorCode::E0008,
            TypeError::MissingFields { .. } => TypeErrorCode::E0009,
            TypeError::NotAStruct { .. } => TypeErrorCode::E0010,
            TypeError::NonExhaustive { .. } => TypeErrorCode::E0006,
            TypeError::AlreadyMoved { .. } => TypeErrorCode::E0101,
            TypeError::MovedInBranch { .. } => TypeErrorCode::E0102,
            TypeError::CapturedMoved { .. } => TypeErrorCode::E0103,
            TypeError::QualifierMismatch { .. } => TypeErrorCode::E0104,
            TypeError::UnsupportedExpr { .. } => TypeErrorCode::E0001,
            TypeError::NoInstance { required_by: None, .. } => TypeErrorCode::E0301,
            TypeError::NoInstance { required_by: Some(_), .. } => TypeErrorCode::E0303,
            TypeError::OrphanInstance { .. } => TypeErrorCode::E0302,
            TypeError::CannotDerive { .. } => TypeErrorCode::E0304,
            TypeError::DefinitionConflictsWithTraitMethod { .. } => TypeErrorCode::E0305,
            TypeError::UnknownType { .. } => TypeErrorCode::E0011,
            TypeError::QuestionMarkBadReturn { .. } => TypeErrorCode::E0401,
            TypeError::QuestionMarkBadOperand { .. } => TypeErrorCode::E0402,
            TypeError::QuestionMarkMismatch { .. } => TypeErrorCode::E0403,
            TypeError::UnknownModule { .. } => TypeErrorCode::E0501,
            TypeError::CircularImport { .. } => TypeErrorCode::E0502,
        }
    }

    /// Return optional help text for this error.
    pub fn help(&self) -> Option<String> {
        match self {
            TypeError::Mismatch { expected, actual } => {
                match (expected, actual) {
                    (Type::Own(inner_e), _)
                        if matches!(inner_e.as_ref(), Type::Fn(_, _))
                            && matches!(actual, Type::Fn(_, _)) =>
                    {
                        Some("a single-use closure (`own fn`) cannot be used where a multi-use function (`fn`) is expected".to_string())
                    }
                    (_, Type::Own(inner_a))
                        if matches!(inner_a.as_ref(), Type::Fn(_, _))
                            && matches!(expected, Type::Fn(_, _)) =>
                    {
                        Some("a single-use closure (`own fn`) cannot be used where a multi-use function (`fn`) is expected".to_string())
                    }
                    (Type::Own(_), _) | (_, Type::Own(_)) => {
                        Some("an `own` value must be passed to a parameter that accepts ownership".to_string())
                    }
                    _ => None,
                }
            }
            TypeError::DuplicateType { name } => {
                Some(format!("type `{}` is already defined", name))
            }
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
            TypeError::UnknownField { type_name, field_name } => {
                Some(format!("type `{}` has no field `{}`", type_name, field_name))
            }
            TypeError::MissingFields { type_name, fields } => {
                Some(format!("type `{}` requires fields: {}", type_name, fields.join(", ")))
            }
            TypeError::NotAStruct { actual } => {
                Some(format!("the expression has type `{}`, which is not a struct", actual))
            }
            TypeError::NonExhaustive { missing } => {
                Some(format!("add arms for: {}", missing.join(", ")))
            }
            TypeError::AlreadyMoved { name } => {
                Some(format!("`{}` was already consumed by a previous use", name))
            }
            TypeError::MovedInBranch { name } => {
                Some(format!("`{}` was consumed in some but not all branches of a conditional", name))
            }
            TypeError::CapturedMoved { name } => {
                Some(format!("`{}` was already consumed before the closure was created", name))
            }
            TypeError::QualifierMismatch { callee, param, .. } => {
                Some(format!("`{callee}` uses parameter `{param}` more than once, so it cannot accept `own` values. Consider cloning first, or use a function that consumes its argument at most once."))
            }
            TypeError::UnsupportedExpr { .. } => None,
            TypeError::NoInstance { required_by: Some(bound), .. } => {
                Some(format!("required by a bound in `{}`", bound))
            }
            TypeError::NoInstance { .. } => None,
            TypeError::OrphanInstance { trait_name, ty } => {
                Some(format!("cannot implement `{}` for `{}`: only user-defined types can have trait implementations", trait_name, ty))
            }
            TypeError::CannotDerive { trait_name, field_type, .. } => {
                Some(format!("field type `{}` does not implement `{}`", field_type, trait_name))
            }
            TypeError::DefinitionConflictsWithTraitMethod { .. } => {
                Some("trait methods are bound as module-level names; choose a different name for this definition".to_string())
            }
            TypeError::UnknownType { name, suggestion } => {
                if let Some(s) = suggestion {
                    Some(format!("did you mean `{s}`?"))
                } else {
                    Some(format!("type `{}` is not defined", name))
                }
            }
            TypeError::QuestionMarkBadReturn { actual } => {
                Some(format!("function returns `{}`, but `?` requires `Result` or `Option`", actual))
            }
            TypeError::QuestionMarkBadOperand { actual } => {
                Some(format!("`?` can only be applied to `Result` or `Option`, found `{}`", actual))
            }
            TypeError::QuestionMarkMismatch { expr_kind, return_kind } => {
                Some(format!("cannot use `?` on `{}` in a function returning `{}`", expr_kind, return_kind))
            }
            TypeError::UnknownModule { path } => {
                Some(format!("module `{}` does not exist in the stdlib", path))
            }
            TypeError::CircularImport { cycle } => {
                Some(format!("import cycle: {}", cycle.join(" → ")))
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
            TypeError::DuplicateType { name } => {
                write!(f, "duplicate type definition: {}", name)
            }
            TypeError::NotAFunction { actual } => {
                write!(f, "not a function: type {} is not callable", actual)
            }
            TypeError::UnknownField { type_name, field_name } => {
                write!(f, "unknown field: type {} has no field {}", type_name, field_name)
            }
            TypeError::MissingFields { type_name, fields } => {
                write!(f, "missing fields on {}: {}", type_name, fields.join(", "))
            }
            TypeError::NotAStruct { actual } => {
                write!(f, "not a struct: type {} is not a record", actual)
            }
            TypeError::NonExhaustive { missing } => {
                write!(f, "non-exhaustive match: missing {}", missing.join(", "))
            }
            TypeError::AlreadyMoved { name } => {
                write!(f, "value already moved: `{}`", name)
            }
            TypeError::MovedInBranch { name } => {
                write!(f, "value may have been moved in a prior branch: `{}`", name)
            }
            TypeError::CapturedMoved { name } => {
                write!(f, "capture of moved value: `{}`", name)
            }
            TypeError::QualifierMismatch { name, callee, .. } => {
                write!(f, "cannot pass `{name}` to `{callee}`: `{callee}` uses its argument multiple times, but `{name}` is single-use (`own`)")
            }
            TypeError::UnsupportedExpr { description } => {
                write!(f, "not yet implemented: {}", description)
            }
            TypeError::NoInstance { trait_name, ty, .. } => {
                write!(f, "the trait `{}` is not implemented for `{}`", trait_name, ty)
            }
            TypeError::OrphanInstance { trait_name, ty } => {
                write!(f, "orphan instance: cannot implement `{}` for `{}`", trait_name, ty)
            }
            TypeError::CannotDerive { trait_name, type_name, field_type } => {
                write!(f, "cannot derive `{}` for `{}`: field type `{}` does not implement `{}`", trait_name, type_name, field_type, trait_name)
            }
            TypeError::DefinitionConflictsWithTraitMethod { def_name, trait_name } => {
                write!(f, "definition `{}` conflicts with trait method `{}.{}`", def_name, trait_name, def_name)
            }
            TypeError::UnknownType { name, .. } => {
                write!(f, "unknown type: {}", name)
            }
            TypeError::QuestionMarkBadReturn { actual } => {
                write!(f, "`?` operator in function returning `{}` (expected Result or Option)", actual)
            }
            TypeError::QuestionMarkBadOperand { actual } => {
                write!(f, "`?` operator on `{}` (expected Result or Option)", actual)
            }
            TypeError::QuestionMarkMismatch { expr_kind, return_kind } => {
                write!(f, "`?` on `{}` in function returning `{}`", expr_kind, return_kind)
            }
            TypeError::UnknownModule { path } => {
                write!(f, "unknown module: {}", path)
            }
            TypeError::CircularImport { cycle } => {
                write!(f, "circular import detected: {}", cycle.join(" → "))
            }
        }
    }
}

/// A type error paired with the source span where it occurred.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedTypeError {
    pub error: TypeError,
    pub span: Span,
    pub note: Option<String>,
    pub secondary_span: Option<(Span, String)>,
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
#[tracing::instrument(level = "trace", skip(subst))]
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
        // own T ↔ T coercion for non-function types.
        //
        // Design note: Literals and constructors produce `own T` to indicate
        // freshly-created, owned values.  Rather than strip `Own` at every
        // consumption site (binary ops, if-branches, generic args, …) we let
        // unification treat `own T` and `T` as equivalent for non-function
        // types.  This mirrors the `linear ≤ unrestricted` subtyping found
        // in Linear Haskell and Clean's uniqueness types.
        //
        // Function types are excluded: `own fn(…)` (affine closure) must NOT
        // silently coerce to `fn(…)` — that distinction is load-bearing for
        // the linearity checker.
        //
        // Fabrication guard (`T → own T` at return sites) is enforced
        // separately in `infer.rs` before calling `unify`, so this symmetric
        // rule does not weaken ownership guarantees.
        (Type::Own(inner), other) | (other, Type::Own(inner))
            if !matches!(inner.as_ref(), Type::Fn(_, _)) =>
        {
            unify(inner, &other, subst)
        }

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
