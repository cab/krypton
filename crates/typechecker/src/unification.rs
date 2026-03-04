// Unification algorithm with occurs check
// Core algorithm for solving type constraints in Algorithm J

use crate::error::TypeError;
use crate::substitution::Substitution;
use crate::types::InferType;
use alang_parser::ast::Span;

/// Unify two types, returning a substitution or error
/// Implements the unification algorithm with occurs check
pub fn unify(t1: &InferType, t2: &InferType, span: &Span) -> Result<Substitution, TypeError> {
    use InferType::*;

    match (t1, t2) {
        // Same type variable
        (Var(v1), Var(v2)) if v1 == v2 => Ok(Substitution::new()),

        // Bind type variable to type (with occurs check)
        (Var(v), t) | (t, Var(v)) => {
            if t.free_vars().contains(v) {
                Err(TypeError::infinite_type(t, span.clone()))
            } else {
                let mut subst = Substitution::new();
                subst.insert(*v, t.clone());
                Ok(subst)
            }
        }

        // Same primitive
        (Primitive(p1), Primitive(p2)) if p1 == p2 => Ok(Substitution::new()),

        // Nominal types: must have same declaration ID
        (
            Nominal {
                decl_id: id1,
                type_args: args1,
                ..
            },
            Nominal {
                decl_id: id2,
                type_args: args2,
                ..
            },
        ) if id1 == id2 => {
            // Unify type arguments
            if args1.len() != args2.len() {
                return Err(TypeError::type_mismatch(t1, t2, span.clone()));
            }

            let mut subst = Substitution::new();
            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                let s = unify(&subst.apply(arg1), &subst.apply(arg2), span)?;
                subst = subst.compose(&s);
            }
            Ok(subst)
        }

        // Function types
        (
            Function {
                params: p1,
                ret: r1,
            },
            Function {
                params: p2,
                ret: r2,
            },
        ) => {
            if p1.len() != p2.len() {
                return Err(TypeError::type_mismatch(t1, t2, span.clone()));
            }

            let mut subst = Substitution::new();

            // Unify parameters
            for (param1, param2) in p1.iter().zip(p2.iter()) {
                let s = unify(&subst.apply(param1), &subst.apply(param2), span)?;
                subst = subst.compose(&s);
            }

            // Unify return types
            let s = unify(&subst.apply(r1), &subst.apply(r2), span)?;
            subst = subst.compose(&s);

            Ok(subst)
        }

        // Affine types: unify inner types
        (Move(t1), Move(t2)) => unify(t1, t2, span),

        // Tuple types
        (Tuple(ts1), Tuple(ts2)) => {
            if ts1.len() != ts2.len() {
                return Err(TypeError::type_mismatch(t1, t2, span.clone()));
            }

            let mut subst = Substitution::new();
            for (ty1, ty2) in ts1.iter().zip(ts2.iter()) {
                let s = unify(&subst.apply(ty1), &subst.apply(ty2), span)?;
                subst = subst.compose(&s);
            }
            Ok(subst)
        }

        // Type mismatch
        _ => Err(TypeError::type_mismatch(t1, t2, span.clone())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::ErrorCode;
    use crate::types::{DeclId, PrimitiveType, TypeVar};

    fn span() -> Span {
        Span { start: 0, end: 0 }
    }

    #[test]
    fn test_unify_same_primitives() {
        let t1 = InferType::Primitive(PrimitiveType::Int);
        let t2 = InferType::Primitive(PrimitiveType::Int);

        let result = unify(&t1, &t2, &span());
        assert!(result.is_ok());
    }

    #[test]
    fn test_unify_different_primitives() {
        let t1 = InferType::Primitive(PrimitiveType::Int);
        let t2 = InferType::Primitive(PrimitiveType::String);

        let result = unify(&t1, &t2, &span());
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, ErrorCode::TypeMismatch);
    }

    #[test]
    fn test_unify_var_with_type() {
        let var_a = TypeVar(0);
        let t1 = InferType::Var(var_a);
        let t2 = InferType::Primitive(PrimitiveType::Int);

        let result = unify(&t1, &t2, &span()).unwrap();

        // Should bind a -> Int
        let bound = result.apply(&t1);
        assert_eq!(bound, InferType::Primitive(PrimitiveType::Int));
    }

    #[test]
    fn test_unify_same_var() {
        let var_a = TypeVar(0);
        let t1 = InferType::Var(var_a);
        let t2 = InferType::Var(var_a);

        let result = unify(&t1, &t2, &span());
        assert!(result.is_ok());
    }

    #[test]
    fn test_occurs_check() {
        // Try to unify 'a with fn('a) -> Int
        // This should fail because 'a occurs in the type
        let var_a = TypeVar(0);
        let t1 = InferType::Var(var_a);
        let t2 = InferType::Function {
            params: vec![InferType::Var(var_a)],
            ret: Box::new(InferType::Primitive(PrimitiveType::Int)),
        };

        let result = unify(&t1, &t2, &span());
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, ErrorCode::InfiniteType);
    }

    #[test]
    fn test_unify_functions() {
        let var_a = TypeVar(0);
        let var_b = TypeVar(1);

        let t1 = InferType::Function {
            params: vec![InferType::Var(var_a)],
            ret: Box::new(InferType::Primitive(PrimitiveType::Int)),
        };

        let t2 = InferType::Function {
            params: vec![InferType::Primitive(PrimitiveType::String)],
            ret: Box::new(InferType::Var(var_b)),
        };

        let result = unify(&t1, &t2, &span()).unwrap();

        // Should bind a -> String, b -> Int
        let bound_a = result.apply(&InferType::Var(var_a));
        let bound_b = result.apply(&InferType::Var(var_b));

        assert_eq!(bound_a, InferType::Primitive(PrimitiveType::String));
        assert_eq!(bound_b, InferType::Primitive(PrimitiveType::Int));
    }

    #[test]
    fn test_unify_nominal() {
        // Same declaration ID should unify
        let decl_id = DeclId(0);
        let t1 = InferType::Nominal {
            name: "Point".to_string(),
            decl_id,
            type_args: vec![],
        };
        let t2 = InferType::Nominal {
            name: "Point".to_string(),
            decl_id,
            type_args: vec![],
        };

        let result = unify(&t1, &t2, &span());
        assert!(result.is_ok());
    }

    #[test]
    fn test_unify_nominal_different_ids() {
        // Different declaration IDs should NOT unify (nominal typing)
        let t1 = InferType::Nominal {
            name: "Point".to_string(),
            decl_id: DeclId(0),
            type_args: vec![],
        };
        let t2 = InferType::Nominal {
            name: "Vec2".to_string(),
            decl_id: DeclId(1),
            type_args: vec![],
        };

        let result = unify(&t1, &t2, &span());
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().code, ErrorCode::TypeMismatch);
    }

    #[test]
    fn test_unify_generic_nominal() {
        // Option['a] ~ Option[Int] should bind 'a -> Int
        let var_a = TypeVar(0);
        let t1 = InferType::Nominal {
            name: "Option".to_string(),
            decl_id: DeclId(0),
            type_args: vec![InferType::Var(var_a)],
        };
        let t2 = InferType::Nominal {
            name: "Option".to_string(),
            decl_id: DeclId(0),
            type_args: vec![InferType::Primitive(PrimitiveType::Int)],
        };

        let result = unify(&t1, &t2, &span()).unwrap();

        let bound = result.apply(&InferType::Var(var_a));
        assert_eq!(bound, InferType::Primitive(PrimitiveType::Int));
    }
}
