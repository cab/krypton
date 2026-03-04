// Substitution: maps type variables to types
// Core data structure for unification in Algorithm J

use crate::types::{InferType, TypeVar};
use std::collections::HashMap;

/// Substitution maps type variables to types
/// Represents the accumulated unification constraints
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    map: HashMap<TypeVar, InferType>,
}

impl Substitution {
    /// Create a new empty substitution
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    /// Insert a binding (type variable -> type)
    pub fn insert(&mut self, var: TypeVar, ty: InferType) {
        self.map.insert(var, ty);
    }

    /// Look up a type variable
    pub fn get(&self, var: TypeVar) -> Option<&InferType> {
        self.map.get(&var)
    }

    /// Apply substitution to a type (recursively)
    /// This is the key operation: replace all type variables with their bindings
    /// Follows chains of substitutions to their conclusion
    pub fn apply(&self, ty: &InferType) -> InferType {
        match ty {
            InferType::Var(v) => match self.get(*v) {
                Some(t) => self.apply(t), // Follow chains transitively
                None => ty.clone(),
            },
            InferType::Function { params, ret } => InferType::Function {
                params: params.iter().map(|p| self.apply(p)).collect(),
                ret: Box::new(self.apply(ret)),
            },
            InferType::Nominal {
                name,
                decl_id,
                type_args,
            } => InferType::Nominal {
                name: name.clone(),
                decl_id: *decl_id,
                type_args: type_args.iter().map(|a| self.apply(a)).collect(),
            },
            InferType::Move(inner) => InferType::Move(Box::new(self.apply(inner))),
            InferType::Tuple(types) => {
                InferType::Tuple(types.iter().map(|t| self.apply(t)).collect())
            }
            InferType::Primitive(_) => ty.clone(),
        }
    }

    /// Compose two substitutions: (s2 ∘ s1)
    /// Apply s2 to all bindings in s1, then merge
    /// Used to combine substitutions from sequential unifications
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = Substitution::new();

        // Apply other to all bindings in self
        for (var, ty) in &self.map {
            result.insert(*var, other.apply(ty));
        }

        // Add bindings from other not in self
        for (var, ty) in &other.map {
            if !result.map.contains_key(var) {
                result.insert(*var, ty.clone());
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{DeclId, PrimitiveType};

    #[test]
    fn test_apply_substitution() {
        let mut subst = Substitution::new();
        let var_a = TypeVar(0);
        subst.insert(var_a, InferType::Primitive(PrimitiveType::Int));

        let ty = InferType::Var(var_a);
        let result = subst.apply(&ty);

        assert_eq!(result, InferType::Primitive(PrimitiveType::Int));
    }

    #[test]
    fn test_apply_chains() {
        // Test transitive application: a -> b, b -> Int
        let mut subst = Substitution::new();
        let var_a = TypeVar(0);
        let var_b = TypeVar(1);

        subst.insert(var_a, InferType::Var(var_b));
        subst.insert(var_b, InferType::Primitive(PrimitiveType::Int));

        let ty = InferType::Var(var_a);
        let result = subst.apply(&ty);

        assert_eq!(result, InferType::Primitive(PrimitiveType::Int));
    }

    #[test]
    fn test_apply_function() {
        let mut subst = Substitution::new();
        let var_a = TypeVar(0);
        subst.insert(var_a, InferType::Primitive(PrimitiveType::Int));

        let ty = InferType::Function {
            params: vec![InferType::Var(var_a)],
            ret: Box::new(InferType::Primitive(PrimitiveType::String)),
        };

        let result = subst.apply(&ty);

        match result {
            InferType::Function { params, .. } => {
                assert_eq!(params[0], InferType::Primitive(PrimitiveType::Int));
            }
            _ => panic!("Expected function type"),
        }
    }

    #[test]
    fn test_compose_substitutions() {
        // s1 = {a -> Int}, s2 = {b -> a}
        // s2 ∘ s1 = {a -> Int, b -> Int}
        let mut s1 = Substitution::new();
        let var_a = TypeVar(0);
        s1.insert(var_a, InferType::Primitive(PrimitiveType::Int));

        let mut s2 = Substitution::new();
        let var_b = TypeVar(1);
        s2.insert(var_b, InferType::Var(var_a));

        let composed = s1.compose(&s2);

        // Check that a -> Int
        let result_a = composed.apply(&InferType::Var(var_a));
        assert_eq!(result_a, InferType::Primitive(PrimitiveType::Int));

        // Check that b -> Int (not b -> a)
        let result_b = composed.apply(&InferType::Var(var_b));
        assert_eq!(result_b, InferType::Primitive(PrimitiveType::Int));
    }

    #[test]
    fn test_apply_nominal() {
        let mut subst = Substitution::new();
        let var_a = TypeVar(0);
        subst.insert(var_a, InferType::Primitive(PrimitiveType::String));

        let ty = InferType::Nominal {
            name: "Option".to_string(),
            decl_id: DeclId(0),
            type_args: vec![InferType::Var(var_a)],
        };

        let result = subst.apply(&ty);

        match result {
            InferType::Nominal { type_args, .. } => {
                assert_eq!(type_args[0], InferType::Primitive(PrimitiveType::String));
            }
            _ => panic!("Expected nominal type"),
        }
    }

    #[test]
    fn test_apply_move() {
        let mut subst = Substitution::new();
        let var_a = TypeVar(0);
        subst.insert(var_a, InferType::Primitive(PrimitiveType::Int));

        let ty = InferType::Move(Box::new(InferType::Var(var_a)));
        let result = subst.apply(&ty);

        match result {
            InferType::Move(inner) => {
                assert_eq!(*inner, InferType::Primitive(PrimitiveType::Int));
            }
            _ => panic!("Expected move type"),
        }
    }
}
