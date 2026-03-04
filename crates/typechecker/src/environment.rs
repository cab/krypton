// Type environment (Γ in inference rules)
// Tracks variable bindings and type declarations

use crate::types::{DeclId, InferType, TypeScheme, TypeVar};
use std::collections::{HashMap, HashSet};

/// Type environment (Γ in inference rules)
/// Maps variables to their types and tracks type declarations
#[derive(Debug, Clone)]
pub struct Environment {
    /// Variable bindings: var name -> type scheme
    /// Uses stack of scopes for lexical scoping
    bindings: Vec<HashMap<String, TypeScheme>>,

    /// Type declarations: type name -> declaration info
    type_decls: HashMap<String, TypeDeclInfo>,

    /// Fresh variable counter
    next_var: u32,

    /// Fresh declaration ID counter
    next_decl_id: u32,
}

/// Information about a type declaration
#[derive(Debug, Clone)]
pub struct TypeDeclInfo {
    pub decl_id: DeclId,
    pub params: Vec<String>, // Type parameter names
    pub kind: TypeDeclKind,
}

/// Kind of type declaration
#[derive(Debug, Clone)]
pub enum TypeDeclKind {
    Struct { fields: Vec<(String, InferType)> },
    Sum { variants: Vec<VariantInfo> },
    Alias { target: InferType },
}

/// Information about a sum type variant
#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: String,
    pub kind: VariantKind,
}

/// Kind of variant in a sum type
#[derive(Debug, Clone)]
pub enum VariantKind {
    Unit,
    Tuple(Vec<InferType>),
    Struct(Vec<(String, InferType)>),
}

impl Environment {
    /// Create a new environment with built-in types
    pub fn new() -> Self {
        let env = Self {
            bindings: vec![HashMap::new()],
            type_decls: HashMap::new(),
            next_var: 0,
            next_decl_id: 0,
        };
        env
    }

    /// Generate a fresh type variable
    pub fn fresh_var(&mut self) -> TypeVar {
        let var = TypeVar(self.next_var);
        self.next_var += 1;
        var
    }

    /// Generate a fresh declaration ID
    pub fn fresh_decl_id(&mut self) -> DeclId {
        let id = DeclId(self.next_decl_id);
        self.next_decl_id += 1;
        id
    }

    /// Push a new scope (for function bodies, let bindings)
    pub fn push_scope(&mut self) {
        self.bindings.push(HashMap::new());
    }

    /// Pop a scope
    pub fn pop_scope(&mut self) {
        self.bindings.pop();
    }

    /// Bind a variable to a type scheme in the current scope
    pub fn bind(&mut self, name: String, scheme: TypeScheme) {
        if let Some(scope) = self.bindings.last_mut() {
            scope.insert(name, scheme);
        }
    }

    /// Look up a variable (searches all scopes, innermost to outermost)
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        for scope in self.bindings.iter().rev() {
            if let Some(scheme) = scope.get(name) {
                return Some(scheme);
            }
        }
        None
    }

    /// Register a type declaration
    pub fn add_type_decl(&mut self, name: String, info: TypeDeclInfo) {
        self.type_decls.insert(name, info);
    }

    /// Look up a type declaration
    pub fn lookup_type(&self, name: &str) -> Option<&TypeDeclInfo> {
        self.type_decls.get(name)
    }

    /// Get all free type variables in the environment
    /// Used for let-generalization
    pub fn free_vars(&self) -> HashSet<TypeVar> {
        let mut vars = HashSet::new();
        for scope in &self.bindings {
            for scheme in scope.values() {
                vars.extend(scheme.ty.free_vars());
                // Don't include quantified variables
                for v in &scheme.forall {
                    vars.remove(v);
                }
            }
        }
        vars
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PrimitiveType;

    #[test]
    fn test_fresh_var() {
        let mut env = Environment::new();
        let v1 = env.fresh_var();
        let v2 = env.fresh_var();

        assert_eq!(v1, TypeVar(0));
        assert_eq!(v2, TypeVar(1));
    }

    #[test]
    fn test_scope_binding() {
        let mut env = Environment::new();

        // Bind in outer scope
        env.bind(
            "x".to_string(),
            TypeScheme {
                forall: vec![],
                ty: InferType::Primitive(PrimitiveType::Int),
            },
        );

        // Push inner scope
        env.push_scope();
        env.bind(
            "y".to_string(),
            TypeScheme {
                forall: vec![],
                ty: InferType::Primitive(PrimitiveType::String),
            },
        );

        // Should find both
        assert!(env.lookup("x").is_some());
        assert!(env.lookup("y").is_some());

        // Pop inner scope
        env.pop_scope();

        // Should only find x now
        assert!(env.lookup("x").is_some());
        assert!(env.lookup("y").is_none());
    }

    #[test]
    fn test_shadowing() {
        let mut env = Environment::new();

        // Bind x in outer scope
        env.bind(
            "x".to_string(),
            TypeScheme {
                forall: vec![],
                ty: InferType::Primitive(PrimitiveType::Int),
            },
        );

        // Push inner scope and shadow x
        env.push_scope();
        env.bind(
            "x".to_string(),
            TypeScheme {
                forall: vec![],
                ty: InferType::Primitive(PrimitiveType::String),
            },
        );

        // Should find String version
        let scheme = env.lookup("x").unwrap();
        assert_eq!(scheme.ty, InferType::Primitive(PrimitiveType::String));

        // Pop scope
        env.pop_scope();

        // Should find Int version again
        let scheme = env.lookup("x").unwrap();
        assert_eq!(scheme.ty, InferType::Primitive(PrimitiveType::Int));
    }

    #[test]
    fn test_free_vars() {
        let mut env = Environment::new();
        let var_a = TypeVar(0);
        let var_b = TypeVar(1);

        // Bind x with free variable 'a
        env.bind(
            "x".to_string(),
            TypeScheme {
                forall: vec![],
                ty: InferType::Var(var_a),
            },
        );

        // Bind y with quantified variable 'b (should not be free)
        env.bind(
            "y".to_string(),
            TypeScheme {
                forall: vec![var_b],
                ty: InferType::Var(var_b),
            },
        );

        let free = env.free_vars();

        // Should only contain 'a, not 'b
        assert!(free.contains(&var_a));
        assert!(!free.contains(&var_b));
    }

    #[test]
    fn test_type_decl() {
        let mut env = Environment::new();
        let decl_id = env.fresh_decl_id();

        let info = TypeDeclInfo {
            decl_id,
            params: vec![],
            kind: TypeDeclKind::Struct {
                fields: vec![
                    ("x".to_string(), InferType::Primitive(PrimitiveType::Int)),
                    ("y".to_string(), InferType::Primitive(PrimitiveType::Int)),
                ],
            },
        };

        env.add_type_decl("Point".to_string(), info);

        let looked_up = env.lookup_type("Point").unwrap();
        assert_eq!(looked_up.decl_id, decl_id);
    }
}
