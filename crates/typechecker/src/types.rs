use std::collections::HashMap;
use std::fmt;

/// Type variable identifier.
pub type TypeVarId = u32;

/// Convert a type variable ID to a display name: 0→a, 1→b, ..., 25→z, 26→a1, etc.
fn var_name(id: TypeVarId) -> String {
    let letter = (b'a' + (id % 26) as u8) as char;
    let suffix = id / 26;
    if suffix == 0 {
        letter.to_string()
    } else {
        format!("{}{}", letter, suffix)
    }
}

/// Core type representation for the krypton type system.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Unit,
    Fn(Vec<Type>, Box<Type>),
    Var(TypeVarId),
    Named(std::string::String, Vec<Type>),
    Own(Box<Type>),
    Tuple(Vec<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Float => write!(f, "Float"),
            Type::Bool => write!(f, "Bool"),
            Type::String => write!(f, "String"),
            Type::Unit => write!(f, "Unit"),
            Type::Fn(params, ret) => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ") -> {}", ret)
            }
            Type::Var(id) => write!(f, "{}", var_name(*id)),
            Type::Named(name, args) => {
                write!(f, "{}", name)?;
                if !args.is_empty() {
                    write!(f, "[")?;
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", a)?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            Type::Own(inner) => write!(f, "own {}", inner),
            Type::Tuple(elems) => {
                write!(f, "(")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A type scheme with universally quantified type variables (for let-polymorphism).
#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub vars: Vec<TypeVarId>,
    pub ty: Type,
}

impl TypeScheme {
    /// Create a monomorphic type scheme (no quantified variables).
    pub fn mono(ty: Type) -> Self {
        TypeScheme {
            vars: Vec::new(),
            ty,
        }
    }

    /// Instantiate the scheme by replacing each quantified variable with a fresh one.
    pub fn instantiate(&self, fresh: &mut impl FnMut() -> TypeVarId) -> Type {
        if self.vars.is_empty() {
            return self.ty.clone();
        }
        let mut sub = Substitution::new();
        for &var in &self.vars {
            sub.map.insert(var, Type::Var(fresh()));
        }
        sub.apply(&self.ty)
    }
}

impl fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            write!(f, "forall")?;
            for &v in &self.vars {
                write!(f, " {}", var_name(v))?;
            }
            write!(f, ". {}", self.ty)
        }
    }
}

/// A substitution mapping type variables to types.
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    map: HashMap<TypeVarId, Type>,
}

impl Substitution {
    pub fn new() -> Self {
        Substitution {
            map: HashMap::new(),
        }
    }

    /// Create a substitution with a single binding.
    pub fn bind(var: TypeVarId, ty: Type) -> Self {
        let mut map = HashMap::new();
        map.insert(var, ty);
        Substitution { map }
    }

    /// Recursively apply this substitution to a type.
    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(id) => match self.map.get(id) {
                Some(t) => self.apply(t),
                None => ty.clone(),
            },
            Type::Fn(params, ret) => Type::Fn(
                params.iter().map(|p| self.apply(p)).collect(),
                Box::new(self.apply(ret)),
            ),
            Type::Named(name, args) => {
                Type::Named(name.clone(), args.iter().map(|a| self.apply(a)).collect())
            }
            Type::Own(inner) => Type::Own(Box::new(self.apply(inner))),
            Type::Tuple(elems) => Type::Tuple(elems.iter().map(|e| self.apply(e)).collect()),
            _ => ty.clone(),
        }
    }

    /// Apply this substitution to a type scheme (only substitutes non-quantified vars).
    pub fn apply_scheme(&self, scheme: &TypeScheme) -> TypeScheme {
        // Remove quantified vars from the substitution before applying
        let mut restricted = self.clone();
        for &v in &scheme.vars {
            restricted.map.remove(&v);
        }
        TypeScheme {
            vars: scheme.vars.clone(),
            ty: restricted.apply(&scheme.ty),
        }
    }

    /// Compose two substitutions: applying the result is equivalent to applying
    /// `other` first, then `self`.
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = HashMap::new();
        // Apply self to each binding in other
        for (&var, ty) in &other.map {
            result.insert(var, self.apply(ty));
        }
        // Add bindings from self that aren't in other
        for (&var, ty) in &self.map {
            result.entry(var).or_insert_with(|| ty.clone());
        }
        Substitution { map: result }
    }

    /// Look up a variable in the substitution.
    pub fn get(&self, var: TypeVarId) -> Option<&Type> {
        self.map.get(&var)
    }

    /// Insert a binding into the substitution.
    pub fn insert(&mut self, var: TypeVarId, ty: Type) {
        self.map.insert(var, ty);
    }
}

/// Scoped type environment for variable lookups.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    scopes: Vec<HashMap<std::string::String, TypeScheme>>,
    pub fn_return_type: Option<Type>,
}

impl TypeEnv {
    /// Create a new environment with one empty scope.
    pub fn new() -> Self {
        TypeEnv {
            scopes: vec![HashMap::new()],
            fn_return_type: None,
        }
    }

    /// Push a new empty scope.
    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Pop the top scope.
    pub fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    /// Bind a name in the current (top) scope.
    pub fn bind(&mut self, name: std::string::String, scheme: TypeScheme) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, scheme);
        }
    }

    /// Look up a name, searching from the top scope down.
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        for scope in self.scopes.iter().rev() {
            if let Some(scheme) = scope.get(name) {
                return Some(scheme);
            }
        }
        None
    }

    /// Remove a name from all scopes (used when shadowing prelude types).
    pub fn unbind(&mut self, name: &str) {
        for scope in &mut self.scopes {
            scope.remove(name);
        }
    }

    /// Iterate over all type schemes in the environment.
    pub fn for_each_scheme(&self, mut f: impl FnMut(&TypeScheme)) {
        for scope in &self.scopes {
            for scheme in scope.values() {
                f(scheme);
            }
        }
    }
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

/// Fresh type variable generator.
pub struct TypeVarGen {
    next: TypeVarId,
}

impl TypeVarGen {
    pub fn new() -> Self {
        TypeVarGen { next: 0 }
    }

    pub fn fresh(&mut self) -> TypeVarId {
        let id = self.next;
        self.next += 1;
        id
    }
}

impl Default for TypeVarGen {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn var_name_letters() {
        assert_eq!(var_name(0), "a");
        assert_eq!(var_name(1), "b");
        assert_eq!(var_name(25), "z");
        assert_eq!(var_name(26), "a1");
        assert_eq!(var_name(27), "b1");
    }
}
