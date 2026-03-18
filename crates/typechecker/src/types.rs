use std::collections::{HashMap, HashSet};
use std::fmt;

/// Type variable identifier (newtype wrapper for type safety).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(u32);

impl fmt::Display for TypeVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

impl TypeVarId {
    /// Human-readable name: 0→a, 1→b, ..., 25→z, 26→a1, etc.
    pub fn display_name(self) -> String {
        let letter = (b'a' + (self.0 % 26) as u8) as char;
        let suffix = self.0 / 26;
        if suffix == 0 {
            letter.to_string()
        } else {
            format!("{}{}", letter, suffix)
        }
    }
}

/// Core type representation for the krypton type system.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Unit,
    Fn(Vec<Type>, Box<Type>),
    Var(TypeVarId),
    Named(std::string::String, Vec<Type>),
    /// Type constructor application where the constructor is a type variable.
    /// e.g., `f[a]` when `f` is a higher-kinded type variable.
    App(Box<Type>, Vec<Type>),
    Own(Box<Type>),
    Tuple(Vec<Type>),
}

/// Normalize a type application: if the constructor is a zero-arg Named type,
/// fold the args into it; otherwise reconstruct App.
pub fn normalize_app(ctor: Type, args: Vec<Type>) -> Type {
    match ctor {
        Type::Named(name, ctor_args) if ctor_args.is_empty() => Type::Named(name, args),
        // Partial application: Named("Result", [e]) applied to [a] → Named("Result", [e, a])
        Type::Named(name, mut ctor_args) => {
            ctor_args.extend(args);
            Type::Named(name, ctor_args)
        }
        _ => Type::App(Box::new(ctor), args),
    }
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
            Type::Var(id) => write!(f, "{}", id.display_name()),
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
            Type::App(ctor, args) => {
                write!(f, "{}", ctor)?;
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
            Type::Own(inner) => write!(f, "~{}", inner),
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

impl TypeScheme {
    /// Renormalize type variables to start from 0, making schemes independent of
    /// the global TypeVarGen counter. Returns the renormalized scheme and the
    /// old→new variable mapping (for updating related data structures).
    pub fn renormalize(&self) -> (TypeScheme, Vec<(TypeVarId, TypeVarId)>) {
        if self.vars.is_empty() {
            return (self.clone(), vec![]);
        }
        let mut gen = TypeVarGen::new();
        let mut mapping = Vec::new();
        let mut subst = Substitution::new();
        for &old_var in &self.vars {
            let new_var = gen.fresh();
            mapping.push((old_var, new_var));
            subst.insert(old_var, Type::Var(new_var));
        }
        let new_ty = subst.apply(&self.ty);
        let new_vars = mapping.iter().map(|&(_, new)| new).collect();
        (TypeScheme { vars: new_vars, ty: new_ty }, mapping)
    }
}

impl fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            write!(f, "forall")?;
            for &v in &self.vars {
                write!(f, " {}", v.display_name())?;
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
        let mut visiting = HashSet::new();
        let mut chain = Vec::new();
        self.apply_inner(ty, &mut visiting, &mut chain)
    }

    fn apply_inner(
        &self,
        ty: &Type,
        visiting: &mut HashSet<TypeVarId>,
        chain: &mut Vec<TypeVarId>,
    ) -> Type {
        match ty {
            Type::Var(id) => match self.map.get(id) {
                Some(t) => {
                    if !visiting.insert(*id) {
                        chain.push(*id);
                        panic!(
                            "substitution cycle detected while applying type vars {:?}",
                            chain
                        );
                    }
                    chain.push(*id);
                    let resolved = self.apply_inner(t, visiting, chain);
                    chain.pop();
                    visiting.remove(id);
                    resolved
                }
                None => ty.clone(),
            },
            Type::Fn(params, ret) => Type::Fn(
                params
                    .iter()
                    .map(|p| self.apply_inner(p, visiting, chain))
                    .collect(),
                Box::new(self.apply_inner(ret, visiting, chain)),
            ),
            Type::Named(name, args) => Type::Named(
                name.clone(),
                args.iter()
                    .map(|a| self.apply_inner(a, visiting, chain))
                    .collect(),
            ),
            Type::App(ctor, args) => {
                let applied_ctor = self.apply_inner(ctor, visiting, chain);
                let applied_args: Vec<Type> = args
                    .iter()
                    .map(|a| self.apply_inner(a, visiting, chain))
                    .collect();
                normalize_app(applied_ctor, applied_args)
            }
            Type::Own(inner) => Type::Own(Box::new(self.apply_inner(inner, visiting, chain))),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| self.apply_inner(e, visiting, chain))
                    .collect(),
            ),
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
    provenance: HashMap<std::string::String, std::string::String>,
}

impl TypeEnv {
    /// Create a new environment with one empty scope.
    pub fn new() -> Self {
        TypeEnv {
            scopes: vec![HashMap::new()],
            fn_return_type: None,
            provenance: HashMap::new(),
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

    /// Bind a name in the current scope with provenance (source module path).
    pub fn bind_with_provenance(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        module_path: std::string::String,
    ) {
        self.bind(name.clone(), scheme);
        self.provenance.insert(name, module_path);
    }

    /// Get the provenance (source module path) for a binding, if any.
    pub fn get_provenance(&self, name: &str) -> Option<&str> {
        self.provenance.get(name).map(|s| s.as_str())
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
    next: u32,
}

impl TypeVarGen {
    pub fn new() -> Self {
        TypeVarGen { next: 0 }
    }

    pub fn fresh(&mut self) -> TypeVarId {
        let id = TypeVarId(self.next);
        self.next += 1;
        id
    }

    /// Ensure the next generated ID is strictly greater than `id`.
    pub fn reserve_past(&mut self, id: TypeVarId) {
        self.next = self.next.max(id.0 + 1);
    }
}

impl Default for TypeVarGen {
    fn default() -> Self {
        Self::new()
    }
}

impl Type {
    /// Strip `Own` wrappers recursively, including inside `Named` type args.
    pub fn strip_own(&self) -> Type {
        match self {
            Type::Own(inner) => inner.strip_own(),
            Type::Named(name, args) => Type::Named(
                name.clone(),
                args.iter().map(|a| a.strip_own()).collect(),
            ),
            other => other.clone(),
        }
    }
}

/// Canonical name for JVM artifact naming (class names, method names).
/// Not used for HashMap keys — those use `(String, Type)` tuples directly.
pub fn type_to_canonical_name(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "Unit".to_string(),
        Type::Named(name, args) if args.is_empty() => name.clone(),
        Type::Named(name, args) => {
            let arg_strs: Vec<String> = args.iter().map(type_to_canonical_name).collect();
            format!("{}${}", name, arg_strs.join("$"))
        }
        Type::Own(inner) => type_to_canonical_name(inner),
        Type::Var(_) => "T".to_string(),
        other => format!("{other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_name_letters() {
        assert_eq!(TypeVarId(0).display_name(), "a");
        assert_eq!(TypeVarId(1).display_name(), "b");
        assert_eq!(TypeVarId(25).display_name(), "z");
        assert_eq!(TypeVarId(26).display_name(), "a1");
        assert_eq!(TypeVarId(27).display_name(), "b1");
    }
}
