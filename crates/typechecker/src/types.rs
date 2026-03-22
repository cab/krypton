use std::collections::{HashMap, HashSet};
use std::fmt;

/// Type variable identifier (newtype wrapper for type safety).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(pub(crate) u32);

impl fmt::Display for TypeVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_name())
    }
}

impl TypeVarId {
    /// Get the numeric index of this type variable.
    pub fn index(self) -> usize {
        self.0 as usize
    }

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
    /// Sentinel for unfilled return positions in partially-applied function type
    /// constructors. Used by HKT machinery — never appears in user-facing types.
    /// Consumed by `normalize_app` when applying type arguments.
    FnHole,
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
        // Partial fn application: Fn([r], FnHole) applied to [a] → Fn([r], a)
        Type::Fn(params, hole) if args.len() == 1 => {
            debug_assert_eq!(*hole, Type::FnHole, "normalize_app: expected FnHole sentinel in partial fn constructor");
            Type::Fn(params, Box::new(args.into_iter().next().unwrap()))
        }
        Type::Fn(mut params, hole) => {
            debug_assert_eq!(*hole, Type::FnHole, "normalize_app: expected FnHole sentinel in partial fn constructor");
            // Multiple holes: first args extend params, last becomes ret
            let ret = args.last().unwrap().clone();
            params.extend(args[..args.len() - 1].iter().cloned());
            Type::Fn(params, Box::new(ret))
        }
        _ => Type::App(Box::new(ctor), args),
    }
}

/// Decompose a concrete `Fn` type into (partial_ctor, remaining_args) for matching
/// against `App(ctor, args)` in HKT contexts.
///
/// Given `Fn([P, Q, R], S)` and `applied_count = 2`:
///   - partial_ctor = `Fn([P], FnHole)` (the partial fn constructor)
///   - remaining = `[R, S]` (the applied arguments)
///
/// Returns `None` if `applied_count` is 0 or exceeds total arity (params + ret).
pub fn decompose_fn_for_app(params: &[Type], ret: &Type, applied_count: usize) -> Option<(Type, Vec<Type>)> {
    let total = params.len() + 1;
    if applied_count == 0 || applied_count > total {
        return None;
    }
    let ctor_count = total - applied_count;
    let ctor = Type::Fn(params[..ctor_count].to_vec(), Box::new(Type::FnHole));
    let mut remaining: Vec<Type> = params[ctor_count..].to_vec();
    remaining.push(ret.clone());
    Some((ctor, remaining))
}

impl Type {
    /// Re-letter type variables to sequential a, b, c, ... based on first-appearance order.
    /// Preserves identity: same original var → same new letter throughout.
    pub fn renumber_for_display(&self) -> Type {
        let mut mapping = HashMap::new();
        let mut next_id = 0u32;
        self.renumber_inner(&mut mapping, &mut next_id)
    }

    fn renumber_inner(&self, mapping: &mut HashMap<TypeVarId, TypeVarId>, next_id: &mut u32) -> Type {
        match self {
            Type::Var(id) => {
                let new_id = *mapping.entry(*id).or_insert_with(|| {
                    let id = TypeVarId(*next_id);
                    *next_id += 1;
                    id
                });
                Type::Var(new_id)
            }
            Type::Fn(params, ret) => Type::Fn(
                params.iter().map(|p| p.renumber_inner(mapping, next_id)).collect(),
                Box::new(ret.renumber_inner(mapping, next_id)),
            ),
            Type::Named(n, args) => Type::Named(
                n.clone(),
                args.iter().map(|a| a.renumber_inner(mapping, next_id)).collect(),
            ),
            Type::Own(inner) => Type::Own(Box::new(inner.renumber_inner(mapping, next_id))),
            Type::Tuple(elems) => Type::Tuple(
                elems.iter().map(|e| e.renumber_inner(mapping, next_id)).collect(),
            ),
            Type::App(ctor, args) => Type::App(
                Box::new(ctor.renumber_inner(mapping, next_id)),
                args.iter().map(|a| a.renumber_inner(mapping, next_id)).collect(),
            ),
            other => other.clone(),
        }
    }

    /// Remap only vars present in the mapping; leave others unchanged.
    fn remap_vars(&self, mapping: &HashMap<TypeVarId, TypeVarId>) -> Type {
        match self {
            Type::Var(id) => Type::Var(*mapping.get(id).unwrap_or(id)),
            Type::Fn(params, ret) => Type::Fn(
                params.iter().map(|p| p.remap_vars(mapping)).collect(),
                Box::new(ret.remap_vars(mapping)),
            ),
            Type::Named(n, args) => Type::Named(
                n.clone(), args.iter().map(|a| a.remap_vars(mapping)).collect(),
            ),
            Type::Own(inner) => Type::Own(Box::new(inner.remap_vars(mapping))),
            Type::Tuple(elems) => Type::Tuple(
                elems.iter().map(|e| e.remap_vars(mapping)).collect(),
            ),
            Type::App(ctor, args) => Type::App(
                Box::new(ctor.remap_vars(mapping)),
                args.iter().map(|a| a.remap_vars(mapping)).collect(),
            ),
            other => other.clone(),
        }
    }
}

/// Renumber type vars across multiple types sharing the same mapping.
pub fn renumber_types_for_display(types: &[&Type]) -> Vec<Type> {
    let mut mapping = HashMap::new();
    let mut next_id = 0u32;
    types.iter().map(|t| t.renumber_inner(&mut mapping, &mut next_id)).collect()
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
                write!(f, "(")?;
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
            Type::FnHole => write!(f, "_"),
        }
    }
}

/// A type scheme with universally quantified type variables (for let-polymorphism).
#[derive(Debug, Clone, PartialEq)]
pub struct TypeScheme {
    pub vars: Vec<TypeVarId>,
    pub ty: Type,
    /// User-written type parameter names (e.g., from `fun foo[elem](...)`).
    /// Display uses these instead of auto-generated letters when available.
    pub var_names: HashMap<TypeVarId, String>,
}

impl TypeScheme {
    /// Create a monomorphic type scheme (no quantified variables).
    pub fn mono(ty: Type) -> Self {
        TypeScheme {
            vars: Vec::new(),
            ty,
            var_names: HashMap::new(),
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
        let new_var_names = self.var_names.iter()
            .filter_map(|(old, name)| {
                mapping.iter().find(|(o, _)| o == old).map(|(_, new)| (*new, name.clone()))
            })
            .collect();
        (TypeScheme { vars: new_vars, ty: new_ty, var_names: new_var_names }, mapping)
    }
}

impl TypeScheme {
    /// Build display names for this scheme's quantified vars.
    /// Uses user names when available, sequential letters otherwise.
    pub fn display_var_names(&self) -> (Type, Vec<String>) {
        // 1. Renumber vars to sequential 0,1,2,... (order in vars list)
        let mut id_mapping = HashMap::new();
        let mut next_id = 0u32;
        for &v in &self.vars {
            id_mapping.entry(v).or_insert_with(|| {
                let new = TypeVarId(next_id);
                next_id += 1;
                new
            });
        }
        let renamed_ty = self.ty.remap_vars(&id_mapping);

        // 2. Assign display names: user names first, then sequential letters
        let mut used: HashSet<String> = HashSet::new();
        let mut names = Vec::new();
        let mut letter_idx = 0u32;
        for &v in &self.vars {
            if let Some(user_name) = self.var_names.get(&v) {
                names.push(user_name.clone());
                used.insert(user_name.clone());
            } else {
                loop {
                    let candidate = TypeVarId(letter_idx).display_name();
                    letter_idx += 1;
                    if !used.contains(&candidate) {
                        used.insert(candidate.clone());
                        names.push(candidate);
                        break;
                    }
                }
            }
        }

        (renamed_ty, names)
    }
}

/// Trait for looking up user-written variable names by TypeVarId.
pub trait VarNameLookup {
    fn lookup(&self, id: &TypeVarId) -> Option<&str>;
}

impl VarNameLookup for [String] {
    fn lookup(&self, id: &TypeVarId) -> Option<&str> {
        let idx = id.index();
        if idx < self.len() {
            Some(&self[idx])
        } else {
            None
        }
    }
}

impl VarNameLookup for HashMap<TypeVarId, &str> {
    fn lookup(&self, id: &TypeVarId) -> Option<&str> {
        self.get(id).copied()
    }
}

/// Format a type using a `VarNameLookup` for variable names.
/// Falls back to `display_name()` for vars not found in the lookup.
fn format_type_impl<L: VarNameLookup + ?Sized>(ty: &Type, names: &L) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "Unit".to_string(),
        Type::Var(id) => {
            if let Some(name) = names.lookup(id) {
                name.to_string()
            } else {
                id.display_name()
            }
        }
        Type::Fn(params, ret) => {
            let ps: Vec<String> = params.iter().map(|p| format_type_impl(p, names)).collect();
            format!("({}) -> {}", ps.join(", "), format_type_impl(ret, names))
        }
        Type::Named(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let as_: Vec<String> = args.iter().map(|a| format_type_impl(a, names)).collect();
                format!("{}[{}]", name, as_.join(", "))
            }
        }
        Type::App(ctor, args) => {
            let base = format_type_impl(ctor, names);
            if args.is_empty() {
                base
            } else {
                let as_: Vec<String> = args.iter().map(|a| format_type_impl(a, names)).collect();
                format!("{}[{}]", base, as_.join(", "))
            }
        }
        Type::Own(inner) => format!("~{}", format_type_impl(inner, names)),
        Type::Tuple(elems) => {
            let es: Vec<String> = elems.iter().map(|e| format_type_impl(e, names)).collect();
            format!("({})", es.join(", "))
        }
        Type::FnHole => "_".to_string(),
    }
}

/// Format a type using explicit var name mappings instead of TypeVarId::display_name().
/// Var(TypeVarId(n)) maps to var_names[n].
pub fn format_type_with_var_names(ty: &Type, var_names: &[String]) -> String {
    format_type_impl(ty, var_names)
}

/// Format a type using a map from TypeVarId to user-written name.
/// Falls back to `display_name()` for vars not in the map.
pub fn format_type_with_var_map(ty: &Type, names: &HashMap<TypeVarId, &str>) -> String {
    format_type_impl(ty, names)
}

impl fmt::Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            let (renamed_ty, names) = self.display_var_names();
            write!(f, "forall")?;
            for name in &names {
                write!(f, " {}", name)?;
            }
            write!(f, ". {}", format_type_with_var_names(&renamed_ty, &names))
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
            var_names: scheme.var_names.clone(),
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

/// Span of a function definition, optionally in a different source module.
#[derive(Debug, Clone)]
pub struct DefSpan {
    pub span: krypton_parser::ast::Span,
    pub source_module: Option<String>, // None = same file
}

/// Scoped type environment for variable lookups.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    scopes: Vec<HashMap<std::string::String, TypeScheme>>,
    pub fn_return_type: Option<Type>,
    provenance: HashMap<std::string::String, std::string::String>,
    def_spans: HashMap<std::string::String, DefSpan>,
}

impl TypeEnv {
    /// Create a new environment with one empty scope.
    pub fn new() -> Self {
        TypeEnv {
            scopes: vec![HashMap::new()],
            fn_return_type: None,
            provenance: HashMap::new(),
            def_spans: HashMap::new(),
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

    /// Bind a name and record its definition span (for secondary diagnostics).
    pub fn bind_with_def_span(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        def_span: DefSpan,
    ) {
        self.bind(name.clone(), scheme);
        self.def_spans.insert(name, def_span);
    }

    /// Get the definition span for a binding, if any.
    pub fn get_def_span(&self, name: &str) -> Option<&DefSpan> {
        self.def_spans.get(name)
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

/// Head type constructor name for parameterized instance dispatch.
/// Returns the outermost constructor as a unique identifier.
pub fn head_type_name(ty: &Type) -> String {
    match ty {
        Type::Own(inner) => head_type_name(inner),
        Type::Named(name, _) => name.clone(),
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "Unit".to_string(),
        Type::Fn(params, _) => format!("$Fun{}", params.len()),
        other => unreachable!("unexpected type in head_type_name: {other:?}"),
    }
}

/// Unique canonical name for a type, used for artifact naming and method mangling.
/// Produces collision-free identifiers: `$Fun` prefix prevents collision with
/// user-defined type names, and type vars are normalized by order of occurrence.
pub fn type_to_canonical_name(ty: &Type) -> String {
    let mut var_map = HashMap::new();
    canonical_name_inner(ty, &mut var_map)
}

fn canonical_name_inner(ty: &Type, var_map: &mut HashMap<TypeVarId, usize>) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "Unit".to_string(),
        Type::Named(name, args) if args.is_empty() => name.clone(),
        Type::Named(name, args) => {
            let arg_strs: Vec<String> = args.iter().map(|a| canonical_name_inner(a, var_map)).collect();
            format!("{}${}", name, arg_strs.join("$"))
        }
        Type::Fn(params, ret) => {
            let mut parts: Vec<String> = params.iter().map(|p| canonical_name_inner(p, var_map)).collect();
            parts.push(canonical_name_inner(ret, var_map));
            format!("$Fun{}${}", params.len(), parts.join("$"))
        }
        Type::Own(inner) => canonical_name_inner(inner, var_map),
        Type::Var(id) => {
            let next = var_map.len();
            let idx = *var_map.entry(*id).or_insert(next);
            format!("T{idx}")
        }
        Type::FnHole => "$FnHole".to_string(),
        other => unreachable!("unexpected type in canonical_name_inner: {other:?}"),
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

    #[test]
    fn canonical_name_primitives() {
        assert_eq!(type_to_canonical_name(&Type::Int), "Int");
        assert_eq!(type_to_canonical_name(&Type::Bool), "Bool");
        assert_eq!(type_to_canonical_name(&Type::Unit), "Unit");
    }

    #[test]
    fn canonical_name_named() {
        assert_eq!(
            type_to_canonical_name(&Type::Named("Point".into(), vec![])),
            "Point"
        );
        assert_eq!(
            type_to_canonical_name(&Type::Named("Vec".into(), vec![Type::Int])),
            "Vec$Int"
        );
    }

    #[test]
    fn canonical_name_fn() {
        // () -> Int
        assert_eq!(
            type_to_canonical_name(&Type::Fn(vec![], Box::new(Type::Int))),
            "$Fun0$Int"
        );
        // (Int) -> Bool
        assert_eq!(
            type_to_canonical_name(&Type::Fn(vec![Type::Int], Box::new(Type::Bool))),
            "$Fun1$Int$Bool"
        );
    }

    #[test]
    fn canonical_name_vars_normalized_by_occurrence() {
        // (a) -> Int and (b) -> Int should produce the same name
        let ty_a = Type::Fn(vec![Type::Var(TypeVarId(5))], Box::new(Type::Int));
        let ty_b = Type::Fn(vec![Type::Var(TypeVarId(99))], Box::new(Type::Int));
        assert_eq!(type_to_canonical_name(&ty_a), "$Fun1$T0$Int");
        assert_eq!(type_to_canonical_name(&ty_a), type_to_canonical_name(&ty_b));
    }

    #[test]
    fn canonical_name_distinct_vars_no_collision() {
        // (a) -> a  vs  (a) -> b  must differ
        let same = Type::Fn(
            vec![Type::Var(TypeVarId(0))],
            Box::new(Type::Var(TypeVarId(0))),
        );
        let diff = Type::Fn(
            vec![Type::Var(TypeVarId(0))],
            Box::new(Type::Var(TypeVarId(1))),
        );
        assert_eq!(type_to_canonical_name(&same), "$Fun1$T0$T0");
        assert_eq!(type_to_canonical_name(&diff), "$Fun1$T0$T1");
        assert_ne!(type_to_canonical_name(&same), type_to_canonical_name(&diff));
    }

    #[test]
    fn canonical_name_different_concrete_returns_no_collision() {
        // (a) -> Int  vs  (a) -> Bool
        let ty_int = Type::Fn(vec![Type::Var(TypeVarId(0))], Box::new(Type::Int));
        let ty_bool = Type::Fn(vec![Type::Var(TypeVarId(0))], Box::new(Type::Bool));
        assert_ne!(type_to_canonical_name(&ty_int), type_to_canonical_name(&ty_bool));
    }

    #[test]
    fn canonical_name_fn_vs_named_no_collision() {
        // Fn([Int], Bool) -> "$Fun1$Int$Bool"
        // Named("Fun1", [Int, Bool]) -> "Fun1$Int$Bool"
        // The $ prefix on function types prevents collision with user type "Fun1"
        let fn_ty = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        let named_ty = Type::Named("Fun1".into(), vec![Type::Int, Type::Bool]);
        assert_ne!(type_to_canonical_name(&fn_ty), type_to_canonical_name(&named_ty));
    }

    #[test]
    fn canonical_name_jvm_safe() {
        // Parameterized fn type impl should produce JVM-safe identifiers (no spaces, parens, arrows)
        let ty = Type::Fn(vec![], Box::new(Type::Var(TypeVarId(42))));
        let name = type_to_canonical_name(&ty);
        assert!(!name.contains(' '), "canonical name must not contain spaces: {name}");
        assert!(!name.contains('('), "canonical name must not contain parens: {name}");
        assert!(!name.contains(')'), "canonical name must not contain parens: {name}");
        assert!(!name.contains('>'), "canonical name must not contain arrows: {name}");
        assert!(!name.contains('-'), "canonical name must not contain dashes: {name}");
    }

    #[test]
    fn head_type_name_basics() {
        assert_eq!(head_type_name(&Type::Int), "Int");
        assert_eq!(head_type_name(&Type::Named("Vec".into(), vec![Type::Int])), "Vec");
        assert_eq!(head_type_name(&Type::Fn(vec![], Box::new(Type::Int))), "$Fun0");
        assert_eq!(head_type_name(&Type::Fn(vec![Type::Int], Box::new(Type::Bool))), "$Fun1");
        assert_eq!(
            head_type_name(&Type::Own(Box::new(Type::Named("Foo".into(), vec![])))),
            "Foo"
        );
    }

    #[test]
    fn head_type_name_fn_no_collision_with_named() {
        // A user type "Fun1" must not collide with the head name for (a) -> b
        assert_ne!(
            head_type_name(&Type::Named("Fun1".into(), vec![])),
            head_type_name(&Type::Fn(vec![Type::Int], Box::new(Type::Bool))),
        );
    }

    #[test]
    fn format_with_var_map_simple() {
        let id = TypeVarId(5);
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Var(id)));
        let names: HashMap<TypeVarId, &str> = [(id, "b")].into_iter().collect();
        assert_eq!(format_type_with_var_map(&ty, &names), "(Int) -> b");
    }

    #[test]
    fn format_with_var_map_nested_fn() {
        let a = TypeVarId(10);
        let b = TypeVarId(11);
        let ty = Type::Fn(
            vec![Type::Var(a)],
            Box::new(Type::Fn(vec![Type::Var(b)], Box::new(Type::Int))),
        );
        let names: HashMap<TypeVarId, &str> = [(a, "x"), (b, "y")].into_iter().collect();
        assert_eq!(format_type_with_var_map(&ty, &names), "(x) -> (y) -> Int");
    }

    #[test]
    fn format_with_var_map_unmapped_fallback() {
        let id = TypeVarId(2); // display_name = "c"
        let ty = Type::Var(id);
        let names: HashMap<TypeVarId, &str> = HashMap::new();
        assert_eq!(format_type_with_var_map(&ty, &names), "c");
    }

    #[test]
    fn format_with_var_map_named_type() {
        let id = TypeVarId(7);
        let ty = Type::Named("Vec".to_string(), vec![Type::Var(id)]);
        let names: HashMap<TypeVarId, &str> = [(id, "a")].into_iter().collect();
        assert_eq!(format_type_with_var_map(&ty, &names), "Vec[a]");
    }
}
