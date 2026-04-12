use std::collections::{HashMap, HashSet};
use std::fmt;

pub use krypton_parser::ast::ParamMode;

use crate::type_error::TypeError;
use crate::typed_ast::TraitName;

/// Type variable identifier (newtype wrapper for type safety).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(pub(crate) u32);

/// Qualifier variable identifier for deferred ownership resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct QualVarId(pub(crate) u32);

/// State of a qualifier variable during inference.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QualifierState {
    /// Not yet decided — may become Affine or Shared.
    Pending,
    /// Confirmed as owned (~T).
    Affine,
    /// Resolved as shared (plain T).
    Shared,
}

/// Token returned by `push_qual_scope`. Must be consumed by either
/// `commit_qual_scope` or `rollback_qual_scope`.
pub struct QualScopeSnapshot {
    next_qual_at_push: u32,
    depth: u32,
}

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
    Fn(Vec<(ParamMode, Type)>, Box<Type>),
    Var(TypeVarId),
    Named(std::string::String, Vec<Type>),
    /// Type constructor application where the constructor is a type variable.
    /// e.g., `f[a]` when `f` is a higher-kinded type variable.
    App(Box<Type>, Vec<Type>),
    Own(Box<Type>),
    /// Ownership-polymorphic wrapper: `shape T` resolves to `~T` if `T` (after
    /// substitution) transitively contains `Own`; otherwise resolves to plain `T`.
    /// Evaluation is deferred until substitution resolves the inner type.
    Shape(Box<Type>),
    /// Deferred ownership: either `~T` or `T` depending on qualifier resolution.
    /// Created when `~T` meets an unbound type variable in a bare (non-constructor) position.
    /// Resolved by `Substitution::apply` once the qualifier state is decided.
    MaybeOwn(QualVarId, Box<Type>),
    Tuple(Vec<Type>),
    /// Sentinel for unfilled return positions in partially-applied function type
    /// constructors. Used by HKT machinery — never appears in user-facing types.
    /// Consumed by `normalize_app` when applying type arguments.
    FnHole,
}

impl Type {
    /// Build a function type whose parameter slots are all consume-mode.
    /// Use this at internal construction sites that synthesize function types
    /// (HKT machinery, intrinsic registry, type registry, partial application,
    /// unification, etc.) — sites that legitimately produce a borrow slot must
    /// build the `Vec<(ParamMode, Type)>` explicitly.
    pub fn fn_consuming(params: Vec<Type>, ret: Type) -> Type {
        Type::Fn(
            params
                .into_iter()
                .map(|t| (ParamMode::Consume, t))
                .collect(),
            Box::new(ret),
        )
    }
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
            debug_assert_eq!(
                *hole,
                Type::FnHole,
                "normalize_app: expected FnHole sentinel in partial fn constructor"
            );
            Type::Fn(params, Box::new(args.into_iter().next().unwrap()))
        }
        Type::Fn(mut params, hole) => {
            debug_assert_eq!(
                *hole,
                Type::FnHole,
                "normalize_app: expected FnHole sentinel in partial fn constructor"
            );
            // Multiple holes: first args extend params (as consume slots), last becomes ret
            let ret = args.last().unwrap().clone();
            params.extend(
                args[..args.len() - 1]
                    .iter()
                    .cloned()
                    .map(|t| (ParamMode::Consume, t)),
            );
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
pub fn decompose_fn_for_app(
    params: &[(ParamMode, Type)],
    ret: &Type,
    applied_count: usize,
) -> Option<(Type, Vec<Type>)> {
    let total = params.len() + 1;
    if applied_count == 0 || applied_count > total {
        return None;
    }
    let ctor_count = total - applied_count;
    let ctor = Type::Fn(params[..ctor_count].to_vec(), Box::new(Type::FnHole));
    let mut remaining: Vec<Type> = params[ctor_count..]
        .iter()
        .map(|(_, t)| t.clone())
        .collect();
    remaining.push(ret.clone());
    Some((ctor, remaining))
}

/// Check if a type syntactically contains `Own` anywhere (no registry lookup).
fn type_contains_own_syntactic(ty: &Type) -> bool {
    match ty {
        Type::Own(_) => true,
        Type::Named(_, args) => args.iter().any(type_contains_own_syntactic),
        Type::Tuple(elems) => elems.iter().any(type_contains_own_syntactic),
        Type::Fn(params, ret) => {
            params
                .iter()
                .any(|(_, p)| type_contains_own_syntactic(p))
                || type_contains_own_syntactic(ret)
        }
        Type::App(ctor, args) => {
            type_contains_own_syntactic(ctor) || args.iter().any(type_contains_own_syntactic)
        }
        _ => false,
    }
}

/// Check if a type still contains unresolved type variables.
fn contains_unresolved_var(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Shape(inner) => contains_unresolved_var(inner),
        Type::Own(inner) => contains_unresolved_var(inner),
        Type::MaybeOwn(_, inner) => contains_unresolved_var(inner),
        Type::Named(_, args) | Type::App(_, args) => args.iter().any(contains_unresolved_var),
        Type::Tuple(elems) => elems.iter().any(contains_unresolved_var),
        Type::Fn(params, ret) => {
            params.iter().any(|(_, p)| contains_unresolved_var(p)) || contains_unresolved_var(ret)
        }
        _ => false,
    }
}

/// Check if a type is a compound type (Named with args, Tuple, Fn).
fn is_compound(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Named(_, args) if !args.is_empty()
    ) || matches!(ty, Type::Tuple(_) | Type::Fn(_, _))
}

/// Bottom-up lifting for compound type arguments that contain Own.
/// Walks into `Named(name, args)` and wraps each compound arg that contains Own.
fn lift_compounds(ty: Type) -> Type {
    match ty {
        Type::Named(name, args) => {
            let new_args: Vec<Type> = args
                .into_iter()
                .map(|a| {
                    let lifted = lift_compounds(a);
                    if is_compound(&lifted) && type_contains_own_syntactic(&lifted) {
                        match lifted {
                            Type::Own(_) => lifted,
                            _ => Type::Own(Box::new(lifted)),
                        }
                    } else {
                        lifted
                    }
                })
                .collect();
            Type::Named(name, new_args)
        }
        Type::Tuple(elems) => {
            Type::Tuple(elems.into_iter().map(lift_compounds).collect())
        }
        other => other,
    }
}

/// Evaluate `shape T`: if `T` (after substitution) contains `Own` transitively,
/// wrap in `~T`; otherwise return plain `T`. Compound type arguments are
/// individually lifted bottom-up before the outer check.
/// If `T` still contains unresolved type variables, keep the `Shape` wrapper.
fn evaluate_shape(ty: Type) -> Type {
    if contains_unresolved_var(&ty) {
        return Type::Shape(Box::new(ty));
    }
    let lifted = lift_compounds(ty);
    if type_contains_own_syntactic(&lifted) {
        match lifted {
            Type::Own(_) => lifted,
            _ => Type::Own(Box::new(lifted)),
        }
    } else {
        lifted
    }
}

impl Type {
    /// Re-letter type variables to sequential a, b, c, ... based on first-appearance order.
    /// Preserves identity: same original var → same new letter throughout.
    pub fn renumber_for_display(&self) -> Type {
        let mut mapping = HashMap::new();
        let mut next_id = 0u32;
        self.renumber_inner(&mut mapping, &mut next_id)
    }

    fn renumber_inner(
        &self,
        mapping: &mut HashMap<TypeVarId, TypeVarId>,
        next_id: &mut u32,
    ) -> Type {
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
                params
                    .iter()
                    .map(|(m, p)| (*m, p.renumber_inner(mapping, next_id)))
                    .collect(),
                Box::new(ret.renumber_inner(mapping, next_id)),
            ),
            Type::Named(n, args) => Type::Named(
                n.clone(),
                args.iter()
                    .map(|a| a.renumber_inner(mapping, next_id))
                    .collect(),
            ),
            Type::Own(inner) => Type::Own(Box::new(inner.renumber_inner(mapping, next_id))),
            Type::Shape(inner) => Type::Shape(Box::new(inner.renumber_inner(mapping, next_id))),
            Type::MaybeOwn(q, inner) => {
                Type::MaybeOwn(*q, Box::new(inner.renumber_inner(mapping, next_id)))
            }
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.renumber_inner(mapping, next_id))
                    .collect(),
            ),
            Type::App(ctor, args) => Type::App(
                Box::new(ctor.renumber_inner(mapping, next_id)),
                args.iter()
                    .map(|a| a.renumber_inner(mapping, next_id))
                    .collect(),
            ),
            other => other.clone(),
        }
    }

    /// Remap only vars present in the mapping; leave others unchanged.
    fn remap_vars(&self, mapping: &HashMap<TypeVarId, TypeVarId>) -> Type {
        match self {
            Type::Var(id) => Type::Var(*mapping.get(id).unwrap_or(id)),
            Type::Fn(params, ret) => Type::Fn(
                params
                    .iter()
                    .map(|(m, p)| (*m, p.remap_vars(mapping)))
                    .collect(),
                Box::new(ret.remap_vars(mapping)),
            ),
            Type::Named(n, args) => Type::Named(
                n.clone(),
                args.iter().map(|a| a.remap_vars(mapping)).collect(),
            ),
            Type::Own(inner) => Type::Own(Box::new(inner.remap_vars(mapping))),
            Type::Shape(inner) => Type::Shape(Box::new(inner.remap_vars(mapping))),
            Type::MaybeOwn(q, inner) => Type::MaybeOwn(*q, Box::new(inner.remap_vars(mapping))),
            Type::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|e| e.remap_vars(mapping)).collect())
            }
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
    types
        .iter()
        .map(|t| t.renumber_inner(&mut mapping, &mut next_id))
        .collect()
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
                for (i, (mode, p)) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    match (mode, p) {
                        (ParamMode::Borrow, Type::Own(inner)) => write!(f, "&~{}", inner)?,
                        (ParamMode::Borrow, _) => {
                            debug_assert!(false, "borrow slot must wrap an Own type, got {:?}", p);
                            write!(f, "&{}", p)?;
                        }
                        (ParamMode::ObservationalBorrow, _) => write!(f, "&{}", p)?,
                        (ParamMode::Consume, _) => write!(f, "{}", p)?,
                    }
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
            Type::Shape(inner) => write!(f, "shape {}", inner),
            Type::MaybeOwn(_, inner) => write!(f, "{}", inner),
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
    pub constraints: Vec<(TraitName, Vec<TypeVarId>)>,
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
            constraints: Vec::new(),
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
        let new_var_names = self
            .var_names
            .iter()
            .filter_map(|(old, name)| {
                mapping
                    .iter()
                    .find(|(o, _)| o == old)
                    .map(|(_, new)| (*new, name.clone()))
            })
            .collect();
        let new_constraints = self
            .constraints
            .iter()
            .map(|(trait_name, old_vars)| {
                let new_vars: Vec<TypeVarId> = old_vars
                    .iter()
                    .map(|old_var| {
                        mapping
                            .iter()
                            .find(|(o, _)| o == old_var)
                            .map(|(_, n)| *n)
                            .unwrap_or(*old_var)
                    })
                    .collect();
                (trait_name.clone(), new_vars)
            })
            .collect();
        (
            TypeScheme {
                vars: new_vars,
                constraints: new_constraints,
                ty: new_ty,
                var_names: new_var_names,
            },
            mapping,
        )
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
            let ps: Vec<String> = params
                .iter()
                .map(|(mode, p)| match (mode, p) {
                    (ParamMode::Borrow, Type::Own(inner)) => {
                        format!("&~{}", format_type_impl(inner, names))
                    }
                    (ParamMode::Borrow, _) => {
                        debug_assert!(false, "borrow slot must wrap an Own type, got {:?}", p);
                        format!("&{}", format_type_impl(p, names))
                    }
                    (ParamMode::ObservationalBorrow, _) => {
                        format!("&{}", format_type_impl(p, names))
                    }
                    (ParamMode::Consume, _) => format_type_impl(p, names),
                })
                .collect();
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
        Type::Shape(inner) => format!("shape {}", format_type_impl(inner, names)),
        Type::MaybeOwn(_, inner) => format_type_impl(inner, names),
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

/// Collect free type variables in left-to-right encounter order, deduplicated.
fn free_vars_ordered(ty: &Type) -> Vec<TypeVarId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    free_vars_ordered_into(ty, &mut out, &mut seen);
    out
}

/// Collect all type variables that appear inside a `Type::Shape(_)` wrapper,
/// in left-to-right encounter order, deduplicated across the whole type.
///
/// Used to identify the shape variables of a trait method signature so the
/// impl body can be dual-checked against every legal value form of each
/// shape parameter (see `typecheck_impl_methods`).
pub fn collect_shape_vars(ty: &Type) -> Vec<TypeVarId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    collect_shape_vars_into(ty, &mut out, &mut seen);
    out
}

fn collect_shape_vars_into(ty: &Type, out: &mut Vec<TypeVarId>, seen: &mut HashSet<TypeVarId>) {
    match ty {
        Type::Shape(inner) => {
            free_vars_ordered_into(inner, out, seen);
        }
        Type::Fn(params, ret) => {
            for (_, p) in params {
                collect_shape_vars_into(p, out, seen);
            }
            collect_shape_vars_into(ret, out, seen);
        }
        Type::Named(_, args) | Type::App(_, args) => {
            for a in args {
                collect_shape_vars_into(a, out, seen);
            }
        }
        Type::Tuple(elems) => {
            for e in elems {
                collect_shape_vars_into(e, out, seen);
            }
        }
        Type::Own(inner) | Type::MaybeOwn(_, inner) => {
            collect_shape_vars_into(inner, out, seen);
        }
        _ => {}
    }
}

fn free_vars_ordered_into(ty: &Type, out: &mut Vec<TypeVarId>, seen: &mut HashSet<TypeVarId>) {
    match ty {
        Type::Var(id) => {
            if seen.insert(*id) {
                out.push(*id);
            }
        }
        Type::Fn(params, ret) => {
            for (_, p) in params {
                free_vars_ordered_into(p, out, seen);
            }
            free_vars_ordered_into(ret, out, seen);
        }
        Type::Named(_, args) | Type::App(_, args) => {
            for a in args {
                free_vars_ordered_into(a, out, seen);
            }
        }
        Type::Tuple(elems) => {
            for e in elems {
                free_vars_ordered_into(e, out, seen);
            }
        }
        Type::Own(inner) => free_vars_ordered_into(inner, out, seen),
        Type::Shape(inner) => free_vars_ordered_into(inner, out, seen),
        Type::MaybeOwn(_, inner) => free_vars_ordered_into(inner, out, seen),
        _ => {}
    }
}

/// Format a type for error messages, renumbering type variables to nice names.
/// Uses declared names from `var_names` where available, sequential letters otherwise.
pub fn format_type_for_error(ty: &Type, var_names: &HashMap<TypeVarId, String>) -> String {
    let vars = free_vars_ordered(ty);
    if vars.is_empty() {
        return format!("{ty}");
    }

    // Renumber vars to sequential 0, 1, 2, ...
    let mut id_mapping = HashMap::new();
    for (i, &v) in vars.iter().enumerate() {
        id_mapping.insert(v, TypeVarId(i as u32));
    }
    let renamed_ty = ty.remap_vars(&id_mapping);

    // Build display names (same logic as TypeScheme::display_var_names)
    let mut used: HashSet<String> = HashSet::new();
    let mut names = Vec::new();
    let mut letter_idx = 0u32;
    for &v in &vars {
        if let Some(user_name) = var_names.get(&v) {
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

    format_type_with_var_names(&renamed_ty, &names)
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
            write!(f, ". {}", format_type_with_var_names(&renamed_ty, &names))?;
            if !self.constraints.is_empty() {
                // Build id → sequential index mapping (same as display_var_names)
                let id_mapping: HashMap<TypeVarId, usize> =
                    self.vars.iter().enumerate().map(|(i, &v)| (v, i)).collect();
                let mut where_parts: Vec<String> = Vec::new();
                for (trait_name, vars) in &self.constraints {
                    let var_names: Vec<String> = vars
                        .iter()
                        .map(|var| {
                            id_mapping
                                .get(var)
                                .map(|&i| names[i].clone())
                                .unwrap_or_else(|| format!("?{}", var.0))
                        })
                        .collect();
                    if var_names.len() == 1 {
                        where_parts.push(format!("{}: {}", var_names[0], trait_name.local_name));
                    } else {
                        where_parts.push(format!(
                            "{}[{}]",
                            trait_name.local_name,
                            var_names.join(", ")
                        ));
                    }
                }
                write!(f, " where {}", where_parts.join(", "))?;
            }
            Ok(())
        }
    }
}

/// A substitution mapping type variables to types, extended with qualifier
/// variables for deferred ownership resolution.
#[derive(Debug, Clone)]
pub struct Substitution {
    map: HashMap<TypeVarId, Type>,
    /// Qualifier variable states (Pending, Affine, or Shared).
    qualifiers: HashMap<QualVarId, QualifierState>,
    /// Union-find for qualifier unification: child → parent.
    qualifier_aliases: HashMap<QualVarId, QualVarId>,
    /// Scope depth at which each qualifier was created.
    qualifier_scope_depth: HashMap<QualVarId, u32>,
    /// Counter for fresh qualifier variable IDs.
    next_qual: u32,
    /// Current qualifier scope nesting depth.
    current_scope_depth: u32,
}

impl Default for Substitution {
    fn default() -> Self {
        Self::new()
    }
}

impl Substitution {
    pub fn new() -> Self {
        Substitution {
            map: HashMap::new(),
            qualifiers: HashMap::new(),
            qualifier_aliases: HashMap::new(),
            qualifier_scope_depth: HashMap::new(),
            next_qual: 0,
            current_scope_depth: 0,
        }
    }

    /// Create a substitution with a single binding.
    pub fn bind(var: TypeVarId, ty: Type) -> Self {
        let mut s = Self::new();
        s.map.insert(var, ty);
        s
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
                    .map(|(m, p)| (*m, self.apply_inner(p, visiting, chain)))
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
            Type::Own(inner) => {
                let resolved_inner = self.apply_inner(inner, visiting, chain);
                match &resolved_inner {
                    Type::Own(_) => resolved_inner, // collapse Own(Own(T))
                    _ => Type::Own(Box::new(resolved_inner)),
                }
            }
            Type::Shape(inner) => {
                let resolved_inner = self.apply_inner(inner, visiting, chain);
                evaluate_shape(resolved_inner)
            }
            Type::MaybeOwn(q, inner) => {
                let resolved_q = self.resolve_qual(*q);
                let resolved_inner = self.apply_inner(inner, visiting, chain);
                match self.qualifiers.get(&resolved_q) {
                    Some(QualifierState::Affine) => {
                        match &resolved_inner {
                            Type::Own(_) => resolved_inner, // collapse Own(Own(T))
                            _ => Type::Own(Box::new(resolved_inner)),
                        }
                    }
                    Some(QualifierState::Shared) => resolved_inner,
                    _ => Type::MaybeOwn(resolved_q, Box::new(resolved_inner)),
                }
            }
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
            constraints: scheme.constraints.clone(),
            ty: restricted.apply(&scheme.ty),
            var_names: scheme.var_names.clone(),
        }
    }

    /// Compose two substitutions: applying the result is equivalent to applying
    /// `other` first, then `self`.
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result_map = HashMap::new();
        // Apply self to each binding in other
        for (&var, ty) in &other.map {
            result_map.insert(var, self.apply(ty));
        }
        // Add bindings from self that aren't in other
        for (&var, ty) in &self.map {
            result_map.entry(var).or_insert_with(|| ty.clone());
        }
        // Merge qualifier maps: self takes precedence
        let mut qualifiers = other.qualifiers.clone();
        for (&q, state) in &self.qualifiers {
            qualifiers.insert(q, state.clone());
        }
        let mut qualifier_aliases = other.qualifier_aliases.clone();
        qualifier_aliases.extend(self.qualifier_aliases.iter());
        let mut qualifier_scope_depth = other.qualifier_scope_depth.clone();
        qualifier_scope_depth.extend(self.qualifier_scope_depth.iter());
        Substitution {
            map: result_map,
            qualifiers,
            qualifier_aliases,
            qualifier_scope_depth,
            next_qual: self.next_qual.max(other.next_qual),
            current_scope_depth: self.current_scope_depth.max(other.current_scope_depth),
        }
    }

    /// Look up a variable in the substitution.
    pub fn get(&self, var: TypeVarId) -> Option<&Type> {
        self.map.get(&var)
    }

    /// Insert a binding into the substitution.
    pub fn insert(&mut self, var: TypeVarId, ty: Type) {
        self.map.insert(var, ty);
    }

    /// Merge all type-variable bindings from `other` into `self`.
    pub fn merge_type_bindings(&mut self, other: Substitution) {
        self.map.extend(other.map);
    }

    // ── Qualifier variable methods ──────────────────────────────────────

    /// Create a fresh qualifier variable at the current scope depth.
    pub fn fresh_qual(&mut self) -> QualVarId {
        let id = QualVarId(self.next_qual);
        self.next_qual += 1;
        self.qualifiers.insert(id, QualifierState::Pending);
        self.qualifier_scope_depth
            .insert(id, self.current_scope_depth);
        id
    }

    /// Follow alias chain to root qualifier.
    pub fn resolve_qual(&self, q: QualVarId) -> QualVarId {
        let mut current = q;
        while let Some(&next) = self.qualifier_aliases.get(&current) {
            current = next;
        }
        current
    }

    /// Get qualifier state, following aliases.
    pub fn get_qualifier(&self, q: QualVarId) -> Option<&QualifierState> {
        self.qualifiers.get(&self.resolve_qual(q))
    }

    /// Confirm qualifier as Affine if still Pending. Returns error if already Shared.
    pub fn confirm_affine(&mut self, q: QualVarId) -> Result<(), TypeError> {
        let root = self.resolve_qual(q);
        match self.qualifiers.get(&root) {
            Some(QualifierState::Pending) | None => {
                self.qualifiers.insert(root, QualifierState::Affine);
                Ok(())
            }
            Some(QualifierState::Affine) => Ok(()),
            Some(QualifierState::Shared) => Err(TypeError::QualifierConflict {
                existing: "shared".into(),
                incoming: "owned".into(),
            }),
        }
    }

    /// Alias two qualifiers. Root keeps minimum (outermost) scope depth.
    /// Propagates decided state. Returns error on Shared+Affine conflict.
    pub fn unify_qualifiers(&mut self, q1: QualVarId, q2: QualVarId) -> Result<(), TypeError> {
        let r1 = self.resolve_qual(q1);
        let r2 = self.resolve_qual(q2);
        if r1 == r2 {
            return Ok(());
        }

        let s1 = self.qualifiers.get(&r1).cloned();
        let s2 = self.qualifiers.get(&r2).cloned();

        // Detect conflicts
        match (&s1, &s2) {
            (Some(QualifierState::Affine), Some(QualifierState::Shared)) => {
                return Err(TypeError::QualifierConflict {
                    existing: "owned".into(),
                    incoming: "shared".into(),
                });
            }
            (Some(QualifierState::Shared), Some(QualifierState::Affine)) => {
                return Err(TypeError::QualifierConflict {
                    existing: "shared".into(),
                    incoming: "owned".into(),
                });
            }
            _ => {}
        }

        // Choose root: prefer the one that's decided (Affine or Shared), else r1
        let (root, child) = match (&s1, &s2) {
            (_, Some(QualifierState::Affine)) | (_, Some(QualifierState::Shared)) => (r2, r1),
            (Some(QualifierState::Affine), _) | (Some(QualifierState::Shared), _) => (r1, r2),
            _ => (r1, r2),
        };
        self.qualifier_aliases.insert(child, root);

        // Root keeps minimum scope depth (outermost scope)
        let d1 = self.qualifier_scope_depth.get(&r1).copied().unwrap_or(0);
        let d2 = self.qualifier_scope_depth.get(&r2).copied().unwrap_or(0);
        self.qualifier_scope_depth.insert(root, d1.min(d2));
        Ok(())
    }

    /// Push a qualifier scope, returning a snapshot token for commit/rollback.
    pub fn push_qual_scope(&mut self) -> QualScopeSnapshot {
        self.current_scope_depth += 1;
        QualScopeSnapshot {
            next_qual_at_push: self.next_qual,
            depth: self.current_scope_depth,
        }
    }

    /// Commit a qualifier scope: default all Pending qualifiers at this
    /// scope depth to Shared, then decrement depth.
    pub fn commit_qual_scope(&mut self, snap: QualScopeSnapshot) {
        debug_assert_eq!(self.current_scope_depth, snap.depth);
        let depth = self.current_scope_depth;
        let to_resolve: Vec<QualVarId> = self
            .qualifiers
            .keys()
            .copied()
            .filter(|q| {
                let root = self.resolve_qual(*q);
                root == *q // only process roots
                    && matches!(self.qualifiers.get(&root), Some(QualifierState::Pending))
                    && self
                        .qualifier_scope_depth
                        .get(&root)
                        .copied()
                        .unwrap_or(0)
                        == depth
            })
            .collect();
        for q in to_resolve {
            self.qualifiers.insert(q, QualifierState::Shared);
        }
        self.current_scope_depth -= 1;
    }

    /// Rollback a qualifier scope: remove all qualifier state created since
    /// the snapshot, then decrement depth.
    pub fn rollback_qual_scope(&mut self, snap: QualScopeSnapshot) {
        debug_assert_eq!(self.current_scope_depth, snap.depth);
        let cutoff = snap.next_qual_at_push;
        self.qualifiers.retain(|q, _| q.0 < cutoff);
        self.qualifier_scope_depth.retain(|q, _| q.0 < cutoff);
        self.qualifier_aliases
            .retain(|child, parent| child.0 < cutoff && parent.0 < cutoff);
        self.next_qual = cutoff;
        self.current_scope_depth -= 1;
    }

    /// Force a qualifier to Shared. Returns error if already Affine.
    pub fn force_shared(&mut self, q: QualVarId) -> Result<(), TypeError> {
        let root = self.resolve_qual(q);
        match self.qualifiers.get(&root) {
            Some(QualifierState::Pending) | None => {
                self.qualifiers.insert(root, QualifierState::Shared);
                Ok(())
            }
            Some(QualifierState::Shared) => Ok(()),
            Some(QualifierState::Affine) => Err(TypeError::QualifierConflict {
                existing: "owned".into(),
                incoming: "shared".into(),
            }),
        }
    }

    /// Read-only access to the qualifier map (for resolve_maybe_own helper).
    pub fn qualifiers_ref(&self) -> &HashMap<QualVarId, QualifierState> {
        &self.qualifiers
    }

    /// Current qualifier scope depth (for debugging).
    pub fn current_scope_depth(&self) -> u32 {
        self.current_scope_depth
    }

}

/// Span of a function definition, optionally in a different source module.
#[derive(Debug, Clone)]
pub struct DefSpan {
    pub span: krypton_parser::ast::Span,
    pub source_module: Option<String>, // None = same file
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BindingQualifiedName {
    pub module_path: String,
    pub local_name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstructorBindingKind {
    Record,
    Variant,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindingSource {
    LocalValue,
    TopLevelLocalFunction {
        qualified_name: BindingQualifiedName,
    },
    ImportedFunction {
        qualified_name: BindingQualifiedName,
        is_prelude: bool,
    },
    Constructor {
        type_qualified_name: BindingQualifiedName,
        constructor_name: String,
        kind: ConstructorBindingKind,
    },
    TraitMethod {
        trait_module_path: String,
        trait_name: String,
        method_name: String,
        is_prelude: bool,
    },
    IntrinsicFunction {
        name: String,
    },
}

#[derive(Debug, Clone)]
pub struct OverloadCandidate {
    pub scheme: TypeScheme,
    pub source: BindingSource,
}

#[derive(Debug, Clone)]
pub struct EnvEntry {
    pub scheme: TypeScheme,
    pub source: BindingSource,
    pub overload_candidates: Option<Vec<OverloadCandidate>>,
}

impl EnvEntry {
    /// Add an overload candidate. On first call, initializes the Vec with the
    /// original entry plus the new candidate. On subsequent calls, appends.
    pub fn add_overload_candidate(&mut self, scheme: TypeScheme, source: BindingSource) {
        let candidates = self.overload_candidates.get_or_insert_with(|| {
            vec![OverloadCandidate {
                scheme: self.scheme.clone(),
                source: self.source.clone(),
            }]
        });
        candidates.push(OverloadCandidate { scheme, source });
    }
}

/// Scoped type environment for variable lookups.
#[derive(Debug, Clone)]
pub struct TypeEnv {
    scopes: Vec<HashMap<std::string::String, EnvEntry>>,
    pub fn_return_type: Option<Type>,
    def_spans: HashMap<std::string::String, DefSpan>,
}

impl TypeEnv {
    /// Create a new environment with one empty scope.
    pub fn new() -> Self {
        TypeEnv {
            scopes: vec![HashMap::new()],
            fn_return_type: None,
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

    /// Bind a name in the current (top) scope with explicit source metadata.
    pub fn bind_with_source(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        source: BindingSource,
    ) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name, EnvEntry { scheme, source, overload_candidates: None });
        }
    }

    /// Bind a name in the current (top) scope.
    pub fn bind(&mut self, name: std::string::String, scheme: TypeScheme) {
        self.bind_with_source(name, scheme, BindingSource::LocalValue);
    }

    pub fn bind_top_level_function(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        module_path: String,
        original_name: String,
    ) {
        self.bind_with_source(
            name,
            scheme,
            BindingSource::TopLevelLocalFunction {
                qualified_name: BindingQualifiedName {
                    module_path,
                    local_name: original_name,
                },
            },
        );
    }

    pub fn bind_imported_function(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        module_path: String,
        original_name: String,
        is_prelude: bool,
    ) {
        self.bind_with_source(
            name,
            scheme,
            BindingSource::ImportedFunction {
                qualified_name: BindingQualifiedName {
                    module_path,
                    local_name: original_name,
                },
                is_prelude,
            },
        );
    }

    pub fn bind_constructor(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        type_module_path: String,
        type_name: String,
        constructor_name: String,
        kind: ConstructorBindingKind,
    ) {
        self.bind_with_source(
            name,
            scheme,
            BindingSource::Constructor {
                type_qualified_name: BindingQualifiedName {
                    module_path: type_module_path,
                    local_name: type_name,
                },
                constructor_name,
                kind,
            },
        );
    }

    pub fn bind_trait_method(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        trait_module_path: String,
        trait_name: String,
        method_name: String,
        is_prelude: bool,
    ) {
        self.bind_with_source(
            name,
            scheme,
            BindingSource::TraitMethod {
                trait_module_path,
                trait_name,
                method_name,
                is_prelude,
            },
        );
    }

    pub fn bind_intrinsic_function(&mut self, name: std::string::String, scheme: TypeScheme) {
        self.bind_with_source(
            name.clone(),
            scheme,
            BindingSource::IntrinsicFunction { name },
        );
    }

    /// Look up a name, searching from the top scope down.
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        self.lookup_entry(name).map(|entry| &entry.scheme)
    }

    /// Look up a name with source metadata, searching from the top scope down.
    pub fn lookup_entry(&self, name: &str) -> Option<&EnvEntry> {
        for scope in self.scopes.iter().rev() {
            if let Some(entry) = scope.get(name) {
                return Some(entry);
            }
        }
        None
    }

    pub fn lookup_entry_mut(&mut self, name: &str) -> Option<&mut EnvEntry> {
        for scope in self.scopes.iter_mut().rev() {
            if let Some(entry) = scope.get_mut(name) {
                return Some(entry);
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

    /// Bind a name with explicit source metadata and record its definition span.
    pub fn bind_with_source_and_def_span(
        &mut self,
        name: std::string::String,
        scheme: TypeScheme,
        source: BindingSource,
        def_span: DefSpan,
    ) {
        self.bind_with_source(name.clone(), scheme, source);
        self.def_spans.insert(name, def_span);
    }

    pub fn set_def_span(&mut self, name: std::string::String, def_span: DefSpan) {
        self.def_spans.insert(name, def_span);
    }

    /// Get the definition span for a binding, if any.
    pub fn get_def_span(&self, name: &str) -> Option<&DefSpan> {
        self.def_spans.get(name)
    }

    /// Return the names and types bound in the top (current) scope.
    pub fn top_scope_bindings(&self) -> Vec<(std::string::String, Type)> {
        self.scopes
            .last()
            .map(|scope| {
                let mut bindings: Vec<_> = scope
                    .iter()
                    .map(|(name, entry)| (name.clone(), entry.scheme.ty.clone()))
                    .collect();
                bindings.sort_by(|a, b| a.0.cmp(&b.0));
                bindings
            })
            .unwrap_or_default()
    }

    /// Iterate over all type schemes in the environment.
    pub fn for_each_scheme(&self, mut f: impl FnMut(&TypeScheme)) {
        for scope in &self.scopes {
            for entry in scope.values() {
                f(&entry.scheme);
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
    /// Strip `Own` and `MaybeOwn` wrappers recursively, including inside `Named` type args.
    pub fn strip_own(&self) -> Type {
        match self {
            Type::Own(inner) => inner.strip_own(),
            Type::Shape(inner) => inner.strip_own(),
            Type::MaybeOwn(_, inner) => inner.strip_own(),
            Type::Named(name, args) => {
                Type::Named(name.clone(), args.iter().map(|a| a.strip_own()).collect())
            }
            other => other.clone(),
        }
    }

    /// Returns true if this type (or any nested type) contains a MaybeOwn node.
    pub fn contains_maybe_own(&self) -> bool {
        match self {
            Type::MaybeOwn(_, _) => true,
            Type::Own(inner) => inner.contains_maybe_own(),
            Type::Shape(inner) => inner.contains_maybe_own(),
            Type::Fn(params, ret) => {
                params.iter().any(|(_, p)| p.contains_maybe_own()) || ret.contains_maybe_own()
            }
            Type::Named(_, args) | Type::App(_, args) => {
                args.iter().any(|a| a.contains_maybe_own())
            }
            Type::Tuple(elems) => elems.iter().any(|e| e.contains_maybe_own()),
            _ => false,
        }
    }
}

/// Head type constructor name for parameterized instance dispatch.
/// Returns the outermost constructor as a unique identifier.
pub fn head_type_name(ty: &Type) -> String {
    match ty {
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => head_type_name(inner),
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
            let arg_strs: Vec<String> = args
                .iter()
                .map(|a| canonical_name_inner(a, var_map))
                .collect();
            format!("{}${}", name, arg_strs.join("$"))
        }
        Type::Fn(params, ret) => {
            let mut parts: Vec<String> = params
                .iter()
                .map(|(_, p)| canonical_name_inner(p, var_map))
                .collect();
            parts.push(canonical_name_inner(ret, var_map));
            format!("$Fun{}${}", params.len(), parts.join("$"))
        }
        Type::Tuple(elems) => {
            let elem_strs: Vec<String> = elems
                .iter()
                .map(|e| canonical_name_inner(e, var_map))
                .collect();
            format!("$Tuple{}${}", elems.len(), elem_strs.join("$"))
        }
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            canonical_name_inner(inner, var_map)
        }
        Type::Var(id) => {
            let next = var_map.len();
            let idx = *var_map.entry(*id).or_insert(next);
            format!("$Var{idx}")
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
            type_to_canonical_name(&Type::fn_consuming(vec![], Type::Int)),
            "$Fun0$Int"
        );
        // (Int) -> Bool
        assert_eq!(
            type_to_canonical_name(&Type::fn_consuming(vec![Type::Int], Type::Bool)),
            "$Fun1$Int$Bool"
        );
    }

    #[test]
    fn canonical_name_vars_normalized_by_occurrence() {
        // (a) -> Int and (b) -> Int should produce the same name
        let ty_a = Type::fn_consuming(vec![Type::Var(TypeVarId(5))], Type::Int);
        let ty_b = Type::fn_consuming(vec![Type::Var(TypeVarId(99))], Type::Int);
        assert_eq!(type_to_canonical_name(&ty_a), "$Fun1$$Var0$Int");
        assert_eq!(type_to_canonical_name(&ty_a), type_to_canonical_name(&ty_b));
    }

    #[test]
    fn canonical_name_distinct_vars_no_collision() {
        // (a) -> a  vs  (a) -> b  must differ
        let same = Type::fn_consuming(vec![Type::Var(TypeVarId(0))], Type::Var(TypeVarId(0)));
        let diff = Type::fn_consuming(vec![Type::Var(TypeVarId(0))], Type::Var(TypeVarId(1)));
        assert_eq!(type_to_canonical_name(&same), "$Fun1$$Var0$$Var0");
        assert_eq!(type_to_canonical_name(&diff), "$Fun1$$Var0$$Var1");
        assert_ne!(type_to_canonical_name(&same), type_to_canonical_name(&diff));
    }

    #[test]
    fn canonical_name_different_concrete_returns_no_collision() {
        // (a) -> Int  vs  (a) -> Bool
        let ty_int = Type::fn_consuming(vec![Type::Var(TypeVarId(0))], Type::Int);
        let ty_bool = Type::fn_consuming(vec![Type::Var(TypeVarId(0))], Type::Bool);
        assert_ne!(
            type_to_canonical_name(&ty_int),
            type_to_canonical_name(&ty_bool)
        );
    }

    #[test]
    fn canonical_name_fn_vs_named_no_collision() {
        // Fn([Int], Bool) -> "$Fun1$Int$Bool"
        // Named("Fun1", [Int, Bool]) -> "Fun1$Int$Bool"
        // The $ prefix on function types prevents collision with user type "Fun1"
        let fn_ty = Type::fn_consuming(vec![Type::Int], Type::Bool);
        let named_ty = Type::Named("Fun1".into(), vec![Type::Int, Type::Bool]);
        assert_ne!(
            type_to_canonical_name(&fn_ty),
            type_to_canonical_name(&named_ty)
        );
    }

    #[test]
    fn canonical_name_jvm_safe() {
        // Parameterized fn type impl should produce JVM-safe identifiers (no spaces, parens, arrows)
        let ty = Type::fn_consuming(vec![], Type::Var(TypeVarId(42)));
        let name = type_to_canonical_name(&ty);
        assert!(
            !name.contains(' '),
            "canonical name must not contain spaces: {name}"
        );
        assert!(
            !name.contains('('),
            "canonical name must not contain parens: {name}"
        );
        assert!(
            !name.contains(')'),
            "canonical name must not contain parens: {name}"
        );
        assert!(
            !name.contains('>'),
            "canonical name must not contain arrows: {name}"
        );
        assert!(
            !name.contains('-'),
            "canonical name must not contain dashes: {name}"
        );
    }

    #[test]
    fn head_type_name_basics() {
        assert_eq!(head_type_name(&Type::Int), "Int");
        assert_eq!(
            head_type_name(&Type::Named("Vec".into(), vec![Type::Int])),
            "Vec"
        );
        assert_eq!(
            head_type_name(&Type::fn_consuming(vec![], Type::Int)),
            "$Fun0"
        );
        assert_eq!(
            head_type_name(&Type::fn_consuming(vec![Type::Int], Type::Bool)),
            "$Fun1"
        );
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
            head_type_name(&Type::fn_consuming(vec![Type::Int], Type::Bool)),
        );
    }

    #[test]
    fn format_with_var_map_simple() {
        let id = TypeVarId(5);
        let ty = Type::fn_consuming(vec![Type::Int], Type::Var(id));
        let names: HashMap<TypeVarId, &str> = [(id, "b")].into_iter().collect();
        assert_eq!(format_type_with_var_map(&ty, &names), "(Int) -> b");
    }

    #[test]
    fn format_with_var_map_nested_fn() {
        let a = TypeVarId(10);
        let b = TypeVarId(11);
        let ty = Type::fn_consuming(
            vec![Type::Var(a)],
            Type::fn_consuming(vec![Type::Var(b)], Type::Int),
        );
        let names: HashMap<TypeVarId, &str> = [(a, "x"), (b, "y")].into_iter().collect();
        assert_eq!(format_type_with_var_map(&ty, &names), "(x) -> (y) -> Int");
    }

    #[test]
    fn type_fn_carries_param_modes() {
        let file_t = Type::Named("File".into(), vec![]);
        let ty = Type::Fn(
            vec![
                (ParamMode::Borrow, Type::Own(Box::new(file_t.clone()))),
                (ParamMode::Consume, Type::Int),
            ],
            Box::new(Type::Unit),
        );
        match &ty {
            Type::Fn(params, ret) => {
                assert_eq!(params.len(), 2);
                assert_eq!(params[0].0, ParamMode::Borrow);
                assert_eq!(params[1].0, ParamMode::Consume);
                assert_eq!(**ret, Type::Unit);
            }
            _ => panic!("expected Type::Fn"),
        }
        assert_eq!(format!("{}", ty), "(&~File, Int) -> Unit");
    }

    #[test]
    fn type_fn_consuming_helper_default() {
        let ty = Type::fn_consuming(vec![Type::Int, Type::Bool], Type::Unit);
        match &ty {
            Type::Fn(params, _) => {
                assert!(params.iter().all(|(m, _)| *m == ParamMode::Consume));
                assert_eq!(params.len(), 2);
            }
            _ => panic!("expected Type::Fn"),
        }
    }

    #[test]
    fn type_fn_display_borrow_slot() {
        let file_t = Type::Named("File".into(), vec![]);
        // Single borrow slot
        let borrow = Type::Fn(
            vec![(ParamMode::Borrow, Type::Own(Box::new(file_t.clone())))],
            Box::new(Type::Unit),
        );
        assert_eq!(format!("{}", borrow), "(&~File) -> Unit");
        // Single consume slot — asymmetric, no `&`
        let consume = Type::Fn(
            vec![(ParamMode::Consume, Type::Own(Box::new(file_t)))],
            Box::new(Type::Unit),
        );
        assert_eq!(format!("{}", consume), "(~File) -> Unit");
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
