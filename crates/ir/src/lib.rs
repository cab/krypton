pub mod expr;
pub mod lint;
pub mod lower;
pub mod pass;
pub mod pretty;

use std::collections::{BTreeSet, HashMap};

pub use expr::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SimpleExprKind, SwitchBranch};
use krypton_parser::ast::Span;
pub use krypton_typechecker::module_interface::{CanonicalRef, LocalSymbolKey, ModulePath};
pub use krypton_typechecker::typed_ast::TraitName;
pub use krypton_typechecker::types::TypeVarId;

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
    App(Box<Type>, Vec<Type>),
    Own(Box<Type>),
    Tuple(Vec<Type>),
    /// Trait dictionary. Only exists in IR — never in the typechecker.
    Dict {
        trait_name: TraitName,
        target: Box<Type>,
    },
    /// HKT sentinel (carried over from TC for bind_type_vars/decompose_fn_for_app).
    FnHole,
}

impl From<krypton_typechecker::types::Type> for Type {
    fn from(tc: krypton_typechecker::types::Type) -> Self {
        use krypton_typechecker::types::Type as TcType;
        match tc {
            TcType::Int => Type::Int,
            TcType::Float => Type::Float,
            TcType::Bool => Type::Bool,
            TcType::String => Type::String,
            TcType::Unit => Type::Unit,
            TcType::Fn(params, ret) => Type::Fn(
                params.into_iter().map(|(_, t)| t.into()).collect(),
                Box::new((*ret).into()),
            ),
            TcType::Var(id) => Type::Var(id),
            TcType::Named(n, args) => Type::Named(n, args.into_iter().map(Into::into).collect()),
            TcType::App(ctor, args) => Type::App(
                Box::new((*ctor).into()),
                args.into_iter().map(Into::into).collect(),
            ),
            TcType::Own(inner) => Type::Own(Box::new((*inner).into())),
            TcType::MaybeOwn(_, _) => {
                unreachable!("ICE: MaybeOwn leaked past qualifier resolution into IR lowering")
            }
            TcType::Tuple(elems) => Type::Tuple(elems.into_iter().map(Into::into).collect()),
            TcType::FnHole => Type::FnHole,
        }
    }
}

impl Module {
    /// How many "free" (non-captured) parameters a closure's underlying function has.
    pub fn closure_free_params(&self, func: FnId, capture_count: usize) -> usize {
        self.functions
            .iter()
            .find(|f| f.id == func)
            .map(|f| f.params.len().saturating_sub(capture_count))
            .unwrap_or(0)
    }

    // --- Backward-compat methods (T8/T9 will remove these) ---

    /// Get the bare name for a FnId.
    pub fn fn_name(&self, id: FnId) -> Option<&str> {
        self.fn_identities.get(&id).map(|fi| fi.name())
    }

    /// Reconstruct the old `fn_names: HashMap<FnId, String>` map.
    pub fn fn_names(&self) -> HashMap<FnId, String> {
        self.fn_identities
            .iter()
            .map(|(&id, fi)| (id, fi.name().to_string()))
            .collect()
    }

}

impl Type {
    /// Strip `Own` wrappers recursively, including inside `Named` type args.
    pub fn strip_own(&self) -> Type {
        match self {
            Type::Own(inner) => inner.strip_own(),
            Type::Named(name, args) => {
                Type::Named(name.clone(), args.iter().map(|a| a.strip_own()).collect())
            }
            Type::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|e| e.strip_own()).collect())
            }
            Type::Fn(params, ret) => {
                Type::Fn(
                    params.iter().map(|p| p.strip_own()).collect(),
                    Box::new(ret.strip_own()),
                )
            }
            other => other.clone(),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
            Type::Dict { trait_name, target } => write!(f, "Dict[{}, {}]", trait_name, target),
            Type::FnHole => write!(f, "_"),
        }
    }
}

/// Head type constructor name for parameterized instance dispatch.
pub fn head_type_name(ty: &Type) -> std::string::String {
    match ty {
        Type::Own(inner) => head_type_name(inner),
        Type::Named(name, _) => name.clone(),
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "Unit".to_string(),
        Type::Fn(params, _) => format!("$Fun{}", params.len()),
        Type::Dict { .. } => "Dict".to_string(),
        Type::Var(_) => "Object".to_string(),
        Type::Tuple(elems) => format!("$Tuple{}", elems.len()),
        Type::App(ctor, _) => head_type_name(ctor),
        other => unreachable!("unexpected type in head_type_name: {other:?}"),
    }
}

/// Full canonical type name matching `type_to_canonical_name` from the typechecker.
/// Includes all type arguments, producing unique names for concrete types like
/// `Vec$Int` (vs `Vec$String`). Type variables become `$Var0`, `$Var1`, etc.
pub fn canonical_type_name(ty: &Type) -> std::string::String {
    use std::collections::HashMap;
    fn inner(ty: &Type, var_map: &mut HashMap<TypeVarId, usize>) -> std::string::String {
        match ty {
            Type::Own(inner_ty) => inner(inner_ty, var_map),
            Type::Named(name, args) if args.is_empty() => name.clone(),
            Type::Named(name, args) => {
                let arg_strs: Vec<_> = args.iter().map(|a| inner(a, var_map)).collect();
                format!("{}${}", name, arg_strs.join("$"))
            }
            Type::Int => "Int".to_string(),
            Type::Float => "Float".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::String => "String".to_string(),
            Type::Unit => "Unit".to_string(),
            Type::Fn(params, ret) => {
                let mut parts: Vec<_> = params.iter().map(|p| inner(p, var_map)).collect();
                parts.push(inner(ret, var_map));
                format!("$Fun{}${}", params.len(), parts.join("$"))
            }
            Type::Var(id) => {
                let next = var_map.len();
                let idx = *var_map.entry(*id).or_insert(next);
                format!("$Var{idx}")
            }
            Type::Tuple(elems) => {
                let parts: Vec<_> = elems.iter().map(|e| inner(e, var_map)).collect();
                format!("$Tuple{}${}", elems.len(), parts.join("$"))
            }
            Type::App(ctor, args) => {
                let ctor_name = inner(ctor, var_map);
                let arg_strs: Vec<_> = args.iter().map(|a| inner(a, var_map)).collect();
                format!("{}${}", ctor_name, arg_strs.join("$"))
            }
            Type::FnHole => "$FnHole".to_string(),
            Type::Dict { .. } => "Dict".to_string(),
        }
    }
    let mut var_map = HashMap::new();
    inner(ty, &mut var_map)
}

/// Extract the type name from a CanonicalRef's symbol (for pretty-printing).
/// Returns a diagnostic fallback for non-Type symbols instead of panicking,
/// since this is used in Display impls where crashing hinders debugging.
pub fn canonical_ref_type_name(cref: &CanonicalRef) -> String {
    match &cref.symbol {
        LocalSymbolKey::Type(name) => name.clone(),
        other => format!("<non-type:{}>", other),
    }
}

/// Returns true if the type contains any type variables or HKT placeholders.
pub fn has_type_vars(ty: &Type) -> bool {
    match ty {
        Type::Var(_) | Type::FnHole => true,
        Type::Named(_, args) => args.iter().any(has_type_vars),
        Type::Fn(params, ret) => params.iter().any(has_type_vars) || has_type_vars(ret),
        Type::Own(inner) => has_type_vars(inner),
        Type::Tuple(elems) => elems.iter().any(has_type_vars),
        Type::App(ctor, args) => has_type_vars(ctor) || args.iter().any(has_type_vars),
        _ => false,
    }
}

/// Decompose a concrete `Fn` type into (partial_ctor, remaining_args) for matching
/// against `App(ctor, args)` in HKT contexts.
pub fn decompose_fn_for_app(
    params: &[Type],
    ret: &Type,
    applied_count: usize,
) -> Option<(Type, Vec<Type>)> {
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

/// Canonical name for a type, used for deduplication of parameterized instances.
/// Type variables are normalized to positional names ($Var0, $Var1, ...).
pub fn type_to_canonical_name(ty: &Type) -> String {
    use std::collections::HashMap;
    fn inner(ty: &Type, var_map: &mut HashMap<TypeVarId, usize>) -> String {
        match ty {
            Type::Int => "Int".to_string(),
            Type::Float => "Float".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::String => "String".to_string(),
            Type::Unit => "Unit".to_string(),
            Type::Named(name, args) if args.is_empty() => name.clone(),
            Type::Named(name, args) => {
                let arg_strs: Vec<String> = args.iter().map(|a| inner(a, var_map)).collect();
                format!("{}${}", name, arg_strs.join("$"))
            }
            Type::Fn(params, ret) => {
                let mut parts: Vec<String> = params.iter().map(|p| inner(p, var_map)).collect();
                parts.push(inner(ret, var_map));
                format!("$Fun{}${}", params.len(), parts.join("$"))
            }
            Type::Own(inner_ty) => inner(inner_ty, var_map),
            Type::Var(id) => {
                let next = var_map.len();
                let idx = *var_map.entry(*id).or_insert(next);
                format!("$Var{idx}")
            }
            Type::App(ctor, args) => {
                let mut parts = vec![inner(ctor, var_map)];
                for a in args {
                    parts.push(inner(a, var_map));
                }
                format!("$App${}", parts.join("$"))
            }
            Type::Tuple(elems) => {
                let parts: Vec<String> = elems.iter().map(|e| inner(e, var_map)).collect();
                format!("$Tuple${}", parts.join("$"))
            }
            Type::Dict { trait_name, target } => {
                format!("$Dict${}${}", trait_name, inner(target, var_map))
            }
            Type::FnHole => "$FnHole".to_string(),
        }
    }
    let mut var_map = HashMap::new();
    inner(ty, &mut var_map)
}

/// Structurally match a type pattern (may contain type vars) against a concrete type,
/// collecting variable bindings. Returns true if the pattern matches.
pub fn bind_type_vars(
    pattern: &Type,
    actual: &Type,
    bindings: &mut HashMap<TypeVarId, Type>,
) -> bool {
    match (pattern, actual) {
        (Type::Var(id), _) => match bindings.get(id) {
            Some(existing) => existing == actual,
            None => {
                bindings.insert(*id, actual.clone());
                true
            }
        },
        (Type::Named(p_name, p_args), Type::Named(a_name, a_args)) => {
            p_name == a_name
                && p_args.len() == a_args.len()
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        (Type::Fn(p_params, p_ret), Type::Fn(a_params, a_ret)) => {
            p_params.len() == a_params.len()
                && p_params
                    .iter()
                    .zip(a_params.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
                && bind_type_vars(p_ret, a_ret, bindings)
        }
        (Type::Tuple(p_elems), Type::Tuple(a_elems)) => {
            p_elems.len() == a_elems.len()
                && p_elems
                    .iter()
                    .zip(a_elems.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        (Type::Own(p), Type::Own(a)) => bind_type_vars(p, a, bindings),
        (Type::Own(p), a) => bind_type_vars(p, a, bindings),
        (a, Type::Own(p)) => bind_type_vars(a, p, bindings),
        (Type::App(p_ctor, p_args), Type::App(a_ctor, a_args)) => {
            bind_type_vars(p_ctor, a_ctor, bindings)
                && p_args.len() == a_args.len()
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        // HKT cross-arm: App(Var(f), [a]) vs Named("Box", [Int])
        (Type::App(p_ctor, p_args), Type::Named(a_name, a_args)) => {
            p_args.len() == a_args.len()
                && bind_type_vars(p_ctor, &Type::Named(a_name.clone(), Vec::new()), bindings)
                && p_args
                    .iter()
                    .zip(a_args.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        // HKT cross-arm: App(Var(f), [a]) vs Fn([Int], Int)
        (Type::App(p_ctor, p_args), Type::Fn(a_params, a_ret))
            if decompose_fn_for_app(a_params, a_ret, p_args.len()).is_some() =>
        {
            let (ctor_fn, remaining) = decompose_fn_for_app(a_params, a_ret, p_args.len()).unwrap();
            bind_type_vars(p_ctor, &ctor_fn, bindings)
                && remaining.len() == p_args.len()
                && p_args
                    .iter()
                    .zip(remaining.iter())
                    .all(|(p, a)| bind_type_vars(p, a, bindings))
        }
        _ => pattern == actual,
    }
}

/// Function names that are compiler intrinsics — they produce inline bytecode
/// rather than static method calls. Both the IR lowerer and JVM codegen reference
/// this list to ensure consistency.
pub const COMPILER_INTRINSICS: &[&str] = &["panic"];

/// Unique function identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FnId(pub u32);

/// Unique variable identifier. No shadowing exists in the IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

/// A resource binding that requires cleanup at function exit.
#[derive(Debug, Clone)]
pub struct FinallyClose {
    pub resource_var: VarId,
    pub type_name: String,
}

// ---------------------------------------------------------------------------
// Symbol-based identity types
// ---------------------------------------------------------------------------

/// Identity of a function known to the IR module.
#[derive(Debug, Clone)]
pub enum FnIdentity {
    /// Defined in this module.
    Local { name: String },
    /// Imported from another Krypton module.
    Imported {
        canonical: CanonicalRef,
        local_alias: String,
    },
    /// Extern FFI binding (Java/JS).
    Extern {
        canonical: CanonicalRef,
        target: ExternTarget,
        name: String,
    },
    /// Compiler intrinsic (panic).
    Intrinsic { name: String },
}

impl FnIdentity {
    /// The bare name used by codegen (binding name / alias).
    pub fn name(&self) -> &str {
        match self {
            FnIdentity::Local { name } => name,
            FnIdentity::Imported { local_alias, .. } => local_alias,
            FnIdentity::Extern { name, .. } => name,
            FnIdentity::Intrinsic { name } => name,
        }
    }
}

/// Variable with debug info.
#[derive(Debug, Clone)]
pub struct VarInfo {
    pub id: VarId,
    pub debug_name: Option<String>,
    pub ty: Type,
}

/// A flat collection of top-level definitions. All lambdas are lifted to
/// top-level functions.
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub structs: Vec<StructDef>,
    pub sum_types: Vec<SumTypeDef>,
    pub functions: Vec<FnDef>,
    /// FnId → identity for all known functions (local + extern + imported + intrinsic).
    pub fn_identities: HashMap<FnId, FnIdentity>,
    /// Extern FFI function bindings (Java/JS).
    pub extern_fns: Vec<ExternFnDef>,
    /// Extern type registrations (opaque types backed by host types).
    pub extern_types: Vec<ExternTypeDef>,
    /// Extern trait definitions (Java interfaces exposed as Krypton traits).
    pub extern_traits: Vec<ExternTraitDef>,
    /// Functions imported from other Krypton modules.
    pub imported_fns: Vec<ImportedFnDef>,
    /// Trait declarations (codegen metadata for dispatch infrastructure).
    pub traits: Vec<TraitDef>,
    /// Trait instance declarations (codegen metadata for dispatch infrastructure).
    pub instances: Vec<InstanceDef>,
    /// Set of tuple arities used in this module (for codegen class generation).
    pub tuple_arities: BTreeSet<usize>,
    /// Canonical module path.
    pub module_path: ModulePath,
    /// Function name → dict parameter requirements (trait_name, type_var_id).
    /// Populated from typechecker constraint requirements during lowering.
    pub fn_dict_requirements: HashMap<String, Vec<(TraitName, TypeVarId)>>,
    /// Function name → disposables that must be cleaned up at function exit.
    /// Target-neutral metadata: each backend decides enforcement mechanism
    /// (JVM: exception table finally handlers, JS: try/finally, etc.).
    ///
    /// Future: consider promoting to explicit IR unwind semantics (invoke/landingpad)
    /// rather than side metadata.
    pub fn_exit_closes: HashMap<String, Vec<FinallyClose>>,

}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub name: String,
    pub type_params: Vec<TypeVarId>,
    pub fields: Vec<(String, Type)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SumTypeDef {
    pub name: String,
    pub type_params: Vec<TypeVarId>,
    pub variants: Vec<VariantDef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantDef {
    pub name: String,
    pub tag: u32,
    pub fields: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct FnDef {
    pub id: FnId,
    pub name: String,
    pub params: Vec<(VarId, Type)>,
    pub return_type: Type,
    pub body: Expr,
}

/// Target-specific binding for extern declarations.
#[derive(Debug, Clone, PartialEq)]
pub enum ExternTarget {
    Java {
        class: String,
    },
    /// Not yet constructed — forward declaration for JS backend.
    Js {
        module: String,
    },
}

/// The kind of JVM invocation for an extern function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExternCallKind {
    Static,
    Instance,
    Constructor,
}

/// An extern FFI function binding (Java/JS).
#[derive(Debug, Clone)]
pub struct ExternFnDef {
    pub id: FnId,
    pub name: String,
    pub declaring_module_path: String,
    pub span: Span,
    pub target: ExternTarget,
    pub nullable: bool,
    pub throws: bool,
    pub call_kind: ExternCallKind,
    pub param_types: Vec<Type>,
    pub return_type: Type,
    /// Per-parameter bridge info: `Some(bridge)` when the parameter needs wrapping
    /// in a bridge class before passing to Java (extern trait constraint).
    pub bridge_params: Vec<Option<ExternTraitBridge>>,
}

/// An opaque extern type backed by a host type.
#[derive(Debug, Clone)]
pub struct ExternTypeDef {
    pub name: String,
    pub target: ExternTarget,
}

/// An extern trait definition — a Java interface exposed as a Krypton trait.
#[derive(Debug, Clone)]
pub struct ExternTraitDef {
    pub trait_name: TraitName,
    pub java_interface: String,
    pub methods: Vec<ExternTraitMethodDef>,
}

/// A method in an extern trait (for bridge class generation).
#[derive(Debug, Clone)]
pub struct ExternTraitMethodDef {
    pub name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// Info for wrapping a parameter in a bridge class before passing to Java.
#[derive(Debug, Clone)]
pub struct ExternTraitBridge {
    pub trait_name: TraitName,
    pub java_interface: String,
}

/// A function imported from another Krypton module.
#[derive(Debug, Clone)]
pub struct ImportedFnDef {
    pub id: FnId,
    pub name: String,
    pub source_module: String,
    pub original_name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// A trait declaration (codegen metadata — dictionary passing is already desugared).
#[derive(Debug, Clone)]
pub struct TraitDef {
    pub name: String,
    pub trait_name: TraitName,
    pub type_var: TypeVarId,
    pub methods: Vec<TraitMethodDef>,
    pub is_imported: bool,
}

/// A method signature within a trait declaration.
#[derive(Debug, Clone)]
pub struct TraitMethodDef {
    pub name: String,
    pub param_count: usize,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// A trait instance declaration linking method FnDefs to a trait/type pair.
#[derive(Debug, Clone)]
pub struct InstanceDef {
    pub trait_name: TraitName,
    pub target_type: Type,
    pub target_type_name: String,
    pub method_fn_ids: Vec<(String, FnId)>,
    pub sub_dict_requirements: Vec<(TraitName, TypeVarId)>,
    pub is_intrinsic: bool,
    pub is_imported: bool,
}

/// Struct definition from another module, needed for field access codegen.
#[derive(Debug, Clone)]
pub struct ImportedStructDef {
    pub name: String,
    pub module_path: String,
    pub type_params: Vec<TypeVarId>,
    pub fields: Vec<(String, Type)>,
}

/// Sum type definition from another module, needed for pattern match codegen.
#[derive(Debug, Clone)]
pub struct ImportedSumTypeDef {
    pub name: String,
    pub module_path: String,
    pub type_params: Vec<TypeVarId>,
    pub variants: Vec<VariantDef>,
}

/// Instance from another module, needed for cross-module dict dispatch.
#[derive(Debug, Clone)]
pub struct ImportedInstanceRef {
    pub source_module_path: String,
    pub trait_name: TraitName,
    pub target_type_name: String,
    pub target_type: Type,
    pub sub_dict_requirements: Vec<(TraitName, TypeVarId)>,
    pub is_intrinsic: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn expr(ty: Type, kind: ExprKind) -> Expr {
        Expr::new((0, 0), ty, kind)
    }

    fn simple(kind: SimpleExprKind) -> SimpleExpr {
        SimpleExpr::new((0, 0), kind)
    }

    #[test]
    fn var_id_is_copy_eq_hash() {
        let a = VarId(0);
        let b = a; // Copy
        assert_eq!(a, b); // Eq
        let mut set = HashSet::new();
        set.insert(a); // Hash
        assert!(set.contains(&b));
    }

    #[test]
    fn fn_id_is_copy_eq_hash() {
        let a = FnId(0);
        let b = a;
        assert_eq!(a, b);
        let mut set = HashSet::new();
        set.insert(a);
        assert!(set.contains(&b));
    }

    #[test]
    fn expr_shape_matches_spec() {
        // Construct an Atom expression
        let atom_expr = expr(Type::Int, ExprKind::Atom(Atom::Lit(Literal::Int(42))));

        // Construct a Let expression
        let let_expr = expr(
            Type::Int,
            ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: simple(SimpleExprKind::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                }),
                body: Box::new(atom_expr),
            },
        );

        assert!(matches!(let_expr.kind, ExprKind::Let { .. }));
    }

    #[test]
    fn simple_expr_variants() {
        let _call = simple(SimpleExprKind::Call {
            func: FnId(0),
            args: vec![Atom::Var(VarId(0))],
        });
        let _call_closure = simple(SimpleExprKind::CallClosure {
            closure: Atom::Var(VarId(1)),
            args: vec![],
        });
        let _make_closure = simple(SimpleExprKind::MakeClosure {
            func: FnId(1),
            captures: vec![Atom::Var(VarId(0))],
        });
        let _construct = simple(SimpleExprKind::Construct {
            type_ref: CanonicalRef {
                module: ModulePath::new("test"),
                symbol: LocalSymbolKey::Type("Point".into()),
            },
            fields: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
        });
        let _variant = simple(SimpleExprKind::ConstructVariant {
            type_ref: CanonicalRef {
                module: ModulePath::new("test"),
                symbol: LocalSymbolKey::Type("Option".into()),
            },
            variant: "Some".into(),
            tag: 0,
            fields: vec![Atom::Lit(Literal::Int(42))],
        });
        let _project = simple(SimpleExprKind::Project {
            value: Atom::Var(VarId(0)),
            field_index: 0,
        });
        let _tag = simple(SimpleExprKind::Tag {
            value: Atom::Var(VarId(0)),
        });
        let _tuple = simple(SimpleExprKind::MakeTuple {
            elements: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Bool(true))],
        });
        let _tuple_project = simple(SimpleExprKind::TupleProject {
            value: Atom::Var(VarId(0)),
            index: 0,
        });
        let _prim = simple(SimpleExprKind::PrimOp {
            op: PrimOp::ConcatString,
            args: vec![
                Atom::Lit(Literal::String("hello".into())),
                Atom::Lit(Literal::String(" world".into())),
            ],
        });
    }

    #[test]
    fn switch_and_join_points() {
        let body = expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit)));

        let _switch = ExprKind::Switch {
            scrutinee: Atom::Var(VarId(0)),
            branches: vec![SwitchBranch {
                tag: 0,
                bindings: vec![(VarId(1), Type::Int)],
                body: body.clone(),
            }],
            default: Some(Box::new(body.clone())),
        };

        let _join = ExprKind::LetJoin {
            name: VarId(10),
            params: vec![(VarId(11), Type::Int)],
            join_body: Box::new(body.clone()),
            body: Box::new(expr(
                Type::Unit,
                ExprKind::Jump {
                    target: VarId(10),
                    args: vec![Atom::Lit(Literal::Int(0))],
                },
            )),
            is_recur: false,
        };

        let _letrec = ExprKind::LetRec {
            bindings: vec![(
                VarId(20),
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                FnId(5),
                vec![],
            )],
            body: Box::new(body),
        };
    }

    #[test]
    fn strip_own_recurses_into_tuple() {
        let ty = Type::Tuple(vec![
            Type::Own(Box::new(Type::Int)),
            Type::Own(Box::new(Type::String)),
        ]);
        assert_eq!(ty.strip_own(), Type::Tuple(vec![Type::Int, Type::String]));
    }

    #[test]
    fn strip_own_recurses_into_fn() {
        let ty = Type::Fn(
            vec![Type::Own(Box::new(Type::Int))],
            Box::new(Type::Own(Box::new(Type::String))),
        );
        assert_eq!(
            ty.strip_own(),
            Type::Fn(vec![Type::Int], Box::new(Type::String))
        );
    }

    #[test]
    fn module_structure() {
        let _module = Module {
            name: "test".into(),
            fn_identities: HashMap::new(),
            structs: vec![StructDef {
                name: "Point".into(),
                type_params: vec![],
                fields: vec![("x".into(), Type::Int), ("y".into(), Type::Int)],
            }],
            sum_types: vec![SumTypeDef {
                name: "Option".into(),
                type_params: vec![],
                variants: vec![
                    VariantDef {
                        name: "Some".into(),
                        tag: 0,
                        fields: vec![Type::Int],
                    },
                    VariantDef {
                        name: "None".into(),
                        tag: 1,
                        fields: vec![],
                    },
                ],
            }],
            functions: vec![FnDef {
                id: FnId(0),
                name: "main".into(),
                params: vec![],
                return_type: Type::Unit,
                body: expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit))),
            }],
            extern_fns: vec![],
            extern_types: vec![],
            extern_traits: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: BTreeSet::new(),
            module_path: ModulePath::new("test"),
            fn_dict_requirements: HashMap::new(),
            fn_exit_closes: HashMap::new(),
        };
    }
}
