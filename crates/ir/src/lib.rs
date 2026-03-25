pub mod expr;
pub mod lint;
pub mod lower;
pub mod pass;
pub mod pretty;

use std::collections::{BTreeSet, HashMap};

pub use expr::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SwitchBranch};
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
    Dict { trait_name: TraitName, target: Box<Type> },
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
                params.into_iter().map(Into::into).collect(),
                Box::new((*ret).into()),
            ),
            TcType::Var(id) => Type::Var(id),
            TcType::Named(n, args) => Type::Named(n, args.into_iter().map(Into::into).collect()),
            TcType::App(ctor, args) => Type::App(
                Box::new((*ctor).into()),
                args.into_iter().map(Into::into).collect(),
            ),
            TcType::Own(inner) => Type::Own(Box::new((*inner).into())),
            TcType::Tuple(elems) => Type::Tuple(elems.into_iter().map(Into::into).collect()),
            TcType::FnHole => Type::FnHole,
        }
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
                    if i > 0 { write!(f, ", ")?; }
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
                        if i > 0 { write!(f, ", ")?; }
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
                        if i > 0 { write!(f, ", ")?; }
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
                    if i > 0 { write!(f, ", ")?; }
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

/// Decompose a concrete `Fn` type into (partial_ctor, remaining_args) for matching
/// against `App(ctor, args)` in HKT contexts.
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

/// Function names that are compiler intrinsics — they produce inline bytecode
/// rather than static method calls. Both the IR lowerer and JVM codegen reference
/// this list to ensure consistency.
pub const COMPILER_INTRINSICS: &[&str] = &["panic", "is_null", "trait_dict"];

/// Unique function identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FnId(pub u32);

/// Unique variable identifier. No shadowing exists in the IR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

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
    /// FnId → debug name for all known functions (local + extern + imported).
    pub fn_names: HashMap<FnId, String>,
    /// Extern FFI function bindings (Java/JS).
    pub extern_fns: Vec<ExternFnDef>,
    /// Extern type registrations (opaque types backed by host types).
    pub extern_types: Vec<ExternTypeDef>,
    /// Functions imported from other Krypton modules.
    pub imported_fns: Vec<ImportedFnDef>,
    /// Trait declarations (codegen metadata for dispatch infrastructure).
    pub traits: Vec<TraitDef>,
    /// Trait instance declarations (codegen metadata for dispatch infrastructure).
    pub instances: Vec<InstanceDef>,
    /// Set of tuple arities used in this module (for codegen class generation).
    pub tuple_arities: BTreeSet<usize>,
    /// Module path for qualified type names (empty for root module).
    pub module_path: String,
    /// Function name → dict parameter requirements (trait_name, type_var_id).
    /// Populated from typechecker constraint requirements during lowering.
    pub fn_dict_requirements: HashMap<String, Vec<(TraitName, TypeVarId)>>,
    /// FnId → (trait_name, method_name) for trait method calls.
    /// Allows codegen to distinguish trait method calls from regular static calls.
    pub trait_method_fn_ids: HashMap<FnId, (TraitName, String)>,
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
    Java { class: String },
    /// Not yet constructed — forward declaration for JS backend.
    Js { module: String },
}

/// An extern FFI function binding (Java/JS).
#[derive(Debug, Clone)]
pub struct ExternFnDef {
    pub id: FnId,
    pub name: String,
    pub target: ExternTarget,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// An opaque extern type backed by a host type.
#[derive(Debug, Clone)]
pub struct ExternTypeDef {
    pub name: String,
    pub target: ExternTarget,
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

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
        let atom_expr = Expr {
            kind: ExprKind::Atom(Atom::Lit(Literal::Int(42))),
            ty: Type::Int,
        };

        // Construct a Let expression
        let let_expr = Expr {
            kind: ExprKind::Let {
                bind: VarId(0),
                ty: Type::Int,
                value: SimpleExpr::PrimOp {
                    op: PrimOp::AddInt,
                    args: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
                },
                body: Box::new(atom_expr),
            },
            ty: Type::Int,
        };

        assert!(matches!(let_expr.kind, ExprKind::Let { .. }));
    }

    #[test]
    fn simple_expr_variants() {
        let _call = SimpleExpr::Call {
            func: FnId(0),
            args: vec![Atom::Var(VarId(0))],
        };
        let _call_closure = SimpleExpr::CallClosure {
            closure: Atom::Var(VarId(1)),
            args: vec![],
        };
        let _make_closure = SimpleExpr::MakeClosure {
            func: FnId(1),
            captures: vec![Atom::Var(VarId(0))],
        };
        let _construct = SimpleExpr::Construct {
            type_name: "Point".into(),
            fields: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Int(2))],
        };
        let _variant = SimpleExpr::ConstructVariant {
            type_name: "Option".into(),
            variant: "Some".into(),
            tag: 0,
            fields: vec![Atom::Lit(Literal::Int(42))],
        };
        let _project = SimpleExpr::Project {
            value: Atom::Var(VarId(0)),
            field_index: 0,
        };
        let _tag = SimpleExpr::Tag {
            value: Atom::Var(VarId(0)),
        };
        let _tuple = SimpleExpr::MakeTuple {
            elements: vec![Atom::Lit(Literal::Int(1)), Atom::Lit(Literal::Bool(true))],
        };
        let _tuple_project = SimpleExpr::TupleProject {
            value: Atom::Var(VarId(0)),
            index: 0,
        };
        let _prim = SimpleExpr::PrimOp {
            op: PrimOp::ConcatString,
            args: vec![
                Atom::Lit(Literal::String("hello".into())),
                Atom::Lit(Literal::String(" world".into())),
            ],
        };
    }

    #[test]
    fn switch_and_join_points() {
        let body = Expr {
            kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
            ty: Type::Unit,
        };

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
            body: Box::new(Expr {
                kind: ExprKind::Jump {
                    target: VarId(10),
                    args: vec![Atom::Lit(Literal::Int(0))],
                },
                ty: Type::Unit,
            }),
            is_recur: false,
        };

        let _letrec = ExprKind::LetRec {
            bindings: vec![(VarId(20), Type::Fn(vec![Type::Int], Box::new(Type::Int)), FnId(5), vec![])],
            body: Box::new(body),
        };
    }

    #[test]
    fn module_structure() {
        let _module = Module {
            name: "test".into(),
            fn_names: HashMap::new(),
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
                body: Expr {
                    kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                    ty: Type::Unit,
                },
            }],
            extern_fns: vec![],
            extern_types: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: BTreeSet::new(),
            module_path: String::new(),
            fn_dict_requirements: HashMap::new(),
            trait_method_fn_ids: HashMap::new(),
        };
    }
}
