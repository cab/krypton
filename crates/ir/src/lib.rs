pub mod expr;
pub mod lint;
pub mod lower;
pub mod pass;
pub mod pretty;

use std::collections::{BTreeSet, HashMap};

pub use expr::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExpr, SwitchBranch};
pub use krypton_typechecker::types::{Type, TypeVarId};

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
    /// Module path for qualified type names (None for main module).
    pub module_path: Option<String>,
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
    pub trait_name: String,
    pub target_type: Type,
    pub target_type_name: String,
    pub method_fn_ids: Vec<(String, FnId)>,
    pub sub_dict_requirements: Vec<(String, TypeVarId)>,
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
            module_path: None,
        };
    }
}
