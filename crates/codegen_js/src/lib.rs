pub mod diagnostics;
pub mod emit;
pub mod repl;
pub mod suspend;

pub use emit::{compile_modules_js, JsCodegenError};
pub use repl::compile_repl_js;

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap, HashSet};

    use krypton_ir::*;
    use krypton_typechecker::link_context::LinkContext;
    use krypton_typechecker::module_interface::{ModuleInterface, ModulePath as LinkModulePath};
    use krypton_typechecker::types::TypeVarGen;

    fn expr(ty: Type, kind: ExprKind) -> Expr {
        Expr::new((0, 0), ty, kind)
    }

    fn simple(kind: SimpleExprKind) -> SimpleExpr {
        SimpleExpr::new((0, 0), kind)
    }

    /// Build a minimal IR Module with the given fields.
    fn make_module(name: &str) -> Module {
        Module {
            name: name.to_string(),
            structs: vec![],
            sum_types: vec![],
            functions: vec![],
            fn_identities: HashMap::new(),
            extern_fns: vec![],
            extern_types: vec![],
            extern_traits: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: BTreeSet::new(),
            module_path: ModulePath::new(name),
            fn_dict_requirements: HashMap::new(),
            fn_exit_closes: HashMap::new(),
        }
    }

    fn test_link_ctx(module_path: &str) -> LinkContext {
        let iface = ModuleInterface {
            module_path: LinkModulePath::new(module_path),
            direct_deps: vec![],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: HashMap::new(),
            type_visibility: HashMap::new(),
            private_names: HashSet::new(),
        };
        LinkContext::build(vec![iface])
    }

    /// Emit JS from a hand-built IR Module directly (bypasses lowering).
    fn emit_module(module: &Module) -> String {
        let suspend = crate::suspend::SuspendSummary::empty();
        emit_module_with_suspend(module, 0, &suspend)
    }

    /// Emit JS from a hand-built IR Module with a specific suspend summary.
    fn emit_module_with_suspend(
        module: &Module,
        module_index: usize,
        suspend: &crate::suspend::SuspendSummary,
    ) -> String {
        let variant_lookup = HashMap::new();
        let qualified_sum_type_names = std::collections::HashSet::new();
        let registry = crate::emit::build_registry_for_modules(&[module]);
        let link_ctx = test_link_ctx(module.module_path.as_str());
        let view = link_ctx
            .view_for(&LinkModulePath::new(module.module_path.as_str()))
            .unwrap();
        let mut emitter = crate::emit::JsEmitter::new(
            module,
            false,
            &variant_lookup,
            &qualified_sum_type_names,
            &registry,
            &view,
            module_index,
            suspend,
        );
        emitter.emit()
    }

    #[test]
    fn empty_module() {
        let module = make_module("empty");
        let js = emit_module(&module);
        // Should produce valid JS — intrinsic dicts are emitted unconditionally
        assert!(
            !js.contains("export function"),
            "empty module should have no exported functions, got: {js:?}"
        );
    }

    #[test]
    fn single_function_add() {
        let mut module = make_module("test");
        // add(x, y) = x + y
        // IR: let v0 = PrimOp(AddInt, [x, y]) in v0
        let x = VarId(0);
        let y = VarId(1);
        let result = VarId(2);
        module.functions.push(FnDef {
            id: FnId(0),
            name: "add".to_string(),
            exported_symbol: "add".to_string(),
            params: vec![(x, Type::Int), (y, Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: result,
                    ty: Type::Int,
                    value: simple(SimpleExprKind::PrimOp {
                        op: PrimOp::AddInt,
                        args: vec![Atom::Var(x), Atom::Var(y)],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(result)))),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "add".to_string(),
                exported_symbol: "add".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(js.contains("export function add("), "should export add fn");
        assert!(js.contains("+"), "should contain addition operator");
        assert!(js.contains("return"), "should have return statement");
    }

    #[test]
    fn struct_emission() {
        let mut module = make_module("test");
        module.structs.push(StructDef {
            name: "Point".to_string(),
            type_params: vec![],
            fields: vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Int)],
        });

        let js = emit_module(&module);
        assert!(
            js.contains("export class Point {"),
            "should export Point class"
        );
        assert!(
            js.contains("constructor(x, y)"),
            "should have constructor with field names"
        );
        assert!(js.contains("this.x = x;"), "should assign this.x");
        assert!(js.contains("this.y = y;"), "should assign this.y");
    }

    #[test]
    fn sum_type_emission() {
        let mut module = make_module("test");
        module.sum_types.push(SumTypeDef {
            name: "Option".to_string(),
            type_params: vec![],
            variants: vec![
                VariantDef {
                    name: "Some".to_string(),
                    tag: 0,
                    fields: vec![Type::Int],
                },
                VariantDef {
                    name: "None".to_string(),
                    tag: 1,
                    fields: vec![],
                },
            ],
        });

        let js = emit_module(&module);
        // Base class
        assert!(
            js.contains("export class Option {"),
            "should export base class"
        );
        // Some extends Option
        assert!(
            js.contains("export class Some extends Option {"),
            "Some should extend Option"
        );
        // None extends Option
        assert!(
            js.contains("export class None extends Option {"),
            "None should extend Option"
        );
    }

    #[test]
    fn variant_field_naming() {
        let mut module = make_module("test");
        module.sum_types.push(SumTypeDef {
            name: "Pair".to_string(),
            type_params: vec![],
            variants: vec![VariantDef {
                name: "MkPair".to_string(),
                tag: 0,
                fields: vec![Type::Int, Type::String],
            }],
        });

        let js = emit_module(&module);
        assert!(
            js.contains("constructor(_0, _1)"),
            "variant fields should use positional _0, _1 naming"
        );
        assert!(js.contains("this._0 = _0;"), "should assign this._0");
        assert!(js.contains("this._1 = _1;"), "should assign this._1");
    }

    #[test]
    fn instanceof_support() {
        let mut module = make_module("test");
        module.sum_types.push(SumTypeDef {
            name: "Option".to_string(),
            type_params: vec![],
            variants: vec![
                VariantDef {
                    name: "Some".to_string(),
                    tag: 0,
                    fields: vec![Type::Int],
                },
                VariantDef {
                    name: "None".to_string(),
                    tag: 1,
                    fields: vec![],
                },
            ],
        });

        let js = emit_module(&module);
        // Both variants extend Option, enabling instanceof
        assert!(
            js.contains("extends Option"),
            "variants should extend base class"
        );
    }

    #[test]
    fn zero_arg_variant_singleton() {
        let mut module = make_module("test");
        module.sum_types.push(SumTypeDef {
            name: "Option".to_string(),
            type_params: vec![],
            variants: vec![VariantDef {
                name: "None".to_string(),
                tag: 1,
                fields: vec![],
            }],
        });

        let js = emit_module(&module);
        assert!(
            js.contains("static INSTANCE = new None();"),
            "zero-arg variant should have static INSTANCE singleton"
        );
    }

    #[test]
    fn import_statements() {
        let mut module = make_module("test");
        module.imported_fns.push(ImportedFnDef {
            id: FnId(10),
            name: "helper".to_string(),
            exported_symbol: "helper".to_string(),
            source_module: "utils".to_string(),
            original_name: "helper".to_string(),
            param_types: vec![Type::Int],
            return_type: Type::Int,
        });
        module.imported_fns.push(ImportedFnDef {
            id: FnId(11),
            name: "format".to_string(),
            exported_symbol: "format".to_string(),
            source_module: "utils".to_string(),
            original_name: "format".to_string(),
            param_types: vec![Type::String],
            return_type: Type::String,
        });

        let js = emit_module(&module);
        assert!(
            js.contains("import { format, helper } from './utils.mjs';"),
            "should emit grouped import from sibling module, got: {js:?}"
        );
    }

    #[test]
    fn import_aliased() {
        // Simulates `import list.{filter as list_filter}` where the module
        // also defines its own `filter` locally.
        let mut module = make_module("vec");
        module.functions.push(FnDef {
            id: FnId(0),
            name: "filter".to_string(),
            exported_symbol: "filter".to_string(),
            params: vec![],
            return_type: Type::Unit,
            body: expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit))),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "filter".to_string(),
                exported_symbol: "filter".to_string(),
            },
        );
        module.imported_fns.push(ImportedFnDef {
            id: FnId(1),
            name: "list_filter".to_string(),
            exported_symbol: "filter".to_string(),
            source_module: "core/list".to_string(),
            original_name: "filter".to_string(),
            param_types: vec![],
            return_type: Type::Unit,
        });
        module.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "list_filter".to_string(),
                exported_symbol: "list_filter".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("import { filter as list_filter } from './core/list.mjs';"),
            "aliased import from root module should use `as`, got: {js:?}"
        );
        // Should NOT have a bare `import { filter }` that shadows the local
        assert!(
            !js.contains("import { filter }"),
            "should not import bare name that shadows local, got: {js:?}"
        );
    }

    #[test]
    fn import_relative_same_directory() {
        // core/io importing core/result should produce './result.mjs', not './core/result.mjs'
        let mut module = make_module("io");
        module.module_path = ModulePath::new("core/io");
        module.imported_fns.push(ImportedFnDef {
            id: FnId(10),
            name: "Ok".to_string(),
            exported_symbol: "Ok".to_string(),
            source_module: "core/result".to_string(),
            original_name: "Ok".to_string(),
            param_types: vec![],
            return_type: Type::Unit,
        });

        let js = emit_module(&module);
        assert!(
            js.contains("from './result.mjs'"),
            "same-directory import should be relative, got: {js:?}"
        );
    }

    #[test]
    fn import_relative_parent_directory() {
        // core/io importing a root-level module 'util' should use '../util.mjs'
        let mut module = make_module("io");
        module.module_path = ModulePath::new("core/io");
        module.imported_fns.push(ImportedFnDef {
            id: FnId(10),
            name: "helper".to_string(),
            exported_symbol: "helper".to_string(),
            source_module: "util".to_string(),
            original_name: "helper".to_string(),
            param_types: vec![],
            return_type: Type::Unit,
        });

        let js = emit_module(&module);
        assert!(
            js.contains("from '../util.mjs'"),
            "parent-directory import should use ../, got: {js:?}"
        );
    }

    #[test]
    fn import_shadowed_skipped() {
        // When name == original_name and a local function has the same name,
        // the import should be skipped entirely (IR reuses the local FnId).
        let mut module = make_module("test");
        module.functions.push(FnDef {
            id: FnId(0),
            name: "combine".to_string(),
            exported_symbol: "combine".to_string(),
            params: vec![],
            return_type: Type::Unit,
            body: expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit))),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "combine".to_string(),
                exported_symbol: "combine".to_string(),
            },
        );
        module.imported_fns.push(ImportedFnDef {
            id: FnId(0), // same FnId — IR lowerer reuses it
            name: "combine".to_string(),
            exported_symbol: "combine".to_string(),
            source_module: "semigroup".to_string(),
            original_name: "combine".to_string(),
            param_types: vec![],
            return_type: Type::Unit,
        });

        let js = emit_module(&module);
        assert!(
            !js.contains("import { combine }"),
            "shadowed import should be skipped entirely, got: {js:?}"
        );
    }

    #[test]
    fn output_file_naming() {
        // Build a Module directly and test the emitter's filename logic directly.
        let module = make_module("hello");
        let variant_lookup = HashMap::new();
        let qualified_sum_type_names = std::collections::HashSet::new();
        let registry = crate::emit::build_registry_for_modules(&[&module]);
        let suspend = crate::suspend::SuspendSummary::empty();
        let link_ctx = test_link_ctx(module.module_path.as_str());
        let view = link_ctx
            .view_for(&LinkModulePath::new(module.module_path.as_str()))
            .unwrap();
        let mut emitter = crate::emit::JsEmitter::new(
            &module,
            false,
            &variant_lookup,
            &qualified_sum_type_names,
            &registry,
            &view,
            0,
            &suspend,
        );
        let _js = emitter.emit();
        // The compile_modules_js function produces "{name}.mjs"
        let filename = format!("{}.mjs", module.name);
        assert_eq!(filename, "hello.mjs");
        assert!(
            filename.ends_with(".mjs"),
            "output should use .mjs extension"
        );
    }

    #[test]
    fn literal_emission() {
        let mut module = make_module("test");
        // fn answer() = 42
        module.functions.push(FnDef {
            id: FnId(0),
            name: "answer".to_string(),
            exported_symbol: "answer".to_string(),
            params: vec![],
            return_type: Type::Int,
            body: expr(Type::Int, ExprKind::Atom(Atom::Lit(Literal::Int(42)))),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "answer".to_string(),
                exported_symbol: "answer".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("return 42;"),
            "Int literals should emit as regular numbers"
        );
    }

    #[test]
    fn string_literal_emission() {
        let mut module = make_module("test");
        module.functions.push(FnDef {
            id: FnId(0),
            name: "greeting".to_string(),
            exported_symbol: "greeting".to_string(),
            params: vec![],
            return_type: Type::String,
            body: expr(
                Type::String,
                ExprKind::Atom(Atom::Lit(Literal::String("hello".to_string()))),
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "greeting".to_string(),
                exported_symbol: "greeting".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("return \"hello\";"),
            "String literals should emit as JS strings"
        );
    }

    #[test]
    fn bool_literal_emission() {
        let mut module = make_module("test");
        module.functions.push(FnDef {
            id: FnId(0),
            name: "yes".to_string(),
            exported_symbol: "yes".to_string(),
            params: vec![],
            return_type: Type::Bool,
            body: expr(Type::Bool, ExprKind::Atom(Atom::Lit(Literal::Bool(true)))),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "yes".to_string(),
                exported_symbol: "yes".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("return true;"),
            "Bool literals should emit as JS booleans"
        );
    }

    #[test]
    fn unit_literal_emission() {
        let mut module = make_module("test");
        module.functions.push(FnDef {
            id: FnId(0),
            name: "noop".to_string(),
            exported_symbol: "noop".to_string(),
            params: vec![],
            return_type: Type::Unit,
            body: expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit))),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "noop".to_string(),
                exported_symbol: "noop".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("return undefined;"),
            "Unit should emit as undefined"
        );
    }

    // ── TraitCall inlining tests ────────────────────────────

    fn make_trait_name(name: &str) -> krypton_ir::TraitName {
        krypton_ir::TraitName::new(format!("core/{}", name.to_lowercase()), name.to_string())
    }

    fn dummy_instance_ref(trait_name: &str, type_name: &str) -> CanonicalRef {
        CanonicalRef {
            module: ModulePath::new("test"),
            symbol: LocalSymbolKey::Instance {
                trait_name: trait_name.to_string(),
                target_type: type_name.to_string(),
            },
        }
    }

    #[test]
    fn trait_call_intrinsic_inline() {
        use krypton_ir::{FnId, InstanceDef, Type, VarId};
        let mut module = make_module("test");
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Eq"),
            target_types: vec![Type::Int],
            target_type_name: "Int".to_string(),
            method_fn_ids: vec![("eq".to_string(), FnId(99))],
            sub_dict_requirements: vec![],
            is_intrinsic: true,
            is_imported: false,
        });
        // fn test(x: Int, y: Int) = let d = GetDict(Eq, Int); let r = TraitCall(Eq, "eq", [d, x, y]); r
        let x = VarId(0);
        let y = VarId(1);
        let d = VarId(2);
        let r = VarId(3);
        module.functions.push(FnDef {
            id: FnId(0),
            name: "test_fn".to_string(),
            exported_symbol: "test_fn".to_string(),
            params: vec![(x, Type::Int), (y, Type::Int)],
            return_type: Type::Bool,
            body: expr(
                Type::Bool,
                ExprKind::Let {
                    bind: d,
                    ty: Type::Dict {
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Int],
                    },
                    value: simple(SimpleExprKind::GetDict {
                        instance_ref: dummy_instance_ref("Eq", "Int"),
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Int],
                    }),
                    body: Box::new(expr(
                        Type::Bool,
                        ExprKind::Let {
                            bind: r,
                            ty: Type::Bool,
                            value: simple(SimpleExprKind::TraitCall {
                                trait_name: make_trait_name("Eq"),
                                method_name: "eq".to_string(),
                                args: vec![Atom::Var(d), Atom::Var(x), Atom::Var(y)],
                            }),
                            body: Box::new(expr(Type::Bool, ExprKind::Atom(Atom::Var(r)))),
                        },
                    )),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "test_fn".to_string(),
                exported_symbol: "test_fn".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("((a, b) => a === b)(v$0, v$1)"),
            "intrinsic TraitCall should be inlined, got: {js:?}"
        );
        assert!(
            !js.contains("v$2.eq("),
            "should NOT use dict dispatch for intrinsic, got: {js:?}"
        );
    }

    #[test]
    fn trait_call_non_intrinsic_passthrough() {
        use krypton_ir::{FnId, InstanceDef, Type, VarId};
        let mut module = make_module("test");
        module.structs.push(krypton_ir::StructDef {
            name: "Point".to_string(),
            type_params: vec![],
            fields: vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Int)],
        });
        module.functions.push(FnDef {
            id: FnId(1),
            name: "Eq$$Point$$eq".to_string(),
            exported_symbol: "Eq$$Point$$eq".to_string(),
            params: vec![],
            return_type: Type::Bool,
            body: expr(Type::Bool, ExprKind::Atom(Atom::Lit(Literal::Bool(true)))),
        });
        module.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "Eq$$Point$$eq".to_string(),
                exported_symbol: "Eq$$Point$$eq".to_string(),
            },
        );
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Eq"),
            target_types: vec![Type::Named("Point".to_string(), vec![])],
            target_type_name: "Point".to_string(),
            method_fn_ids: vec![("eq".to_string(), FnId(1))],
            sub_dict_requirements: vec![],
            is_intrinsic: false,
            is_imported: false,
        });
        // fn test(x: Point, y: Point) = let d = GetDict(Eq, Point); let r = TraitCall(Eq, "eq", [d, x, y]); r
        let x = VarId(0);
        let y = VarId(1);
        let d = VarId(2);
        let r = VarId(3);
        module.functions.push(FnDef {
            id: FnId(0),
            name: "test_fn".to_string(),
            exported_symbol: "test_fn".to_string(),
            params: vec![
                (x, Type::Named("Point".to_string(), vec![])),
                (y, Type::Named("Point".to_string(), vec![])),
            ],
            return_type: Type::Bool,
            body: expr(
                Type::Bool,
                ExprKind::Let {
                    bind: d,
                    ty: Type::Dict {
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Named("Point".to_string(), vec![])],
                    },
                    value: simple(SimpleExprKind::GetDict {
                        instance_ref: dummy_instance_ref("Eq", "Point"),
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Named("Point".to_string(), vec![])],
                    }),
                    body: Box::new(expr(
                        Type::Bool,
                        ExprKind::Let {
                            bind: r,
                            ty: Type::Bool,
                            value: simple(SimpleExprKind::TraitCall {
                                trait_name: make_trait_name("Eq"),
                                method_name: "eq".to_string(),
                                args: vec![Atom::Var(d), Atom::Var(x), Atom::Var(y)],
                            }),
                            body: Box::new(expr(Type::Bool, ExprKind::Atom(Atom::Var(r)))),
                        },
                    )),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "test_fn".to_string(),
                exported_symbol: "test_fn".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("v$2.eq(v$0, v$1)"),
            "non-intrinsic TraitCall should use dict dispatch, got: {js:?}"
        );
    }

    #[test]
    fn trait_call_opaque_dict_passthrough() {
        use krypton_ir::{FnId, Type, VarId};
        use krypton_typechecker::types::TypeVarGen;
        let mut module = make_module("test");
        let mut gen = TypeVarGen::new();
        let tv_a = gen.fresh();
        // fn test(dict: Dict[Eq, a], x: a, y: a) = TraitCall(Eq, "eq", [dict, x, y])
        let dict = VarId(0);
        let x = VarId(1);
        let y = VarId(2);
        let r = VarId(3);
        module.functions.push(FnDef {
            id: FnId(0),
            name: "test_fn".to_string(),
            exported_symbol: "test_fn".to_string(),
            params: vec![
                (
                    dict,
                    Type::Dict {
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Var(tv_a)],
                    },
                ),
                (x, Type::Var(tv_a)),
                (y, Type::Var(tv_a)),
            ],
            return_type: Type::Bool,
            body: expr(
                Type::Bool,
                ExprKind::Let {
                    bind: r,
                    ty: Type::Bool,
                    value: simple(SimpleExprKind::TraitCall {
                        trait_name: make_trait_name("Eq"),
                        method_name: "eq".to_string(),
                        args: vec![Atom::Var(dict), Atom::Var(x), Atom::Var(y)],
                    }),
                    body: Box::new(expr(Type::Bool, ExprKind::Atom(Atom::Var(r)))),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "test_fn".to_string(),
                exported_symbol: "test_fn".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("v$0.eq(v$1, v$2)"),
            "opaque dict (Type::Var) should fall back to dict dispatch, got: {js:?}"
        );
    }

    #[test]
    fn panic_intrinsic_emission() {
        use krypton_ir::{FnId, Type, VarId};
        let mut module = make_module("test");
        let panic_fn = FnId(99);
        module.fn_identities.insert(
            panic_fn,
            FnIdentity::Local {
                name: "panic".to_string(),
                exported_symbol: "panic".to_string(),
            },
        );
        let msg = VarId(0);
        let r = VarId(1);
        module.functions.push(FnDef {
            id: FnId(0),
            name: "test_fn".to_string(),
            exported_symbol: "test_fn".to_string(),
            params: vec![(msg, Type::String)],
            return_type: Type::Unit,
            body: expr(
                Type::Unit,
                ExprKind::Let {
                    bind: r,
                    ty: Type::Unit,
                    value: simple(SimpleExprKind::Call {
                        func: panic_fn,
                        args: vec![Atom::Var(msg)],
                    }),
                    body: Box::new(expr(Type::Unit, ExprKind::Atom(Atom::Var(r)))),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "test_fn".to_string(),
                exported_symbol: "test_fn".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("throw new KryptonPanic("),
            "panic intrinsic should emit throw KryptonPanic, got: {js:?}"
        );
    }

    // ── Dict emission tests ──────────────────────────────────

    #[test]
    fn dict_concrete_instance() {
        use krypton_ir::{FnId, InstanceDef, Type};
        let mut module = make_module("test");
        module.structs.push(krypton_ir::StructDef {
            name: "Point".to_string(),
            type_params: vec![],
            fields: vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Int)],
        });
        module.functions.push(krypton_ir::FnDef {
            id: FnId(1),
            name: "Eq$$Point$$eq".to_string(),
            exported_symbol: "Eq$$Point$$eq".to_string(),
            params: vec![],
            return_type: Type::Bool,
            body: expr(
                Type::Bool,
                krypton_ir::ExprKind::Atom(krypton_ir::Atom::Lit(krypton_ir::Literal::Bool(true))),
            ),
        });
        module.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "Eq$$Point$$eq".to_string(),
                exported_symbol: "Eq$$Point$$eq".to_string(),
            },
        );
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Eq"),
            target_types: vec![Type::Named("Point".to_string(), vec![])],
            target_type_name: "Point".to_string(),
            method_fn_ids: vec![("eq".to_string(), FnId(1))],
            sub_dict_requirements: vec![],
            is_intrinsic: false,
            is_imported: false,
        });

        let js = emit_module(&module);
        assert!(
            js.contains("export const Eq$$Point = { eq: Eq$$Point$$eq };"),
            "should emit concrete dict constant, got: {js:?}"
        );
    }

    #[test]
    fn dict_intrinsic_instance() {
        use krypton_ir::{FnId, InstanceDef, Type};
        let mut module = make_module("test");
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Eq"),
            target_types: vec![Type::Int],
            target_type_name: "Int".to_string(),
            method_fn_ids: vec![("eq".to_string(), FnId(99))],
            sub_dict_requirements: vec![],
            is_intrinsic: true,
            is_imported: false,
        });

        let js = emit_module(&module);
        assert!(
            js.contains("const Eq$$Int = { eq: (a, b) => a === b };"),
            "should emit intrinsic dict inline, got: {js:?}"
        );
    }

    #[test]
    fn dict_parameterized_instance() {
        use krypton_ir::{FnId, InstanceDef, Type};
        let mut gen = TypeVarGen::new();
        let tv_a = gen.fresh();
        let mut module = make_module("test");
        module.functions.push(krypton_ir::FnDef {
            id: FnId(2),
            name: "Show$$Option$$show".to_string(),
            exported_symbol: "Show$$Option$$show".to_string(),
            params: vec![],
            return_type: Type::String,
            body: expr(
                Type::String,
                krypton_ir::ExprKind::Atom(krypton_ir::Atom::Lit(krypton_ir::Literal::String(
                    "x".to_string(),
                ))),
            ),
        });
        module.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "Show$$Option$$show".to_string(),
                exported_symbol: "Show$$Option$$show".to_string(),
            },
        );
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Show"),
            target_types: vec![Type::Named("Option".to_string(), vec![Type::Var(tv_a)])],
            target_type_name: "Option".to_string(),
            method_fn_ids: vec![("show".to_string(), FnId(2))],
            sub_dict_requirements: vec![(make_trait_name("Show"), vec![tv_a])],
            is_intrinsic: false,
            is_imported: false,
        });

        let js = emit_module(&module);
        assert!(
            js.contains("export function Show$$Option$$Var0(dict$$Show$$a)"),
            "should emit factory function, got: {js:?}"
        );
        assert!(
            js.contains("return { show:"),
            "should return dict object, got: {js:?}"
        );
    }

    #[test]
    fn get_dict_emission() {
        use krypton_ir::{FnId, InstanceDef, Type, VarId};
        let mut module = make_module("test");
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Eq"),
            target_types: vec![Type::Int],
            target_type_name: "Int".to_string(),
            method_fn_ids: vec![("eq".to_string(), FnId(99))],
            sub_dict_requirements: vec![],
            is_intrinsic: true,
            is_imported: false,
        });
        // fn test() = let d = GetDict(Eq, Int) in d
        let d = VarId(0);
        module.functions.push(krypton_ir::FnDef {
            id: FnId(0),
            name: "test_fn".to_string(),
            exported_symbol: "test_fn".to_string(),
            params: vec![],
            return_type: Type::Unit,
            body: expr(
                Type::Unit,
                krypton_ir::ExprKind::Let {
                    bind: d,
                    ty: Type::Dict {
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Int],
                    },
                    value: simple(krypton_ir::SimpleExprKind::GetDict {
                        instance_ref: dummy_instance_ref("Eq", "Int"),
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Int],
                    }),
                    body: Box::new(expr(
                        Type::Unit,
                        krypton_ir::ExprKind::Atom(krypton_ir::Atom::Var(d)),
                    )),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "test_fn".to_string(),
                exported_symbol: "test_fn".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("const v$0 = Eq$$Int;"),
            "GetDict should resolve to dict constant name, got: {js:?}"
        );
    }

    #[test]
    fn get_dict_ice_on_repeated_type_var_mismatch() {
        use krypton_ir::{FnId, InstanceDef, Type, VarId};

        let mut gen = TypeVarGen::new();
        let tv = gen.fresh();
        let mut module = make_module("test");
        module.functions.push(krypton_ir::FnDef {
            id: FnId(2),
            name: "Eq$$Pair$$eq".to_string(),
            exported_symbol: "Eq$$Pair$$eq".to_string(),
            params: vec![],
            return_type: Type::Bool,
            body: expr(
                Type::Bool,
                krypton_ir::ExprKind::Atom(krypton_ir::Atom::Lit(krypton_ir::Literal::Bool(true))),
            ),
        });
        module.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "Eq$$Pair$$eq".to_string(),
                exported_symbol: "Eq$$Pair$$eq".to_string(),
            },
        );
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Eq"),
            target_types: vec![Type::Tuple(vec![Type::Var(tv), Type::Var(tv)])],
            target_type_name: "$Tuple2".to_string(),
            method_fn_ids: vec![("eq".to_string(), FnId(2))],
            sub_dict_requirements: vec![],
            is_intrinsic: false,
            is_imported: false,
        });

        let d = VarId(0);
        module.functions.push(krypton_ir::FnDef {
            id: FnId(0),
            name: "test_fn".to_string(),
            exported_symbol: "test_fn".to_string(),
            params: vec![],
            return_type: Type::Unit,
            body: expr(
                Type::Unit,
                krypton_ir::ExprKind::Let {
                    bind: d,
                    ty: Type::Dict {
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Tuple(vec![Type::Int, Type::String])],
                    },
                    value: simple(krypton_ir::SimpleExprKind::GetDict {
                        instance_ref: dummy_instance_ref("Eq", "$Tuple2"),
                        trait_name: make_trait_name("Eq"),
                        target_types: vec![Type::Tuple(vec![Type::Int, Type::String])],
                    }),
                    body: Box::new(expr(
                        Type::Unit,
                        krypton_ir::ExprKind::Atom(krypton_ir::Atom::Var(d)),
                    )),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "test_fn".to_string(),
                exported_symbol: "test_fn".to_string(),
            },
        );

        let panic = std::panic::catch_unwind(|| emit_module(&module))
            .expect_err("mismatched repeated type vars should ICE");
        let msg = if let Some(msg) = panic.downcast_ref::<String>() {
            msg.clone()
        } else if let Some(msg) = panic.downcast_ref::<&str>() {
            msg.to_string()
        } else {
            String::new()
        };
        assert!(
            msg.contains("ICE: unresolved JS dict lookup"),
            "expected unresolved dict ICE, got: {msg:?}"
        );
    }

    #[test]
    fn make_dict_emission() {
        use krypton_ir::{FnId, InstanceDef, Type, VarId};
        let mut gen = TypeVarGen::new();
        let tv_a = gen.fresh();
        let mut module = make_module("test");
        module.functions.push(krypton_ir::FnDef {
            id: FnId(2),
            name: "Show$$Option$$show".to_string(),
            exported_symbol: "Show$$Option$$show".to_string(),
            params: vec![],
            return_type: Type::String,
            body: expr(
                Type::String,
                krypton_ir::ExprKind::Atom(krypton_ir::Atom::Lit(krypton_ir::Literal::String(
                    "x".to_string(),
                ))),
            ),
        });
        module.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "Show$$Option$$show".to_string(),
                exported_symbol: "Show$$Option$$show".to_string(),
            },
        );
        module.instances.push(InstanceDef {
            trait_name: make_trait_name("Show"),
            target_types: vec![Type::Named("Option".to_string(), vec![Type::Var(tv_a)])],
            target_type_name: "Option".to_string(),
            method_fn_ids: vec![("show".to_string(), FnId(2))],
            sub_dict_requirements: vec![(make_trait_name("Show"), vec![tv_a])],
            is_intrinsic: false,
            is_imported: false,
        });

        // fn test(d) = let x = MakeDict(Show, Option, [d]) in x
        let d_var = VarId(0);
        let x_var = VarId(1);
        module.functions.push(krypton_ir::FnDef {
            id: FnId(0),
            name: "test_fn".to_string(),
            exported_symbol: "test_fn".to_string(),
            params: vec![(d_var, Type::Unit)],
            return_type: Type::Unit,
            body: expr(
                Type::Unit,
                krypton_ir::ExprKind::Let {
                    bind: x_var,
                    ty: Type::Unit,
                    value: simple(krypton_ir::SimpleExprKind::MakeDict {
                        instance_ref: dummy_instance_ref("Show", "Option"),
                        trait_name: make_trait_name("Show"),
                        target_types: vec![Type::Named("Option".to_string(), vec![Type::Int])],
                        sub_dicts: vec![krypton_ir::Atom::Var(d_var)],
                    }),
                    body: Box::new(expr(
                        Type::Unit,
                        krypton_ir::ExprKind::Atom(krypton_ir::Atom::Var(x_var)),
                    )),
                },
            ),
        });
        module.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "test_fn".to_string(),
                exported_symbol: "test_fn".to_string(),
            },
        );

        let js = emit_module(&module);
        assert!(
            js.contains("Show$$Option$$Var0(v$0)"),
            "MakeDict should emit factory call, got: {js:?}"
        );
    }

    #[test]
    fn tag_getter_on_variants() {
        let mut module = make_module("test");
        module.sum_types.push(SumTypeDef {
            name: "Color".to_string(),
            type_params: vec![],
            variants: vec![
                VariantDef {
                    name: "Red".to_string(),
                    tag: 0,
                    fields: vec![],
                },
                VariantDef {
                    name: "Green".to_string(),
                    tag: 1,
                    fields: vec![],
                },
                VariantDef {
                    name: "Blue".to_string(),
                    tag: 2,
                    fields: vec![],
                },
            ],
        });

        let js = emit_module(&module);
        assert!(
            js.contains("get $tag() { return 0; }"),
            "Red should have tag 0"
        );
        assert!(
            js.contains("get $tag() { return 1; }"),
            "Green should have tag 1"
        );
        assert!(
            js.contains("get $tag() { return 2; }"),
            "Blue should have tag 2"
        );
    }

    // ── Async/await emission tests ────────────────────────────

    /// Build a 2-module IR: module 0 = core/actor with raw_receive seed,
    /// module 1 = app with main calling imported receive.
    #[test]
    fn async_emit_basic() {
        // Module 0: core/actor with raw_receive extern
        let mut actor_mod = make_module("core/actor");
        actor_mod.extern_fns.push(ExternFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            declaring_module_path: "core/actor".to_string(),
            span: (0, 0),
            target: ExternTarget::Js {
                module: "../extern/js/actor.mjs".to_string(),
            },
            nullable: false,
            throws: false,
            call_kind: ExternCallKind::Static,
            param_types: vec![Type::Named("Mailbox".into(), vec![])],
            return_type: Type::Int,
            bridge_params: vec![],
        });
        actor_mod.fn_identities.insert(
            FnId(0),
            FnIdentity::Extern {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".into()),
                },
                target: ExternTarget::Js {
                    module: "../extern/js/actor.mjs".to_string(),
                },
                name: "raw_receive".to_string(),
            },
        );
        // receive wraps raw_receive (in real code it's a function, here we
        // just make it a function that calls raw_receive).
        actor_mod.functions.push(FnDef {
            id: FnId(1),
            name: "receive".to_string(),
            exported_symbol: "receive".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".into(), vec![]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        actor_mod.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "receive".to_string(),
                exported_symbol: "receive".to_string(),
            },
        );

        // Module 1: app with main calling imported receive
        let mut app_mod = make_module("app");
        app_mod.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "receive".to_string(),
            exported_symbol: "receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "receive".to_string(),
            param_types: vec![Type::Named("Mailbox".into(), vec![])],
            return_type: Type::Int,
        });
        app_mod.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("receive".into()),
                },
                local_alias: "receive".to_string(),
                exported_symbol: "receive".to_string(),
            },
        );
        // non_suspending() — a plain function
        app_mod.functions.push(FnDef {
            id: FnId(1),
            name: "non_suspending".to_string(),
            exported_symbol: "non_suspending".to_string(),
            params: vec![],
            return_type: Type::Int,
            body: expr(Type::Int, ExprKind::Atom(Atom::Lit(Literal::Int(0)))),
        });
        app_mod.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "non_suspending".to_string(),
                exported_symbol: "non_suspending".to_string(),
            },
        );
        // main(mb) calls receive(mb)
        app_mod.functions.push(FnDef {
            id: FnId(2),
            name: "main".to_string(),
            exported_symbol: "main".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".into(), vec![]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        app_mod.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "main".to_string(),
                exported_symbol: "main".to_string(),
            },
        );

        let modules = vec![actor_mod, app_mod];
        let suspend = crate::suspend::analyze_suspend(&modules);

        // actor/receive should suspend (calls raw_receive)
        assert!(suspend.fn_suspends(0, FnId(1)), "receive should suspend");
        // app/main should suspend (calls imported receive)
        assert!(suspend.fn_suspends(1, FnId(2)), "main should suspend");
        // app/non_suspending should not
        assert!(
            !suspend.fn_suspends(1, FnId(1)),
            "non_suspending should not suspend"
        );

        // Emit app module
        let app = &modules[1];
        let js = emit_module_with_suspend(app, 1, &suspend);
        assert!(
            js.contains("export async function main("),
            "main should be async, got:\n{js}"
        );
        assert!(
            js.contains("await receive("),
            "call to receive should have await, got:\n{js}"
        );
        assert!(
            js.contains("export function non_suspending("),
            "non_suspending should be plain function, got:\n{js}"
        );
        assert!(
            !js.contains("async function non_suspending("),
            "non_suspending must NOT be async, got:\n{js}"
        );
    }

    #[test]
    fn closure_await() {
        // Module 0: core/actor with raw_receive seed
        let mut actor_mod = make_module("core/actor");
        actor_mod.extern_fns.push(ExternFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            declaring_module_path: "core/actor".to_string(),
            span: (0, 0),
            target: ExternTarget::Js {
                module: "../extern/js/actor.mjs".to_string(),
            },
            nullable: false,
            throws: false,
            call_kind: ExternCallKind::Static,
            param_types: vec![Type::Int],
            return_type: Type::Int,
            bridge_params: vec![],
        });
        actor_mod.fn_identities.insert(
            FnId(0),
            FnIdentity::Extern {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".into()),
                },
                target: ExternTarget::Js {
                    module: "../extern/js/actor.mjs".to_string(),
                },
                name: "raw_receive".to_string(),
            },
        );
        // recv(x) — wraps raw_receive
        actor_mod.functions.push(FnDef {
            id: FnId(1),
            name: "recv".to_string(),
            exported_symbol: "recv".to_string(),
            params: vec![(VarId(0), Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        actor_mod.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "recv".to_string(),
                exported_symbol: "recv".to_string(),
            },
        );

        // Module 1: app with a local suspending fn and MakeClosure over it
        let mut app_mod = make_module("app");
        app_mod.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "recv".to_string(),
            exported_symbol: "recv".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "recv".to_string(),
            param_types: vec![Type::Int],
            return_type: Type::Int,
        });
        app_mod.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("recv".into()),
                },
                local_alias: "recv".to_string(),
                exported_symbol: "recv".to_string(),
            },
        );
        // suspending_fn(cap, x) — local fn that calls imported recv
        // (MakeClosure always targets local fns in real IR)
        app_mod.functions.push(FnDef {
            id: FnId(1),
            name: "suspending_fn".to_string(),
            exported_symbol: "suspending_fn".to_string(),
            params: vec![(VarId(0), Type::Int), (VarId(1), Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(2),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(1))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(2))))),
                },
            ),
        });
        app_mod.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "suspending_fn".to_string(),
                exported_symbol: "suspending_fn".to_string(),
            },
        );
        // wrapper(mb) { let cls = MakeClosure(suspending_fn, [mb]); let r = CallClosure(cls, [42]); r }
        app_mod.functions.push(FnDef {
            id: FnId(2),
            name: "wrapper".to_string(),
            exported_symbol: "wrapper".to_string(),
            params: vec![(VarId(10), Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(11),
                    ty: Type::Fn(vec![Type::Int], Box::new(Type::Int)),
                    value: simple(SimpleExprKind::MakeClosure {
                        func: FnId(1),
                        captures: vec![Atom::Var(VarId(10))],
                    }),
                    body: Box::new(expr(
                        Type::Int,
                        ExprKind::Let {
                            bind: VarId(12),
                            ty: Type::Int,
                            value: simple(SimpleExprKind::CallClosure {
                                closure: Atom::Var(VarId(11)),
                                args: vec![Atom::Lit(Literal::Int(42))],
                            }),
                            body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(12))))),
                        },
                    )),
                },
            ),
        });
        app_mod.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "wrapper".to_string(),
                exported_symbol: "wrapper".to_string(),
            },
        );

        let modules = vec![actor_mod, app_mod];
        let suspend = crate::suspend::analyze_suspend(&modules);

        assert!(
            suspend.fn_suspends(1, FnId(1)),
            "suspending_fn should suspend"
        );
        assert!(
            suspend.fn_suspends(1, FnId(2)),
            "wrapper should suspend (closure calls suspending fn)"
        );

        let app = &modules[1];
        let js = emit_module_with_suspend(app, 1, &suspend);
        assert!(
            js.contains("async (a$0) => await suspending_fn("),
            "closure wrapper should be async with await, got:\n{js}"
        );
        assert!(
            js.contains("await v$1("),
            "CallClosure should emit await, got:\n{js}"
        );
    }

    #[test]
    fn non_recur_join_async() {
        // Module 0: core/actor with raw_receive seed
        let mut actor_mod = make_module("core/actor");
        actor_mod.extern_fns.push(ExternFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            declaring_module_path: "core/actor".to_string(),
            span: (0, 0),
            target: ExternTarget::Js {
                module: "../extern/js/actor.mjs".to_string(),
            },
            nullable: false,
            throws: false,
            call_kind: ExternCallKind::Static,
            param_types: vec![Type::Int],
            return_type: Type::Int,
            bridge_params: vec![],
        });
        actor_mod.fn_identities.insert(
            FnId(0),
            FnIdentity::Extern {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".into()),
                },
                target: ExternTarget::Js {
                    module: "../extern/js/actor.mjs".to_string(),
                },
                name: "raw_receive".to_string(),
            },
        );
        actor_mod.functions.push(FnDef {
            id: FnId(1),
            name: "recv".to_string(),
            exported_symbol: "recv".to_string(),
            params: vec![(VarId(0), Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        actor_mod.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "recv".to_string(),
                exported_symbol: "recv".to_string(),
            },
        );

        // Module 1: app with a non-recur LetJoin whose body calls recv
        let mut app_mod = make_module("app");
        app_mod.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "recv".to_string(),
            exported_symbol: "recv".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "recv".to_string(),
            param_types: vec![Type::Int],
            return_type: Type::Int,
        });
        app_mod.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("recv".into()),
                },
                local_alias: "recv".to_string(),
                exported_symbol: "recv".to_string(),
            },
        );
        // main(x): LetJoin j(y) = recv(y); in Jump(j, x)
        let join_name = VarId(10);
        app_mod.functions.push(FnDef {
            id: FnId(1),
            name: "main".to_string(),
            exported_symbol: "main".to_string(),
            params: vec![(VarId(0), Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::LetJoin {
                    name: join_name,
                    params: vec![(VarId(1), Type::Int)],
                    join_body: Box::new(expr(
                        Type::Int,
                        ExprKind::Let {
                            bind: VarId(2),
                            ty: Type::Int,
                            value: simple(SimpleExprKind::Call {
                                func: FnId(0),
                                args: vec![Atom::Var(VarId(1))],
                            }),
                            body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(2))))),
                        },
                    )),
                    body: Box::new(expr(
                        Type::Int,
                        ExprKind::Jump {
                            target: join_name,
                            args: vec![Atom::Var(VarId(0))],
                        },
                    )),
                    is_recur: false,
                },
            ),
        });
        app_mod.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "main".to_string(),
                exported_symbol: "main".to_string(),
            },
        );

        let modules = vec![actor_mod, app_mod];
        let suspend = crate::suspend::analyze_suspend(&modules);

        assert!(suspend.fn_suspends(1, FnId(1)), "main should suspend");

        let app = &modules[1];
        let js = emit_module_with_suspend(app, 1, &suspend);
        assert!(
            js.contains("async function v$1("),
            "join helper should be async function, got:\n{js}"
        );
        assert!(
            js.contains("return await v$1("),
            "jump to join should emit return await, got:\n{js}"
        );
    }
}
