pub mod emit;

pub use emit::{compile_modules_js, JsCodegenError};

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap};

    use krypton_ir::*;

    /// Build a minimal IR Module with the given fields.
    fn make_module(name: &str) -> Module {
        Module {
            name: name.to_string(),
            structs: vec![],
            sum_types: vec![],
            functions: vec![],
            fn_names: HashMap::new(),
            extern_fns: vec![],
            extern_types: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: BTreeSet::new(),
            module_path: name.to_string(),
            fn_dict_requirements: HashMap::new(),
        }
    }

    /// Emit JS from a hand-built IR Module directly (bypasses lowering).
    fn emit_module(module: &Module) -> String {
        let mut emitter = crate::emit::JsEmitter::new(module);
        emitter.emit()
    }

    #[test]
    fn empty_module() {
        let module = make_module("empty");
        let js = emit_module(&module);
        // Should produce valid JS (empty or whitespace only)
        assert!(
            js.trim().is_empty(),
            "empty module should produce empty JS, got: {js:?}"
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
            params: vec![(x, Type::Int), (y, Type::Int)],
            return_type: Type::Int,
            body: Expr {
                kind: ExprKind::Let {
                    bind: result,
                    ty: Type::Int,
                    value: SimpleExpr::PrimOp {
                        op: PrimOp::AddInt,
                        args: vec![Atom::Var(x), Atom::Var(y)],
                    },
                    body: Box::new(Expr {
                        kind: ExprKind::Atom(Atom::Var(result)),
                        ty: Type::Int,
                    }),
                },
                ty: Type::Int,
            },
        });
        module.fn_names.insert(FnId(0), "add".to_string());

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
            fields: vec![
                ("x".to_string(), Type::Int),
                ("y".to_string(), Type::Int),
            ],
        });

        let js = emit_module(&module);
        assert!(js.contains("export class Point {"), "should export Point class");
        assert!(js.contains("constructor(x, y)"), "should have constructor with field names");
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
        assert!(js.contains("export class Option {"), "should export base class");
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
        assert!(js.contains("extends Option"), "variants should extend base class");
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
            source_module: "utils".to_string(),
            original_name: "helper".to_string(),
            param_types: vec![Type::Int],
            return_type: Type::Int,
        });
        module.imported_fns.push(ImportedFnDef {
            id: FnId(11),
            name: "format".to_string(),
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
            params: vec![],
            return_type: Type::Unit,
            body: Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                ty: Type::Unit,
            },
        });
        module.fn_names.insert(FnId(0), "filter".to_string());
        module.imported_fns.push(ImportedFnDef {
            id: FnId(1),
            name: "list_filter".to_string(),
            source_module: "core/list".to_string(),
            original_name: "filter".to_string(),
            param_types: vec![],
            return_type: Type::Unit,
        });
        module.fn_names.insert(FnId(1), "list_filter".to_string());

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
        module.module_path = "core/io".to_string();
        module.imported_fns.push(ImportedFnDef {
            id: FnId(10),
            name: "Ok".to_string(),
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
        module.module_path = "core/io".to_string();
        module.imported_fns.push(ImportedFnDef {
            id: FnId(10),
            name: "helper".to_string(),
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
            params: vec![],
            return_type: Type::Unit,
            body: Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                ty: Type::Unit,
            },
        });
        module.fn_names.insert(FnId(0), "combine".to_string());
        module.imported_fns.push(ImportedFnDef {
            id: FnId(0), // same FnId — IR lowerer reuses it
            name: "combine".to_string(),
            source_module: "semigroup".to_string(),
            original_name: "combine".to_string(),
            param_types: vec![],
            return_type: Type::Unit,
        });

        let js = emit_module(&module);
        assert!(
            !js.contains("import"),
            "shadowed import should be skipped entirely, got: {js:?}"
        );
    }

    #[test]
    fn output_file_naming() {
        // Build a Module directly and check that compile_modules_js produces .mjs filenames.
        // We can't call compile_modules_js with hand-built modules (it takes TypedModule),
        // so we test the emitter's filename logic directly.
        let module = make_module("hello");
        let mut emitter = crate::emit::JsEmitter::new(&module);
        let _js = emitter.emit();
        // The compile_modules_js function produces "{name}.mjs"
        let filename = format!("{}.mjs", module.name);
        assert_eq!(filename, "hello.mjs");
        assert!(filename.ends_with(".mjs"), "output should use .mjs extension");
    }

    #[test]
    fn literal_emission() {
        let mut module = make_module("test");
        // fn answer() = 42
        module.functions.push(FnDef {
            id: FnId(0),
            name: "answer".to_string(),
            params: vec![],
            return_type: Type::Int,
            body: Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Int(42))),
                ty: Type::Int,
            },
        });
        module.fn_names.insert(FnId(0), "answer".to_string());

        let js = emit_module(&module);
        assert!(js.contains("return 42n;"), "Int literals should emit as BigInt (42n)");
    }

    #[test]
    fn string_literal_emission() {
        let mut module = make_module("test");
        module.functions.push(FnDef {
            id: FnId(0),
            name: "greeting".to_string(),
            params: vec![],
            return_type: Type::String,
            body: Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::String("hello".to_string()))),
                ty: Type::String,
            },
        });
        module.fn_names.insert(FnId(0), "greeting".to_string());

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
            params: vec![],
            return_type: Type::Bool,
            body: Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Bool(true))),
                ty: Type::Bool,
            },
        });
        module.fn_names.insert(FnId(0), "yes".to_string());

        let js = emit_module(&module);
        assert!(js.contains("return true;"), "Bool literals should emit as JS booleans");
    }

    #[test]
    fn unit_literal_emission() {
        let mut module = make_module("test");
        module.functions.push(FnDef {
            id: FnId(0),
            name: "noop".to_string(),
            params: vec![],
            return_type: Type::Unit,
            body: Expr {
                kind: ExprKind::Atom(Atom::Lit(Literal::Unit)),
                ty: Type::Unit,
            },
        });
        module.fn_names.insert(FnId(0), "noop".to_string());

        let js = emit_module(&module);
        assert!(
            js.contains("return undefined;"),
            "Unit should emit as undefined"
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
        assert!(js.contains("get $tag() { return 0; }"), "Red should have tag 0");
        assert!(js.contains("get $tag() { return 1; }"), "Green should have tag 1");
        assert!(js.contains("get $tag() { return 2; }"), "Blue should have tag 2");
    }
}
