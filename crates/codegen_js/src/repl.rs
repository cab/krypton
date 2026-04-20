//! JS REPL codegen: wraps compiled `__eval` in an async `__repl_eval()` that
//! loads prior bindings from the Var registry and stores results back.

use std::collections::HashMap;

use krypton_ir::Module;
use krypton_typechecker::link_context::LinkContext;

use crate::emit::{compile_modules_js, js_safe_name, JsCodegenError};

/// Compile IR modules for a REPL eval, producing JS files with a `__repl_eval()` wrapper.
///
/// - `repl_vars`: ordered `(name, registry_key)` pairs — parameters to `__eval`
/// - `store_var`: if `Some`, the registry key where the result is stored
///
/// The entry module gets a `__repl_eval()` appended that:
/// 1. Loads each prior binding from the Registry via `__repl_lookup(key).get()`
/// 2. Calls `await __eval(...)` with those values
/// 3. Optionally stores the result via `__repl_intern(key).set(result)`
/// 4. Returns the result
pub fn compile_repl_js(
    ir_modules: &[Module],
    module_name: &str,
    link_ctx: &LinkContext,
    module_sources: &HashMap<String, Option<String>>,
    repl_vars: &[(String, String)],
    store_var: Option<&str>,
    show_wrapped: bool,
) -> Result<Vec<(String, String)>, JsCodegenError> {
    let mut files = compile_modules_js(ir_modules, module_name, false, link_ctx, module_sources)?;

    let entry_filename = format!("{}.mjs", module_name);

    // Find and patch the entry module
    let entry = files
        .iter_mut()
        .find(|(path, _)| *path == entry_filename)
        .unwrap_or_else(|| {
            panic!(
                "ICE: entry module '{}' not found in JS codegen output",
                entry_filename
            )
        });

    let mut patched = String::new();

    // Prepend registry import
    patched.push_str(
        "import { lookup as __repl_lookup, intern as __repl_intern } from './extern/js/repl-registry.mjs';\n",
    );
    patched.push_str(&entry.1);

    // Build the eval wrapper
    patched.push_str("\nexport async function __repl_eval() {\n");

    // Load prior bindings from Registry
    for (name, key) in repl_vars {
        let safe_name = js_safe_name(name);
        patched.push_str(&format!(
            "  const {} = __repl_lookup(\"{}\").get();\n",
            safe_name, key
        ));
    }

    // Call __eval
    let args = repl_vars
        .iter()
        .map(|(name, _)| js_safe_name(name))
        .collect::<Vec<_>>()
        .join(", ");

    if show_wrapped {
        // __eval returns a tuple [rawValue, showString]
        patched.push_str(&format!("  const __tuple = await __eval({});\n", args));
        patched.push_str("  const __result = __tuple[0];\n");
        patched.push_str("  const __display = __tuple[1];\n");
    } else {
        patched.push_str(&format!("  const __result = await __eval({});\n", args));
    }

    // Store result if needed
    if let Some(key) = store_var {
        patched.push_str(&format!("  __repl_intern(\"{}\").set(__result);\n", key));
    }

    if show_wrapped {
        patched.push_str("  return { value: __result, display: __display };\n");
    } else {
        patched.push_str("  return { value: __result, display: null };\n");
    }
    patched.push_str("}\n");

    entry.1 = patched;

    Ok(files)
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::collections::BTreeSet;

    use rustc_hash::FxHashMap;

    use krypton_ir::*;
    use krypton_typechecker::link_context::LinkContext;
    use krypton_typechecker::module_interface::{ModuleInterface, ModulePath as LinkModulePath};

    fn make_eval_module(return_type: Type) -> Module {
        Module {
            name: "repl_1".into(),
            fn_identities: {
                let mut m = FxHashMap::default();
                m.insert(
                    FnId(0),
                    FnIdentity::Local {
                        name: "__eval".into(),
                        exported_symbol: "__eval".into(),
                    },
                );
                m
            },
            structs: vec![],
            sum_types: vec![],
            functions: vec![FnDef {
                id: FnId(0),
                name: "__eval".into(),
                exported_symbol: "__eval".into(),
                params: vec![],
                return_type: return_type.clone(),
                body: Expr::new(
                    (0, 0),
                    return_type,
                    ExprKind::Atom(Atom::Lit(Literal::Int(42))),
                ),
            }],
            extern_fns: vec![],
            extern_types: vec![],
            extern_traits: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: BTreeSet::new(),
            module_path: krypton_ir::ModulePath::new("repl_1"),
            fn_dict_requirements: Default::default(),
            fn_exit_closes: Default::default(),
        }
    }

    fn make_link_ctx(module_path: &str) -> LinkContext {
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
            exported_fn_qualifiers: Default::default(),
            type_visibility: Default::default(),
            private_names: Default::default(),
        };
        LinkContext::build(vec![iface])
    }

    #[test]
    fn repl_wrapper_no_vars() {
        let modules = vec![make_eval_module(Type::Int)];
        let link_ctx = make_link_ctx("repl_1");
        let sources: HashMap<String, Option<String>> = HashMap::new();

        let files =
            compile_repl_js(&modules, "repl_1", &link_ctx, &sources, &[], None, false).unwrap();
        let entry = files.iter().find(|(p, _)| p == "repl_1.mjs").unwrap();

        assert!(entry
            .1
            .contains("import { lookup as __repl_lookup, intern as __repl_intern }"));
        assert!(entry.1.contains("export async function __repl_eval()"));
        assert!(entry.1.contains("const __result = await __eval()"));
        assert!(entry
            .1
            .contains("return { value: __result, display: null };"));
        // The import line contains __repl_intern but no .set() call should be present
        assert!(!entry.1.contains(".set(__result)"));
    }

    #[test]
    fn repl_wrapper_with_vars_and_store() {
        let modules = vec![make_eval_module(Type::Int)];
        let link_ctx = make_link_ctx("repl_1");
        let sources: HashMap<String, Option<String>> = HashMap::new();

        let repl_vars = vec![
            ("x".to_string(), "x".to_string()),
            ("y".to_string(), "y".to_string()),
        ];

        let files = compile_repl_js(
            &modules,
            "repl_1",
            &link_ctx,
            &sources,
            &repl_vars,
            Some("res0"),
            false,
        )
        .unwrap();
        let entry = files.iter().find(|(p, _)| p == "repl_1.mjs").unwrap();

        assert!(entry.1.contains("const x = __repl_lookup(\"x\").get();"));
        assert!(entry.1.contains("const y = __repl_lookup(\"y\").get();"));
        assert!(entry.1.contains("const __result = await __eval(x, y)"));
        assert!(entry.1.contains("__repl_intern(\"res0\").set(__result)"));
        assert!(entry
            .1
            .contains("return { value: __result, display: null };"));
    }

    #[test]
    fn repl_wrapper_mangles_reserved_binding_names() {
        let modules = vec![make_eval_module(Type::Int)];
        let link_ctx = make_link_ctx("repl_1");
        let sources: HashMap<String, Option<String>> = HashMap::new();

        let repl_vars = vec![
            ("default".to_string(), "default".to_string()),
            ("await".to_string(), "await".to_string()),
            ("class".to_string(), "class".to_string()),
        ];

        let files = compile_repl_js(
            &modules, "repl_1", &link_ctx, &sources, &repl_vars, None, false,
        )
        .unwrap();
        let entry = files.iter().find(|(p, _)| p == "repl_1.mjs").unwrap();

        assert!(entry
            .1
            .contains("const $default = __repl_lookup(\"default\").get();"));
        assert!(entry
            .1
            .contains("const $await = __repl_lookup(\"await\").get();"));
        assert!(entry
            .1
            .contains("const $class = __repl_lookup(\"class\").get();"));
        assert!(entry
            .1
            .contains("const __result = await __eval($default, $await, $class)"));
    }

    /// End-to-end test: compile real Krypton source through the full REPL pipeline.
    #[test]
    fn repl_end_to_end_bare_expr() {
        use krypton_modules::{module_resolver::ModuleResolver, stdlib_loader::StdlibLoader};

        struct TestResolver(String, String);
        impl ModuleResolver for TestResolver {
            fn resolve(&self, path: &str) -> Option<String> {
                if path == self.0 {
                    Some(self.1.clone())
                } else {
                    StdlibLoader::get_source(path).map(str::to_owned)
                }
            }
        }

        // Simulate: first eval is "1 + 2", stored as res0
        let source = "fun __eval() = 1 + 2\n";
        let module_name = "repl_1";
        let (parsed, errors) = krypton_parser::parser::parse(source);
        assert!(errors.is_empty());

        let resolver = TestResolver(module_name.into(), source.into());
        let (typed, interfaces) = krypton_typechecker::infer::infer_module(
            &parsed,
            &resolver,
            module_name.into(),
            krypton_parser::ast::CompileTarget::Js,
        )
        .unwrap();

        let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
        let (ir_modules, module_sources) =
            krypton_ir::lower::lower_all(&typed, module_name, &link_ctx).unwrap();

        let js_sources: HashMap<String, Option<String>> = module_sources
            .into_iter()
            .map(|(k, v)| (k, Some(v)))
            .collect();

        let files = compile_repl_js(
            &ir_modules,
            module_name,
            &link_ctx,
            &js_sources,
            &[],
            Some("res0"),
            false,
        )
        .unwrap();

        let entry = files.iter().find(|(p, _)| p == "repl_1.mjs").unwrap();
        let js = &entry.1;

        // Registry import present
        assert!(js.contains("import { lookup as __repl_lookup, intern as __repl_intern }"));
        // __eval is defined (compiled from source)
        assert!(js.contains("function __eval("));
        // Wrapper calls __eval with no args (no prior bindings)
        assert!(js.contains("const __result = await __eval()"));
        // Result stored in registry
        assert!(js.contains("__repl_intern(\"res0\").set(__result)"));
        // Returns { value, display } object
        assert!(js.contains("return { value: __result, display: null };"));
    }

    /// End-to-end: compile with prior bindings passed through.
    #[test]
    fn repl_end_to_end_with_prior_binding() {
        use krypton_modules::{module_resolver::ModuleResolver, stdlib_loader::StdlibLoader};

        struct TestResolver(String, String);
        impl ModuleResolver for TestResolver {
            fn resolve(&self, path: &str) -> Option<String> {
                if path == self.0 {
                    Some(self.1.clone())
                } else {
                    StdlibLoader::get_source(path).map(str::to_owned)
                }
            }
        }

        // Simulate: prior binding x: Int, now eval "x * 2"
        let source = "fun __eval(x: Int) = x * 2\n";
        let module_name = "repl_2";
        let (parsed, errors) = krypton_parser::parser::parse(source);
        assert!(errors.is_empty());

        let resolver = TestResolver(module_name.into(), source.into());
        let (typed, interfaces) = krypton_typechecker::infer::infer_module(
            &parsed,
            &resolver,
            module_name.into(),
            krypton_parser::ast::CompileTarget::Js,
        )
        .unwrap();

        let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
        let (ir_modules, module_sources) =
            krypton_ir::lower::lower_all(&typed, module_name, &link_ctx).unwrap();

        let js_sources: HashMap<String, Option<String>> = module_sources
            .into_iter()
            .map(|(k, v)| (k, Some(v)))
            .collect();

        let repl_vars = vec![("x".to_string(), "x".to_string())];
        let files = compile_repl_js(
            &ir_modules,
            module_name,
            &link_ctx,
            &js_sources,
            &repl_vars,
            Some("res1"),
            false,
        )
        .unwrap();

        let entry = files.iter().find(|(p, _)| p == "repl_2.mjs").unwrap();
        let js = &entry.1;

        // Prior binding loaded from registry
        assert!(js.contains("const x = __repl_lookup(\"x\").get()"));
        // __eval called with prior binding
        assert!(js.contains("const __result = await __eval(x)"));
        // Result stored
        assert!(js.contains("__repl_intern(\"res1\").set(__result)"));
    }

    #[test]
    fn repl_end_to_end_with_reserved_prior_binding() {
        use krypton_modules::{module_resolver::ModuleResolver, stdlib_loader::StdlibLoader};

        struct TestResolver(String, String);
        impl ModuleResolver for TestResolver {
            fn resolve(&self, path: &str) -> Option<String> {
                if path == self.0 {
                    Some(self.1.clone())
                } else {
                    StdlibLoader::get_source(path).map(str::to_owned)
                }
            }
        }

        let source = "fun __eval(default: Int, await: Int) = default + await\n";
        let module_name = "repl_reserved";
        let (parsed, errors) = krypton_parser::parser::parse(source);
        assert!(errors.is_empty());

        let resolver = TestResolver(module_name.into(), source.into());
        let (typed, interfaces) = krypton_typechecker::infer::infer_module(
            &parsed,
            &resolver,
            module_name.into(),
            krypton_parser::ast::CompileTarget::Js,
        )
        .unwrap();

        let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
        let (ir_modules, module_sources) =
            krypton_ir::lower::lower_all(&typed, module_name, &link_ctx).unwrap();

        let js_sources: HashMap<String, Option<String>> = module_sources
            .into_iter()
            .map(|(k, v)| (k, Some(v)))
            .collect();

        let repl_vars = vec![
            ("default".to_string(), "default".to_string()),
            ("await".to_string(), "await".to_string()),
        ];
        let files = compile_repl_js(
            &ir_modules,
            module_name,
            &link_ctx,
            &js_sources,
            &repl_vars,
            Some("res_reserved"),
            false,
        )
        .unwrap();

        let entry = files
            .iter()
            .find(|(p, _)| p == "repl_reserved.mjs")
            .unwrap();
        let js = &entry.1;

        assert!(js.contains("function __eval("));
        assert!(js.contains("const $default = __repl_lookup(\"default\").get()"));
        assert!(js.contains("const $await = __repl_lookup(\"await\").get()"));
        assert!(js.contains("const __result = await __eval($default, $await)"));
    }

    /// End-to-end: fun def produces no store call.
    #[test]
    fn repl_end_to_end_fun_def() {
        use krypton_modules::{module_resolver::ModuleResolver, stdlib_loader::StdlibLoader};

        struct TestResolver(String, String);
        impl ModuleResolver for TestResolver {
            fn resolve(&self, path: &str) -> Option<String> {
                if path == self.0 {
                    Some(self.1.clone())
                } else {
                    StdlibLoader::get_source(path).map(str::to_owned)
                }
            }
        }

        // Fun def: __eval returns Unit, no store
        let source = "fun f(n: Int) -> Int = n + 1\nfun __eval() -> Unit = ()\n";
        let module_name = "repl_3";
        let (parsed, errors) = krypton_parser::parser::parse(source);
        assert!(errors.is_empty());

        let resolver = TestResolver(module_name.into(), source.into());
        let (typed, interfaces) = krypton_typechecker::infer::infer_module(
            &parsed,
            &resolver,
            module_name.into(),
            krypton_parser::ast::CompileTarget::Js,
        )
        .unwrap();

        let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
        let (ir_modules, module_sources) =
            krypton_ir::lower::lower_all(&typed, module_name, &link_ctx).unwrap();

        let js_sources: HashMap<String, Option<String>> = module_sources
            .into_iter()
            .map(|(k, v)| (k, Some(v)))
            .collect();

        let files = compile_repl_js(
            &ir_modules,
            module_name,
            &link_ctx,
            &js_sources,
            &[],
            None,
            false, // no store_var for fun defs
        )
        .unwrap();

        let entry = files.iter().find(|(p, _)| p == "repl_3.mjs").unwrap();
        let js = &entry.1;

        // Wrapper exists
        assert!(js.contains("export async function __repl_eval()"));
        // No store call (no .set)
        assert!(!js.contains(".set(__result)"));
        // f is defined
        assert!(js.contains("function f("));
    }
}
