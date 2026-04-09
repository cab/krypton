use std::collections::HashMap;

use krypton_modules::module_resolver::{CompositeResolver, ModuleResolver};
use krypton_parser::parser::parse;
use krypton_typechecker::infer;
use krypton_typechecker::link_context::LinkContext;
use krypton_typechecker::module_interface::*;
use krypton_typechecker::typed_ast::TraitName;

// ---------------------------------------------------------------------------
// In-memory resolver for multi-module tests
// ---------------------------------------------------------------------------

struct InMemoryResolver {
    modules: HashMap<String, String>,
}

impl InMemoryResolver {
    fn new(modules: Vec<(&str, &str)>) -> Self {
        Self {
            modules: modules
                .into_iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
        }
    }
}

impl ModuleResolver for InMemoryResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        self.modules.get(module_path).cloned()
    }
}

struct TestResolver {
    stdlib: CompositeResolver,
    memory: InMemoryResolver,
}

impl TestResolver {
    fn new(libs: Vec<(&str, &str)>) -> Self {
        Self {
            stdlib: CompositeResolver::stdlib_only(),
            memory: InMemoryResolver::new(libs),
        }
    }
}

impl ModuleResolver for TestResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        self.stdlib
            .resolve(module_path)
            .or_else(|| self.memory.resolve(module_path))
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_multi(
    root_src: &str,
    root_path: &str,
    libs: Vec<(&str, &str)>,
) -> Vec<(String, ModuleInterface)> {
    // Parse all sources so we can get direct_deps from the ASTs
    let mut all_sources: HashMap<String, String> = libs
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    all_sources.insert(root_path.to_string(), root_src.to_string());

    let (root_module, errors) = parse(root_src);
    assert!(errors.is_empty(), "root parse errors: {:?}", errors);
    let resolver = TestResolver::new(libs);
    let (modules, _) = infer::infer_module(
        &root_module,
        &resolver,
        root_path.to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("typecheck failed");

    modules
        .iter()
        .map(|typed| {
            // Re-parse the source to get direct deps from the AST
            let dep_strs = if let Some(src) = all_sources.get(&typed.module_path) {
                let (parsed, _) = parse(src);
                collect_direct_deps(&parsed)
                    .iter()
                    .map(|p| p.0.clone())
                    .collect()
            } else {
                // stdlib module — try to resolve and parse
                let dep_strs: Vec<String> = if let Some(src) = resolver.resolve(&typed.module_path)
                {
                    let (parsed, _) = parse(&src);
                    collect_direct_deps(&parsed)
                        .iter()
                        .map(|p| p.0.clone())
                        .collect()
                } else {
                    vec![]
                };
                dep_strs
            };
            let iface = extract_interface(typed, &dep_strs);
            (typed.module_path.clone(), iface)
        })
        .collect()
}

// ===========================================================================
// Integration tests
// ===========================================================================

// 18. Link context from real interfaces
#[test]
fn test_link_context_from_real_interfaces() {
    let libs = vec![("mylib", "pub fun helper() -> Int = 42")];
    let all = extract_multi(
        "import mylib.{helper}\npub fun main() -> Int = helper()",
        "test",
        libs,
    );

    let interfaces: Vec<ModuleInterface> = all.into_iter().map(|(_, iface)| iface).collect();
    let ctx = LinkContext::build(interfaces);

    // Verify basic lookups
    let summary = ctx.lookup_fn_summary(&ModulePath::new("mylib"), "helper");
    assert!(summary.is_some(), "should find helper in mylib");
    assert_eq!(summary.unwrap().name, "helper");

    let main_fn = ctx.lookup_fn_summary(&ModulePath::new("test"), "main");
    assert!(main_fn.is_some(), "should find main in test");
}

// 19. Link context reexport chain
#[test]
fn test_link_context_reexport_chain() {
    let libs = vec![
        ("inner", "pub type Point = { x: Int, y: Int }"),
        ("outer", "pub import inner.{Point}\nimport inner.{Point}"),
    ];
    let all = extract_multi(
        "import outer.{Point}\npub fun origin() -> Point = Point { x = 0, y = 0 }",
        "test",
        libs,
    );

    let interfaces: Vec<ModuleInterface> = all.into_iter().map(|(_, iface)| iface).collect();
    let ctx = LinkContext::build(interfaces);

    // outer reexports Point from inner
    let canonical = ctx.resolve_type_canonical(&ModulePath::new("outer"), "Point");
    assert!(canonical.is_some(), "outer should have reexported Point");
    assert_eq!(canonical.unwrap().module, ModulePath::new("inner"));
}

// 20. Link context instance resolution
#[test]
fn test_link_context_instance_resolution() {
    let libs = vec![(
        "mylib",
        r#"
import core/show.{Show, show}
pub type Color = Red | Green | Blue
impl Show[Color] {
    fun show(c: Color) -> String = match c {
        Red => "Red",
        Green => "Green",
        Blue => "Blue",
    }
}
"#,
    )];
    let all = extract_multi(
        "import mylib.{Color, Red, Green, Blue}\nimport core/show.{Show, show}\npub fun main() -> String = show(Red)",
        "test",
        libs,
    );

    let interfaces: Vec<ModuleInterface> = all.into_iter().map(|(_, iface)| iface).collect();
    let ctx = LinkContext::build(interfaces);

    let show_trait = TraitName::new("core/show".to_string(), "Show".to_string());
    let instances = ctx.instances_for_trait(&show_trait);
    // Should find Show[Color] from mylib
    let color_inst = instances
        .iter()
        .find(|(_, inst)| inst.target_type_name == "Color");
    assert!(color_inst.is_some(), "should find Show[Color] instance");
    assert_eq!(color_inst.unwrap().0, &ModulePath::new("mylib"));
}
