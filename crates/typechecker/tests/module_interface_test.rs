use std::collections::HashMap;

use krypton_modules::module_resolver::{CompositeResolver, ModuleResolver};
use krypton_parser::parser::parse;
use krypton_typechecker::infer;
use krypton_typechecker::module_interface::*;

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

/// Combined resolver: stdlib + in-memory test modules.
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

fn typecheck_and_extract(src: &str) -> ModuleInterface {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let dep_paths = collect_direct_deps(&module);
    let dep_strs: Vec<String> = dep_paths.iter().map(|p| p.0.clone()).collect();
    let modules = infer::infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
    )
    .expect("typecheck failed");
    extract_interface(&modules[0], &dep_strs)
}

fn extract_multi(root_src: &str, libs: Vec<(&str, &str)>) -> ModuleInterface {
    let (root_module, errors) = parse(root_src);
    assert!(errors.is_empty(), "root parse errors: {:?}", errors);
    let dep_paths = collect_direct_deps(&root_module);
    let dep_strs: Vec<String> = dep_paths.iter().map(|p| p.0.clone()).collect();
    let resolver = TestResolver::new(libs);
    let modules =
        infer::infer_module(&root_module, &resolver, "test".to_string()).expect("typecheck failed");
    extract_interface(&modules[0], &dep_strs)
}

// ===========================================================================
// Unit tests for identity types
// ===========================================================================

#[test]
fn module_path_display() {
    assert_eq!(
        ModulePath::new("core/semigroup").to_string(),
        "core/semigroup"
    );
}

#[test]
fn module_path_equality() {
    assert_eq!(ModulePath::new("core/eq"), ModulePath::new("core/eq"));
    assert_ne!(ModulePath::new("core/eq"), ModulePath::new("core/ord"));
}

#[test]
fn local_symbol_key_display_function() {
    assert_eq!(LocalSymbolKey::Function("add".into()).to_string(), "fn/add");
}

#[test]
fn local_symbol_key_display_type() {
    assert_eq!(
        LocalSymbolKey::Type("Point".into()).to_string(),
        "type/Point"
    );
}

#[test]
fn local_symbol_key_display_trait() {
    assert_eq!(LocalSymbolKey::Trait("Eq".into()).to_string(), "trait/Eq");
}

#[test]
fn local_symbol_key_display_constructor() {
    assert_eq!(
        LocalSymbolKey::Constructor {
            parent_type: "Option".into(),
            name: "Some".into(),
        }
        .to_string(),
        "type/Option/ctor/Some"
    );
}

#[test]
fn local_symbol_key_display_instance() {
    assert_eq!(
        LocalSymbolKey::Instance {
            trait_name: "Eq".into(),
            target_type: "Point".into(),
        }
        .to_string(),
        "instance/Eq/Point"
    );
}

#[test]
fn canonical_ref_equality() {
    let a = CanonicalRef {
        module: ModulePath::new("core/eq"),
        symbol: LocalSymbolKey::Function("eq".into()),
    };
    let b = CanonicalRef {
        module: ModulePath::new("core/eq"),
        symbol: LocalSymbolKey::Function("eq".into()),
    };
    let c = CanonicalRef {
        module: ModulePath::new("core/ord"),
        symbol: LocalSymbolKey::Function("eq".into()),
    };
    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn canonical_ref_display() {
    let r = CanonicalRef {
        module: ModulePath::new("core/eq"),
        symbol: LocalSymbolKey::Function("eq".into()),
    };
    assert_eq!(r.to_string(), "core/eq::fn/eq");
}

// ===========================================================================
// Extraction tests: single module
// ===========================================================================

#[test]
fn extract_interface_module_path() {
    let iface = typecheck_and_extract("pub fun add(x: Int, y: Int) -> Int = x + y");
    assert_eq!(iface.module_path, ModulePath::new("test"));
}

#[test]
fn extract_interface_pub_fn() {
    let iface = typecheck_and_extract(
        "pub fun add(x: Int, y: Int) -> Int = x + y\nfun private_helper(x: Int) -> Int = x",
    );
    assert!(
        iface.exported_fns.iter().any(|f| f.name == "add"),
        "expected 'add' in exported_fns"
    );
    assert!(
        !iface
            .exported_fns
            .iter()
            .any(|f| f.name == "private_helper"),
        "private_helper should not be in exported_fns"
    );
}

#[test]
fn extract_interface_pub_fn_key_is_function() {
    let iface = typecheck_and_extract("pub fun add(x: Int, y: Int) -> Int = x + y");
    let f = iface.exported_fns.iter().find(|f| f.name == "add").unwrap();
    assert_eq!(f.key, LocalSymbolKey::Function("add".into()));
}

#[test]
fn extract_interface_record_type() {
    let iface = typecheck_and_extract("pub type Point = { x: Int, y: Int }");
    let t = iface
        .exported_types
        .iter()
        .find(|t| t.name == "Point")
        .expect("Point should be in exported_types");
    assert_eq!(t.key, LocalSymbolKey::Type("Point".into()));
    match &t.kind {
        TypeSummaryKind::Record { fields } => {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "x");
            assert_eq!(fields[1].0, "y");
        }
        _ => panic!("expected Record kind"),
    }
}

#[test]
fn extract_interface_sum_type() {
    let iface = typecheck_and_extract("pub type Color = Red | Green | Blue");
    let t = iface
        .exported_types
        .iter()
        .find(|t| t.name == "Color")
        .expect("Color should be in exported_types");
    assert_eq!(t.key, LocalSymbolKey::Type("Color".into()));
    match &t.kind {
        TypeSummaryKind::Sum { variants } => {
            assert_eq!(variants.len(), 3);
            assert_eq!(variants[0].name, "Red");
            assert_eq!(
                variants[0].key,
                LocalSymbolKey::Constructor {
                    parent_type: "Color".into(),
                    name: "Red".into(),
                }
            );
        }
        _ => panic!("expected Sum kind"),
    }
}

#[test]
fn extract_interface_private_type_excluded() {
    let iface = typecheck_and_extract(
        "type Internal = { val: Int }\npub fun make() -> Internal = Internal { val = 0 }",
    );
    assert!(
        !iface.exported_types.iter().any(|t| t.name == "Internal"),
        "private type should not be in exported_types"
    );
}

#[test]
fn extract_interface_opaque_type() {
    let iface = typecheck_and_extract("pub opaque type Secret = { inner: Int }");
    let t = iface
        .exported_types
        .iter()
        .find(|t| t.name == "Secret")
        .expect("Secret should be in exported_types");
    assert_eq!(t.visibility, krypton_parser::ast::Visibility::Opaque);
}

#[test]
fn extract_interface_extern_alias_is_opaque() {
    let iface = typecheck_and_extract(r#"extern js "./ffi.mjs" as pub Blob[a] {}"#);
    let t = iface
        .exported_types
        .iter()
        .find(|t| t.name == "Blob")
        .expect("Blob should be in exported_types");
    assert_eq!(t.visibility, krypton_parser::ast::Visibility::Opaque);
    assert!(matches!(t.kind, TypeSummaryKind::Opaque));
}

#[test]
fn extract_interface_constructors_as_exported_fns() {
    let iface = typecheck_and_extract("pub type Color = Red | Green | Blue");
    let red = iface
        .exported_fns
        .iter()
        .find(|f| f.name == "Red")
        .expect("Red constructor should be in exported_fns");
    assert_eq!(
        red.key,
        LocalSymbolKey::Constructor {
            parent_type: "Color".into(),
            name: "Red".into(),
        }
    );
}

#[test]
fn extract_interface_record_constructor_as_exported_fn() {
    let iface = typecheck_and_extract("pub type Point = { x: Int, y: Int }");
    let ctor = iface
        .exported_fns
        .iter()
        .find(|f| f.name == "Point")
        .expect("Point constructor should be in exported_fns");
    assert_eq!(
        ctor.key,
        LocalSymbolKey::Constructor {
            parent_type: "Point".into(),
            name: "Point".into(),
        }
    );
}

#[test]
fn extract_interface_trait() {
    let src = r#"
pub trait Describable[a] {
    fun describe(x: a) -> String
}
"#;
    let iface = typecheck_and_extract(src);
    let t = iface
        .exported_traits
        .iter()
        .find(|t| t.name == "Describable")
        .expect("Describable should be in exported_traits");
    assert_eq!(t.key, LocalSymbolKey::Trait("Describable".into()));
    assert_eq!(t.methods.len(), 1);
    assert_eq!(t.methods[0].name, "describe");
}

#[test]
fn extract_interface_instance_no_bodies() {
    let src = r#"
import core/show.{Show, show}
pub type Color = Red | Green | Blue
impl Show[Color] {
    fun show(c: Color) -> String = match c {
        Red => "Red",
        Green => "Green",
        Blue => "Blue",
    }
}
"#;
    let iface = typecheck_and_extract(src);
    let inst = iface
        .exported_instances
        .iter()
        .find(|i| i.target_type_name == "Color")
        .expect("Show[Color] instance should be in exported_instances");
    assert_eq!(
        inst.key,
        LocalSymbolKey::Instance {
            trait_name: "Show".into(),
            target_type: "Color".into(),
        }
    );
    assert!(!inst.method_summaries.is_empty());
    assert_eq!(inst.method_summaries[0].name, "show");
}

#[test]
fn extract_interface_extern_fn() {
    let src = r#"
extern java "java.lang.Math" {
    pub fun abs(n: Int) -> Int
}
"#;
    let iface = typecheck_and_extract(src);
    let ef = iface
        .extern_fns
        .iter()
        .find(|e| e.name == "abs")
        .expect("abs should be in extern_fns");
    assert_eq!(ef.declaring_module, ModulePath::new("test"));
    assert_eq!(ef.host_module_path, "java.lang.Math");
}

#[test]
fn extract_interface_no_transitive_deps() {
    let iface = extract_multi(
        "import mylib.{helper}\nfun main() = helper()",
        vec![
            (
                "mylib",
                "import innerlib.{inner}\npub fun helper() -> Int = inner()",
            ),
            ("innerlib", "pub fun inner() -> Int = 42"),
        ],
    );
    let dep_names: Vec<&str> = iface.direct_deps.iter().map(|d| d.as_str()).collect();
    assert!(
        dep_names.contains(&"mylib"),
        "should have mylib as direct dep"
    );
    assert!(
        !dep_names.contains(&"innerlib"),
        "should NOT have innerlib as direct dep"
    );
}

// ===========================================================================
// Multi-module: reexport tests
// ===========================================================================

#[test]
fn extract_interface_reexported_fn_has_canonical_ref() {
    let iface = extract_multi(
        "pub import mylib.{helper}",
        vec![("mylib", "pub fun helper() -> Int = 42")],
    );
    let reex = iface
        .reexported_fns
        .iter()
        .find(|f| f.local_name == "helper")
        .expect("helper should be in reexported_fns");
    assert_eq!(reex.canonical_ref.module, ModulePath::new("mylib"));
    assert_eq!(
        reex.canonical_ref.symbol,
        LocalSymbolKey::Function("helper".into())
    );
}

#[test]
fn extract_interface_reexported_type_preserves_origin() {
    let iface = extract_multi(
        "pub import mylib.{Color, Red, Green, Blue}",
        vec![("mylib", "pub type Color = Red | Green | Blue")],
    );
    let reex = iface
        .reexported_types
        .iter()
        .find(|t| t.local_name == "Color")
        .expect("Color should be in reexported_types");
    assert_eq!(reex.canonical_ref.module, ModulePath::new("mylib"));
}

#[test]
fn extract_interface_direct_deps() {
    let iface = extract_multi(
        "import mylib_a.{a_fn}\nimport mylib_b.{b_fn}\nfun main() = a_fn() + b_fn()",
        vec![
            ("mylib_a", "pub fun a_fn() -> Int = 1"),
            ("mylib_b", "pub fun b_fn() -> Int = 2"),
        ],
    );
    let dep_names: Vec<&str> = iface.direct_deps.iter().map(|d| d.as_str()).collect();
    assert!(dep_names.contains(&"mylib_a"));
    assert!(dep_names.contains(&"mylib_b"));
}

// ===========================================================================
// Snapshot tests
// ===========================================================================

#[test]
fn extract_interface_snapshot_basic() {
    let src = r#"
import core/show.{Show, show}

pub type Color = Red | Green | Blue

pub type Point = { x: Int, y: Int }

pub fun origin() -> Point = Point { x = 0, y = 0 }

pub fun add(x: Int, y: Int) -> Int = x + y

impl Show[Color] {
    fun show(c: Color) -> String = match c {
        Red => "Red",
        Green => "Green",
        Blue => "Blue",
    }
}
"#;
    let iface = typecheck_and_extract(src);
    insta::assert_snapshot!(display_interface(&iface));
}

#[test]
fn extract_interface_snapshot_reexport() {
    let iface = extract_multi(
        r#"
import mylib.{helper, Color, Red, Green, Blue}
pub import mylib.{helper, Color, Red, Green, Blue}

pub fun use_it() -> Int = helper()
"#,
        vec![(
            "mylib",
            "pub type Color = Red | Green | Blue\npub fun helper() -> Int = 42",
        )],
    );
    insta::assert_snapshot!(display_interface(&iface));
}
