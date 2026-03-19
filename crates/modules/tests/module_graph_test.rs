use std::collections::HashMap;

use krypton_modules::module_graph::{build_module_graph, ModuleGraphError};
use krypton_modules::module_resolver::ModuleResolver;

/// Test resolver that returns source from a map.
struct MapResolver {
    modules: HashMap<String, String>,
}

impl MapResolver {
    fn new(modules: Vec<(&str, &str)>) -> Self {
        Self {
            modules: modules.into_iter().map(|(k, v)| (k.to_string(), v.to_string())).collect(),
        }
    }
}

impl ModuleResolver for MapResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        self.modules.get(module_path).cloned()
    }
}

fn parse(source: &str) -> krypton_parser::ast::Module {
    let (module, errors) = krypton_parser::parser::parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    module
}

#[test]
fn graph_single_import() {
    let resolver = MapResolver::new(vec![
        ("mylib", "pub fun add(x: Int, y: Int) -> Int = x + y"),
    ]);
    let root = parse("import mylib.{add}\nfun main() -> Int = add(1, 2)");
    let graph = build_module_graph(&root, &resolver).unwrap();

    // Should contain prelude tree + mylib
    let user_modules: Vec<&str> = graph.modules.iter()
        .filter(|m| !m.path.starts_with("core/") && m.path != "prelude")
        .map(|m| m.path.as_str())
        .collect();
    assert_eq!(user_modules, vec!["mylib"]);
}

#[test]
fn graph_transitive_imports() {
    let resolver = MapResolver::new(vec![
        ("a", "import b.{foo}\npub fun bar() -> Int = foo()"),
        ("b", "import c.{baz}\npub fun foo() -> Int = baz()"),
        ("c", "pub fun baz() -> Int = 42"),
    ]);
    let root = parse("import a.{bar}\nfun main() -> Int = bar()");
    let graph = build_module_graph(&root, &resolver).unwrap();

    let user_modules: Vec<&str> = graph.modules.iter()
        .filter(|m| !m.path.starts_with("core/") && m.path != "prelude")
        .map(|m| m.path.as_str())
        .collect();
    // Topological order: c before b before a
    assert_eq!(user_modules, vec!["c", "b", "a"]);
}

#[test]
fn graph_diamond_dedup() {
    let resolver = MapResolver::new(vec![
        ("b", "import d.{x}\npub fun fb() -> Int = x()"),
        ("c", "import d.{x}\npub fun fc() -> Int = x()"),
        ("d", "pub fun x() -> Int = 1"),
    ]);
    let root = parse("import b.{fb}\nimport c.{fc}\nfun main() -> Int = fb() + fc()");
    let graph = build_module_graph(&root, &resolver).unwrap();

    let user_modules: Vec<&str> = graph.modules.iter()
        .filter(|m| !m.path.starts_with("core/") && m.path != "prelude")
        .map(|m| m.path.as_str())
        .collect();
    // d appears only once, before b and c
    assert_eq!(user_modules.iter().filter(|&&m| m == "d").count(), 1);
    let d_pos = user_modules.iter().position(|&m| m == "d").unwrap();
    let b_pos = user_modules.iter().position(|&m| m == "b").unwrap();
    let c_pos = user_modules.iter().position(|&m| m == "c").unwrap();
    assert!(d_pos < b_pos);
    assert!(d_pos < c_pos);
}

#[test]
fn graph_cycle_detection() {
    let resolver = MapResolver::new(vec![
        ("a", "import b.{y}\npub fun x() -> Int = y()"),
        ("b", "import a.{x}\npub fun y() -> Int = x()"),
    ]);
    let root = parse("import a.{x}\nfun main() -> Int = x()");
    let result = build_module_graph(&root, &resolver);

    assert!(result.is_err());
    match result.unwrap_err() {
        ModuleGraphError::CircularImport { cycle, .. } => {
            assert!(cycle.contains(&"a".to_string()));
            assert!(cycle.contains(&"b".to_string()));
        }
        other => panic!("expected CircularImport, got {other:?}"),
    }
}

#[test]
fn graph_unknown_module() {
    let resolver = MapResolver::new(vec![]);
    let root = parse("import nonexistent.{foo}\nfun main() -> Int = foo()");
    let result = build_module_graph(&root, &resolver);

    assert!(result.is_err());
    match result.unwrap_err() {
        ModuleGraphError::UnknownModule { path, .. } => {
            assert_eq!(path, "nonexistent");
        }
        other => panic!("expected UnknownModule, got {other:?}"),
    }
}

#[test]
fn graph_bare_import() {
    let resolver = MapResolver::new(vec![
        ("foo", "pub fun bar() -> Int = 1"),
    ]);
    let root = parse("import foo\nfun main() -> Int = 1");
    let graph = build_module_graph(&root, &resolver).unwrap();

    let user_modules: Vec<&str> = graph.modules.iter()
        .filter(|m| !m.path.starts_with("core/") && m.path != "prelude")
        .map(|m| m.path.as_str())
        .collect();
    assert_eq!(user_modules, vec!["foo"]);
}

#[test]
fn graph_prelude_included() {
    let resolver = MapResolver::new(vec![]);
    let root = parse("fun main() -> Int = 42");
    let graph = build_module_graph(&root, &resolver).unwrap();

    let paths: Vec<&str> = graph.modules.iter().map(|m| m.path.as_str()).collect();
    assert!(paths.contains(&"prelude"), "prelude should be in graph");
    assert!(paths.contains(&"core/option"), "core/option should be in graph");
    assert!(paths.contains(&"core/result"), "core/result should be in graph");
    assert!(paths.contains(&"core/list"), "core/list should be in graph");
    assert!(paths.contains(&"core/ordering"), "core/ordering should be in graph");

    // Prelude should come after its deps
    let prelude_pos = paths.iter().position(|&p| p == "prelude").unwrap();
    let option_pos = paths.iter().position(|&p| p == "core/option").unwrap();
    assert!(option_pos < prelude_pos, "core/option should come before prelude");
}

#[test]
fn graph_parse_error_in_import() {
    let resolver = MapResolver::new(vec![
        ("bad", "fun broken( -> Int = 1"), // invalid syntax
    ]);
    let root = parse("import bad.{broken}\nfun main() -> Int = broken()");
    let result = build_module_graph(&root, &resolver);

    assert!(result.is_err());
    match result.unwrap_err() {
        ModuleGraphError::ParseError { path, errors, .. } => {
            assert_eq!(path, "bad");
            assert!(!errors.is_empty(), "should have parse error details");
        }
        other => panic!("expected ParseError, got {other:?}"),
    }
}
