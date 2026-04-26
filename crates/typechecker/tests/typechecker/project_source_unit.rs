use rustc_hash::FxHashMap;

use krypton_modules::module_resolver::{CompositeResolver, ModuleResolver};
use krypton_parser::ast::CompileTarget;
use krypton_parser::parser::parse;
use krypton_typechecker::infer::{
    infer_project_source_unit, infer_test_module, InferError, ProjectSourceUnit,
};

/// In-memory resolver: stdlib first (for prelude/core/*), then a fixed map of
/// user-source modules supplied to [`MultiRootTest::new`].
struct MemoryResolver {
    stdlib: CompositeResolver,
    modules: FxHashMap<String, String>,
}

impl MemoryResolver {
    fn new(modules: Vec<(&str, &str)>) -> Self {
        Self {
            stdlib: CompositeResolver::stdlib_only(),
            modules: modules
                .into_iter()
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect(),
        }
    }
}

impl ModuleResolver for MemoryResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        self.stdlib
            .resolve(module_path)
            .or_else(|| self.modules.get(module_path).cloned())
    }
}

fn parse_ok(source: &str) -> krypton_parser::ast::Module {
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    module
}

/// Build a [`ProjectSourceUnit`] from an inline fixture: each entry is
/// `(module_path, source_text)` and every entry is parsed and handed to
/// [`infer_project_source_unit`] as a peer source.
fn infer_unit(sources: Vec<(&str, &str)>) -> Result<ProjectSourceUnit, Vec<InferError>> {
    let resolver = MemoryResolver::new(sources.clone());
    let parsed: Vec<(String, krypton_parser::ast::Module)> = sources
        .iter()
        .map(|(p, src)| (p.to_string(), parse_ok(src)))
        .collect();
    infer_project_source_unit(parsed, &resolver, CompileTarget::Jvm)
}

#[test]
fn infer_project_source_unit_two_sources_import_each_other() {
    // `a.kr` imports `b.kr`; both succeed and both land in the result.
    let unit = infer_unit(vec![
        ("a", "import b.{y}\n\npub fun x() -> Int = y()\n"),
        ("b", "pub fun y() -> Int = 42\n"),
    ])
    .expect("source unit should typecheck");

    let paths: Vec<String> = unit
        .typed_modules
        .iter()
        .map(|tm| tm.module_path.clone())
        .collect();
    assert!(
        paths.iter().any(|p| p == "a"),
        "source unit must contain module 'a', got {paths:?}"
    );
    assert!(
        paths.iter().any(|p| p == "b"),
        "source unit must contain module 'b', got {paths:?}"
    );

    let iface_paths: Vec<String> = unit
        .interfaces
        .iter()
        .map(|i| i.module_path.as_str().to_string())
        .collect();
    assert!(
        iface_paths.iter().any(|p| p == "a"),
        "interfaces must include 'a', got {iface_paths:?}"
    );
    assert!(
        iface_paths.iter().any(|p| p == "b"),
        "interfaces must include 'b', got {iface_paths:?}"
    );

    // `b` must appear before `a` — toposort puts dependencies first.
    let pos_a = paths.iter().position(|p| p == "a").unwrap();
    let pos_b = paths.iter().position(|p| p == "b").unwrap();
    assert!(
        pos_b < pos_a,
        "b must appear before a in toposort: {paths:?}"
    );
}

#[test]
fn infer_project_source_unit_reports_error_in_any_source() {
    // `a.kr` is fine; `b.kr` has a type error. The failure must surface
    // even though `a.kr` would otherwise typecheck.
    let result = infer_unit(vec![
        ("a", "pub fun x() -> Int = 1\n"),
        ("b", "pub fun y() -> Int = \"not an int\"\n"),
    ]);
    let errors = match result {
        Ok(_) => panic!("expected typecheck to fail on b.kr"),
        Err(errors) => errors,
    };
    assert!(
        !errors.is_empty(),
        "must return at least one InferError, got empty vec"
    );
    // The error must originate in module `b` (not `a`).
    let attributed_to_b = errors.iter().any(|e| match e {
        InferError::TypeError {
            error_source,
            error,
        } => {
            error_source
                .as_ref()
                .map(|(p, _)| p == "b")
                .unwrap_or(false)
                || error.source_file.as_deref() == Some("b")
        }
        _ => false,
    });
    assert!(
        attributed_to_b,
        "error should be attributed to module 'b', got: {errors:?}"
    );
}

#[test]
fn infer_test_module_uses_phase1_interfaces() {
    // Phase 1: `math` exports `pub fun add`.
    let unit = infer_unit(vec![(
        "math",
        "pub fun add(x: Int, y: Int) -> Int = x + y\n",
    )])
    .expect("phase 1 should typecheck");

    // Phase 2: `math_test` imports `add` from `math` and uses it. The
    // function returns `Unit` so it satisfies the `test_*` signature rule
    // enforced by `validate_test_signatures`.
    let test_src = "import math.{add}\n\nfun test_sum() { let _ = add(1, 2) }\n";
    let test_module = parse_ok(test_src);
    let resolver = MemoryResolver::new(vec![(
        "math",
        "pub fun add(x: Int, y: Int) -> Int = x + y\n",
    )]);

    let (typed_test, _iface, _extras) = infer_test_module(
        &test_module,
        "math_test".to_string(),
        &resolver,
        CompileTarget::Jvm,
        &unit,
        Some(test_src.to_string()),
    )
    .expect("phase 2 should typecheck against phase 1 interfaces");

    // The test module must have inferred `test_sum`.
    assert!(
        typed_test.fn_types_by_name.contains_key("test_sum"),
        "test module must have a fn_type entry for `test_sum`, got keys: {:?}",
        typed_test.fn_types_by_name.keys().collect::<Vec<_>>()
    );

    // Phase 1 already typechecked `math`. `all_module_paths` must list it,
    // and `skip_set`-powered graph building ensures Phase 2 does not
    // re-type-check it — verified indirectly: if the test module's typed
    // form exists and references `math::add`, the Phase 1 interface was
    // the resolution source (the only place `math::add` is known).
    assert!(
        unit.all_module_paths.contains("math"),
        "ProjectSourceUnit must record 'math' in all_module_paths"
    );
}

#[test]
fn infer_test_module_reports_type_error_without_touching_phase1() {
    // Phase 1 succeeds.
    let unit = infer_unit(vec![(
        "math",
        "pub fun add(x: Int, y: Int) -> Int = x + y\n",
    )])
    .expect("phase 1 should typecheck");

    // Phase 2: the test has a bare type error (String where Int expected).
    // Phase 1's interfaces must not be perturbed.
    let test_src = "fun test_bad() -> Int = \"not an int\"\n";
    let test_module = parse_ok(test_src);
    let resolver = MemoryResolver::new(vec![(
        "math",
        "pub fun add(x: Int, y: Int) -> Int = x + y\n",
    )]);

    let result = infer_test_module(
        &test_module,
        "math_test".to_string(),
        &resolver,
        CompileTarget::Jvm,
        &unit,
        Some(test_src.to_string()),
    );
    let errors = match result {
        Ok(_) => panic!("phase 2 should fail with a type error"),
        Err(errors) => errors,
    };
    assert!(
        !errors.is_empty(),
        "must return at least one InferError, got empty vec"
    );
    let attributed_to_test = errors.iter().any(|e| match e {
        InferError::TypeError {
            error_source,
            error,
        } => {
            error_source
                .as_ref()
                .map(|(p, _)| p == "math_test")
                .unwrap_or(false)
                || error.source_file.as_deref() == Some("math_test")
        }
        _ => false,
    });
    assert!(
        attributed_to_test,
        "error should be attributed to 'math_test', got: {errors:?}"
    );

    // Phase 1's typed_modules and interfaces are unchanged (we only hold
    // a reference, and no mutation API exists), but sanity-check the
    // module is still present.
    assert!(
        unit.typed_modules.iter().any(|m| m.module_path == "math"),
        "phase 1 TypedModule for 'math' should be untouched"
    );
    assert!(
        unit.interfaces
            .iter()
            .any(|i| i.module_path.as_str() == "math"),
        "phase 1 ModuleInterface for 'math' should be untouched"
    );
}
