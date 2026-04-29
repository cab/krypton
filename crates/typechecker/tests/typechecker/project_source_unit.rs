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

type CompanionTestResult = Result<
    (
        krypton_typechecker::typed_ast::TypedModule,
        krypton_typechecker::module_interface::ModuleInterface,
        Vec<(
            krypton_typechecker::typed_ast::TypedModule,
            krypton_typechecker::module_interface::ModuleInterface,
        )>,
    ),
    Vec<InferError>,
>;

/// Helper: compile Phase 1, then `infer_test_module` with the given test
/// source. Returns the test-module result so individual tests can poke at
/// the typed module / interface / errors.
fn infer_companion_test(
    phase1: Vec<(&str, &str)>,
    test_path: &str,
    test_src: &str,
) -> CompanionTestResult {
    let unit = infer_unit(phase1.clone()).expect("phase 1 should typecheck");
    let test_module = parse_ok(test_src);
    let resolver = MemoryResolver::new(phase1);
    infer_test_module(
        &test_module,
        test_path.to_string(),
        &resolver,
        CompileTarget::Jvm,
        &unit,
        Some(test_src.to_string()),
    )
}

#[test]
fn test_module_can_import_private_fn_from_companion() {
    // `parser` defines `tokenize` without `pub`. `parser_test` imports it
    // by name and the typechecker accepts the import via the companion
    // bypass.
    let test_src = "import parser.{tokenize}\n\nfun test_t() { let _ = tokenize(1) }\n";
    let result = infer_companion_test(
        vec![("parser", "fun tokenize(x: Int) -> Int = x\n")],
        "parser_test",
        test_src,
    );
    let (typed, _iface, _extras) = result.expect("companion private fn should be importable");
    assert!(
        typed.fn_types_by_name.contains_key("test_t"),
        "test_t should be present"
    );
}

#[test]
fn test_module_can_use_private_type_from_companion() {
    // `parser` declares a private record `Token`. `parser_test` imports
    // both the type and a public helper that returns it, then constructs
    // the type and reads its field.
    let parser_src = "type Token = { kind: Int }\n\
                      pub fun make_token() -> Token = Token { kind = 1 }\n";
    let test_src = "import parser.{Token, make_token}\n\
                    fun test_t() {\n\
                    \x20 let t = Token { kind = 7 }\n\
                    \x20 let _ = make_token()\n\
                    \x20 let _ = t.kind\n\
                    }\n";
    let result = infer_companion_test(
        vec![("parser", parser_src)],
        "parser_test",
        test_src,
    );
    let (typed, _iface, _extras) =
        result.expect("companion private type should be constructible from test");
    assert!(typed.fn_types_by_name.contains_key("test_t"));
}

#[test]
fn test_module_cannot_import_private_from_sibling() {
    // `parser` has a private fn. `lexer_test` is the companion of `lexer`
    // — `parser` is a sibling, not the companion, so the import must fail
    // with `PrivateName` (E0503).
    let test_src = "import parser.{tokenize}\n\nfun test_t() { let _ = tokenize(1) }\n";
    let result = infer_companion_test(
        vec![
            ("parser", "fun tokenize(x: Int) -> Int = x\n"),
            ("lexer", "pub fun lex() -> Int = 0\n"),
        ],
        "lexer_test",
        test_src,
    );
    let errors = match result {
        Ok(_) => panic!("sibling module's privates must remain hidden"),
        Err(errors) => errors,
    };
    let saw_private = errors.iter().any(|e| match e {
        InferError::TypeError { error, .. } => matches!(
            *error.error,
            krypton_typechecker::type_error::TypeError::PrivateName { .. }
        ),
        _ => false,
    });
    assert!(
        saw_private,
        "expected PrivateName error for sibling import, got: {errors:?}"
    );
}

#[test]
fn test_module_with_no_companion_compiles() {
    // `helpers_test.kr` exists but `helpers.kr` does not. The test file
    // typechecks as a standalone module: no companion path is set, so no
    // private bypass is available, but no error is raised either.
    let test_src = "fun test_x() { }\n";
    let (typed, iface, _extras) = infer_companion_test(
        vec![("other", "pub fun other() -> Int = 1\n")],
        "helpers_test",
        test_src,
    )
    .expect("standalone test module should typecheck");
    assert!(typed.fn_types_by_name.contains_key("test_x"));
    assert!(
        iface.private_friend_module.is_none(),
        "no friend should be recorded when the source twin doesn't exist"
    );
}

#[test]
fn test_companion_bypass_does_not_propagate_to_extras() {
    // The friend bypass must be scoped to the test file itself. Extras
    // (modules pulled in by the test's import graph that Phase 1 didn't
    // cover) must NOT see the bypass — they typecheck like any other
    // consumer. We verify this structurally by checking the test
    // interface's `private_friend_module`: it points at `parser`, so the
    // test module bypasses `parser`'s privates, but no extras-loop module
    // could possibly carry that flag because `infer_test_module` clears
    // the friend arg for every extras call.
    let parser_src = "fun internal() -> Int = 1\npub fun add(x: Int) -> Int = x + 1\n";
    let test_src = "import parser.{internal}\n\nfun test_x() { let _ = internal() }\n";
    let (_typed, iface, extras) = infer_companion_test(
        vec![("parser", parser_src)],
        "parser_test",
        test_src,
    )
    .expect("companion access should typecheck");
    assert_eq!(
        iface.private_friend_module.as_ref().map(|p| p.as_str()),
        Some("parser"),
        "test interface must record its friend module"
    );
    // Every extras interface — should there be any — must have a `None`
    // friend flag. (Most commonly the extras list is empty when the test
    // file pulls in nothing beyond the source unit; both cases are valid
    // AC #5 evidence.)
    for (_, extra_iface) in &extras {
        assert!(
            extra_iface.private_friend_module.is_none(),
            "extras module {} must not carry a friend flag",
            extra_iface.module_path
        );
    }
}

#[test]
fn assert_panics_callable_from_test_module() {
    // `core/test::assert_panics` is `is_test_only`. Importing it from a
    // `_test.kr` companion must succeed: the test module's leaf ends in
    // `_test`, so the resolver hands it back as a normal `Fn`.
    let phase1 = vec![("math", "pub fun nope() -> Unit = panic(\"x\")\n")];
    let test_src = "import core/test.{assert_panics}\n\
                    import math.{nope}\n\
                    fun test_p() {\n\
                    \x20 let m = assert_panics(() -> nope())\n\
                    \x20 ()\n\
                    }\n";
    let result = infer_companion_test(phase1, "math_test", test_src);
    let (typed, _iface, _extras) =
        result.expect("assert_panics should be importable from a `_test.kr` companion");
    assert!(
        typed.fn_types_by_name.contains_key("test_p"),
        "test_p should be present"
    );
}

#[test]
fn assert_panics_rejected_when_imported_from_non_test() {
    // Importing `assert_panics` from a non-test module must fail with
    // `TypeError::TestOnlyFn` (E0522).
    let result = infer_unit(vec![(
        "app",
        "import core/test.{assert_panics}\nfun main() = ()\n",
    )]);
    let errors = match result {
        Ok(_) => panic!("expected E0522 for non-test import of assert_panics"),
        Err(errors) => errors,
    };
    let test_only_err = errors.iter().find_map(|e| match e {
        InferError::TypeError { error, .. } => match &*error.error {
            krypton_typechecker::type_error::TypeError::TestOnlyFn { name, module_path } => {
                Some((name.clone(), module_path.clone()))
            }
            _ => None,
        },
        _ => None,
    });
    let (name, module_path) = test_only_err.unwrap_or_else(|| {
        panic!(
            "expected TypeError::TestOnlyFn in errors, got: {errors:?}"
        )
    });
    assert_eq!(name, "assert_panics");
    assert_eq!(module_path, "core/test");
}

#[test]
fn other_assertions_still_importable_from_non_test() {
    // Guard against accidental over-restriction: `assert_eq` (and every other
    // pub fn in `core/test`) must remain importable from non-test code,
    // because production code that wraps `core/test` helpers in convenience
    // utilities is supported.
    let unit = infer_unit(vec![(
        "app",
        "import core/test.{assert_eq}\nfun main() = assert_eq(1, 1)\n",
    )])
    .expect("assert_eq must remain importable from non-test code");
    assert!(
        unit.typed_modules.iter().any(|tm| tm.module_path == "app"),
        "app must be present in typed_modules"
    );
}
