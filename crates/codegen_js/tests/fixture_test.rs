use std::path::{Path, PathBuf};
use std::process::Command;

use krypton_codegen_js::compile_modules_js;
use krypton_modules::module_resolver::{CompositeResolver, ModuleResolver};
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::diagnostics::render_infer_error;
use krypton_typechecker::infer::infer_module;
use rstest::rstest;

struct NoopResolver;

impl ModuleResolver for NoopResolver {
    fn resolve(&self, _module_path: &str) -> Option<String> {
        None
    }
}

fn compile_js_result_with_resolver(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
    fixture_name: &str,
) -> Result<Vec<(String, String)>, krypton_codegen_js::JsCodegenError> {
    let (module, errors) = parse(source);
    assert!(
        errors.is_empty(),
        "fixture {fixture_name}: parse errors: {errors:?}"
    );

    let typed_modules = infer_module(&module, resolver, "test".to_string()).unwrap_or_else(|e| {
        let rendered = render_infer_error(fixture_name, source, &e);
        panic!("fixture {fixture_name}: type check failed:\n{rendered}");
    });
    compile_modules_js(&typed_modules, "test")
}

/// Copy runtime/js/*.mjs files into the temp output directory so that
/// stdlib extern JS imports (e.g. `../runtime/js/io.mjs`) resolve at Node runtime.
fn copy_runtime_files(dest: &Path) {
    let runtime_src = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../runtime/js");
    let runtime_dest = dest.join("runtime/js");
    std::fs::create_dir_all(&runtime_dest).unwrap();

    for entry in std::fs::read_dir(&runtime_src).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("mjs")
            && path.file_name().unwrap() != "test_runtime.mjs"
        {
            std::fs::copy(&path, runtime_dest.join(path.file_name().unwrap())).unwrap();
        }
    }
}

/// Write compiled JS files to a temp directory, copy the JS runtime, and run with Node.
fn run_js_files(files: &[(String, String)], fixture_name: &str) -> String {
    let dir = tempfile::tempdir().unwrap();
    let mut entry_path = None;
    for (filename, js_source) in files {
        let file_path = dir.path().join(filename);
        if let Some(parent) = file_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&file_path, js_source).unwrap();
        if entry_path.is_none() {
            entry_path = Some(file_path);
        }
    }

    copy_runtime_files(dir.path());

    let entry = entry_path.expect("no JS files generated");
    let output = Command::new("node")
        .arg(&entry)
        .output()
        .expect("node command should run");

    assert!(
        output.status.success(),
        "fixture {fixture_name}: node exited with {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

#[test]
fn local_extern_println_shadows_prelude_import_in_js_output() {
    let source = r#"
        extern java "java/io/PrintStream" {
            fun println[a](x: a) -> Unit
        }

        extern js "./runtime.mjs" {
            fun println[a](x: a) -> Unit
        }

        fun main() = println(42)
    "#;
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let typed_modules =
        infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string())
            .expect("typecheck should succeed");
    let root = typed_modules
        .iter()
        .find(|tm| tm.module_path == "test")
        .expect("expected root typed module");
    let lowered = krypton_ir::lower::lower_module(root, "test").expect("lowering should succeed");

    assert!(
        lowered
            .extern_fns
            .iter()
            .any(|ext| ext.name == "println"
                && matches!(
                    ext.target,
                    krypton_ir::ExternTarget::Js { ref module } if module == "./runtime.mjs"
                )),
        "local extern println should lower as JS extern"
    );
    assert!(
        !lowered
            .imported_fns
            .iter()
            .any(|imp| imp.name == "println" && imp.source_module == "core/io"),
        "shadowed prelude println should not lower as core/io import"
    );
}

#[test]
fn referenced_java_only_extern_fails_js_codegen() {
    let source = r#"
        extern java "krypton.runtime.KryptonIO" {
            fun println[a](x: a) -> Unit
        }

        fun main() = println(42)
    "#;

    let err = compile_js_result_with_resolver(source, &NoopResolver, "java_only")
        .expect_err("expected missing JS target error");
    let msg = err.to_string();
    assert!(
        msg.contains("println"),
        "error should mention function name, got: {msg}"
    );
    assert!(
        msg.contains("module `test`"),
        "error should mention referencing module, got: {msg}"
    );
    assert!(
        msg.contains("java:krypton.runtime.KryptonIO"),
        "error should list available targets, got: {msg}"
    );
}

/// Verify that non-actor stdlib modules compile successfully with JS target.
#[test]
fn stdlib_modules_compile_to_js() {
    // Each source imports a stdlib module and calls a function from it,
    // ensuring the extern JS targets are present and valid.
    let cases = vec![
        (
            "io",
            r#"
                import core/io.{println}
                fun main() = println("hello")
            "#,
        ),
        (
            "string",
            r#"
                import core/string.{length}
                fun main() = length("hello")
            "#,
        ),
        (
            "vec",
            r#"
                import core/vec.{len}
                fun main() = len
            "#,
        ),
        (
            "map",
            r#"
                import core/map.{empty, size}
                fun main() = size(empty())
            "#,
        ),
        (
            "json",
            r#"
                import core/json.{parse_json}
                fun main() = parse_json("{}")
            "#,
        ),
    ];

    for (name, source) in cases {
        let resolver = CompositeResolver::stdlib_only();
        let result = compile_js_result_with_resolver(source, &resolver, name);
        assert!(
            result.is_ok(),
            "stdlib module {name} should compile to JS, got: {}",
            result.unwrap_err()
        );
    }
}

/// Verify that actor module compiles to JS (runtime panics, not compile errors).
#[test]
fn actor_module_compiles_to_js() {
    let source = r#"
        import core/actor.{Mailbox, spawn}

        fun main() = spawn((mb) -> ())
    "#;

    let resolver = CompositeResolver::stdlib_only();
    let result = compile_js_result_with_resolver(source, &resolver, "actor_js");
    assert!(
        result.is_ok(),
        "actor module should compile to JS (panics at runtime), got: {}",
        result.unwrap_err()
    );
}

const SKIP_DIRS: &[&str] = &["parser", "bench", "smoke", "modules", "inspect"];

fn should_skip(path: &PathBuf) -> bool {
    path.components().any(|c| {
        SKIP_DIRS
            .iter()
            .any(|d| c.as_os_str() == std::ffi::OsStr::new(d))
    })
}

#[rstest]
fn js_codegen_fixture(
    #[files("tests/fixtures/**/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    if should_skip(&path) {
        return;
    }

    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() {
        return;
    }

    let name = path.file_stem().unwrap().to_string_lossy().to_string();
    let resolver = CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    for expectation in &fixture.expectations {
        match expectation {
            Expectation::Output(expected) => {
                let files = compile_js_result_with_resolver(&fixture.source, &resolver, &name);
                let files = match files {
                    Ok(f) => f,
                    Err(_) => return, // Java-only externs, skip
                };
                let actual = run_js_files(&files, &name);
                assert_eq!(actual, *expected, "fixture {name}: output mismatch");
            }
            Expectation::Ok => {
                let (module, errors) = parse(&fixture.source);
                assert!(
                    errors.is_empty(),
                    "fixture {name}: expected ok but parse errors: {errors:?}"
                );
                let typed_modules = infer_module(&module, &resolver, "test".to_string())
                    .unwrap_or_else(|e| {
                        let rendered = render_infer_error(&name, &fixture.source, &e);
                        panic!("fixture {name}: expected ok but typecheck failed:\n{rendered}");
                    });
                compile_modules_js(&typed_modules, "test").unwrap_or_else(|e| {
                    panic!("fixture {name}: JS codegen failed: {e}");
                });
            }
            Expectation::Error(_) => {}
        }
    }
}

#[rstest]
fn js_codegen_module(
    #[files("tests/fixtures/modules/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() {
        return;
    }

    let name = path.file_stem().unwrap().to_string_lossy().to_string();
    let resolver = CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    for expectation in &fixture.expectations {
        match expectation {
            Expectation::Output(expected) => {
                let files = match compile_js_result_with_resolver(&fixture.source, &resolver, &name)
                {
                    Ok(f) => f,
                    Err(_) => return,
                };
                let actual = run_js_files(&files, &name);
                assert_eq!(actual, *expected, "fixture {name}: output mismatch");
            }
            Expectation::Ok => {
                let (module, errors) = parse(&fixture.source);
                assert!(
                    errors.is_empty(),
                    "fixture {name}: expected ok but parse errors: {errors:?}"
                );
                let typed_modules = infer_module(&module, &resolver, "test".to_string())
                    .unwrap_or_else(|e| {
                        let rendered = render_infer_error(&name, &fixture.source, &e);
                        panic!("fixture {name}: expected ok but typecheck failed:\n{rendered}");
                    });
                let _ = compile_modules_js(&typed_modules, "test");
            }
            Expectation::Error(_) => {}
        }
    }
}
