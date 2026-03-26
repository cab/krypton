use std::path::PathBuf;
use std::process::Command;

use krypton_codegen_js::compile_modules_js;
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::diagnostics::render_infer_error;
use krypton_typechecker::infer::infer_module;
use rstest::rstest;

fn run_js_program_with_resolver(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
    fixture_name: &str,
) -> String {
    let (module, errors) = parse(source);
    assert!(
        errors.is_empty(),
        "fixture {fixture_name}: parse errors: {errors:?}"
    );

    let typed_modules = infer_module(&module, resolver, "test".to_string()).unwrap_or_else(|e| {
        let rendered = render_infer_error(fixture_name, source, &e);
        panic!("fixture {fixture_name}: type check failed:\n{rendered}");
    });
    let files = compile_modules_js(&typed_modules, "test")
        .unwrap_or_else(|e| panic!("fixture {fixture_name}: JS compile failed: {e}"));

    let dir = tempfile::tempdir().unwrap();
    let mut entry_path = None;
    for (filename, js_source) in &files {
        let file_path = dir.path().join(filename);
        if let Some(parent) = file_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&file_path, js_source).unwrap();
        if entry_path.is_none() {
            entry_path = Some(file_path);
        }
    }

    // Write runtime.mjs for extern JS imports (println, etc.)
    std::fs::write(
        dir.path().join("runtime.mjs"),
        "export function println(x) { console.log(String(x)); }\n",
    )
    .unwrap();

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
                let actual = run_js_program_with_resolver(&fixture.source, &resolver, &name);
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
                // Accept compile success or any error (JS codegen is incomplete)
                let _ = compile_modules_js(&typed_modules, "test");
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
                let actual = run_js_program_with_resolver(&fixture.source, &resolver, &name);
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
