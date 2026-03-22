use std::path::PathBuf;

use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::infer;
use rstest::rstest;

fn infer_module_snapshot(source: &str) -> Result<String, String> {
    infer_module_snapshot_with_resolver(source, &CompositeResolver::stdlib_only())
}

fn infer_module_snapshot_with_resolver(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<String, String> {
    let (module, errors) = parse(source);
    if !errors.is_empty() {
        return Err(errors[0].code.to_string());
    }
    match infer::infer_module(&module, resolver) {
        Ok(modules) => {
            let lines: Vec<String> = modules[0]
                .fn_types
                .iter()
                .map(|e| format!("{}: {}", e.name, e.scheme))
                .collect();
            Ok(lines.join("\n"))
        }
        Err(e) => {
            let code = match &e {
                infer::InferError::TypeError { error, .. } => error.error.error_code().to_string(),
                infer::InferError::ModuleParseError { .. } => "E0506".to_string(),
            };
            Err(code)
        }
    }
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
fn typecheck_fixture(
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

    for expectation in &fixture.expectations {
        match expectation {
            Expectation::Ok => {
                let result = infer_module_snapshot(&fixture.source);
                let snapshot = result.unwrap_or_else(|code| {
                    panic!("fixture {name}: expected ok but got error {code}")
                });
                insta::assert_snapshot!(name.clone(), snapshot);
            }
            Expectation::Error(code) => {
                let result = infer_module_snapshot(&fixture.source);
                match result {
                    Ok(ty) => {
                        panic!("fixture {name}: expected error {code} but inferred: {ty}")
                    }
                    Err(actual_code) => {
                        assert_eq!(
                            &actual_code, code,
                            "fixture {name}: expected error {code} but got {actual_code}"
                        );
                    }
                }
            }
            Expectation::Output(_) => {}
        }
    }
}

#[rstest]
fn typecheck_module(
    #[files("tests/fixtures/modules/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() {
        return;
    }

    let name = path.file_stem().unwrap().to_string_lossy().to_string();
    let resolver =
        CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    for expectation in &fixture.expectations {
        match expectation {
            Expectation::Error(code) => {
                let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
                match result {
                    Ok(ty) => {
                        panic!("fixture {name}: expected error {code} but inferred: {ty}")
                    }
                    Err(actual_code) => {
                        assert_eq!(
                            &actual_code, code,
                            "fixture {name}: expected error {code} but got {actual_code}"
                        );
                    }
                }
            }
            _ => {
                let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
                assert!(
                    result.is_ok(),
                    "fixture {name}: expected ok but got error {:?}",
                    result.err()
                );
            }
        }
    }
}
