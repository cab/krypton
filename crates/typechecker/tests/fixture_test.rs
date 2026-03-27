use std::path::PathBuf;

use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::infer;
use rstest::rstest;

fn infer_module_snapshot(source: &str) -> Result<String, Vec<String>> {
    infer_module_snapshot_with_resolver(source, &CompositeResolver::stdlib_only())
}

fn infer_module_snapshot_with_resolver(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<String, Vec<String>> {
    let (module, errors) = parse(source);
    if !errors.is_empty() {
        return Err(vec![errors[0].code.to_string()]);
    }
    match infer::infer_module(&module, resolver, "test".to_string()) {
        Ok(modules) => {
            let lines: Vec<String> = modules[0]
                .fn_types
                .iter()
                .map(|e| format!("{}: {}", e.name, e.scheme))
                .collect();
            Ok(lines.join("\n"))
        }
        Err(infer_errors) => {
            let codes: Vec<String> = infer_errors
                .iter()
                .map(|e| match e {
                    infer::InferError::TypeError { error, .. } => {
                        error.error.error_code().to_string()
                    }
                    infer::InferError::ModuleParseError { .. } => "E0506".to_string(),
                })
                .collect();
            Err(codes)
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

    let expected_errors: Vec<&str> = fixture
        .expectations
        .iter()
        .filter_map(|e| match e {
            Expectation::Error(code) => Some(code.as_str()),
            _ => None,
        })
        .collect();

    if expected_errors.is_empty() {
        // Expect success
        for expectation in &fixture.expectations {
            if let Expectation::Ok = expectation {
                let result = infer_module_snapshot(&fixture.source);
                let snapshot = result.unwrap_or_else(|codes| {
                    panic!("fixture {name}: expected ok but got errors {codes:?}")
                });
                insta::assert_snapshot!(name.clone(), snapshot);
            }
        }
    } else {
        // Expect errors — check all expected codes appear in actual codes
        let result = infer_module_snapshot(&fixture.source);
        match result {
            Ok(ty) => {
                panic!("fixture {name}: expected errors {expected_errors:?} but inferred: {ty}")
            }
            Err(actual_codes) => {
                let mut remaining = actual_codes.clone();
                for expected in &expected_errors {
                    let pos = remaining.iter().position(|c| c == expected);
                    assert!(
                        pos.is_some(),
                        "fixture {name}: expected error {expected} not found in actual errors {actual_codes:?}"
                    );
                    remaining.remove(pos.unwrap());
                }
                assert_eq!(
                    actual_codes.len(),
                    expected_errors.len(),
                    "fixture {name}: expected {expected_errors:?} but got {actual_codes:?}"
                );
            }
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
    let resolver = CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    let expected_errors: Vec<&str> = fixture
        .expectations
        .iter()
        .filter_map(|e| match e {
            Expectation::Error(code) => Some(code.as_str()),
            _ => None,
        })
        .collect();

    if expected_errors.is_empty() {
        let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
        assert!(
            result.is_ok(),
            "fixture {name}: expected ok but got error {:?}",
            result.err()
        );
    } else {
        let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
        match result {
            Ok(ty) => {
                panic!("fixture {name}: expected errors {expected_errors:?} but inferred: {ty}")
            }
            Err(actual_codes) => {
                let mut remaining = actual_codes.clone();
                for expected in &expected_errors {
                    let pos = remaining.iter().position(|c| c == expected);
                    assert!(
                        pos.is_some(),
                        "fixture {name}: expected error {expected} not found in actual errors {actual_codes:?}"
                    );
                    remaining.remove(pos.unwrap());
                }
                assert_eq!(
                    actual_codes.len(),
                    expected_errors.len(),
                    "fixture {name}: expected {expected_errors:?} but got {actual_codes:?}"
                );
            }
        }
    }
}
