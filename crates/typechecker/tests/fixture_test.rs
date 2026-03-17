use std::path::Path;

use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};
use krypton_typechecker::infer;

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
        Err(e) => Err(e.error.error_code().to_string()),
    }
}

fn run_fixtures(subdir: &str) {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join(format!("tests/fixtures/{}", subdir));

    let fixtures = discover_fixtures(&fixture_dir);
    assert!(
        !fixtures.is_empty(),
        "no fixtures found in {}",
        fixture_dir.display()
    );

    for fixture_path in fixtures {
        let fixture = load_fixture(&fixture_path);
        let name = fixture_path
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();

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
                Expectation::Output(_) => {
                    // Output expectations are for runtime, not type checking
                }
            }
        }
    }
}

#[test]
fn m2_fixtures() {
    run_fixtures("m2");
}

#[test]
fn m3_fixtures() {
    run_fixtures("m3");
}

#[test]
fn m6_fixtures() {
    run_fixtures("m6");
}

#[test]
fn m7_fixtures() {
    run_fixtures("m7");
}

#[test]
fn m8_fixtures() {
    run_fixtures("m8");
}

#[test]
fn m9_fixtures() {
    run_fixtures("m9");
}

#[test]
fn m11_fixtures() {
    run_fixtures("m11");
}

#[test]
fn m18_fixtures() {
    run_fixtures("m18");
}

#[test]
fn m20_fixtures() {
    run_fixtures("m20");
}

#[test]
fn m18_module_fixtures() {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/m18/modules");

    let fixtures = discover_fixtures(&fixture_dir);
    assert!(
        !fixtures.is_empty(),
        "no fixtures found in {}",
        fixture_dir.display()
    );

    for fixture_path in fixtures {
        let fixture = load_fixture(&fixture_path);
        let name = fixture_path
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();

        let resolver =
            CompositeResolver::with_source_root(fixture_path.parent().unwrap().to_path_buf());

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
                Expectation::Output(_) => {
                    let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
                    assert!(
                        result.is_ok(),
                        "fixture {name}: expected ok but got error {:?}",
                        result.err()
                    );
                }
                Expectation::Ok => {
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
}

#[test]
fn m21_fixtures() {
    run_fixtures("m21");
}

#[test]
fn a_fixtures() {
    run_fixtures("a");
}

#[test]
fn m11_module_fixtures() {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/m11/modules");

    let fixtures = discover_fixtures(&fixture_dir);
    assert!(
        !fixtures.is_empty(),
        "no fixtures found in {}",
        fixture_dir.display()
    );

    for fixture_path in fixtures {
        let fixture = load_fixture(&fixture_path);
        let name = fixture_path
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();

        let resolver =
            CompositeResolver::with_source_root(fixture_path.parent().unwrap().to_path_buf());

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
                Expectation::Output(_) => {
                    // Verify type-checking succeeds (runtime test handled by codegen)
                    let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
                    assert!(
                        result.is_ok(),
                        "fixture {name}: expected ok but got error {:?}",
                        result.err()
                    );
                }
                Expectation::Ok => {
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
}
