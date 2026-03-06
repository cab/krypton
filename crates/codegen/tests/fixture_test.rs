use std::io::Write;
use std::path::Path;
use std::process::Command;

use krypton_codegen::emit::compile_module;
use krypton_parser::parser::parse;
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};

fn run_program(source: &str) -> String {
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let classes = compile_module(&module, "Test").expect("compile_module should succeed");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        let mut f = std::fs::File::create(&class_path).unwrap();
        f.write_all(bytes).unwrap();
    }

    let output = Command::new("java")
        .arg("-cp")
        .arg(dir.path())
        .arg("Test")
        .output()
        .expect("java command should run");

    assert!(
        output.status.success(),
        "java exited with {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

#[test]
fn m4_fixtures() {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/m4");

    let fixtures = discover_fixtures(&fixture_dir);
    assert!(
        !fixtures.is_empty(),
        "no fixtures found in {}",
        fixture_dir.display()
    );

    let mut ran = 0;
    for fixture_path in fixtures {
        let fixture = load_fixture(&fixture_path);
        let name = fixture_path
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Output(expected) => {
                    let actual = run_program(&fixture.source);
                    assert_eq!(
                        actual, *expected,
                        "fixture {name}: expected output {expected:?} but got {actual:?}"
                    );
                    ran += 1;
                }
                Expectation::Ok => {
                    let (module, errors) = parse(&fixture.source);
                    assert!(
                        errors.is_empty(),
                        "fixture {name}: expected ok but got parse errors: {errors:?}"
                    );
                    compile_module(&module, "Test").unwrap_or_else(|e| {
                        panic!("fixture {name}: expected ok but compile failed: {e}")
                    });
                    ran += 1;
                }
                Expectation::Error(_) => {
                    // Skip error expectations in codegen fixtures
                }
            }
        }
    }

    assert!(ran > 0, "no output/ok fixtures were found to run");
}

#[test]
fn m5_fixtures() {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/m5");

    let fixtures = discover_fixtures(&fixture_dir);
    assert!(
        !fixtures.is_empty(),
        "no fixtures found in {}",
        fixture_dir.display()
    );

    let mut ran = 0;
    for fixture_path in fixtures {
        let fixture = load_fixture(&fixture_path);
        let name = fixture_path
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Output(expected) => {
                    let actual = run_program(&fixture.source);
                    assert_eq!(
                        actual, *expected,
                        "fixture {name}: expected output {expected:?} but got {actual:?}"
                    );
                    ran += 1;
                }
                Expectation::Ok => {
                    let (module, errors) = parse(&fixture.source);
                    assert!(
                        errors.is_empty(),
                        "fixture {name}: expected ok but got parse errors: {errors:?}"
                    );
                    compile_module(&module, "Test").unwrap_or_else(|e| {
                        panic!("fixture {name}: expected ok but compile failed: {e}")
                    });
                    ran += 1;
                }
                Expectation::Error(_) => {
                    // Skip error expectations in codegen fixtures
                }
            }
        }
    }

    assert!(ran > 0, "no output/ok fixtures were found to run");
}
