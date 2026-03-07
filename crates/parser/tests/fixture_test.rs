use std::path::Path;

use krypton_parser::parser::parse;
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};

#[test]
fn m1_fixtures() {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/m1");

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

        let (module, errors) = parse(&fixture.source);

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Ok => {
                    assert!(
                        errors.is_empty(),
                        "fixture {name}: expected ok but got errors: {errors:?}"
                    );
                    insta::assert_yaml_snapshot!(name.clone(), module);
                }
                Expectation::Error(code) => {
                    // Skip non-parser error codes (e.g. E0001 is a typechecker error)
                    if !code.starts_with('P') {
                        continue;
                    }
                    assert!(
                        !errors.is_empty(),
                        "fixture {name}: expected error {code} but got no errors"
                    );
                    let codes: Vec<String> =
                        errors.iter().map(|e| e.code.to_string()).collect();
                    assert!(
                        codes.iter().any(|c| c == code),
                        "fixture {name}: expected error {code} but got {codes:?}"
                    );
                }
                Expectation::Output(_) => {
                    // Output expectations are for runtime, not parsing
                }
            }
        }
    }
}

#[test]
fn m9_fixtures() {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/m9");

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

        let (module, errors) = parse(&fixture.source);

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Ok => {
                    assert!(
                        errors.is_empty(),
                        "fixture {name}: expected ok but got errors: {errors:?}"
                    );
                    insta::assert_yaml_snapshot!(name.clone(), module);
                }
                Expectation::Error(code) => {
                    // Skip non-parser error codes (e.g. E0001 is a typechecker error)
                    if !code.starts_with('P') {
                        continue;
                    }
                    assert!(
                        !errors.is_empty(),
                        "fixture {name}: expected error {code} but got no errors"
                    );
                    let codes: Vec<String> =
                        errors.iter().map(|e| e.code.to_string()).collect();
                    assert!(
                        codes.iter().any(|c| c == code),
                        "fixture {name}: expected error {code} but got {codes:?}"
                    );
                }
                Expectation::Output(_) => {
                    // Output expectations are for runtime, not parsing
                }
            }
        }
    }
}
