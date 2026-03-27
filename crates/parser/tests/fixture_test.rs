use std::path::PathBuf;

use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use rstest::rstest;

#[rstest]
fn parser_fixture(
    #[files("tests/fixtures/parser/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() {
        return;
    }

    let name = path.file_stem().unwrap().to_string_lossy().to_string();
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
                if !code.starts_with('P') {
                    continue;
                }
                assert!(
                    !errors.is_empty(),
                    "fixture {name}: expected error {code} but got no errors"
                );
                let codes: Vec<String> = errors.iter().map(|e| e.code.to_string()).collect();
                assert!(
                    codes.iter().any(|c| c == code),
                    "fixture {name}: expected error {code} but got {codes:?}"
                );
            }
            Expectation::Output(_) | Expectation::Panic(_) => {}
        }
    }
}

#[rstest]
fn parser_stdlib_fixture(
    #[files("tests/fixtures/stdlib/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() {
        return;
    }

    let name = path.file_stem().unwrap().to_string_lossy().to_string();
    let (_, errors) = parse(&fixture.source);

    for expectation in &fixture.expectations {
        match expectation {
            Expectation::Ok | Expectation::Output(_) | Expectation::Panic(_) => {
                assert!(
                    errors.is_empty(),
                    "fixture {name}: expected ok but got parse errors: {errors:?}"
                );
            }
            Expectation::Error(code) => {
                if !code.starts_with('P') {
                    continue;
                }
                assert!(
                    !errors.is_empty(),
                    "fixture {name}: expected error {code} but got no errors"
                );
            }
        }
    }
}
