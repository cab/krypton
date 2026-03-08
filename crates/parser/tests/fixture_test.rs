use std::path::Path;

use krypton_parser::parser::parse;
use krypton_parser::surface_parser::surface_parse;
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation, Syntax};

fn parse_fixture(source: &str, syntax: Syntax) -> (krypton_parser::ast::Module, Vec<krypton_parser::parser::ParseError>) {
    match syntax {
        Syntax::Sexp => parse(source),
        Syntax::Surface => surface_parse(source),
    }
}

fn run_parser_fixtures(subdir: &str) {
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

        let (module, errors) = parse_fixture(&fixture.source, fixture.syntax);

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
fn m1_fixtures() {
    run_parser_fixtures("m1");
}

#[test]
fn m9_fixtures() {
    run_parser_fixtures("m9");
}
