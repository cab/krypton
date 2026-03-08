use std::path::Path;

use krypton_parser::ast::{Decl};
use krypton_parser::lexer;
use krypton_parser::parser::{parse, parse_expr};
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};
use krypton_typechecker::infer;
use krypton_typechecker::types::{Substitution, TypeEnv, TypeVarGen};
use chumsky::prelude::*;

fn has_module_decls(source: &str) -> bool {
    let (module, _) = parse(source);
    module.decls.iter().any(|d| matches!(d, Decl::DefFn(_) | Decl::DefType(_) | Decl::DefTrait { .. } | Decl::DefImpl { .. } | Decl::ExternJava { .. }))
}

fn infer_module_snapshot(source: &str) -> Result<String, String> {
    let (module, errors) = parse(source);
    if !errors.is_empty() {
        return Err(errors[0].code.to_string());
    }
    match infer::infer_module(&module) {
        Ok(info) => {
            let lines: Vec<String> = info.fn_types
                .iter()
                .map(|(name, scheme)| format!("{name}: {scheme}"))
                .collect();
            Ok(lines.join("\n"))
        }
        Err(e) => Err(e.error.error_code().to_string()),
    }
}

fn infer_expr_snapshot(source: &str) -> Result<String, String> {
    let (tokens, lex_errors) = lexer::lexer().parse(source).into_output_errors();
    if !lex_errors.is_empty() {
        return Err("P0003".to_string());
    }
    let tokens = tokens.unwrap();
    let (expr, parse_errors) = parse_expr(&tokens);
    if !parse_errors.is_empty() {
        return Err("P0001".to_string());
    }
    let expr = expr.expect("no expression parsed");

    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();

    match infer::infer_expr(&expr, &mut env, &mut subst, &mut gen) {
        Ok(ty) => Ok(infer::display_type(&ty, &subst, &env)),
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

        let use_module = has_module_decls(&fixture.source);

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Ok => {
                    let result = if use_module {
                        infer_module_snapshot(&fixture.source)
                    } else {
                        infer_expr_snapshot(&fixture.source)
                    };
                    let snapshot = result.unwrap_or_else(|code| {
                        panic!("fixture {name}: expected ok but got error {code}")
                    });
                    insta::assert_snapshot!(name.clone(), snapshot);
                }
                Expectation::Error(code) => {
                    let result = if use_module {
                        infer_module_snapshot(&fixture.source)
                    } else {
                        infer_expr_snapshot(&fixture.source)
                    };
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
fn m8_fixtures() {
    run_fixtures("m8");
}

#[test]
fn m9_fixtures() {
    run_fixtures("m9");
}
