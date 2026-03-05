use krypton_parser::lexer;
use krypton_parser::parser::parse_expr;
use krypton_typechecker::diagnostics::render_type_errors;
use krypton_typechecker::infer;
use krypton_typechecker::types::{Substitution, TypeEnv, TypeVarGen};
use krypton_typechecker::unify::SpannedTypeError;
use chumsky::prelude::*;

fn parse_and_infer_error(src: &str) -> SpannedTypeError {
    let (tokens, lex_errors) = lexer::lexer().parse(src).into_output_errors();
    assert!(lex_errors.is_empty(), "lex errors: {:?}", lex_errors);
    let tokens = tokens.unwrap();
    let (expr, parse_errors) = parse_expr(&tokens);
    assert!(parse_errors.is_empty(), "parse errors: {:?}", parse_errors);
    let expr = expr.expect("no expression parsed");

    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();

    infer::infer_expr(&expr, &mut env, &mut subst, &mut gen)
        .expect_err("expected a type error")
}

fn render_error(src: &str) -> String {
    let err = parse_and_infer_error(src);
    let rendered = render_type_errors("test.kr", src, &[err]);
    // Strip ANSI escape codes for snapshot stability
    strip_ansi_escapes(rendered)
}

fn strip_ansi_escapes(s: String) -> String {
    let mut result = String::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\x1b' {
            // Skip until we hit a letter (end of ANSI sequence)
            while let Some(&next) = chars.peek() {
                chars.next();
                if next.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            result.push(c);
        }
    }
    result
}

#[test]
fn type_mismatch_diagnostic() {
    insta::assert_snapshot!(render_error("(if true 1 \"hi\")"));
}

#[test]
fn not_a_function_diagnostic() {
    insta::assert_snapshot!(render_error("(42 1)"));
}

#[test]
fn wrong_arity_diagnostic() {
    insta::assert_snapshot!(render_error("(do (let f (fn [x] x)) (f 1 2))"));
}

#[test]
fn infinite_type_diagnostic() {
    insta::assert_snapshot!(render_error("(fn [x] (x x))"));
}

#[test]
fn unknown_var_diagnostic() {
    insta::assert_snapshot!(render_error("(+ x 1)"));
}

#[test]
fn error_codes_present() {
    // Verify each error code appears in at least one diagnostic
    let cases = [
        ("E0001", "(if true 1 \"hi\")"),
        ("E0003", "(+ x 1)"),
        ("E0004", "(42 1)"),
        ("E0005", "(do (let f (fn [x] x)) (f 1 2))"),
        ("E0007", "(fn [x] (x x))"),
    ];
    for (code, src) in cases {
        let output = render_error(src);
        assert!(
            output.contains(code),
            "expected error code {} in output:\n{}",
            code,
            output
        );
    }
}
