use krypton_parser::lexer;
use krypton_parser::parser::{parse, parse_expr};
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

fn render_fixture_error(fixture: &str) -> String {
    let src = std::fs::read_to_string(fixture).unwrap();
    let (module, errors) = parse(&src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let err = match infer::infer_module(&module) {
        Ok(_) => panic!("expected a type error"),
        Err(e) => e,
    };
    let rendered = render_type_errors(fixture, &src, &[err]);
    strip_ansi_escapes(rendered)
}

fn render_module_error(src: &str) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let err = match infer::infer_module(&module) {
        Ok(_) => panic!("expected a type error"),
        Err(e) => e,
    };
    let rendered = render_type_errors("test.kr", src, &[err]);
    strip_ansi_escapes(rendered)
}

#[test]
fn own_fn_vs_fn_help_text() {
    let src = "(def call_many (fn [f] [(fn [] String)] String (f)))\n(def bad (fn [x] [(own String)] String\n  (call_many (fn [] x))))";
    let output = render_module_error(src);
    assert!(
        output.contains("single-use closure"),
        "expected own fn help text in:\n{output}"
    );
}

#[test]
fn own_t_vs_t_help_text() {
    let src = "(def bad (fn [x] [String] (own String) x))";
    let output = render_module_error(src);
    assert!(
        output.contains("own"),
        "expected ownership help text in:\n{output}"
    );
}

#[test]
fn no_own_mismatch_no_help() {
    let output = render_error("(if true 1 \"hi\")");
    assert!(
        !output.contains("single-use closure") && !output.contains("own"),
        "expected no ownership help text in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_e0101() {
    let src = "(def consume (fn [buf] [(own String)] String buf))\n(def bad (fn [x] [(own String)] String\n  (do (let f (fn [] (consume x)))\n      (f)\n      (f))))";
    let output = render_module_error(src);
    assert!(
        output.contains("captures own value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_e0001() {
    let src = "(def call_many (fn [f] [(fn [] String)] String (f)))\n(def bad (fn [x] [(own String)] String\n  (call_many (fn [] x))))";
    let output = render_module_error(src);
    assert!(
        output.contains("captures own value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_correct_name() {
    let src = "(def consume (fn [buf] [(own String)] String buf))\n(def bad (fn [a b] [String (own String)] String\n  (do (let f (fn [] (consume b)))\n      (f)\n      (f))))";
    let output = render_module_error(src);
    assert!(
        output.contains("captures own value `b`"),
        "expected own capture note mentioning `b` in:\n{output}"
    );
}

#[test]
fn test_qualifier_mismatch_diagnostic() {
    let output = render_fixture_error("../../tests/fixtures/m6/qualifier_dup_error.kr");
    insta::assert_snapshot!(output);
    // No type-theory jargon in error/help lines (exclude file path lines)
    let message_lines: String = output.lines()
        .filter(|l| !l.contains("qualifier_dup_error.kr"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(!message_lines.contains("affine"), "should not contain 'affine': {message_lines}");
    assert!(!message_lines.contains("qualifier"), "should not contain 'qualifier': {message_lines}");
    assert!(!message_lines.contains("unlimited"), "should not contain 'unlimited': {message_lines}");
}

#[test]
fn test_e0101_shows_first_use() {
    let output = render_fixture_error("../../tests/fixtures/m6/own_double_use.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("first use here"),
        "expected 'first use here' secondary label in:\n{output}"
    );
}

#[test]
fn test_e0102_shows_consuming_branch() {
    let output = render_fixture_error("../../tests/fixtures/m6/branch_if_one.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("consumed here"),
        "expected 'consumed here' secondary label in:\n{output}"
    );
}

#[test]
fn test_e0103_shows_prior_use() {
    let output = render_fixture_error("../../tests/fixtures/m6/own_capture_moved.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("consumed here"),
        "expected 'consumed here' secondary label in:\n{output}"
    );
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
