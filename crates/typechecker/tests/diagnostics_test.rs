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
    let src = "(type Box (record (value String)))\n(def bad (fn [x] [(own String)] Box (Box x)))";
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
