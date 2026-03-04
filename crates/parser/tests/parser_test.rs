use alang_parser::ast::Expr;
use alang_parser::lexer::lexer;
use alang_parser::parser::parse_expr;
use chumsky::Parser;
use insta::assert_yaml_snapshot;

fn parse(input: &str) -> Expr {
    let (tokens, lex_errors) = lexer().parse(input).into_output_errors();
    assert!(lex_errors.is_empty(), "unexpected lex errors: {lex_errors:?}");
    let tokens = tokens.unwrap();
    let (expr, parse_errors) = parse_expr(&tokens);
    assert!(
        parse_errors.is_empty(),
        "unexpected parse errors: {parse_errors:?}"
    );
    expr.unwrap()
}

fn parse_with_errors(input: &str) -> (Option<Expr>, usize) {
    let (tokens, _) = lexer().parse(input).into_output_errors();
    let tokens = tokens.unwrap_or_default();
    let (expr, errors) = parse_expr(&tokens);
    (expr, errors.len())
}

#[test]
fn test_int_literal() {
    assert_yaml_snapshot!(parse("42"));
}

#[test]
fn test_float_literal() {
    assert_yaml_snapshot!(parse("3.14"));
}

#[test]
fn test_string_literal() {
    assert_yaml_snapshot!(parse("\"hello\""));
}

#[test]
fn test_bool_literal() {
    assert_yaml_snapshot!(parse("true"));
}

#[test]
fn test_var() {
    assert_yaml_snapshot!(parse("x"));
}

#[test]
fn test_binary_op() {
    assert_yaml_snapshot!(parse("(+ 1 2)"));
}

#[test]
fn test_comparison_op() {
    assert_yaml_snapshot!(parse("(== x y)"));
}

#[test]
fn test_lambda() {
    assert_yaml_snapshot!(parse("(fn [x y] (+ x y))"));
}

#[test]
fn test_let() {
    assert_yaml_snapshot!(parse("(let x 42)"));
}

#[test]
fn test_do_block() {
    assert_yaml_snapshot!(parse("(do (let x 1) (let y 2) (+ x y))"));
}

#[test]
fn test_if() {
    assert_yaml_snapshot!(parse("(if true 1 2)"));
}

#[test]
fn test_application() {
    assert_yaml_snapshot!(parse("(foo x y z)"));
}

#[test]
fn test_match() {
    assert_yaml_snapshot!(parse("(match x (0 \"zero\") (1 \"one\") (_ \"other\"))"));
}

#[test]
fn test_field_access() {
    assert_yaml_snapshot!(parse("(. point x)"));
}

#[test]
fn test_question_mark() {
    assert_yaml_snapshot!(parse("(? (read_file path))"));
}

#[test]
fn test_list() {
    assert_yaml_snapshot!(parse("(list 1 2 3)"));
}

#[test]
fn test_tuple() {
    assert_yaml_snapshot!(parse("(tuple 1 \"two\" 3)"));
}

#[test]
fn test_nested_expr() {
    assert_yaml_snapshot!(parse("(+ (* 2 3) (- 5 1))"));
}

#[test]
fn test_recur() {
    assert_yaml_snapshot!(parse("(recur (+ n 1))"));
}

#[test]
fn test_self() {
    assert_yaml_snapshot!(parse("self"));
}

#[test]
fn test_error_recovery() {
    // Malformed inner expression — outer should still parse via error recovery
    let (expr, error_count) = parse_with_errors("(+ 1 (let) 2)");
    assert!(error_count > 0, "expected at least one parse error");
    // The outer expression should still produce something thanks to recovery
    assert!(expr.is_some(), "expected error recovery to produce an AST");
}
