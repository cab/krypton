use krypton_parser::lexer::{lexer, Token};
use chumsky::Parser;
use insta::assert_yaml_snapshot;

fn lex(input: &str) -> Vec<Token<'_>> {
    let (tokens, errors) = lexer().parse(input).into_output_errors();
    assert!(errors.is_empty(), "unexpected lex errors: {errors:?}");
    tokens
        .unwrap()
        .into_iter()
        .map(|(tok, _span)| tok)
        .collect()
}

fn lex_with_errors(input: &str) -> (Vec<Token<'_>>, usize) {
    let (tokens, errors) = lexer().parse(input).into_output_errors();
    let toks: Vec<_> = tokens
        .unwrap_or_default()
        .into_iter()
        .map(|(tok, _span)| tok)
        .collect();
    (toks, errors.len())
}

#[test]
fn test_basic_arithmetic() {
    assert_yaml_snapshot!(lex("(+ 1 2)"));
}

#[test]
fn test_keywords_and_brackets() {
    assert_yaml_snapshot!(lex("(def foo (fn [x] Int x))"));
}

#[test]
fn test_string_literal() {
    assert_yaml_snapshot!(lex("\"hello world\""));
}

#[test]
fn test_comment() {
    assert_yaml_snapshot!(lex("# this is a comment\n(+ 1 2)"));
}

#[test]
fn test_all_operators() {
    assert_yaml_snapshot!(lex("+ - * / == != < > <= >= ? | . : _"));
}

#[test]
fn test_all_keywords() {
    assert_yaml_snapshot!(lex(
        "def fn let if match type do receive recur send spawn self own trait impl import list tuple deriving"
    ));
}

#[test]
fn test_bool_literals() {
    assert_yaml_snapshot!(lex("true false"));
}

#[test]
fn test_float_literal() {
    assert_yaml_snapshot!(lex("3.14 0.5 42"));
}

#[test]
fn test_error_recovery() {
    let (tokens, error_count) = lex_with_errors("(+ 1 @ 2)");
    assert!(error_count > 0, "expected at least one error for '@'");
    // Lexing should still produce tokens around the error
    let non_error: Vec<_> = tokens.iter().filter(|t| !matches!(t, Token::Error)).collect();
    assert!(non_error.len() >= 4, "expected at least 4 valid tokens, got {non_error:?}");
}

#[test]
fn test_nested_expression() {
    assert_yaml_snapshot!(lex("(def add (fn [x y] Int (+ x y)))"));
}

#[test]
fn test_spans() {
    let (tokens, _) = lexer().parse("(+ 1 2)").into_output_errors();
    let tokens = tokens.unwrap();
    // '(' at position 0
    assert_eq!(tokens[0].1.start, 0);
    assert_eq!(tokens[0].1.end, 1);
    // '+' at position 1
    assert_eq!(tokens[1].1.start, 1);
    assert_eq!(tokens[1].1.end, 2);
    // '1' at position 3
    assert_eq!(tokens[2].1.start, 3);
    assert_eq!(tokens[2].1.end, 4);
}
