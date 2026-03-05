use krypton_parser::ast::{Expr, Module};
use krypton_parser::lexer::lexer;
use krypton_parser::parser::{parse as parse_source, parse_expr};
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

fn parse_module(input: &str) -> Module {
    let (module, errors) = parse_source(input);
    assert!(errors.is_empty(), "unexpected parse errors: {errors:?}");
    module
}

fn parse_module_with_errors(input: &str) -> (Module, usize) {
    let (module, errors) = parse_source(input);
    (module, errors.len())
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
fn test_error_recovery() {
    // Malformed inner expression — outer should still parse via error recovery
    let (expr, error_count) = parse_with_errors("(+ 1 (let) 2)");
    assert!(error_count > 0, "expected at least one parse error");
    // The outer expression should still produce something thanks to recovery
    assert!(expr.is_some(), "expected error recovery to produce an AST");
}

// --- Declaration tests ---

#[test]
fn test_def_fn_simple() {
    assert_yaml_snapshot!(parse_module("(def add (fn [a b] (+ a b)))"));
}

#[test]
fn test_def_fn_typed() {
    assert_yaml_snapshot!(parse_module(
        "(def factorial (fn [n] [Int] Int (if (<= n 1) 1 (* n (factorial (- n 1))))))"
    ));
}

#[test]
fn test_type_record() {
    assert_yaml_snapshot!(parse_module("(type Point (record (x Int) (y Int)))"));
}

#[test]
fn test_type_record_deriving() {
    assert_yaml_snapshot!(parse_module(
        "(type Point (record (x Int) (y Int)) deriving [Eq Hash Show])"
    ));
}

#[test]
fn test_type_sum() {
    assert_yaml_snapshot!(parse_module("(type Option [a] (| (Some a) None))"));
}

#[test]
fn test_type_sum_deriving() {
    assert_yaml_snapshot!(parse_module(
        "(type Option [a] (| (Some a) None) deriving [Eq Show])"
    ));
}

#[test]
fn test_type_sum_no_tvars() {
    assert_yaml_snapshot!(parse_module(
        "(type CounterMsg (| Inc Dec (Get (ActorRef Int))))"
    ));
}

#[test]
fn test_trait() {
    assert_yaml_snapshot!(parse_module(
        "(trait Eq [a] (def eq [a a] Bool) (def neq [a a] Bool (not (eq a b))))"
    ));
}

#[test]
fn test_trait_with_superclass() {
    assert_yaml_snapshot!(parse_module(
        "(trait Ord [a] : [Eq] (def compare [a a] Ordering))"
    ));
}

#[test]
fn test_impl() {
    assert_yaml_snapshot!(parse_module(
        "(impl Eq Point (def eq [a b] (and (== (. a x) (. b x)) (== (. a y) (. b y)))))"
    ));
}

#[test]
fn test_import() {
    assert_yaml_snapshot!(parse_module("(import core.option [Option Some None])"));
}

#[test]
fn test_complete_program() {
    assert_yaml_snapshot!(parse_module(
        r#"
        (type Point (record (x Int) (y Int)))
        (def add (fn [a b] (+ a b)))
        (def main (fn [] (let result (add 1 2))))
        "#
    ));
}

#[test]
fn test_decl_error_recovery() {
    let (module, error_count) =
        parse_module_with_errors("(def) (def add (fn [a b] (+ a b)))");
    assert!(error_count > 0, "expected at least one parse error");
    // The second valid declaration should still parse
    assert!(
        !module.decls.is_empty(),
        "expected error recovery to produce at least one decl"
    );
}
