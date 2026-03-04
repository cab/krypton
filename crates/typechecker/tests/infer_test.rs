use alang_parser::ast::Expr;
use alang_parser::lexer;
use alang_parser::parser::parse_expr;
use alang_typechecker::infer;
use alang_typechecker::types::{Substitution, TypeEnv, TypeVarGen};
use chumsky::prelude::*;

fn parse(src: &str) -> Expr {
    let (tokens, lex_errors) = lexer::lexer().parse(src).into_output_errors();
    assert!(lex_errors.is_empty(), "lex errors: {:?}", lex_errors);
    let tokens = tokens.unwrap();
    let (expr, parse_errors) = parse_expr(&tokens);
    assert!(parse_errors.is_empty(), "parse errors: {:?}", parse_errors);
    expr.expect("no expression parsed")
}

fn infer(src: &str) -> String {
    let expr = parse(src);

    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();

    match infer::infer_expr(&expr, &mut env, &mut subst, &mut gen) {
        Ok(ty) => infer::display_type(&ty, &subst, &env),
        Err(e) => format!("TypeError: {}", e),
    }
}

#[test]
fn infer_int_literal() {
    insta::assert_snapshot!(infer("42"), @"Int");
}

#[test]
fn infer_bool_literal() {
    insta::assert_snapshot!(infer("true"), @"Bool");
}

#[test]
fn infer_string_literal() {
    insta::assert_snapshot!(infer("\"hello\""), @"String");
}

#[test]
fn infer_identity_lambda() {
    insta::assert_snapshot!(infer("(fn [x] x)"), @"forall a. fn(a) -> a");
}

#[test]
fn infer_const_lambda() {
    insta::assert_snapshot!(infer("(fn [x] 42)"), @"forall a. fn(a) -> Int");
}

#[test]
fn infer_let_id_applied() {
    insta::assert_snapshot!(infer("(do (let id (fn [x] x)) (id 42))"), @"Int");
}

#[test]
fn infer_if_int() {
    insta::assert_snapshot!(infer("(if true 1 2)"), @"Int");
}

#[test]
fn infer_if_mismatch() {
    insta::assert_snapshot!(infer("(if true 1 \"hi\")"), @"TypeError: type mismatch: expected Int, found String");
}

#[test]
fn infer_if_non_bool_cond() {
    insta::assert_snapshot!(infer("(if 42 1 2)"), @"TypeError: type mismatch: expected Int, found Bool");
}

#[test]
fn infer_application() {
    insta::assert_snapshot!(infer("(do (let f (fn [x] (+ x 1))) (f 5))"), @"Int");
}

#[test]
fn infer_do_block() {
    insta::assert_snapshot!(infer("(do 1 2 3)"), @"Int");
}

#[test]
fn infer_nested_let() {
    insta::assert_snapshot!(infer("(do (let x 1) (let y 2) (+ x y))"), @"Int");
}

#[test]
fn infer_let_polymorphism() {
    insta::assert_snapshot!(infer("(do (let id (fn [x] x)) (let a (id 1)) (id true))"), @"Bool");
}

#[test]
fn infer_binary_add() {
    insta::assert_snapshot!(infer("(+ 1 2)"), @"Int");
}

#[test]
fn infer_binary_eq() {
    insta::assert_snapshot!(infer("(== 1 2)"), @"Bool");
}

#[test]
fn infer_binary_gt() {
    insta::assert_snapshot!(infer("(> 1 2)"), @"Bool");
}
