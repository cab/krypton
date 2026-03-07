use krypton_parser::ast::{Expr, Module};
use krypton_parser::lexer;
use krypton_parser::parser::{parse as parse_module_src, parse_expr};
use krypton_typechecker::infer;
use krypton_typechecker::scc;
use krypton_typechecker::types::{Substitution, TypeEnv, TypeVarGen};
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
        Err(e) => format!("TypeError: {}", e.error),
    }
}

#[test]
fn infer_int_literal() {
    insta::assert_snapshot!(infer("42"), @"own Int");
}

#[test]
fn infer_bool_literal() {
    insta::assert_snapshot!(infer("true"), @"own Bool");
}

#[test]
fn infer_string_literal() {
    insta::assert_snapshot!(infer("\"hello\""), @"own String");
}

#[test]
fn infer_identity_lambda() {
    insta::assert_snapshot!(infer("(fn [x] x)"), @"forall a. fn(a) -> a");
}

#[test]
fn infer_const_lambda() {
    insta::assert_snapshot!(infer("(fn [x] 42)"), @"forall a. fn(a) -> own Int");
}

#[test]
fn infer_let_id_applied() {
    insta::assert_snapshot!(infer("(do (let id (fn [x] x)) (id 42))"), @"own Int");
}

#[test]
fn infer_if_int() {
    insta::assert_snapshot!(infer("(if true 1 2)"), @"own Int");
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
    insta::assert_snapshot!(infer("(do 1 2 3)"), @"own Int");
}

#[test]
fn infer_nested_let() {
    insta::assert_snapshot!(infer("(do (let x 1) (let y 2) (+ x y))"), @"Int");
}

#[test]
fn infer_let_polymorphism() {
    insta::assert_snapshot!(infer("(do (let id (fn [x] x)) (let a (id 1)) (id true))"), @"own Bool");
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

fn parse_module(src: &str) -> Module {
    let (module, errors) = parse_module_src(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    module
}

fn infer_module_types(src: &str) -> String {
    let module = parse_module(src);
    match infer::infer_module(&module) {
        Ok(info) => info.fn_types
            .iter()
            .map(|(name, scheme)| format!("{}: {}", name, scheme))
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => format!("TypeError: {}", e.error),
    }
}

#[test]
fn infer_undefined_variable() {
    insta::assert_snapshot!(infer("x"), @"TypeError: unknown variable: x");
}

#[test]
fn infer_shadowing() {
    insta::assert_snapshot!(infer("(do (let x 1) (let x true) x)"), @"own Bool");
}

#[test]
fn infer_forward_reference() {
    insta::assert_snapshot!(
        infer_module_types("(def f (fn [x] (g x))) (def g (fn [x] (+ x 1)))"),
        @"
    f: fn(own Int) -> Int
    g: fn(own Int) -> Int
    "
    );
}

#[test]
fn infer_do_block_scoping() {
    insta::assert_snapshot!(infer("(do (do (let x 1)) x)"), @"TypeError: unknown variable: x");
}

#[test]
fn infer_module_basic() {
    insta::assert_snapshot!(
        infer_module_types("(def add (fn [a b] (+ a b)))"),
        @"add: fn(Int, Int) -> Int"
    );
}

#[test]
fn infer_module_forward_ref() {
    insta::assert_snapshot!(
        infer_module_types("(def f (fn [x] (g x))) (def g (fn [x] (+ x 1)))"),
        @"
    f: fn(own Int) -> Int
    g: fn(own Int) -> Int
    "
    );
}

#[test]
fn infer_mutual_recursion() {
    insta::assert_snapshot!(
        infer_module_types(
            "(def is_even (fn [n] (if (== n 0) true (is_odd (- n 1))))) \
             (def is_odd (fn [n] (if (== n 0) false (is_even (- n 1)))))"
        ),
        @"
    is_even: fn(own Int) -> Bool
    is_odd: fn(Int) -> own Bool
    "
    );
}

#[test]
fn scc_tarjan_unit_test() {
    // Graph: a(0) -> b(1), b(1) -> a(0), c(2) -> a(0)
    let adj = vec![
        vec![1],    // a -> b
        vec![0],    // b -> a
        vec![0],    // c -> a
    ];
    let sccs = scc::tarjan_scc(&adj);
    assert_eq!(sccs.len(), 2);
    assert_eq!(sccs[0], vec![0, 1]); // {a, b} — mutual recursion
    assert_eq!(sccs[1], vec![2]);    // {c} — depends on a
}

#[test]
fn infer_record_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Point (record (x Int) (y Int))) \
             (def p (fn [] (Point 1 2)))"
        ),
        @"
    Point: fn(Int, Int) -> Point
    p: fn() -> Point
    "
    );
}

#[test]
fn infer_sum_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Option [a] (| (Some a) None)) \
             (def wrap (fn [x] (Some x)))"
        ),
        @"
    Some: forall a. fn(a) -> Option<a>
    None: forall a. Option<a>
    wrap: forall c. fn(c) -> Option<c>
    "
    );
}

#[test]
fn infer_bare_variant() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Option [a] (| (Some a) None)) \
             (def none (fn [] None))"
        ),
        @"
    Some: forall a. fn(a) -> Option<a>
    None: forall a. Option<a>
    none: forall c. fn() -> Option<c>
    "
    );
}

#[test]
fn infer_duplicate_type_error() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Foo (record (x Int))) \
             (type Foo (record (y Int))) \
             (def f (fn [x] x))"
        ),
        @"TypeError: duplicate type definition: Foo"
    );
}

#[test]
fn infer_scc_generalization_order() {
    // id should be generalized (polymorphic) before f and g use it,
    // so f and g can each instantiate id at different types.
    insta::assert_snapshot!(
        infer_module_types(
            "(def id (fn [x] x)) \
             (def f (fn [n] (id n))) \
             (def g (fn [s] (id s)))"
        ),
        @r#"
    id: forall b. fn(b) -> b
    f: forall f. fn(f) -> f
    g: forall j. fn(j) -> j
    "#
    );
}

#[test]
fn infer_field_access() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Point (record (x Int) (y Int))) \
             (def get_x (fn [] (. (Point 1 2) x)))"
        ),
        @"
    Point: fn(Int, Int) -> Point
    get_x: fn() -> Int
    "
    );
}

#[test]
fn infer_struct_update() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Point (record (x Int) (y Int))) \
             (def move_x (fn [] (.. (Point 1 2) (x 42))))"
        ),
        @"
    Point: fn(Int, Int) -> Point
    move_x: fn() -> Point
    "
    );
}

#[test]
fn infer_unknown_field_error() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Point (record (x Int) (y Int))) \
             (def bad (fn [] (. (Point 1 2) z)))"
        ),
        @"TypeError: unknown field: type Point has no field z"
    );
}

#[test]
fn infer_field_access_non_struct() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Point (record (x Int) (y Int))) \
             (def bad (fn [] (. 42 y)))"
        ),
        @"TypeError: not a struct: type Int is not a record"
    );
}

#[test]
fn infer_struct_update_unknown_field() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Point (record (x Int) (y Int))) \
             (def bad (fn [] (.. (Point 1 2) (z 42))))"
        ),
        @"TypeError: unknown field: type Point has no field z"
    );
}

#[test]
fn infer_match_option() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Option [a] (| (Some a) None)) \
             (def unwrap_or (fn [opt default] \
               (match opt \
                 ((Some x) x) \
                 ((None) default))))"
        ),
        @"
    Some: forall a. fn(a) -> Option<a>
    None: forall a. Option<a>
    unwrap_or: forall d. fn(Option<d>, d) -> d
    "
    );
}

#[test]
fn infer_match_literal() {
    insta::assert_snapshot!(
        infer_module_types(
            "(def describe (fn [x] \
               (match x \
                 (1 \"one\") \
                 (2 \"two\") \
                 (_ \"other\"))))"
        ),
        @"describe: fn(Int) -> String"
    );
}

#[test]
fn infer_match_variable() {
    insta::assert_snapshot!(
        infer_module_types(
            "(def identity (fn [x] \
               (match x \
                 (y y))))"
        ),
        @"identity: forall b. fn(b) -> b"
    );
}

#[test]
fn infer_match_nested_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type List [a] (| (Cons a (List a)) Nil)) \
             (def sum2 (fn [xs] \
               (match xs \
                 ((Cons h (Cons h2 t)) (+ h h2)) \
                 (_ 0))))"
        ),
        @"
    Cons: forall a. fn(a, List<a>) -> List<a>
    Nil: forall a. List<a>
    sum2: fn(List<Int>) -> Int
    "
    );
}

#[test]
fn infer_tuple_creation() {
    insta::assert_snapshot!(infer("(tuple 1 \"hi\")"), @"(own Int, own String)");
}

#[test]
fn infer_tuple_nested() {
    insta::assert_snapshot!(infer("(tuple 1 (tuple true \"x\"))"), @"(own Int, (own Bool, own String))");
}

#[test]
fn infer_tuple_in_match() {
    insta::assert_snapshot!(
        infer_module_types(
            "(def first (fn [p] (match p ((tuple a b) a))))"
        ),
        @"first: forall d e. fn((d, e)) -> d"
    );
}

#[test]
fn infer_let_destructure_tuple() {
    insta::assert_snapshot!(infer("(do (let (tuple a b) (tuple 1 \"hi\")) a)"), @"own Int");
}

#[test]
fn infer_tuple_polymorphic() {
    insta::assert_snapshot!(
        infer_module_types(
            "(def swap (fn [p] (match p ((tuple a b) (tuple b a)))))"
        ),
        @"swap: forall d e. fn((d, e)) -> (e, d)"
    );
}

#[test]
fn infer_match_wrong_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Color (| Red Green Blue)) \
             (type Option [a] (| (Some a) None)) \
             (def bad (fn [c] \
               (match Red \
                 ((Some x) x) \
                 (_ 0))))"
        ),
        @"TypeError: type mismatch: expected Color, found Option<e>"
    );
}

#[test]
fn test_exhaustive_complete() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Option [a] (| (Some a) None)) \
             (def unwrap (fn [opt] \
               (match opt \
                 ((Some x) x) \
                 ((None) 0))))"
        ),
        @"
    Some: forall a. fn(a) -> Option<a>
    None: forall a. Option<a>
    unwrap: fn(Option<own Int>) -> Int
    "
    );
}

#[test]
fn test_exhaustive_missing_variant() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Option [a] (| (Some a) None)) \
             (def test (fn [opt] \
               (match opt \
                 ((Some x) x))))"
        ),
        @"TypeError: non-exhaustive match: missing None"
    );
}

#[test]
fn test_exhaustive_wildcard_covers_all() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Option [a] (| (Some a) None)) \
             (def test (fn [opt] \
               (match opt \
                 (_ 0))))"
        ),
        @"
    Some: forall a. fn(a) -> Option<a>
    None: forall a. Option<a>
    test: forall c. fn(c) -> Int
    "
    );
}

#[test]
fn test_exhaustive_nested() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type Option [a] (| (Some a) None)) \
             (def test (fn [opt] \
               (match opt \
                 ((Some (Some x)) x) \
                 ((Some (None)) 0))))"
        ),
        @"TypeError: non-exhaustive match: missing None"
    );
}

#[test]
fn infer_call_site_coercion_borrow() {
    insta::assert_snapshot!(
        infer_module_types(
            "(def len (fn [s] [String] Int 42)) \
             (def test (fn [buf] [(own String)] Int (do (len buf) (len buf))))"
        ),
        @r#"
    len: fn(String) -> Int
    test: fn(own String) -> Int
    "#
    );
}

#[test]
fn infer_call_site_coercion_no_collection() {
    insta::assert_snapshot!(
        infer_module_types(
            "(type MyList (| (Cons String MyList) Nil)) \
             (def test (fn [buf] [(own String)] MyList (Cons buf Nil)))"
        ),
        @"
    Cons: fn(String, MyList) -> MyList
    Nil: MyList
    test: fn(own String) -> MyList
    "
    );
}

#[test]
fn float_add_infers_float() {
    insta::assert_snapshot!(infer("(+ 1.0 2.0)"), @"Float");
}

#[test]
fn float_lt_infers_bool() {
    insta::assert_snapshot!(infer("(< 1.0 2.0)"), @"Bool");
}

#[test]
fn float_neg_infers_float() {
    insta::assert_snapshot!(infer("(- 3.14)"), @"Float");
}
