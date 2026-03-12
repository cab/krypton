use std::path::Path;

use krypton_parser::parser::parse;
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};
use insta::assert_yaml_snapshot;

// --- Fixture tests ---

#[test]
fn m12_fixtures() {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("tests/fixtures/m12");

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

        let (module, errors) = parse(&fixture.source);

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Ok => {
                    assert!(
                        errors.is_empty(),
                        "fixture {name}: expected ok but got errors: {errors:?}"
                    );
                    insta::assert_yaml_snapshot!(format!("m12_{name}"), module);
                }
                Expectation::Error(code) => {
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
                Expectation::Output(_) => {}
            }
        }
    }
}

// --- Unit tests for specific constructs ---

#[test]
fn test_literal_int() {
    let (module, errors) = parse("fun f() -> Int = 42");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_binary_precedence() {
    let (module, errors) = parse("fun f() -> Int = 1 + 2 * 3");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_boolean_ops() {
    let (module, errors) = parse("fun f(a: Bool, b: Bool) -> Bool = a && b || !a");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_if_else() {
    let (module, errors) = parse("fun f(x: Int) -> Int = if x > 0 { x } else { -x }");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_lambda() {
    let (module, errors) = parse("fun f() -> (Int) -> Int = x -> x + 1");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_block() {
    let (module, errors) = parse("fun f() -> Int { let x = 1; let y = 2; x + y }");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_match() {
    let src = r#"
type Option[a] = Some(a) | None
fun f(x: Option[Int]) -> Int = match x {
    Some(v) => v,
    None => 0,
}
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_match_guard() {
    let src = r#"
type Option[a] = Some(a) | None
fun f(x: Option[Int]) -> Int = match x {
    Some(v) if v > 0 => v,
    _ => 0,
}
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_field_access() {
    let src = "type P = { x: Int }\nfun f(p: P) -> Int = p.x";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_ufcs() {
    let src = "fun inc(x: Int) -> Int = x + 1\nfun f(x: Int) -> Int = x.inc()";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_list_literal() {
    let (module, errors) = parse("fun f() = [1, 2, 3]");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_tuple_expr() {
    let (module, errors) = parse("fun f() = (1, 2, 3)");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_struct_literal() {
    let src = "type Point = { x: Int, y: Int }\nfun f() -> Point = Point { x = 1, y = 2 }";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_multiline_call_argument_with_struct_literal() {
    let src = r#"
type Player = { name: String, score: Int }
fun main() = println(
  Player { name = "hi", score = 1 }
)
"#;
    let (_module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
}

#[test]
fn test_multiline_function_signature_before_return_arrow() {
    let src = r#"
fun fold[T](
  xs: List[T],
  start: T,
  f: (Option[T], T) -> T
) -> Option[T] {
  1
}
"#;
    let (_module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
}

#[test]
fn test_block_body_after_assign_is_not_record_like() {
    let src = r#"
fun f() = {
  let x = 1
  x
}
"#;
    let (_module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
}

#[test]
fn test_multiline_record_type_fields_do_not_use_asi() {
    let src = r#"
type Player = {
  name: String,
  score: Int,
}
"#;
    let (_module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
}

#[test]
fn test_hkt_type_params_on_functions_and_methods() {
    let src = r#"
trait Hoist[a] {
  fun hoist[f[_], g[_]](x: f[a], k: (f[a]) -> g[a]) -> g[a]
}

impl Hoist[Int] {
  fun hoist[f[_], g[_]](x: f[Int], k: (f[Int]) -> g[Int]) -> g[Int] = k(x)
}

fun apply[f[_], a](fa: f[a]) -> f[a] = fa
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");

    match &module.decls[0] {
        krypton_parser::ast::Decl::DefTrait { methods, .. } => {
            assert_eq!(methods[0].type_params.len(), 2);
            assert_eq!(methods[0].type_params[0].name, "f");
            assert_eq!(methods[0].type_params[0].arity, 1);
            assert_eq!(methods[0].type_params[1].name, "g");
            assert_eq!(methods[0].type_params[1].arity, 1);
        }
        other => panic!("expected DefTrait, got {:?}", other),
    }

    match &module.decls[1] {
        krypton_parser::ast::Decl::DefImpl { methods, .. } => {
            assert_eq!(methods[0].type_params.len(), 2);
            assert_eq!(methods[0].type_params[0].arity, 1);
            assert_eq!(methods[0].type_params[1].arity, 1);
        }
        other => panic!("expected DefImpl, got {:?}", other),
    }

    match &module.decls[2] {
        krypton_parser::ast::Decl::DefFn(f) => {
            assert_eq!(f.type_params.len(), 2);
            assert_eq!(f.type_params[0].name, "f");
            assert_eq!(f.type_params[0].arity, 1);
            assert_eq!(f.type_params[1].name, "a");
            assert_eq!(f.type_params[1].arity, 0);
        }
        other => panic!("expected DefFn, got {:?}", other),
    }
}

#[test]
fn test_explicit_type_application_and_call() {
    let src = r#"
fun identity[a](x: a) -> a = x
fun f() = identity[Int](42)
fun g() = identity[Int]
fun h(xs: List[Int], f: (Int) -> String) = xs.map[String](f)
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");

    match &module.decls[1] {
        krypton_parser::ast::Decl::DefFn(f) => match &*f.body {
            krypton_parser::ast::Expr::App { func, args, .. } => {
                assert_eq!(args.len(), 1);
                match func.as_ref() {
                    krypton_parser::ast::Expr::TypeApp { expr, type_args, .. } => {
                        assert_eq!(type_args.len(), 1);
                        assert!(matches!(
                            expr.as_ref(),
                            krypton_parser::ast::Expr::Var { name, .. } if name == "identity"
                        ));
                    }
                    other => panic!("expected TypeApp callee, got {:?}", other),
                }
            }
            other => panic!("expected App body, got {:?}", other),
        },
        other => panic!("expected DefFn, got {:?}", other),
    }

    match &module.decls[2] {
        krypton_parser::ast::Decl::DefFn(f) => match &*f.body {
            krypton_parser::ast::Expr::TypeApp { expr, type_args, .. } => {
                assert_eq!(type_args.len(), 1);
                assert!(matches!(
                    expr.as_ref(),
                    krypton_parser::ast::Expr::Var { name, .. } if name == "identity"
                ));
            }
            other => panic!("expected standalone TypeApp, got {:?}", other),
        },
        other => panic!("expected DefFn, got {:?}", other),
    }

    match &module.decls[3] {
        krypton_parser::ast::Decl::DefFn(f) => match &*f.body {
            krypton_parser::ast::Expr::App { func, args, .. } => {
                assert_eq!(args.len(), 2);
                match func.as_ref() {
                    krypton_parser::ast::Expr::TypeApp { expr, type_args, .. } => {
                        assert_eq!(type_args.len(), 1);
                        assert!(matches!(
                            expr.as_ref(),
                            krypton_parser::ast::Expr::Var { name, .. } if name == "map"
                        ));
                    }
                    other => panic!("expected UFCS TypeApp callee, got {:?}", other),
                }
            }
            other => panic!("expected App body, got {:?}", other),
        },
        other => panic!("expected DefFn, got {:?}", other),
    }
}

#[test]
fn test_import() {
    let (module, errors) = parse("import core/option.{Option, Some, None}");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_import_alias() {
    let (module, errors) = parse("import core/list.{List, map as listMap}");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_visibility() {
    let (module, errors) = parse("pub fun add(a: Int, b: Int) -> Int = a + b");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_pub_open_type() {
    let (module, errors) = parse("pub open type Color = Red | Green | Blue");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_where_clause() {
    let (module, errors) = parse("fun compare(a: a, b: a) -> Bool where a: Ord = a < b");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_recur() {
    let (module, errors) = parse("fun f(n: Int) -> Int = if n <= 1 { 1 } else { n * recur(n - 1) }");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_trait_decl() {
    let src = r#"
trait Eq[a] {
    fun eq(self: a, other: a) -> Bool
}
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_impl_decl() {
    let src = r#"
type Point = { x: Int, y: Int }
impl Eq[Point] {
    fun eq(a, b) = a.x == b.x
}
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_extern_decl() {
    let src = r#"
extern "java.lang.Math" {
    fun abs(Int) -> Int
    fun max(Int, Int) -> Int
}
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_record_type() {
    let (module, errors) = parse("type Point = { x: Int, y: Int }");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_sum_type() {
    let (module, errors) = parse("type Option[a] = Some(a) | None");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_function_call() {
    let (module, errors) = parse("fun f(x: Int) -> Int = add(x, 1)");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_question_mark() {
    let (module, errors) = parse("fun f(x: Option[Int]) -> Int = x?");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_trait_method_missing_annotation() {
    let src = "trait Eq[a] {\n  fun eq(a, a) -> Bool\n}";
    let (_, errors) = parse(src);
    assert!(!errors.is_empty(), "expected a parse error");
    assert!(
        errors[0].message.contains("trait method parameters require types"),
        "expected helpful error about typed parameters, got: {}",
        errors[0].message,
    );
}

#[test]
fn test_pub_import() {
    let (module, errors) = parse("pub import core/option.{Option, Some, None}");
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_pub_import_multiple() {
    let src = "pub import core/option.{Option, Some, None}\npub import core/result.{Result}";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn test_pub_use_suggests_pub_import() {
    let (_, errors) = parse("pub use Foo");
    assert!(!errors.is_empty(), "expected parse error for pub use");
}

#[test]
fn test_error_recovery() {
    let (_, errors) = parse("fun bad( = 42");
    assert!(!errors.is_empty(), "expected parse errors");
}

#[test]
fn let_with_type_annotation() {
    let src = "fun f() -> Int { let x: Int = 5; x }";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}

#[test]
fn let_with_generic_type_annotation() {
    let src = "fun f() { let xs: List[Int] = [1, 2, 3]; xs }";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_yaml_snapshot!(module);
}
