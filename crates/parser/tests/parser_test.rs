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
    let (module, errors) = parse("fun f() -> (Int) -> Int = x => x + 1");
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
fn test_error_recovery() {
    let (_, errors) = parse("fun bad( = 42");
    assert!(!errors.is_empty(), "expected parse errors");
}
