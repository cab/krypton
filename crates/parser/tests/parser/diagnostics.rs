use krypton_diagnostics::{DiagnosticRenderer, PlainTextRenderer};
use krypton_parser::diagnostics::{self, ErrorCode};
use krypton_parser::parser::parse;

#[test]
fn test_p0001_unexpected_token() {
    let source = "fun 42()";
    let (_module, errors) = parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0001),
        "expected P0001 error, got: {errors:?}"
    );
    let (diags, srcs) = diagnostics::lower_parse_errors("test.kr", source, &errors);
    let plain: String = diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect();
    insta::assert_snapshot!(plain);
}

#[test]
fn test_p0002_unclosed_paren() {
    let source = "fun add(a, b) = (a + b";
    let (_module, errors) = parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0002),
        "expected P0002 error, got: {errors:?}"
    );
    let (diags, srcs) = diagnostics::lower_parse_errors("test.kr", source, &errors);
    let plain: String = diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect();
    insta::assert_snapshot!(plain);
}

#[test]
fn test_p0003_invalid_literal() {
    let source = "fun foo() = \"unterminated";
    let (_module, errors) = parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0003),
        "expected P0003 error, got: {errors:?}"
    );
    let (diags, srcs) = diagnostics::lower_parse_errors("test.kr", source, &errors);
    let plain: String = diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect();
    insta::assert_snapshot!(plain);
}

#[test]
fn test_p0004_pub_on_trait_method() {
    let source = "pub trait Foo[a] { pub fun bar(x: a) -> a }";
    let (_module, errors) = parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0004),
        "expected P0004 error, got: {errors:?}"
    );
    assert!(
        errors[0]
            .message
            .contains("pub is not needed on trait methods"),
        "expected helpful message, got: {}",
        errors[0].message
    );
    let (diags, srcs) = diagnostics::lower_parse_errors("test.kr", source, &errors);
    let plain: String = diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect();
    insta::assert_snapshot!(plain);
}

#[test]
fn test_pub_opaque_on_fun_rejected() {
    let source = "pub opaque fun foo() = 1";
    let (_module, errors) = parse(source);
    assert!(
        !errors.is_empty(),
        "pub opaque on fun should produce a parse error"
    );
}

#[test]
fn test_pub_opaque_on_trait_rejected() {
    let source = "pub opaque trait Foo[a] { fun bar(x: a) -> a }";
    let (_module, errors) = parse(source);
    assert!(
        !errors.is_empty(),
        "pub opaque on trait should produce a parse error"
    );
}

#[test]
fn test_pub_opaque_on_type_still_works() {
    let source = "pub opaque type Foo = MkFoo(Int)";
    let (_module, errors) = parse(source);
    assert!(
        errors.is_empty(),
        "pub opaque on type should still work, got: {errors:?}"
    );
}

#[test]
fn test_p0006_borrow_requires_owned() {
    let source = "fun read(&r: File) -> Int = 0";
    let (_module, errors) = parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0006),
        "expected P0006 error, got: {errors:?}"
    );
    assert!(
        errors.iter().any(|e| e
            .message
            .contains("borrow mode requires an owned parameter type")),
        "expected helpful message, got: {errors:?}"
    );
}

#[test]
fn test_p0005_old_superclass_syntax() {
    let source = "trait Foo[a] : Bar { fun foo(x: a) -> a }";
    let (_module, errors) = parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0005),
        "expected P0005 error, got: {errors:?}"
    );
    let (diags, srcs) = diagnostics::lower_parse_errors("test.kr", source, &errors);
    let plain: String = diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect();
    insta::assert_snapshot!(plain);
}

fn assert_slot_not_a_type(source: &str) {
    let (_module, errors) = parse(source);
    assert!(!errors.is_empty(), "expected a parse error for {source:?}");
    assert!(
        errors.iter().any(|e| e
            .message
            .contains("`&~T` is a parameter-slot calling convention")),
        "expected slot-not-a-type message for {source:?}, got: {errors:?}"
    );
}

#[test]
fn slot_borrow_in_let_type_rejected() {
    assert_slot_not_a_type("fun f() -> Unit = { let x: &~File = file; () }");
}

#[test]
fn slot_borrow_in_generic_arg_rejected() {
    assert_slot_not_a_type("fun f(xs: List[&~File]) -> Unit = ()");
}

#[test]
fn slot_borrow_in_option_arg_rejected() {
    assert_slot_not_a_type("fun f(x: Option[&~File]) -> Unit = ()");
}

#[test]
fn slot_borrow_in_return_position_rejected() {
    assert_slot_not_a_type("fun f() -> &~File = file");
}

#[test]
fn slot_borrow_in_record_field_rejected() {
    assert_slot_not_a_type("type R = { f: &~File }");
}

#[test]
fn slot_borrow_in_tuple_position_rejected() {
    assert_slot_not_a_type("fun f(x: (&~File, Int)) -> Unit = ()");
}
