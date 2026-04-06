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
