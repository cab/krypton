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
    let plain: String = diags.iter().map(|d| PlainTextRenderer.render(d, &srcs)).collect();
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
    let plain: String = diags.iter().map(|d| PlainTextRenderer.render(d, &srcs)).collect();
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
    let plain: String = diags.iter().map(|d| PlainTextRenderer.render(d, &srcs)).collect();
    insta::assert_snapshot!(plain);
}
