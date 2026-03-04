use alang_parser::diagnostics;
use alang_parser::parser::{self, ErrorCode};

#[test]
fn test_p0001_unexpected_token() {
    let source = "(def 42)";
    let (_module, errors) = parser::parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0001),
        "expected P0001 error, got: {errors:?}"
    );
    let rendered = diagnostics::render_errors("test.al", source, &errors);
    let plain = strip_ansi_escapes::strip_str(&rendered);
    insta::assert_snapshot!(plain);
}

#[test]
fn test_p0002_unclosed_paren() {
    let source = "(def add (fn [a b] (+ a b)";
    let (_module, errors) = parser::parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0002),
        "expected P0002 error, got: {errors:?}"
    );
    let rendered = diagnostics::render_errors("test.al", source, &errors);
    let plain = strip_ansi_escapes::strip_str(&rendered);
    insta::assert_snapshot!(plain);
}

#[test]
fn test_p0003_invalid_literal() {
    let source = "(def foo (fn [] 0xFF_bad!))";
    let (_module, errors) = parser::parse(source);
    assert!(!errors.is_empty(), "expected at least one error");
    assert!(
        errors.iter().any(|e| e.code == ErrorCode::P0003),
        "expected P0003 error, got: {errors:?}"
    );
    let rendered = diagnostics::render_errors("test.al", source, &errors);
    let plain = strip_ansi_escapes::strip_str(&rendered);
    insta::assert_snapshot!(plain);
}
