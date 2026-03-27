use krypton_diagnostics::{Diagnostic, Severity, SourceEntry};

use crate::emit::CodegenError;

/// Lower a codegen error into the shared diagnostic model.
pub fn lower_codegen_error(
    filename: &str,
    source: &str,
    error: &CodegenError,
) -> (Vec<Diagnostic>, Vec<SourceEntry>) {
    let (fname, src) = if let Some((ref f, ref s)) = error.error_source {
        (f.as_str(), s.as_str())
    } else {
        (filename, source)
    };

    let code = error.error_code();
    let message = error.to_string();

    let sources = vec![SourceEntry {
        filename: fname.to_string(),
        source: src.to_string(),
    }];

    let diag = Diagnostic {
        severity: Severity::Error,
        code: code.to_string(),
        message: message.clone(),
        primary_file: fname.to_string(),
        primary_span: error.span(),
        primary_label: error.span().map(|_| format!("{code}: {message}")),
        secondary_labels: vec![],
        help: None,
        note: None,
    };

    (vec![diag], sources)
}

#[cfg(test)]
mod tests {
    use super::*;
    use krypton_diagnostics::{DiagnosticRenderer, PlainTextRenderer};

    fn render(error: &CodegenError, filename: &str, source: &str) -> String {
        let (diags, srcs) = lower_codegen_error(filename, source, error);
        diags.iter().map(|d| PlainTextRenderer.render(d, &srcs)).collect()
    }

    #[test]
    fn render_error_with_span() {
        let source = "fun main() = recur(1)";
        let error = CodegenError::RecurNotInTailPosition(Some((14, 21)));
        let output = render(&error, "test.kr", source);
        assert!(
            output.contains("C0006"),
            "should contain error code: {output}"
        );
        assert!(
            output.contains("recur must be in tail position"),
            "should contain message: {output}"
        );
        assert!(
            output.contains("test.kr"),
            "should contain filename: {output}"
        );
    }

    #[test]
    fn render_error_without_span() {
        let error = CodegenError::NoMainFunction();
        let output = render(&error, "test.kr", "fun foo() = 1");
        assert!(
            output.contains("C0002"),
            "should contain error code: {output}"
        );
        assert!(
            output.contains("no main function found"),
            "should contain message: {output}"
        );
        // Should be a plain error line, not an ariadne report
        assert!(
            output.starts_with("error["),
            "should be plain format: {output}"
        );
    }

    #[test]
    fn render_unsupported_expr_with_span() {
        let source = "fun main() = something_weird";
        let error = CodegenError::UnsupportedExpr("test expr".to_string(), Some((14, 28)));
        let output = render(&error, "test.kr", source);
        assert!(
            output.contains("C0003"),
            "should contain error code: {output}"
        );
        assert!(
            output.contains("unsupported expression"),
            "should contain message: {output}"
        );
    }

    #[test]
    fn render_undefined_variable() {
        let source = "fun main() = x\n";
        let error = CodegenError::UndefinedVariable("x".to_string(), Some((14, 15)));
        let output = render(&error, "test.kr", source);
        assert!(
            output.contains("C0004"),
            "should contain error code: {output}"
        );
        assert!(
            output.contains("undefined variable: x"),
            "should contain message: {output}"
        );
    }

    #[test]
    fn render_type_error_no_span() {
        let error = CodegenError::TypeError("unknown named type: Foo".to_string(), None);
        let output = render(&error, "test.kr", "fun main() = 1");
        assert!(
            output.contains("C0005"),
            "should contain error code: {output}"
        );
        assert!(
            output.contains("type error"),
            "should contain message: {output}"
        );
        assert!(
            output.starts_with("error["),
            "should be plain format: {output}"
        );
    }
}
