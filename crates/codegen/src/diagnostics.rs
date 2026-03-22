use ariadne::{sources, Color, Config, IndexType, Label, Report, ReportKind};

use crate::emit::CodegenError;

/// Render a codegen error as an ariadne diagnostic string.
pub fn render_codegen_error(filename: &str, source: &str, error: &CodegenError) -> String {
    // Use the error's own source info if present (for errors from imported modules),
    // otherwise fall back to the caller-provided filename/source.
    let (fname, src) = if let Some((ref f, ref s)) = error.error_source {
        (f.as_str(), s.as_str())
    } else {
        (filename, source)
    };

    let code = error.error_code();
    let message = error.to_string();

    if let Some((start, end)) = error.span() {
        let mut output = Vec::new();
        let report = Report::build(ReportKind::Error, (fname.to_string(), start..end))
            .with_config(Config::new().with_index_type(IndexType::Byte))
            .with_code(code)
            .with_message(&message)
            .with_label(
                Label::new((fname.to_string(), start..end))
                    .with_message(format!("{code}: {message}"))
                    .with_color(Color::Red),
            )
            .finish();
        report
            .write(sources([(fname.to_string(), src.to_string())]), &mut output)
            .unwrap();
        String::from_utf8(output).unwrap()
    } else {
        // No span: emit a plain error line instead of a misleading 0..0 report
        format!("error[{code}]: {message}\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn render_error_with_span() {
        let source = "fun main() = recur(1)";
        let error = CodegenError::RecurNotInTailPosition(Some((14, 21)));
        let output = render_codegen_error("test.kr", source, &error);
        assert!(output.contains("C0006"), "should contain error code: {output}");
        assert!(output.contains("recur must be in tail position"), "should contain message: {output}");
        assert!(output.contains("test.kr"), "should contain filename: {output}");
    }

    #[test]
    fn render_error_without_span() {
        let error = CodegenError::NoMainFunction();
        let output = render_codegen_error("test.kr", "fun foo() = 1", &error);
        assert!(output.contains("C0002"), "should contain error code: {output}");
        assert!(output.contains("no main function found"), "should contain message: {output}");
        // Should be a plain error line, not an ariadne report
        assert!(output.starts_with("error["), "should be plain format: {output}");
    }

    #[test]
    fn render_unsupported_expr_with_span() {
        let source = "fun main() = something_weird";
        let error = CodegenError::UnsupportedExpr("test expr".to_string(), Some((14, 28)));
        let output = render_codegen_error("test.kr", source, &error);
        assert!(output.contains("C0003"), "should contain error code: {output}");
        assert!(output.contains("unsupported expression"), "should contain message: {output}");
    }

    #[test]
    fn render_undefined_variable() {
        let source = "fun main() = x\n";
        let error = CodegenError::UndefinedVariable("x".to_string(), Some((14, 15)));
        let output = render_codegen_error("test.kr", source, &error);
        assert!(output.contains("C0004"), "should contain error code: {output}");
        assert!(output.contains("undefined variable: x"), "should contain message: {output}");
    }

    #[test]
    fn render_type_error_no_span() {
        let error = CodegenError::TypeError("unknown named type: Foo".to_string(), None);
        let output = render_codegen_error("test.kr", "fun main() = 1", &error);
        assert!(output.contains("C0005"), "should contain error code: {output}");
        assert!(output.contains("type error"), "should contain message: {output}");
        assert!(output.starts_with("error["), "should be plain format: {output}");
    }
}
