use ariadne::{sources, Color, Config, IndexType, Label, Report, ReportKind};
use serde::Serialize;

use crate::ast::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ErrorCode {
    P0001, // Unexpected token
    P0002, // Unclosed delimiter
    P0003, // Invalid literal / lex error
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ErrorCode::P0001 => write!(f, "P0001"),
            ErrorCode::P0002 => write!(f, "P0002"),
            ErrorCode::P0003 => write!(f, "P0003"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ParseError {
    pub code: ErrorCode,
    pub message: String,
    pub span: Span,
}

/// Render parse errors as ariadne diagnostics, returning the rendered string.
pub fn render_errors(filename: &str, source: &str, errors: &[ParseError]) -> String {
    let mut output = Vec::new();
    let fname = filename.to_string();
    let src = source.to_string();

    for error in errors {
        let (start, end) = error.span;
        let report = Report::build(ReportKind::Error, (fname.clone(), start..end))
            .with_config(Config::new().with_index_type(IndexType::Byte))
            .with_code(error.code.to_string())
            .with_message(&error.message)
            .with_label(
                Label::new((fname.clone(), start..end))
                    .with_message(format!("{}: {}", error.code, &error.message))
                    .with_color(Color::Red),
            )
            .finish();
        report
            .write(sources([(fname.clone(), src.clone())]), &mut output)
            .unwrap();
    }

    String::from_utf8(output).unwrap()
}
