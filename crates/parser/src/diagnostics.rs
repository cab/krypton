use serde::Serialize;

use crate::ast::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ErrorCode {
    P0001, // Unexpected token
    P0002, // Unclosed delimiter
    P0003, // Invalid literal / lex error
    P0004, // Unnecessary syntax
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ErrorCode::P0001 => write!(f, "P0001"),
            ErrorCode::P0002 => write!(f, "P0002"),
            ErrorCode::P0003 => write!(f, "P0003"),
            ErrorCode::P0004 => write!(f, "P0004"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ParseError {
    pub code: ErrorCode,
    pub message: String,
    pub span: Span,
}

/// Lower parse errors into the shared diagnostic model.
pub fn lower_parse_errors(
    filename: &str,
    source: &str,
    errors: &[ParseError],
) -> (Vec<krypton_diagnostics::Diagnostic>, Vec<krypton_diagnostics::SourceEntry>) {
    let sources = vec![krypton_diagnostics::SourceEntry {
        filename: filename.to_string(),
        source: source.to_string(),
    }];
    let diags = errors
        .iter()
        .map(|error| krypton_diagnostics::Diagnostic {
            severity: krypton_diagnostics::Severity::Error,
            code: error.code.to_string(),
            message: error.message.clone(),
            primary_file: filename.to_string(),
            primary_span: Some(error.span),
            primary_label: Some(format!("{}: {}", error.code, &error.message)),
            secondary_labels: vec![],
            help: None,
            note: None,
        })
        .collect();
    (diags, sources)
}
