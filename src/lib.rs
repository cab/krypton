// alang compiler library
// Provides lexer, parser, and AST for the alang programming language

pub mod ast;
pub mod lexer;
pub mod parser;

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::*;

pub use ast::*;
pub use lexer::{lexer, Span, Spanned, Token};
pub use parser::program_parser;

/// Parse a complete program from source code
/// Returns Ok(Program) on success, or Err(error_output) on failure
pub fn parse_program(source: &str) -> Result<Program, String> {
    parse_program_with_filename(source, "input")
}

/// Parse a complete program from source code with a filename for error reporting
pub fn parse_program_with_filename(source: &str, filename: &str) -> Result<Program, String> {
    // Lexer phase
    let (tokens, lex_errors) = lexer().parse(source).into_output_errors();

    if !lex_errors.is_empty() {
        let mut error_output = Vec::new();
        for e in lex_errors {
            Report::build(ReportKind::Error, (filename, e.span().into_range()))
                .with_message("Lexical error")
                .with_label(
                    Label::new((filename, e.span().into_range()))
                        .with_message(e.to_string())
                        .with_color(Color::Red),
                )
                .finish()
                .write((filename, Source::from(&source)), &mut error_output)
                .unwrap();
        }
        return Err(String::from_utf8(error_output).unwrap());
    }

    let tokens = tokens.unwrap();

    // Parser phase
    let len = source.len();
    let (ast, parse_errors) = program_parser()
        .parse(tokens.as_slice().map((len..len).into(), |(t, s)| (t, s)))
        .into_output_errors();

    if !parse_errors.is_empty() {
        let mut error_output = Vec::new();
        for e in parse_errors {
            let report = Report::build(ReportKind::Error, (filename, e.span().into_range()))
                .with_message(format!("{}", e.reason()))
                .with_label(
                    Label::new((filename, e.span().into_range()))
                        .with_message(e.reason().to_string())
                        .with_color(Color::Red),
                );

            // Add context labels if available
            let report = e.contexts().fold(report, |report, (label, span)| {
                report.with_label(
                    Label::new((filename, span.into_range()))
                        .with_message(format!("while parsing this {}", label))
                        .with_color(Color::Yellow),
                )
            });

            report
                .finish()
                .write((filename, Source::from(&source)), &mut error_output)
                .unwrap();
        }
        return Err(String::from_utf8(error_output).unwrap());
    }

    ast.ok_or_else(|| "Failed to parse program".to_string())
}
