// alang compiler library
// Provides lexer, parser, and AST for the alang programming language

pub mod ast;
pub mod lexer;
pub mod parser;

use chumsky::prelude::*;

pub use ast::*;
pub use lexer::{lexer, Span, Spanned, Token};
pub use parser::program_parser;

/// Parse a complete program from source code
pub fn parse_program(source: &str) -> Result<Program, String> {
    let tokens = lexer()
        .parse(source)
        .into_result()
        .map_err(|e| format!("Lexer errors: {:?}", e))?;

    let len = source.len();
    program_parser()
        .parse(
            tokens
                .as_slice()
                .map((len..len).into(), |(t, s)| (t, s)),
        )
        .into_result()
        .map_err(|e| format!("Parser errors: {:?}", e))
}
