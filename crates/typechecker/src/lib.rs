// alang-typechecker library
// Algorithm J type inference for the alang programming language

pub mod affine;
pub mod builtins;
pub mod environment;
pub mod error;
pub mod exhaustiveness;
pub mod inference;
pub mod substitution;
pub mod types;
pub mod unification;

use alang_parser::Program;
pub use error::{report_error, report_errors, ErrorCode, TypeError};
pub use inference::{typecheck_program, TypedProgram};
pub use types::{InferType, TypeScheme};

/// Type check a program
/// Returns Ok(typed program) or Err(list of errors)
pub fn typecheck(program: &Program) -> Result<TypedProgram, Vec<TypeError>> {
    // Run type inference
    let typed = typecheck_program(program)?;

    // Run affine checking (stub for now)
    affine::check_affine_usage()?;

    Ok(typed)
}

/// Type check and pretty-print errors
pub fn typecheck_with_errors(
    program: &Program,
    filename: &str,
    source: &str,
) -> Result<TypedProgram, String> {
    match typecheck(program) {
        Ok(typed) => Ok(typed),
        Err(errors) => Err(report_errors(&errors, filename, source)),
    }
}
