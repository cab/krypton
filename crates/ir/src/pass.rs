use std::fmt;

use crate::Module;

/// A transformation or validation pass over an IR module.
pub trait IrPass {
    fn name(&self) -> &str;
    fn run(self, module: Module) -> Result<Module, IrPassError>;
}

/// Error produced by an IR pass.
#[derive(Debug, Clone)]
pub struct IrPassError {
    pub pass: String,
    pub message: String,
}

impl fmt::Display for IrPassError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}", self.pass, self.message)
    }
}

impl std::error::Error for IrPassError {}
