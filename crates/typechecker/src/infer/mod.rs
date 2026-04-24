use crate::unify::SpannedTypeError;

/// Error from `infer_module`, bundling the error with enough context
/// to render diagnostics against the correct file.
#[derive(Debug)]
pub enum InferError {
    /// A type error, possibly from an imported module.
    TypeError {
        error: SpannedTypeError,
        /// (module_path, source_text) for the module where the error originated.
        /// `None` means the error is in the root/user file.
        error_source: Option<(String, String)>,
    },
    /// Parse errors in an imported module — rendered via the parser's own diagnostics.
    ModuleParseError {
        path: String,
        source: String,
        errors: Vec<krypton_parser::diagnostics::ParseError>,
    },
}

impl InferError {
    /// Get the `SpannedTypeError` if this is a type error, or `None` for parse errors.
    pub fn type_error(&self) -> Option<&SpannedTypeError> {
        match self {
            InferError::TypeError { error, .. } => Some(error),
            InferError::ModuleParseError { .. } => None,
        }
    }
}

mod bodies;
mod checks;
mod derive;
mod deriving_pass;
mod display;
mod entry;
mod expr;
mod extern_decl;
mod fork;
mod helpers;
mod impls;
mod import_ctx;
mod imports;
mod module_driver;
mod pattern;
mod resolve_multi;
mod resolve_overloads;
mod state;
mod test_signature_validation;
mod traits_register;

pub use display::display_type;
pub use entry::infer_expr;
pub use module_driver::{
    infer_module, infer_module_single, infer_project_source_unit, infer_test_module,
    ProjectSourceUnit,
};

pub(super) use display::leading_type_var;
pub(super) use entry::{find_first_recur_span, first_own_capture, instantiate_field_type};
pub(super) use helpers::*;

pub(crate) use entry::collect_parser_pattern_bindings;
pub(crate) use expr::InferenceContext;
pub(crate) use import_ctx::ImportBinding;
pub(crate) use state::ModuleInferenceState;
