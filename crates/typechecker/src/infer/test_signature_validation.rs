use crate::type_error::{SpannedTypeError, TypeError};
use crate::typed_ast::TypedModule;
use crate::types::Type;

/// Validate the signatures of every `test_*` function in a test module.
///
/// A `test_*` function must be `() -> Unit` with no type parameters: it takes
/// no arguments, returns `Unit`, and is not generic. Order of checks is
/// arguments → return type → generics; the first failure for a given function
/// is reported and subsequent checks for that function are skipped.
pub(crate) fn validate_test_signatures(typed: &TypedModule) -> Vec<SpannedTypeError> {
    let mut errors = Vec::new();
    for fn_decl in &typed.functions {
        if !fn_decl.name.starts_with("test_") {
            continue;
        }
        if !fn_decl.params.is_empty() {
            errors.push(make_error(
                fn_decl.def_span,
                "test_* functions must take no arguments",
            ));
            continue;
        }
        let Some(&idx) = typed.fn_types_by_name.get(&fn_decl.name) else {
            continue;
        };
        let scheme = &typed.fn_types[idx].scheme;
        let ret_ty = match &scheme.ty {
            Type::Fn(_, ret) => ret.as_ref(),
            other => other,
        };
        if !matches!(ret_ty, Type::Unit) && !ret_ty.is_never() {
            errors.push(make_error(
                fn_decl.def_span,
                "test_* functions must return `Unit`",
            ));
            continue;
        }
        if !scheme.vars.is_empty() {
            errors.push(make_error(
                fn_decl.def_span,
                "test_* functions must not be generic",
            ));
            continue;
        }
    }
    errors
}

fn make_error(span: krypton_parser::ast::Span, reason: &str) -> SpannedTypeError {
    SpannedTypeError {
        error: Box::new(TypeError::InvalidTestSignature {
            reason: reason.to_string(),
        }),
        span,
        note: None,
        secondary_span: None,
        source_file: None,
        var_names: None,
    }
}
