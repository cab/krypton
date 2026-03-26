use ariadne::{sources, Color, Config, IndexType, Label, Report, ReportKind};

use crate::infer::InferError;
use crate::unify::SpannedTypeError;
use krypton_modules::stdlib_loader::StdlibLoader;

/// Render an `InferError` as a diagnostic string.
///
/// For type errors, renders via ariadne against the correct file.
/// For module parse errors, delegates to the parser's own diagnostic renderer.
pub fn render_infer_error(filename: &str, source: &str, err: &InferError) -> String {
    match err {
        InferError::TypeError {
            error,
            error_source,
        } => render_type_error_with_source(filename, source, error, error_source.as_ref()),
        InferError::ModuleParseError {
            path,
            source: mod_source,
            errors,
        } => krypton_parser::diagnostics::render_errors(path, mod_source, errors),
    }
}

/// Render type errors against the root file (used by tests that construct SpannedTypeError directly).
pub fn render_type_errors(filename: &str, source: &str, errors: &[SpannedTypeError]) -> String {
    let mut output = String::new();
    for err in errors {
        output.push_str(&render_type_error_with_source(filename, source, err, None));
    }
    output
}

/// Render a single type error as an ariadne diagnostic.
///
/// If `error_source` is provided, renders against that module's file/source
/// instead of the root file.
fn render_type_error_with_source(
    filename: &str,
    source: &str,
    err: &SpannedTypeError,
    error_source: Option<&(String, String)>,
) -> String {
    let mut output = Vec::new();

    let (start, end) = err.span;
    let code = err.error.error_code();
    let message = err.format_message();

    // Use the module's filename/source if the error originated in a module
    let (err_file, err_src) = match error_source {
        Some((path, src)) => (path.as_str(), src.as_str()),
        None => (filename, source),
    };

    let mut report = Report::build(ReportKind::Error, (err_file.to_string(), start..end))
        .with_config(Config::new().with_index_type(IndexType::Byte))
        .with_code(code.to_string())
        .with_message(&message)
        .with_label(
            Label::new((err_file.to_string(), start..end))
                .with_message(format!("{}: {}", code, &message))
                .with_color(Color::Red),
        );

    // Build source table — include both root and module source if different
    let mut all_sources = vec![(err_file.to_string(), err_src.to_string())];
    if err_file != filename {
        all_sources.push((filename.to_string(), source.to_string()));
    }

    if let Some(sec) = &err.secondary_span {
        let (sec_start, sec_end) = sec.span;
        let sec_file = sec.source_file.as_deref().unwrap_or(err_file);
        report = report.with_label(
            Label::new((sec_file.to_string(), sec_start..sec_end))
                .with_message(&sec.message)
                .with_color(Color::Blue),
        );
        if let Some(mod_path) = &sec.source_file {
            if mod_path.as_str() != err_file {
                if let Some(sec_src) = StdlibLoader::get_source(mod_path) {
                    all_sources.push((mod_path.clone(), sec_src.to_string()));
                }
            }
        }
    }

    if let Some(help) = err.format_help() {
        report = report.with_help(help);
    }

    if let Some(note) = &err.note {
        report = report.with_note(note);
    }

    report
        .finish()
        .write(sources(all_sources), &mut output)
        .unwrap();

    String::from_utf8(output).unwrap()
}
