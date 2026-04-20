use rustc_hash::FxHashSet;

use krypton_diagnostics::{sort_diagnostics, Diagnostic, DiagnosticLabel, Severity, SourceEntry};

use crate::infer::InferError;
use crate::unify::SpannedTypeError;
use krypton_modules::stdlib_loader::StdlibLoader;

/// Lower a single `InferError` into the shared diagnostic model.
pub fn lower_infer_error(
    filename: &str,
    source: &str,
    err: &InferError,
) -> (Vec<Diagnostic>, Vec<SourceEntry>) {
    match err {
        InferError::TypeError {
            error,
            error_source,
        } => lower_type_error(filename, source, error, error_source.as_ref()),
        InferError::ModuleParseError {
            path,
            source: mod_source,
            errors,
        } => krypton_parser::diagnostics::lower_parse_errors(path, mod_source, errors),
    }
}

/// Lower multiple `InferError`s into the shared diagnostic model with deterministic ordering.
pub fn lower_infer_errors(
    filename: &str,
    source: &str,
    errors: &[InferError],
) -> (Vec<Diagnostic>, Vec<SourceEntry>) {
    let mut all_diags = Vec::new();
    let mut all_sources = Vec::new();
    let mut seen_sources: FxHashSet<String> = FxHashSet::default();

    for err in errors {
        let (diags, sources) = lower_infer_error(filename, source, err);
        all_diags.extend(diags);
        for src in sources {
            if seen_sources.insert(src.filename.clone()) {
                all_sources.push(src);
            }
        }
    }

    sort_diagnostics(&mut all_diags);
    (all_diags, all_sources)
}

fn lower_type_error(
    filename: &str,
    source: &str,
    err: &SpannedTypeError,
    error_source: Option<&(String, String)>,
) -> (Vec<Diagnostic>, Vec<SourceEntry>) {
    let code = err.error.error_code();
    let message = err.format_message();

    let (err_file, err_src) = match error_source {
        Some((path, src)) => (path.as_str(), src.as_str()),
        None => (filename, source),
    };

    let mut all_sources = vec![SourceEntry {
        filename: err_file.to_string(),
        source: err_src.to_string(),
    }];
    if err_file != filename {
        all_sources.push(SourceEntry {
            filename: filename.to_string(),
            source: source.to_string(),
        });
    }

    let mut secondary_labels = vec![];
    if let Some(sec) = &err.secondary_span {
        let sec_file = sec.source_file.as_deref().unwrap_or(err_file);
        secondary_labels.push(DiagnosticLabel {
            span: sec.span,
            message: sec.message.clone(),
            filename: sec_file.to_string(),
        });
        if let Some(mod_path) = &sec.source_file {
            if mod_path.as_str() != err_file {
                if let Some(sec_src) = StdlibLoader::get_source(mod_path) {
                    all_sources.push(SourceEntry {
                        filename: mod_path.clone(),
                        source: sec_src.to_string(),
                    });
                }
            }
        }
    }

    let diag = Diagnostic {
        severity: Severity::Error,
        code: code.to_string(),
        message,
        primary_file: err_file.to_string(),
        primary_span: Some(err.span),
        primary_label: Some(format!("{}: {}", code, err.format_message())),
        secondary_labels,
        help: err.format_help(),
        note: err.note.clone().or_else(|| err.error.note()),
    };

    (vec![diag], all_sources)
}
