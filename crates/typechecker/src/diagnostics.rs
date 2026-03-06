use ariadne::{sources, Color, Config, IndexType, Label, Report, ReportKind};

use crate::unify::SpannedTypeError;

/// Render type errors as ariadne diagnostics, returning the rendered string.
pub fn render_type_errors(filename: &str, source: &str, errors: &[SpannedTypeError]) -> String {
    let mut output = Vec::new();
    let fname = filename.to_string();
    let src = source.to_string();

    for err in errors {
        let (start, end) = err.span;
        let code = err.error.error_code();
        let message = err.error.to_string();

        let mut report = Report::build(ReportKind::Error, (fname.clone(), start..end))
            .with_config(Config::new().with_index_type(IndexType::Byte))
            .with_code(code.to_string())
            .with_message(&message)
            .with_label(
                Label::new((fname.clone(), start..end))
                    .with_message(format!("{}: {}", code, &message))
                    .with_color(Color::Red),
            );

        if let Some(help) = err.error.help() {
            report = report.with_help(help);
        }

        if let Some(note) = &err.note {
            report = report.with_note(note);
        }

        report
            .finish()
            .write(sources([(fname.clone(), src.clone())]), &mut output)
            .unwrap();
    }

    String::from_utf8(output).unwrap()
}
