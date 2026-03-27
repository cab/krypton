use ariadne::{sources, Color, Config, IndexType, Label, Report, ReportKind};
use serde::Serialize;

pub type Span = (usize, usize);

#[derive(Debug, Clone, Serialize)]
pub struct SourceEntry {
    pub filename: String,
    pub source: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone, Serialize)]
pub struct DiagnosticLabel {
    pub span: Span,
    pub message: String,
    pub filename: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: String,
    pub message: String,
    pub primary_file: String,
    pub primary_span: Option<Span>,
    pub primary_label: Option<String>,
    pub secondary_labels: Vec<DiagnosticLabel>,
    pub help: Option<String>,
    pub note: Option<String>,
}

pub trait DiagnosticRenderer {
    type Output;
    fn render(&self, diagnostic: &Diagnostic, sources: &[SourceEntry]) -> Self::Output;
}

pub struct AriadneRenderer;
pub struct PlainTextRenderer;

impl DiagnosticRenderer for AriadneRenderer {
    type Output = String;

    fn render(&self, diagnostic: &Diagnostic, src_entries: &[SourceEntry]) -> String {
        render_ariadne(diagnostic, src_entries, true)
    }
}

impl DiagnosticRenderer for PlainTextRenderer {
    type Output = String;

    fn render(&self, diagnostic: &Diagnostic, src_entries: &[SourceEntry]) -> String {
        render_ariadne(diagnostic, src_entries, false)
    }
}

fn render_ariadne(diagnostic: &Diagnostic, src_entries: &[SourceEntry], color: bool) -> String {
    let (start, end) = match diagnostic.primary_span {
        Some(span) => span,
        None => {
            // Spanless: plain error line
            if diagnostic.code.is_empty() {
                return format!("error: {}\n", diagnostic.message);
            }
            return format!("error[{}]: {}\n", diagnostic.code, diagnostic.message);
        }
    };

    let report_kind = match diagnostic.severity {
        Severity::Error => ReportKind::Error,
        Severity::Warning => ReportKind::Warning,
    };

    let mut report =
        Report::build(report_kind, (diagnostic.primary_file.clone(), start..end))
            .with_config(
                Config::new()
                    .with_index_type(IndexType::Byte)
                    .with_color(color),
            )
            .with_code(&diagnostic.code)
            .with_message(&diagnostic.message);

    if let Some(label_msg) = &diagnostic.primary_label {
        report = report.with_label(
            Label::new((diagnostic.primary_file.clone(), start..end))
                .with_message(label_msg)
                .with_color(Color::Red),
        );
    }

    for sec in &diagnostic.secondary_labels {
        let (sec_start, sec_end) = sec.span;
        report = report.with_label(
            Label::new((sec.filename.clone(), sec_start..sec_end))
                .with_message(&sec.message)
                .with_color(Color::Blue),
        );
    }

    if let Some(help) = &diagnostic.help {
        report = report.with_help(help);
    }

    if let Some(note) = &diagnostic.note {
        report = report.with_note(note);
    }

    let all_sources: Vec<(String, String)> = src_entries
        .iter()
        .map(|e| (e.filename.clone(), e.source.clone()))
        .collect();

    let mut output = Vec::new();
    report
        .finish()
        .write(sources(all_sources), &mut output)
        .unwrap();
    String::from_utf8(output).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_diagnostic() -> Diagnostic {
        Diagnostic {
            severity: Severity::Error,
            code: "E0001".to_string(),
            message: "type mismatch".to_string(),
            primary_file: "test.kr".to_string(),
            primary_span: Some((10, 15)),
            primary_label: Some("E0001: type mismatch".to_string()),
            secondary_labels: vec![],
            help: None,
            note: None,
        }
    }

    fn sample_sources() -> Vec<SourceEntry> {
        vec![SourceEntry {
            filename: "test.kr".to_string(),
            source: "fun main() = 42\n".to_string(),
        }]
    }

    #[test]
    fn ariadne_renderer_contains_code_and_message() {
        let diag = sample_diagnostic();
        let sources = sample_sources();
        let output = AriadneRenderer.render(&diag, &sources);
        assert!(output.contains("E0001"), "should contain error code: {output}");
        assert!(
            output.contains("type mismatch"),
            "should contain message: {output}"
        );
        assert!(
            output.contains("test.kr"),
            "should contain filename: {output}"
        );
    }

    #[test]
    fn plain_text_renderer_no_ansi() {
        let diag = sample_diagnostic();
        let sources = sample_sources();
        let output = PlainTextRenderer.render(&diag, &sources);
        assert!(
            !output.contains("\x1b["),
            "should not contain ANSI escape codes: {output}"
        );
        assert!(output.contains("E0001"), "should contain error code: {output}");
        assert!(
            output.contains("type mismatch"),
            "should contain message: {output}"
        );
    }

    #[test]
    fn spanless_diagnostic_uses_plain_format() {
        let diag = Diagnostic {
            severity: Severity::Error,
            code: "C0002".to_string(),
            message: "no main function found".to_string(),
            primary_file: "test.kr".to_string(),
            primary_span: None,
            primary_label: None,
            secondary_labels: vec![],
            help: None,
            note: None,
        };
        let sources = sample_sources();
        let output = AriadneRenderer.render(&diag, &sources);
        assert_eq!(output, "error[C0002]: no main function found\n");
    }

    #[test]
    fn secondary_labels_rendered() {
        let diag = Diagnostic {
            severity: Severity::Error,
            code: "E0101".to_string(),
            message: "value already moved".to_string(),
            primary_file: "test.kr".to_string(),
            primary_span: Some((10, 15)),
            primary_label: Some("used here".to_string()),
            secondary_labels: vec![DiagnosticLabel {
                span: (0, 5),
                message: "first use here".to_string(),
                filename: "test.kr".to_string(),
            }],
            help: None,
            note: None,
        };
        let sources = sample_sources();
        let output = PlainTextRenderer.render(&diag, &sources);
        assert!(
            output.contains("first use here"),
            "should contain secondary label: {output}"
        );
    }

    #[test]
    fn help_and_note_rendered() {
        let diag = Diagnostic {
            severity: Severity::Error,
            code: "E0001".to_string(),
            message: "type mismatch".to_string(),
            primary_file: "test.kr".to_string(),
            primary_span: Some((10, 15)),
            primary_label: Some("E0001: type mismatch".to_string()),
            secondary_labels: vec![],
            help: Some("try converting the type".to_string()),
            note: Some("expected Int, found String".to_string()),
        };
        let sources = sample_sources();
        let output = PlainTextRenderer.render(&diag, &sources);
        assert!(
            output.contains("try converting the type"),
            "should contain help text: {output}"
        );
        assert!(
            output.contains("expected Int, found String"),
            "should contain note: {output}"
        );
    }
}
