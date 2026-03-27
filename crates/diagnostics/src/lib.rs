use ariadne::{sources, Color, Config, IndexType, Label, Report, ReportKind};
use serde::Serialize;

pub type Span = (usize, usize);

#[derive(Debug, Clone, Serialize)]
pub struct SourceEntry {
    pub filename: String,
    pub source: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DiagnosticLabel {
    pub span: Span,
    pub message: String,
    pub filename: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
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
pub struct JsonRenderer;

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

impl DiagnosticRenderer for JsonRenderer {
    type Output = String;

    fn render(&self, diagnostic: &Diagnostic, _sources: &[SourceEntry]) -> String {
        serde_json::to_string(diagnostic).expect("Diagnostic serialization cannot fail")
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

/// Sort diagnostics by file, then span position, then error code for deterministic output.
pub fn sort_diagnostics(diags: &mut [Diagnostic]) {
    diags.sort_by(|a, b| {
        a.primary_file
            .cmp(&b.primary_file)
            .then(a.primary_span.cmp(&b.primary_span))
            .then(a.code.cmp(&b.code))
    });
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
    fn json_renderer_round_trips_diagnostic() {
        let diag = Diagnostic {
            severity: Severity::Error,
            code: "E0001".to_string(),
            message: "type mismatch".to_string(),
            primary_file: "test.kr".to_string(),
            primary_span: Some((10, 15)),
            primary_label: Some("expected Int".to_string()),
            secondary_labels: vec![DiagnosticLabel {
                span: (0, 5),
                message: "first defined here".to_string(),
                filename: "other.kr".to_string(),
            }],
            help: Some("try converting the type".to_string()),
            note: Some("expected Int, found String".to_string()),
        };
        let sources = sample_sources();
        let output = JsonRenderer.render(&diag, &sources);
        let json: serde_json::Value = serde_json::from_str(&output).expect("valid JSON");
        assert_eq!(json["severity"], "Error");
        assert_eq!(json["code"], "E0001");
        assert_eq!(json["message"], "type mismatch");
        assert_eq!(json["primary_file"], "test.kr");
        assert_eq!(json["primary_span"], serde_json::json!([10, 15]));
        assert_eq!(json["primary_label"], "expected Int");
        assert_eq!(json["secondary_labels"][0]["span"], serde_json::json!([0, 5]));
        assert_eq!(json["secondary_labels"][0]["message"], "first defined here");
        assert_eq!(json["secondary_labels"][0]["filename"], "other.kr");
        assert_eq!(json["help"], "try converting the type");
        assert_eq!(json["note"], "expected Int, found String");
    }

    #[test]
    fn json_renderer_spanless_diagnostic() {
        let diag = Diagnostic {
            severity: Severity::Warning,
            code: "W0001".to_string(),
            message: "unused variable".to_string(),
            primary_file: "test.kr".to_string(),
            primary_span: None,
            primary_label: None,
            secondary_labels: vec![],
            help: None,
            note: None,
        };
        let sources = sample_sources();
        let output = JsonRenderer.render(&diag, &sources);
        let json: serde_json::Value = serde_json::from_str(&output).expect("valid JSON");
        assert_eq!(json["severity"], "Warning");
        assert!(json["primary_span"].is_null());
        assert!(json["primary_label"].is_null());
        assert_eq!(json["secondary_labels"], serde_json::json!([]));
        assert!(json["help"].is_null());
        assert!(json["note"].is_null());
    }

    #[test]
    fn json_renderer_ignores_sources() {
        let diag = sample_diagnostic();
        let sources1 = sample_sources();
        let sources2 = vec![SourceEntry {
            filename: "different.kr".to_string(),
            source: "completely different content\n".to_string(),
        }];
        let output1 = JsonRenderer.render(&diag, &sources1);
        let output2 = JsonRenderer.render(&diag, &sources2);
        assert_eq!(output1, output2);
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
