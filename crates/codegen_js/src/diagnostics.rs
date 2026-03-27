use krypton_diagnostics::{Diagnostic, DiagnosticLabel, Severity, SourceEntry};

use crate::emit::{JsCodegenError, MissingExternTarget};

const MISSING_EXTERN_TARGET_CODE: &str = "J0001";

/// Lower a JS codegen error into the shared diagnostic model.
pub fn lower_js_codegen_error(
    filename: &str,
    source: &str,
    error: &JsCodegenError,
) -> (Vec<Diagnostic>, Vec<SourceEntry>) {
    match error {
        JsCodegenError::MissingExternTarget(items) => {
            lower_missing_extern_targets(filename, source, items)
        }
        _ => {
            // Spanless errors: LowerError, UnsupportedFeature
            let diag = Diagnostic {
                severity: Severity::Error,
                code: String::new(),
                message: error.to_string(),
                primary_file: filename.to_string(),
                primary_span: None,
                primary_label: None,
                secondary_labels: vec![],
                help: None,
                note: None,
            };
            let sources = vec![SourceEntry {
                filename: filename.to_string(),
                source: source.to_string(),
            }];
            (vec![diag], sources)
        }
    }
}

fn lower_missing_extern_targets(
    filename: &str,
    source: &str,
    items: &[MissingExternTarget],
) -> (Vec<Diagnostic>, Vec<SourceEntry>) {
    let mut diags = Vec::new();
    let mut all_sources = Vec::new();
    let mut seen_sources = std::collections::HashSet::new();

    for item in items {
        let (report_file, report_source) = if item.is_root_module {
            (filename.to_string(), source.to_string())
        } else if let Some(module_source) = &item.referencing_module_source {
            (format!("{}.kr", item.referencing_module), module_source.clone())
        } else {
            // No source available — spanless fallback
            diags.push(Diagnostic {
                severity: Severity::Error,
                code: MISSING_EXTERN_TARGET_CODE.to_string(),
                message: format!(
                    "extern function `{}` referenced from module `{}` has no JS target declaration (available targets: {})",
                    item.function_name,
                    item.referencing_module,
                    item.available_targets.join(", ")
                ),
                primary_file: filename.to_string(),
                primary_span: None,
                primary_label: None,
                secondary_labels: vec![],
                help: None,
                note: None,
            });
            continue;
        };

        // Add report file source
        if seen_sources.insert(report_file.clone()) {
            all_sources.push(SourceEntry {
                filename: report_file.clone(),
                source: report_source.clone(),
            });
        }

        let use_span = normalize_span(item.use_span, report_source.len());

        let mut secondary_labels = vec![];
        let declaration_file = format!("{}.kr", item.declaring_module);
        if let Some(decl_source) = &item.declaring_module_source {
            let decl_span = normalize_span(item.declaration_span, decl_source.len());
            secondary_labels.push(DiagnosticLabel {
                span: (decl_span.start, decl_span.end),
                message: "extern declared here".to_string(),
                filename: declaration_file.clone(),
            });
            if seen_sources.insert(declaration_file.clone()) {
                all_sources.push(SourceEntry {
                    filename: declaration_file,
                    source: decl_source.clone(),
                });
            }
        }

        diags.push(Diagnostic {
            severity: Severity::Error,
            code: MISSING_EXTERN_TARGET_CODE.to_string(),
            message: format!(
                "extern function `{}` referenced from module `{}` has no JS target declaration",
                item.function_name, item.referencing_module
            ),
            primary_file: report_file,
            primary_span: Some((use_span.start, use_span.end)),
            primary_label: Some("reachable JS code in this module requires this extern".to_string()),
            secondary_labels,
            help: None,
            note: Some(format!(
                "available targets: {}",
                item.available_targets.join(", ")
            )),
        });
    }

    (diags, all_sources)
}

fn normalize_span((start, end): (usize, usize), source_len: usize) -> std::ops::Range<usize> {
    let start = start.min(source_len);
    let mut end = end.min(source_len);
    if end <= start {
        end = (start + 1).min(source_len);
    }
    start..end
}

#[cfg(test)]
mod tests {
    use super::*;
    use krypton_diagnostics::{DiagnosticRenderer, PlainTextRenderer};

    fn render(error: &JsCodegenError, filename: &str, source: &str) -> String {
        let (diags, srcs) = lower_js_codegen_error(filename, source, error);
        diags.iter().map(|d| PlainTextRenderer.render(d, &srcs)).collect()
    }

    #[test]
    fn render_missing_extern_target_root_module() {
        let err = JsCodegenError::MissingExternTarget(vec![MissingExternTarget {
            function_name: "println".to_string(),
            referencing_module: "test".to_string(),
            available_targets: vec!["java:krypton.runtime.KryptonIO".to_string()],
            referencing_module_source: None,
            is_root_module: true,
            use_span: (13, 20),
            declaring_module: "core/io".to_string(),
            declaring_module_source: Some("extern java println(Int): Unit\n".to_string()),
            declaration_span: (12, 19),
        }]);
        let output = render(&err, "test.kr", "fun main() = println(42)\n");
        assert!(output.contains("J0001"), "should contain error code: {output}");
        assert!(
            output.contains("println"),
            "should mention function name: {output}"
        );
        assert!(
            output.contains("available targets: java:krypton.runtime.KryptonIO"),
            "should mention available targets: {output}"
        );
    }
}
