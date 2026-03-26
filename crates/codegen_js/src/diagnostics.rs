use ariadne::{sources, Color, Config, IndexType, Label, Report, ReportKind};

use crate::emit::{JsCodegenError, MissingExternTarget};

const MISSING_EXTERN_TARGET_CODE: &str = "J0001";

/// Render a JS codegen error using the same diagnostic pipeline as parser/typechecker/JVM codegen.
pub fn render_js_codegen_error(filename: &str, source: &str, error: &JsCodegenError) -> String {
    match error {
        JsCodegenError::MissingExternTarget(items) => {
            render_missing_extern_targets(filename, source, items)
        }
        _ => format!("error: {error}\n"),
    }
}

fn render_missing_extern_targets(
    filename: &str,
    source: &str,
    items: &[MissingExternTarget],
) -> String {
    let mut output = String::new();

    for item in items {
        let (report_file, report_source) = if item.is_root_module {
            (filename.to_string(), source.to_string())
        } else if let Some(module_source) = &item.referencing_module_source {
            (format!("{}.kr", item.referencing_module), module_source.clone())
        } else {
            output.push_str(&format!(
                "error[{MISSING_EXTERN_TARGET_CODE}]: extern function `{}` referenced from module `{}` has no JS target declaration (available targets: {})\n",
                item.function_name,
                item.referencing_module,
                item.available_targets.join(", ")
            ));
            continue;
        };

        let mut source_map = vec![(report_file.clone(), report_source.clone())];
        let use_range = normalize_span(item.use_span, report_source.len());
        let declaration_file = format!("{}.kr", item.declaring_module);
        let declaration_range = item
            .declaring_module_source
            .as_ref()
            .map(|decl_source| normalize_span(item.declaration_span, decl_source.len()));
        if let Some(decl_source) = &item.declaring_module_source {
            if declaration_file != report_file {
                source_map.push((declaration_file.clone(), decl_source.clone()));
            }
        }

        let mut buffer = Vec::new();
        let mut report = Report::build(ReportKind::Error, (report_file.clone(), use_range.clone()))
            .with_config(Config::new().with_index_type(IndexType::Byte))
            .with_code(MISSING_EXTERN_TARGET_CODE)
            .with_message(format!(
                "extern function `{}` referenced from module `{}` has no JS target declaration",
                item.function_name, item.referencing_module
            ))
            .with_label(
                Label::new((report_file.clone(), use_range))
                    .with_message("reachable JS code in this module requires this extern")
                    .with_color(Color::Red),
            );
        if let (Some(_), Some(range)) = (&item.declaring_module_source, declaration_range) {
            report = report.with_label(
                Label::new((declaration_file.clone(), range))
                    .with_message("extern declared here")
                    .with_color(Color::Blue),
            );
        }
        let report = report
            .with_note(format!(
                "available targets: {}",
                item.available_targets.join(", ")
            ))
            .finish();
        report
            .write(sources(source_map), &mut buffer)
            .unwrap();
        output.push_str(&String::from_utf8(buffer).unwrap());
    }

    output
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
        let output = render_js_codegen_error("test.kr", "fun main() = println(42)\n", &err);
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
