/// Static invariant: JS codegen must not import TypedModule.
///
/// Lowering happens before codegen. The codegen_js crate receives
/// only IR modules, never TypedModule. This test greps the source files
/// to ensure no one re-introduces a TypedModule dependency.
#[test]
fn js_codegen_does_not_import_typed_module() {
    let src_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut violations = Vec::new();
    collect_violations(&src_dir, &src_dir, &mut violations);

    assert!(
        violations.is_empty(),
        "codegen_js source files must not reference TypedModule (use IR modules instead):\n{}",
        violations.join("\n")
    );
}

fn collect_violations(
    dir: &std::path::Path,
    base: &std::path::Path,
    violations: &mut Vec<String>,
) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_violations(&path, base, violations);
        } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
            let contents = std::fs::read_to_string(&path).unwrap();
            for (lineno, line) in contents.lines().enumerate() {
                if line.contains("TypedModule") && !line.trim_start().starts_with("//") {
                    violations.push(format!(
                        "{}:{}: {}",
                        path.strip_prefix(base).unwrap().display(),
                        lineno + 1,
                        line.trim()
                    ));
                }
            }
        }
    }
}
