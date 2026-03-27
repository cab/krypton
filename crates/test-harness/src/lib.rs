use std::path::{Path, PathBuf};

/// Expected outcome parsed from a fixture file's header comments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expectation {
    /// The program should compile/run without errors.
    Ok,
    /// The program should produce a specific error code.
    Error(String),
    /// The program should produce specific output on stdout.
    Output(String),
    /// The program should panic (exit non-zero). Optional message to match in stderr.
    Panic(Option<String>),
}

/// A loaded fixture file with its parsed expectations.
#[derive(Debug, Clone)]
pub struct Fixture {
    pub path: PathBuf,
    pub source: String,
    pub expectations: Vec<Expectation>,
    /// Targets to skip: `(target, reason)` from `# skip: target(reason)` directives.
    pub skip_targets: Vec<(String, String)>,
}

/// Parse `# expect:` header comments from source text.
///
/// Recognized forms:
/// - `# expect: ok`
/// - `# expect: error E0001`
/// - `# expect: output "hello world"`
/// - `# expect: output 42`
///
/// Lines without `# expect:` are ignored.
/// If no expectations are found, returns an empty vec (caller decides default).
pub fn parse_expectations(source: &str) -> Vec<Expectation> {
    let mut expectations = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix("# expect:") else {
            continue;
        };
        let rest = rest.trim();
        if rest.eq_ignore_ascii_case("ok") {
            expectations.push(Expectation::Ok);
        } else if let Some(code) = rest.strip_prefix("error") {
            let code = code.trim();
            if !code.is_empty() {
                expectations.push(Expectation::Error(code.to_string()));
            }
        } else if let Some(text) = rest.strip_prefix("panic") {
            let text = text.trim();
            if text.is_empty() {
                expectations.push(Expectation::Panic(None));
            } else if text.starts_with('"') && text.ends_with('"') && text.len() >= 2 {
                let msg = text[1..text.len() - 1]
                    .replace("\\\\", "\x00")
                    .replace("\\n", "\n")
                    .replace("\\\"", "\"")
                    .replace('\x00', "\\");
                expectations.push(Expectation::Panic(Some(msg)));
            } else {
                expectations.push(Expectation::Panic(Some(text.to_string())));
            }
        } else if let Some(text) = rest.strip_prefix("output") {
            let text = text.trim();
            // Strip surrounding quotes if present, then unescape \n
            let text = if text.starts_with('"') && text.ends_with('"') && text.len() >= 2 {
                // Use \x00 as a temporary placeholder for escaped backslashes so that
                // "\\n" (literal backslash + n) is not confused with "\n" (newline).
                // Assumes test expectations never contain literal NUL bytes.
                text[1..text.len() - 1]
                    .replace("\\\\", "\x00")
                    .replace("\\n", "\n")
                    .replace("\\\"", "\"")
                    .replace('\x00', "\\")
            } else {
                text.to_string()
            };
            expectations.push(Expectation::Output(text));
        }
    }
    expectations
}

/// Parse `# skip: target(reason)` directives from source text.
pub fn parse_skip_targets(source: &str) -> Vec<(String, String)> {
    let mut skips = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        let Some(rest) = trimmed.strip_prefix("# skip:") else {
            continue;
        };
        let rest = rest.trim();
        // Expected format: target(reason)
        if let Some(paren_pos) = rest.find('(') {
            if rest.ends_with(')') {
                let target = rest[..paren_pos].trim().to_string();
                let reason = rest[paren_pos + 1..rest.len() - 1].to_string();
                if !target.is_empty() && !reason.is_empty() {
                    skips.push((target, reason));
                }
            }
        }
    }
    skips
}

/// Discover `.kr` fixture files directly in `dir` (non-recursive).
///
/// Returns paths sorted for determinism.
pub fn discover_fixtures(dir: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    if !dir.exists() {
        return paths;
    }
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("failed to read directory {}: {e}", dir.display()));
    for entry in entries {
        let Ok(entry) = entry else { continue };
        let path = entry.path();
        if path.is_file() && path.extension().is_some_and(|ext| ext == "kr") {
            paths.push(path);
        }
    }
    paths.sort();
    paths
}

/// Load a fixture file: read its source and parse header expectations.
pub fn load_fixture(path: &Path) -> Fixture {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("failed to read fixture {}: {e}", path.display()));
    let expectations = parse_expectations(&source);
    let skip_targets = parse_skip_targets(&source);
    Fixture {
        path: path.to_path_buf(),
        source,
        expectations,
        skip_targets,
    }
}
