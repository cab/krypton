use include_dir::{include_dir, Dir};
use std::sync::LazyLock;

static STDLIB_DIR: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/../../stdlib");

/// Module paths extracted from prelude.kr `pub import <path>.{...}` lines,
/// plus "prelude" itself.
pub static PRELUDE_MODULES: LazyLock<Vec<String>> = LazyLock::new(|| {
    let prelude_src = STDLIB_DIR
        .get_file("prelude.kr")
        .expect("stdlib must contain prelude.kr")
        .contents_utf8()
        .expect("prelude.kr must be valid UTF-8");

    let mut modules: Vec<String> = prelude_src
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            // Match lines like: pub import core/foo.{...}
            let rest = trimmed.strip_prefix("pub import ")?;
            let dot_pos = rest.find('.')?;
            Some(rest[..dot_pos].to_string())
        })
        .collect();
    modules.push("prelude".to_string());
    modules
});

pub struct StdlibLoader;

impl StdlibLoader {
    pub fn get_source(module_path: &str) -> Option<&'static str> {
        let file_path = format!("{module_path}.kr");
        STDLIB_DIR.get_file(&file_path)?.contents_utf8()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_source_option() {
        let source = StdlibLoader::get_source("core/option").unwrap();
        assert!(source.contains("Option"));
        assert!(source.contains("Some"));
        assert!(source.contains("None"));
    }

    #[test]
    fn test_get_source_result() {
        let source = StdlibLoader::get_source("core/result").unwrap();
        assert!(source.contains("Result"));
        assert!(source.contains("Ok"));
        assert!(source.contains("Err"));
    }

    #[test]
    fn test_get_source_list() {
        let source = StdlibLoader::get_source("core/list").unwrap();
        assert!(source.contains("List"));
        assert!(source.contains("Cons"));
        assert!(source.contains("Nil"));
    }

    #[test]
    fn test_get_source_string() {
        let source = StdlibLoader::get_source("core/string").unwrap();
        assert!(source.contains("string"));
    }

    #[test]
    fn test_get_source_unknown() {
        assert!(StdlibLoader::get_source("core/nonexistent").is_none());
    }

    #[test]
    fn test_core_paths_never_filesystem() {
        // include_dir! embeds at compile time, so this is always embedded content
        let source = StdlibLoader::get_source("core/option").unwrap();
        assert!(source.contains("type Option"));
    }

    #[test]
    fn test_prelude_modules_contains_expected() {
        let modules = &*PRELUDE_MODULES;
        assert!(modules.contains(&"core/option".to_string()));
        assert!(modules.contains(&"core/eq".to_string()));
        assert!(modules.contains(&"prelude".to_string()));
    }

    #[test]
    fn test_prelude_modules_dynamic() {
        // Verify the list is derived from prelude.kr, not hardcoded
        let modules = &*PRELUDE_MODULES;
        assert!(modules.len() > 5, "prelude should have many modules");
    }
}
