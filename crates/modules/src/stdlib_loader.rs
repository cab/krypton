pub struct StdlibLoader;

impl StdlibLoader {
    const OPTION: &str = include_str!("../../../stdlib/core/option.kr");
    const RESULT: &str = include_str!("../../../stdlib/core/result.kr");
    const LIST: &str = include_str!("../../../stdlib/core/list.kr");
    const STRING: &str = include_str!("../../../stdlib/core/string.kr");
    const ORDERING: &str = include_str!("../../../stdlib/core/ordering.kr");
    const IO: &str = include_str!("../../../stdlib/core/io.kr");
    const VEC: &str = include_str!("../../../stdlib/core/vec.kr");
    const PRELUDE: &str = include_str!("../../../stdlib/prelude.kr");

    /// Module paths for prelude types (auto-seeded without import).
    pub const PRELUDE_MODULES: &[&str] = &[
        "core/option",
        "core/result",
        "core/list",
        "core/ordering",
    ];

    pub fn get_source(module_path: &str) -> Option<&'static str> {
        match module_path {
            "core/option" => Some(Self::OPTION),
            "core/result" => Some(Self::RESULT),
            "core/list" => Some(Self::LIST),
            "core/string" => Some(Self::STRING),
            "core/ordering" => Some(Self::ORDERING),
            "core/io" => Some(Self::IO),
            "core/vec" => Some(Self::VEC),
            "prelude" => Some(Self::PRELUDE),
            _ => None,
        }
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
        // include_str! embeds at compile time, so this is always embedded content
        let source = StdlibLoader::get_source("core/option").unwrap();
        assert!(source.contains("type Option"));
    }
}
