use std::ffi::OsStr;
use std::io;
use std::path::{Path, PathBuf};

/// Two disjoint lists of project source files, each sorted lexicographically
/// by path relative to the `src/` directory passed to [`walk_project_sources`].
#[derive(Debug)]
pub struct SourceFiles {
    /// `*.kr` files whose filename does not end with `_test.kr`.
    // Consumed by the two-phase `krypton test` compile pipeline.
    #[allow(dead_code)]
    pub sources: Vec<PathBuf>,
    /// `*.kr` files whose filename ends with `_test.kr`.
    pub tests: Vec<PathBuf>,
}

/// Recursively walk `src_dir`, classifying every `*.kr` file into either the
/// `sources` or `tests` list. Hidden entries (any path segment beginning with
/// `.`) and symlinks are skipped. Paths are returned absolute; each list is
/// sorted lexicographically by its path relative to `src_dir` so ordering is
/// deterministic across platforms and directory-traversal order.
pub fn walk_project_sources(src_dir: &Path) -> io::Result<SourceFiles> {
    if !src_dir.exists() {
        return Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("source directory not found: {}", src_dir.display()),
        ));
    }

    let mut sources: Vec<PathBuf> = Vec::new();
    let mut tests: Vec<PathBuf> = Vec::new();
    let mut stack: Vec<PathBuf> = vec![src_dir.to_path_buf()];

    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir)? {
            let entry = entry?;
            let file_name = entry.file_name();

            if starts_with_dot(&file_name) {
                continue;
            }

            // DirEntry::file_type() does not follow symlinks, matching the
            // symlinks-not-followed invariant.
            let file_type = entry.file_type()?;
            if file_type.is_symlink() {
                continue;
            }

            let path = entry.path();
            if file_type.is_dir() {
                stack.push(path);
                continue;
            }
            if !file_type.is_file() {
                continue;
            }

            if ends_with_test_kr(&file_name) {
                tests.push(path);
            } else if has_kr_extension(&file_name) {
                sources.push(path);
            }
        }
    }

    sort_by_relative_path(&mut sources, src_dir);
    sort_by_relative_path(&mut tests, src_dir);

    Ok(SourceFiles { sources, tests })
}

fn starts_with_dot(name: &OsStr) -> bool {
    name.as_encoded_bytes().first() == Some(&b'.')
}

fn ends_with_test_kr(name: &OsStr) -> bool {
    name.as_encoded_bytes().ends_with(b"_test.kr")
}

fn has_kr_extension(name: &OsStr) -> bool {
    Path::new(name).extension() == Some(OsStr::new("kr"))
}

fn sort_by_relative_path(paths: &mut [PathBuf], base: &Path) {
    paths.sort_by(|a, b| {
        let ra = a.strip_prefix(base).unwrap_or(a.as_path());
        let rb = b.strip_prefix(base).unwrap_or(b.as_path());
        ra.cmp(rb)
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    fn write_file(path: &Path, content: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, content).unwrap();
    }

    fn relative_paths(paths: &[PathBuf], base: &Path) -> Vec<String> {
        paths
            .iter()
            .map(|p| {
                p.strip_prefix(base)
                    .unwrap()
                    .to_string_lossy()
                    .replace('\\', "/")
            })
            .collect()
    }

    #[test]
    fn empty_src_yields_empty_lists() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        fs::create_dir_all(&src).unwrap();

        let result = walk_project_sources(&src).unwrap();
        assert!(result.sources.is_empty());
        assert!(result.tests.is_empty());
    }

    #[test]
    fn missing_src_is_error() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        // intentionally not created

        let err = walk_project_sources(&src).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn flat_layout_classifies_by_suffix() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        write_file(&src.join("main.kr"), "");
        write_file(&src.join("math.kr"), "");
        write_file(&src.join("math_test.kr"), "");

        let result = walk_project_sources(&src).unwrap();
        assert_eq!(
            relative_paths(&result.sources, &src),
            vec!["main.kr", "math.kr"]
        );
        assert_eq!(relative_paths(&result.tests, &src), vec!["math_test.kr"]);
    }

    #[test]
    fn nested_paths_are_discovered() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        write_file(&src.join("main.kr"), "");
        write_file(&src.join("parser/lexer.kr"), "");
        write_file(&src.join("parser/lexer_test.kr"), "");

        let result = walk_project_sources(&src).unwrap();
        assert_eq!(
            relative_paths(&result.sources, &src),
            vec!["main.kr", "parser/lexer.kr"]
        );
        assert_eq!(
            relative_paths(&result.tests, &src),
            vec!["parser/lexer_test.kr"]
        );
    }

    #[test]
    fn sort_order_is_lexicographic_by_relative_path() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        // Written in a non-sorted order to exercise the sort.
        write_file(&src.join("z_test.kr"), "");
        write_file(&src.join("parser/a_test.kr"), "");
        write_file(&src.join("a_test.kr"), "");

        let result = walk_project_sources(&src).unwrap();
        assert_eq!(
            relative_paths(&result.tests, &src),
            vec!["a_test.kr", "parser/a_test.kr", "z_test.kr"]
        );
    }

    #[test]
    fn standalone_test_without_companion_is_collected() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        write_file(&src.join("helpers_test.kr"), "");

        let result = walk_project_sources(&src).unwrap();
        assert!(result.sources.is_empty());
        assert_eq!(
            relative_paths(&result.tests, &src),
            vec!["helpers_test.kr"]
        );
    }

    #[test]
    fn non_kr_files_ignored() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        write_file(&src.join("main.kr"), "");
        write_file(&src.join("README.md"), "");
        write_file(&src.join("main.kr.bak"), "");
        write_file(&src.join("foo.txt"), "");

        let result = walk_project_sources(&src).unwrap();
        assert_eq!(relative_paths(&result.sources, &src), vec!["main.kr"]);
        assert!(result.tests.is_empty());
    }

    #[test]
    fn hidden_entries_skipped() {
        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        write_file(&src.join("main.kr"), "");
        write_file(&src.join(".DS_Store"), "");
        write_file(&src.join(".hidden/foo.kr"), "");

        let result = walk_project_sources(&src).unwrap();
        assert_eq!(relative_paths(&result.sources, &src), vec!["main.kr"]);
        assert!(result.tests.is_empty());
    }

    #[cfg(unix)]
    #[test]
    fn symlinks_not_followed() {
        use std::os::unix::fs::symlink;

        let dir = tempdir().unwrap();
        let src = dir.path().join("src");
        let outside = dir.path().join("outside");
        write_file(&outside.join("a.kr"), "");
        fs::create_dir_all(&src).unwrap();
        symlink(outside.join("a.kr"), src.join("link.kr")).unwrap();
        // Add a regular file so the walk has real content to find.
        write_file(&src.join("main.kr"), "");

        let result = walk_project_sources(&src).unwrap();
        assert_eq!(relative_paths(&result.sources, &src), vec!["main.kr"]);
    }
}
