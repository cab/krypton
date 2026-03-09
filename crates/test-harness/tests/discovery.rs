use krypton_test_harness::discover_fixtures;
use std::fs;
use std::path::Path;

#[test]
fn discovers_kr_files_non_recursive() {
    let dir = tempfile::tempdir().unwrap();
    let sub = dir.path().join("sub");
    fs::create_dir_all(&sub).unwrap();
    fs::write(dir.path().join("a.kr"), "# expect: ok\n").unwrap();
    fs::write(sub.join("b.kr"), "# expect: ok\n").unwrap();

    // discover_fixtures is non-recursive — only finds files directly in dir
    let paths = discover_fixtures(dir.path());
    assert_eq!(paths.len(), 1);
    assert!(paths[0].ends_with("a.kr"));
}

#[test]
fn returns_sorted_paths() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("z.kr"), "").unwrap();
    fs::write(dir.path().join("a.kr"), "").unwrap();
    fs::write(dir.path().join("m.kr"), "").unwrap();

    let paths = discover_fixtures(dir.path());
    let names: Vec<&str> = paths
        .iter()
        .map(|p| p.file_name().unwrap().to_str().unwrap())
        .collect();
    assert_eq!(names, vec!["a.kr", "m.kr", "z.kr"]);
}

#[test]
fn skips_non_kr_files() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("test.kr"), "").unwrap();
    fs::write(dir.path().join("readme.md"), "").unwrap();
    fs::write(dir.path().join("notes.txt"), "").unwrap();

    let paths = discover_fixtures(dir.path());
    assert_eq!(paths.len(), 1);
    assert!(paths[0].ends_with("test.kr"));
}

#[test]
fn empty_directory_returns_empty() {
    let dir = tempfile::tempdir().unwrap();
    let paths = discover_fixtures(dir.path());
    assert!(paths.is_empty());
}

#[test]
fn nonexistent_directory_returns_empty() {
    let paths = discover_fixtures(Path::new("/nonexistent/path"));
    assert!(paths.is_empty());
}
