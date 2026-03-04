use alang_test_harness::discover_fixtures;
use std::fs;
use std::path::Path;

#[test]
fn discovers_al_files_in_subdirectories() {
    let dir = tempfile::tempdir().unwrap();
    let sub = dir.path().join("sub");
    fs::create_dir_all(&sub).unwrap();
    fs::write(dir.path().join("a.al"), "# expect: ok\n").unwrap();
    fs::write(sub.join("b.al"), "# expect: ok\n").unwrap();

    let paths = discover_fixtures(dir.path());
    assert_eq!(paths.len(), 2);
    assert!(paths[0].ends_with("a.al"));
    assert!(paths[1].ends_with("b.al"));
}

#[test]
fn returns_sorted_paths() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("z.al"), "").unwrap();
    fs::write(dir.path().join("a.al"), "").unwrap();
    fs::write(dir.path().join("m.al"), "").unwrap();

    let paths = discover_fixtures(dir.path());
    let names: Vec<&str> = paths
        .iter()
        .map(|p| p.file_name().unwrap().to_str().unwrap())
        .collect();
    assert_eq!(names, vec!["a.al", "m.al", "z.al"]);
}

#[test]
fn skips_non_al_files() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("test.al"), "").unwrap();
    fs::write(dir.path().join("readme.md"), "").unwrap();
    fs::write(dir.path().join("notes.txt"), "").unwrap();

    let paths = discover_fixtures(dir.path());
    assert_eq!(paths.len(), 1);
    assert!(paths[0].ends_with("test.al"));
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
