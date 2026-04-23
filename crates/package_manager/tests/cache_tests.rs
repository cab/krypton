use std::path::PathBuf;

use krypton_package_manager::CacheDir;
use tempfile::tempdir;

#[test]
fn root_equals_explicit_path() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());
    assert_eq!(cache.root(), tmp.path());
}

#[test]
fn package_source_dir_layout() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());

    let expected: PathBuf = tmp
        .path()
        .join("cache")
        .join("packages")
        .join("clementine")
        .join("http")
        .join("0.3.0");
    assert_eq!(
        cache.package_source_dir("clementine", "http", "0.3.0"),
        expected
    );
}

#[test]
fn package_compiled_dir_layout() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());

    let expected: PathBuf = tmp
        .path()
        .join("cache")
        .join("packages")
        .join("clementine")
        .join("http")
        .join("0.3.0")
        .join("target")
        .join("jvm")
        .join("abc123");
    assert_eq!(
        cache.package_compiled_dir("clementine", "http", "0.3.0", "abc123"),
        expected
    );
}

#[test]
fn git_clone_dir_layout() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());

    let expected: PathBuf = tmp
        .path()
        .join("cache")
        .join("git")
        .join("clementine")
        .join("http");
    assert_eq!(cache.git_clone_dir("clementine", "http"), expected);
}

#[test]
fn maven_jar_path_layout() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());

    let expected: PathBuf = tmp
        .path()
        .join("cache")
        .join("maven")
        .join("org")
        .join("postgresql")
        .join("postgresql")
        .join("42.7.1")
        .join("postgresql-42.7.1.jar");
    assert_eq!(
        cache.maven_jar_path(
            "org.postgresql",
            "postgresql",
            "42.7.1",
            "postgresql-42.7.1.jar"
        ),
        expected
    );
}

#[test]
fn maven_jar_path_nested_group() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());

    let expected: PathBuf = tmp
        .path()
        .join("cache")
        .join("maven")
        .join("com")
        .join("google")
        .join("guava")
        .join("guava")
        .join("33.0.0-jre")
        .join("guava-33.0.0-jre.jar");
    assert_eq!(
        cache.maven_jar_path(
            "com.google.guava",
            "guava",
            "33.0.0-jre",
            "guava-33.0.0-jre.jar",
        ),
        expected
    );
}

#[test]
fn tools_dir_not_under_cache() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());

    let tools = cache.tools_dir();
    assert_eq!(tools, tmp.path().join("tools"));
    assert!(
        !tools.starts_with(tmp.path().join("cache")),
        "tools_dir() must not be a descendant of cache/, got {}",
        tools.display()
    );
}

#[test]
fn path_methods_do_not_create_directories() {
    let tmp = tempdir().expect("tempdir");
    let cache = CacheDir::with_root(tmp.path().to_path_buf());

    let _ = cache.root();
    let _ = cache.package_source_dir("clementine", "http", "0.3.0");
    let _ = cache.package_compiled_dir("clementine", "http", "0.3.0", "abc123");
    let _ = cache.maven_jar_path(
        "org.postgresql",
        "postgresql",
        "42.7.1",
        "postgresql-42.7.1.jar",
    );
    let _ = cache.tools_dir();

    assert!(
        !tmp.path().join("cache").exists(),
        "path methods must not create <root>/cache"
    );
    assert!(
        !tmp.path().join("tools").exists(),
        "path methods must not create <root>/tools"
    );
}

/// Environment-touching integration test — the sole test in this suite that
/// mutates process env. Race scope: only racy with other tests that read
/// `KRYPTON_HOME` or `HOME`, and no other test in this workspace does.
#[test]
fn new_with_krypton_home_env() {
    let tmp = tempdir().expect("tempdir");
    let root = tmp.path().to_path_buf();

    // SAFETY: single-threaded access to the env var; no other test in this
    // workspace reads KRYPTON_HOME (verified by grep at plan time).
    unsafe {
        std::env::set_var("KRYPTON_HOME", &root);
    }
    let cache = CacheDir::new().expect("new() with KRYPTON_HOME set");
    assert_eq!(cache.root(), root.as_path());
    unsafe {
        std::env::remove_var("KRYPTON_HOME");
    }
}
