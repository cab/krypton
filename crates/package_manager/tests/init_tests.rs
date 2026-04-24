use std::fs;

use krypton_package_manager::{init_project, InitError, Manifest};
use semver::Version;
use tempfile::tempdir;

#[test]
fn creates_expected_files_and_directories() {
    let tmp = tempdir().expect("tempdir");
    let dir = init_project(tmp.path(), "clementine/my-app").expect("init succeeds");

    assert_eq!(dir, tmp.path().join("my-app"));
    assert!(dir.is_dir(), "project dir should exist");
    assert!(dir.join("src").is_dir(), "src/ should exist");
    assert!(
        dir.join("krypton.toml").is_file(),
        "krypton.toml should exist"
    );
    assert!(
        dir.join("src/main.kr").is_file(),
        "src/main.kr should exist"
    );
    assert!(dir.join(".gitignore").is_file(), ".gitignore should exist");
}

#[test]
fn generated_manifest_roundtrips() {
    let tmp = tempdir().expect("tempdir");
    let dir = init_project(tmp.path(), "clementine/my-app").expect("init succeeds");

    let manifest_src = fs::read_to_string(dir.join("krypton.toml")).expect("read manifest");
    let manifest = Manifest::from_str(&manifest_src).expect("manifest should round-trip");

    assert_eq!(manifest.package.name, "clementine/my-app");
    assert_eq!(manifest.package.version, Version::parse("0.1.0").unwrap());
    assert!(
        manifest.dependencies.is_empty(),
        "dependencies should be empty"
    );
    assert!(
        manifest.dev_dependencies.is_empty(),
        "dev-dependencies should be empty"
    );
    assert!(manifest.jvm.is_none(), "no [jvm] section expected");
}

#[test]
fn generated_manifest_contains_empty_dependencies_section() {
    let tmp = tempdir().expect("tempdir");
    let dir = init_project(tmp.path(), "clementine/my-app").expect("init succeeds");

    let manifest_src = fs::read_to_string(dir.join("krypton.toml")).expect("read manifest");
    assert!(
        manifest_src.contains("[dependencies]"),
        "manifest should include a visible empty [dependencies] section, got:\n{manifest_src}"
    );
}

#[test]
fn gitignore_contains_target() {
    let tmp = tempdir().expect("tempdir");
    let dir = init_project(tmp.path(), "clementine/my-app").expect("init succeeds");

    let gitignore = fs::read_to_string(dir.join(".gitignore")).expect("read .gitignore");
    assert!(
        gitignore.lines().any(|line| line.trim() == "target/"),
        ".gitignore should contain 'target/' on its own line, got:\n{gitignore}"
    );
}

#[test]
fn directory_name_is_name_part() {
    let tmp = tempdir().expect("tempdir");
    init_project(tmp.path(), "clementine/my-app").expect("init succeeds");

    assert!(
        tmp.path().join("my-app").is_dir(),
        "tempdir should contain my-app/"
    );
    assert!(
        !tmp.path().join("clementine").exists(),
        "tempdir should not contain an owner-named directory"
    );
}

#[test]
fn errors_when_target_dir_exists() {
    let tmp = tempdir().expect("tempdir");
    fs::create_dir(tmp.path().join("my-app")).expect("pre-create collision dir");

    let err = init_project(tmp.path(), "clementine/my-app").expect_err("should fail");
    match err {
        InitError::DirectoryExists(p) => assert_eq!(p, tmp.path().join("my-app")),
        other => panic!("expected DirectoryExists, got {other:?}"),
    }
}

#[test]
fn errors_on_invalid_name_no_slash() {
    let tmp = tempdir().expect("tempdir");
    let err = init_project(tmp.path(), "myapp").expect_err("should fail");
    assert!(
        matches!(err, InitError::InvalidName(_)),
        "expected InvalidName, got {err:?}"
    );
}

#[test]
fn errors_on_invalid_name_empty_owner() {
    let tmp = tempdir().expect("tempdir");
    let err = init_project(tmp.path(), "/my-app").expect_err("should fail");
    assert!(
        matches!(err, InitError::InvalidName(_)),
        "expected InvalidName, got {err:?}"
    );
}

#[test]
fn errors_on_invalid_name_uppercase() {
    let tmp = tempdir().expect("tempdir");
    let err = init_project(tmp.path(), "Clementine/my-app").expect_err("should fail");
    assert!(
        matches!(err, InitError::InvalidName(_)),
        "expected InvalidName, got {err:?}"
    );
}

#[test]
fn main_kr_contains_runnable_program() {
    let tmp = tempdir().expect("tempdir");
    let dir = init_project(tmp.path(), "clementine/my-app").expect("init succeeds");

    let main_src = fs::read_to_string(dir.join("src/main.kr")).expect("read main.kr");
    assert!(
        main_src.contains("fun main()"),
        "main.kr should define fun main(), got:\n{main_src}"
    );
    assert!(
        main_src.contains("println"),
        "main.kr should call println, got:\n{main_src}"
    );
}
