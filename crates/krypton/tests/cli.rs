use std::path::PathBuf;
use std::process::Command;
use tempfile::tempdir;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn krypton_bin() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_krypton"));
    cmd.current_dir(workspace_root());
    cmd
}

#[test]
fn test_parse_prints_ast() {
    let output = krypton_bin()
        .args(["parse", "tests/fixtures/m1/hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("DefFn"), "stdout should contain DefFn: {stdout}");
}

#[test]
fn test_parse_surface_format() {
    let output = krypton_bin()
        .args(["parse", "--format", "surface", "tests/fixtures/m1/hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("fun main"),
        "stdout should contain fun main: {stdout}"
    );
}

#[test]
fn test_parse_errors_exit_1() {
    let output = krypton_bin()
        .args(["parse", "tests/fixtures/m1/bad.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(!output.status.success(), "exit code should be non-zero");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("P0001") || stderr.contains("P0002"),
        "stderr should contain parser error code: {stderr}"
    );
}

#[test]
fn test_check_identity() {
    let output = krypton_bin()
        .args(["check", "tests/fixtures/m2/identity.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("identity : forall"),
        "stdout should contain polymorphic inferred type: {stdout}"
    );
}

#[test]
fn test_check_type_error() {
    let output = krypton_bin()
        .args(["check", "tests/fixtures/m2/type_error_check.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(!output.status.success(), "exit code should be non-zero");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("E0001"),
        "stderr should contain E0001 error code: {stderr}"
    );
}

#[test]
fn test_check_prints_multiple_defs() {
    let output = krypton_bin()
        .args(["check", "tests/fixtures/m2/multi_def.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("id :") && stdout.contains("always :"),
        "stdout should contain types for both defs: {stdout}"
    );
}

#[test]
fn test_fmt_pretty_prints() {
    let output = krypton_bin()
        .args(["fmt", "tests/fixtures/m1/hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("fun main"),
        "stdout should contain fun main: {stdout}"
    );
}

#[test]
fn test_compile_produces_class_file() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/m4/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["compile", "hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "compile should succeed: {}", String::from_utf8_lossy(&output.stderr));
    assert!(dir.path().join("Hello.class").exists(), "Hello.class should be created");
}

#[test]
fn test_run_hello_world() {
    let output = krypton_bin()
        .args(["run", "tests/fixtures/m4/hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0: {}", String::from_utf8_lossy(&output.stderr));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "stdout should contain 'hello world': {stdout}"
    );
}

#[test]
fn test_run_factorial() {
    let output = krypton_bin()
        .args(["run", "tests/fixtures/m4/factorial.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0: {}", String::from_utf8_lossy(&output.stderr));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("3628800"),
        "stdout should contain '3628800': {stdout}"
    );
}

#[test]
fn test_run_parse_error_exits_1() {
    let dir = tempdir().expect("failed to create temp dir");
    let bad_file = dir.path().join("bad.kr");
    std::fs::write(&bad_file, "fun main(\n").expect("write bad file");
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .args(["run", bad_file.to_str().unwrap()])
        .output()
        .expect("failed to run krypton");
    assert!(!output.status.success(), "exit code should be non-zero");
}

#[test]
fn test_run_type_error_exits_1() {
    let output = krypton_bin()
        .args(["run", "tests/fixtures/m2/type_error_check.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(!output.status.success(), "exit code should be non-zero");
}
