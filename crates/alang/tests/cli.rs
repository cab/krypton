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

fn alang_bin() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_alang"));
    cmd.current_dir(workspace_root());
    cmd
}

#[test]
fn test_parse_prints_ast() {
    let output = alang_bin()
        .args(["parse", "tests/fixtures/m1/hello.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("DefFn"), "stdout should contain DefFn: {stdout}");
}

#[test]
fn test_parse_sexp_format() {
    let output = alang_bin()
        .args(["parse", "--format", "sexp", "tests/fixtures/m1/hello.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("(def main"),
        "stdout should contain (def main: {stdout}"
    );
}

#[test]
fn test_parse_errors_exit_1() {
    let output = alang_bin()
        .args(["parse", "tests/fixtures/m1/bad.al"])
        .output()
        .expect("failed to run alang");
    assert!(!output.status.success(), "exit code should be non-zero");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("P0002"),
        "stderr should contain P0002 error code: {stderr}"
    );
}

#[test]
fn test_check_identity() {
    let output = alang_bin()
        .args(["check", "tests/fixtures/m2/identity.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("identity : forall"),
        "stdout should contain polymorphic inferred type: {stdout}"
    );
}

#[test]
fn test_check_type_error() {
    let output = alang_bin()
        .args(["check", "tests/fixtures/m2/type_error_check.al"])
        .output()
        .expect("failed to run alang");
    assert!(!output.status.success(), "exit code should be non-zero");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("E0001"),
        "stderr should contain E0001 error code: {stderr}"
    );
}

#[test]
fn test_check_prints_multiple_defs() {
    let output = alang_bin()
        .args(["check", "tests/fixtures/m2/multi_def.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("id :") && stdout.contains("always :"),
        "stdout should contain types for both defs: {stdout}"
    );
}

#[test]
fn test_fmt_pretty_prints() {
    let output = alang_bin()
        .args(["fmt", "tests/fixtures/m1/hello.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("(def main"),
        "stdout should contain (def main: {stdout}"
    );
}

#[test]
fn test_compile_produces_class_file() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/m4/hello.al");
    std::fs::copy(&fixture, dir.path().join("hello.al")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_alang"))
        .current_dir(dir.path())
        .args(["compile", "hello.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "compile should succeed: {}", String::from_utf8_lossy(&output.stderr));
    assert!(dir.path().join("Hello.class").exists(), "Hello.class should be created");
}

#[test]
fn test_run_hello_world() {
    let output = alang_bin()
        .args(["run", "tests/fixtures/m4/hello.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "exit code should be 0: {}", String::from_utf8_lossy(&output.stderr));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "stdout should contain 'hello world': {stdout}"
    );
}

#[test]
fn test_run_factorial() {
    let output = alang_bin()
        .args(["run", "tests/fixtures/m4/factorial.al"])
        .output()
        .expect("failed to run alang");
    assert!(output.status.success(), "exit code should be 0: {}", String::from_utf8_lossy(&output.stderr));
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("3628800"),
        "stdout should contain '3628800': {stdout}"
    );
}

#[test]
fn test_run_parse_error_exits_1() {
    let output = alang_bin()
        .args(["run", "tests/fixtures/m1/bad.al"])
        .output()
        .expect("failed to run alang");
    assert!(!output.status.success(), "exit code should be non-zero");
}

#[test]
fn test_run_type_error_exits_1() {
    let output = alang_bin()
        .args(["run", "tests/fixtures/m2/type_error_check.al"])
        .output()
        .expect("failed to run alang");
    assert!(!output.status.success(), "exit code should be non-zero");
}
