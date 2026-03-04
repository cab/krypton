use std::path::PathBuf;
use std::process::Command;

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
