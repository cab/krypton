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
fn timings_flag_prints_phase_durations_for_compile() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/m4/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["--timings", "compile", "hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "compile should succeed: {}", String::from_utf8_lossy(&output.stderr));
    let stderr = String::from_utf8_lossy(&output.stderr);
    for phase in &["parse:", "typecheck:", "codegen:", "emit:", "total:"] {
        assert!(stderr.contains(phase), "stderr should contain '{}': {}", phase, stderr);
    }
}

#[test]
fn timings_flag_with_run_includes_jvm() {
    let output = krypton_bin()
        .args(["--timings", "run", "tests/fixtures/m4/hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "run should succeed: {}", String::from_utf8_lossy(&output.stderr));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("jvm:"), "stderr should contain 'jvm:': {}", stderr);
}

#[test]
fn no_timings_flag_prints_nothing_extra() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/m4/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["compile", "hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "compile should succeed: {}", String::from_utf8_lossy(&output.stderr));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("parse:"), "stderr should NOT contain 'parse:': {}", stderr);
    assert!(!stderr.contains("total:"), "stderr should NOT contain 'total:': {}", stderr);
}

#[test]
fn timings_with_check_subcommand() {
    let output = krypton_bin()
        .args(["--timings", "check", "tests/fixtures/m4/arithmetic.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "check should succeed: {}", String::from_utf8_lossy(&output.stderr));
    let stderr = String::from_utf8_lossy(&output.stderr);
    for phase in &["parse:", "typecheck:", "total:"] {
        assert!(stderr.contains(phase), "stderr should contain '{}': {}", phase, stderr);
    }
    assert!(!stderr.contains("codegen:"), "stderr should NOT contain 'codegen:': {}", stderr);
    assert!(!stderr.contains("emit:"), "stderr should NOT contain 'emit:': {}", stderr);
}
