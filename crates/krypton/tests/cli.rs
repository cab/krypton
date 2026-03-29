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
        .args(["parse", "tests/fixtures/parser/basic_hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(output.status.success(), "exit code should be 0");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("DefFn"),
        "stdout should contain DefFn: {stdout}"
    );
}

#[test]
fn test_parse_surface_format() {
    let output = krypton_bin()
        .args([
            "parse",
            "--format",
            "surface",
            "tests/fixtures/parser/basic_hello.kr",
        ])
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
        .args(["parse", "tests/fixtures/parser/bad.kr"])
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
        .args(["check", "tests/fixtures/inference/identity.kr"])
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
        .args(["check", "tests/fixtures/inference/type_error_check.kr"])
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
        .args(["check", "tests/fixtures/inference/multi_def.kr"])
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
        .args(["fmt", "tests/fixtures/parser/basic_hello.kr"])
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
fn test_compile_produces_jar() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/functions/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["compile", "hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(
        output.status.success(),
        "compile should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        dir.path().join("hello.jar").exists(),
        "hello.jar should be created"
    );
}

#[test]
fn test_compile_jar_runs_with_java() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/functions/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let compile = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["compile", "hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(
        compile.status.success(),
        "compile should succeed: {}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new("java")
        .current_dir(dir.path())
        .args(["-jar", "hello.jar"])
        .output()
        .expect("failed to run java");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "java -jar should succeed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(
        stdout.contains("hello world"),
        "stdout should contain 'hello world': {stdout}"
    );
}

#[test]
fn test_compile_custom_output() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/functions/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["compile", "hello.kr", "-o", "build/out.jar"])
        .output()
        .expect("failed to run krypton");
    assert!(
        output.status.success(),
        "compile should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        dir.path().join("build/out.jar").exists(),
        "build/out.jar should be created"
    );
}

#[test]
fn test_run_hello_world() {
    let output = krypton_bin()
        .args(["run", "tests/fixtures/functions/hello.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(
        output.status.success(),
        "exit code should be 0: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "stdout should contain 'hello world': {stdout}"
    );
}

#[test]
fn test_run_factorial() {
    let output = krypton_bin()
        .args(["run", "tests/fixtures/functions/factorial.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(
        output.status.success(),
        "exit code should be 0: {}",
        String::from_utf8_lossy(&output.stderr)
    );
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
        .args(["run", "tests/fixtures/inference/type_error_check.kr"])
        .output()
        .expect("failed to run krypton");
    assert!(!output.status.success(), "exit code should be non-zero");
}

#[test]
fn test_compile_target_js_produces_mjs() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/functions/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let out_dir = dir.path().join("out");
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args([
            "compile",
            "hello.kr",
            "--target",
            "js",
            "-o",
            out_dir.to_str().unwrap(),
        ])
        .output()
        .expect("failed to run krypton");
    assert!(
        output.status.success(),
        "compile --target js should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        out_dir.join("hello.mjs").exists(),
        "hello.mjs should be created in output directory"
    );

    let content = std::fs::read_to_string(out_dir.join("hello.mjs")).unwrap();
    assert!(
        content.contains("export function main("),
        "generated .mjs should contain main function export: {content}"
    );
}
