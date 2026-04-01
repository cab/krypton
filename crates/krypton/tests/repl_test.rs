use std::io::Write;
use std::process::{Command, Stdio};

fn krypton_bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_krypton"))
}

fn run_repl_with_input(input: &str) -> (String, String, bool) {
    let mut child = krypton_bin()
        .arg("repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start krypton repl");

    if let Some(ref mut stdin) = child.stdin {
        stdin.write_all(input.as_bytes()).ok();
    }
    // Close stdin so the REPL gets EOF
    drop(child.stdin.take());

    let output = child.wait_with_output().expect("failed to wait on child");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr, output.status.success())
}

#[test]
fn test_banner_on_startup() {
    let (stdout, _, success) = run_repl_with_input("");
    assert!(success, "REPL should exit cleanly on EOF");
    assert!(
        stdout.contains("Krypton v0.1"),
        "Banner should contain version: {stdout}"
    );
    assert!(
        stdout.contains(":help"),
        "Banner should mention :help: {stdout}"
    );
}

#[test]
fn test_single_line_echo() {
    let (stdout, _, success) = run_repl_with_input("1 + 2\n");
    assert!(success);
    assert!(
        stdout.contains("1 + 2"),
        "Should echo back the input: {stdout}"
    );
}

#[test]
fn test_multiline_continuation() {
    let input = "let f = fun(x) {\nx + 1\n}\n";
    let (stdout, _, success) = run_repl_with_input(input);
    assert!(success);
    assert!(
        stdout.contains("let f = fun(x) {\nx + 1\n}"),
        "Should echo back the complete multi-line input: {stdout}"
    );
}

#[test]
fn test_quit_exits_cleanly() {
    let (_, _, success) = run_repl_with_input(":quit\n");
    assert!(success, "REPL should exit cleanly on :quit");
}

#[test]
fn test_help_output() {
    let (stdout, _, success) = run_repl_with_input(":help\n");
    assert!(success);
    assert!(
        stdout.contains(":quit"),
        "Help should list :quit: {stdout}"
    );
    assert!(
        stdout.contains(":help"),
        "Help should list :help: {stdout}"
    );
    assert!(
        stdout.contains(":reset"),
        "Help should list :reset: {stdout}"
    );
}

#[test]
fn test_eof_exits_cleanly() {
    // Empty input → immediate EOF
    let (_, _, success) = run_repl_with_input("");
    assert!(success, "REPL should exit cleanly on EOF");
}

#[test]
fn test_history_file_created() {
    // Use a temp dir as HOME so we don't pollute the real home
    let tmp = tempfile::tempdir().expect("failed to create temp dir");
    let mut child = krypton_bin()
        .arg("repl")
        .env("HOME", tmp.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start krypton repl");

    if let Some(ref mut stdin) = child.stdin {
        stdin.write_all(b"1 + 2\n:quit\n").ok();
    }
    drop(child.stdin.take());

    let output = child.wait_with_output().expect("failed to wait on child");
    assert!(output.status.success());

    let history = tmp.path().join(".krypton/repl_history");
    assert!(
        history.exists(),
        "History file should be created at {:?}",
        history
    );
}
