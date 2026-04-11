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

fn krypton_bin() -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_krypton"));
    cmd.current_dir(workspace_root());
    cmd
}

fn run_inspect(fixture: &str) -> String {
    let output = krypton_bin()
        .args(["inspect", fixture])
        .output()
        .expect("failed to run krypton");
    assert!(
        output.status.success(),
        "inspect should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("invalid utf8")
}

#[test]
fn inspect_basic() {
    let output = run_inspect("tests/fixtures/inspect/inspect_basic.kr");
    insta::assert_snapshot!(output);
}

#[test]
fn inspect_shadow() {
    let output = run_inspect("tests/fixtures/inspect/inspect_shadow.kr");
    insta::assert_snapshot!(output);
}

#[test]
fn inspect_question_mark() {
    let output = run_inspect("tests/fixtures/inspect/inspect_question_mark.kr");
    insta::assert_snapshot!(output);
}

#[test]
fn inspect_consumed() {
    let output = run_inspect("tests/fixtures/inspect/inspect_consumed.kr");
    insta::assert_snapshot!(output);
}

#[test]
fn inspect_borrow_auto_close() {
    let output = run_inspect("tests/fixtures/inspect/inspect_borrow_auto_close.kr");
    insta::assert_snapshot!(output);
}

#[test]
fn inspect_borrow_then_consume() {
    let output = run_inspect("tests/fixtures/inspect/inspect_borrow_then_consume.kr");
    insta::assert_snapshot!(output);
}

#[test]
fn inspect_borrow_read_write_close_once() {
    let output = run_inspect("tests/fixtures/inspect/inspect_borrow_read_write_close_once.kr");
    insta::assert_snapshot!(output);
}

#[test]
fn inspect_borrow_question_mark() {
    let output = run_inspect("tests/fixtures/inspect/inspect_borrow_question_mark.kr");
    insta::assert_snapshot!(output);
}
