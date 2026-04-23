#![allow(dead_code)]

use std::path::Path;
use std::process::Command;

use tempfile::{TempDir, tempdir};

pub fn run_in(dir: &Path, args: &[&str]) -> std::process::Output {
    let output = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("failed to run git {args:?} in {}: {e}", dir.display()));
    assert!(
        output.status.success(),
        "git {args:?} in {} failed: stderr={}",
        dir.display(),
        String::from_utf8_lossy(&output.stderr),
    );
    output
}

/// Initialize a git repo at `dir`, write the given files, commit them, and
/// return the resulting commit SHA. The repo is configured with a fixed
/// identity and a deterministic default branch (`main`) so tests don't
/// depend on the host's git config.
pub fn make_repo(dir: &Path, files: &[(&str, &str)]) -> String {
    Command::new("git")
        .args(["-c", "init.defaultBranch=main", "init", "--quiet"])
        .arg(dir)
        .output()
        .expect("git init");
    run_in(dir, &["config", "user.email", "test@example.invalid"]);
    run_in(dir, &["config", "user.name", "Test User"]);
    run_in(dir, &["config", "commit.gpgsign", "false"]);
    write_files(dir, files);
    run_in(dir, &["add", "--all"]);
    run_in(dir, &["commit", "-m", "initial", "--quiet"]);
    current_sha(dir)
}

pub fn write_files(dir: &Path, files: &[(&str, &str)]) {
    for (rel, contents) in files {
        let path = dir.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("mkdir parent");
        }
        std::fs::write(&path, contents).expect("write file");
    }
}

pub fn add_commit(dir: &Path, message: &str, files: &[(&str, &str)]) -> String {
    write_files(dir, files);
    run_in(dir, &["add", "--all"]);
    run_in(dir, &["commit", "-m", message, "--quiet"]);
    current_sha(dir)
}

pub fn add_tag(dir: &Path, tag: &str) {
    run_in(dir, &["tag", tag]);
}

pub fn current_sha(dir: &Path) -> String {
    let out = run_in(dir, &["rev-parse", "HEAD"]);
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

pub fn make_cache_root() -> TempDir {
    tempdir().expect("cache tempdir")
}

pub fn manifest(name: &str, version: &str) -> String {
    format!("[package]\nname = \"{name}\"\nversion = \"{version}\"\n")
}
