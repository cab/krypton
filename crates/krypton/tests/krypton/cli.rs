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

#[test]
fn test_init_creates_project() {
    let dir = tempdir().expect("failed to create temp dir");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["init", "clementine/my-app"])
        .output()
        .expect("failed to run krypton");
    assert!(
        output.status.success(),
        "init should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let project = dir.path().join("my-app");
    assert!(project.join("krypton.toml").is_file());
    assert!(project.join("src/main.kr").is_file());
    assert!(project.join(".gitignore").is_file());
}

#[test]
fn test_init_generated_project_compiles_and_runs() {
    let dir = tempdir().expect("failed to create temp dir");

    let init = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["init", "clementine/my-app"])
        .output()
        .expect("failed to run krypton init");
    assert!(
        init.status.success(),
        "init should succeed: {}",
        String::from_utf8_lossy(&init.stderr)
    );

    let project = dir.path().join("my-app");
    let compile = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .args(["compile", "src/main.kr"])
        .output()
        .expect("failed to run krypton compile");
    assert!(
        compile.status.success(),
        "compile should succeed: {}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let run = Command::new("java")
        .current_dir(&project)
        .args(["-jar", "main.jar"])
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
        "generated program should print 'hello world', got: {stdout}"
    );
}

#[test]
fn test_init_errors_on_existing_directory() {
    let dir = tempdir().expect("failed to create temp dir");
    std::fs::create_dir(dir.path().join("my-app")).expect("pre-create collision dir");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["init", "clementine/my-app"])
        .output()
        .expect("failed to run krypton");
    assert!(
        !output.status.success(),
        "init should fail when target directory exists"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("my-app") && stderr.to_lowercase().contains("exist"),
        "stderr should mention the collision, got: {stderr}"
    );
}

#[test]
fn test_init_errors_on_invalid_name() {
    let dir = tempdir().expect("failed to create temp dir");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["init", "myapp"])
        .output()
        .expect("failed to run krypton");
    assert!(
        !output.status.success(),
        "init should fail on invalid name"
    );
}
