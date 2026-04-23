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
fn test_lock_writes_lockfile() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = dir.path().join("proj");
    let dep = dir.path().join("mylib");
    std::fs::create_dir_all(&project).unwrap();
    std::fs::create_dir_all(&dep).unwrap();
    std::fs::write(
        dep.join("krypton.toml"),
        "[package]\nname = \"clementine/mylib\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(
        project.join("krypton.toml"),
        format!(
            "[package]\nname = \"clementine/demo\"\nversion = \"0.1.0\"\n\n\
             [dependencies]\nmylib = {{ package = \"clementine/mylib\", path = \"{}\" }}\n",
            dep.display()
        ),
    )
    .unwrap();

    // Isolate the cache dir so the test never touches the developer's real
    // ~/.krypton. `CacheDir::new()` prefers `KRYPTON_HOME` when set.
    let cache_root = dir.path().join("krypton-home");
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", &cache_root)
        .arg("lock")
        .output()
        .expect("failed to run krypton lock");
    assert!(
        output.status.success(),
        "lock should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let lock_path = project.join("krypton.lock");
    assert!(lock_path.is_file(), "krypton.lock should be created");
    let body = std::fs::read_to_string(&lock_path).unwrap();
    assert!(
        body.starts_with("# This file is generated. Do not edit manually."),
        "lockfile must begin with the header comment, got:\n{body}"
    );
    assert!(
        body.contains("clementine/mylib"),
        "lockfile must reference the dep: {body}"
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

/// Run `krypton init` inside `parent_dir`, returning the created project path
/// and a cache root (to be threaded via `KRYPTON_HOME` so tests never touch
/// the developer's real `~/.krypton`).
fn init_project_for_test(parent_dir: &std::path::Path) -> PathBuf {
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(parent_dir)
        .args(["init", "clementine/my-app"])
        .output()
        .expect("failed to run krypton init");
    assert!(
        output.status.success(),
        "init should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    parent_dir.join("my-app")
}

#[test]
fn test_build_no_manifest_errors() {
    let dir = tempdir().expect("failed to create temp dir");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        !output.status.success(),
        "build should fail without krypton.toml"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("krypton.toml"),
        "stderr should mention krypton.toml, got: {stderr}"
    );
}

#[test]
fn test_build_executable_produces_jar() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        output.status.success(),
        "build should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let jar_path = project.join("target/jvm/my-app.jar");
    assert!(
        jar_path.is_file(),
        "expected target/jvm/my-app.jar to exist at {}",
        jar_path.display()
    );

    let run = Command::new("java")
        .current_dir(&project)
        .args(["-jar", jar_path.to_str().unwrap()])
        .output()
        .expect("failed to run java");
    assert!(
        run.status.success(),
        "java -jar should succeed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("hello world"),
        "expected 'hello world' in stdout, got: {stdout}"
    );
}

#[test]
fn test_build_library_omits_main_class() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // Replace src/main.kr with src/lib.kr — a trivial library module.
    std::fs::remove_file(project.join("src/main.kr")).expect("remove main.kr");
    std::fs::write(
        project.join("src/lib.kr"),
        "fun greet() = \"hello from lib\"\n",
    )
    .expect("write lib.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        output.status.success(),
        "library build should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let jar_path = project.join("target/jvm/my-app.jar");
    assert!(jar_path.is_file(), "jar should exist at {}", jar_path.display());

    // Read the JAR manifest and assert Main-Class is absent.
    let jar_bytes = std::fs::read(&jar_path).expect("read jar");
    let reader = std::io::Cursor::new(jar_bytes);
    let mut archive = zip::ZipArchive::new(reader).expect("valid zip");
    let mut manifest = archive
        .by_name("META-INF/MANIFEST.MF")
        .expect("manifest entry");
    let mut contents = String::new();
    use std::io::Read;
    manifest.read_to_string(&mut contents).expect("read manifest");
    assert!(
        !contents.contains("Main-Class:"),
        "library JAR manifest must not declare Main-Class, got:\n{contents}"
    );
}

#[test]
fn test_build_missing_both_entries_errors() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::remove_file(project.join("src/main.kr")).expect("remove main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        !output.status.success(),
        "build should fail with no entry module"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("src/main.kr") && stderr.contains("src/lib.kr"),
        "stderr should mention both entry paths, got: {stderr}"
    );
}

#[test]
fn test_build_target_js_produces_mjs() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["build", "--target", "js"])
        .output()
        .expect("failed to run krypton build");
    assert!(
        output.status.success(),
        "js build should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mjs_path = project.join("target/js/my-app.mjs");
    assert!(
        mjs_path.is_file(),
        "expected target/js/my-app.mjs at {}",
        mjs_path.display()
    );
    let content = std::fs::read_to_string(&mjs_path).expect("read mjs");
    assert!(
        content.contains("export function main"),
        "generated .mjs should contain main function export: {content}"
    );
}

#[test]
fn test_build_project_detection_walks_up() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // Run `krypton build` from inside `src/`, a sub-directory of the project.
    let src_dir = project.join("src");
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&src_dir)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        output.status.success(),
        "build from subdirectory should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let jar_path = project.join("target/jvm/my-app.jar");
    assert!(
        jar_path.is_file(),
        "JAR should be written to the project's target/, not the cwd; expected {}",
        jar_path.display()
    );
}

#[test]
fn test_build_dep_compile_error_attributes_to_dep() {
    let dir = tempdir().expect("failed to create temp dir");
    let lib = dir.path().join("mylib");
    let app = dir.path().join("app");
    std::fs::create_dir_all(lib.join("src")).unwrap();
    std::fs::create_dir_all(app.join("src")).unwrap();

    // Library manifest + a broken module that should fail typechecking.
    // `x : Int = "not an int"` triggers a type error inside the dep.
    std::fs::write(
        lib.join("krypton.toml"),
        "[package]\nname = \"clementine/mylib\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(
        lib.join("src/lib.kr"),
        "fun broken() : Int = \"not an int\"\n",
    )
    .unwrap();

    // App manifest with a path dependency on the broken lib, and a main
    // module that imports from it.
    std::fs::write(
        app.join("krypton.toml"),
        format!(
            "[package]\nname = \"clementine/app\"\nversion = \"0.1.0\"\n\n\
             [dependencies]\nmylib = {{ package = \"clementine/mylib\", path = \"{}\" }}\n",
            lib.display()
        ),
    )
    .unwrap();
    std::fs::write(
        app.join("src/main.kr"),
        "import mylib.{broken}\n\nfun main() = println(broken().toString())\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&app)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        !output.status.success(),
        "build should fail when dep has a type error"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("mylib"),
        "diagnostics should attribute the error to the dep via its import root 'mylib', got: {stderr}"
    );
}

#[test]
fn test_build_timings_prints_resolution_phase() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["--timings", "build"])
        .output()
        .expect("failed to run krypton build");
    assert!(
        output.status.success(),
        "build should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("resolve:"),
        "--timings should include resolve phase, got: {stderr}"
    );
    assert!(
        stderr.contains("typecheck:"),
        "--timings should include typecheck phase, got: {stderr}"
    );
}
