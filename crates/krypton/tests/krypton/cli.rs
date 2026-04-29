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
    assert!(!output.status.success(), "init should fail on invalid name");
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
    assert!(
        jar_path.is_file(),
        "jar should exist at {}",
        jar_path.display()
    );

    // Read the JAR manifest and assert Main-Class is absent.
    let jar_bytes = std::fs::read(&jar_path).expect("read jar");
    let reader = std::io::Cursor::new(jar_bytes);
    let mut archive = zip::ZipArchive::new(reader).expect("valid zip");
    let mut manifest = archive
        .by_name("META-INF/MANIFEST.MF")
        .expect("manifest entry");
    let mut contents = String::new();
    use std::io::Read;
    manifest
        .read_to_string(&mut contents)
        .expect("read manifest");
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

#[test]
fn test_run_project_executable_prints_hello_world() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    assert!(
        output.status.success(),
        "run should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "expected 'hello world' in stdout, got: {stdout}"
    );
}

#[test]
fn test_run_project_target_js() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["run", "--target", "js"])
        .output()
        .expect("failed to run krypton run --target js");
    assert!(
        output.status.success(),
        "run --target js should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "expected 'hello world' in stdout, got: {stdout}"
    );
}

#[test]
fn test_run_project_library_only_errors() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::remove_file(project.join("src/main.kr")).expect("remove main.kr");
    std::fs::write(
        project.join("src/lib.kr"),
        "fun greet() = \"hello from lib\"\n",
    )
    .expect("write lib.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    assert!(
        !output.status.success(),
        "run on library-only package should fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("no entry point: src/main.kr not found"),
        "stderr should mention missing src/main.kr entry, got: {stderr}"
    );
}

/// Write a minimal but valid JAR (zip with only a MANIFEST.MF entry) to `path`.
fn write_empty_jar(path: &std::path::Path) {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).expect("create parent");
    }
    let file = std::fs::File::create(path).expect("create jar");
    let mut writer = zip::ZipWriter::new(file);
    let opts: zip::write::SimpleFileOptions =
        zip::write::SimpleFileOptions::default().compression_method(zip::CompressionMethod::Stored);
    writer
        .start_file("META-INF/MANIFEST.MF", opts)
        .expect("start manifest");
    use std::io::Write;
    writer
        .write_all(b"Manifest-Version: 1.0\r\n\r\n")
        .expect("write manifest");
    writer.finish().expect("finish jar");
}

#[test]
fn test_run_project_manifest_classpath_included() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let extra_jar = project.join("libs/extra.jar");
    write_empty_jar(&extra_jar);

    let toml_path = project.join("krypton.toml");
    let mut toml = std::fs::read_to_string(&toml_path).expect("read manifest");
    toml.push_str("\n[jvm]\nclasspath = [\"libs/extra.jar\"]\n");
    std::fs::write(&toml_path, toml).expect("write manifest");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    assert!(
        output.status.success(),
        "run with extra classpath jar should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "expected 'hello world' in stdout, got: {stdout}"
    );
}

#[test]
fn test_run_project_missing_classpath_entry_errors() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let toml_path = project.join("krypton.toml");
    let mut toml = std::fs::read_to_string(&toml_path).expect("read manifest");
    toml.push_str("\n[jvm]\nclasspath = [\"libs/does-not-exist.jar\"]\n");
    std::fs::write(&toml_path, toml).expect("write manifest");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    assert!(
        !output.status.success(),
        "run should fail when a manifest classpath entry is missing"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("libs/does-not-exist.jar"),
        "stderr should mention the missing classpath entry, got: {stderr}"
    );
}

#[test]
fn test_check_project_success_no_codegen() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("check")
        .output()
        .expect("failed to run krypton check");
    assert!(
        output.status.success(),
        "check should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !project.join("target").exists(),
        "check must not run codegen; target/ should not exist"
    );
}

#[test]
fn test_check_project_type_error_exits_1() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/main.kr"),
        "fun main() = println((1 + \"hi\").toString())\n",
    )
    .expect("write main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("check")
        .output()
        .expect("failed to run krypton check");
    assert_eq!(
        output.status.code(),
        Some(1),
        "check should exit 1 on type error, got status: {:?}",
        output.status
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !stderr.is_empty(),
        "stderr should contain a type-error diagnostic"
    );
}

#[test]
fn test_check_project_library_allowed() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::remove_file(project.join("src/main.kr")).expect("remove main.kr");
    std::fs::write(
        project.join("src/lib.kr"),
        "fun greet() = \"hello from lib\"\n",
    )
    .expect("write lib.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("check")
        .output()
        .expect("failed to run krypton check");
    assert!(
        output.status.success(),
        "check on library should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_run_file_still_works() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/functions/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["run", "hello.kr"])
        .output()
        .expect("failed to run krypton run");
    assert!(
        output.status.success(),
        "run of file should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "expected 'hello world' in stdout, got: {stdout}"
    );
}

#[test]
fn test_check_file_still_works() {
    let dir = tempdir().expect("failed to create temp dir");
    let fixture = workspace_root().join("tests/fixtures/functions/hello.kr");
    std::fs::copy(&fixture, dir.path().join("hello.kr")).expect("failed to copy fixture");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .args(["check", "hello.kr"])
        .output()
        .expect("failed to run krypton check");
    assert!(
        output.status.success(),
        "check of file should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

// ---------------------------------------------------------------------------
// `krypton add` / `krypton remove` / `krypton update`
// ---------------------------------------------------------------------------

/// Invoke `git -C <dir> <args>` and assert success.
fn git(dir: &std::path::Path, args: &[&str]) -> std::process::Output {
    let output = Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("git {args:?} in {}: {e}", dir.display()));
    assert!(
        output.status.success(),
        "git {args:?} in {} failed: stderr={}",
        dir.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

/// Initialize a self-contained git repo at `dir` with the given files,
/// commit them on `main`, and return the resulting SHA. Uses a local
/// identity and disables gpg signing so the test does not depend on
/// the developer's git config.
fn git_init_repo(dir: &std::path::Path, files: &[(&str, &str)]) -> String {
    Command::new("git")
        .args(["-c", "init.defaultBranch=main", "init", "--quiet"])
        .arg(dir)
        .output()
        .expect("git init");
    git(dir, &["config", "user.email", "test@example.invalid"]);
    git(dir, &["config", "user.name", "Test User"]);
    git(dir, &["config", "commit.gpgsign", "false"]);
    for (rel, contents) in files {
        let path = dir.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(path, contents).unwrap();
    }
    git(dir, &["add", "--all"]);
    git(dir, &["commit", "-m", "initial", "--quiet"]);
    let out = git(dir, &["rev-parse", "HEAD"]);
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn git_add_commit(dir: &std::path::Path, message: &str, files: &[(&str, &str)]) -> String {
    for (rel, contents) in files {
        let path = dir.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(path, contents).unwrap();
    }
    git(dir, &["add", "--all"]);
    git(dir, &["commit", "-m", message, "--quiet"]);
    let out = git(dir, &["rev-parse", "HEAD"]);
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

/// Create a sibling path-dep directory `<parent>/mylib/` with a minimal
/// valid `krypton.toml` and `src/lib.kr`. Returns its absolute path.
fn write_sibling_path_dep(parent: &std::path::Path, name: &str, canonical: &str) -> PathBuf {
    let dep = parent.join(name);
    std::fs::create_dir_all(dep.join("src")).unwrap();
    std::fs::write(
        dep.join("krypton.toml"),
        format!("[package]\nname = \"{canonical}\"\nversion = \"0.1.0\"\n"),
    )
    .unwrap();
    std::fs::write(dep.join("src/lib.kr"), "fun greet() = \"hi\"\n").unwrap();
    dep
}

#[test]
fn test_add_path_dep_updates_manifest_and_lock() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());
    write_sibling_path_dep(dir.path(), "mylib", "clementine/mylib");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["add", "clementine/mylib", "--path", "../mylib"])
        .output()
        .expect("failed to run krypton add");
    assert!(
        output.status.success(),
        "add should succeed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let toml = std::fs::read_to_string(project.join("krypton.toml")).unwrap();
    assert!(
        toml.contains(r#"mylib = { package = "clementine/mylib", path = "../mylib" }"#),
        "manifest should list the new dep, got:\n{toml}"
    );

    let lock = std::fs::read_to_string(project.join("krypton.lock")).unwrap();
    assert!(
        lock.contains("clementine/mylib"),
        "lockfile should mention the new dep, got:\n{lock}"
    );
}

#[test]
fn test_add_git_dep_records_git_fields() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());

    // Build a local git repo that a `--git` dep can point at.
    let remote = dir.path().join("remote.git");
    std::fs::create_dir_all(&remote).unwrap();
    git_init_repo(
        &remote,
        &[(
            "krypton.toml",
            "[package]\nname = \"clementine/mylib\"\nversion = \"0.1.0\"\n",
        )],
    );
    git(&remote, &["tag", "v0.1.0"]);

    let url = format!("file://{}", remote.display());
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["add", "clementine/mylib", "--git", &url, "--tag", "v0.1.0"])
        .output()
        .expect("failed to run krypton add --git");
    assert!(
        output.status.success(),
        "add --git should succeed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let toml = std::fs::read_to_string(project.join("krypton.toml")).unwrap();
    assert!(
        toml.contains("git = "),
        "manifest should contain git url: {toml}"
    );
    assert!(
        toml.contains(r#"tag = "v0.1.0""#),
        "manifest should contain tag: {toml}"
    );
}

#[test]
fn test_add_errors_on_existing_local_root() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());
    let dep_path = write_sibling_path_dep(dir.path(), "mylib", "clementine/mylib");

    // Seed an initial `mylib` entry.
    let toml_path = project.join("krypton.toml");
    let mut toml = std::fs::read_to_string(&toml_path).unwrap();
    toml.push_str(&format!(
        "mylib = {{ package = \"clementine/mylib\", path = \"{}\" }}\n",
        dep_path.display()
    ));
    std::fs::write(&toml_path, toml).unwrap();

    // A second `krypton add` with the same default local-root must error.
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["add", "clementine/mylib", "--path", "../x"])
        .output()
        .expect("failed to run krypton add");
    assert!(!output.status.success(), "duplicate add should fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("dependency 'mylib' already exists"),
        "stderr should mention duplication, got: {stderr}"
    );
}

#[test]
fn test_add_with_as_flag_uses_custom_local_root() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());
    write_sibling_path_dep(dir.path(), "mylib", "clementine/mylib");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args([
            "add",
            "clementine/mylib",
            "--path",
            "../mylib",
            "--as",
            "my_lib",
        ])
        .output()
        .expect("failed to run krypton add --as");
    assert!(
        output.status.success(),
        "add --as should succeed: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let toml = std::fs::read_to_string(project.join("krypton.toml")).unwrap();
    assert!(
        toml.contains(r#"my_lib = { package = "clementine/mylib""#),
        "manifest should use custom local root 'my_lib': {toml}"
    );
    assert!(
        !toml.contains("\nmylib = "),
        "default 'mylib' key must not have been inserted: {toml}"
    );
}

#[test]
fn test_remove_existing_dep() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());
    write_sibling_path_dep(dir.path(), "mylib", "clementine/mylib");

    // First add, then remove.
    let add = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["add", "clementine/mylib", "--path", "../mylib"])
        .output()
        .expect("failed to run krypton add");
    assert!(add.status.success(), "add should succeed");

    let remove = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["remove", "mylib"])
        .output()
        .expect("failed to run krypton remove");
    assert!(
        remove.status.success(),
        "remove should succeed: stderr={}",
        String::from_utf8_lossy(&remove.stderr)
    );

    let toml = std::fs::read_to_string(project.join("krypton.toml")).unwrap();
    assert!(
        !toml.contains("clementine/mylib"),
        "dep should be gone: {toml}"
    );

    let lock = std::fs::read_to_string(project.join("krypton.lock")).unwrap();
    assert!(
        !lock.contains("clementine/mylib"),
        "lockfile should no longer reference the dep, got:\n{lock}"
    );
}

#[test]
fn test_remove_nonexistent_errors() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["remove", "does-not-exist"])
        .output()
        .expect("failed to run krypton remove");
    assert!(!output.status.success(), "remove of missing dep must fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("dependency 'does-not-exist' not found in [dependencies]"),
        "stderr should report missing dep, got: {stderr}"
    );
}

#[test]
fn test_update_rewrites_lockfile_for_branch_dep() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());

    // Build a local git repo we can push additional commits to.
    let remote = dir.path().join("remote");
    std::fs::create_dir_all(&remote).unwrap();
    let first_sha = git_init_repo(
        &remote,
        &[(
            "krypton.toml",
            "[package]\nname = \"clementine/mylib\"\nversion = \"0.1.0\"\n",
        )],
    );

    let url = format!("file://{}", remote.display());
    // Add a branch-tracked dep, which will populate the lockfile with first_sha.
    let add = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["add", "clementine/mylib", "--git", &url, "--branch", "main"])
        .output()
        .expect("failed to run krypton add --git --branch");
    assert!(
        add.status.success(),
        "add --git --branch should succeed: stderr={}",
        String::from_utf8_lossy(&add.stderr)
    );
    let lock_before = std::fs::read_to_string(project.join("krypton.lock")).unwrap();
    assert!(
        lock_before.contains(&first_sha),
        "initial lockfile should pin to first sha {first_sha}, got:\n{lock_before}"
    );

    // Push a second commit that bumps the dep version.
    let second_sha = git_add_commit(
        &remote,
        "second",
        &[(
            "krypton.toml",
            "[package]\nname = \"clementine/mylib\"\nversion = \"0.2.0\"\n",
        )],
    );
    assert_ne!(first_sha, second_sha);

    let update = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("update")
        .output()
        .expect("failed to run krypton update");
    assert!(
        update.status.success(),
        "update should succeed: stderr={}",
        String::from_utf8_lossy(&update.stderr)
    );

    let lock_after = std::fs::read_to_string(project.join("krypton.lock")).unwrap();
    assert!(
        lock_after.contains(&second_sha),
        "updated lockfile should advance to {second_sha}, got:\n{lock_after}"
    );
    assert!(
        !lock_after.contains(&first_sha),
        "updated lockfile should no longer reference first sha {first_sha}, got:\n{lock_after}"
    );
}

#[test]
fn test_update_noop_when_nothing_changed() {
    let dir = tempdir().expect("tempdir");
    let project = init_project_for_test(dir.path());

    let first = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("update")
        .output()
        .expect("failed to run krypton update");
    assert!(
        first.status.success(),
        "first update should succeed: stderr={}",
        String::from_utf8_lossy(&first.stderr)
    );
    let lock_first = std::fs::read_to_string(project.join("krypton.lock")).unwrap();

    let second = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("update")
        .output()
        .expect("failed to run second krypton update");
    assert!(second.status.success(), "second update should succeed");
    let lock_second = std::fs::read_to_string(project.join("krypton.lock")).unwrap();

    assert_eq!(
        lock_first, lock_second,
        "re-running update on a fresh project should be a no-op"
    );
}

#[test]
fn test_test_no_manifest_errors() {
    let dir = tempdir().expect("failed to create temp dir");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(dir.path())
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        !output.status.success(),
        "test should fail without krypton.toml"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("krypton.toml"),
        "stderr should mention krypton.toml, got: {stderr}"
    );
}

#[test]
fn test_test_succeeds_in_project_with_no_test_files() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        output.status.success(),
        "test should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.trim().is_empty(),
        "non-verbose stdout with no test files should be empty, got: {stdout}"
    );
    assert!(
        project.join("krypton.lock").is_file(),
        "krypton.lock should exist after `krypton test`"
    );
}

#[test]
fn test_test_accepts_filter_args() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["test", "math_test", "parser/lexer_test"])
        .output()
        .expect("failed to run krypton test");
    assert!(
        output.status.success(),
        "test should succeed with filter args: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_test_help_documents_filter_arg() {
    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .args(["test", "--help"])
        .output()
        .expect("failed to run krypton test --help");
    assert!(
        output.status.success(),
        "`krypton test --help` should exit 0: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("FILTERS"),
        "help should document the FILTERS positional, got: {stdout}"
    );
    assert!(
        !stdout.contains("--filter"),
        "help should not advertise a --filter long flag, got: {stdout}"
    );
}

#[test]
fn test_test_unknown_flag_errors() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["test", "--bogus-flag"])
        .output()
        .expect("failed to run krypton test --bogus-flag");
    assert!(
        !output.status.success(),
        "test should fail with an unknown flag"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("unexpected argument"),
        "stderr should mention 'unexpected argument', got: {stderr}"
    );
}

#[test]
fn test_test_verbose_prints_zero_when_no_tests() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["test", "--verbose"])
        .output()
        .expect("failed to run krypton test --verbose");
    assert!(
        output.status.success(),
        "test should succeed on bare init: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("0 test file"),
        "verbose output should mention '0 test file', got: {stdout}"
    );
}

#[test]
fn test_test_verbose_prints_count_with_tests() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(project.join("src/math_test.kr"), "# empty\n").expect("write math_test.kr");
    std::fs::create_dir_all(project.join("src/parser")).expect("create parser dir");
    std::fs::write(project.join("src/parser/lexer_test.kr"), "# empty\n")
        .expect("write parser/lexer_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["test", "--verbose"])
        .output()
        .expect("failed to run krypton test --verbose");
    assert!(
        output.status.success(),
        "test should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("2 test file"),
        "verbose output should mention '2 test file', got: {stdout}"
    );
}

#[test]
fn test_test_nonverbose_omits_count() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(project.join("src/math_test.kr"), "# empty\n").expect("write math_test.kr");
    std::fs::create_dir_all(project.join("src/parser")).expect("create parser dir");
    std::fs::write(project.join("src/parser/lexer_test.kr"), "# empty\n")
        .expect("write parser/lexer_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        output.status.success(),
        "test should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("test file"),
        "non-verbose output must not include count, got: {stdout}"
    );
}

#[test]
fn test_build_ignores_broken_test_file() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // A test file that would fail to parse, but is not imported anywhere.
    // `krypton build` must not touch it.
    std::fs::write(project.join("src/foo_test.kr"), "fun $$$ @@@\n").expect("write foo_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        output.status.success(),
        "build should ignore orphan test file: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        project.join("target/jvm/my-app.jar").is_file(),
        "target/jvm/my-app.jar should exist"
    );
}

#[test]
fn test_run_ignores_broken_test_file() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(project.join("src/foo_test.kr"), "fun $$$ @@@\n").expect("write foo_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    assert!(
        output.status.success(),
        "run should ignore orphan test file: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello world"),
        "run should still print 'hello world', got: {stdout}"
    );
}

#[test]
fn test_build_rejects_import_of_test_file() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // Well-formed test module that exports a public binding.
    std::fs::write(project.join("src/foo_test.kr"), "pub fun helper() = 42\n")
        .expect("write foo_test.kr");

    // Main imports the test module — must be rejected.
    std::fs::write(
        project.join("src/main.kr"),
        "import foo_test.{helper}\n\nfun main() { println(\"hi\") }\n",
    )
    .expect("overwrite main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    assert!(
        !output.status.success(),
        "build should reject test-module import"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("E0521"),
        "stderr should mention E0521, got: {stderr}"
    );
    assert!(
        stderr.contains("test module") || stderr.contains("krypton test"),
        "stderr should identify the rule (mention 'test module' or 'krypton test'), got: {stderr}"
    );
}

#[test]
fn test_test_verbose_short_flag() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(project.join("src/math_test.kr"), "# empty\n").expect("write math_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .args(["test", "-v"])
        .output()
        .expect("failed to run krypton test -v");
    assert!(
        output.status.success(),
        "test should succeed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("1 test file"),
        "short-flag verbose output should mention '1 test file', got: {stdout}"
    );
}

#[test]
fn test_test_source_error_aborts_before_tests() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // Source phase error: `main.kr` calls an undefined function.
    std::fs::write(
        project.join("src/main.kr"),
        "fun main() { undefined_fn() }\n",
    )
    .expect("overwrite main.kr");

    // A test file that would otherwise compile.
    std::fs::write(project.join("src/math_test.kr"), "fun test_noop() { }\n")
        .expect("write math_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        !output.status.success(),
        "test should fail when source unit has a type error"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stderr.contains("undefined_fn") || stderr.contains("src/main.kr"),
        "stderr should name the source error, got: {stderr}"
    );
    assert!(
        !stdout.contains("FAIL math_test") && !stdout.contains("FAIL src/math_test"),
        "must not print per-test FAIL when source phase aborted, got stdout: {stdout}"
    );
}

#[test]
fn test_test_compile_error_in_one_test_does_not_block_others() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // Good test — compiles clean.
    std::fs::write(project.join("src/good_test.kr"), "fun test_noop() { }\n")
        .expect("write good_test.kr");

    // Bad test — type error (assigning a String to an Int).
    std::fs::write(
        project.join("src/bad_test.kr"),
        "fun test_bad() { let x: Int = \"not an int\" }\n",
    )
    .expect("write bad_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        !output.status.success(),
        "test should fail when any test file fails to compile"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("FAIL src/bad_test.kr — compile error"),
        "stdout should contain FAIL line for bad_test, got: {stdout}"
    );
    assert!(
        !stdout.contains("FAIL src/good_test.kr"),
        "stdout must not FAIL the good test file, got: {stdout}"
    );
    // The diagnostic must be indented beneath the FAIL line.
    let mut lines = stdout.lines();
    let fail_idx = lines
        .position(|l| l.starts_with("FAIL src/bad_test.kr"))
        .expect("FAIL line must exist");
    let after: Vec<&str> = stdout.lines().skip(fail_idx + 1).collect();
    assert!(
        after.iter().any(|l| l.starts_with("  ")),
        "at least one line after FAIL should be indented (the diagnostic), got:\n{stdout}"
    );
}

#[test]
fn test_test_all_test_files_compile_exits_zero() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(project.join("src/a_test.kr"), "fun test_one() { }\n").expect("write a_test.kr");
    std::fs::write(project.join("src/b_test.kr"), "fun test_two() { }\n").expect("write b_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        output.status.success(),
        "test should succeed: stderr={}  stdout={}",
        String::from_utf8_lossy(&output.stderr),
        String::from_utf8_lossy(&output.stdout),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("FAIL "),
        "stdout should have no FAIL lines, got: {stdout}"
    );
}

#[test]
fn test_test_exit_code_one_on_any_compile_error() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(project.join("src/ok_a_test.kr"), "fun test_a() { }\n")
        .expect("write ok_a_test.kr");
    std::fs::write(project.join("src/ok_b_test.kr"), "fun test_b() { }\n")
        .expect("write ok_b_test.kr");
    std::fs::write(
        project.join("src/bad_test.kr"),
        "fun test_bad() { let x: Int = \"not an int\" }\n",
    )
    .expect("write bad_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        !output.status.success(),
        "exit code must be non-zero when any test file fails to compile"
    );
}

#[test]
fn test_test_test_links_against_source_exports() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // Source module exports `add`.
    std::fs::write(
        project.join("src/math.kr"),
        "pub fun add(x: Int, y: Int) -> Int = x + y\n",
    )
    .expect("write math.kr");

    std::fs::write(
        project.join("src/math_test.kr"),
        "import math.{add}\n\nfun test_sum() { let _ = add(1, 2) }\n",
    )
    .expect("write math_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    assert!(
        output.status.success(),
        "test should succeed when test imports live source exports: stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !stdout.contains("FAIL "),
        "stdout should have no FAIL lines, got: {stdout}"
    );
}

#[test]
fn test_test_one_passing_one_panicking_exits_1() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/simple_test.kr"),
        "fun test_passes() { }\nfun test_panics() { panic(\"boom\") }\n",
    )
    .expect("write simple_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when any test panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok simple_test/test_passes"),
        "expected 'ok simple_test/test_passes' line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL simple_test/test_panics"),
        "expected 'FAIL simple_test/test_panics' line, got: {stdout}"
    );
    assert!(
        stdout.contains("1 passed, 1 failed"),
        "expected summary '1 passed, 1 failed', got: {stdout}"
    );
}

#[test]
fn test_test_companion_compile_error_still_runs_passing_sibling() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(project.join("src/good_test.kr"), "fun test_x() { }\n")
        .expect("write good_test.kr");
    std::fs::write(
        project.join("src/bad_test.kr"),
        "fun test_y() { let x: Int = \"not an int\" }\n",
    )
    .expect("write bad_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when any test file fails to compile; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok good_test/test_x"),
        "passing sibling must run even when another test file fails to compile, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL src/bad_test.kr — compile error"),
        "expected per-file compile-error line, got: {stdout}"
    );
}

#[test]
fn test_test_invalid_test_signature_is_compile_error() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/bad_sig_test.kr"),
        "fun test_takes_arg(x: Int) { }\n\
         fun test_returns_int() -> Int = 1\n\
         fun test_generic[a]() { }\n\
         fun test_ok() { }\n",
    )
    .expect("write bad_sig_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let combined = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
    assert!(
        !output.status.success(),
        "exit code must be 1 when a test file has invalid signatures; combined={combined}"
    );
    let e0019_count = combined.matches("E0019").count();
    assert!(
        e0019_count >= 2,
        "expected at least two E0019 diagnostics (one per invalid signature), got {e0019_count}: {combined}"
    );
    assert!(
        !stdout.contains("ok bad_sig_test/test_ok"),
        "test_ok must not run because the file failed to compile, got: {stdout}"
    );
}

#[test]
fn test_test_assert_eq_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/eq_test.kr"),
        "import core/test.{assert_eq}\n\
         \n\
         fun test_assert_eq_passes() { assert_eq(3, 3) }\n\
         fun test_assert_eq_fails() { assert_eq(3, 4) }\n",
    )
    .expect("write eq_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when an assert_eq panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok eq_test/test_assert_eq_passes"),
        "expected 'ok eq_test/test_assert_eq_passes', got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL eq_test/test_assert_eq_fails"),
        "expected 'FAIL eq_test/test_assert_eq_fails', got: {stdout}"
    );
}

#[test]
fn test_test_assert_true_false_and_assert() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/bool_test.kr"),
        "import core/test.{assert, assert_true, assert_false}\n\
         \n\
         fun test_assert_true_pass() { assert(true) }\n\
         fun test_assert_true_fail() { assert(false) }\n\
         fun test_assert_true_helper_pass() { assert_true(true) }\n\
         fun test_assert_true_helper_fail() { assert_true(false) }\n\
         fun test_assert_false_pass() { assert_false(false) }\n\
         fun test_assert_false_fail() { assert_false(true) }\n",
    )
    .expect("write bool_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when an assertion panics; stdout={stdout} stderr={stderr}"
    );
    for name in [
        "test_assert_true_pass",
        "test_assert_true_helper_pass",
        "test_assert_false_pass",
    ] {
        let line = format!("ok bool_test/{name}");
        assert!(
            stdout.contains(&line),
            "expected '{line}' line, got: {stdout}"
        );
    }
    for name in [
        "test_assert_true_fail",
        "test_assert_true_helper_fail",
        "test_assert_false_fail",
    ] {
        let line = format!("FAIL bool_test/{name}");
        assert!(
            stdout.contains(&line),
            "expected '{line}' line, got: {stdout}"
        );
    }
}

#[test]
fn test_test_assert_neq_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/neq_test.kr"),
        "import core/test.{assert_neq}\n\
         \n\
         fun test_assert_neq_passes() { assert_neq(3, 4) }\n\
         fun test_assert_neq_fails() { assert_neq(3, 3) }\n",
    )
    .expect("write neq_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_neq panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok neq_test/test_assert_neq_passes"),
        "expected 'ok neq_test/test_assert_neq_passes', got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL neq_test/test_assert_neq_fails"),
        "expected 'FAIL neq_test/test_assert_neq_fails', got: {stdout}"
    );
}

#[test]
fn test_test_assert_does_not_consume_borrowed_subject() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/borrow_test.kr"),
        "import core/test.{assert_eq}\n\
         import core/string.{length, concat}\n\
         \n\
         fun test_buffer_length() {\n\
         \x20   let buf = \"hello\"\n\
         \x20   assert_eq(length(buf), 5)\n\
         \x20   let _ = concat(buf, \"!\")\n\
         }\n",
    )
    .expect("write borrow_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "test should pass when assert_eq does not consume its subject; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok borrow_test/test_buffer_length"),
        "expected 'ok borrow_test/test_buffer_length', got: {stdout}"
    );
}

#[test]
fn test_test_import_core_test_from_non_test_file() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/util.kr"),
        "import core/test.{assert_eq}\n\
         \n\
         pub fun check_one() -> Unit = assert_eq(1, 1)\n",
    )
    .expect("write util.kr");

    std::fs::write(
        project.join("src/util_test.kr"),
        "import util.{check_one}\n\
         \n\
         fun test_check_one_passes() { check_one() }\n",
    )
    .expect("write util_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "non-test files must be allowed to import core/test assertions; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok util_test/test_check_one_passes"),
        "expected 'ok util_test/test_check_one_passes', got: {stdout}"
    );
}

#[test]
fn test_test_assert_ok_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/assert_ok_test.kr"),
        "import core/test.{assert_ok}\n\
         import core/result.{Result, Ok, Err}\n\
         \n\
         fun a_success() -> Result[String, Int] = Ok(7)\n\
         fun a_failure() -> Result[String, Int] = Err(\"boom\")\n\
         \n\
         fun test_assert_ok_pass() {\n\
         \x20   let _ = assert_ok(a_success())\n\
         }\n\
         fun test_assert_ok_fail() {\n\
         \x20   let _ = assert_ok(a_failure())\n\
         }\n",
    )
    .expect("write assert_ok_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_ok panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok assert_ok_test/test_assert_ok_pass"),
        "expected 'ok assert_ok_test/test_assert_ok_pass', got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL assert_ok_test/test_assert_ok_fail"),
        "expected 'FAIL assert_ok_test/test_assert_ok_fail', got: {stdout}"
    );
}

#[test]
fn test_test_assert_err_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/assert_err_test.kr"),
        "import core/test.{assert_err}\n\
         import core/result.{Result, Ok, Err}\n\
         \n\
         fun a_failure() -> Result[String, Int] = Err(\"boom\")\n\
         fun a_success() -> Result[String, Int] = Ok(7)\n\
         \n\
         fun test_assert_err_pass() {\n\
         \x20   let _ = assert_err(a_failure())\n\
         }\n\
         fun test_assert_err_fail() {\n\
         \x20   let _ = assert_err(a_success())\n\
         }\n",
    )
    .expect("write assert_err_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_err panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok assert_err_test/test_assert_err_pass"),
        "expected 'ok assert_err_test/test_assert_err_pass', got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL assert_err_test/test_assert_err_fail"),
        "expected 'FAIL assert_err_test/test_assert_err_fail', got: {stdout}"
    );
}

#[test]
fn test_test_assert_some_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/assert_some_test.kr"),
        "import core/test.{assert_some}\n\
         import core/option.{Option, Some, None}\n\
         \n\
         fun nothing() -> Option[Int] = None\n\
         \n\
         fun test_assert_some_pass() {\n\
         \x20   let _ = assert_some(Some(42))\n\
         }\n\
         fun test_assert_some_fail() {\n\
         \x20   let _ = assert_some(nothing())\n\
         }\n",
    )
    .expect("write assert_some_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_some panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok assert_some_test/test_assert_some_pass"),
        "expected 'ok assert_some_test/test_assert_some_pass', got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL assert_some_test/test_assert_some_fail"),
        "expected 'FAIL assert_some_test/test_assert_some_fail', got: {stdout}"
    );
}

#[test]
fn test_test_assert_none_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/assert_none_test.kr"),
        "import core/test.{assert_none}\n\
         import core/option.{Option, Some, None}\n\
         \n\
         fun nothing() -> Option[Int] = None\n\
         \n\
         fun test_assert_none_pass() {\n\
         \x20   assert_none(nothing())\n\
         }\n\
         fun test_assert_none_fail() {\n\
         \x20   assert_none(Some(99))\n\
         }\n",
    )
    .expect("write assert_none_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_none panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok assert_none_test/test_assert_none_pass"),
        "expected 'ok assert_none_test/test_assert_none_pass', got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL assert_none_test/test_assert_none_fail"),
        "expected 'FAIL assert_none_test/test_assert_none_fail', got: {stdout}"
    );
}

#[test]
fn test_test_assert_ok_chained_unwrap() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/chain_test.kr"),
        "import core/test.{assert_ok, assert_eq}\n\
         import core/result.{Result, Ok, Err}\n\
         \n\
         fun returns_ok() -> Result[String, Int] = Ok(7)\n\
         \n\
         fun test_assert_ok_chained() {\n\
         \x20   let v = assert_ok(returns_ok())\n\
         \x20   assert_eq(v, 7)\n\
         }\n",
    )
    .expect("write chain_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "chained assert_ok unwrap should pass; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok chain_test/test_assert_ok_chained"),
        "expected 'ok chain_test/test_assert_ok_chained', got: {stdout}"
    );
}

#[test]
fn test_test_companion_private_fn_callable_from_test_file() {
    // The companion `_test.kr` file invokes a non-pub function from its
    // source twin and asserts the return value. The compiler accepts the
    // import via the companion bypass and the test runs to completion.
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/parser.kr"),
        "fun tokenize(x: Int) -> Int = x + 1\n",
    )
    .expect("write parser.kr");
    std::fs::write(
        project.join("src/parser_test.kr"),
        "import parser.{tokenize}\n\
         import core/test.{assert_eq}\n\
         \n\
         fun test_tokenize() { assert_eq(tokenize(41), 42) }\n",
    )
    .expect("write parser_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "test should succeed when test imports companion's private fn; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok parser_test/test_tokenize"),
        "expected 'ok parser_test/test_tokenize', got: {stdout}"
    );
}

#[test]
fn test_test_sibling_private_inaccessible() {
    // `lexer_test` (companion of `lexer`) tries to import a private fn
    // from `parser` — a sibling, not its companion. Compilation must
    // fail with the standard E0503 PrivateName diagnostic.
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/parser.kr"),
        "fun private_x(x: Int) -> Int = x\npub fun parse(x: Int) -> Int = private_x(x)\n",
    )
    .expect("write parser.kr");
    std::fs::write(
        project.join("src/lexer.kr"),
        "pub fun lex() -> Int = 0\n",
    )
    .expect("write lexer.kr");
    std::fs::write(
        project.join("src/lexer_test.kr"),
        "import parser.{private_x}\n\nfun test_x() { let _ = private_x(1) }\n",
    )
    .expect("write lexer_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be non-zero when sibling imports a private name"
    );
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("E0503"),
        "expected E0503 diagnostic for sibling-private import, got stdout={stdout} stderr={stderr}"
    );
}

#[test]
fn test_test_companion_private_type_and_constructor_visible() {
    // The companion test constructs a private record from the source twin
    // and reads its field, exercising both private-type binding and
    // private-constructor binding through the bypass.
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/data.kr"),
        "type Inner = { x: Int }\n\
         pub fun zero() -> Int = 0\n",
    )
    .expect("write data.kr");
    std::fs::write(
        project.join("src/data_test.kr"),
        "import data.{Inner}\n\
         import core/test.{assert_eq}\n\
         \n\
         fun test_inner() {\n\
         \x20 let inner = Inner { x = 7 }\n\
         \x20 assert_eq(inner.x, 7)\n\
         }\n",
    )
    .expect("write data_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "test should succeed when test constructs companion's private type; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok data_test/test_inner"),
        "expected 'ok data_test/test_inner', got: {stdout}"
    );
}

#[test]
fn test_test_helpers_test_with_no_companion_compiles() {
    // `helpers_test.kr` has no `helpers.kr` source twin. The file must
    // still typecheck and run as a standalone test module — no companion
    // bypass is set, but no error fires either.
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/helpers_test.kr"),
        "fun test_x() { }\n",
    )
    .expect("write helpers_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "standalone test file with no companion source must still run; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok helpers_test/test_x"),
        "expected 'ok helpers_test/test_x', got: {stdout}"
    );
}

#[test]
fn test_test_imported_module_cannot_access_test_companion_privates() {
    // A sibling source module (`util.kr`) tries to import a private fn
    // from `parser`. Even with `parser_test.kr` present in the project,
    // ordinary cross-module visibility rules apply: the compiler emits
    // E0503. The bypass is scoped to the test file itself, not propagated
    // to other consumers.
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/parser.kr"),
        "fun private_x(x: Int) -> Int = x\npub fun parse(x: Int) -> Int = private_x(x)\n",
    )
    .expect("write parser.kr");
    std::fs::write(
        project.join("src/parser_test.kr"),
        "import parser.{parse}\n\nfun test_p() { let _ = parse(1) }\n",
    )
    .expect("write parser_test.kr");
    std::fs::write(
        project.join("src/util.kr"),
        "import parser.{private_x}\n\npub fun u(x: Int) -> Int = private_x(x)\n",
    )
    .expect("write util.kr");
    // Wire `util` into the build's transitive closure so `build` actually
    // typechecks it (the build entry is `src/main.kr`, which the init
    // template populates with a no-import `println`).
    std::fs::write(
        project.join("src/main.kr"),
        "import util.{u}\n\nfun main() = println(show(u(1)))\n",
    )
    .expect("overwrite main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "build must reject ordinary modules that import companion privates"
    );
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("E0503"),
        "expected E0503 diagnostic for non-test sibling consumer, got stdout={stdout} stderr={stderr}"
    );
}

#[test]
fn test_test_assert_true_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/true_msg_test.kr"),
        "import core/test.{assert_true_msg}\n\
         \n\
         fun test_assert_true_msg_pass() { assert_true_msg(true, \"ok\") }\n\
         fun test_assert_true_msg_fail() { assert_true_msg(false, \"case-1\") }\n",
    )
    .expect("write true_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_true_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok true_msg_test/test_assert_true_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL true_msg_test/test_assert_true_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_test_assert_false_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/false_msg_test.kr"),
        "import core/test.{assert_false_msg}\n\
         \n\
         fun test_assert_false_msg_pass() { assert_false_msg(false, \"ok\") }\n\
         fun test_assert_false_msg_fail() { assert_false_msg(true, \"case-1\") }\n",
    )
    .expect("write false_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_false_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok false_msg_test/test_assert_false_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL false_msg_test/test_assert_false_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_test_assert_eq_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/eq_msg_test.kr"),
        "import core/test.{assert_eq_msg}\n\
         \n\
         fun test_assert_eq_msg_pass() { assert_eq_msg(3, 3, \"ok\") }\n\
         fun test_assert_eq_msg_fail() { assert_eq_msg(3, 4, \"case-1\") }\n",
    )
    .expect("write eq_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_eq_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok eq_msg_test/test_assert_eq_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL eq_msg_test/test_assert_eq_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_test_assert_neq_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/neq_msg_test.kr"),
        "import core/test.{assert_neq_msg}\n\
         \n\
         fun test_assert_neq_msg_pass() { assert_neq_msg(3, 4, \"ok\") }\n\
         fun test_assert_neq_msg_fail() { assert_neq_msg(3, 3, \"case-1\") }\n",
    )
    .expect("write neq_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_neq_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok neq_msg_test/test_assert_neq_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL neq_msg_test/test_assert_neq_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_test_assert_ok_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/ok_msg_test.kr"),
        "import core/test.{assert_ok_msg}\n\
         import core/result.{Result, Ok, Err}\n\
         \n\
         fun a_success() -> Result[String, Int] = Ok(7)\n\
         fun a_failure() -> Result[String, Int] = Err(\"boom\")\n\
         \n\
         fun test_assert_ok_msg_pass() {\n\
         \x20   let _ = assert_ok_msg(a_success(), \"ok\")\n\
         }\n\
         fun test_assert_ok_msg_fail() {\n\
         \x20   let _ = assert_ok_msg(a_failure(), \"case-1\")\n\
         }\n",
    )
    .expect("write ok_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_ok_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok ok_msg_test/test_assert_ok_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL ok_msg_test/test_assert_ok_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_test_assert_err_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/err_msg_test.kr"),
        "import core/test.{assert_err_msg}\n\
         import core/result.{Result, Ok, Err}\n\
         \n\
         fun a_failure() -> Result[String, Int] = Err(\"boom\")\n\
         fun a_success() -> Result[String, Int] = Ok(7)\n\
         \n\
         fun test_assert_err_msg_pass() {\n\
         \x20   let _ = assert_err_msg(a_failure(), \"ok\")\n\
         }\n\
         fun test_assert_err_msg_fail() {\n\
         \x20   let _ = assert_err_msg(a_success(), \"case-1\")\n\
         }\n",
    )
    .expect("write err_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_err_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok err_msg_test/test_assert_err_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL err_msg_test/test_assert_err_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_test_assert_some_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/some_msg_test.kr"),
        "import core/test.{assert_some_msg}\n\
         import core/option.{Option, Some, None}\n\
         \n\
         fun nothing() -> Option[Int] = None\n\
         \n\
         fun test_assert_some_msg_pass() {\n\
         \x20   let _ = assert_some_msg(Some(42), \"ok\")\n\
         }\n\
         fun test_assert_some_msg_fail() {\n\
         \x20   let _ = assert_some_msg(nothing(), \"case-1\")\n\
         }\n",
    )
    .expect("write some_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_some_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok some_msg_test/test_assert_some_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL some_msg_test/test_assert_some_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_test_assert_none_msg_passes_and_fails() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/none_msg_test.kr"),
        "import core/test.{assert_none_msg}\n\
         import core/option.{Option, Some, None}\n\
         \n\
         fun nothing() -> Option[Int] = None\n\
         \n\
         fun test_assert_none_msg_pass() {\n\
         \x20   assert_none_msg(nothing(), \"ok\")\n\
         }\n\
         fun test_assert_none_msg_fail() {\n\
         \x20   assert_none_msg(Some(99), \"case-1\")\n\
         }\n",
    )
    .expect("write none_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when assert_none_msg panics; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok none_msg_test/test_assert_none_msg_pass"),
        "expected pass line, got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL none_msg_test/test_assert_none_msg_fail"),
        "expected FAIL line, got: {stdout}"
    );
}

#[test]
fn test_run_assert_eq_msg_panic_includes_context_line() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/main.kr"),
        "import core/test.{assert_eq_msg}\n\
         \n\
         fun main() = assert_eq_msg(1, 2, \"my-label\")\n",
    )
    .expect("overwrite main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "krypton run must exit non-zero on uncaught panic; stdout={stdout} stderr={stderr}"
    );
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("assertion failed: assert_eq"),
        "expected base-name header 'assertion failed: assert_eq', got stdout={stdout} stderr={stderr}"
    );
    assert!(
        !combined.contains("assertion failed: assert_eq_msg"),
        "header must use base name (assert_eq), not assert_eq_msg; got stdout={stdout} stderr={stderr}"
    );
    assert!(
        combined.contains("expected: 2"),
        "expected 'expected: 2' line, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        combined.contains("got:      1"),
        "expected 'got:      1' line, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        combined.contains("context: my-label"),
        "expected 'context: my-label' line, got stdout={stdout} stderr={stderr}"
    );
}

#[test]
fn test_run_assert_ok_msg_panic_includes_context_line() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/main.kr"),
        "import core/test.{assert_ok_msg}\n\
         import core/result.{Result, Ok, Err}\n\
         \n\
         fun mk() -> Result[String, Int] = Err(\"boom\")\n\
         fun main() {\n\
         \x20   let _ = assert_ok_msg(mk(), \"load step\")\n\
         }\n",
    )
    .expect("overwrite main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "krypton run must exit non-zero on uncaught panic; stdout={stdout} stderr={stderr}"
    );
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("assertion failed: assert_ok"),
        "expected base-name header 'assertion failed: assert_ok', got stdout={stdout} stderr={stderr}"
    );
    assert!(
        !combined.contains("assertion failed: assert_ok_msg"),
        "header must use base name (assert_ok), not assert_ok_msg; got stdout={stdout} stderr={stderr}"
    );
    assert!(
        combined.contains("got: Err(\"boom\")") || combined.contains("got: Err(boom)"),
        "expected 'got: Err(...)' line with err payload, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        combined.contains("context: load step"),
        "expected 'context: load step' line, got stdout={stdout} stderr={stderr}"
    );
}

#[test]
fn test_run_assert_none_msg_panic_includes_context_line() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/main.kr"),
        "import core/test.{assert_none_msg}\n\
         import core/option.{Option, Some, None}\n\
         \n\
         fun main() = assert_none_msg(Some(99), \"lookup\")\n",
    )
    .expect("overwrite main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("run")
        .output()
        .expect("failed to run krypton run");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "krypton run must exit non-zero on uncaught panic; stdout={stdout} stderr={stderr}"
    );
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("assertion failed: assert_none"),
        "expected base-name header 'assertion failed: assert_none', got stdout={stdout} stderr={stderr}"
    );
    assert!(
        !combined.contains("assertion failed: assert_none_msg"),
        "header must use base name (assert_none), not assert_none_msg; got stdout={stdout} stderr={stderr}"
    );
    assert!(
        combined.contains("got: Some(99)"),
        "expected 'got: Some(99)' line, got stdout={stdout} stderr={stderr}"
    );
    assert!(
        combined.contains("context: lookup"),
        "expected 'context: lookup' line, got stdout={stdout} stderr={stderr}"
    );
}

#[test]
fn test_test_assert_eq_msg_table_driven_identifies_case() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/table_test.kr"),
        "import core/test.{assert_eq_msg}\n\
         \n\
         fun double(x: Int) -> Int = if x == 5 { 11 } else { x + x }\n\
         \n\
         fun test_table() {\n\
         \x20   assert_eq_msg(double(1), 2, \"double(1)\")\n\
         \x20   assert_eq_msg(double(3), 6, \"double(3)\")\n\
         \x20   assert_eq_msg(double(5), 10, \"double(5)\")\n\
         \x20   assert_eq_msg(double(7), 14, \"double(7)\")\n\
         }\n",
    )
    .expect("write table_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "table-driven test should fail (case 3 is wrong); stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("FAIL table_test/test_table"),
        "expected FAIL line for table_test/test_table, got: {stdout}"
    );
    assert!(
        stdout.contains("0 passed, 1 failed"),
        "expected '0 passed, 1 failed' summary, got: {stdout}"
    );
}

#[test]
fn test_test_assert_ok_msg_and_some_msg_chained_unwrap() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/chain_msg_test.kr"),
        "import core/test.{assert_ok_msg, assert_some_msg, assert_eq}\n\
         import core/result.{Result, Ok, Err}\n\
         import core/option.{Option, Some, None}\n\
         \n\
         fun mk_ok() -> Result[String, Int] = Ok(7)\n\
         fun mk_some() -> Option[Int] = Some(42)\n\
         \n\
         fun test_chain() {\n\
         \x20   let v = assert_ok_msg(mk_ok(), \"load step\")\n\
         \x20   assert_eq(v, 7)\n\
         \x20   let w = assert_some_msg(mk_some(), \"lookup step\")\n\
         \x20   assert_eq(w, 42)\n\
         }\n",
    )
    .expect("write chain_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "chained _msg unwraps should pass; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok chain_msg_test/test_chain"),
        "expected 'ok chain_msg_test/test_chain', got: {stdout}"
    );
}

#[test]
fn test_test_assert_msg_passing_calls_emit_no_context_noise() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/quiet_msg_test.kr"),
        "import core/test.{assert_eq_msg, assert_neq_msg, assert_true_msg}\n\
         \n\
         fun test_quiet() {\n\
         \x20   assert_eq_msg(1, 1, \"x\")\n\
         \x20   assert_neq_msg(1, 2, \"y\")\n\
         \x20   assert_true_msg(true, \"z\")\n\
         }\n",
    )
    .expect("write quiet_msg_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "passing _msg calls should produce a green run; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok quiet_msg_test/test_quiet"),
        "expected 'ok quiet_msg_test/test_quiet', got: {stdout}"
    );
    assert!(
        !stdout.contains("context:"),
        "passing _msg calls must not emit any 'context:' line, got stdout={stdout}"
    );
}

#[test]
fn test_test_assert_eq_failure_includes_at_line() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // The assert_eq call sits on line 3 of the file. The test asserts the
    // failure message points at that line via the `at src/sample_test.kr:3`
    // footer.
    std::fs::write(
        project.join("src/sample_test.kr"),
        "import core/test.{assert_eq}\n\
         fun test_fail() {\n\
         \x20   assert_eq(3, 4)\n\
         }\n",
    )
    .expect("write sample_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "assert_eq(3, 4) should fail; stdout={stdout} stderr={stderr}"
    );
    // `assert_eq(left, right)` reports `expected: <right>` (the second arg
    // — the value we expected to see) and `got: <left>` (the first arg — the
    // value actually produced). This is the same orientation as Rust's
    // `assert_eq!` macro: arg-1 is the value-under-test, arg-2 is the
    // expected reference.
    for needle in [
        "assertion failed: assert_eq",
        "expected: 4",
        "got:      3",
        "at src/sample_test.kr:3",
    ] {
        assert!(
            stdout.contains(needle),
            "expected stdout to contain `{needle}`, got: {stdout}"
        );
    }
}

#[test]
fn test_test_assert_at_line_skips_core_test_frames() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // `do_assert` sits in the same `_test.kr` file as `test_fail`. The
    // stack-walk picks the most-recent (deepest) frame whose source file
    // ends in `_test.kr`, which is the `do_assert` body itself — line 4 of
    // skip_test.kr. core/test frames are skipped because their file is
    // `test.kr` (no `_test.kr` suffix).
    std::fs::write(
        project.join("src/skip_test.kr"),
        "import core/test.{assert_eq}\n\
         \n\
         fun do_assert() {\n\
         \x20   assert_eq(1, 2)\n\
         }\n\
         \n\
         fun test_fail() {\n\
         \x20   do_assert()\n\
         }\n",
    )
    .expect("write skip_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "stack-walk skip test should fail; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("at src/skip_test.kr:4"),
        "expected `at src/skip_test.kr:4` (helper-body line), got: {stdout}"
    );
}

#[test]
fn test_test_short_form_assertions_have_no_expected_got() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // The `assert(false)` call is on line 3. Short-form assertions render
    // only the assertion-name line and the `at` footer — no `expected:` /
    // `got:` lines (AC3).
    std::fs::write(
        project.join("src/short_test.kr"),
        "import core/test.{assert}\n\
         fun test_fail() {\n\
         \x20   assert(false)\n\
         }\n",
    )
    .expect("write short_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "short-form assert should fail; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("assertion failed: assert"),
        "expected `assertion failed: assert`, got: {stdout}"
    );
    assert!(
        stdout.contains("at src/short_test.kr:3"),
        "expected `at src/short_test.kr:3`, got: {stdout}"
    );
    // Slice the failure message between `assertion failed:` and the next
    // FAIL/summary line — the `expected:`/`got:` exclusion only applies
    // there, not anywhere else in the output.
    let failure_segment = stdout
        .split_once("assertion failed: assert")
        .map(|(_, rest)| rest.split("\n0 passed").next().unwrap_or(rest))
        .unwrap_or(&stdout);
    assert!(
        !failure_segment.contains("expected:"),
        "short-form must not contain `expected:`, got: {stdout}"
    );
    assert!(
        !failure_segment.contains("got:"),
        "short-form must not contain `got:`, got: {stdout}"
    );
}

#[test]
fn test_test_assert_none_shows_got_some_value() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/none_test.kr"),
        "import core/test.{assert_none}\n\
         import core/option.{Some}\n\
         fun test_fail() {\n\
         \x20   assert_none(Some(42))\n\
         }\n",
    )
    .expect("write none_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "assert_none(Some(42)) should fail; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("got: Some(42)"),
        "expected `got: Some(42)`, got: {stdout}"
    );
    assert!(
        stdout.contains("at src/none_test.kr:4"),
        "expected `at src/none_test.kr:4`, got: {stdout}"
    );
}

#[test]
fn test_test_assert_eq_multiline_show_is_indented() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // A custom Show instance whose render contains a newline. The continuation
    // lines must be re-indented to column 12 so they align with the value
    // column under `expected:` / `got:` (AC5).
    // The custom `Show` instance returns a multi-line string. Continuation
    // lines start at the very first column of the rendered string —
    // `indent_show` is responsible for re-indenting every newline to match
    // the value column under `expected:` / `got:`. The fixture deliberately
    // emits a value whose own lines start at column 0 so the reindent shows
    // up unambiguously as exactly 12 leading spaces.
    std::fs::write(
        project.join("src/multi_test.kr"),
        "import core/test.{assert_eq}\n\
         import core/show.{Show}\n\
         \n\
         pub type Foo = Foo(Int)\n\
         \n\
         impl Show[Foo] {\n\
         \x20   fun show(f: Foo) -> String = match f {\n\
         \x20       Foo(n) => \"Foo {\\nx: 1\\ny: 2\\n}\",\n\
         \x20   }\n\
         }\n\
         \n\
         impl Eq[Foo] {\n\
         \x20   fun eq(a: Foo, b: Foo) -> Bool = false\n\
         }\n\
         \n\
         fun test_fail() {\n\
         \x20   assert_eq(Foo(1), Foo(2))\n\
         }\n",
    )
    .expect("write multi_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "multiline-show assert_eq should fail; stdout={stdout} stderr={stderr}"
    );
    // Continuation lines are indented to column 12 so they line up under the
    // `expected:` / `got:` value columns. The `Foo {` opening line is
    // followed by `<12 spaces>x: 1` (the literal indent emitted by
    // `indent_show`).
    assert!(
        stdout.contains("Foo {\n            x: 1"),
        "expected continuation line indented to column 12 after `Foo {{`, got: {stdout}"
    );
}

#[test]
fn test_test_first_test_frame_helper_is_not_public() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    // Importing `firstTestFrame` from the project entry point (`src/main.kr`)
    // must fail because the helper is module-private (no `pub`) inside
    // `core/test`. AC6. We overwrite the scaffolded `main.kr` so the build
    // exercises the import-path visibility check on the real entry — random
    // sibling files like `src/leak.kr` are not compiled by `krypton build`.
    std::fs::write(
        project.join("src/main.kr"),
        "import core/test.{firstTestFrame}\n\
         pub fun main() -> Unit = ()\n",
    )
    .expect("write main.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("build")
        .output()
        .expect("failed to run krypton build");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "build must fail when leaking firstTestFrame; stdout={stdout} stderr={stderr}"
    );
    let combined = format!("{stdout}{stderr}");
    assert!(
        combined.contains("firstTestFrame"),
        "diagnostic should mention `firstTestFrame`, got: {combined}"
    );
}

/// A non-cooperative tail-recursive helper drives a wall-clock timeout in the
/// middle test. The two surrounding tests must pass, the timing-out test must
/// be marked FAIL with the message `test timed out`, and the suite must
/// continue executing past the timeout — covering acceptance criteria 1, 3,
/// 5 and 6 of M44-T10 in a single 5-second-budget fixture.
#[test]
fn test_test_timeout_marks_test_as_failed_and_continues() {
    let dir = tempdir().expect("failed to create temp dir");
    let project = init_project_for_test(dir.path());

    std::fs::write(
        project.join("src/timeout_test.kr"),
        "fun loop_forever() -> Unit = recur()\n\
         \n\
         fun test_a_passes() { }\n\
         fun test_b_loops() { loop_forever() }\n\
         fun test_c_after() { }\n",
    )
    .expect("write timeout_test.kr");

    let output = Command::new(env!("CARGO_BIN_EXE_krypton"))
        .current_dir(&project)
        .env("KRYPTON_HOME", dir.path().join("krypton-home"))
        .arg("test")
        .output()
        .expect("failed to run krypton test");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "exit code must be 1 when a test times out; stdout={stdout} stderr={stderr}"
    );
    assert!(
        stdout.contains("ok timeout_test/test_a_passes"),
        "expected 'ok timeout_test/test_a_passes', got: {stdout}"
    );
    assert!(
        stdout.contains("FAIL timeout_test/test_b_loops"),
        "expected 'FAIL timeout_test/test_b_loops', got: {stdout}"
    );
    assert!(
        stdout.contains("test timed out"),
        "expected 'test timed out' message in failure output, got: {stdout}"
    );
    assert!(
        stdout.contains("ok timeout_test/test_c_after"),
        "subsequent test must still run after a timeout, got: {stdout}"
    );
    assert!(
        stdout.contains("2 passed, 1 failed"),
        "expected summary '2 passed, 1 failed', got: {stdout}"
    );
}
