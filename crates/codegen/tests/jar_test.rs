use krypton_codegen::emit::generate_empty_main;
use krypton_codegen::jar::{find_runtime_jar, write_jar};
use std::io::{Cursor, Read, Write};
use std::process::Command;

#[test]
fn test_jar_loadable_by_java() {
    let class_bytes = generate_empty_main("Test").expect("generate_empty_main should succeed");
    let classes = vec![("Test".to_string(), class_bytes)];
    let jar_bytes = write_jar(&classes, "Test", None).expect("write_jar should succeed");

    let dir = tempfile::tempdir().unwrap();
    let jar_path = dir.path().join("test.jar");
    let mut f = std::fs::File::create(&jar_path).unwrap();
    f.write_all(&jar_bytes).unwrap();

    let output = Command::new("java")
        .arg("-jar")
        .arg(&jar_path)
        .output()
        .expect("java command should run");

    assert!(
        output.status.success(),
        "java should exit 0, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_manifest_contents() {
    let class_bytes = generate_empty_main("Test").expect("generate_empty_main should succeed");
    let classes = vec![("Test".to_string(), class_bytes)];
    let jar_bytes = write_jar(&classes, "Test", None).expect("write_jar should succeed");

    let cursor = Cursor::new(jar_bytes);
    let mut archive = zip::ZipArchive::new(cursor).expect("should be valid zip");

    let mut manifest = archive
        .by_name("META-INF/MANIFEST.MF")
        .expect("manifest should exist");
    let mut contents = String::new();
    manifest.read_to_string(&mut contents).unwrap();

    assert!(
        contents.contains("Manifest-Version: 1.0"),
        "manifest should contain version"
    );
    assert!(
        contents.contains("Main-Class: Test"),
        "manifest should contain main class"
    );
}

#[test]
fn test_nested_package_paths() {
    let main_bytes = generate_empty_main("Test").expect("generate_empty_main should succeed");
    let nested_bytes = generate_empty_main("Option").expect("generate_empty_main should succeed");

    let classes = vec![
        ("Test".to_string(), main_bytes),
        ("core/option".to_string(), nested_bytes),
    ];
    let jar_bytes = write_jar(&classes, "Test", None).expect("write_jar should succeed");

    let cursor = Cursor::new(jar_bytes);
    let archive = zip::ZipArchive::new(cursor).expect("should be valid zip");

    let names: Vec<&str> = archive.file_names().collect();
    assert!(
        names.contains(&"Test.class"),
        "should contain Test.class, got: {names:?}"
    );
    assert!(
        names.contains(&"core/option.class"),
        "should contain core/option.class, got: {names:?}"
    );
}

#[test]
fn test_bundle_runtime_classes() {
    let runtime_jar = find_runtime_jar().expect("runtime JAR should exist (build with gradle first)");

    let class_bytes = generate_empty_main("Test").expect("generate_empty_main should succeed");
    let classes = vec![("Test".to_string(), class_bytes)];
    let jar_bytes =
        write_jar(&classes, "Test", Some(&runtime_jar)).expect("write_jar should succeed");

    let cursor = Cursor::new(jar_bytes);
    let archive = zip::ZipArchive::new(cursor).expect("should be valid zip");

    let names: Vec<&str> = archive.file_names().collect();

    // User class should be present
    assert!(
        names.contains(&"Test.class"),
        "should contain Test.class, got: {names:?}"
    );

    // Runtime classes should be bundled
    assert!(
        names.contains(&"krypton/runtime/KryptonRuntime.class"),
        "should contain KryptonRuntime.class, got: {names:?}"
    );
    assert!(
        names.contains(&"krypton/runtime/KryptonIO.class"),
        "should contain KryptonIO.class, got: {names:?}"
    );
    assert!(
        names.contains(&"krypton/runtime/KryptonString.class"),
        "should contain KryptonString.class, got: {names:?}"
    );

    // META-INF from runtime should NOT be duplicated
    let meta_count = names.iter().filter(|n| n.starts_with("META-INF/")).count();
    assert_eq!(meta_count, 1, "should have exactly one META-INF entry (manifest)");
}

#[test]
fn test_fat_jar_runs_with_java_jar() {
    let runtime_jar = find_runtime_jar().expect("runtime JAR should exist (build with gradle first)");

    // Compile a hello-world program that uses println (requires runtime)
    let source = "import core/io.{println}\nfun main() = println(\"hello from fat jar\")";

    let (module, errors) = krypton_parser::parser::parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let resolver = krypton_modules::module_resolver::CompositeResolver::stdlib_only();
    let typed_modules = krypton_typechecker::infer::infer_module(&module, &resolver, "test".to_string())
        .expect("type checking should succeed");

    let classes = krypton_codegen::emit::compile_modules(&typed_modules, "FatJarTest")
        .expect("codegen should succeed");

    let jar_bytes = write_jar(&classes, "FatJarTest", Some(&runtime_jar))
        .expect("write_jar should succeed");

    let dir = tempfile::tempdir().unwrap();
    let jar_path = dir.path().join("fatjar.jar");
    std::fs::write(&jar_path, &jar_bytes).unwrap();

    let output = Command::new("java")
        .arg("-jar")
        .arg(&jar_path)
        .output()
        .expect("java command should run");

    assert!(
        output.status.success(),
        "java -jar should exit 0, stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("hello from fat jar"),
        "expected 'hello from fat jar' in stdout, got: {stdout}"
    );
}
