use krypton_codegen::emit::generate_empty_main;
use krypton_codegen::jar::write_jar;
use std::io::{Cursor, Read, Write};
use std::process::Command;

#[test]
fn test_jar_loadable_by_java() {
    let class_bytes = generate_empty_main("Test").expect("generate_empty_main should succeed");
    let classes = vec![("Test".to_string(), class_bytes)];
    let jar_bytes = write_jar(&classes, "Test").expect("write_jar should succeed");

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
    let jar_bytes = write_jar(&classes, "Test").expect("write_jar should succeed");

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
    let jar_bytes = write_jar(&classes, "Test").expect("write_jar should succeed");

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
