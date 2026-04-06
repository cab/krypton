use krypton_codegen::emit::generate_empty_main;
use std::io::Write;
use std::process::Command;

#[test]
fn test_generate_valid_classfile() {
    let bytes = generate_empty_main("TestClass").expect("should generate class file");
    // Class files start with magic 0xCAFEBABE
    assert_eq!(&bytes[..4], &[0xCA, 0xFE, 0xBA, 0xBE]);
}

#[test]
fn test_java_loads_classfile() {
    let bytes = generate_empty_main("TestClass").unwrap();
    let dir = tempfile::tempdir().unwrap();
    let class_path = dir.path().join("TestClass.class");
    let mut f = std::fs::File::create(&class_path).unwrap();
    f.write_all(&bytes).unwrap();
    drop(f);

    let output = Command::new("java")
        .arg("-cp")
        .arg(dir.path())
        .arg("TestClass")
        .output()
        .expect("java command should run");

    assert!(
        output.status.success(),
        "java exited with {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn test_javap_confirms_bytecode() {
    let bytes = generate_empty_main("TestClass").unwrap();
    let dir = tempfile::tempdir().unwrap();
    let class_path = dir.path().join("TestClass.class");
    std::fs::write(&class_path, &bytes).unwrap();

    let output = Command::new("javap")
        .arg("-v")
        .arg("TestClass")
        .current_dir(dir.path())
        .output()
        .expect("javap command should run");

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "javap failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        stdout.contains("public static void main(java.lang.String[])"),
        "expected main method signature in javap output:\n{stdout}"
    );
    assert!(
        stdout.contains("return"),
        "expected return instruction in javap output:\n{stdout}"
    );
}
