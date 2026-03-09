use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use krypton_codegen::emit::compile_module;
use krypton_parser::parser::parse;
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};

fn build_classpath(class_dir: &Path) -> String {
    let sep = if cfg!(windows) { ";" } else { ":" };
    let jar = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../runtime/build/libs/krypton-runtime.jar");
    if jar.exists() {
        format!("{}{}{}", class_dir.display(), sep, jar.display())
    } else {
        class_dir.display().to_string()
    }
}

fn run_program(source: &str) -> String {
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let classes = compile_module(&module, "Test").expect("compile_module should succeed");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        let mut f = std::fs::File::create(&class_path).unwrap();
        f.write_all(bytes).unwrap();
    }

    let classpath = build_classpath(dir.path());
    let output = Command::new("java")
        .arg("-cp")
        .arg(&classpath)
        .arg("Test")
        .output()
        .expect("java command should run");

    assert!(
        output.status.success(),
        "java exited with {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

fn run_codegen_fixtures(subdir: &str) {
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join(format!("tests/fixtures/{}", subdir));

    let fixtures = discover_fixtures(&fixture_dir);
    assert!(
        !fixtures.is_empty(),
        "no fixtures found in {}",
        fixture_dir.display()
    );

    let mut ran = 0;
    for fixture_path in fixtures {
        let fixture = load_fixture(&fixture_path);
        let name = fixture_path
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Output(expected) => {
                    let actual = run_program(&fixture.source);
                    assert_eq!(
                        actual, *expected,
                        "fixture {name}: expected output {expected:?} but got {actual:?}"
                    );
                    ran += 1;
                }
                Expectation::Ok => {
                    let (module, errors) = parse(&fixture.source);
                    if !errors.is_empty() {
                        continue;
                    }
                    match compile_module(&module, "Test") {
                        Ok(_) => { ran += 1; }
                        Err(krypton_codegen::emit::CodegenError::NoMainFunction) => {}
                        Err(e) => {
                            panic!("fixture {name}: expected ok but compile failed: {e}")
                        }
                    }
                }
                Expectation::Error(_) => {}
            }
        }
    }

    assert!(ran > 0, "no output/ok fixtures were found to run {subdir}");
}

#[test]
fn m4_fixtures() {
    run_codegen_fixtures("m4");
}

#[test]
fn m5_fixtures() {
    run_codegen_fixtures("m5");
}

#[test]
fn m8_fixtures() {
    run_codegen_fixtures("m8");
}

#[test]
fn m9_fixtures() {
    run_codegen_fixtures("m9");
}

#[test]
fn m10_fixtures() {
    run_codegen_fixtures("m10");
}

#[test]
fn m11_fixtures() {
    run_codegen_fixtures("m11");
}
