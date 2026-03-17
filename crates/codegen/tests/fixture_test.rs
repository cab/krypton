use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use krypton_codegen::emit::compile_modules;
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};
use krypton_typechecker::infer::infer_module;

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

fn run_program_with_resolver(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> String {
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let typed_modules = infer_module(&module, resolver).expect("type check should succeed");
    let classes = compile_modules(&typed_modules, "Test").expect("compile_modules should succeed");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = class_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
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

        let resolver =
            CompositeResolver::with_source_root(fixture_path.parent().unwrap().to_path_buf());

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Output(expected) => {
                    let actual = run_program_with_resolver(&fixture.source, &resolver);
                    assert_eq!(
                        actual, *expected,
                        "fixture {name}: expected output {expected:?} but got {actual:?}"
                    );
                    ran += 1;
                }
                Expectation::Ok => {
                    let (module, errors) = parse(&fixture.source);
                    if !errors.is_empty() {
                        panic!("fixture {name}: expected ok but parse errors: {errors:?}");
                    }
                    let typed_modules = match infer_module(&module, &resolver) {
                        Ok(tm) => tm,
                        Err(e) => panic!("fixture {name}: expected ok but typecheck failed: {e}"),
                    };
                    match compile_modules(&typed_modules, "Test") {
                        Ok(_) | Err(krypton_codegen::emit::CodegenError::NoMainFunction) => {
                            ran += 1;
                        }
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

#[test]
fn m11_module_fixtures() {
    run_codegen_fixtures("m11/modules");
}

#[test]
fn m18_fixtures() {
    run_codegen_fixtures("m18");
}

#[test]
fn m18_module_fixtures() {
    run_codegen_fixtures("m18/modules");
}

#[test]
fn m19_fixtures() {
    run_codegen_fixtures("m19");
}

#[test]
fn m6_fixtures() {
    run_codegen_fixtures("m6");
}

#[test]
fn m7_fixtures() {
    run_codegen_fixtures("m7");
}

#[test]
fn a_fixtures() {
    run_codegen_fixtures("a");
}

#[test]
fn m20_fixtures() {
    run_codegen_fixtures("m20");
}
