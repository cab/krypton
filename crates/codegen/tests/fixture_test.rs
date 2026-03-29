use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use krypton_codegen::emit::compile_modules;
use krypton_diagnostics::{DiagnosticRenderer, PlainTextRenderer};
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::diagnostics::{lower_infer_error, lower_infer_errors};
use krypton_typechecker::infer::infer_module;
use rstest::rstest;

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

/// Compile and run a fixture, returning the raw process output.
fn run_program_raw(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
    fixture_name: &str,
) -> std::process::Output {
    let (module, errors) = parse(source);
    assert!(
        errors.is_empty(),
        "fixture {fixture_name}: parse errors: {errors:?}"
    );

    let typed_modules =
        infer_module(&module, resolver, "test".to_string()).unwrap_or_else(|errors| {
            let (diags, srcs) = lower_infer_errors(fixture_name, source, &errors);
            let rendered: String = diags
                .iter()
                .map(|d| PlainTextRenderer.render(d, &srcs))
                .collect();
            panic!("fixture {fixture_name}: type check failed:\n{rendered}");
        });
    let classes = compile_modules(&typed_modules, "Kr$Test")
        .unwrap_or_else(|e| panic!("fixture {fixture_name}: compile failed: {e}"));

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
    Command::new("java")
        .arg("-cp")
        .arg(&classpath)
        .arg("Kr$Test")
        .output()
        .expect("java command should run")
}

fn run_program_with_resolver(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
    fixture_name: &str,
) -> String {
    let output = run_program_raw(source, resolver, fixture_name);
    assert!(
        output.status.success(),
        "fixture {fixture_name}: java exited with {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

const SKIP_DIRS: &[&str] = &["parser", "bench", "smoke", "modules", "inspect"];

fn should_skip(path: &PathBuf) -> bool {
    path.components().any(|c| {
        SKIP_DIRS
            .iter()
            .any(|d| c.as_os_str() == std::ffi::OsStr::new(d))
    })
}

#[rstest]
fn codegen_fixture(
    #[files("tests/fixtures/**/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    if should_skip(&path) {
        return;
    }

    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() {
        return;
    }

    let name = path.file_stem().unwrap().to_string_lossy().to_string();
    let resolver = CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    let has_panic = fixture
        .expectations
        .iter()
        .any(|e| matches!(e, Expectation::Panic(_)));

    if has_panic {
        // Run once, check panic + output expectations against the raw result
        let output = run_program_raw(&fixture.source, &resolver, &name);
        let stdout = String::from_utf8_lossy(&output.stdout).trim().to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        assert!(
            !output.status.success(),
            "fixture {name}: expected panic but program exited successfully"
        );

        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Panic(Some(msg)) => {
                    assert!(
                        stderr.contains(msg.as_str()),
                        "fixture {name}: expected panic message {msg:?} in stderr, got:\n{stderr}"
                    );
                }
                Expectation::Panic(None) => {} // already checked non-zero exit
                Expectation::Output(expected) => {
                    assert_eq!(
                        stdout, *expected,
                        "fixture {name}: output mismatch (panic fixture)"
                    );
                }
                _ => {}
            }
        }
    } else {
        for expectation in &fixture.expectations {
            match expectation {
                Expectation::Output(expected) => {
                    let actual = run_program_with_resolver(&fixture.source, &resolver, &name);
                    assert_eq!(actual, *expected, "fixture {name}: output mismatch");
                }
                Expectation::Ok => {
                    let (module, errors) = parse(&fixture.source);
                    assert!(
                        errors.is_empty(),
                        "fixture {name}: expected ok but parse errors: {errors:?}"
                    );
                    let typed_modules = infer_module(&module, &resolver, "test".to_string())
                        .unwrap_or_else(|errors| {
                            let (diags, srcs) = lower_infer_errors(&name, &fixture.source, &errors);
                            let rendered: String = diags
                                .iter()
                                .map(|d| PlainTextRenderer.render(d, &srcs))
                                .collect();
                            panic!("fixture {name}: expected ok but typecheck failed:\n{rendered}");
                        });
                    match compile_modules(&typed_modules, "Kr$Test") {
                        Ok(_)
                        | Err(krypton_codegen::emit::CodegenError {
                            kind: krypton_codegen::emit::CodegenErrorKind::NoMainFunction,
                            ..
                        }) => {}
                        Err(e) => panic!("fixture {name}: expected ok but compile failed: {e}"),
                    }
                }
                Expectation::Error(_) | Expectation::Panic(_) => {}
            }
        }
    }
}

#[rstest]
fn codegen_module(
    #[files("tests/fixtures/modules/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() {
        return;
    }

    let name = path.file_stem().unwrap().to_string_lossy().to_string();
    let resolver = CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    for expectation in &fixture.expectations {
        match expectation {
            Expectation::Output(expected) => {
                let actual = run_program_with_resolver(&fixture.source, &resolver, &name);
                assert_eq!(actual, *expected, "fixture {name}: output mismatch");
            }
            Expectation::Ok => {
                let (module, errors) = parse(&fixture.source);
                assert!(
                    errors.is_empty(),
                    "fixture {name}: expected ok but parse errors: {errors:?}"
                );
                let typed_modules = infer_module(&module, &resolver, "test".to_string())
                    .unwrap_or_else(|errors| {
                        let (diags, srcs) = lower_infer_errors(&name, &fixture.source, &errors);
                        let rendered: String = diags
                            .iter()
                            .map(|d| PlainTextRenderer.render(d, &srcs))
                            .collect();
                        panic!("fixture {name}: expected ok but typecheck failed:\n{rendered}");
                    });
                match compile_modules(&typed_modules, "Kr$Test") {
                    Ok(_)
                    | Err(krypton_codegen::emit::CodegenError {
                        kind: krypton_codegen::emit::CodegenErrorKind::NoMainFunction,
                        ..
                    }) => {}
                    Err(e) => panic!("fixture {name}: expected ok but compile failed: {e}"),
                }
            }
            Expectation::Error(_) | Expectation::Panic(_) => {}
        }
    }
}
