use std::path::PathBuf;

use krypton_ir::lower::lower_module;
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::infer::infer_module;
use rstest::rstest;

const SKIP_DIRS: &[&str] = &["parser", "bench", "smoke", "inspect"];

fn should_skip(path: &PathBuf) -> bool {
    path.components().any(|c| {
        SKIP_DIRS
            .iter()
            .any(|d| c.as_os_str() == std::ffi::OsStr::new(d))
    })
}

/// Returns true if the fixture expects a type/parse error (not a successful compilation).
fn expects_error(expectations: &[Expectation]) -> bool {
    expectations
        .iter()
        .any(|e| matches!(e, Expectation::Error(_)))
}

#[rstest]
fn ir_lower(
    #[files("tests/fixtures/**/*.kr")]
    #[base_dir = "../.."]
    path: PathBuf,
) {
    if should_skip(&path) {
        return;
    }

    let fixture = load_fixture(&path);
    if fixture.expectations.is_empty() || expects_error(&fixture.expectations) {
        return;
    }

    let stem = path.file_stem().unwrap().to_string_lossy().to_string();
    let parent = path
        .parent()
        .and_then(|p| p.file_name())
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_default();
    let name = if parent.is_empty() || parent == "fixtures" {
        stem.clone()
    } else {
        format!("{parent}__{stem}")
    };
    let resolver = CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    let (module, errors) = parse(&fixture.source);
    assert!(
        errors.is_empty(),
        "fixture {name}: parse errors: {errors:?}"
    );

    let typed_modules = infer_module(&module, &resolver)
        .unwrap_or_else(|e| panic!("fixture {name}: typecheck failed: {e:?}"));

    let ir_module = lower_module(&typed_modules[0], &name)
        .unwrap_or_else(|e| panic!("fixture {name}: IR lowering failed: {e:?}"));

    insta::assert_snapshot!(name, ir_module.to_string());
}
