use std::path::{Path, PathBuf};

use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::infer;
use rstest::rstest;

fn infer_module_snapshot(source: &str) -> Result<String, Vec<String>> {
    infer_module_snapshot_with_resolver(source, &CompositeResolver::stdlib_only())
}

fn infer_module_snapshot_at(source: &str, fixture_dir: &Path) -> Result<String, Vec<String>> {
    infer_module_snapshot_with_resolver(
        source,
        &CompositeResolver::with_source_root(fixture_dir.to_path_buf()),
    )
}

fn infer_module_snapshot_with_resolver(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> Result<String, Vec<String>> {
    let (module, errors) = parse(source);
    if !errors.is_empty() {
        return Err(vec![errors[0].code.to_string()]);
    }
    match infer::infer_module(
        &module,
        resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    ) {
        Ok((modules, _)) => {
            let lines: Vec<String> = modules[0]
                .fn_types
                .iter()
                .map(|e| format!("{}: {}", e.name, e.scheme))
                .collect();
            Ok(lines.join("\n"))
        }
        Err(infer_errors) => {
            let codes: Vec<String> = infer_errors
                .iter()
                .map(|e| match e {
                    infer::InferError::TypeError { error, .. } => {
                        error.error.error_code().to_string()
                    }
                    infer::InferError::ModuleParseError { .. } => "E0506".to_string(),
                })
                .collect();
            Err(codes)
        }
    }
}

const SKIP_DIRS: &[&str] = &["parser", "bench", "smoke", "inspect"];

fn should_skip(path: &Path) -> bool {
    path.components().any(|c| {
        SKIP_DIRS
            .iter()
            .any(|d| c.as_os_str() == std::ffi::OsStr::new(d))
    })
}

#[rstest]
fn typecheck_fixture(
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
    let fixture_dir = path.parent().unwrap();

    let expected_errors: Vec<&str> = fixture
        .expectations
        .iter()
        .filter_map(|e| match e {
            Expectation::Error(code) => Some(code.as_str()),
            _ => None,
        })
        .collect();

    if expected_errors.is_empty() {
        // Expect success
        for expectation in &fixture.expectations {
            if let Expectation::Ok = expectation {
                let result = infer_module_snapshot_at(&fixture.source, fixture_dir);
                let snapshot = result.unwrap_or_else(|codes| {
                    panic!("fixture {name}: expected ok but got errors {codes:?}")
                });
                insta::assert_snapshot!(name.clone(), snapshot);
            }
        }
    } else {
        // Expect errors — check all expected codes appear in actual codes
        let result = infer_module_snapshot_at(&fixture.source, fixture_dir);
        match result {
            Ok(ty) => {
                panic!("fixture {name}: expected errors {expected_errors:?} but inferred: {ty}")
            }
            Err(actual_codes) => {
                let mut remaining = actual_codes.clone();
                for expected in &expected_errors {
                    let pos = remaining.iter().position(|c| c == expected);
                    assert!(
                        pos.is_some(),
                        "fixture {name}: expected error {expected} not found in actual errors {actual_codes:?}"
                    );
                    remaining.remove(pos.unwrap());
                }
                assert_eq!(
                    actual_codes.len(),
                    expected_errors.len(),
                    "fixture {name}: expected {expected_errors:?} but got {actual_codes:?}"
                );
            }
        }
    }
}

#[rstest]
fn typecheck_module(
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

    let expected_errors: Vec<&str> = fixture
        .expectations
        .iter()
        .filter_map(|e| match e {
            Expectation::Error(code) => Some(code.as_str()),
            _ => None,
        })
        .collect();

    if expected_errors.is_empty() {
        let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
        assert!(
            result.is_ok(),
            "fixture {name}: expected ok but got error {:?}",
            result.err()
        );
    } else {
        let result = infer_module_snapshot_with_resolver(&fixture.source, &resolver);
        match result {
            Ok(ty) => {
                panic!("fixture {name}: expected errors {expected_errors:?} but inferred: {ty}")
            }
            Err(actual_codes) => {
                let mut remaining = actual_codes.clone();
                for expected in &expected_errors {
                    let pos = remaining.iter().position(|c| c == expected);
                    assert!(
                        pos.is_some(),
                        "fixture {name}: expected error {expected} not found in actual errors {actual_codes:?}"
                    );
                    remaining.remove(pos.unwrap());
                }
                assert_eq!(
                    actual_codes.len(),
                    expected_errors.len(),
                    "fixture {name}: expected {expected_errors:?} but got {actual_codes:?}"
                );
            }
        }
    }
}

#[test]
fn importing_map_functions_does_not_expose_map_as_value() {
    let snapshot = infer_module_snapshot(
        r#"
            import core/map.{empty, size}
            fun main() = println(size(empty()))
        "#,
    )
    .expect("typecheck should succeed");

    assert!(
        !snapshot.lines().any(|line| line.starts_with("Map: ")),
        "Map should remain type-only, got:\n{snapshot}"
    );
}

#[test]
fn applicative_constraint_satisfies_functor_method_call() {
    // Superclass entailment: `where g: Applicative` should satisfy a Functor
    // method call on g, since Applicative declares Functor as a superclass.
    let snapshot = infer_module_snapshot(
        r#"
            import core/applicative.{Applicative}
            import core/functor.{map}
            fun lift_ap[g[_], a, b](ga: g[a], f: (a) -> b) -> g[b] where g: Applicative =
                map(ga, f)
        "#,
    )
    .expect("typecheck should succeed: g: Applicative implies g: Functor");
    assert!(
        snapshot.contains("lift_ap"),
        "expected lift_ap in inferred fn types, got:\n{snapshot}"
    );
}

#[test]
fn applicative_constraint_does_not_satisfy_unrelated_trait() {
    // Negative test: superclass entailment is single-direction.
    // `where g: Functor` does NOT satisfy a call needing g: Applicative.
    let result = infer_module_snapshot(
        r#"
            import core/applicative.{pure}
            import core/functor.{Functor}
            fun lift_pure[g[_], a](x: a) -> g[a] where g: Functor = pure(x)
        "#,
    );
    let codes = result.expect_err("expected E0312 for missing Applicative bound");
    assert!(codes.iter().any(|c| c == "E0312"), "got codes: {codes:?}");
}

#[test]
fn codec_constraint_satisfies_my_show_method_call() {
    // Multi-parameter superclass entailment: `where Codec[fmt, ty]` should
    // satisfy a MyShow method call on `ty`, since Codec declares MyShow as a
    // superclass at position 1.
    let snapshot = infer_module_snapshot(
        r#"
            trait MyShow[a] {
                fun my_show(x: a) -> String
            }
            trait Codec[fmt, ty] where ty: MyShow {
                fun encode(x: ty) -> fmt
            }
            fun describe[fmt, ty](x: ty, hint: fmt) -> String where Codec[fmt, ty] =
                my_show(x)
        "#,
    )
    .expect("typecheck should succeed: Codec[fmt, ty] implies MyShow[ty]");
    assert!(
        snapshot.contains("describe"),
        "expected describe in inferred fn types, got:\n{snapshot}"
    );
}
