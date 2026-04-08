use std::path::{Path, PathBuf};

use krypton_ir::lint::LintPass;
use krypton_ir::lower::lower_module;
use krypton_ir::pass::IrPass;
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_test_harness::{load_fixture, Expectation};
use krypton_typechecker::infer::infer_module;
use krypton_typechecker::link_context::LinkContext;
use krypton_typechecker::module_interface::ModulePath;
use rstest::rstest;

const SKIP_DIRS: &[&str] = &["parser", "bench", "smoke", "inspect"];

fn should_skip(path: &Path) -> bool {
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

    let (typed_modules, interfaces) = infer_module(&module, &resolver, name.clone(), krypton_parser::ast::CompileTarget::Jvm)
        .unwrap_or_else(|e| panic!("fixture {name}: typecheck failed: {e:?}"));

    let link_ctx = LinkContext::build(interfaces);
    let view = link_ctx
        .view_for(&ModulePath::new(&typed_modules[0].module_path))
        .unwrap_or_else(|| panic!("fixture {name}: no LinkContext view for root module"));
    let ir_module = lower_module(&typed_modules[0], &name, &view)
        .unwrap_or_else(|e| panic!("fixture {name}: IR lowering failed: {e:?}"));

    insta::assert_snapshot!(name, ir_module.to_string());
}

#[rstest]
fn ir_link(
    #[files("tests/fixtures/modules/*.kr")]
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
    let name = format!("link__{stem}");
    let resolver = CompositeResolver::with_source_root(path.parent().unwrap().to_path_buf());

    let (module, errors) = parse(&fixture.source);
    assert!(
        errors.is_empty(),
        "fixture {name}: parse errors: {errors:?}"
    );

    let (typed_modules, interfaces) = infer_module(&module, &resolver, stem.clone(), krypton_parser::ast::CompileTarget::Jvm)
        .unwrap_or_else(|e| panic!("fixture {name}: typecheck failed: {e:?}"));

    let link_ctx = LinkContext::build(interfaces);
    let mut output = String::new();
    for (i, typed) in typed_modules.iter().enumerate() {
        let mod_name = if i == 0 {
            stem.clone()
        } else {
            typed.module_path.clone()
        };
        let view = link_ctx
            .view_for(&ModulePath::new(&typed.module_path))
            .unwrap_or_else(|| {
                panic!("fixture {name}: no LinkContext view for module {mod_name}")
            });
        let ir_module = lower_module(typed, &mod_name, &view).unwrap_or_else(|e| {
            panic!("fixture {name}: IR lowering failed for module {i} ({mod_name}): {e}")
        });
        let ir_module = LintPass.run(ir_module).unwrap_or_else(|e| {
            panic!("fixture {name}: IR lint failed for module {mod_name}: {e}")
        });
        output.push_str(&ir_module.to_string());
    }

    insta::assert_snapshot!(name, output);
}

#[test]
fn nullary_constructors_have_no_fn_id() {
    let source = r#"
type Opt[a] = Some(a) | None
fun main() = {
    let x = None
    let _ = match x { Some(_) => 0, None => 0 }
    0
}
"#;
    let name = "nullary_ctor_no_fn_id";
    let resolver = CompositeResolver::stdlib_only();

    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let (typed_modules, interfaces) = infer_module(&module, &resolver, name.to_string(), krypton_parser::ast::CompileTarget::Jvm)
        .unwrap_or_else(|e| panic!("typecheck failed: {e:?}"));

    let link_ctx = LinkContext::build(interfaces);
    let view = link_ctx
        .view_for(&ModulePath::new(&typed_modules[0].module_path))
        .unwrap_or_else(|| panic!("no LinkContext view"));
    let ir_module = lower_module(&typed_modules[0], name, &view)
        .unwrap_or_else(|e| panic!("IR lowering failed: {e:?}"));

    let has_none = ir_module
        .fn_identities
        .values()
        .any(|fi| fi.name() == "None");
    assert!(!has_none, "fn_identities should not contain nullary constructor 'None'");

    let has_main = ir_module
        .fn_identities
        .values()
        .any(|fi| fi.name() == "main");
    assert!(has_main, "fn_identities should contain 'main'");
}
