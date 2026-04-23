use std::path::PathBuf;

use krypton_modules::module_resolver::{
    CompositeResolver, DependencyResolver, ModuleResolver, ResolverError,
};
use tempfile::TempDir;

/// Create a fake dependency src directory with the given files, returning the
/// tempdir handle (kept alive for the test) and the path to the `src/` dir.
fn make_dep_src(files: &[(&str, &str)]) -> (TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = dir.path().join("src");
    std::fs::create_dir_all(&src).expect("mkdir src");
    for (rel, contents) in files {
        let path = src.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("mkdir parent");
        }
        std::fs::write(&path, contents).expect("write file");
    }
    let src_path = src.clone();
    (dir, src_path)
}

fn make_project_src(files: &[(&str, &str)]) -> (TempDir, PathBuf) {
    let dir = tempfile::tempdir().expect("tempdir");
    let src = dir.path().join("src");
    std::fs::create_dir_all(&src).expect("mkdir src");
    for (rel, contents) in files {
        let path = src.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("mkdir parent");
        }
        std::fs::write(&path, contents).expect("write file");
    }
    let src_path = src.clone();
    (dir, src_path)
}

#[test]
fn dep_root_alone_resolves_to_lib_kr() {
    let (_http_dir, http_src) = make_dep_src(&[("lib.kr", "pub fun http_root() -> Int = 1")]);
    let (_json_dir, json_src) = make_dep_src(&[("lib.kr", "pub fun json_root() -> Int = 2")]);

    let resolver = DependencyResolver::new(vec![
        ("http".to_string(), http_src),
        ("json".to_string(), json_src),
    ]);

    assert_eq!(
        resolver.resolve("http").as_deref(),
        Some("pub fun http_root() -> Int = 1")
    );
    assert_eq!(
        resolver.resolve("json").as_deref(),
        Some("pub fun json_root() -> Int = 2")
    );
}

#[test]
fn dep_submodule_resolves_relative_to_src() {
    let (_http_dir, http_src) = make_dep_src(&[
        ("lib.kr", "pub fun root() -> Int = 0"),
        ("client.kr", "pub fun get() -> Int = 42"),
    ]);
    let resolver = DependencyResolver::new(vec![("http".to_string(), http_src)]);

    assert_eq!(
        resolver.resolve("http/client").as_deref(),
        Some("pub fun get() -> Int = 42")
    );
}

#[test]
fn dep_nested_submodule_resolves() {
    let (_http_dir, http_src) = make_dep_src(&[
        ("lib.kr", "pub fun root() -> Int = 0"),
        ("client/response.kr", "pub fun parse() -> Int = 7"),
    ]);
    let resolver = DependencyResolver::new(vec![("http".to_string(), http_src)]);

    assert_eq!(
        resolver.resolve("http/client/response").as_deref(),
        Some("pub fun parse() -> Int = 7")
    );
}

#[test]
fn resolution_order_stdlib_wins_over_dep() {
    // A dep root named `core` points at a dir that contains a bogus `option.kr`
    // — but since stdlib is consulted first, resolving `core/option` should
    // return the embedded stdlib source, not the bogus file.
    let (_bogus_dir, bogus_src) =
        make_dep_src(&[("option.kr", "this is not valid krypton source")]);

    let resolver =
        CompositeResolver::new(None, vec![("core".to_string(), bogus_src)]).expect("construct");
    let got = resolver.resolve("core/option").expect("resolves");
    assert!(
        !got.contains("this is not valid krypton source"),
        "expected stdlib source, got bogus dep file: {got}"
    );
    // stdlib's core/option should mention `Option` somewhere.
    assert!(
        got.contains("Option"),
        "expected stdlib core/option to mention 'Option'"
    );
}

#[test]
fn resolution_order_project_wins_over_dep_when_no_conflict() {
    // Project src/ contains mylib.kr; a dep root `other` is registered pointing
    // at a different tempdir. Resolving `mylib` finds the project source;
    // resolving `other` finds the dep's lib.kr.
    let (_proj_dir, proj_src) = make_project_src(&[("mylib.kr", "pub fun mine() -> Int = 1")]);
    let (_other_dir, other_src) = make_dep_src(&[("lib.kr", "pub fun theirs() -> Int = 2")]);

    let resolver = CompositeResolver::new(Some(proj_src), vec![("other".to_string(), other_src)])
        .expect("construct");

    assert_eq!(
        resolver.resolve("mylib").as_deref(),
        Some("pub fun mine() -> Int = 1")
    );
    assert_eq!(
        resolver.resolve("other").as_deref(),
        Some("pub fun theirs() -> Int = 2")
    );
}

#[test]
fn unknown_module_returns_none() {
    let resolver = CompositeResolver::new(None, vec![]).expect("construct");
    assert!(resolver.resolve("no/such/module").is_none());
}

#[test]
fn import_root_conflict_with_local_file() {
    let (_proj_dir, proj_src) = make_project_src(&[("http.kr", "pub fun local() -> Int = 1")]);
    let (_dep_dir, dep_src) = make_dep_src(&[("lib.kr", "pub fun dep() -> Int = 2")]);

    let result =
        CompositeResolver::new(Some(proj_src.clone()), vec![("http".to_string(), dep_src)]);
    match result {
        Err(ResolverError::ImportRootConflict { name, local_path }) => {
            assert_eq!(name, "http");
            assert_eq!(local_path, proj_src.join("http.kr"));
        }
        Ok(_) => panic!("expected construction error"),
    }
}

#[test]
fn import_root_conflict_with_local_dir() {
    let (_proj_dir, proj_src) =
        make_project_src(&[("http/client.kr", "pub fun local() -> Int = 1")]);
    let (_dep_dir, dep_src) = make_dep_src(&[("lib.kr", "pub fun dep() -> Int = 2")]);

    let result =
        CompositeResolver::new(Some(proj_src.clone()), vec![("http".to_string(), dep_src)]);
    match result {
        Err(ResolverError::ImportRootConflict { name, local_path }) => {
            assert_eq!(name, "http");
            assert_eq!(local_path, proj_src.join("http"));
        }
        Ok(_) => panic!("expected construction error"),
    }
}

#[test]
fn two_external_source_roots() {
    let (_http_dir, http_src) = make_dep_src(&[
        ("lib.kr", "pub fun http_root() -> Int = 1"),
        ("client.kr", "pub fun get() -> Int = 42"),
    ]);
    let (_json_dir, json_src) = make_dep_src(&[
        ("lib.kr", "pub fun json_root() -> Int = 2"),
        ("parser.kr", "pub fun parse() -> Int = 7"),
    ]);

    let resolver = CompositeResolver::new(
        None,
        vec![
            ("http".to_string(), http_src),
            ("json".to_string(), json_src),
        ],
    )
    .expect("construct");

    assert_eq!(
        resolver.resolve("http").as_deref(),
        Some("pub fun http_root() -> Int = 1")
    );
    assert_eq!(
        resolver.resolve("http/client").as_deref(),
        Some("pub fun get() -> Int = 42")
    );
    assert_eq!(
        resolver.resolve("json").as_deref(),
        Some("pub fun json_root() -> Int = 2")
    );
    assert_eq!(
        resolver.resolve("json/parser").as_deref(),
        Some("pub fun parse() -> Int = 7")
    );
}

#[test]
fn first_match_wins_within_deps() {
    // The data type allows duplicate names in the Vec. TOML-driven entry points
    // deduplicate, but documenting + testing that the resolver is total (no
    // panic) and first-entry-wins is deliberate.
    let (_first_dir, first_src) = make_dep_src(&[("lib.kr", "pub fun first() -> Int = 1")]);
    let (_second_dir, second_src) = make_dep_src(&[("lib.kr", "pub fun second() -> Int = 2")]);

    let resolver = DependencyResolver::new(vec![
        ("dup".to_string(), first_src),
        ("dup".to_string(), second_src),
    ]);

    assert_eq!(
        resolver.resolve("dup").as_deref(),
        Some("pub fun first() -> Int = 1")
    );
}
