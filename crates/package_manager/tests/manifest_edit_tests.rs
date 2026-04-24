use std::path::{Path, PathBuf};

use krypton_package_manager::{AddSource, GitRef, Manifest, ManifestEditError, ManifestEditor};

fn editor(src: &str) -> ManifestEditor {
    ManifestEditor::from_str_with_path(src, Path::new("krypton.toml"))
        .expect("manifest should parse")
}

const BASE: &str = r#"[package]
name = "clementine/app"
version = "0.1.0"

[dependencies]
"#;

#[test]
fn add_git_dep_with_tag() {
    let mut ed = editor(BASE);
    let key = ed
        .add_dependency(
            "clementine/foo",
            AddSource::Git {
                url: "https://example.invalid/clementine/foo".into(),
                git_ref: GitRef::Tag("v0.1.0".into()),
            },
            None,
        )
        .expect("add");
    assert_eq!(key, "foo");
    let s = ed.render();
    assert!(
        s.contains(r#"foo = { package = "clementine/foo", git = "https://example.invalid/clementine/foo", tag = "v0.1.0" }"#),
        "rendered:\n{s}"
    );
}

#[test]
fn add_git_dep_with_branch() {
    let mut ed = editor(BASE);
    ed.add_dependency(
        "clementine/foo",
        AddSource::Git {
            url: "https://example.invalid/clementine/foo".into(),
            git_ref: GitRef::Branch("main".into()),
        },
        None,
    )
    .expect("add");
    let s = ed.render();
    assert!(s.contains(r#"branch = "main""#), "rendered:\n{s}");
    assert!(!s.contains("tag = "));
    assert!(!s.contains("rev = "));
}

#[test]
fn add_git_dep_with_rev() {
    let mut ed = editor(BASE);
    ed.add_dependency(
        "clementine/foo",
        AddSource::Git {
            url: "https://example.invalid/clementine/foo".into(),
            git_ref: GitRef::Rev("abc123".into()),
        },
        None,
    )
    .expect("add");
    let s = ed.render();
    assert!(s.contains(r#"rev = "abc123""#), "rendered:\n{s}");
}

#[test]
fn add_path_dep() {
    let mut ed = editor(BASE);
    ed.add_dependency(
        "clementine/shared",
        AddSource::Path {
            path: PathBuf::from("../shared"),
        },
        None,
    )
    .expect("add");
    let s = ed.render();
    assert!(
        s.contains(r#"shared = { package = "clementine/shared", path = "../shared" }"#),
        "rendered:\n{s}"
    );
    // Path deps without a version requirement must not emit a `version`
    // key inside the inline table.
    assert!(
        !s.contains(r#"path = "../shared", version"#),
        "rendered:\n{s}"
    );
}

#[test]
fn add_registry_version_dep() {
    let mut ed = editor(BASE);
    ed.add_dependency(
        "clementine/http",
        AddSource::Registry {
            version: "0.3.0".into(),
        },
        None,
    )
    .expect("add");
    let s = ed.render();
    assert!(
        s.contains(r#"http = { package = "clementine/http", version = "0.3.0" }"#),
        "rendered:\n{s}"
    );
}

#[test]
fn add_default_local_root_from_canonical_leaf() {
    let mut ed = editor(BASE);
    let key = ed
        .add_dependency(
            "clementine/json",
            AddSource::Registry {
                version: "0.1.0".into(),
            },
            None,
        )
        .expect("add");
    assert_eq!(key, "json");
}

#[test]
fn add_hyphenated_leaf_normalizes_to_underscore() {
    let mut ed = editor(BASE);
    let key = ed
        .add_dependency(
            "clementine/http-client",
            AddSource::Registry {
                version: "0.1.0".into(),
            },
            None,
        )
        .expect("add");
    assert_eq!(key, "http_client");
    let s = ed.render();
    assert!(
        s.contains(r#"http_client = { package = "clementine/http-client""#),
        "rendered:\n{s}"
    );
}

#[test]
fn add_explicit_as_overrides_default() {
    let mut ed = editor(BASE);
    let key = ed
        .add_dependency(
            "clementine/json",
            AddSource::Registry {
                version: "0.1.0".into(),
            },
            Some("my_json"),
        )
        .expect("add");
    assert_eq!(key, "my_json");
    let s = ed.render();
    assert!(s.contains(r#"my_json = { package = "clementine/json""#));
    // The default `json` key must not have been inserted alongside it.
    assert!(!s.contains("\njson = "), "rendered:\n{s}");
}

#[test]
fn add_errors_on_duplicate_local_root() {
    let mut ed = editor(BASE);
    ed.add_dependency(
        "clementine/json",
        AddSource::Registry {
            version: "0.1.0".into(),
        },
        None,
    )
    .expect("first add");
    let err = ed
        .add_dependency(
            "clementine/json",
            AddSource::Registry {
                version: "0.2.0".into(),
            },
            None,
        )
        .expect_err("second add must fail");
    assert!(
        matches!(
            &err,
            ManifestEditError::DuplicateDependency { local_root } if local_root == "json"
        ),
        "unexpected error: {err:?}"
    );
    assert!(
        err.to_string().contains("dependency 'json' already exists"),
        "display: {err}"
    );
}

#[test]
fn add_preserves_surrounding_comments_and_whitespace() {
    let src = r#"# leading comment
[package]
name = "clementine/app"
version = "0.1.0"
# inline comment after package
description = "a thing"

[dependencies]
shared = { package = "clementine/shared", path = "../shared" }

[jvm]
maven = ["org.postgresql:postgresql:42.7.1"]
"#;
    let mut ed = editor(src);
    ed.add_dependency(
        "clementine/json",
        AddSource::Registry {
            version: "0.1.0".into(),
        },
        None,
    )
    .expect("add");
    let s = ed.render();
    assert!(s.starts_with("# leading comment\n"), "rendered:\n{s}");
    assert!(
        s.contains("# inline comment after package\n"),
        "rendered:\n{s}"
    );
    assert!(s.contains("\n\n[jvm]\n"), "rendered:\n{s}");
    // Original dep must still be present.
    assert!(
        s.contains(r#"shared = { package = "clementine/shared", path = "../shared" }"#),
        "rendered:\n{s}"
    );
    // New dep rendered.
    assert!(
        s.contains(r#"json = { package = "clementine/json", version = "0.1.0" }"#),
        "rendered:\n{s}"
    );
    // Result must still parse as a valid manifest.
    Manifest::from_str(&s).expect("edited manifest must parse");
}

#[test]
fn add_creates_dependencies_section_if_missing() {
    let src = r#"[package]
name = "clementine/app"
version = "0.1.0"
"#;
    let mut ed = editor(src);
    ed.add_dependency(
        "clementine/json",
        AddSource::Registry {
            version: "0.1.0".into(),
        },
        None,
    )
    .expect("add");
    let s = ed.render();
    assert!(s.contains("[dependencies]\n"), "rendered:\n{s}");
    assert!(
        s.contains(r#"json = { package = "clementine/json", version = "0.1.0" }"#),
        "rendered:\n{s}"
    );
    Manifest::from_str(&s).expect("edited manifest must parse");
}

#[test]
fn remove_existing_dep_deletes_entry() {
    let src = r#"[package]
name = "clementine/app"
version = "0.1.0"

# deps live here
[dependencies]
json = { package = "clementine/json", version = "0.1.0" }
shared = { package = "clementine/shared", path = "../shared" }
"#;
    let mut ed = editor(src);
    ed.remove_dependency("json").expect("remove");
    let s = ed.render();
    assert!(!s.contains("json ="), "rendered:\n{s}");
    assert!(
        s.contains(r#"shared = { package = "clementine/shared", path = "../shared" }"#),
        "rendered:\n{s}"
    );
    assert!(s.contains("# deps live here\n"), "rendered:\n{s}");
    Manifest::from_str(&s).expect("edited manifest must parse");
}

#[test]
fn remove_nonexistent_dep_errors() {
    let src = r#"[package]
name = "clementine/app"
version = "0.1.0"

[dependencies]
shared = { package = "clementine/shared", path = "../shared" }
"#;
    let mut ed = editor(src);
    let err = ed.remove_dependency("json").expect_err("remove must fail");
    assert!(
        matches!(
            &err,
            ManifestEditError::DependencyNotFound { local_root } if local_root == "json"
        ),
        "unexpected error: {err:?}"
    );
    assert!(
        err.to_string()
            .contains("dependency 'json' not found in [dependencies]"),
        "display: {err}"
    );
}
