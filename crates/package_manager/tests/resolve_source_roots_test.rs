use std::path::Path;

use krypton_package_manager::{CacheDir, Manifest, resolve};
use tempfile::tempdir;

mod common;
use common::*;

fn load_root(dir: &Path) -> Manifest {
    Manifest::from_path(dir.join("krypton.toml")).expect("root manifest parses")
}

fn manifest_with(name: &str, version: &str, deps: &[(&str, &str)]) -> String {
    let mut out = format!("[package]\nname = \"{name}\"\nversion = \"{version}\"\n");
    if !deps.is_empty() {
        out.push_str("\n[dependencies]\n");
        for (key, body) in deps {
            out.push_str(key);
            out.push_str(" = ");
            out.push_str(body);
            out.push('\n');
        }
    }
    out
}

fn write_manifest(dir: &Path, name: &str, version: &str, deps: &[(&str, &str)]) {
    std::fs::create_dir_all(dir).expect("mkdir");
    std::fs::write(dir.join("krypton.toml"), manifest_with(name, version, deps))
        .expect("write manifest");
}

#[test]
fn source_roots_maps_dep_key_to_src_dir() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let http_dir = work.path().join("http");
    let json_dir = work.path().join("json");

    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "http",
                &format!(
                    "{{ package = \"clementine/http\", path = \"{}\" }}",
                    http_dir.display()
                ),
            ),
            (
                "json",
                &format!(
                    "{{ package = \"clementine/json\", path = \"{}\" }}",
                    json_dir.display()
                ),
            ),
        ],
    );
    write_manifest(&http_dir, "clementine/http", "0.1.0", &[]);
    write_manifest(&json_dir, "clementine/json", "0.1.0", &[]);

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest.clone(), &cache).expect("resolve");
    let roots = graph.source_roots(&root_manifest);

    assert_eq!(roots.len(), 2);
    // Each local key maps to the package's canonicalized source_path + /src.
    let http = roots.iter().find(|(k, _)| k == "http").expect("http entry");
    let json = roots.iter().find(|(k, _)| k == "json").expect("json entry");
    assert!(
        http.1.ends_with("src"),
        "http source_root ends with src: {}",
        http.1.display()
    );
    assert!(
        json.1.ends_with("src"),
        "json source_root ends with src: {}",
        json.1.display()
    );
    // The parent of the `src` segment should point at the resolved source_path.
    let http_pkg = graph
        .iter()
        .find(|(c, _)| c.as_str() == "clementine/http")
        .map(|(_, p)| p)
        .unwrap();
    let json_pkg = graph
        .iter()
        .find(|(c, _)| c.as_str() == "clementine/json")
        .map(|(_, p)| p)
        .unwrap();
    assert_eq!(http.1, http_pkg.source_path.join("src"));
    assert_eq!(json.1, json_pkg.source_path.join("src"));
}

#[test]
fn source_roots_preserves_manifest_order() {
    // BTreeMap iterates keys alphabetically. Register deps in reverse-alpha
    // order in the manifest source to confirm the helper reflects BTreeMap
    // ordering (not source-file ordering).
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let zz_dir = work.path().join("zz");
    let aa_dir = work.path().join("aa");

    // Note: source order is zz then aa; BTreeMap will yield aa first.
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "zz",
                &format!(
                    "{{ package = \"clementine/zz\", path = \"{}\" }}",
                    zz_dir.display()
                ),
            ),
            (
                "aa",
                &format!(
                    "{{ package = \"clementine/aa\", path = \"{}\" }}",
                    aa_dir.display()
                ),
            ),
        ],
    );
    write_manifest(&zz_dir, "clementine/zz", "0.1.0", &[]);
    write_manifest(&aa_dir, "clementine/aa", "0.1.0", &[]);

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest.clone(), &cache).expect("resolve");
    let roots = graph.source_roots(&root_manifest);

    let keys: Vec<&str> = roots.iter().map(|(k, _)| k.as_str()).collect();
    assert_eq!(keys, vec!["aa", "zz"]);
}

#[test]
fn transitive_hints_excludes_direct_deps() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let http_dir = work.path().join("http");
    let utils_dir = work.path().join("utils");

    // root depends on http; http depends on utils; utils has no deps.
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "http",
            &format!(
                "{{ package = \"clementine/http\", path = \"{}\" }}",
                http_dir.display()
            ),
        )],
    );
    write_manifest(
        &http_dir,
        "clementine/http",
        "0.1.0",
        &[(
            "utils",
            &format!(
                "{{ package = \"clementine/utils\", path = \"{}\" }}",
                utils_dir.display()
            ),
        )],
    );
    write_manifest(&utils_dir, "clementine/utils", "0.1.0", &[]);

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest.clone(), &cache).expect("resolve");
    let hints = graph.transitive_hints(&root_manifest);

    // http is a direct dep; should be excluded. utils is transitive; should appear.
    assert_eq!(hints.len(), 1, "hints should contain only transitive deps");
    let (local, canonical) = &hints[0];
    assert_eq!(local, "utils");
    assert_eq!(canonical, "clementine/utils");
}

#[test]
fn transitive_hints_normalizes_hyphens() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let mid_dir = work.path().join("mid");
    let hyph_dir = work.path().join("hyph");

    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "mid",
            &format!(
                "{{ package = \"clementine/mid\", path = \"{}\" }}",
                mid_dir.display()
            ),
        )],
    );
    write_manifest(
        &mid_dir,
        "clementine/mid",
        "0.1.0",
        &[(
            "hc",
            &format!(
                "{{ package = \"clementine/http-client\", path = \"{}\" }}",
                hyph_dir.display()
            ),
        )],
    );
    write_manifest(&hyph_dir, "clementine/http-client", "0.1.0", &[]);

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest.clone(), &cache).expect("resolve");
    let hints = graph.transitive_hints(&root_manifest);

    let hyph = hints
        .iter()
        .find(|(_, c)| c == "clementine/http-client")
        .expect("http-client appears as transitive dep");
    assert_eq!(
        hyph.0, "http_client",
        "package-name leaf with '-' normalized to '_'"
    );
}

#[test]
fn transitive_hints_empty_when_flat_deps() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let a_dir = work.path().join("a");
    let b_dir = work.path().join("b");

    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "a",
                &format!(
                    "{{ package = \"clementine/a\", path = \"{}\" }}",
                    a_dir.display()
                ),
            ),
            (
                "b",
                &format!(
                    "{{ package = \"clementine/b\", path = \"{}\" }}",
                    b_dir.display()
                ),
            ),
        ],
    );
    write_manifest(&a_dir, "clementine/a", "0.1.0", &[]);
    write_manifest(&b_dir, "clementine/b", "0.1.0", &[]);

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest.clone(), &cache).expect("resolve");
    let hints = graph.transitive_hints(&root_manifest);
    assert!(hints.is_empty(), "no transitive deps → empty hints");
}
