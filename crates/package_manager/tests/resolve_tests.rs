use std::path::Path;
use std::time::{Duration, Instant};

use krypton_package_manager::{
    resolve, CacheDir, Manifest, ResolveError, SourceDescriptor, SourceType,
};
use semver::Version;
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

fn find<'a>(
    graph: &'a krypton_package_manager::ResolvedGraph,
    canonical: &str,
) -> &'a krypton_package_manager::ResolvedPackage {
    graph
        .iter()
        .find(|(c, _)| c.as_str() == canonical)
        .map(|(_, p)| p)
        .unwrap_or_else(|| panic!("canonical '{canonical}' not in resolved graph"))
}

#[test]
fn single_path_dep_resolves() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let b_dir = work.path().join("b");
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", path = \"{}\" }}",
                b_dir.display()
            ),
        )],
    );
    write_manifest(&b_dir, "clementine/b", "0.1.0", &[]);

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest, &cache).expect("resolve");
    assert_eq!(graph.len(), 1, "root excluded, one transitive dep");
    let b = find(&graph, "clementine/b");
    assert_eq!(b.version, Version::parse("0.1.0").unwrap());
    assert!(matches!(b.source_type, SourceType::Path { .. }));
    assert!(b.source_path.ends_with("b") || b.source_path.to_string_lossy().contains("/b"));
    assert!(b.source_path.is_absolute());
}

#[test]
fn single_git_dep_resolves() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let remote = work.path().join("remote-b");
    std::fs::create_dir_all(&remote).unwrap();
    let b_sha = make_repo(
        &remote,
        &[("krypton.toml", &manifest("clementine/b", "0.1.0"))],
    );
    add_tag(&remote, "v0.1.0");

    let root_dir = work.path().join("root");
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", git = \"{}\", tag = \"v0.1.0\" }}",
                remote.display()
            ),
        )],
    );

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest, &cache).expect("resolve");
    let b = find(&graph, "clementine/b");
    match &b.source_type {
        SourceType::Git { sha, .. } => assert_eq!(sha, &b_sha),
        other => panic!("expected Git source, got {other:?}"),
    }
    assert!(
        b.source_path.starts_with(cache.root()),
        "git source under cache"
    );
    assert_eq!(
        b.source_path,
        cache.package_source_dir("clementine", "b", &b_sha)
    );
}

#[test]
fn transitive_chain_path() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let b_dir = work.path().join("b");
    let c_dir = work.path().join("c");
    let d_dir = work.path().join("d");

    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", path = \"{}\" }}",
                b_dir.display()
            ),
        )],
    );
    write_manifest(
        &b_dir,
        "clementine/b",
        "0.2.0",
        &[(
            "c",
            &format!(
                "{{ package = \"clementine/c\", path = \"{}\" }}",
                c_dir.display()
            ),
        )],
    );
    write_manifest(
        &c_dir,
        "clementine/c",
        "0.3.0",
        &[(
            "d",
            &format!(
                "{{ package = \"clementine/d\", path = \"{}\" }}",
                d_dir.display()
            ),
        )],
    );
    write_manifest(&d_dir, "clementine/d", "0.4.0", &[]);

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest, &cache).expect("resolve");
    assert_eq!(graph.len(), 3, "chain of 3 deps, root excluded");
    assert_eq!(find(&graph, "clementine/b").version.to_string(), "0.2.0");
    assert_eq!(find(&graph, "clementine/c").version.to_string(), "0.3.0");
    assert_eq!(find(&graph, "clementine/d").version.to_string(), "0.4.0");
}

#[test]
fn transitive_chain_git() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let remote_d = work.path().join("remote-d");
    std::fs::create_dir_all(&remote_d).unwrap();
    let d_sha = make_repo(
        &remote_d,
        &[("krypton.toml", &manifest("clementine/d", "0.4.0"))],
    );
    add_tag(&remote_d, "v0.4.0");

    let remote_c = work.path().join("remote-c");
    std::fs::create_dir_all(&remote_c).unwrap();
    let c_manifest = manifest_with(
        "clementine/c",
        "0.3.0",
        &[(
            "d",
            &format!(
                "{{ package = \"clementine/d\", git = \"{}\", tag = \"v0.4.0\" }}",
                remote_d.display()
            ),
        )],
    );
    let c_sha = make_repo(&remote_c, &[("krypton.toml", &c_manifest)]);
    add_tag(&remote_c, "v0.3.0");

    let remote_b = work.path().join("remote-b");
    std::fs::create_dir_all(&remote_b).unwrap();
    let b_manifest = manifest_with(
        "clementine/b",
        "0.2.0",
        &[(
            "c",
            &format!(
                "{{ package = \"clementine/c\", git = \"{}\", tag = \"v0.3.0\" }}",
                remote_c.display()
            ),
        )],
    );
    let b_sha = make_repo(&remote_b, &[("krypton.toml", &b_manifest)]);
    add_tag(&remote_b, "v0.2.0");

    let root_dir = work.path().join("root");
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", git = \"{}\", tag = \"v0.2.0\" }}",
                remote_b.display()
            ),
        )],
    );

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest, &cache).expect("resolve");
    assert_eq!(graph.len(), 3);
    match &find(&graph, "clementine/b").source_type {
        SourceType::Git { sha, .. } => assert_eq!(sha, &b_sha),
        other => panic!("expected Git, got {other:?}"),
    }
    match &find(&graph, "clementine/c").source_type {
        SourceType::Git { sha, .. } => assert_eq!(sha, &c_sha),
        other => panic!("expected Git, got {other:?}"),
    }
    match &find(&graph, "clementine/d").source_type {
        SourceType::Git { sha, .. } => assert_eq!(sha, &d_sha),
        other => panic!("expected Git, got {other:?}"),
    }
}

#[test]
fn diamond_compatible() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let b_dir = work.path().join("b");
    let c_dir = work.path().join("c");
    let d_dir = work.path().join("d");

    // D 1.5.0 satisfies both ^1.0.0 (B) and ^1.2.0 (C) since they each accept
    // any version in the `>=1.x, <2.0` window that includes the lower bound.
    write_manifest(&d_dir, "clementine/d", "1.5.0", &[]);
    write_manifest(
        &b_dir,
        "clementine/b",
        "0.1.0",
        &[(
            "d",
            &format!(
                "{{ package = \"clementine/d\", path = \"{}\", version = \"^1.0.0\" }}",
                d_dir.display()
            ),
        )],
    );
    write_manifest(
        &c_dir,
        "clementine/c",
        "0.1.0",
        &[(
            "d",
            &format!(
                "{{ package = \"clementine/d\", path = \"{}\", version = \"^1.2.0\" }}",
                d_dir.display()
            ),
        )],
    );
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "b",
                &format!(
                    "{{ package = \"clementine/b\", path = \"{}\" }}",
                    b_dir.display()
                ),
            ),
            (
                "c",
                &format!(
                    "{{ package = \"clementine/c\", path = \"{}\" }}",
                    c_dir.display()
                ),
            ),
        ],
    );

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest, &cache).expect("resolve");
    assert_eq!(find(&graph, "clementine/d").version.to_string(), "1.5.0");
}

#[test]
fn diamond_incompatible_single_version() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let b_dir = work.path().join("b");
    let c_dir = work.path().join("c");
    let d_dir = work.path().join("d");

    // D 1.0.0 cannot satisfy ^1.2.0 (C's constraint) so resolution fails.
    write_manifest(&d_dir, "clementine/d", "1.0.0", &[]);
    write_manifest(
        &b_dir,
        "clementine/b",
        "0.1.0",
        &[(
            "d",
            &format!(
                "{{ package = \"clementine/d\", path = \"{}\", version = \"^1.0.0\" }}",
                d_dir.display()
            ),
        )],
    );
    write_manifest(
        &c_dir,
        "clementine/c",
        "0.1.0",
        &[(
            "d",
            &format!(
                "{{ package = \"clementine/d\", path = \"{}\", version = \"^1.2.0\" }}",
                d_dir.display()
            ),
        )],
    );
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "b",
                &format!(
                    "{{ package = \"clementine/b\", path = \"{}\" }}",
                    b_dir.display()
                ),
            ),
            (
                "c",
                &format!(
                    "{{ package = \"clementine/c\", path = \"{}\" }}",
                    c_dir.display()
                ),
            ),
        ],
    );

    let root_manifest = load_root(&root_dir);
    let err = resolve(&root_dir, root_manifest, &cache).expect_err("should fail");
    match &err {
        ResolveError::Unsatisfiable { rendered } => {
            assert!(
                rendered.contains("clementine/d"),
                "rendered message must name the contested package:\n{rendered}"
            );
        }
        other => panic!("expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn conflict_named_requesters() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let a_dir = work.path().join("a");
    let c_dir = work.path().join("c");
    let b_dir = work.path().join("b");

    write_manifest(&b_dir, "clementine/b", "1.5.0", &[]);
    write_manifest(
        &a_dir,
        "clementine/a",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", path = \"{}\", version = \"^1.0.0\" }}",
                b_dir.display()
            ),
        )],
    );
    write_manifest(
        &c_dir,
        "clementine/c",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", path = \"{}\", version = \"^2.0.0\" }}",
                b_dir.display()
            ),
        )],
    );
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
                "c",
                &format!(
                    "{{ package = \"clementine/c\", path = \"{}\" }}",
                    c_dir.display()
                ),
            ),
        ],
    );

    let root_manifest = load_root(&root_dir);
    let err = resolve(&root_dir, root_manifest, &cache).expect_err("should fail");
    match &err {
        ResolveError::Unsatisfiable { rendered } => {
            assert!(
                rendered.contains("clementine/b"),
                "names contested:\n{rendered}"
            );
            // At least one of the requesters should appear in the report.
            let mentions_a = rendered.contains("clementine/a");
            let mentions_c = rendered.contains("clementine/c");
            assert!(
                mentions_a || mentions_c,
                "at least one requester must be named:\n{rendered}"
            );
        }
        other => panic!("expected Unsatisfiable, got {other:?}"),
    }
}

#[test]
fn source_mismatch_path_vs_git() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let remote_foo = work.path().join("remote-foo");
    std::fs::create_dir_all(&remote_foo).unwrap();
    make_repo(
        &remote_foo,
        &[("krypton.toml", &manifest("clementine/foo", "0.1.0"))],
    );
    add_tag(&remote_foo, "v0.1.0");

    let foo_local = work.path().join("foo");
    write_manifest(&foo_local, "clementine/foo", "0.1.0", &[]);

    let root_dir = work.path().join("root");
    let a_dir = work.path().join("a");
    let c_dir = work.path().join("c");

    write_manifest(
        &a_dir,
        "clementine/a",
        "0.1.0",
        &[(
            "foo",
            &format!(
                "{{ package = \"clementine/foo\", path = \"{}\" }}",
                foo_local.display()
            ),
        )],
    );
    write_manifest(
        &c_dir,
        "clementine/c",
        "0.1.0",
        &[(
            "foo",
            &format!(
                "{{ package = \"clementine/foo\", git = \"{}\", tag = \"v0.1.0\" }}",
                remote_foo.display()
            ),
        )],
    );
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
                "c",
                &format!(
                    "{{ package = \"clementine/c\", path = \"{}\" }}",
                    c_dir.display()
                ),
            ),
        ],
    );

    let root_manifest = load_root(&root_dir);
    let err = resolve(&root_dir, root_manifest, &cache).expect_err("should fail");
    match &err {
        ResolveError::SourceMismatch {
            canonical,
            first,
            second,
        } => {
            assert_eq!(canonical.as_str(), "clementine/foo");
            // Order depends on pubgrub traversal; accept either (path, git) or (git, path).
            let is_path = |d: &SourceDescriptor| matches!(d, SourceDescriptor::Path { .. });
            let is_git = |d: &SourceDescriptor| matches!(d, SourceDescriptor::Git { .. });
            assert!(
                (is_path(first) && is_git(second)) || (is_git(first) && is_path(second)),
                "descriptors must be one path + one git, got first={first:?} second={second:?}"
            );
        }
        other => panic!("expected SourceMismatch, got {other:?}"),
    }
}

#[test]
fn cycle_detection_terminates() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let b_dir = work.path().join("b");

    // A (the root) at 0.1.0 depends on B ^1.0, while B depends back on A ^2.0.
    // A's actual version cannot satisfy that constraint, so pubgrub must
    // terminate with an Unsatisfiable result rather than loop on the cycle.
    write_manifest(
        &b_dir,
        "clementine/b",
        "1.0.0",
        &[(
            "root",
            &format!(
                "{{ package = \"clementine/root\", path = \"{}\", version = \"^2.0.0\" }}",
                root_dir.display()
            ),
        )],
    );
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", path = \"{}\", version = \"^1.0.0\" }}",
                b_dir.display()
            ),
        )],
    );

    let root_manifest = load_root(&root_dir);
    let start = Instant::now();
    let result = resolve(&root_dir, root_manifest, &cache);
    let elapsed = start.elapsed();
    assert!(
        elapsed < Duration::from_secs(2),
        "cycle must terminate; took {elapsed:?}"
    );
    match result {
        Err(ResolveError::Unsatisfiable { .. }) | Err(ResolveError::Cycle { .. }) => {}
        Err(other) => panic!("expected Unsatisfiable/Cycle, got {other:?}"),
        Ok(_) => panic!("cycle with conflicting version bounds must not succeed"),
    }
}

#[test]
fn path_without_version_unconstrained() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    let b_dir = work.path().join("b");

    write_manifest(&b_dir, "clementine/b", "7.0.0", &[]);
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", path = \"{}\" }}",
                b_dir.display()
            ),
        )],
    );

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest, &cache).expect("resolve");
    assert_eq!(find(&graph, "clementine/b").version.to_string(), "7.0.0");
}

#[test]
fn cache_hit_skips_git() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    // Pre-populate a SHA-keyed source under the cache without involving git.
    let sha = "a".repeat(40);
    let sha_dir = cache.package_source_dir("clementine", "b", &sha);
    std::fs::create_dir_all(&sha_dir).expect("create sha dir");
    std::fs::write(
        sha_dir.join("krypton.toml"),
        manifest("clementine/b", "0.1.0"),
    )
    .expect("write manifest");

    // Intentionally bogus url — fetch_git's cache-hit path must short-circuit
    // on the full SHA, never invoking git against this URL.
    let bogus = work.path().join("no-such-remote");

    let root_dir = work.path().join("root");
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", git = \"{}\", rev = \"{}\" }}",
                bogus.display(),
                sha
            ),
        )],
    );

    let root_manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, root_manifest, &cache).expect("resolve");
    let b = find(&graph, "clementine/b");
    assert_eq!(
        b.source_path,
        cache.package_source_dir("clementine", "b", &sha)
    );
    match &b.source_type {
        SourceType::Git { sha: got, .. } => assert_eq!(got, &sha),
        other => panic!("expected Git source, got {other:?}"),
    }
    // No persistent clone dir should have been created, proving git wasn't run.
    assert!(
        !cache.git_clone_dir("clementine", "b").exists(),
        "cache-hit path must not create a persistent clone"
    );
}

#[test]
fn registry_dep_rejected_today() {
    let work = tempdir().expect("work tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let root_dir = work.path().join("root");
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "foo",
            "{ package = \"clementine/foo\", version = \"1.0.0\" }",
        )],
    );

    let root_manifest = load_root(&root_dir);
    let err = resolve(&root_dir, root_manifest, &cache).expect_err("registry not supported");
    match err {
        ResolveError::RegistryUnsupported { canonical } => {
            assert_eq!(canonical.as_str(), "clementine/foo");
        }
        other => panic!("expected RegistryUnsupported, got {other:?}"),
    }
}
