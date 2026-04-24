use std::path::Path;

use krypton_package_manager::{
    resolve, CacheDir, Lockfile, LockfileError, Manifest, MavenArtifact,
};
use tempfile::tempdir;

mod common;
use common::*;

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
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("krypton.toml"), manifest_with(name, version, deps)).unwrap();
}

fn load_root(dir: &Path) -> Manifest {
    Manifest::from_path(dir.join("krypton.toml")).unwrap()
}

/// Build a tiny fixture with one git dep and one path dep, returning the
/// generated lockfile plus the paths needed to exercise it.
struct MixedFixture {
    _work: tempfile::TempDir,
    _cache_root: tempfile::TempDir,
    cache: CacheDir,
    root_dir: std::path::PathBuf,
    remote_http: std::path::PathBuf,
    http_sha: String,
    lib_dir: std::path::PathBuf,
}

fn build_mixed_fixture() -> MixedFixture {
    let work = tempdir().unwrap();
    let cache_root = tempdir().unwrap();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let remote_http = work.path().join("remote-http");
    std::fs::create_dir_all(&remote_http).unwrap();
    let http_sha = make_repo(
        &remote_http,
        &[("krypton.toml", &manifest("clementine/http", "0.3.0"))],
    );
    add_tag(&remote_http, "v0.3.0");

    let lib_dir = work.path().join("mylib");
    write_manifest(&lib_dir, "clementine/mylib", "0.2.0", &[]);

    let root_dir = work.path().join("root");
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "http",
                &format!(
                    "{{ package = \"clementine/http\", git = \"{}\", tag = \"v0.3.0\" }}",
                    remote_http.display()
                ),
            ),
            (
                "mylib",
                &format!(
                    "{{ package = \"clementine/mylib\", path = \"{}\" }}",
                    lib_dir.display()
                ),
            ),
        ],
    );

    MixedFixture {
        _work: work,
        _cache_root: cache_root,
        cache,
        root_dir,
        remote_http,
        http_sha,
        lib_dir,
    }
}

#[test]
fn generates_expected_toml_for_path_and_git_mix() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();
    let rendered = lock.to_toml_string();

    // Normalize volatile substrings: SHAs, hashes, and the remote URL.
    let normalized = rendered
        .replace(&fx.http_sha, "<SHA>")
        .replace(fx.remote_http.to_str().unwrap(), "<REMOTE-HTTP>");
    let mut redacted = String::with_capacity(normalized.len());
    for line in normalized.lines() {
        let line = if let Some(idx) = line.find("hash = \"sha256:") {
            let mut s = line[..idx].to_string();
            s.push_str("hash = \"sha256:<HASH>\"");
            s
        } else {
            line.to_string()
        };
        redacted.push_str(&line);
        redacted.push('\n');
    }

    insta::assert_snapshot!(redacted);
}

#[test]
fn header_comment_present() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let rendered = Lockfile::generate(&graph, &[], &fx.root_dir)
        .unwrap()
        .to_toml_string();

    let first_nonempty = rendered
        .lines()
        .find(|l| !l.trim().is_empty())
        .expect("lockfile has content");
    assert_eq!(
        first_nonempty.trim(),
        "# This file is generated. Do not edit manually."
    );
}

#[test]
fn roundtrip_generate_write_read() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    let tmp = tempdir().unwrap();
    let lock_path = tmp.path().join("krypton.lock");
    lock.write(&lock_path).unwrap();
    let read_back = Lockfile::read(&lock_path).unwrap();

    assert_eq!(read_back.packages.len(), lock.packages.len());
    assert_eq!(read_back.maven.len(), lock.maven.len());
    for (a, b) in lock.packages.iter().zip(read_back.packages.iter()) {
        assert_eq!(a.name, b.name);
        assert_eq!(a.version, b.version);
        assert_eq!(a.hash, b.hash);
        assert_eq!(a.source, b.source);
    }
    assert_eq!(lock.maven, read_back.maven);
}

#[test]
fn roundtrip_to_resolved_graph() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    let tmp = tempdir().unwrap();
    let lock_path = tmp.path().join("krypton.lock");
    lock.write(&lock_path).unwrap();
    let read_back = Lockfile::read(&lock_path).unwrap();

    let rehydrated = read_back
        .to_resolved_graph(&fx.cache, &fx.root_dir)
        .expect("rehydrate");

    assert_eq!(rehydrated.len(), graph.len());
    for (canonical, original) in graph.iter() {
        let reb = rehydrated
            .get(canonical)
            .unwrap_or_else(|| panic!("missing {canonical} after rehydration"));
        assert_eq!(reb.version, original.version);
        assert_eq!(reb.source_path, original.source_path);
        assert_eq!(
            std::mem::discriminant(&reb.source_type),
            std::mem::discriminant(&original.source_type),
            "source_type discriminant must match for {canonical}"
        );
    }
}

#[test]
fn is_current_true_when_manifest_unchanged() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest.clone(), &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    assert!(lock.is_current(&manifest, &fx.root_dir));
}

#[test]
fn is_current_false_when_dep_added() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    // Add a fresh path dep to the manifest after locking.
    let extra_dir = fx.root_dir.parent().unwrap().join("extra");
    write_manifest(&extra_dir, "clementine/extra", "0.1.0", &[]);
    write_manifest(
        &fx.root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "http",
                &format!(
                    "{{ package = \"clementine/http\", git = \"{}\", tag = \"v0.3.0\" }}",
                    fx.remote_http.display()
                ),
            ),
            (
                "mylib",
                &format!(
                    "{{ package = \"clementine/mylib\", path = \"{}\" }}",
                    fx.lib_dir.display()
                ),
            ),
            (
                "extra",
                &format!(
                    "{{ package = \"clementine/extra\", path = \"{}\" }}",
                    extra_dir.display()
                ),
            ),
        ],
    );
    let new_manifest = load_root(&fx.root_dir);

    assert!(!lock.is_current(&new_manifest, &fx.root_dir));
}

#[test]
fn is_current_false_when_dep_removed() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    // Remove `mylib` from the manifest, leaving only `http`, then add an
    // entirely unrelated path dep that isn't in the lockfile. This guarantees
    // the manifest direct deps are not a subset of the lockfile's packages.
    let other_dir = fx.root_dir.parent().unwrap().join("other");
    write_manifest(&other_dir, "clementine/other", "0.1.0", &[]);
    write_manifest(
        &fx.root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "other",
            &format!(
                "{{ package = \"clementine/other\", path = \"{}\" }}",
                other_dir.display()
            ),
        )],
    );
    let new_manifest = load_root(&fx.root_dir);

    assert!(!lock.is_current(&new_manifest, &fx.root_dir));
}

#[test]
fn is_current_false_when_git_url_changed() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    // Rewrite `http`'s git URL to a different (unused) remote; keep the same
    // canonical name. `is_current` should reject on URL mismatch.
    write_manifest(
        &fx.root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "http",
                "{ package = \"clementine/http\", git = \"https://example.invalid/otherorg/http\", tag = \"v0.3.0\" }",
            ),
            (
                "mylib",
                &format!(
                    "{{ package = \"clementine/mylib\", path = \"{}\" }}",
                    fx.lib_dir.display()
                ),
            ),
        ],
    );
    let new_manifest = load_root(&fx.root_dir);
    assert!(!lock.is_current(&new_manifest, &fx.root_dir));
}

#[test]
fn is_current_false_when_git_rev_changed() {
    let work = tempdir().unwrap();
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let remote = work.path().join("remote");
    std::fs::create_dir_all(&remote).unwrap();
    let sha1 = make_repo(
        &remote,
        &[("krypton.toml", &manifest("clementine/http", "0.3.0"))],
    );
    let sha2 = add_commit(
        &remote,
        "bump",
        &[("krypton.toml", &manifest("clementine/http", "0.3.1"))],
    );
    assert_ne!(sha1, sha2);

    let root_dir = work.path().join("root");
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "http",
            &format!(
                "{{ package = \"clementine/http\", git = \"{}\", rev = \"{}\" }}",
                remote.display(),
                sha1
            ),
        )],
    );
    let manifest1 = load_root(&root_dir);
    let graph = resolve(&root_dir, manifest1, &cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &root_dir).unwrap();

    // Swap to sha2: rev differs, so the lock is stale.
    write_manifest(
        &root_dir,
        "clementine/root",
        "0.1.0",
        &[(
            "http",
            &format!(
                "{{ package = \"clementine/http\", git = \"{}\", rev = \"{}\" }}",
                remote.display(),
                sha2
            ),
        )],
    );
    let manifest2 = load_root(&root_dir);
    assert!(!lock.is_current(&manifest2, &root_dir));
}

#[test]
fn is_current_false_when_path_changed() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    // Point `mylib` at a different directory — canonical path mismatch.
    let alt_lib = fx.root_dir.parent().unwrap().join("mylib-alt");
    write_manifest(&alt_lib, "clementine/mylib", "0.2.0", &[]);
    write_manifest(
        &fx.root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "http",
                &format!(
                    "{{ package = \"clementine/http\", git = \"{}\", tag = \"v0.3.0\" }}",
                    fx.remote_http.display()
                ),
            ),
            (
                "mylib",
                &format!(
                    "{{ package = \"clementine/mylib\", path = \"{}\" }}",
                    alt_lib.display()
                ),
            ),
        ],
    );
    let new_manifest = load_root(&fx.root_dir);
    assert!(!lock.is_current(&new_manifest, &fx.root_dir));
}

#[test]
fn to_resolved_graph_errors_on_cache_miss() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    // Wipe the git-source cache; path deps still rehydrate off the filesystem.
    let packages_root = fx.cache.root().join("cache").join("packages");
    if packages_root.exists() {
        std::fs::remove_dir_all(&packages_root).unwrap();
    }

    let err = lock
        .to_resolved_graph(&fx.cache, &fx.root_dir)
        .expect_err("cache miss should error");
    match err {
        LockfileError::Invalid { message } => {
            assert!(
                message.contains("krypton.toml"),
                "error must reference the missing manifest: {message}"
            );
            assert!(
                message.to_lowercase().contains("krypton lock"),
                "error must prompt `krypton lock`: {message}"
            );
        }
        other => panic!("expected Invalid, got {other:?}"),
    }
}

#[test]
fn git_entry_has_rev_path_entry_does_not() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();
    let rendered = Lockfile::generate(&graph, &[], &fx.root_dir)
        .unwrap()
        .to_toml_string();

    let doc: toml::Value = toml::from_str(&rendered).expect("valid TOML");
    let packages = doc
        .get("package")
        .and_then(|v| v.as_array())
        .expect("[[package]] entries present");

    let mut saw_git = false;
    let mut saw_path = false;
    for row in packages {
        let tbl = row.as_table().expect("package is a table");
        let source = tbl.get("source").and_then(|v| v.as_str()).expect("source");
        if source.starts_with("git+") {
            saw_git = true;
            assert!(
                tbl.contains_key("rev"),
                "git [[package]] row must have a `rev`: {tbl:?}"
            );
        } else if source.starts_with("path+") {
            saw_path = true;
            assert!(
                !tbl.contains_key("rev"),
                "path [[package]] row must not carry a `rev`: {tbl:?}"
            );
        }
    }
    assert!(
        saw_git && saw_path,
        "fixture should have one git and one path row"
    );
}

#[test]
fn maven_entries_roundtrip() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();

    let maven = vec![
        MavenArtifact {
            coord: "org.postgresql:postgresql:42.7.1".to_string(),
            url: "https://repo1.maven.org/maven2/org/postgresql/postgresql/42.7.1/postgresql-42.7.1.jar"
                .to_string(),
            hash: "sha256:abcdef".to_string(),
        },
        MavenArtifact {
            coord: "com.google.guava:guava:33.0.0-jre".to_string(),
            url: "https://repo1.maven.org/maven2/com/google/guava/guava/33.0.0-jre/guava-33.0.0-jre.jar"
                .to_string(),
            hash: "sha256:fedcba".to_string(),
        },
    ];

    let lock = Lockfile::generate(&graph, &maven, &fx.root_dir).unwrap();
    let tmp = tempdir().unwrap();
    let lock_path = tmp.path().join("krypton.lock");
    lock.write(&lock_path).unwrap();
    let read_back = Lockfile::read(&lock_path).unwrap();

    assert_eq!(read_back.maven.len(), 2);
    // Sorted by coord: com.google.guava precedes org.postgresql.
    assert_eq!(
        read_back.maven[0].coord,
        "com.google.guava:guava:33.0.0-jre"
    );
    assert_eq!(read_back.maven[1].coord, "org.postgresql:postgresql:42.7.1");
    assert_eq!(read_back.maven[0].hash, "sha256:fedcba");
    assert_eq!(
        read_back.maven[1].url,
        "https://repo1.maven.org/maven2/org/postgresql/postgresql/42.7.1/postgresql-42.7.1.jar"
    );
}

#[test]
fn fresh_second_build_scenario() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest.clone(), &fx.cache).unwrap();

    // First build: no lockfile → generate + write.
    let lock_path = fx.root_dir.join("krypton.lock");
    assert!(
        !lock_path.exists(),
        "fresh project should not have a lockfile"
    );
    let lock = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();
    lock.write(&lock_path).unwrap();
    assert!(lock_path.exists());

    // Second build: read + is_current == true.
    let round = Lockfile::read(&lock_path).unwrap();
    assert!(round.is_current(&manifest, &fx.root_dir));

    // Add a dep: is_current → false.
    let extra_dir = fx.root_dir.parent().unwrap().join("extra");
    write_manifest(&extra_dir, "clementine/extra", "0.1.0", &[]);
    write_manifest(
        &fx.root_dir,
        "clementine/root",
        "0.1.0",
        &[
            (
                "http",
                &format!(
                    "{{ package = \"clementine/http\", git = \"{}\", tag = \"v0.3.0\" }}",
                    fx.remote_http.display()
                ),
            ),
            (
                "mylib",
                &format!(
                    "{{ package = \"clementine/mylib\", path = \"{}\" }}",
                    fx.lib_dir.display()
                ),
            ),
            (
                "extra",
                &format!(
                    "{{ package = \"clementine/extra\", path = \"{}\" }}",
                    extra_dir.display()
                ),
            ),
        ],
    );
    let modified = load_root(&fx.root_dir);
    assert!(!round.is_current(&modified, &fx.root_dir));
}

#[test]
fn hash_deterministic_across_runs() {
    let fx = build_mixed_fixture();
    let manifest = load_root(&fx.root_dir);
    let graph = resolve(&fx.root_dir, manifest, &fx.cache).unwrap();

    let lock1 = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();
    let lock2 = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();
    assert_eq!(lock1.packages, lock2.packages);

    // Mutate `mylib` source; the path dep's hash must change.
    std::fs::write(fx.lib_dir.join("changed.kr"), "fn f() = 0\n").unwrap();
    let lock3 = Lockfile::generate(&graph, &[], &fx.root_dir).unwrap();

    let orig_hash = lock1
        .packages
        .iter()
        .find(|p| p.name.as_str() == "clementine/mylib")
        .unwrap()
        .hash
        .clone();
    let new_hash = lock3
        .packages
        .iter()
        .find(|p| p.name.as_str() == "clementine/mylib")
        .unwrap()
        .hash
        .clone();
    assert_ne!(orig_hash, new_hash, "content change must alter the hash");
}

#[test]
fn path_source_serializes_relative() {
    let work = tempdir().unwrap();
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    // Sibling path dep: root at <work>/a, dep at <work>/b → relative `../b`.
    let root_dir = work.path().join("a");
    let dep_dir = work.path().join("b");
    write_manifest(&dep_dir, "clementine/b", "0.1.0", &[]);
    write_manifest(
        &root_dir,
        "clementine/a",
        "0.1.0",
        &[(
            "b",
            &format!(
                "{{ package = \"clementine/b\", path = \"{}\" }}",
                dep_dir.display()
            ),
        )],
    );

    let manifest = load_root(&root_dir);
    let graph = resolve(&root_dir, manifest, &cache).unwrap();
    let lock = Lockfile::generate(&graph, &[], &root_dir).unwrap();

    let rendered = lock.to_toml_string();
    assert!(
        rendered.contains("source = \"path+../b\""),
        "expected relative sibling path with forward slashes, got:\n{rendered}"
    );
}
