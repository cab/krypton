use std::process::Command;

use krypton_package_manager::{CacheDir, FetchError, GitRef, fetch_git};
use tempfile::tempdir;

mod common;
use common::*;

#[test]
fn tag_ref_clones_resolves_and_checks_out() {
    let remote = tempdir().expect("remote tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let manifest_text = manifest("clementine/http", "0.1.0");
    let tagged_sha = make_repo(remote.path(), &[("krypton.toml", &manifest_text)]);
    add_tag(remote.path(), "v0.1.0");

    let url = remote.path().to_str().unwrap();
    let fetched = fetch_git(
        &cache,
        "http",
        "clementine",
        "http",
        url,
        &GitRef::Tag("v0.1.0".to_string()),
    )
    .expect("fetch_git tag");

    assert_eq!(fetched.sha, tagged_sha);
    assert_eq!(
        fetched.source_dir,
        cache.package_source_dir("clementine", "http", &tagged_sha)
    );
    assert!(fetched.source_dir.join("krypton.toml").exists());
    assert_eq!(fetched.manifest.package.name, "clementine/http");
}

#[test]
fn rev_ref_checks_out_exact_sha() {
    let remote = tempdir().expect("remote tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let first_sha = make_repo(
        remote.path(),
        &[("krypton.toml", &manifest("clementine/http", "0.1.0"))],
    );
    let _second_sha = add_commit(
        remote.path(),
        "second",
        &[("krypton.toml", &manifest("clementine/http", "0.2.0"))],
    );

    let url = remote.path().to_str().unwrap();
    let fetched = fetch_git(
        &cache,
        "http",
        "clementine",
        "http",
        url,
        &GitRef::Rev(first_sha.clone()),
    )
    .expect("fetch_git rev");

    assert_eq!(fetched.sha, first_sha);
    let on_disk = std::fs::read_to_string(fetched.source_dir.join("krypton.toml"))
        .expect("read manifest");
    assert!(on_disk.contains("0.1.0"));
}

#[test]
fn branch_ref_resolves_head() {
    let remote = tempdir().expect("remote tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let initial = make_repo(
        remote.path(),
        &[("krypton.toml", &manifest("clementine/http", "0.1.0"))],
    );
    let head = add_commit(
        remote.path(),
        "second",
        &[("krypton.toml", &manifest("clementine/http", "0.2.0"))],
    );
    assert_ne!(initial, head);

    let url = remote.path().to_str().unwrap();
    let fetched = fetch_git(
        &cache,
        "http",
        "clementine",
        "http",
        url,
        &GitRef::Branch("main".to_string()),
    )
    .expect("fetch_git branch");

    assert_eq!(fetched.sha, head);
}

#[test]
fn cache_hit_skips_git() {
    let remote = tempdir().expect("remote tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let sha = make_repo(
        remote.path(),
        &[("krypton.toml", &manifest("clementine/http", "0.1.0"))],
    );
    add_tag(remote.path(), "v0.1.0");

    let url = remote.path().to_str().unwrap().to_string();
    let first = fetch_git(
        &cache,
        "http",
        "clementine",
        "http",
        &url,
        &GitRef::Tag("v0.1.0".to_string()),
    )
    .expect("first fetch");
    assert_eq!(first.sha, sha);

    // Now ensure subsequent fetches that hit the cache do not call git: drop
    // the remote AND repoint the persistent clone's `origin` at a path that
    // does not exist. With the SHA-keyed cache populated, fetch_git with a
    // GitRef::Rev for the same SHA must return purely from the filesystem.
    drop(remote);
    let bogus = cache_root.path().join("nonexistent-remote");
    let clone_dir = cache.git_clone_dir("clementine", "http");
    let set_url = Command::new("git")
        .arg("-C")
        .arg(&clone_dir)
        .args(["remote", "set-url", "origin"])
        .arg(&bogus)
        .output()
        .expect("set-url");
    assert!(set_url.status.success(), "set-url failed");

    let second = fetch_git(
        &cache,
        "http",
        "clementine",
        "http",
        bogus.to_str().unwrap(),
        &GitRef::Rev(sha.clone()),
    )
    .expect("second fetch should hit cache");
    assert_eq!(second.sha, sha);
    assert_eq!(second.source_dir, first.source_dir);
}

#[test]
fn cache_miss_with_existing_clone_reuses_it() {
    let remote = tempdir().expect("remote tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let v1 = make_repo(
        remote.path(),
        &[("krypton.toml", &manifest("clementine/http", "0.1.0"))],
    );
    add_tag(remote.path(), "v0.1.0");

    let url = remote.path().to_str().unwrap();
    let first = fetch_git(
        &cache,
        "http",
        "clementine",
        "http",
        url,
        &GitRef::Tag("v0.1.0".to_string()),
    )
    .expect("first fetch");
    assert_eq!(first.sha, v1);

    let clone_dir = cache.git_clone_dir("clementine", "http");
    let head_path = clone_dir.join(".git").join("HEAD");
    let pre_meta = std::fs::metadata(&head_path).expect("HEAD before");
    let pre_ctime = pre_meta.modified().expect("modified before");

    let v2 = add_commit(
        remote.path(),
        "second",
        &[("krypton.toml", &manifest("clementine/http", "0.2.0"))],
    );
    add_tag(remote.path(), "v0.2.0");

    let second = fetch_git(
        &cache,
        "http",
        "clementine",
        "http",
        url,
        &GitRef::Tag("v0.2.0".to_string()),
    )
    .expect("second fetch");
    assert_eq!(second.sha, v2);

    // The persistent clone must still exist (no rm -rf and re-clone).
    let post_meta = std::fs::metadata(&head_path).expect("HEAD after");
    let post_ctime = post_meta.modified().expect("modified after");
    assert!(
        post_ctime >= pre_ctime,
        "HEAD modification time should not regress (pre={pre_ctime:?}, post={post_ctime:?})",
    );

    // Both SHAs are now extracted under packages/.
    assert!(
        cache
            .package_source_dir("clementine", "http", &v1)
            .join("krypton.toml")
            .exists(),
        "v0.1.0 source still present"
    );
    assert!(
        cache
            .package_source_dir("clementine", "http", &v2)
            .join("krypton.toml")
            .exists(),
        "v0.2.0 source extracted"
    );
}

#[test]
fn missing_krypton_toml_errors() {
    let remote = tempdir().expect("remote tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    make_repo(remote.path(), &[("README.md", "no manifest here\n")]);
    add_tag(remote.path(), "v0.1.0");

    let url = remote.path().to_str().unwrap();
    let err = fetch_git(
        &cache,
        "clementine/http",
        "clementine",
        "http",
        url,
        &GitRef::Tag("v0.1.0".to_string()),
    )
    .expect_err("should error");

    match &err {
        FetchError::MissingManifest { dep_key, url: u } => {
            assert_eq!(dep_key, "clementine/http");
            assert_eq!(u, url);
        }
        other => panic!("expected MissingManifest, got {other:?}"),
    }
    let msg = err.to_string();
    assert!(msg.contains("clementine/http"), "msg = {msg}");
    assert!(msg.contains(url), "msg = {msg}");
}

#[test]
fn invalid_krypton_toml_errors() {
    let remote = tempdir().expect("remote tempdir");
    let cache_root = make_cache_root();
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    make_repo(
        remote.path(),
        &[("krypton.toml", "not = \"a valid manifest\"\n")],
    );
    add_tag(remote.path(), "v0.1.0");

    let url = remote.path().to_str().unwrap();
    let err = fetch_git(
        &cache,
        "clementine/http",
        "clementine",
        "http",
        url,
        &GitRef::Tag("v0.1.0".to_string()),
    )
    .expect_err("should error");

    let inner_msg = match &err {
        FetchError::InvalidManifest {
            dep_key,
            url: u,
            source,
        } => {
            assert_eq!(dep_key, "clementine/http");
            assert_eq!(u, url);
            source.to_string()
        }
        other => panic!("expected InvalidManifest, got {other:?}"),
    };
    let msg = err.to_string();
    assert!(msg.contains("clementine/http"), "msg = {msg}");
    assert!(msg.contains(url), "msg = {msg}");
    assert!(
        msg.contains(inner_msg.trim()),
        "outer msg should embed inner parse error: outer={msg}, inner={inner_msg}"
    );
}
