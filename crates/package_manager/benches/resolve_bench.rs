use std::path::Path;

use criterion::{criterion_group, criterion_main, Criterion};
use krypton_package_manager::{resolve, CacheDir, Manifest};
use tempfile::{tempdir, TempDir};

fn write_manifest(dir: &Path, name: &str, version: &str, deps: &[(&str, &str)]) {
    std::fs::create_dir_all(dir).unwrap();
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
    std::fs::write(dir.join("krypton.toml"), out).unwrap();
}

/// Build a root that depends on two siblings, one of which itself pulls in a
/// transitive path dep — the small realistic resolver shape that lockfile
/// generation and `krypton build` will exercise most often.
fn build_fixture() -> (TempDir, TempDir) {
    let work = tempdir().unwrap();
    let cache_root = tempdir().unwrap();

    let root_dir = work.path().join("root");
    let a_dir = work.path().join("a");
    let b_dir = work.path().join("b");
    let c_dir = work.path().join("c");

    write_manifest(&c_dir, "clementine/c", "0.3.0", &[]);
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
    write_manifest(&a_dir, "clementine/a", "0.2.0", &[]);
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
    // Stash the root dir path as a sibling of `work`'s TempDir lifetime.
    // Returning both TempDirs keeps the filesystem alive for the bench loop.
    (work, cache_root)
}

fn resolve_benchmarks(c: &mut Criterion) {
    let (work, cache_root) = build_fixture();
    let root_dir = work.path().join("root");
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    c.bench_function("resolve_small_path_tree", |b| {
        b.iter(|| {
            let manifest = Manifest::from_path(root_dir.join("krypton.toml")).unwrap();
            resolve(std::hint::black_box(&root_dir), manifest, &cache).unwrap()
        });
    });
}

criterion_group!(benches, resolve_benchmarks);
criterion_main!(benches);
