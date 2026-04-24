use std::path::Path;

use criterion::{criterion_group, criterion_main, Criterion};
use krypton_package_manager::{resolve, CacheDir, Lockfile, Manifest};
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

/// Same shape as `resolve_bench.rs::build_fixture`: root depends on two path
/// siblings, one of which pulls in a transitive dep.
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
    (work, cache_root)
}

fn lock_benchmarks(c: &mut Criterion) {
    let (work, cache_root) = build_fixture();
    let root_dir = work.path().join("root");
    let cache = CacheDir::with_root(cache_root.path().to_path_buf());

    let manifest = Manifest::from_path(root_dir.join("krypton.toml")).unwrap();
    let graph = resolve(&root_dir, manifest.clone(), &cache).unwrap();

    c.bench_function("lockfile_generate", |b| {
        b.iter(|| Lockfile::generate(std::hint::black_box(&graph), &[], &root_dir).unwrap());
    });

    c.bench_function("lockfile_write_read_roundtrip", |b| {
        let tmp = tempdir().unwrap();
        let lock_path = tmp.path().join("krypton.lock");
        b.iter(|| {
            let lf = Lockfile::generate(&graph, &[], &root_dir).unwrap();
            let rendered = lf.to_toml_string();
            std::fs::write(&lock_path, rendered).unwrap();
            Lockfile::read(std::hint::black_box(&lock_path)).unwrap()
        });
    });

    let lockfile = Lockfile::generate(&graph, &[], &root_dir).unwrap();
    c.bench_function("lockfile_is_current_hit", |b| {
        b.iter(|| lockfile.is_current(std::hint::black_box(&manifest), &root_dir));
    });
}

criterion_group!(benches, lock_benchmarks);
criterion_main!(benches);
