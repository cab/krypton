use std::path::{Path, PathBuf};

use criterion::{criterion_group, criterion_main, Criterion};
use krypton_package_manager::{AddSource, Manifest, ManifestEditor};

const TRIVIAL: &str = r#"[package]
name = "my-org/app"
version = "0.1.0"
"#;

const SPEC_EXAMPLE: &str = r#"[package]
name = "my-org/my-app"
version = "0.1.0"
description = "A short description"
license = "MIT"
krypton = ">=0.1.0"

[dependencies]
http = { package = "clementine/http", version = "0.3.0" }
json = { package = "clementine/json", git = "https://github.com/clementine/krypton-json", tag = "v0.2.0" }
shared = { package = "my-org/shared", path = "../shared" }

[dev-dependencies]
test_utils = { package = "clementine/test-utils", version = "0.1.0" }

[jvm]
maven = [
    "org.postgresql:postgresql:42.7.1",
    "com.google.guava:guava:33.0.0-jre",
]
classpath = [
    "lib/proprietary-driver.jar",
]
"#;

fn manifest_benchmarks(c: &mut Criterion) {
    c.bench_function("manifest_parse_trivial", |b| {
        b.iter(|| Manifest::from_str(std::hint::black_box(TRIVIAL)).unwrap());
    });
    c.bench_function("manifest_parse_spec_example", |b| {
        b.iter(|| Manifest::from_str(std::hint::black_box(SPEC_EXAMPLE)).unwrap());
    });

    let path = Path::new("krypton.toml");
    c.bench_function("manifest_edit_add_dep", |b| {
        b.iter(|| {
            let mut editor =
                ManifestEditor::from_str_with_path(std::hint::black_box(SPEC_EXAMPLE), path)
                    .unwrap();
            editor
                .add_dependency(
                    "clementine/new",
                    AddSource::Path {
                        path: PathBuf::from("../new"),
                    },
                    None,
                )
                .unwrap();
            std::hint::black_box(editor.render())
        });
    });
    c.bench_function("manifest_edit_remove_dep", |b| {
        b.iter(|| {
            let mut editor =
                ManifestEditor::from_str_with_path(std::hint::black_box(SPEC_EXAMPLE), path)
                    .unwrap();
            editor.remove_dependency("http").unwrap();
            std::hint::black_box(editor.render())
        });
    });
}

criterion_group!(benches, manifest_benchmarks);
criterion_main!(benches);
