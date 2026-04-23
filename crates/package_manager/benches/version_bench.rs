use criterion::{criterion_group, criterion_main, Criterion};
use krypton_package_manager::VersionReq;
use semver::Version;

fn version_benchmarks(c: &mut Criterion) {
    c.bench_function("version_req_parse_caret", |b| {
        b.iter(|| VersionReq::parse(std::hint::black_box("1.2.3")).unwrap());
    });

    c.bench_function("version_req_parse_compound", |b| {
        b.iter(|| VersionReq::parse(std::hint::black_box(">=0.2.0, <0.4.0")).unwrap());
    });

    let req = VersionReq::parse("^1.2.3").expect("parses");
    let probes = [
        Version::parse("1.2.3").unwrap(),
        Version::parse("1.99.99").unwrap(),
        Version::parse("2.0.0").unwrap(),
    ];
    c.bench_function("version_req_matches", |b| {
        b.iter(|| {
            let mut hits = 0usize;
            for probe in &probes {
                if req.matches(std::hint::black_box(probe)) {
                    hits += 1;
                }
            }
            hits
        });
    });
}

criterion_group!(benches, version_benchmarks);
criterion_main!(benches);
