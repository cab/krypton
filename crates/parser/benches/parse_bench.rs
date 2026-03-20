use criterion::{criterion_group, criterion_main, Criterion};
use krypton_parser::parser::parse;

const TRIVIAL: &str = "fun f(x: Int) -> Int = x + 1";

fn stress_source() -> &'static str {
    static SOURCE: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    SOURCE.get_or_init(|| {
        std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/bench/stress.kr"),
        )
        .expect("failed to read stress fixture")
    })
}

fn parse_benchmarks(c: &mut Criterion) {
    c.bench_function("parse_trivial", |b| {
        b.iter(|| parse(std::hint::black_box(TRIVIAL)));
    });

    let source = stress_source();
    c.bench_function("parse_stress", |b| {
        b.iter(|| parse(std::hint::black_box(source)));
    });
}

criterion_group!(benches, parse_benchmarks);
criterion_main!(benches);
