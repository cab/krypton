use criterion::{criterion_group, criterion_main, Criterion};
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_typechecker::infer::infer_module;

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

fn typecheck_benchmarks(c: &mut Criterion) {
    let resolver = CompositeResolver::stdlib_only();

    // Trivial: pre-parse, benchmark only typechecking
    let (trivial_module, errors) = parse(TRIVIAL);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    c.bench_function("typecheck_trivial", |b| {
        b.iter(|| infer_module(std::hint::black_box(&trivial_module), &resolver, None));
    });

    // Stress: pre-parse, benchmark only typechecking
    let (stress_module, errors) = parse(stress_source());
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    c.bench_function("typecheck_stress", |b| {
        b.iter(|| infer_module(std::hint::black_box(&stress_module), &resolver, None));
    });
}

criterion_group!(benches, typecheck_benchmarks);
criterion_main!(benches);
