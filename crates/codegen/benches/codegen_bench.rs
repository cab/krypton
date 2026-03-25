use criterion::{criterion_group, criterion_main, Criterion};
use krypton_codegen::emit::compile_modules;
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_typechecker::infer::infer_module;

const TRIVIAL: &str = "fun main() -> Int = 42";

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

fn codegen_benchmarks(c: &mut Criterion) {
    let resolver = CompositeResolver::stdlib_only();

    // Trivial: pre-parse + pre-typecheck, benchmark only codegen
    let (trivial_module, errors) = parse(TRIVIAL);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let trivial_typed = infer_module(&trivial_module, &resolver, String::new()).expect("typecheck should succeed");

    c.bench_function("codegen_trivial", |b| {
        b.iter(|| {
            compile_modules(std::hint::black_box(&trivial_typed), "Bench")
                .expect("codegen should succeed")
        });
    });

    // Stress: pre-parse + pre-typecheck, benchmark only codegen
    let (stress_module, errors) = parse(stress_source());
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let stress_typed = infer_module(&stress_module, &resolver, String::new()).expect("typecheck should succeed");

    c.bench_function("codegen_stress", |b| {
        b.iter(|| {
            compile_modules(std::hint::black_box(&stress_typed), "Bench")
                .expect("codegen should succeed")
        });
    });

    // End-to-end pipeline: parse + typecheck + codegen
    let source = stress_source();
    c.bench_function("pipeline_stress", |b| {
        b.iter(|| {
            let (module, _errors) = parse(std::hint::black_box(source));
            let typed = infer_module(&module, &resolver, String::new()).expect("typecheck");
            compile_modules(&typed, "Bench").expect("codegen")
        });
    });
}

criterion_group!(benches, codegen_benchmarks);
criterion_main!(benches);
