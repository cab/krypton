use criterion::{criterion_group, criterion_main, Criterion};
use krypton_codegen::emit::compile_modules;
use krypton_ir::lower::lower_all;
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_typechecker::infer::infer_module;

const TRIVIAL: &str = "fun main() -> Unit = ()";

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

fn superclass_chain_source() -> &'static str {
    static SOURCE: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    SOURCE.get_or_init(|| {
        std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/bench/superclass_chain.kr"),
        )
        .expect("failed to read superclass_chain fixture")
    })
}

fn codegen_benchmarks(c: &mut Criterion) {
    let resolver = CompositeResolver::stdlib_only();

    // Trivial: pre-parse + pre-typecheck + pre-lower, benchmark only codegen
    let (trivial_module, errors) = parse(TRIVIAL);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let (trivial_typed, trivial_interfaces) = infer_module(
        &trivial_module,
        &resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("typecheck should succeed");
    let trivial_link_ctx =
        krypton_typechecker::link_context::LinkContext::build(trivial_interfaces);
    let (trivial_ir, trivial_sources) =
        lower_all(&trivial_typed, "Bench", &trivial_link_ctx).expect("lowering should succeed");

    c.bench_function("codegen_trivial", |b| {
        b.iter(|| {
            compile_modules(
                std::hint::black_box(&trivial_ir),
                "Bench",
                true,
                &trivial_link_ctx,
                &trivial_sources,
            )
            .expect("codegen should succeed")
        });
    });

    // Stress: pre-parse + pre-typecheck + pre-lower, benchmark only codegen
    let (stress_module, errors) = parse(stress_source());
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let (stress_typed, stress_interfaces) = infer_module(
        &stress_module,
        &resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("typecheck should succeed");
    let stress_link_ctx = krypton_typechecker::link_context::LinkContext::build(stress_interfaces);
    let (stress_ir, stress_sources) =
        lower_all(&stress_typed, "Bench", &stress_link_ctx).expect("lowering should succeed");

    c.bench_function("codegen_stress", |b| {
        b.iter(|| {
            compile_modules(
                std::hint::black_box(&stress_ir),
                "Bench",
                true,
                &stress_link_ctx,
                &stress_sources,
            )
            .expect("codegen should succeed")
        });
    });

    // IR lowering alone — isolates trait-metadata and dict-resolution work
    // from parse/typecheck/codegen so per-module improvements are visible.
    c.bench_function("ir_lower_stress", |b| {
        b.iter(|| {
            lower_all(
                std::hint::black_box(&stress_typed),
                "Bench",
                &stress_link_ctx,
            )
            .expect("lower")
        });
    });

    // Superclass-chain IR lowering — isolates the repeated superclass dict
    // projection hot path inside a single function body.
    let (chain_module, errors) = parse(superclass_chain_source());
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let (chain_typed, chain_interfaces) = infer_module(
        &chain_module,
        &resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("typecheck should succeed");
    let chain_link_ctx = krypton_typechecker::link_context::LinkContext::build(chain_interfaces);
    c.bench_function("ir_lower_superclass_chain", |b| {
        b.iter(|| {
            lower_all(std::hint::black_box(&chain_typed), "Bench", &chain_link_ctx).expect("lower")
        });
    });

    // End-to-end pipeline: parse + typecheck + lower + codegen
    let source = stress_source();
    c.bench_function("pipeline_stress", |b| {
        b.iter(|| {
            let (module, _errors) = parse(std::hint::black_box(source));
            let (typed, interfaces) = infer_module(
                &module,
                &resolver,
                "test".to_string(),
                krypton_parser::ast::CompileTarget::Jvm,
            )
            .expect("typecheck");
            let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
            let (ir, sources) = lower_all(&typed, "Bench", &link_ctx).expect("lower");
            compile_modules(&ir, "Bench", true, &link_ctx, &sources).expect("codegen")
        });
    });
}

criterion_group!(benches, codegen_benchmarks);
criterion_main!(benches);
