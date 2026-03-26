# Build everything
build: build-runtime
    cargo build

# Build the Java runtime JAR
build-runtime:
    ./gradlew :runtime:build

# Run all tests (Rust + Java + JS runtime)
test: build-runtime
    cargo nextest run
    ./gradlew :runtime:test
    node runtime/js/test_runtime.mjs

# Run all tests with cargo test (no nextest)
test-cargo: build-runtime
    cargo test --workspace
    ./gradlew :runtime:test
    node runtime/js/test_runtime.mjs

# Run a .kr file
run file: build-runtime
    cargo run -- run {{file}}

# Type-check a .kr file
check file:
    cargo run -- check {{file}}

# Run Java runtime tests only
test-runtime:
    ./gradlew :runtime:test

# Run JS runtime tests only
test-js-runtime:
    node runtime/js/test_runtime.mjs

# Format Rust code
fmt:
    cargo fmt

# Lint everything
lint:
    cargo clippy --workspace
    cargo fmt -- --check

# Run all benchmarks (criterion only)
bench:
    cargo bench -p krypton-parser --bench parse_bench
    cargo bench -p krypton-typechecker --bench typecheck_bench
    cargo bench -p krypton-codegen --bench codegen_bench

# Run benchmarks for a specific crate (parser, typechecker, codegen)
bench-crate crate:
    cargo bench -p krypton-{{crate}}

# Save a named benchmark baseline
bench-save name:
    cargo bench -p krypton-parser --bench parse_bench -- --save-baseline {{name}}
    cargo bench -p krypton-typechecker --bench typecheck_bench -- --save-baseline {{name}}
    cargo bench -p krypton-codegen --bench codegen_bench -- --save-baseline {{name}}

# Compare against a named baseline
bench-compare name:
    cargo bench -p krypton-parser --bench parse_bench -- --baseline {{name}}
    cargo bench -p krypton-typechecker --bench typecheck_bench -- --baseline {{name}}
    cargo bench -p krypton-codegen --bench codegen_bench -- --baseline {{name}}
