default:
    @echo "krypton just tasks"
    @echo ""
    @echo "Common workflows:"
    @echo "  just build                Build compiler + all runtime artifacts"
    @echo "  just test                 Run Rust tests + JVM runtime tests + JS runtime tests"
    @echo "  just test-cargo           Run cargo test workspace + both runtime test suites"
    @echo ""
    @echo "Runtime tasks:"
    @echo "  just build-runtime        Build JVM and JS runtime artifacts"
    @echo "  just build-runtime-jvm    Build the JVM runtime JAR"
    @echo "  just build-runtime-js     Build the JS runtime bundle"
    @echo "  just test-runtime         Run JVM and JS runtime tests"
    @echo "  just test-runtime-jvm     Run JVM runtime tests"
    @echo "  just test-runtime-js      Run JS runtime tests"
    @echo ""
    @echo "Targeted tasks:"
    @echo "  just test-js             Run JS target fixture tests"
    @echo "  just run path/to/file.kr Compile and run a .kr file"
    @echo "  just check path/to/file.kr Type-check a .kr file"
    @echo ""
    @echo "Run 'just --list' for the full task list."

# Build everything
build: build-runtime
    cargo build

# Build all runtime artifacts
build-runtime: build-runtime-jvm build-runtime-js

# Build the JVM runtime JAR
build-runtime-jvm:
    ./gradlew :runtime:build

# Build the JS runtime bundle
build-runtime-js:
    npm --prefix runtime/js run build

# Run all tests (Rust + Java + JS runtime)
test: build-runtime
    cargo nextest run
    just test-runtime

# Run all tests with cargo test (no nextest)
test-cargo: build-runtime
    cargo test --workspace
    just test-runtime

# Run a .kr file
run file: build-runtime
    cargo run -- run {{file}}

# Type-check a .kr file
check file:
    cargo run -- check {{file}}

# Run all runtime tests
test-runtime: test-runtime-jvm test-runtime-js

# Run JVM runtime tests only
test-runtime-jvm:
    ./gradlew :runtime:test

# Run JS target fixture tests only (codegen_js crate)
test-js:
    cargo nextest run -p krypton-codegen-js

# Run JS runtime tests only
test-runtime-js: build-runtime-js
    npm --prefix runtime/js test

# Backward-compatible alias for JS runtime tests
test-js-runtime: test-runtime-js

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

# Generate a large Krypton project for compile-time benchmarking
bench-gen *ARGS:
    python3 bench/gen_bench.py {{ARGS}}

# Time type-checking of the generated benchmark (run bench-gen first)
bench-compile *ARGS:
    cargo run --release -- check bench/generated/main.kr --timings {{ARGS}}

# Time full compilation (parse + typecheck + codegen + emit) of the generated benchmark
bench-compile-full target="jvm" *ARGS:
    cargo run --release -- compile bench/generated/main.kr --timings --target {{target}} -o /tmp/kr_bench_out {{ARGS}}
