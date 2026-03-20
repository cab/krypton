# Build everything
build: build-runtime
    cargo build

# Build the Java runtime JAR
build-runtime:
    ./gradlew :runtime:build

# Run all tests (Rust + Java)
test: build-runtime
    cargo test --workspace
    ./gradlew :runtime:test

# Run a .kr file
run file: build-runtime
    cargo run -- run {{file}}

# Type-check a .kr file
check file:
    cargo run -- check {{file}}

# Run Java runtime tests only
test-runtime:
    ./gradlew :runtime:test

# Format Rust code
fmt:
    cargo fmt

# Lint everything
lint:
    cargo clippy --workspace
    cargo fmt -- --check

# Run all benchmarks
bench:
    cargo bench

# Run benchmarks for a specific crate (parser, typechecker, codegen)
bench-crate crate:
    cargo bench -p krypton-{{crate}}

# Save a named benchmark baseline
bench-save name:
    cargo bench -- --save-baseline {{name}}

# Compare against a named baseline
bench-compare name:
    cargo bench -- --baseline {{name}}
