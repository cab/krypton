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

# Format Rust code
fmt:
    cargo fmt

# Lint everything
lint:
    cargo clippy --workspace
    cargo fmt -- --check
