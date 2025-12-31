# Examples

This directory contains example alang programs and utilities.

## Example Programs

- **hello.al** - Simple valid program demonstrating type and function declarations
- **error_demo.al** - Intentionally broken program to demonstrate parser error reporting
- **lex_error.al** - Invalid token to demonstrate lexer error reporting

## Example Binaries

### test_parser

A simple command-line tool to parse alang source files and display errors.

```bash
# Parse a valid file
cargo run --example test_parser examples/hello.al

# See beautiful error messages
cargo run --example test_parser examples/error_demo.al
```

The error output uses [ariadne](https://docs.rs/ariadne) to display source code context with colored annotations pointing to the exact location of errors.
