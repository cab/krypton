use alang_codegen::emit::compile_module;
use alang_parser::parser::parse;
use std::io::Write;
use std::process::Command;

/// Parse source, compile to .class, run java, return trimmed stdout.
fn run_program(source: &str) -> String {
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let bytes = compile_module(&module, "Test").expect("compile_module should succeed");

    let dir = tempfile::tempdir().unwrap();
    let class_path = dir.path().join("Test.class");
    let mut f = std::fs::File::create(&class_path).unwrap();
    f.write_all(&bytes).unwrap();
    drop(f);

    let output = Command::new("java")
        .arg("-cp")
        .arg(dir.path())
        .arg("Test")
        .output()
        .expect("java command should run");

    assert!(
        output.status.success(),
        "java exited with {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

#[test]
fn test_int_addition() {
    assert_eq!(run_program("(def main (fn [] (+ 1 2)))"), "3");
}

#[test]
fn test_int_arithmetic() {
    assert_eq!(run_program("(def main (fn [] (- (* 3 4) 2)))"), "10");
}

#[test]
fn test_if_eq_string() {
    assert_eq!(
        run_program(r#"(def main (fn [] (if (== 1 1) "yes" "no")))"#),
        "yes"
    );
}

#[test]
fn test_if_neq() {
    assert_eq!(
        run_program(r#"(def main (fn [] (if (== 1 2) "yes" "no")))"#),
        "no"
    );
}

#[test]
fn test_let_binding() {
    assert_eq!(
        run_program("(def main (fn [] (do (let x 10) (+ x 5))))"),
        "15"
    );
}

#[test]
fn test_bool_literal() {
    assert_eq!(run_program("(def main (fn [] true))"), "true");
}

#[test]
fn test_string_literal() {
    assert_eq!(
        run_program(r#"(def main (fn [] "hello"))"#),
        "hello"
    );
}

#[test]
fn test_comparison_lt() {
    assert_eq!(
        run_program(r#"(def main (fn [] (if (< 1 2) "yes" "no")))"#),
        "yes"
    );
}
