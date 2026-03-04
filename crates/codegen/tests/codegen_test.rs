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

#[test]
fn test_factorial() {
    let src = r#"
(def factorial (fn [n] (if (== n 0) 1 (* n (factorial (- n 1))))))
(def main (fn [] (factorial 10)))
"#;
    assert_eq!(run_program(src), "3628800");
}

#[test]
fn test_mutual_recursion() {
    let src = r#"
(def is_even (fn [n] (if (== n 0) true (is_odd (- n 1)))))
(def is_odd (fn [n] (if (== n 0) false (is_even (- n 1)))))
(def main (fn [] (is_even 10)))
"#;
    assert_eq!(run_program(src), "true");
}

#[test]
fn test_if_gt_positive() {
    let src = r#"
(def classify (fn [n] (if (> n 0) "positive" "non-positive")))
(def main (fn [] (classify 5)))
"#;
    assert_eq!(run_program(src), "positive");
}

#[test]
fn test_if_gt_non_positive() {
    let src = r#"
(def classify (fn [n] (if (> n 0) "positive" "non-positive")))
(def main (fn [] (classify 0)))
"#;
    assert_eq!(run_program(src), "non-positive");
}

#[test]
fn test_do_block_let_bindings() {
    assert_eq!(
        run_program("(def main (fn [] (do (let x 10) (let y 20) (+ x y))))"),
        "30"
    );
}

#[test]
fn test_hello_world() {
    assert_eq!(
        run_program(r#"(def main (fn [] "hello world"))"#),
        "hello world"
    );
}

#[test]
fn test_recur_loop() {
    let src = r#"
(def loop_fn (fn [n] (if (== n 0) 0 (recur (- n 1)))))
(def main (fn [] (loop_fn 1000000)))
"#;
    assert_eq!(run_program(src), "0");
}

#[test]
fn test_recur_countdown() {
    let src = r#"
(def sum (fn [n acc] (if (== n 0) acc (recur (- n 1) (+ acc n)))))
(def main (fn [] (sum 100 0)))
"#;
    assert_eq!(run_program(src), "5050");
}

#[test]
fn test_java_21_classfile_version() {
    let (module, errors) = parse("(def main (fn [] 42))");
    assert!(errors.is_empty());
    let bytes = compile_module(&module, "Test").expect("compile_module should succeed");
    // Class file bytes 4-5 = minor version, 6-7 = major version (big-endian)
    assert_eq!(bytes[4..6], [0, 0], "minor version should be 0");
    assert_eq!(bytes[6..8], [0, 65], "major version should be 65 (Java 21)");
}
