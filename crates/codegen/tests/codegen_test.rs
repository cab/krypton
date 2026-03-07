use krypton_codegen::emit::compile_module;
use krypton_parser::parser::parse;
use std::io::Write;
use std::process::Command;
use tempfile;

/// Parse source, compile to .class files, run java, return trimmed stdout.
fn run_program(source: &str) -> String {
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let classes = compile_module(&module, "Test").expect("compile_module should succeed");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        let mut f = std::fs::File::create(&class_path).unwrap();
        f.write_all(bytes).unwrap();
    }

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
    assert_eq!(run_program("(def main (fn [] (println (+ 1 2))))"), "3");
}

#[test]
fn test_int_arithmetic() {
    assert_eq!(run_program("(def main (fn [] (println (- (* 3 4) 2))))"), "10");
}

#[test]
fn test_if_eq_string() {
    assert_eq!(
        run_program(r#"(def main (fn [] (println (if (== 1 1) "yes" "no"))))"#),
        "yes"
    );
}

#[test]
fn test_if_neq() {
    assert_eq!(
        run_program(r#"(def main (fn [] (println (if (== 1 2) "yes" "no"))))"#),
        "no"
    );
}

#[test]
fn test_let_binding() {
    assert_eq!(
        run_program("(def main (fn [] (do (let x 10) (println (+ x 5)))))"),
        "15"
    );
}

#[test]
fn test_bool_literal() {
    assert_eq!(run_program("(def main (fn [] (println true)))"), "true");
}

#[test]
fn test_string_literal() {
    assert_eq!(
        run_program(r#"(def main (fn [] (println "hello")))"#),
        "hello"
    );
}

#[test]
fn test_comparison_lt() {
    assert_eq!(
        run_program(r#"(def main (fn [] (println (if (< 1 2) "yes" "no"))))"#),
        "yes"
    );
}

#[test]
fn test_factorial() {
    let src = r#"
(def factorial (fn [n] (if (== n 0) 1 (* n (factorial (- n 1))))))
(def main (fn [] (println (factorial 10))))
"#;
    assert_eq!(run_program(src), "3628800");
}

#[test]
fn test_mutual_recursion() {
    let src = r#"
(def is_even (fn [n] (if (== n 0) true (is_odd (- n 1)))))
(def is_odd (fn [n] (if (== n 0) false (is_even (- n 1)))))
(def main (fn [] (println (is_even 10))))
"#;
    assert_eq!(run_program(src), "true");
}

#[test]
fn test_if_gt_positive() {
    let src = r#"
(def classify (fn [n] (if (> n 0) "positive" "non-positive")))
(def main (fn [] (println (classify 5))))
"#;
    assert_eq!(run_program(src), "positive");
}

#[test]
fn test_if_gt_non_positive() {
    let src = r#"
(def classify (fn [n] (if (> n 0) "positive" "non-positive")))
(def main (fn [] (println (classify 0))))
"#;
    assert_eq!(run_program(src), "non-positive");
}

#[test]
fn test_do_block_let_bindings() {
    assert_eq!(
        run_program("(def main (fn [] (do (let x 10) (let y 20) (println (+ x y)))))"),
        "30"
    );
}

#[test]
fn test_hello_world() {
    assert_eq!(
        run_program(r#"(def main (fn [] (println "hello world")))"#),
        "hello world"
    );
}

#[test]
fn test_recur_loop() {
    let src = r#"
(def loop_fn (fn [n] (if (== n 0) 0 (recur (- n 1)))))
(def main (fn [] (println (loop_fn 1000000))))
"#;
    assert_eq!(run_program(src), "0");
}

#[test]
fn test_recur_countdown() {
    let src = r#"
(def sum (fn [n acc] (if (== n 0) acc (recur (- n 1) (+ acc n)))))
(def main (fn [] (println (sum 100 0))))
"#;
    assert_eq!(run_program(src), "5050");
}

#[test]
fn test_java_21_classfile_version() {
    let (module, errors) = parse("(def main (fn [] 42))");
    assert!(errors.is_empty());
    let classes = compile_module(&module, "Test").expect("compile_module should succeed");
    let bytes = &classes.iter().find(|(n, _)| n == "Test").unwrap().1;
    // Class file bytes 4-5 = minor version, 6-7 = major version (big-endian)
    assert_eq!(bytes[4..6], [0, 0], "minor version should be 0");
    assert_eq!(bytes[6..8], [0, 65], "major version should be 65 (Java 21)");
}

#[test]
fn test_struct_create_and_field_access() {
    let src = r#"
(type Point (record (x Int) (y Int)))
(def main (fn [] (do (let p (Point 1 2)) (println (. p x)))))
"#;
    assert_eq!(run_program(src), "1");
}

#[test]
fn test_struct_update() {
    let src = r#"
(type Point (record (x Int) (y Int)))
(def main (fn [] (do (let p (Point 1 2)) (let p2 (.. p (x 3))) (println (. p2 x)))))
"#;
    assert_eq!(run_program(src), "3");
}

#[test]
fn test_struct_field_y() {
    let src = r#"
(type Point (record (x Int) (y Int)))
(def main (fn [] (do (let p (Point 10 20)) (println (. p y)))))
"#;
    assert_eq!(run_program(src), "20");
}

#[test]
fn test_struct_update_preserves_unchanged() {
    let src = r#"
(type Point (record (x Int) (y Int)))
(def main (fn [] (do (let p (Point 1 2)) (let p2 (.. p (x 99))) (println (. p2 y)))))
"#;
    assert_eq!(run_program(src), "2");
}

#[test]
fn test_sum_type_option() {
    let src = r#"
(type Option [a] (| (Some a) (None)))
(def main (fn [] (do (let s (Some 42)) (let n None) (println s))))
"#;
    assert_eq!(run_program(src), "Some");
}

#[test]
fn test_sum_type_sealed_interface_structure() {
    let src = r#"
(type Option [a] (| (Some a) (None)))
(def main (fn [] None))
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let classes = compile_module(&module, "Test").expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        std::fs::File::create(&path).unwrap().write_all(bytes).unwrap();
    }
    let output = Command::new("javap")
        .arg("-v")
        .arg(dir.path().join("Option.class"))
        .output()
        .expect("javap");
    let javap_out = String::from_utf8_lossy(&output.stdout);
    assert!(javap_out.contains("interface"), "should be interface");
    assert!(
        javap_out.contains("PermittedSubclasses"),
        "should have PermittedSubclasses"
    );
}

#[test]
fn test_sum_type_nullary_variant() {
    let src = r#"
(type Color (| (Red) (Green) (Blue)))
(def main (fn [] (println Green)))
"#;
    assert_eq!(run_program(src), "Green");
}

#[test]
fn test_match_option_int() {
    let src = r#"
(type Option [a] (| (Some a) (None)))
(def unwrap_or (fn [opt default]
  (match opt
    ((Some x) x)
    ((None) default))))
(def main (fn [] (println (unwrap_or (Some 42) 0))))
"#;
    assert_eq!(run_program(src), "42");
}

#[test]
fn test_match_four_variants() {
    let src = r#"
(type Dir (| (North) (South) (East) (West)))
(def to_num (fn [d]
  (match d
    ((North) 1)
    ((South) 2)
    ((East) 3)
    ((West) 4))))
(def main (fn [] (println (to_num East))))
"#;
    assert_eq!(run_program(src), "3");
}

// Lambda / closure tests

#[test]
fn test_lambda_basic() {
    let src = "(def main (fn [] (do (let f (fn [x] (+ x 1))) (println (f 5)))))";
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_lambda_capture() {
    let src = "(def main (fn [] (do (let y 10) (let f (fn [x] (+ x y))) (println (f 5)))))";
    assert_eq!(run_program(src), "15");
}

#[test]
fn test_higher_order() {
    let src = r#"
(def apply_fn (fn [f x] (f x)))
(def main (fn [] (println (apply_fn (fn [x] (+ x 1)) 5))))
"#;
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_match_nested_pattern() {
    let src = r#"
(type List [a] (| (Cons a (List a)) (Nil)))
(def second (fn [xs]
  (match xs
    ((Cons h (Cons h2 _)) h2)
    (_ 0))))
(def main (fn [] (println (second (Cons 10 (Cons 20 Nil))))))
"#;
    assert_eq!(run_program(src), "20");
}

#[test]
fn test_trait_dictionary_parameter() {
    let src = r#"
(type Point (record (x Int) (y Int)))
(trait Eq [a] (def eq [a a] Bool))
(impl Eq Point
  (def eq [x y] (if (== (. x x) (. y x)) (== (. x y) (. y y)) false)))
(def are_equal (fn [x y] (eq x y)))
(def main (fn [] (println (are_equal (Point 1 2) (Point 1 2)))))
"#;
    // First verify it runs correctly
    assert_eq!(run_program(src), "true");

    // Now verify that are_equal has an extra dictionary parameter via javap
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let classes = compile_module(&module, "Test").expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        std::fs::File::create(&path).unwrap().write_all(bytes).unwrap();
    }
    let output = Command::new("javap")
        .arg("-p")
        .arg(dir.path().join("Test.class"))
        .output()
        .expect("javap");
    let javap_out = String::from_utf8_lossy(&output.stdout);
    // are_equal should have 3 params: dict (Object) + x (Object) + y (Object)
    assert!(
        javap_out.contains("are_equal(java.lang.Object, java.lang.Object, java.lang.Object)"),
        "are_equal should have 3 Object params (dict + x + y), javap output:\n{javap_out}"
    );
}
