use krypton_codegen::emit::compile_module;
use krypton_parser::parser::parse;
use krypton_typechecker::infer::infer_module;
use krypton_typechecker::module_resolver::CompositeResolver;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use tempfile;

const PRINTLN_EXTERN: &str = r#"extern "krypton.runtime.KryptonIO" { fun println(Object) -> Unit }"#;

fn find_runtime_jar() -> Option<PathBuf> {
    let jar = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../runtime/build/libs/krypton-runtime.jar");
    if jar.exists() { Some(jar) } else { None }
}

fn build_classpath(class_dir: &std::path::Path) -> String {
    match find_runtime_jar() {
        Some(jar) => format!("{}:{}", class_dir.display(), jar.display()),
        None => class_dir.display().to_string(),
    }
}

/// Parse source, compile to .class files, run java, return trimmed stdout.
fn run_program(source: &str) -> String {
    let full_source = format!("{PRINTLN_EXTERN}\n{source}");
    let (module, errors) = parse(&full_source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let typed_modules = infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check should succeed");
    let classes = compile_module(&typed_modules[0], "Test").expect("compile_module should succeed");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        let mut f = std::fs::File::create(&class_path).unwrap();
        f.write_all(bytes).unwrap();
    }

    let output = Command::new("java")
        .arg("-cp")
        .arg(build_classpath(dir.path()))
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
    assert_eq!(run_program("fun main() = println(1 + 2)"), "3");
}

#[test]
fn test_int_arithmetic() {
    assert_eq!(run_program("fun main() = println(3 * 4 - 2)"), "10");
}

#[test]
fn test_if_eq_string() {
    assert_eq!(
        run_program(r#"fun main() = println(if 1 == 1 { "yes" } else { "no" })"#),
        "yes"
    );
}

#[test]
fn test_if_neq() {
    assert_eq!(
        run_program(r#"fun main() = println(if 1 == 2 { "yes" } else { "no" })"#),
        "no"
    );
}

#[test]
fn test_let_binding() {
    assert_eq!(
        run_program("fun main() = { let x = 10; println(x + 5) }"),
        "15"
    );
}

#[test]
fn test_bool_literal() {
    assert_eq!(run_program("fun main() = println(true)"), "true");
}

#[test]
fn test_string_literal() {
    assert_eq!(
        run_program(r#"fun main() = println("hello")"#),
        "hello"
    );
}

#[test]
fn test_comparison_lt() {
    assert_eq!(
        run_program(r#"fun main() = println(if 1 < 2 { "yes" } else { "no" })"#),
        "yes"
    );
}

#[test]
fn test_factorial() {
    let src = r#"
fun factorial(n) = if n == 0 { 1 } else { n * factorial(n - 1) }
fun main() = println(factorial(10))
"#;
    assert_eq!(run_program(src), "3628800");
}

#[test]
fn test_mutual_recursion() {
    let src = r#"
fun is_even(n) = if n == 0 { true } else { is_odd(n - 1) }
fun is_odd(n) = if n == 0 { false } else { is_even(n - 1) }
fun main() = println(is_even(10))
"#;
    assert_eq!(run_program(src), "true");
}

#[test]
fn test_if_gt_positive() {
    let src = r#"
fun classify(n) = if n > 0 { "positive" } else { "non-positive" }
fun main() = println(classify(5))
"#;
    assert_eq!(run_program(src), "positive");
}

#[test]
fn test_if_gt_non_positive() {
    let src = r#"
fun classify(n) = if n > 0 { "positive" } else { "non-positive" }
fun main() = println(classify(0))
"#;
    assert_eq!(run_program(src), "non-positive");
}

#[test]
fn test_do_block_let_bindings() {
    assert_eq!(
        run_program("fun main() = { let x = 10; let y = 20; println(x + y) }"),
        "30"
    );
}

#[test]
fn test_hello_world() {
    assert_eq!(
        run_program(r#"fun main() = println("hello world")"#),
        "hello world"
    );
}

#[test]
fn test_recur_loop() {
    let src = r#"
fun loop_fn(n) = if n == 0 { 0 } else { recur(n - 1) }
fun main() = println(loop_fn(1000000))
"#;
    assert_eq!(run_program(src), "0");
}

#[test]
fn test_recur_countdown() {
    let src = r#"
fun sum(n, acc) = if n == 0 { acc } else { recur(n - 1, acc + n) }
fun main() = println(sum(100, 0))
"#;
    assert_eq!(run_program(src), "5050");
}

#[test]
fn test_java_21_classfile_version() {
    let (module, errors) = parse("fun main() = 42");
    assert!(errors.is_empty());
    let typed_module = &infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check")[0];
    let classes = compile_module(typed_module, "Test").expect("compile_module should succeed");
    let bytes = &classes.iter().find(|(n, _)| n == "Test").unwrap().1;
    // Class file bytes 4-5 = minor version, 6-7 = major version (big-endian)
    assert_eq!(bytes[4..6], [0, 0], "minor version should be 0");
    assert_eq!(bytes[6..8], [0, 65], "major version should be 65 (Java 21)");
}

#[test]
fn test_struct_create_and_field_access() {
    let src = r#"
type Point = { x: Int, y: Int }
fun main() = { let p = Point(1, 2); println(p.x) }
"#;
    assert_eq!(run_program(src), "1");
}

#[test]
fn test_struct_update() {
    let src = r#"
type Point = { x: Int, y: Int }
fun main() = { let p = Point(1, 2); let p2 = { p | x = 3 }; println(p2.x) }
"#;
    assert_eq!(run_program(src), "3");
}

#[test]
fn test_struct_field_y() {
    let src = r#"
type Point = { x: Int, y: Int }
fun main() = { let p = Point(10, 20); println(p.y) }
"#;
    assert_eq!(run_program(src), "20");
}

#[test]
fn test_struct_update_preserves_unchanged() {
    let src = r#"
type Point = { x: Int, y: Int }
fun main() = { let p = Point(1, 2); let p2 = { p | x = 99 }; println(p2.y) }
"#;
    assert_eq!(run_program(src), "2");
}

#[test]
fn test_sum_type_option() {
    let src = r#"
type Option[a] = Some(a) | None
fun main() = { let s = Some(42); let n = None; println(s) }
"#;
    assert_eq!(run_program(src), "Some");
}

#[test]
fn test_sum_type_sealed_interface_structure() {
    let src = r#"
type Option[a] = Some(a) | None
fun main() = None
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let typed_module = &infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check")[0];
    let classes = compile_module(typed_module, "Test").expect("compile");
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
type Color = Red | Green | Blue
fun main() = println(Green)
"#;
    assert_eq!(run_program(src), "Green");
}

#[test]
fn test_match_option_int() {
    let src = r#"
type Option[a] = Some(a) | None
fun unwrap_or(opt, default) = match opt { Some(x) => x, None => default }
fun main() = println(unwrap_or(Some(42), 0))
"#;
    assert_eq!(run_program(src), "42");
}

#[test]
fn test_match_four_variants() {
    let src = r#"
type Dir = North | South | East | West
fun to_num(d) = match d { North => 1, South => 2, East => 3, West => 4 }
fun main() = println(to_num(East))
"#;
    assert_eq!(run_program(src), "3");
}

// Lambda / closure tests

#[test]
fn test_lambda_basic() {
    let src = "fun main() = { let f = x => x + 1; println(f(5)) }";
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_lambda_capture() {
    let src = "fun main() = { let y = 10; let f = x => x + y; println(f(5)) }";
    assert_eq!(run_program(src), "15");
}

#[test]
fn test_higher_order() {
    let src = r#"
fun apply_fn(f, x) = f(x)
fun main() = println(apply_fn(x => x + 1, 5))
"#;
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_match_nested_pattern() {
    let src = r#"
type List[a] = Cons(a, List[a]) | Nil
fun second(xs) = match xs { Cons(h, Cons(h2, _)) => h2, _ => 0 }
fun main() = println(second(Cons(10, Cons(20, Nil))))
"#;
    assert_eq!(run_program(src), "20");
}

#[test]
fn test_trait_dictionary_parameter() {
    let src = r#"
type Point = { x: Int, y: Int }
trait Eq[a] { fun eq(_0: a, _1: a) -> Bool }
impl Eq[Point] { fun eq(x, y) = if x.x == y.x { x.y == y.y } else { false } }
fun are_equal(x, y) = eq(x, y)
fun main() = println(are_equal(Point(1, 2), Point(1, 2)))
"#;
    // First verify it runs correctly
    assert_eq!(run_program(src), "true");

    // Now verify that are_equal has an extra dictionary parameter via javap
    let full_src = format!("{PRINTLN_EXTERN}\n{src}");
    let (module, errors) = parse(&full_src);
    assert!(errors.is_empty());
    let typed_module = &infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check")[0];
    let classes = compile_module(typed_module, "Test").expect("compile");
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

#[test]
fn test_typed_module_direct() {
    // Demonstrates that codegen tests can supply TypedModule directly
    let source = format!("{PRINTLN_EXTERN}\nfun main() = println(42)");
    let (module, errors) = parse(&source);
    assert!(errors.is_empty());
    let typed_module = &infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check")[0];
    let classes = compile_module(typed_module, "Test").expect("codegen");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        std::fs::File::create(&class_path).unwrap().write_all(bytes).unwrap();
    }

    let output = Command::new("java")
        .arg("-cp")
        .arg(build_classpath(dir.path()))
        .arg("Test")
        .output()
        .expect("java command should run");

    assert!(output.status.success(), "java exited with {}", output.status);
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}
