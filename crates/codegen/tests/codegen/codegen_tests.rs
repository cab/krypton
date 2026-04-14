use krypton_codegen::emit::compile_modules;
use krypton_ir::lower::lower_all;
use krypton_parser::parser::parse;
use krypton_typechecker::infer::infer_module;
use krypton_typechecker::typed_ast::TypedModule;

use krypton_modules::module_resolver::CompositeResolver;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

const PRINTLN_EXTERN: &str =
    r#"extern java "krypton.runtime.KryptonIO" { fun println[a](x: a) -> Unit }"#;

fn find_runtime_jar() -> Option<PathBuf> {
    let jar = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../extern/jvm/runtime/build/libs/krypton-runtime.jar");
    if jar.exists() {
        Some(jar)
    } else {
        None
    }
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

    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check should succeed");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        lower_all(&typed_modules, "Test", &link_ctx).expect("lowering should succeed");
    let classes = compile_modules(&ir_modules, "Test", &link_ctx, &module_sources)
        .expect("compile_module_standalone should succeed");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = class_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
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

fn javap_output(class_file: &std::path::Path, verbose: bool) -> String {
    let mut cmd = Command::new("javap");
    if verbose {
        cmd.arg("-v");
    } else {
        cmd.arg("-p");
    }
    let output = cmd.arg(class_file).output().expect("javap");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn compile_typed_modules(
    typed_modules: &[TypedModule],
    link_ctx: &krypton_typechecker::link_context::LinkContext,
) -> tempfile::TempDir {
    let (ir_modules, module_sources) =
        lower_all(typed_modules, "Test", link_ctx).expect("lowering should succeed");
    let classes = compile_modules(&ir_modules, "Test", link_ctx, &module_sources)
        .expect("compile_modules should succeed");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = class_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        let mut f = std::fs::File::create(&class_path).unwrap();
        f.write_all(bytes).unwrap();
    }
    dir
}

fn compile_java_sources(class_dir: &Path, sources: &[(&str, &str)]) {
    if sources.is_empty() {
        return;
    }

    let mut java_files = Vec::new();
    for (class_name, source) in sources {
        let java_path = class_dir.join(format!("{class_name}.java"));
        std::fs::write(&java_path, source).unwrap();
        java_files.push(java_path);
    }

    let mut cmd = Command::new("javac");
    cmd.arg("-d").arg(class_dir);
    for path in &java_files {
        cmd.arg(path);
    }
    let output = cmd.output().expect("javac should run");
    assert!(
        output.status.success(),
        "javac exited with {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

fn compile_typed_modules_with_java_sources(
    typed_modules: &[TypedModule],
    sources: &[(&str, &str)],
    link_ctx: &krypton_typechecker::link_context::LinkContext,
) -> tempfile::TempDir {
    let dir = compile_typed_modules(typed_modules, link_ctx);
    compile_java_sources(dir.path(), sources);
    dir
}

fn run_typed_modules_with_java_sources(
    typed_modules: &[TypedModule],
    sources: &[(&str, &str)],
    link_ctx: &krypton_typechecker::link_context::LinkContext,
) -> String {
    let dir = compile_typed_modules_with_java_sources(typed_modules, sources, link_ctx);
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

fn infer_typed_modules(
    source: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> (
    Vec<TypedModule>,
    Vec<krypton_typechecker::module_interface::ModuleInterface>,
) {
    let (module, errors) = parse(source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    infer_module(
        &module,
        resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check should succeed")
}

const NULLABLE_HOST_JAVA: &str = r#"
public final class NullableHost {
    public static String maybe_string(String s) {
        return "none".equals(s) ? null : s.toUpperCase();
    }

    public static Long maybe_int(String s) {
        return "none".equals(s) ? null : Long.valueOf(Long.parseLong(s));
    }

    public static Double maybe_float(String s) {
        return "none".equals(s) ? null : Double.valueOf(Double.parseDouble(s));
    }

    public static String definitely_string(String s) {
        return s.toUpperCase();
    }
}
"#;

const CONSTRAINED_HOST_JAVA: &str = r#"
public final class ConstrainedHost {
    public static String render_key(String x, Object eqDict, Object hashDict) {
        if (eqDict == null || hashDict == null) {
            throw new RuntimeException("missing dict");
        }
        return x.toUpperCase();
    }
}
"#;

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
    assert_eq!(run_program(r#"fun main() = println("hello")"#), "hello");
}

#[test]
fn nullable_extern_wrappers_produce_expected_options() {
    let source = r#"
extern java "NullableHost" {
    @nullable fun maybe_string(s: String) -> Option[String]
    @nullable fun maybe_int(s: String) -> Option[Int]
    @nullable fun maybe_float(s: String) -> Option[Float]
    fun definitely_string(s: String) -> String
}

fun main() = {
    println(maybe_string("none"))
    println(maybe_string("hi"))
    println(maybe_int("none"))
    println(maybe_int("42"))
    println(maybe_float("none"))
    println(maybe_float("3.5"))
    println(definitely_string("ok"))
}
"#;

    let (typed_modules, interfaces) =
        infer_typed_modules(source, &CompositeResolver::stdlib_only());
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let output = run_typed_modules_with_java_sources(
        &typed_modules,
        &[("NullableHost", NULLABLE_HOST_JAVA)],
        &link_ctx,
    );

    assert_eq!(
        output,
        "None\nSome(HI)\nNone\nSome(42)\nNone\nSome(3.5)\nOK"
    );
}

#[test]
fn imported_nullable_extern_calls_route_through_declaring_module_wrapper() {
    let temp = tempfile::tempdir().unwrap();
    std::fs::write(
        temp.path().join("nullable_lib.kr"),
        r#"
extern java "NullableHost" {
    @nullable pub fun maybe_int(s: String) -> Option[Int]
}
"#,
    )
    .unwrap();

    let source = r#"
import nullable_lib.{maybe_int}

fun main() = println(maybe_int("42"))
"#;
    let resolver = CompositeResolver::with_source_root(temp.path().to_path_buf());
    let (typed_modules, interfaces) = infer_typed_modules(source, &resolver);
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);

    let test_output = javap_output(&dir.path().join("Test.class"), true);
    assert!(
        test_output
            .contains("Method nullable_lib.maybe_int:(Ljava/lang/String;)Lcore/option/Option;")
            || test_output
                .contains("Method nullable_lib.maybe_int:(Ljava/lang/String;)Ljava/lang/Object;"),
        "expected imported call to target nullable_lib wrapper, got:\n{test_output}"
    );

    let lib_output = javap_output(&dir.path().join("nullable_lib.class"), true);
    assert!(
        lib_output.contains("public static core.option.Option maybe_int(java.lang.String);"),
        "expected declaring module to emit nullable wrapper, got:\n{lib_output}"
    );
}

#[test]
fn wrapper_bytecode_is_emitted_for_all_externs() {
    let source = r#"
extern java "NullableHost" {
    @nullable fun maybe_string(s: String) -> Option[String]
    @nullable fun maybe_int(s: String) -> Option[Int]
    @nullable fun maybe_float(s: String) -> Option[Float]
    fun definitely_string(s: String) -> String
}

fun main() = {
    println(maybe_string("hi"))
    println(maybe_int("42"))
    println(maybe_float("3.5"))
    println(definitely_string("ok"))
}
"#;

    let (typed_modules, interfaces) =
        infer_typed_modules(source, &CompositeResolver::stdlib_only());
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules_with_java_sources(
        &typed_modules,
        &[("NullableHost", NULLABLE_HOST_JAVA)],
        &link_ctx,
    );
    let javap_out = javap_output(&dir.path().join("Test.class"), true);

    // All externs (nullable and non-nullable) get wrapper methods on the defining class.
    assert!(javap_out.contains("public static core.option.Option maybe_string(java.lang.String);"));
    assert!(javap_out.contains("public static core.option.Option maybe_int(java.lang.String);"));
    assert!(javap_out.contains("public static core.option.Option maybe_float(java.lang.String);"));
    assert!(
        javap_out.contains("public static java.lang.String definitely_string(java.lang.String);")
    );
    assert!(javap_out.contains("java/lang/Long.longValue:()J"));
    assert!(javap_out.contains("java/lang/Double.doubleValue:()D"));
    assert!(javap_out.contains("Field core/option/Option$None.INSTANCE:Lcore/option/Option$None;"));
}

#[test]
fn constrained_java_extern_appends_nonbridged_dict_args() {
    let source = r#"
extern java "ConstrainedHost" {
    fun render_key[a](x: String) -> String where a: Eq + Hash
}

fun main() = println(render_key[String]("hi"))
"#;

    let (typed_modules, interfaces) =
        infer_typed_modules(source, &CompositeResolver::stdlib_only());
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let output = run_typed_modules_with_java_sources(
        &typed_modules,
        &[("ConstrainedHost", CONSTRAINED_HOST_JAVA)],
        &link_ctx,
    );
    assert_eq!(output, "HI");

    let dir = compile_typed_modules_with_java_sources(
        &typed_modules,
        &[("ConstrainedHost", CONSTRAINED_HOST_JAVA)],
        &link_ctx,
    );
    let wrapper_output = javap_output(&dir.path().join("Test.class"), false);
    assert!(
        wrapper_output.contains("public static java.lang.String render_key(java.lang.Object, java.lang.Object, java.lang.String);"),
        "expected wrapper signature with leading dict params, got:\n{wrapper_output}"
    );

    let verbose_output = javap_output(&dir.path().join("Test.class"), true);
    assert!(
        verbose_output.contains("Method ConstrainedHost.render_key:(Ljava/lang/String;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/String;"),
        "expected raw host call to append dict args after user args, got:\n{verbose_output}"
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
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        lower_all(&typed_modules, "Test", &link_ctx).expect("lowering should succeed");
    let classes = compile_modules(&ir_modules, "Test", &link_ctx, &module_sources)
        .expect("compile_module_standalone should succeed");
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
fun main() = { let s = Some(42); let n = None; let _ = match n { Some(_) => 0, None => 0 }; println(s) }
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
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        lower_all(&typed_modules, "Test", &link_ctx).expect("lowering should succeed");
    let classes =
        compile_modules(&ir_modules, "Test", &link_ctx, &module_sources).expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::File::create(&path)
            .unwrap()
            .write_all(bytes)
            .unwrap();
    }
    let output = Command::new("javap")
        .arg("-v")
        .arg(dir.path().join("test/Option.class"))
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
    let src = "fun main() = { let f = x -> x + 1; println(f(5)) }";
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_lambda_capture() {
    let src = "fun main() = { let y = 10; let f = x -> x + y; println(f(5)) }";
    assert_eq!(run_program(src), "15");
}

#[test]
fn test_higher_order() {
    let src = r#"
fun apply_fn(f, x) = f(x)
fun main() = println(apply_fn(x -> x + 1, 5))
"#;
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_own_fn_param() {
    let src = r#"
fun call_once(f: ~() -> String) -> String = f()
fun make_fn() -> String = "hello"
fun main() = println(call_once(make_fn))
"#;
    assert_eq!(run_program(src), "hello");
}

#[test]
fn test_named_function_reference_let_call() {
    let src = r#"
fun add1(x) = x + 1
fun main() = { let f = add1; println(f(5)) }
"#;
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_named_function_reference_higher_order_arg() {
    let src = r#"
fun add1(x) = x + 1
fun apply_fn(f, x) = f(x)
fun main() = println(apply_fn(add1, 5))
"#;
    assert_eq!(run_program(src), "6");
}

#[test]
fn test_struct_constructor_reference() {
    let src = r#"
type Player = { name: String, score: Int }
fun main() = {
    let mk = Player;
    let p = mk("hi", 1);
    println(p.name);
    println(p.score)
}
"#;
    assert_eq!(run_program(src), "hi\n1");
}

#[test]
fn test_lambda_string_param() {
    let src = r#"
fun apply(x, f) = f(x)
fun main() = println(apply("hi", x -> x + "f"))
"#;
    assert_eq!(run_program(src), "hif");
}

#[test]
fn test_lambda_string_capture() {
    let src = r#"
fun main() = {
    let s = "hello";
    let f = x -> s + x;
    println(f(" world"))
}
"#;
    assert_eq!(run_program(src), "hello world");
}

#[test]
fn test_variant_constructor_reference() {
    let src = r#"
type Option[a] = Some(a) | None
fun main() = {
    let wrap = Some;
    match wrap(42) {
        Some(x) => println(x),
        None => println(0),
    }
}
"#;
    assert_eq!(run_program(src), "42");
}

#[test]
fn test_qualified_nullary_constructor_reference() {
    let src = r#"
import core/option
fun main() = {
    let f: Option[Int] = option.None;
    println(f)
}
"#;
    assert_eq!(run_program(src), "None");
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
impl Eq[Point] { fun eq(x, y) = if x.x == y.x { x.y == y.y } else { false } }
fun are_equal[a](x: a, y: a) -> Bool where a: Eq = eq(x, y)
fun main() = println(are_equal(Point(1, 2), Point(1, 2)))
"#;
    // First verify it runs correctly
    assert_eq!(run_program(src), "true");

    // Now verify that are_equal has an extra dictionary parameter via javap
    let full_src = format!("{PRINTLN_EXTERN}\n{src}");
    let (module, errors) = parse(&full_src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        lower_all(&typed_modules, "Test", &link_ctx).expect("lowering should succeed");
    let classes =
        compile_modules(&ir_modules, "Test", &link_ctx, &module_sources).expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::File::create(&path)
            .unwrap()
            .write_all(bytes)
            .unwrap();
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
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        lower_all(&typed_modules, "Test", &link_ctx).expect("lowering should succeed");
    let classes =
        compile_modules(&ir_modules, "Test", &link_ctx, &module_sources).expect("codegen");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = class_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::File::create(&class_path)
            .unwrap()
            .write_all(bytes)
            .unwrap();
    }

    let output = Command::new("java")
        .arg("-cp")
        .arg(build_classpath(dir.path()))
        .arg("Test")
        .output()
        .expect("java command should run");

    assert!(
        output.status.success(),
        "java exited with {}",
        output.status
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

#[test]
fn test_unused_parameterized_instance_not_in_constant_pool() {
    // Option deriving Show creates parameterized Show$Option,
    // but main() never calls show() — so Show$Option should not be in the CP
    let src = r#"
type Option[a] = Some(a) | None deriving (Show)
fun main() = println(Some(42))
"#;
    let full_src = format!("{PRINTLN_EXTERN}\n{src}");
    let (module, errors) = parse(&full_src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        lower_all(&typed_modules, "Test", &link_ctx).expect("lowering should succeed");
    let classes =
        compile_modules(&ir_modules, "Test", &link_ctx, &module_sources).expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::File::create(&path)
            .unwrap()
            .write_all(bytes)
            .unwrap();
    }
    let output = Command::new("javap")
        .arg("-v")
        .arg(dir.path().join("Test.class"))
        .output()
        .expect("javap");
    let javap_out = String::from_utf8_lossy(&output.stdout);
    // Check that Show$Option doesn't appear as a Class entry in the constant pool.
    // It may appear as a substring of method names like Show$Option$show, so we
    // check specifically for the javap class reference format.
    assert!(
        !javap_out.contains("// class Show$Option"),
        "unused parameterized instance Show$Option should not appear as a class in constant pool:\n{javap_out}"
    );
}

#[test]
fn test_parameterized_instance_show_option() {
    let src = r#"
type Maybe[a] = Just(a) | Nothing deriving (Show)
fun main() = println(show(Just(42)))
"#;
    assert_eq!(run_program(src), "Just(42)");
}

#[test]
fn test_record_function_field_codegen() {
    let src = r#"
type Player2 = { name: String, score: (Int) -> Int }
impl Show[Player2] {
    fun show(x: Player2) -> String = x.name
}
fun main() = println(show(Player2 { name = "hi", score = x -> x }))
"#;
    assert_eq!(run_program(src), "hi");
}

#[test]
fn test_constrained_instance_dictionary_passing_runtime() {
    let src = r#"
trait Render[a] {
    fun render(x: a) -> String
}
type Wrap[a] = Wrap(a) | Empty
impl Render[Int] {
    fun render(x: Int) -> String = "x"
}
impl[a] Render[Wrap[a]] where a: Render {
    fun render(value: Wrap[a]) -> String = match value {
        Wrap(inner) => "Wrap(" + render(inner) + ")",
        Empty => "Empty",
    }
}
fun main() = println(render(Wrap(42)))
"#;
    assert_eq!(run_program(src), "Wrap(x)");
}

#[test]
fn test_constrained_instance_dictionary_passing_nested_runtime() {
    let src = r#"
trait Render[a] {
    fun render(x: a) -> String
}
type Wrap[a] = Wrap(a) | Empty
impl Render[Int] {
    fun render(x: Int) -> String = "x"
}
impl[a] Render[Wrap[a]] where a: Render {
    fun render(value: Wrap[a]) -> String = match value {
        Wrap(inner) => "Wrap(" + render(inner) + ")",
        Empty => "Empty",
    }
}
fun main() = println(render(Wrap(Wrap(42))))
"#;
    assert_eq!(run_program(src), "Wrap(Wrap(x))");
}

#[test]
fn test_constrained_instance_dictionary_forwarding_from_polymorphic_context() {
    // Tests that a polymorphic wrapper function can forward dict params to trait calls
    let src = r#"
import core/show.{Show, show}
fun show_it[a](x: a) -> String where a: Show = show(x)
fun main() = println(show_it(42))
"#;
    assert_eq!(run_program(src), "42");
}

#[test]
fn test_constrained_instance_class_captures_dictionary_parameter() {
    let src = r#"
trait Render[a] {
    fun render(x: a) -> String
}
type Wrap[a] = Wrap(a) | Empty
impl Render[Int] {
    fun render(x: Int) -> String = "x"
}
impl[a] Render[Wrap[a]] where a: Render {
    fun render(value: Wrap[a]) -> String = match value {
        Wrap(inner) => "Wrap(" + render(inner) + ")",
        Empty => "Empty",
    }
}
fun main() = println(render(Wrap(42)))
"#;
    let full_src = format!("{PRINTLN_EXTERN}\n{src}");
    let (module, errors) = parse(&full_src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let (ir_modules, module_sources) =
        lower_all(&typed_modules, "Test", &link_ctx).expect("lowering should succeed");
    let classes =
        compile_modules(&ir_modules, "Test", &link_ctx, &module_sources).expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::File::create(&path)
            .unwrap()
            .write_all(bytes)
            .unwrap();
    }
    // Find the parameterized instance class for Render[Wrap[a]]
    let render_wrap_class = classes
        .iter()
        .find(|(n, _)| n.contains("Render$$Wrap"))
        .expect("should have a Render$$Wrap* instance class");
    let class_output = javap_output(
        &dir.path().join(format!("{}.class", render_wrap_class.0)),
        false,
    );
    assert!(
        class_output.contains("java.lang.Object dict0;"),
        "expected constrained instance to store dictionary field, javap output:\n{class_output}"
    );

    let test_output = javap_output(&dir.path().join("Test.class"), true);
    let expected_ctor = format!(
        "Method {}.\"<init>\":(Ljava/lang/Object;)V",
        render_wrap_class.0
    );
    assert!(
        test_output.contains(&expected_ctor),
        "expected constrained instance construction with dictionary arg, javap output:\n{test_output}"
    );
}

#[test]
fn test_constrained_function_ref_capture_runtime() {
    let src = r#"
import core/show.{Show}

fun show_it[a](x: a) -> String where a: Show = show(x)

fun main() = {
  let f = show_it[Int]
  println(f(42) == "42")
}
"#;
    assert_eq!(run_program(src), "true");
}

#[test]
fn test_constrained_function_ref_capture_from_polymorphic_scope_runtime() {
    let src = r#"
import core/show.{Show}

fun show_it[a](x: a) -> String where a: Show = show(x)

fun use_it[a](x: a) -> String where a: Show = {
  let f = show_it
  f(x)
}

fun main() = println(use_it(42) == "42")
"#;
    assert_eq!(run_program(src), "true");
}

#[test]
fn test_eta_expansion_of_constrained_function_runtime() {
    let src = r#"
import core/show.{Show}

fun show_it[a](x: a) -> String where a: Show = show(x)

fun main() = {
  let f = y -> show_it[Int](y)
  println(f(42) == "42")
}
"#;
    assert_eq!(run_program(src), "true");
}

#[test]
fn test_constrained_function_ref_capture_uses_invokedynamic_with_capture() {
    let src = r#"
import core/show.{Show}

fun show_it[a](x: a) -> String where a: Show = show(x)
fun stringify(x: Int) -> String = show_it(x)

fun main() = {
  let constrained = show_it[Int]
  let plain = stringify
  println(constrained(1) + plain(2))
}
"#;
    let full_source = format!("{PRINTLN_EXTERN}\n{src}");
    let (module, errors) = parse(&full_source);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check should succeed");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);
    let test_output = javap_output(&dir.path().join("Test.class"), true);
    assert!(
        test_output.contains("InvokeDynamic")
            && test_output.contains("apply:(Ljava/lang/Object;)Lkrypton/runtime/Fun1;"),
        "expected constrained function ref to capture a dictionary, javap output:\n{test_output}"
    );
    assert!(
        test_output.contains("apply:()Lkrypton/runtime/Fun1;"),
        "expected unconstrained function ref to keep zero-capture path, javap output:\n{test_output}"
    );
}

#[test]
fn test_zero_arg_trait_method() {
    let src = r#"
trait Default[a] {
    fun default() -> a
}

impl Default[Int] {
    fun default() = 42
}

fun main() = println(default[Int]())
"#;
    assert_eq!(run_program(src), "42");

    // Verify javap output contains the instance class and interface
    let full_src = format!("{PRINTLN_EXTERN}\n{src}");
    let (module, errors) = parse(&full_src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);
    let javap_out = javap_output(&dir.path().join("Test.class"), false);
    assert!(
        javap_out.contains("Default$$Int"),
        "expected Default$$Int instance class in javap output:\n{javap_out}"
    );
}

#[test]
fn test_match_bool_literals() {
    let src = r#"
fun describe(b: Bool) -> String = if b { "yes" } else { "no" }

fun main() = {
  println(describe(true))
  println(describe(false))
}
"#;
    assert_eq!(run_program(src), "yes\nno");
}

#[test]
fn test_match_three_variants() {
    let src = r#"
type Color = Red | Green | Blue

fun name(c: Color) -> String = match c {
  Red => "red",
  Green => "green",
  Blue => "blue",
}

fun main() = { println(name(Red)); println(name(Green)); println(name(Blue)) }
"#;
    assert_eq!(run_program(src), "red\ngreen\nblue");
}

#[test]
fn test_match_default_checkcast() {
    let src = r#"
type Shape = Circle(Int) | Square(Int) | Triangle(Int)

fun describe(s: Shape) -> String = match s {
  Circle(r) => "circle",
  _ => "other",
}

fun main() = { println(describe(Circle(5))); println(describe(Square(3))); println(describe(Triangle(1))) }
"#;
    assert_eq!(run_program(src), "circle\nother\nother");
}

#[test]
fn test_never_sealed_interface() {
    // Compile a program that uses Never (via panic). The prelude Never type
    // should produce a sealed interface class with zero PermittedSubclasses.
    let src = r#"
fun diverge() -> Never = panic("boom")
fun main() = diverge()
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);

    // Check that core/never/Never.class exists
    let never_class = dir.path().join("core/never/Never.class");
    assert!(
        never_class.exists(),
        "core/never/Never.class should exist"
    );
    let javap_out = javap_output(&never_class, true);
    assert!(
        javap_out.contains("interface"),
        "Never should be an interface"
    );
    assert!(
        javap_out.contains("PermittedSubclasses"),
        "Never should have PermittedSubclasses"
    );
}

#[test]
fn test_user_empty_sum_sealed_interface() {
    let src = r#"
type NoMessages = |
fun main() = 0
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);

    let class_path = dir.path().join("test/NoMessages.class");
    assert!(
        class_path.exists(),
        "test/NoMessages.class should exist"
    );
    let javap_out = javap_output(&class_path, true);
    assert!(
        javap_out.contains("interface"),
        "NoMessages should be an interface"
    );
    assert!(
        javap_out.contains("PermittedSubclasses"),
        "NoMessages should have PermittedSubclasses"
    );
}

#[test]
fn test_never_no_trailing_return() {
    let src = r#"
fun diverge() -> Never = panic("boom")
fun main() = diverge()
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);
    let javap_out = javap_output(&dir.path().join("Test.class"), true);

    // diverge() should use Never descriptor, not Object
    assert!(
        javap_out.contains("Lcore/never/Never;"),
        "diverge() descriptor should use core/never/Never, got:\n{javap_out}"
    );
    // Should contain athrow (from panic)
    assert!(
        javap_out.contains("athrow"),
        "diverge() should contain athrow, got:\n{javap_out}"
    );
}

#[test]
fn test_never_int_return_panic() {
    let src = r#"
fun diverge() -> Int = panic("boom")
fun main() = diverge()
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);
    let javap_out = javap_output(&dir.path().join("Test.class"), true);

    // diverge() returns Int, body panics — should contain athrow
    assert!(
        javap_out.contains("athrow"),
        "diverge() -> Int with panic body should contain athrow, got:\n{javap_out}"
    );
}

#[test]
fn test_never_recur_has_goto() {
    let src = r#"
fun counter(n: Int) -> Never = if n > 1000 { panic("done") } else { recur(n + 1) }
fun main() = counter(0)
"#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let (typed_modules, interfaces) = infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("type check");
    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
    let dir = compile_typed_modules(&typed_modules, &link_ctx);
    let javap_out = javap_output(&dir.path().join("Test.class"), true);

    // counter() should contain goto (for recur)
    assert!(
        javap_out.contains("goto"),
        "counter() should contain goto for recur, got:\n{javap_out}"
    );
}
