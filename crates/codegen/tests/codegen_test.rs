use krypton_codegen::emit::compile_modules;
use krypton_parser::ast::{BinOp, Lit, TypeConstraint, TypeExpr, Variant, Visibility};
use krypton_parser::parser::parse;
use krypton_typechecker::infer::infer_module;
use krypton_typechecker::typed_ast::{
    AutoCloseInfo, ExternFnInfo, FnOrigin, InstanceDefInfo, InstanceMethod, TraitDefInfo,
    TypedExpr, TypedExprKind, TypedFnDecl, TypedMatchArm, TypedModule, TypedPattern,
};
use krypton_typechecker::types::{Type, TypeScheme};
use krypton_modules::module_resolver::CompositeResolver;
use std::collections::HashMap;
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
    let classes = compile_modules(&typed_modules, "Test").expect("compile_module_standalone should succeed");

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

fn compile_typed_modules(typed_modules: &[TypedModule]) -> tempfile::TempDir {
    let classes = compile_modules(typed_modules, "Test").expect("compile_modules should succeed");
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

fn run_typed_modules(typed_modules: &[TypedModule]) -> String {
    let dir = compile_typed_modules(typed_modules);
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

fn string_lit(value: &str) -> TypedExpr {
    TypedExpr {
        kind: TypedExprKind::Lit(Lit::String(value.to_string())),
        ty: Type::String,
        span: (0, 0),
    }
}

fn int_lit(value: i64) -> TypedExpr {
    TypedExpr {
        kind: TypedExprKind::Lit(Lit::Int(value)),
        ty: Type::Int,
        span: (0, 0),
    }
}

fn var_expr(name: &str, ty: Type) -> TypedExpr {
    TypedExpr {
        kind: TypedExprKind::Var(name.to_string()),
        ty,
        span: (0, 0),
    }
}

fn app_expr(name: &str, func_ty: Type, args: Vec<TypedExpr>, ret_ty: Type) -> TypedExpr {
    TypedExpr {
        kind: TypedExprKind::App {
            func: Box::new(var_expr(name, func_ty)),
            args,
        },
        ty: ret_ty,
        span: (0, 0),
    }
}

fn concat_expr(lhs: TypedExpr, rhs: TypedExpr) -> TypedExpr {
    TypedExpr {
        kind: TypedExprKind::BinaryOp {
            op: BinOp::Add,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        ty: Type::String,
        span: (0, 0),
    }
}

fn wrap_type(inner: Type) -> Type {
    Type::Named("Wrap".to_string(), vec![inner])
}

fn wrap_expr(inner: TypedExpr) -> TypedExpr {
    let inner_ty = inner.ty.clone();
    app_expr(
        "Wrap",
        Type::Fn(vec![inner_ty.clone()], Box::new(wrap_type(inner_ty.clone()))),
        vec![inner],
        wrap_type(inner_ty),
    )
}

fn build_constrained_render_module(use_polymorphic_wrapper: bool, nested: bool) -> TypedModule {
    let a_ty = Type::Var(0);
    let wrap_a_ty = wrap_type(a_ty.clone());
    let wrap_int_ty = if nested {
        wrap_type(wrap_type(Type::Int))
    } else {
        wrap_type(Type::Int)
    };

    let inner_pattern = TypedPattern::Var {
        name: "inner".to_string(),
        ty: a_ty.clone(),
        span: (0, 0),
    };
    let wrap_pattern = TypedPattern::Constructor {
        name: "Wrap".to_string(),
        args: vec![inner_pattern],
        ty: wrap_a_ty.clone(),
        span: (0, 0),
    };
    let empty_pattern = TypedPattern::Constructor {
        name: "Empty".to_string(),
        args: vec![],
        ty: wrap_a_ty.clone(),
        span: (0, 0),
    };

    let render_inner = app_expr(
        "render",
        Type::Fn(vec![a_ty.clone()], Box::new(Type::String)),
        vec![var_expr("inner", a_ty.clone())],
        Type::String,
    );
    let wrap_render_body = TypedExpr {
        kind: TypedExprKind::Match {
            scrutinee: Box::new(var_expr("value", wrap_a_ty.clone())),
            arms: vec![
                TypedMatchArm {
                    pattern: wrap_pattern,
                    body: concat_expr(
                        string_lit("Wrap("),
                        concat_expr(render_inner, string_lit(")")),
                    ),
                },
                TypedMatchArm {
                    pattern: empty_pattern,
                    body: string_lit("Empty"),
                },
            ],
        },
        ty: Type::String,
        span: (0, 0),
    };

    let wrapped_main_value = if nested {
        wrap_expr(wrap_expr(int_lit(42)))
    } else {
        wrap_expr(int_lit(42))
    };
    let rendered_main_value = if use_polymorphic_wrapper {
        app_expr(
            "render_wrap",
            Type::Fn(vec![wrap_int_ty.clone()], Box::new(Type::String)),
            vec![wrapped_main_value],
            Type::String,
        )
    } else {
        app_expr(
            "render",
            Type::Fn(vec![wrap_int_ty.clone()], Box::new(Type::String)),
            vec![wrapped_main_value],
            Type::String,
        )
    };

    let render_int_scheme = TypeScheme::mono(Type::Fn(vec![Type::Int], Box::new(Type::String)));
    let render_wrap_scheme = TypeScheme {
        vars: vec![0],
        ty: Type::Fn(vec![wrap_a_ty.clone()], Box::new(Type::String)),
    };

    let mut fn_types = vec![
        (
            "main".to_string(),
            TypeScheme::mono(Type::Fn(vec![], Box::new(Type::Unit))),
            FnOrigin::Regular,
        ),
    ];

    let render_int_method = InstanceMethod {
        name: "render".to_string(),
        params: vec!["x".to_string()],
        body: string_lit("x"),
        scheme: render_int_scheme,
    };
    let render_wrap_method = InstanceMethod {
        name: "render".to_string(),
        params: vec!["value".to_string()],
        body: wrap_render_body,
        scheme: render_wrap_scheme,
    };

    let mut functions = vec![];

    let mut fn_constraints = HashMap::new();
    let mut fn_constraint_requirements = HashMap::new();
    if use_polymorphic_wrapper {
        fn_types.push((
            "render_wrap".to_string(),
            TypeScheme {
                vars: vec![0],
                ty: Type::Fn(vec![wrap_a_ty.clone()], Box::new(Type::String)),
            },
            FnOrigin::Regular,
        ));
        functions.push(TypedFnDecl {
            name: "render_wrap".to_string(),
            visibility: Visibility::Pub,
            params: vec!["value".to_string()],
            body: app_expr(
                "render",
                Type::Fn(vec![wrap_a_ty.clone()], Box::new(Type::String)),
                vec![var_expr("value", wrap_a_ty.clone())],
                Type::String,
            ),
        });
        fn_constraints.insert("render_wrap".to_string(), vec![("Render".to_string(), 0)]);
        fn_constraint_requirements.insert("render_wrap".to_string(), vec![("Render".to_string(), 0)]);
    }

    functions.push(TypedFnDecl {
        name: "main".to_string(),
        visibility: Visibility::Pub,
        params: vec![],
        body: app_expr(
            "println",
            Type::Fn(
                vec![Type::Named("Object".to_string(), vec![])],
                Box::new(Type::Unit),
            ),
            vec![rendered_main_value],
            Type::Unit,
        ),
    });

    TypedModule {
        module_path: None,
        fn_types,
        exported_fn_types: vec![],
        functions,
        trait_defs: vec![TraitDefInfo {
            name: "Render".to_string(),
            methods: vec![("render".to_string(), 1)],
            is_imported: false,
        }],
        instance_defs: vec![
            InstanceDefInfo {
                trait_name: "Render".to_string(),
                target_type_name: "Int".to_string(),
                target_type: Type::Int,
                type_var_ids: HashMap::new(),
                constraints: vec![],
                methods: vec![render_int_method],
                subdict_traits: vec![],
                is_intrinsic: false,
            },
            InstanceDefInfo {
                trait_name: "Render".to_string(),
                target_type_name: "Wrap".to_string(),
                target_type: wrap_a_ty.clone(),
                type_var_ids: HashMap::from([("a".to_string(), 0)]),
                constraints: vec![TypeConstraint {
                    type_var: "a".to_string(),
                    trait_name: "Render".to_string(),
                    span: (0, 0),
                }],
                methods: vec![render_wrap_method],
                subdict_traits: vec![],
                is_intrinsic: false,
            },
        ],
        fn_constraints,
        fn_constraint_requirements,
        imported_fn_constraints: HashMap::new(),
        trait_method_map: HashMap::from([("render".to_string(), "Render".to_string())]),
        extern_fns: vec![ExternFnInfo {
            name: "println".to_string(),
            java_class: "krypton.runtime.KryptonIO".to_string(),
            param_types: vec![Type::Named("Object".to_string(), vec![])],
            return_type: Type::Unit,
        }],
        imported_extern_fns: vec![],
        struct_decls: vec![],
        sum_decls: vec![(
            "Wrap".to_string(),
            vec!["a".to_string()],
            vec![
                Variant {
                    name: "Wrap".to_string(),
                    fields: vec![TypeExpr::Var {
                        name: "a".to_string(),
                        span: (0, 0),
                    }],
                    span: (0, 0),
                },
                Variant {
                    name: "Empty".to_string(),
                    fields: vec![],
                    span: (0, 0),
                },
            ],
        )],
        fn_provenance: HashMap::new(),
        type_provenance: HashMap::new(),
        type_visibility: HashMap::new(),
        reexported_fn_types: vec![],
        reexported_type_names: vec![],
        reexported_type_visibility: HashMap::new(),
        exported_trait_defs: vec![],
        auto_close: AutoCloseInfo::default(),
        exported_fn_qualifiers: HashMap::new(),
    }
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
    let classes = compile_modules(std::slice::from_ref(typed_module), "Test").expect("compile_module_standalone should succeed");
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
    let classes = compile_modules(std::slice::from_ref(typed_module), "Test").expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
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
    let classes = compile_modules(std::slice::from_ref(typed_module), "Test").expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
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
    let classes = compile_modules(std::slice::from_ref(typed_module), "Test").expect("codegen");

    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let class_path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = class_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
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
    let typed_module = &infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check")[0];
    let classes = compile_modules(std::slice::from_ref(typed_module), "Test").expect("compile");
    let dir = tempfile::tempdir().unwrap();
    for (name, bytes) in &classes {
        let path = dir.path().join(format!("{name}.class"));
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::File::create(&path).unwrap().write_all(bytes).unwrap();
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
    let module = build_constrained_render_module(false, false);
    assert_eq!(run_typed_modules(&[module]), "Wrap(x)");
}

#[test]
fn test_constrained_instance_dictionary_passing_nested_runtime() {
    let module = build_constrained_render_module(false, true);
    assert_eq!(run_typed_modules(&[module]), "Wrap(Wrap(x))");
}

#[test]
fn test_constrained_instance_dictionary_forwarding_from_polymorphic_context() {
    let module = build_constrained_render_module(true, false);
    assert_eq!(run_typed_modules(&[module]), "Wrap(x)");
}

#[test]
fn test_constrained_instance_class_captures_dictionary_parameter() {
    let module = build_constrained_render_module(false, false);
    let dir = compile_typed_modules(&[module]);
    let class_output = javap_output(&dir.path().join("Render$Wrap.class"), false);
    assert!(
        class_output.contains("java.lang.Object dict0;"),
        "expected constrained instance to store dictionary field, javap output:\n{class_output}"
    );

    let test_output = javap_output(&dir.path().join("Test.class"), true);
    assert!(
        test_output.contains("Method Render$Wrap.\"<init>\":(Ljava/lang/Object;)V"),
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
    let typed_modules =
        infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check should succeed");
    let dir = compile_typed_modules(&typed_modules);
    let test_output = javap_output(&dir.path().join("Test.class"), true);
    assert!(
        test_output.contains("InvokeDynamic") && test_output.contains("apply:(Ljava/lang/Object;)LFun1;"),
        "expected constrained function ref to capture a dictionary, javap output:\n{test_output}"
    );
    assert!(
        test_output.contains("apply:()LFun1;"),
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
    let typed_modules =
        infer_module(&module, &CompositeResolver::stdlib_only()).expect("type check");
    let dir = compile_typed_modules(&typed_modules);
    let javap_out = javap_output(&dir.path().join("Test.class"), false);
    assert!(
        javap_out.contains("Default$Int"),
        "expected Default$Int instance class in javap output:\n{javap_out}"
    );
}
