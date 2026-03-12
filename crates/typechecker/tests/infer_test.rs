use krypton_modules::module_resolver::{CompositeResolver, ModuleResolver};
use krypton_parser::ast::Module;
use krypton_parser::parser::parse;
use krypton_typechecker::infer;
use krypton_typechecker::scc;
use krypton_typechecker::types::{Substitution, TypeEnv, TypeVarGen};

fn parse_expr_via_module(src: &str) -> krypton_parser::ast::Expr {
    let wrapped = format!("fun _test() = {src}");
    let (module, errors) = parse(&wrapped);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    match &module.decls[0] {
        krypton_parser::ast::Decl::DefFn(f) => *f.body.clone(),
        other => panic!("expected DefFn, got {:?}", other),
    }
}

fn infer_module_fn(src: &str, fn_name: &str) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    match infer::infer_module(&module, &CompositeResolver::stdlib_only()) {
        Ok(modules) => modules[0]
            .fn_types
            .iter()
            .find(|(name, _)| name == fn_name)
            .map(|(_, scheme)| format!("{scheme}"))
            .unwrap_or_else(|| panic!("function {fn_name} not found in module")),
        Err(e) => format!("TypeError: {}", e.error),
    }
}

fn infer(src: &str) -> String {
    let expr = parse_expr_via_module(src);

    let mut env = TypeEnv::new();
    let mut subst = Substitution::new();
    let mut gen = TypeVarGen::new();

    match infer::infer_expr(&expr, &mut env, &mut subst, &mut gen) {
        Ok(ty) => infer::display_type(&ty, &subst, &env),
        Err(e) => format!("TypeError: {}", e.error),
    }
}

#[test]
fn infer_int_literal() {
    insta::assert_snapshot!(infer("42"), @"own Int");
}

#[test]
fn infer_bool_literal() {
    insta::assert_snapshot!(infer("true"), @"own Bool");
}

#[test]
fn infer_string_literal() {
    insta::assert_snapshot!(infer("\"hello\""), @"own String");
}

#[test]
fn infer_identity_lambda() {
    insta::assert_snapshot!(infer("x => x"), @"forall a. fn(a) -> a");
}

#[test]
fn infer_const_lambda() {
    insta::assert_snapshot!(infer("x => 42"), @"forall a. fn(a) -> own Int");
}

#[test]
fn infer_let_id_applied() {
    insta::assert_snapshot!(infer("{ let id = x => x; id(42) }"), @"own Int");
}

#[test]
fn infer_if_int() {
    insta::assert_snapshot!(infer("if true { 1 } else { 2 }"), @"own Int");
}

#[test]
fn infer_if_mismatch() {
    insta::assert_snapshot!(infer("if true { 1 } else { \"hi\" }"), @"TypeError: type mismatch: expected Int, found String");
}

#[test]
fn infer_if_non_bool_cond() {
    insta::assert_snapshot!(infer("if 42 { 1 } else { 2 }"), @"TypeError: type mismatch: expected Int, found Bool");
}

#[test]
fn infer_application() {
    insta::assert_snapshot!(infer("{ let f = x => x + 1; f(5) }"), @"Int");
}

#[test]
fn infer_do_block() {
    insta::assert_snapshot!(infer("{ 1; 2; 3 }"), @"own Int");
}

#[test]
fn infer_nested_let() {
    insta::assert_snapshot!(infer("{ let x = 1; let y = 2; x + y }"), @"Int");
}

#[test]
fn infer_let_polymorphism() {
    insta::assert_snapshot!(infer("{ let id = x => x; let a = id(1); id(true) }"), @"own Bool");
}

#[test]
fn infer_binary_add() {
    insta::assert_snapshot!(infer("1 + 2"), @"Int");
}

#[test]
fn infer_binary_eq() {
    insta::assert_snapshot!(infer("1 == 2"), @"Bool");
}

#[test]
fn infer_binary_gt() {
    insta::assert_snapshot!(infer("1 > 2"), @"Bool");
}

fn parse_module(src: &str) -> Module {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    module
}

fn infer_module_types(src: &str) -> String {
    let module = parse_module(src);
    match infer::infer_module(&module, &CompositeResolver::stdlib_only()) {
        Ok(modules) => modules[0]
            .fn_types
            .iter()
            .map(|(name, scheme)| format!("{}: {}", name, scheme))
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => format!("TypeError: {}", e.error),
    }
}

#[test]
fn infer_module_with_custom_resolver() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub fun add(x: Int, y: Int) -> Int = x + y".to_string())
            } else {
                None
            }
        }
    }

    let src = r#"
        import mylib.{add}
        fun main() -> Int = add(1, 2)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver);
    assert!(result.is_ok(), "expected Ok, got {:?}", result.err());
    let modules = result.unwrap();
    let info = &modules[0];
    let main_type = info.fn_types.iter().find(|(n, _)| n == "main").unwrap();
    assert_eq!(format!("{}", main_type.1), "fn() -> Int");
}

#[test]
fn impl_where_clause_constraints_are_stored_on_instance_defs() {
    let src = r#"
        type Option[a] = Some(a) | None

        trait MyEq[a] {
            fun eq(x: a, y: a) -> Bool
        }

        impl MyEq[Option[a]] where a: MyEq {
            fun eq(x, y) = true
        }
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);

    let modules = infer::infer_module(&module, &CompositeResolver::stdlib_only()).unwrap();
    let instance = modules[0]
        .instance_defs
        .iter()
        .find(|inst| inst.trait_name == "MyEq" && inst.target_type_name == "Option")
        .expect("expected MyEq[Option[a]] instance");

    assert_eq!(instance.constraints.len(), 1);
    assert_eq!(instance.constraints[0].type_var, "a");
    assert_eq!(instance.constraints[0].trait_name, "MyEq");
}

#[test]
fn impl_without_where_clause_stores_empty_constraints() {
    let src = r#"
        type Point = { x: Int, y: Int }

        trait MyEq[a] {
            fun eq(x: a, y: a) -> Bool
        }

        impl MyEq[Point] {
            fun eq(x, y) = true
        }
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);

    let modules = infer::infer_module(&module, &CompositeResolver::stdlib_only()).unwrap();
    let instance = modules[0]
        .instance_defs
        .iter()
        .find(|inst| inst.trait_name == "MyEq" && inst.target_type_name == "Point")
        .expect("expected MyEq[Point] instance");

    assert!(instance.constraints.is_empty());
}

#[test]
fn infer_undefined_variable() {
    insta::assert_snapshot!(infer("x"), @"TypeError: unknown variable: x");
}

#[test]
fn infer_shadowing() {
    insta::assert_snapshot!(infer("{ let x = 1; let x = true; x }"), @"own Bool");
}

#[test]
fn infer_forward_reference() {
    insta::assert_snapshot!(
        infer_module_types("fun f(x) = g(x)\nfun g(x) = x + 1"),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    f: fn(own Int) -> Int
    g: fn(own Int) -> Int
    "
    );
}

#[test]
fn infer_do_block_scoping() {
    insta::assert_snapshot!(infer("{ { let x = 1 }; x }"), @"TypeError: unknown variable: x");
}

#[test]
fn infer_module_basic() {
    insta::assert_snapshot!(
        infer_module_types("fun add(a, b) = a + b"),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    add: fn(Int, Int) -> Int
    "
    );
}

#[test]
fn infer_module_forward_ref() {
    insta::assert_snapshot!(
        infer_module_types("fun f(x) = g(x)\nfun g(x) = x + 1"),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    f: fn(own Int) -> Int
    g: fn(own Int) -> Int
    "
    );
}

#[test]
fn infer_mutual_recursion() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun is_even(n) = if n == 0 { true } else { is_odd(n - 1) }\nfun is_odd(n) = if n == 0 { false } else { is_even(n - 1) }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    is_even: fn(own Int) -> Bool
    is_odd: fn(Int) -> own Bool
    "
    );
}

#[test]
fn scc_tarjan_unit_test() {
    // Graph: a(0) -> b(1), b(1) -> a(0), c(2) -> a(0)
    let adj = vec![
        vec![1], // a -> b
        vec![0], // b -> a
        vec![0], // c -> a
    ];
    let sccs = scc::tarjan_scc(&adj);
    assert_eq!(sccs.len(), 2);
    assert_eq!(sccs[0], vec![0, 1]); // {a, b} — mutual recursion
    assert_eq!(sccs[1], vec![2]); // {c} — depends on a
}

#[test]
fn infer_record_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Point = { x: Int, y: Int }\nfun p() = Point(1, 2)"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Point: fn(Int, Int) -> Point
    p: fn() -> Point
    "
    );
}

#[test]
fn infer_sum_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun wrap(x) = Some(x)"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall j. fn(j) -> Option[j]
    None: forall j. Option[j]
    wrap: forall u. fn(u) -> Option[u]
    "
    );
}

#[test]
fn infer_bare_variant() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun none() = None"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall j. fn(j) -> Option[j]
    None: forall j. Option[j]
    none: forall v. fn() -> Option[v]
    "
    );
}

#[test]
fn infer_duplicate_type_error() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Foo = { x: Int }\ntype Foo = { y: Int }\nfun f(x) = x"
        ),
        @"TypeError: duplicate type definition: Foo"
    );
}

#[test]
fn infer_scc_generalization_order() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun id(x) = x\nfun f(n) = id(n)\nfun g(s) = id(s)"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    id: forall t. fn(t) -> t
    f: forall z. fn(z) -> z
    g: forall e1. fn(e1) -> e1
    "
    );
}

#[test]
fn infer_field_access() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Point = { x: Int, y: Int }\nfun get_x() = Point(1, 2).x"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Point: fn(Int, Int) -> Point
    get_x: fn() -> Int
    "
    );
}

#[test]
fn infer_struct_update() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Point = { x: Int, y: Int }\nfun move_x() = { Point(1, 2) | x = 42 }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Point: fn(Int, Int) -> Point
    move_x: fn() -> Point
    "
    );
}

#[test]
fn infer_unknown_field_error() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Point = { x: Int, y: Int }\nfun bad() = Point(1, 2).z"
        ),
        @"TypeError: unknown field: type Point has no field z"
    );
}

#[test]
fn infer_field_access_non_struct() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Point = { x: Int, y: Int }\nfun bad() = 42.y"
        ),
        @"TypeError: not a struct: type Int is not a record"
    );
}

#[test]
fn infer_struct_update_unknown_field() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Point = { x: Int, y: Int }\nfun bad() = { Point(1, 2) | z = 42 }"
        ),
        @"TypeError: unknown field: type Point has no field z"
    );
}

#[test]
fn infer_match_option() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun unwrap_or(opt, default) = match opt { Some(x) => x, None => default }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall j. fn(j) -> Option[j]
    None: forall j. Option[j]
    unwrap_or: forall v. fn(Option[v], v) -> v
    "
    );
}

#[test]
fn infer_match_literal() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun describe(x) = match x { 1 => \"one\", 2 => \"two\", _ => \"other\" }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    describe: fn(Int) -> String
    "
    );
}

#[test]
fn infer_match_variable() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun identity(x) = match x { y => y }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    identity: forall t. fn(t) -> t
    "
    );
}

#[test]
fn infer_match_nested_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "type List[a] = Cons(a, List[a]) | Nil\nfun sum2(xs) = match xs { Cons(h, Cons(h2, t)) => h + h2, _ => 0 }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Cons: forall j. fn(j, List[j]) -> List[j]
    Nil: forall j. List[j]
    sum2: fn(List[Int]) -> Int
    "
    );
}

#[test]
fn infer_tuple_creation() {
    insta::assert_snapshot!(infer("(1, \"hi\")"), @"(own Int, own String)");
}

#[test]
fn infer_tuple_nested() {
    insta::assert_snapshot!(infer("(1, (true, \"x\"))"), @"(own Int, (own Bool, own String))");
}

#[test]
fn infer_tuple_in_match() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun first(p) = match p { (a, b) => a }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    first: forall w x. fn((w, x)) -> w
    "
    );
}

#[test]
fn infer_let_destructure_tuple() {
    insta::assert_snapshot!(infer("{ let (a, b) = (1, \"hi\"); a }"), @"own Int");
}

#[test]
fn infer_tuple_polymorphic() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun swap(p) = match p { (a, b) => (b, a) }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    swap: forall w x. fn((w, x)) -> (x, w)
    "
    );
}

#[test]
fn infer_match_wrong_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Color = Red | Green | Blue\ntype Option[a] = Some(a) | None\nfun bad(c) = match Red { Some(x) => x, _ => 0 }"
        ),
        @"TypeError: type mismatch: expected Color, found Option[x]"
    );
}

#[test]
fn test_exhaustive_complete() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun unwrap(opt) = match opt { Some(x) => x, None => 0 }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall j. fn(j) -> Option[j]
    None: forall j. Option[j]
    unwrap: fn(Option[own Int]) -> Int
    "
    );
}

#[test]
fn test_exhaustive_missing_variant() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun test(opt) = match opt { Some(x) => x }"
        ),
        @"TypeError: non-exhaustive match: missing None"
    );
}

#[test]
fn test_exhaustive_wildcard_covers_all() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun test(opt) = match opt { _ => 0 }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall j. fn(j) -> Option[j]
    None: forall j. Option[j]
    test: forall u. fn(u) -> Int
    "
    );
}

#[test]
fn test_exhaustive_nested() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun test(opt) = match opt { Some(Some(x)) => x, Some(None) => 0 }"
        ),
        @"TypeError: non-exhaustive match: missing None"
    );
}

#[test]
fn infer_call_site_coercion_borrow() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun len(s: String) -> Int = 42\nfun test(buf: ~String) -> Int = { len(buf); len(buf) }"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    len: fn(String) -> Int
    test: fn(own String) -> Int
    "
    );
}

#[test]
fn infer_call_site_coercion_no_collection() {
    insta::assert_snapshot!(
        infer_module_types(
            "type MyList = Cons(String, MyList) | Nil\nfun test(buf: ~String) -> MyList = Cons(buf, Nil)"
        ),
        @"
    println: forall i. fn(i) -> Unit
    Some: forall b. fn(b) -> Option[b]
    None: forall b. Option[b]
    Ok: forall c d. fn(d) -> Result[c, d]
    Err: forall c d. fn(c) -> Result[c, d]
    Cons: forall e. fn(e, List[e]) -> List[e]
    Nil: forall e. List[e]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Cons: fn(String, MyList) -> MyList
    Nil: MyList
    test: fn(own String) -> MyList
    "
    );
}

#[test]
fn float_add_infers_float() {
    insta::assert_snapshot!(infer("1.0 + 2.0"), @"Float");
}

#[test]
fn float_lt_infers_bool() {
    insta::assert_snapshot!(infer("1.0 < 2.0"), @"Bool");
}

#[test]
fn float_neg_infers_float() {
    insta::assert_snapshot!(infer("-3.14"), @"Float");
}

// ── Explicit type parameters on functions ──

#[test]
fn explicit_type_param_generalized() {
    // fun view[t](x: ~t) -> t should produce forall t. fn(own t) -> t
    insta::assert_snapshot!(
        infer_module_fn("fun view[t](x: ~t) -> t = x", "view"),
        @"forall t. fn(own t) -> t"
    );
}

#[test]
fn explicit_type_param_identity() {
    // fun id[a](x: a) -> a should produce forall a. fn(a) -> a
    insta::assert_snapshot!(
        infer_module_fn("fun id[a](x: a) -> a = x", "id"),
        @"forall t. fn(t) -> t"
    );
}

#[test]
fn explicit_type_param_multiple() {
    // fun const[a, b](x: a, y: b) -> a should produce forall a b. fn(a, b) -> a
    insta::assert_snapshot!(
        infer_module_fn("fun const_[a, b](x: a, y: b) -> a = x", "const_"),
        @"forall t u. fn(t, u) -> t"
    );
}

#[test]
fn explicit_hkt_type_param_generalized() {
    let src = r#"
        type Box[a] = Box(a)

        trait Functor[f[_]] {
            fun fmap[a, b](fa: f[a], g: (a) -> b) -> f[b]
        }

        impl Functor[Box] {
            fun fmap[a, b](fa: Box[a], g: (a) -> b) -> Box[b] =
                match fa { Box(x) => Box(g(x)) }
        }

        fun apply[f[_], a](fa: f[a]) -> f[a] where f: Functor = fmap(fa, x => x)
    "#;
    insta::assert_snapshot!(infer_module_fn(src, "apply"), @"forall x y. fn(x[y]) -> x[y]");
}

#[test]
fn explicit_hkt_type_param_wrong_arity_is_error() {
    let src = "fun bad[f[_], a, b](x: f[a, b]) -> f[a] = x";
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only());
    assert!(result.is_err(), "expected kind mismatch");
    let err = result.err().unwrap();
    assert_eq!(err.error.error_code().to_string(), "E0507");
}

#[test]
fn trait_and_impl_methods_accept_hkt_type_params() {
    let src = r#"
        trait Hoist[a] {
            fun hoist[f[_], g[_]](x: f[a], k: (f[a]) -> g[a]) -> g[a]
        }

        impl Hoist[Int] {
            fun hoist[f[_], g[_]](x: f[Int], k: (f[Int]) -> g[Int]) -> g[Int] = k(x)
        }
    "#;
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only());
    assert!(result.is_ok(), "expected method-level HKTs to typecheck");
}

#[test]
fn no_type_params_still_generalizes() {
    // Unannotated identity should still generalize via HM
    insta::assert_snapshot!(
        infer_module_fn("fun id(x) = x", "id"),
        @"forall t. fn(t) -> t"
    );
}

#[test]
fn explicit_type_args_call_site_success() {
    let src = r#"
        fun identity[a](x: a) -> a = x
        fun use_it() = identity[Int](42)
    "#;
    insta::assert_snapshot!(infer_module_fn(src, "use_it"), @"fn() -> Int");
}

#[test]
fn explicit_type_args_call_site_mismatch_is_error() {
    let src = r#"
        fun identity[a](x: a) -> a = x
        fun use_it() = identity[Int]("hello")
    "#;
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only());
    assert!(result.is_err(), "expected mismatch error");
    let err = result.err().unwrap();
    assert_eq!(err.error.error_code().to_string(), "E0001");
}

#[test]
fn explicit_type_args_wrong_count_is_error() {
    let src = r#"
        fun identity[a](x: a) -> a = x
        fun use_it() = identity[Int, String](42)
    "#;
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only());
    assert!(result.is_err(), "expected wrong arity error");
    let err = result.err().unwrap();
    assert_eq!(err.error.error_code().to_string(), "E0005");
}

#[test]
fn standalone_explicit_type_application_typechecks() {
    let src = r#"
        fun identity[a](x: a) -> a = x
        fun use_it() = {
            let id_int = identity[Int]
            id_int(42)
        }
    "#;
    insta::assert_snapshot!(infer_module_fn(src, "use_it"), @"fn() -> Int");
}

#[test]
fn explicit_type_args_work_with_methods() {
    let src = r#"
        import core/list.{List, Cons, Nil, map}

        fun stringify(x: Int) -> String = "n"

        fun use_it(xs: List[Int]) = xs.map[String](stringify)
    "#;
    insta::assert_snapshot!(infer_module_fn(src, "use_it"), @"fn(List[Int]) -> List[String]");
}

// --- Unknown type error tests ---

#[test]
fn unknown_type_in_param() {
    insta::assert_snapshot!(
        infer_module_types("fun f(x: Foo) = x"),
        @"TypeError: unknown type: Foo"
    );
}

#[test]
fn unknown_type_in_return() {
    insta::assert_snapshot!(
        infer_module_types("fun f(x: Int) -> Foo = x"),
        @"TypeError: unknown type: Foo"
    );
}

#[test]
fn known_types_still_work() {
    insta::assert_snapshot!(
        infer_module_fn("fun f(x: Int) -> Bool = true", "f"),
        @"fn(Int) -> Bool"
    );
}

#[test]
fn typo_in_type_name() {
    insta::assert_snapshot!(
        infer_module_types("fun f(x: Stirng) = x"),
        @"TypeError: unknown type: Stirng"
    );
}

#[test]
fn type_param_not_unknown() {
    insta::assert_snapshot!(
        infer_module_fn("fun id[a](x: a) -> a = x", "id"),
        @"forall t. fn(t) -> t"
    );
}

#[test]
fn self_referential_type_ok() {
    insta::assert_snapshot!(
        infer_module_fn(
            "type List[a] = Cons(a, List[a]) | Nil\nfun f(x: List[Int]) = x",
            "f"
        ),
        @"fn(List[Int]) -> List[Int]"
    );
}

#[test]
fn typo_in_type_field() {
    insta::assert_snapshot!(
        infer_module_types("type Foo = Bar(Stirng)"),
        @"TypeError: unknown type: Stirng"
    );
}

#[test]
fn mutual_type_refs_ok() {
    insta::assert_snapshot!(
        infer_module_fn(
            "type A = MkA(B)\ntype B = MkB(A)\nfun f(x: A) = x",
            "f"
        ),
        @"fn(A) -> A"
    );
}

// ── Multi-module typechecking (M11-T2b) ──

#[test]
fn infer_module_returns_all_modules() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub fun add(x: Int, y: Int) -> Int = x + y".to_string())
            } else {
                None
            }
        }
    }

    let src = r#"
        import mylib.{add}
        fun main() -> Int = add(1, 2)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let modules = infer::infer_module(&module, &FakeResolver).unwrap();
    // Main module + mylib
    assert!(
        modules.len() >= 2,
        "expected at least 2 modules, got {}",
        modules.len()
    );
    assert!(
        modules[0].module_path.is_none(),
        "first module should be main (no path)"
    );
    assert!(
        modules
            .iter()
            .any(|m| m.module_path.as_deref() == Some("mylib")),
        "should have a TypedModule for mylib"
    );
}

#[test]
fn infer_module_provenance_on_bindings() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub fun add(x: Int, y: Int) -> Int = x + y".to_string())
            } else {
                None
            }
        }
    }

    let src = r#"
        import mylib.{add}
        fun main() -> Int = add(1, 2)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let modules = infer::infer_module(&module, &FakeResolver).unwrap();
    // The main module should have `add` in fn_types with provenance
    let main = &modules[0];
    assert!(
        main.fn_types.iter().any(|(n, _)| n == "add"),
        "main module should have add in fn_types"
    );
}

#[test]
fn infer_module_cache_prevents_recheck() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    static RESOLVE_COUNT: AtomicUsize = AtomicUsize::new(0);

    struct CountingResolver;
    impl ModuleResolver for CountingResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                RESOLVE_COUNT.fetch_add(1, Ordering::SeqCst);
                Some("pub fun helper() -> Int = 42".to_string())
            } else {
                None
            }
        }
    }

    RESOLVE_COUNT.store(0, Ordering::SeqCst);
    let src = r#"
        import mylib.{helper}
        fun main() -> Int = helper()
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let modules = infer::infer_module(&module, &CountingResolver).unwrap();
    // Only one TypedModule for mylib despite resolver being called
    let mylib_count = modules
        .iter()
        .filter(|m| m.module_path.as_deref() == Some("mylib"))
        .count();
    assert_eq!(
        mylib_count, 1,
        "should have exactly one TypedModule for mylib"
    );
}

#[test]
fn infer_module_circular_import_detected() {
    struct CircularResolver;
    impl ModuleResolver for CircularResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "a" => Some("import b.{bar}\nfun foo(x: Int) -> Int = bar(x)".to_string()),
                "b" => Some("import a.{foo}\nfun bar(x: Int) -> Int = foo(x)".to_string()),
                _ => None,
            }
        }
    }

    let src = "import a.{foo}\nfun main() -> Int = foo(1)";
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let result = infer::infer_module(&module, &CircularResolver);
    assert!(result.is_err(), "should detect circular import");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected circular import error"),
    };
    assert_eq!(err.error.error_code().to_string(), "E0502");
}

#[test]
fn infer_module_stdlib_own_typed_module() {
    let src = r#"
        import core/option.{Some, None}
        fun wrap(x: Int) -> Option[Int] = Some(x)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let modules = infer::infer_module(&module, &CompositeResolver::stdlib_only()).unwrap();
    // Should have a TypedModule for core/option
    assert!(
        modules
            .iter()
            .any(|m| m.module_path.as_deref() == Some("core/option")),
        "should have a TypedModule for core/option"
    );
}

#[test]
fn infer_module_cross_module_typecheck() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "math" {
                Some("pub fun double(x: Int) -> Int = x + x".to_string())
            } else {
                None
            }
        }
    }

    let src = r#"
        import math.{double}
        fun quadruple(x: Int) -> Int = double(double(x))
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let modules = infer::infer_module(&module, &FakeResolver).unwrap();
    let main = &modules[0];
    let quad_type = main
        .fn_types
        .iter()
        .find(|(n, _)| n == "quadruple")
        .unwrap();
    assert_eq!(format!("{}", quad_type.1), "fn(Int) -> Int");
}

#[test]
fn infer_module_private_by_default() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("fun internal_helper() -> Int = 1\npub fun public_fn() -> Int = internal_helper()".to_string())
            } else {
                None
            }
        }
    }

    // Importing a private function should fail with E0503
    let src = r#"
        import mylib.{public_fn, internal_helper}
        fun main() -> Int = public_fn() + internal_helper()
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let result = infer::infer_module(&module, &FakeResolver);
    assert!(result.is_err(), "importing private fn should fail");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.error.error_code().to_string(), "E0503");

    // Importing only the public function should succeed
    let src2 = r#"
        import mylib.{public_fn}
        fun main() -> Int = public_fn()
    "#;
    let (module2, errors2) = parse(src2);
    assert!(errors2.is_empty());
    let result2 = infer::infer_module(&module2, &FakeResolver);
    assert!(
        result2.is_ok(),
        "importing pub fn should work: {:?}",
        result2.err()
    );
}

#[test]
fn infer_module_bare_import_error() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub fun add(x: Int, y: Int) -> Int = x + y".to_string())
            } else {
                None
            }
        }
    }
    let src = r#"
        import mylib
        fun main() -> Int = 1
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver);
    assert!(result.is_err(), "bare import should fail");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.error.error_code().to_string(), "E0504");
}

#[test]
fn infer_module_pub_import_reexport() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "lib_a" => Some("pub fun helper(x: Int) -> Int = x + 1".to_string()),
                "facade" => Some("pub import lib_a.{helper}".to_string()),
                _ => None,
            }
        }
    }
    let src = r#"
        import facade.{helper}
        fun main() -> Int = helper(5)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver);
    assert!(
        result.is_ok(),
        "pub import re-export should succeed: {:?}",
        result.err()
    );
    let modules = result.unwrap();
    // Main module should have helper in its fn_types
    let main_mod = &modules[0];
    assert!(
        main_mod.fn_types.iter().any(|(n, _)| n == "helper"),
        "main module should have 'helper' in fn_types"
    );
    // fn_provenance should point to the original module (lib_a), not the facade
    assert_eq!(
        main_mod.fn_provenance.get("helper"),
        Some(&("lib_a".to_string(), "helper".to_string()))
    );
}

#[test]
fn infer_module_pub_import_reexport_private_error() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "lib_a" => Some("pub fun helper(x: Int) -> Int = x + 1".to_string()),
                "facade" => Some("pub import lib_a.{helper, missing_name}".to_string()),
                _ => None,
            }
        }
    }
    let src = r#"
        import facade.{helper}
        fun main() -> Int = helper(5)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver);
    assert!(
        result.is_err(),
        "pub import of non-existent name should fail"
    );
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.error.error_code().to_string(), "E0505");
}

#[test]
fn cross_module_deriving_show() {
    use krypton_modules::module_resolver::StdlibResolver;
    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, path: &str) -> Option<String> {
            match path {
                "mylib" => Some("pub open type Point = { x: Int, y: Int } deriving (Show)".into()),
                _ => StdlibResolver.resolve(path),
            }
        }
    }
    let src = r#"
        import mylib.{Point}
        import core/io.{println}
        fun main() = println(Point { x = 1, y = 2 })
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &Resolver);
    assert!(
        result.is_ok(),
        "cross-module deriving Show should work: {:?}",
        result.err()
    );
}

#[test]
fn cross_module_derived_constrained_instance_resolves_when_inner_instance_exists() {
    use krypton_modules::module_resolver::StdlibResolver;
    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, path: &str) -> Option<String> {
            match path {
                "mylib" => Some("pub open type Box[a] = Box(a) deriving (Show)".into()),
                _ => StdlibResolver.resolve(path),
            }
        }
    }
    let src = r#"
        import mylib.{Box}
        import core/io.{println}

        type Player = { name: String, score: Int } deriving (Show)

        fun main() = println(Box(Player { name = "ana", score = 7 }))
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &Resolver);
    assert!(
        result.is_ok(),
        "cross-module derived constrained instance should resolve: {:?}",
        result.err()
    );
}

#[test]
fn cross_module_derived_constrained_instance_reports_e0301_when_inner_instance_missing() {
    use krypton_modules::module_resolver::StdlibResolver;
    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, path: &str) -> Option<String> {
            match path {
                "mylib" => Some("pub open type Box[a] = Box(a) deriving (Show)".into()),
                _ => StdlibResolver.resolve(path),
            }
        }
    }
    let src = r#"
        import mylib.{Box}
        import core/io.{println}

        type Player = { name: String, score: Int }

        fun main() = println(Box(Player { name = "ana", score = 7 }))
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let err = match infer::infer_module(&module, &Resolver) {
        Ok(_) => panic!("expected E0301"),
        Err(err) => err,
    };
    assert_eq!(err.error.error_code().to_string(), "E0301");
}

#[test]
fn cross_module_derived_instance_exports_constraint_metadata() {
    use krypton_modules::module_resolver::StdlibResolver;
    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, path: &str) -> Option<String> {
            match path {
                "mylib" => Some("pub open type Box[a] = Box(a) deriving (Show)".into()),
                _ => StdlibResolver.resolve(path),
            }
        }
    }
    let src = r#"
        import mylib.{Box}
        fun main(x) = x
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let modules = infer::infer_module(&module, &Resolver).expect("typecheck should succeed");
    let imported = modules
        .iter()
        .find(|typed_module| typed_module.module_path.as_deref() == Some("mylib"))
        .expect("expected imported mylib module");
    let instance = imported
        .instance_defs
        .iter()
        .find(|inst| inst.trait_name == "Show" && inst.target_type_name == "Box")
        .expect("expected derived Show[Box[a]] instance");

    assert_eq!(instance.constraints.len(), 1);
    assert_eq!(instance.constraints[0].trait_name, "Show");
    assert_eq!(instance.constraints[0].type_var, "a");
    assert!(instance.type_var_ids.contains_key("a"));
}

#[test]
fn local_prelude_shadow_can_derive_show_without_importing_prelude_instance() {
    use krypton_modules::module_resolver::StdlibResolver;

    let src = r#"
        type Option[a] = Some(a) | None deriving (Show)
        fun main() = println(Some(42))
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &StdlibResolver);
    assert!(
        result.is_ok(),
        "local shadowed prelude type should derive Show independently: {:?}",
        result.err()
    );
}

#[test]
fn infer_module_private_trait() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "traitlib" {
                // Private trait (no pub) — should not be importable
                Some(
                    r#"
                    type MyType = MkMyType(Int)
                    trait Secret[a] {
                        fun secret(x: a) -> Int
                    }
                    impl Secret[MyType] {
                        fun secret(x: MyType) -> Int = 1
                    }
                    pub fun public_fn() -> Int = 42
                "#
                    .to_string(),
                )
            } else {
                None
            }
        }
    }

    // Explicitly importing a private trait should fail with E0503
    let src = r#"
        import traitlib.{Secret, public_fn}
        fun main() -> Int = public_fn()
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let result = infer::infer_module(&module, &FakeResolver);
    assert!(result.is_err(), "importing private trait should fail");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.error.error_code().to_string(), "E0503");

    // Wildcard import should silently skip private traits
    let src2 = r#"
        import traitlib.{public_fn}
        fun main() -> Int = public_fn()
    "#;
    let (module2, errors2) = parse(src2);
    assert!(errors2.is_empty());
    let result2 = infer::infer_module(&module2, &FakeResolver);
    assert!(
        result2.is_ok(),
        "wildcard import should skip private traits: {:?}",
        result2.err()
    );
}

#[test]
fn infer_module_parse_error_produces_e0506() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "broken" {
                Some("fun bad( -> Int = 1".to_string()) // invalid syntax
            } else {
                None
            }
        }
    }
    let src = r#"
        import broken.{bad}
        fun main() -> Int = bad()
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver);
    assert!(
        result.is_err(),
        "import of module with parse errors should fail"
    );
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.error.error_code().to_string(), "E0506");
}

#[test]
fn let_type_annotation_correct() {
    let result = infer_module_fn("fun f() -> Int { let x: Int = 5; x }", "f");
    assert_eq!(result, "fn() -> Int");
}

#[test]
fn let_type_annotation_mismatch() {
    let result = infer_module_fn("fun f() -> Int { let x: String = 5; x }", "f");
    assert!(
        result.starts_with("TypeError:"),
        "expected type error, got: {result}"
    );
}

#[test]
fn let_type_annotation_generic() {
    let result = infer_module_fn(
        "fun f() -> Vec[Int] { let xs: Vec[Int] = [1, 2, 3]; xs }",
        "f",
    );
    assert_eq!(result, "fn() -> Vec[Int]");
}

// --- Prelude synthetic import tests ---

#[test]
fn prelude_option_auto_imported() {
    let result = infer_module_fn("fun wrap(x) = Some(x)", "wrap");
    assert!(
        !result.starts_with("TypeError:"),
        "Some should be available from prelude: {result}"
    );
}

#[test]
fn prelude_result_auto_imported() {
    let result = infer_module_fn("fun ok(x) = Ok(x)", "ok");
    assert!(
        !result.starts_with("TypeError:"),
        "Ok should be available from prelude: {result}"
    );
}

#[test]
fn prelude_println_auto_imported() {
    let result = infer_module_fn("fun greet(x) = println(x)", "greet");
    assert!(
        !result.starts_with("TypeError:"),
        "println should be available from prelude: {result}"
    );
}

#[test]
fn prelude_type_shadowable() {
    // User defines their own Option type that shadows prelude's Option
    let result = infer_module_fn("type Option = MyOpt(Int)\nfun make() = MyOpt(42)", "make");
    assert!(
        !result.starts_with("TypeError:"),
        "local type should shadow prelude Option: {result}"
    );
}

#[test]
fn prelude_fn_shadowable() {
    // User declares extern println that shadows prelude's println — no Show constraint
    let result = infer_module_fn(
        r#"extern "java/io/PrintStream" {
            fun println(Object) -> Unit
        }
        fun greet() = println(42)"#,
        "greet",
    );
    assert!(
        !result.starts_with("TypeError:"),
        "extern should shadow prelude println: {result}"
    );
}

#[test]
fn reserved_name_krypton_intrinsic_rejected() {
    let src = "fun __krypton_intrinsic() = 42\nfun main() = __krypton_intrinsic()";
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only());
    assert!(result.is_err(), "should reject __krypton_intrinsic");
    let err = match result {
        Err(e) => e,
        Ok(_) => unreachable!(),
    };
    assert_eq!(err.error.error_code().to_string(), "E0012");
}

#[test]
fn reserved_name_krypton_prefix_rejected() {
    let src = "fun __krypton_foo() = 1\nfun main() = __krypton_foo()";
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only());
    assert!(result.is_err(), "should reject __krypton_ prefix");
    let err = match result {
        Err(e) => e,
        Ok(_) => unreachable!(),
    };
    assert_eq!(err.error.error_code().to_string(), "E0012");
}

#[test]
fn non_reserved_name_allowed() {
    // A user function named "intrinsic" (without __krypton_ prefix) should be fine
    let result = infer_module_fn(
        "fun intrinsic() = 42\nfun main() = intrinsic()",
        "intrinsic",
    );
    assert_eq!(result, "fn() -> Int");
}

#[test]
fn prelude_not_imported_in_prelude_tree() {
    use krypton_modules::module_resolver::StdlibResolver;
    // Prelude-tree modules should not self-import the prelude.
    // We test by inferring the prelude module itself — it should succeed without errors.
    let prelude_src = StdlibResolver
        .resolve("prelude")
        .expect("prelude should be resolvable");
    let (module, errors) = parse(&prelude_src);
    assert!(errors.is_empty(), "prelude parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only());
    assert!(
        result.is_ok(),
        "prelude module should type-check without self-import: {:?}",
        result.err()
    );
}

// ── Lambda parameter type propagation from call site ──

#[test]
fn lambda_params_inferred_from_higher_order_fn() {
    // Lambda param types should be inferred from the function signature,
    // allowing field access on record-typed params without annotation.
    insta::assert_snapshot!(
        infer_module_types(r#"
            type Player = { name: String, score: Int }
            fun apply(p: Player, f: (Player) -> Int) -> Int = f(p)
            fun get_score(p: Player) -> Int = apply(p, (x) => x.score)
        "#),
        @"println: forall i. fn(i) -> Unit
Some: forall b. fn(b) -> Option[b]
None: forall b. Option[b]
Ok: forall c d. fn(d) -> Result[c, d]
Err: forall c d. fn(c) -> Result[c, d]
Cons: forall e. fn(e, List[e]) -> List[e]
Nil: forall e. List[e]
LT: Ordering
EQ: Ordering
GT: Ordering
Player: fn(String, Int) -> Player
apply: fn(Player, fn(Player) -> Int) -> Int
get_score: fn(Player) -> Int"
    );
}
