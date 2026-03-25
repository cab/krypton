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
    match infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string()) {
        Ok(modules) => modules[0]
            .fn_types
            .iter()
            .find(|e| e.name == fn_name)
            .map(|e| format!("{}", e.scheme))
            .unwrap_or_else(|| panic!("function {fn_name} not found in module")),
        Err(e) => match e.type_error() {
            Some(te) => format!("TypeError: {}", te.error),
            None => format!("InferError: {e:?}"),
        },
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
    insta::assert_snapshot!(infer("42"), @"~Int");
}

#[test]
fn infer_bool_literal() {
    insta::assert_snapshot!(infer("true"), @"~Bool");
}

#[test]
fn infer_string_literal() {
    insta::assert_snapshot!(infer("\"hello\""), @"~String");
}

#[test]
fn infer_identity_lambda() {
    insta::assert_snapshot!(infer("x -> x"), @"forall a. (a) -> a");
}

#[test]
fn infer_const_lambda() {
    insta::assert_snapshot!(infer("x -> 42"), @"forall a. (a) -> ~Int");
}

#[test]
fn infer_let_id_applied() {
    insta::assert_snapshot!(infer("{ let id = x -> x; id(42) }"), @"Int");
}

#[test]
fn infer_if_int() {
    insta::assert_snapshot!(infer("if true { 1 } else { 2 }"), @"~Int");
}

#[test]
fn infer_if_mismatch() {
    insta::assert_snapshot!(infer("if true { 1 } else { \"hi\" }"), @"TypeError: type mismatch: expected Int, found String");
}

#[test]
fn infer_if_non_bool_cond() {
    insta::assert_snapshot!(infer("if 42 { 1 } else { 2 }"), @"TypeError: type mismatch: expected Bool, found Int");
}

#[test]
fn infer_application() {
    insta::assert_snapshot!(infer("{ let f = x -> x + 1; f(5) }"), @"Int");
}

#[test]
fn infer_do_block() {
    insta::assert_snapshot!(infer("{ 1; 2; 3 }"), @"~Int");
}

#[test]
fn infer_nested_let() {
    insta::assert_snapshot!(infer("{ let x = 1; let y = 2; x + y }"), @"Int");
}

#[test]
fn infer_let_polymorphism() {
    insta::assert_snapshot!(infer("{ let id = x -> x; let a = id(1); id(true) }"), @"Bool");
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
    match infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string()) {
        Ok(modules) => modules[0]
            .fn_types
            .iter()
            .map(|e| format!("{}: {}", e.name, e.scheme))
            .collect::<Vec<_>>()
            .join("\n"),
        Err(e) => match e.type_error() {
            Some(te) => format!("TypeError: {}", te.error),
            None => format!("InferError: {e:?}"),
        },
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
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_ok(), "expected Ok, got {:?}", result.err());
    let modules = result.unwrap();
    let info = &modules[0];
    let main_type = info.fn_types.iter().find(|e| e.name == "main").unwrap();
    assert_eq!(format!("{}", main_type.scheme), "() -> Int");
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

    let modules = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string()).unwrap();
    let instance = modules[0]
        .instance_defs
        .iter()
        .find(|inst| inst.trait_name.local_name == "MyEq" && inst.target_type_name == "Option$$Var0")
        .expect("expected MyEq[Option[a]] instance");

    assert_eq!(instance.constraints.len(), 1);
    assert_eq!(instance.constraints[0].type_var, "a");
    assert_eq!(instance.constraints[0].trait_name.local_name, "MyEq");
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

    let modules = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string()).unwrap();
    let instance = modules[0]
        .instance_defs
        .iter()
        .find(|inst| inst.trait_name.local_name == "MyEq" && inst.target_type_name == "Point")
        .expect("expected MyEq[Point] instance");

    assert!(instance.constraints.is_empty());
}

#[test]
fn infer_undefined_variable() {
    insta::assert_snapshot!(infer("x"), @"TypeError: unknown variable: x");
}

#[test]
fn infer_shadowing() {
    insta::assert_snapshot!(infer("{ let x = 1; let x = true; x }"), @"~Bool");
}

#[test]
fn infer_forward_reference() {
    insta::assert_snapshot!(
        infer_module_types("fun f(x) = g(x)\nfun g(x) = x + 1"),
        @"
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    f: (Int) -> Int
    g: (Int) -> Int
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
        @"TypeError: function `add` uses trait method from `Semigroup` on type variable `?204` without a corresponding bound"
    );
}

#[test]
fn infer_module_forward_ref() {
    insta::assert_snapshot!(
        infer_module_types("fun f(x) = g(x)\nfun g(x) = x + 1"),
        @"
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    f: (Int) -> Int
    g: (Int) -> Int
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    is_even: (Int) -> Bool
    is_odd: (Int) -> Bool
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Point: (Int, Int) -> Point
    p: () -> Point
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    wrap: forall a. (a) -> Option[a]
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    none: forall a. () -> Option[a]
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    id: forall a. (a) -> a
    f: forall a. (a) -> a
    g: forall a. (a) -> a
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Point: (Int, Int) -> Point
    get_x: () -> Int
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Point: (Int, Int) -> Point
    move_x: () -> Point
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    unwrap_or: forall a. (Option[a], a) -> a
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    describe: (Int) -> String
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    identity: forall a. (a) -> a
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    sum2: (List[Int]) -> Int
    "
    );
}

#[test]
fn infer_tuple_creation() {
    insta::assert_snapshot!(infer("(1, \"hi\")"), @"(~Int, ~String)");
}

#[test]
fn infer_tuple_nested() {
    insta::assert_snapshot!(infer("(1, (true, \"x\"))"), @"(~Int, (~Bool, ~String))");
}

#[test]
fn infer_tuple_in_match() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun first(p) = match p { (a, b) => a }"
        ),
        @"
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    first: forall a b. ((a, b)) -> a
    "
    );
}

#[test]
fn infer_let_destructure_tuple() {
    insta::assert_snapshot!(infer("{ let (a, b) = (1, \"hi\"); a }"), @"~Int");
}

#[test]
fn infer_tuple_polymorphic() {
    insta::assert_snapshot!(
        infer_module_types(
            "fun swap(p) = match p { (a, b) => (b, a) }"
        ),
        @"
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    swap: forall a b. ((a, b)) -> (b, a)
    "
    );
}

#[test]
fn infer_match_wrong_constructor() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Color = Red | Green | Blue\ntype Option[a] = Some(a) | None\nfun bad(c) = match Red { Some(x) => x, _ => 0 }"
        ),
        @"TypeError: type mismatch: expected Color, found Option[a]"
    );
}

#[test]
fn test_exhaustive_complete() {
    insta::assert_snapshot!(
        infer_module_types(
            "type Option[a] = Some(a) | None\nfun unwrap(opt) = match opt { Some(x) => x, None => 0 }"
        ),
        @"
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    unwrap: (Option[Int]) -> Int
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    test: forall a. (a) -> Int
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    len: (String) -> Int
    test: (~String) -> Int
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
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Cons: (String, MyList) -> MyList
    Nil: MyList
    test: (~String) -> MyList
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
        @"forall t. (~t) -> t"
    );
}

#[test]
fn explicit_type_param_identity() {
    // fun id[a](x: a) -> a should produce forall a. fn(a) -> a
    insta::assert_snapshot!(
        infer_module_fn("fun id[a](x: a) -> a = x", "id"),
        @"forall a. (a) -> a"
    );
}

#[test]
fn explicit_type_param_multiple() {
    // fun const[a, b](x: a, y: b) -> a should produce forall a b. fn(a, b) -> a
    insta::assert_snapshot!(
        infer_module_fn("fun const_[a, b](x: a, y: b) -> a = x", "const_"),
        @"forall a b. (a, b) -> a"
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

        fun apply[f[_], a](fa: f[a]) -> f[a] where f: Functor = fmap(fa, x -> x)
    "#;
    insta::assert_snapshot!(infer_module_fn(src, "apply"), @"forall f a. (f[a]) -> f[a]");
}

#[test]
fn explicit_hkt_type_param_wrong_arity_is_error() {
    let src = "fun bad[f[_], a, b](x: f[a, b]) -> f[a] = x";
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    assert!(result.is_err(), "expected kind mismatch");
    let err = result.err().unwrap();
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0507");
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
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    assert!(result.is_ok(), "expected method-level HKTs to typecheck");
}

#[test]
fn no_type_params_still_generalizes() {
    // Unannotated identity should still generalize via HM
    insta::assert_snapshot!(
        infer_module_fn("fun id(x) = x", "id"),
        @"forall a. (a) -> a"
    );
}

#[test]
fn explicit_type_args_call_site_success() {
    let src = r#"
        fun identity[a](x: a) -> a = x
        fun use_it() = identity[Int](42)
    "#;
    insta::assert_snapshot!(infer_module_fn(src, "use_it"), @"() -> Int");
}

#[test]
fn explicit_type_args_call_site_mismatch_is_error() {
    let src = r#"
        fun identity[a](x: a) -> a = x
        fun use_it() = identity[Int]("hello")
    "#;
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    assert!(result.is_err(), "expected mismatch error");
    let err = result.err().unwrap();
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0001");
}

#[test]
fn explicit_type_args_wrong_count_is_error() {
    let src = r#"
        fun identity[a](x: a) -> a = x
        fun use_it() = identity[Int, String](42)
    "#;
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    assert!(result.is_err(), "expected wrong arity error");
    let err = result.err().unwrap();
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0005");
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
    insta::assert_snapshot!(infer_module_fn(src, "use_it"), @"() -> Int");
}

#[test]
fn constrained_polymorphic_function_reference_is_rejected() {
    let src = r#"
        import core/show.{Show}

        fun show_it[a](x: a) -> String where a: Show = show(x)

        fun main() = {
            let r = show_it
            0
        }
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    assert!(result.is_err(), "expected constrained polymorphic ref to fail");
    let err = result.err().unwrap();
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0001");
    let message = err.type_error().unwrap().error.to_string();
    assert!(
        message.contains("first-class constrained polymorphic function values"),
        "unexpected error message: {message}"
    );
    assert!(
        message.contains("lambda"),
        "expected lambda guidance in error message: {message}"
    );
}

#[test]
fn explicit_type_args_work_with_methods() {
    let src = r#"
        import core/list.{List, Cons, Nil, map}

        fun stringify(x: Int) -> String = "n"

        fun use_it(xs: List[Int]) = xs.map[String](stringify)
    "#;
    insta::assert_snapshot!(infer_module_fn(src, "use_it"), @"(List[Int]) -> List[String]");
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
        @"(Int) -> Bool"
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
        @"forall a. (a) -> a"
    );
}

#[test]
fn self_referential_type_ok() {
    insta::assert_snapshot!(
        infer_module_fn(
            "type List[a] = Cons(a, List[a]) | Nil\nfun f(x: List[Int]) = x",
            "f"
        ),
        @"(List[Int]) -> List[Int]"
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
        @"(A) -> A"
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
    let modules = infer::infer_module(&module, &FakeResolver, "test".to_string()).unwrap();
    // Main module + mylib
    assert!(
        modules.len() >= 2,
        "expected at least 2 modules, got {}",
        modules.len()
    );
    assert!(
        modules[0].module_path == "test",
        "first module should have path 'test'"
    );
    assert!(
        modules
            .iter()
            .any(|m| m.module_path == "mylib"),
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
    let modules = infer::infer_module(&module, &FakeResolver, "test".to_string()).unwrap();
    // The main module should have `add` in fn_types with provenance
    let main = &modules[0];
    assert!(
        main.fn_types.iter().any(|e| e.name == "add"),
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
    let modules = infer::infer_module(&module, &CountingResolver, "test".to_string()).unwrap();
    // Only one TypedModule for mylib despite resolver being called
    let mylib_count = modules
        .iter()
        .filter(|m| m.module_path == "mylib")
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
    let result = infer::infer_module(&module, &CircularResolver, "test".to_string());
    assert!(result.is_err(), "should detect circular import");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected circular import error"),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0502");
}

#[test]
fn infer_module_stdlib_own_typed_module() {
    let src = r#"
        import core/option.{Some, None}
        fun wrap(x: Int) -> Option[Int] = Some(x)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty());
    let modules = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string()).unwrap();
    // Should have a TypedModule for core/option
    assert!(
        modules
            .iter()
            .any(|m| m.module_path == "core/option"),
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
    let modules = infer::infer_module(&module, &FakeResolver, "test".to_string()).unwrap();
    let main = &modules[0];
    let quad_type = main
        .fn_types
        .iter()
        .find(|e| e.name == "quadruple")
        .unwrap();
    assert_eq!(format!("{}", quad_type.scheme), "(Int) -> Int");
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
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_err(), "importing private fn should fail");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0503");

    // Importing only the public function should succeed
    let src2 = r#"
        import mylib.{public_fn}
        fun main() -> Int = public_fn()
    "#;
    let (module2, errors2) = parse(src2);
    assert!(errors2.is_empty());
    let result2 = infer::infer_module(&module2, &FakeResolver, "test".to_string());
    assert!(
        result2.is_ok(),
        "importing pub fn should work: {:?}",
        result2.err()
    );
}

#[test]
fn infer_module_bare_import_binds_qualifier() {
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
        fun main() -> Int = mylib.add(1, 2)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_ok(), "bare import should resolve qualified names: {:?}", result.err());
}

#[test]
fn infer_module_import_alias_binds_only_alias() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub fun twice(x: Int) -> Int = x * 2".to_string())
            } else {
                None
            }
        }
    }
    let src = r#"
        import mylib.{twice as double}
        fun main() -> Int = double(2) + twice(2)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_err(), "original import name should stay out of scope");
    let err = match result {
        Err(err) => err,
        Ok(_) => panic!("expected alias-only import to reject original name"),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0003");
}

#[test]
fn infer_module_missing_qualified_export_errors_clearly() {
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
        fun main() -> Int = mylib.missing(1, 2)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_err(), "missing qualified export should fail");
    let err = match result {
        Err(err) => err,
        Ok(_) => panic!("expected missing qualified export to fail"),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0508");
}

#[test]
fn infer_module_qualifier_used_as_value_errors_clearly() {
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
        fun main() -> Int = { let m = mylib; 0 }
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_err(), "module qualifier as value should fail");
    let err = match result {
        Err(err) => err,
        Ok(_) => panic!("expected module qualifier value use to fail"),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0504");
}

#[test]
fn infer_module_qualified_nullary_constructor_value_resolves() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub type Option[a] = Some(a) | None".to_string())
            } else {
                None
            }
        }
    }
    let src = r#"
        import mylib
        fun main() -> Option[Int] = mylib.None
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(
        result.is_ok(),
        "qualified nullary constructor should resolve as a value: {:?}",
        result.err()
    );
}

#[test]
fn infer_module_qualified_constructor_call_typechecks() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub type Box[a] = Box(a)".to_string())
            } else {
                None
            }
        }
    }
    // mylib.Box(42) is desugared by the parser to UFCS: Box(mylib, 42)
    // The typechecker's reverse-app qualified-call path handles this.
    // Verifies that qualified constructor calls resolve correctly and
    // the is_constructor check uses the exported name (not internal local_name).
    let src = r#"
        import mylib
        fun main() -> Box[Int] = mylib.Box(42)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(
        result.is_ok(),
        "qualified constructor call should succeed: {:?}",
        result.err()
    );
    let modules = result.unwrap();
    let main_ty = modules[0]
        .fn_types
        .iter()
        .find(|e| e.name == "main")
        .map(|e| format!("{}", e.scheme))
        .expect("main not found");
    assert_eq!(main_ty, "() -> Box[Int]");
}

#[test]
fn infer_module_constructor_alias_resolves() {
    struct FakeResolver;
    impl ModuleResolver for FakeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            if module_path == "mylib" {
                Some("pub type Box[a] = Box(a)".to_string())
            } else {
                None
            }
        }
    }
    let src = r#"
        import mylib.{Box as MkBox}
        fun main() = MkBox(1)
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_ok(), "constructor alias should resolve: {:?}", result.err().map(|e| e.type_error().map(|te| te.error.error_code().to_string())));
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
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(
        result.is_ok(),
        "pub import re-export should succeed: {:?}",
        result.err()
    );
    let modules = result.unwrap();
    // Main module should have helper in its fn_types
    let main_mod = &modules[0];
    assert!(
        main_mod.fn_types.iter().any(|e| e.name == "helper"),
        "main module should have 'helper' in fn_types"
    );
    // qualified_name should point to the original module (lib_a), not the facade
    let helper_entry = main_mod.fn_types.iter().find(|e| e.name == "helper").unwrap();
    assert_eq!(helper_entry.qualified_name.module_path, "lib_a");
    assert_eq!(helper_entry.qualified_name.local_name, "helper");
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
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(
        result.is_err(),
        "pub import of non-existent name should fail"
    );
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0510");
}

#[test]
fn cross_module_deriving_show() {
    use krypton_modules::module_resolver::StdlibResolver;
    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, path: &str) -> Option<String> {
            match path {
                "mylib" => Some("pub type Point = { x: Int, y: Int } deriving (Show)".into()),
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
    let result = infer::infer_module(&module, &Resolver, "test".to_string());
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
                "mylib" => Some("pub type Box[a] = Box(a) deriving (Show)".into()),
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
    let result = infer::infer_module(&module, &Resolver, "test".to_string());
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
                "mylib" => Some("pub type Box[a] = Box(a) deriving (Show)".into()),
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
    let err = match infer::infer_module(&module, &Resolver, "test".to_string()) {
        Ok(_) => panic!("expected E0301"),
        Err(err) => err,
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0301");
}

#[test]
fn cross_module_derived_instance_exports_constraint_metadata() {
    use krypton_modules::module_resolver::StdlibResolver;
    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, path: &str) -> Option<String> {
            match path {
                "mylib" => Some("pub type Box[a] = Box(a) deriving (Show)".into()),
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
    let modules = infer::infer_module(&module, &Resolver, "test".to_string()).expect("typecheck should succeed");
    let imported = modules
        .iter()
        .find(|typed_module| typed_module.module_path == "mylib")
        .expect("expected imported mylib module");
    let instance = imported
        .instance_defs
        .iter()
        .find(|inst| inst.trait_name.local_name == "Show" && inst.target_type_name == "Box")
        .expect("expected derived Show[Box[a]] instance");

    assert_eq!(instance.constraints.len(), 1);
    assert_eq!(instance.constraints[0].trait_name.local_name, "Show");
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
    let result = infer::infer_module(&module, &StdlibResolver, "test".to_string());
    assert!(
        result.is_ok(),
        "local shadowed prelude type should derive Show independently: {:?}",
        result.err()
    );
}

#[test]
fn empty_impl_is_rejected() {
    let src = r#"
        type Player2 = { name: String, score: (Int) -> Int }

        impl Show[Player2] {
        }

        fun main() = 0
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let err = match infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string()) {
        Ok(_) => panic!("expected E0306"),
        Err(err) => err,
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0306");
    assert!(
        err.type_error().unwrap().error
            .help()
            .unwrap_or_default()
            .contains("missing method(s): show"),
        "unexpected help text: {:?}",
        err.type_error().unwrap().error.help()
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
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(result.is_err(), "importing private trait should fail");
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0503");

    // Wildcard import should silently skip private traits
    let src2 = r#"
        import traitlib.{public_fn}
        fun main() -> Int = public_fn()
    "#;
    let (module2, errors2) = parse(src2);
    assert!(errors2.is_empty());
    let result2 = infer::infer_module(&module2, &FakeResolver, "test".to_string());
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
    let result = infer::infer_module(&module, &FakeResolver, "test".to_string());
    assert!(
        result.is_err(),
        "import of module with parse errors should fail"
    );
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert!(
        matches!(err, infer::InferError::ModuleParseError { ref path, .. } if path == "broken"),
        "expected ModuleParseError for 'broken', got: {err:?}"
    );
}

#[test]
fn let_type_annotation_correct() {
    let result = infer_module_fn("fun f() -> Int { let x: Int = 5; x }", "f");
    assert_eq!(result, "() -> Int");
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
    assert_eq!(result, "() -> Vec[Int]");
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
        r#"extern java "java/io/PrintStream" {
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
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    assert!(result.is_err(), "should reject __krypton_intrinsic");
    let err = match result {
        Err(e) => e,
        Ok(_) => unreachable!(),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0012");
}

#[test]
fn reserved_name_krypton_prefix_rejected() {
    let src = "fun __krypton_foo() = 1\nfun main() = __krypton_foo()";
    let module = parse_module(src);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    assert!(result.is_err(), "should reject __krypton_ prefix");
    let err = match result {
        Err(e) => e,
        Ok(_) => unreachable!(),
    };
    assert_eq!(err.type_error().unwrap().error.error_code().to_string(), "E0012");
}

#[test]
fn non_reserved_name_allowed() {
    // A user function named "intrinsic" (without __krypton_ prefix) should be fine
    let result = infer_module_fn(
        "fun intrinsic() = 42\nfun main() = intrinsic()",
        "intrinsic",
    );
    assert_eq!(result, "() -> Int");
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
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
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
            fun get_score(p: Player) -> Int = apply(p, (x) -> x.score)
        "#),
        @"
    eq: forall a. (a, a) -> Bool
    lt: forall a. (a, a) -> Bool
    combine: forall a. (a, a) -> a
    sub: forall a. (a, a) -> a
    mul: forall a. (a, a) -> a
    div: forall a. (a, a) -> a
    neg: forall a. (a) -> a
    show: forall a. (a) -> String
    hash: forall a. (a) -> Int
    close: forall a. (~a) -> Unit
    peek: forall a. (a) -> a
    last: forall a. (List[a]) -> Option[a]
    sort_by: forall b a. (List[a], (a) -> b) -> List[a]
    filter: forall a. (List[a], (a) -> Bool) -> List[a]
    fold: forall a b. (List[a], b, (b, a) -> b) -> b
    map: forall a b. (List[a], (a) -> b) -> List[b]
    to_list: forall a. (Vec[a]) -> List[a]
    println: forall a. (a) -> Unit
    Some: forall a. (a) -> Option[a]
    None: forall a. Option[a]
    Ok: forall a b. (b) -> Result[a, b]
    Err: forall a b. (a) -> Result[a, b]
    Cons: forall a. (a, List[a]) -> List[a]
    Nil: forall a. List[a]
    LT: Ordering
    EQ: Ordering
    GT: Ordering
    Player: (String, Int) -> Player
    apply: (Player, (Player) -> Int) -> Int
    get_score: (Player) -> Int
    "
    );
}

#[test]
fn shadowed_prelude_fn_note_on_ufcs_mismatch() {
    // Importing filter from core/vec shadows prelude's core/list.filter.
    // Chaining .filter(...).map(...) should fail (Vec vs List) with a note about shadowing.
    let src = r#"
        import core/vec.{filter}
        fun main() = {
            let xs = Cons(1, Cons(2, Nil))
            xs.filter(x -> eq(x, 1)).map(x -> x + 1)
        }
    "#;
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &CompositeResolver::stdlib_only(), "test".to_string());
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("should fail with type mismatch"),
    };
    let te = err.type_error().expect("should be a type error");
    let note = te.note.as_ref().expect("should have a note about shadowing");
    assert!(
        note.contains("shadowed"),
        "note should mention shadowing, got: {note}"
    );
    assert!(
        note.contains("filter"),
        "note should mention the shadowed function name, got: {note}"
    );
}

// ── Alpha-renaming / user type param names ──

#[test]
fn infer_user_type_param_names_preserved() {
    insta::assert_snapshot!(
        infer_module_fn("fun identity[elem](x: elem) -> elem = x", "identity"),
        @"forall elem. (elem) -> elem"
    );
}

#[test]
fn infer_user_type_param_names_multi() {
    insta::assert_snapshot!(
        infer_module_fn("fun swap[a, b](x: a, y: b) -> (b, a) = (y, x)", "swap"),
        @"forall a b. (a, b) -> (b, a)"
    );
}

#[test]
fn infer_anonymous_vars_renumbered() {
    insta::assert_snapshot!(
        infer_module_fn("fun id(x) = x", "id"),
        @"forall a. (a) -> a"
    );
}
