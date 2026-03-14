use krypton_parser::ast::*;
use krypton_parser::parser::parse;
use krypton_parser::pretty::{pretty_print, pretty_print_with, PrettyConfig};
use insta::assert_snapshot;

// --- Zero-span helpers (copied from pretty_test.rs) ---

fn zero_spans_module(module: &Module) -> Module {
    Module {
        decls: module.decls.iter().map(zero_spans_decl).collect(),
    }
}

fn zero_spans_decl(decl: &Decl) -> Decl {
    match decl {
        Decl::DefFn(f) => Decl::DefFn(zero_spans_fn_decl(f)),
        Decl::DefType(t) => Decl::DefType(zero_spans_type_decl(t)),
        Decl::DefTrait {
            visibility,
            name,
            type_param,
            superclasses,
            methods,
            ..
        } => Decl::DefTrait {
            visibility: visibility.clone(),
            name: name.clone(),
            type_param: TypeParam {
                name: type_param.name.clone(),
                arity: type_param.arity,
                span: (0, 0),
            },
            superclasses: superclasses.clone(),
            methods: methods.iter().map(zero_spans_fn_decl).collect(),
            span: (0, 0),
        },
        Decl::DefImpl {
            trait_name,
            target_type,
            type_constraints,
            methods,
            ..
        } => Decl::DefImpl {
            trait_name: trait_name.clone(),
            target_type: zero_spans_type_expr(target_type),
            type_constraints: type_constraints
                .iter()
                .map(|c| TypeConstraint {
                    trait_name: c.trait_name.clone(),
                    type_var: c.type_var.clone(),
                    span: (0, 0),
                })
                .collect(),
            methods: methods.iter().map(zero_spans_fn_decl).collect(),
            span: (0, 0),
        },
        Decl::Import { is_pub, path, names, .. } => Decl::Import {
            is_pub: *is_pub,
            path: path.clone(),
            names: names.clone(),
            span: (0, 0),
        },
        Decl::ExternJava {
            class_name,
            methods,
            ..
        } => Decl::ExternJava {
            class_name: class_name.clone(),
            methods: methods
                .iter()
                .map(|m| ExternMethod {
                    visibility: m.visibility.clone(),
                    name: m.name.clone(),
                    param_types: m.param_types.iter().map(zero_spans_type_expr).collect(),
                    return_type: zero_spans_type_expr(&m.return_type),
                    span: (0, 0),
                })
                .collect(),
            span: (0, 0),
        },
    }
}

fn zero_spans_fn_decl(f: &FnDecl) -> FnDecl {
    FnDecl {
        name: f.name.clone(),
        visibility: f.visibility.clone(),
        type_params: f.type_params.clone(),
        params: f
            .params
            .iter()
            .map(|p| Param {
                name: p.name.clone(),
                ty: p.ty.as_ref().map(zero_spans_type_expr),
                span: (0, 0),
            })
            .collect(),
        constraints: f
            .constraints
            .iter()
            .map(|c| TypeConstraint {
                trait_name: c.trait_name.clone(),
                type_var: c.type_var.clone(),
                span: (0, 0),
            })
            .collect(),
        return_type: f.return_type.as_ref().map(zero_spans_type_expr),
        body: Box::new(zero_spans_expr(&f.body)),
        span: (0, 0),
    }
}

fn zero_spans_type_decl(t: &TypeDecl) -> TypeDecl {
    TypeDecl {
        name: t.name.clone(),
        visibility: t.visibility.clone(),
        type_params: t.type_params.clone(),
        kind: match &t.kind {
            TypeDeclKind::Record { fields } => TypeDeclKind::Record {
                fields: fields
                    .iter()
                    .map(|(n, ty)| (n.clone(), zero_spans_type_expr(ty)))
                    .collect(),
            },
            TypeDeclKind::Sum { variants } => TypeDeclKind::Sum {
                variants: variants
                    .iter()
                    .map(|v| Variant {
                        name: v.name.clone(),
                        fields: v.fields.iter().map(zero_spans_type_expr).collect(),
                        span: (0, 0),
                    })
                    .collect(),
            },
        },
        deriving: t.deriving.clone(),
        span: (0, 0),
    }
}

fn zero_spans_expr(expr: &Expr) -> Expr {
    match expr {
        Expr::Lit { value, .. } => Expr::Lit {
            value: value.clone(),
            span: (0, 0),
        },
        Expr::Var { name, .. } => Expr::Var {
            name: name.clone(),
            span: (0, 0),
        },
        Expr::BinaryOp { op, lhs, rhs, .. } => Expr::BinaryOp {
            op: op.clone(),
            lhs: Box::new(zero_spans_expr(lhs)),
            rhs: Box::new(zero_spans_expr(rhs)),
            span: (0, 0),
        },
        Expr::UnaryOp { op, operand, .. } => Expr::UnaryOp {
            op: op.clone(),
            operand: Box::new(zero_spans_expr(operand)),
            span: (0, 0),
        },
        Expr::Lambda {
            params,
            body,
            ..
        } => Expr::Lambda {
            params: params
                .iter()
                .map(|p| Param {
                    name: p.name.clone(),
                    ty: p.ty.as_ref().map(zero_spans_type_expr),
                    span: (0, 0),
                })
                .collect(),
            body: Box::new(zero_spans_expr(body)),
            span: (0, 0),
        },
        Expr::Let {
            name, ty, value, body, ..
        } => Expr::Let {
            name: name.clone(),
            ty: ty.as_ref().map(zero_spans_type_expr),
            value: Box::new(zero_spans_expr(value)),
            body: body.as_ref().map(|b| Box::new(zero_spans_expr(b))),
            span: (0, 0),
        },
        Expr::Do { exprs, .. } => Expr::Do {
            exprs: exprs.iter().map(zero_spans_expr).collect(),
            span: (0, 0),
        },
        Expr::If {
            cond, then_, else_, ..
        } => Expr::If {
            cond: Box::new(zero_spans_expr(cond)),
            then_: Box::new(zero_spans_expr(then_)),
            else_: Box::new(zero_spans_expr(else_)),
            span: (0, 0),
        },
        Expr::App { func, args, .. } => Expr::App {
            func: Box::new(zero_spans_expr(func)),
            args: args.iter().map(zero_spans_expr).collect(),
            span: (0, 0),
        },
        Expr::TypeApp {
            expr, type_args, ..
        } => Expr::TypeApp {
            expr: Box::new(zero_spans_expr(expr)),
            type_args: type_args.iter().map(zero_spans_type_expr).collect(),
            span: (0, 0),
        },
        Expr::Match {
            scrutinee, arms, ..
        } => Expr::Match {
            scrutinee: Box::new(zero_spans_expr(scrutinee)),
            arms: arms.iter().map(zero_spans_match_arm).collect(),
            span: (0, 0),
        },
        Expr::FieldAccess { expr, field, .. } => Expr::FieldAccess {
            expr: Box::new(zero_spans_expr(expr)),
            field: field.clone(),
            span: (0, 0),
        },
        Expr::QuestionMark { expr, .. } => Expr::QuestionMark {
            expr: Box::new(zero_spans_expr(expr)),
            span: (0, 0),
        },
        Expr::List { elements, .. } => Expr::List {
            elements: elements.iter().map(zero_spans_expr).collect(),
            span: (0, 0),
        },
        Expr::Tuple { elements, .. } => Expr::Tuple {
            elements: elements.iter().map(zero_spans_expr).collect(),
            span: (0, 0),
        },
        Expr::Recur { args, .. } => Expr::Recur {
            args: args.iter().map(zero_spans_expr).collect(),
            span: (0, 0),
        },
        Expr::StructLit { name, fields, .. } => Expr::StructLit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(n, e)| (n.clone(), zero_spans_expr(e)))
                .collect(),
            span: (0, 0),
        },
        Expr::LetPattern {
            pattern,
            ty,
            value,
            body,
            ..
        } => Expr::LetPattern {
            pattern: zero_spans_pattern(pattern),
            ty: ty.as_ref().map(zero_spans_type_expr),
            value: Box::new(zero_spans_expr(value)),
            body: body.as_ref().map(|b| Box::new(zero_spans_expr(b))),
            span: (0, 0),
        },
        Expr::StructUpdate { base, fields, .. } => Expr::StructUpdate {
            base: Box::new(zero_spans_expr(base)),
            fields: fields
                .iter()
                .map(|(n, e)| (n.clone(), zero_spans_expr(e)))
                .collect(),
            span: (0, 0),
        },
    }
}

fn zero_spans_match_arm(arm: &MatchArm) -> MatchArm {
    MatchArm {
        pattern: zero_spans_pattern(&arm.pattern),
        guard: arm.guard.as_ref().map(|g| Box::new(zero_spans_expr(g))),
        body: zero_spans_expr(&arm.body),
        span: (0, 0),
    }
}

fn zero_spans_pattern(pat: &Pattern) -> Pattern {
    match pat {
        Pattern::Wildcard { .. } => Pattern::Wildcard { span: (0, 0) },
        Pattern::Var { name, .. } => Pattern::Var {
            name: name.clone(),
            span: (0, 0),
        },
        Pattern::Constructor { name, args, .. } => Pattern::Constructor {
            name: name.clone(),
            args: args.iter().map(zero_spans_pattern).collect(),
            span: (0, 0),
        },
        Pattern::Lit { value, .. } => Pattern::Lit {
            value: value.clone(),
            span: (0, 0),
        },
        Pattern::Tuple { elements, .. } => Pattern::Tuple {
            elements: elements.iter().map(zero_spans_pattern).collect(),
            span: (0, 0),
        },
        Pattern::StructPat {
            name, fields, rest, ..
        } => Pattern::StructPat {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(n, p)| (n.clone(), zero_spans_pattern(p)))
                .collect(),
            rest: *rest,
            span: (0, 0),
        },
    }
}

fn zero_spans_type_expr(ty: &TypeExpr) -> TypeExpr {
    match ty {
        TypeExpr::Named { name, .. } => TypeExpr::Named {
            name: name.clone(),
            span: (0, 0),
        },
        TypeExpr::Var { name, .. } => TypeExpr::Var {
            name: name.clone(),
            span: (0, 0),
        },
        TypeExpr::App { name, args, .. } => TypeExpr::App {
            name: name.clone(),
            args: args.iter().map(zero_spans_type_expr).collect(),
            span: (0, 0),
        },
        TypeExpr::Fn { params, ret, .. } => TypeExpr::Fn {
            params: params.iter().map(zero_spans_type_expr).collect(),
            ret: Box::new(zero_spans_type_expr(ret)),
            span: (0, 0),
        },
        TypeExpr::Own { inner, .. } => TypeExpr::Own {
            inner: Box::new(zero_spans_type_expr(inner)),
            span: (0, 0),
        },
        TypeExpr::Tuple { elements, .. } => TypeExpr::Tuple {
            elements: elements.iter().map(zero_spans_type_expr).collect(),
            span: (0, 0),
        },
    }
}

// --- Round-trip helper ---

fn assert_surface_roundtrip(input: &str) {
    let (module1, errors1) = parse(input);
    assert!(
        errors1.is_empty(),
        "parse errors on input: {errors1:?}\ninput: {input}"
    );

    let printed = pretty_print(&module1);
    let (module2, errors2) = parse(&printed);
    assert!(
        errors2.is_empty(),
        "parse errors on pretty-printed output: {errors2:?}\nprinted:\n{printed}"
    );

    let norm1 = zero_spans_module(&module1);
    let norm2 = zero_spans_module(&module2);
    assert_eq!(
        norm1, norm2,
        "round-trip mismatch!\ninput:   {input}\nprinted: {printed}"
    );
}

// --- Round-trip tests ---

#[test]
fn roundtrip_literal_int() {
    assert_surface_roundtrip("fun f() -> Int = 42");
}

#[test]
fn roundtrip_literal_float() {
    assert_surface_roundtrip("fun f() -> Float = 3.14");
}

#[test]
fn roundtrip_literal_string() {
    assert_surface_roundtrip("fun f() -> String = \"hello world\"");
}

#[test]
fn roundtrip_literal_bool() {
    assert_surface_roundtrip("fun f() -> Bool = true");
}

#[test]
fn roundtrip_literal_unit() {
    assert_surface_roundtrip("fun f() = ()");
}

#[test]
fn roundtrip_variable() {
    assert_surface_roundtrip("fun f(x: Int) -> Int = x");
}

#[test]
fn roundtrip_hkt_type_params_on_function() {
    assert_surface_roundtrip("fun apply[f[_], a](fa: f[a]) -> f[a] = fa");
}

#[test]
fn roundtrip_explicit_type_application() {
    assert_surface_roundtrip("fun f() = identity[Int](42)\nfun g() = identity[Int]");
}

#[test]
fn roundtrip_binary_ops() {
    assert_surface_roundtrip("fun f(a: Int, b: Int) -> Int = a + b");
}

#[test]
fn roundtrip_binary_precedence() {
    assert_surface_roundtrip("fun f() -> Int = 1 + 2 * 3");
}

#[test]
fn roundtrip_binary_all_ops() {
    assert_surface_roundtrip("fun f(a: Int, b: Int) -> Bool = a + b > a * b");
}

#[test]
fn roundtrip_boolean_ops() {
    assert_surface_roundtrip("fun f(a: Bool, b: Bool) -> Bool = a && b || !a");
}

#[test]
fn roundtrip_unary_neg() {
    assert_surface_roundtrip("fun f(x: Int) -> Int = -x");
}

#[test]
fn roundtrip_unary_not() {
    assert_surface_roundtrip("fun f(x: Bool) -> Bool = !x");
}

#[test]
fn roundtrip_fn_expr_body() {
    assert_surface_roundtrip("fun add(a: Int, b: Int) -> Int = a + b");
}

#[test]
fn roundtrip_fn_block_body() {
    assert_surface_roundtrip("fun f() -> Int { let x = 1; let y = 2; x + y }");
}

#[test]
fn roundtrip_fn_untyped_params() {
    assert_surface_roundtrip("fun f(x) = x");
}

#[test]
fn roundtrip_fn_typed_params() {
    assert_surface_roundtrip("fun f(x: Int, y: Int) -> Int = x + y");
}

#[test]
fn roundtrip_pub_fun() {
    assert_surface_roundtrip("pub fun add(a: Int, b: Int) -> Int = a + b");
}

#[test]
fn roundtrip_record_type() {
    assert_surface_roundtrip("type Point = { x: Int, y: Int }");
}

#[test]
fn roundtrip_sum_type() {
    assert_surface_roundtrip("type Option[a] = Some(a) | None");
}

#[test]
fn roundtrip_pub_open_type() {
    assert_surface_roundtrip("pub type Color = Red | Green | Blue");
}

#[test]
fn roundtrip_opaque_type() {
    assert_surface_roundtrip("pub opaque type Opaque = { inner: Int }");
}

#[test]
fn roundtrip_deriving() {
    assert_surface_roundtrip("type Color = Red | Green | Blue deriving (Eq, Show)");
}

#[test]
fn roundtrip_import_with_names() {
    assert_surface_roundtrip("import core/option.{Option, Some, None}");
}

#[test]
fn roundtrip_import_bare() {
    assert_surface_roundtrip("import core/option");
}

#[test]
fn roundtrip_import_alias() {
    assert_surface_roundtrip("import core/list.{List, map as listMap}");
}

#[test]
fn roundtrip_trait() {
    assert_surface_roundtrip(
        r#"trait Eq[a] {
    fun eq(self: a, other: a) -> Bool
}"#,
    );
}

#[test]
fn roundtrip_trait_with_superclass() {
    assert_surface_roundtrip(
        r#"trait Ord[a] where a: Eq {
    fun compare(self: a, other: a) -> Ordering
}"#,
    );
}

#[test]
fn roundtrip_impl() {
    let src = r#"impl Eq[Point] {
    fun eq(a, b) = a.x == b.x
}"#;
    assert_surface_roundtrip(src);
}

#[test]
fn roundtrip_extern() {
    let src = r#"extern "java.lang.Math" {
    fun abs(Int) -> Int
    fun max(Int, Int) -> Int
}"#;
    assert_surface_roundtrip(src);
}

#[test]
fn roundtrip_if_else() {
    assert_surface_roundtrip("fun f(x: Int) -> Int = if x > 0 { x } else { -x }");
}

#[test]
fn roundtrip_if_no_else() {
    assert_surface_roundtrip("fun f(x: Int) = if x > 0 { x }");
}

#[test]
fn roundtrip_match() {
    let src = r#"fun f(x: Option[Int]) -> Int = match x {
    Some(v) => v,
    None => 0,
}"#;
    assert_surface_roundtrip(src);
}

#[test]
fn roundtrip_match_guard() {
    let src = r#"fun f(x: Option[Int]) -> Int = match x {
    Some(v) if v > 0 => v,
    _ => 0,
}"#;
    assert_surface_roundtrip(src);
}

#[test]
fn roundtrip_do_block() {
    assert_surface_roundtrip("fun f() -> Int { let x = 1; let y = 2; x + y }");
}

#[test]
fn roundtrip_lambda_single() {
    assert_surface_roundtrip("fun f() -> (Int) -> Int = x -> x + 1");
}

#[test]
fn roundtrip_lambda_multi() {
    assert_surface_roundtrip("fun f() = (x, y) -> x + y");
}

#[test]
fn roundtrip_lambda_typed() {
    assert_surface_roundtrip("fun f() = (x: Int) -> x + 1");
}

#[test]
fn roundtrip_field_access() {
    assert_surface_roundtrip("fun f(p: Point) -> Int = p.x");
}

#[test]
fn roundtrip_question_mark() {
    assert_surface_roundtrip("fun f(x: Option[Int]) -> Int = x?");
}

#[test]
fn roundtrip_recur() {
    assert_surface_roundtrip(
        "fun f(n: Int) -> Int = if n <= 1 { 1 } else { n * recur(n - 1) }",
    );
}

#[test]
fn roundtrip_list() {
    assert_surface_roundtrip("fun f() = [1, 2, 3]");
}

#[test]
fn roundtrip_tuple() {
    assert_surface_roundtrip("fun f() = (1, 2, 3)");
}

#[test]
fn roundtrip_struct_literal() {
    assert_surface_roundtrip("fun f() -> Point = Point { x = 1, y = 2 }");
}

#[test]
fn roundtrip_struct_update() {
    assert_surface_roundtrip("fun f(p: Point) -> Point = { p | x = 10 }");
}

#[test]
fn roundtrip_where_clause() {
    assert_surface_roundtrip("fun compare(a: a, b: a) -> Bool where a: Ord = a < b");
}

#[test]
fn roundtrip_function_call() {
    assert_surface_roundtrip("fun f(x: Int) -> Int = add(x, 1)");
}

#[test]
fn roundtrip_let_pattern() {
    assert_surface_roundtrip("fun f() { let (a, b) = (1, 2); a + b }");
}

#[test]
fn roundtrip_wildcard_pattern() {
    let src = r#"fun f(x: Int) -> Int = match x {
    _ => 0,
}"#;
    assert_surface_roundtrip(src);
}

#[test]
fn roundtrip_pub_import() {
    assert_surface_roundtrip("pub import core/option.{Option, Some, None}");
}

// --- Operator precedence tests ---

#[test]
fn roundtrip_precedence_add_mul() {
    // 1 + 2 * 3 should parse as 1 + (2 * 3) and round-trip correctly
    let input = "fun f() -> Int = 1 + 2 * 3";
    let (module1, _) = parse(input);
    let printed = pretty_print(&module1);
    assert!(
        printed.contains("1 + 2 * 3"),
        "expected no extra parens, got: {printed}"
    );
    assert_surface_roundtrip(input);
}

#[test]
fn roundtrip_precedence_left_assoc() {
    // (1 - 2) - 3 should not need parens, 1 - (2 - 3) would
    assert_surface_roundtrip("fun f() -> Int = 1 - 2 - 3");
}

// --- Snapshot test ---

#[test]
fn snapshot_multi_decl_program() {
    let input = r#"import core/option.{Option, Some, None}

type Point = { x: Int, y: Int }

type Option[a] = Some(a) | None deriving (Eq, Show)

trait Eq[a] {
    fun eq(self: a, other: a) -> Bool
}

impl Eq[Point] {
    fun eq(a, b) = a.x == b.x && a.y == b.y
}

pub fun add(a: Int, b: Int) -> Int = a + b

fun main() -> Int {
    let x = 1;
    let y = 2;
    add(x, y)
}"#;

    let (module, errors) = parse(input);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let output = pretty_print(&module);
    assert_snapshot!(output);
    // Also verify round-trip
    assert_surface_roundtrip(input);
}

// --- Config test ---

#[test]
fn configurable_indent_width() {
    let input = r#"fun main() -> Int {
    let x = 1;
    let y = 2;
    x + y
}"#;
    let (module, errors) = parse(input);
    assert!(errors.is_empty(), "parse errors: {errors:?}");

    let config = PrettyConfig { indent_width: 2 };
    let output = pretty_print_with(&module, &config);
    // With 2-space indent, the block should use 2 spaces
    assert!(
        output.contains("\n  let x = 1;"),
        "expected 2-space indent, got:\n{output}"
    );
}

#[test]
fn roundtrip_let_type_annotation() {
    assert_surface_roundtrip("fun f() -> Int { let x: Int = 5; x }");
}

#[test]
fn roundtrip_let_pattern_type_annotation() {
    assert_surface_roundtrip("fun f() { let (a, b): (Int, String) = pair; a }");
}
