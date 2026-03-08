use krypton_parser::ast::*;
use krypton_parser::parser::parse;
use krypton_parser::pretty::pretty_print;
use insta::assert_snapshot;

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
            name,
            type_var,
            superclasses,
            methods,
            ..
        } => Decl::DefTrait {
            name: name.clone(),
            type_var: type_var.clone(),
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
        Decl::Import { path, names, .. } => Decl::Import {
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
            return_type,
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
            return_type: return_type.as_ref().map(zero_spans_type_expr),
            body: Box::new(zero_spans_expr(body)),
            span: (0, 0),
        },
        Expr::Let {
            name, value, body, ..
        } => Expr::Let {
            name: name.clone(),
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
        Expr::LetPattern { pattern, value, body, .. } => Expr::LetPattern {
            pattern: zero_spans_pattern(pattern),
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

/// Parse source, pretty-print, re-parse, and assert the ASTs match (with spans zeroed).
fn assert_roundtrip(input: &str) {
    let (module1, errors1) = parse(input);
    assert!(errors1.is_empty(), "parse errors on input: {errors1:?}");

    let printed = pretty_print(&module1);
    let (module2, errors2) = parse(&printed);
    assert!(
        errors2.is_empty(),
        "parse errors on pretty-printed output: {errors2:?}\nprinted: {printed}"
    );

    let norm1 = zero_spans_module(&module1);
    let norm2 = zero_spans_module(&module2);
    assert_eq!(norm1, norm2, "round-trip mismatch!\ninput:   {input}\nprinted: {printed}");
}

// --- Round-trip tests ---

#[test]
fn roundtrip_simple_untyped_fn() {
    assert_roundtrip("(def add (fn [a b] (+ a b)))");
}

#[test]
fn roundtrip_typed_fn() {
    assert_roundtrip(
        "(def factorial (fn [n] [Int] Int (if (<= n 1) 1 (* n (factorial (- n 1))))))",
    );
}

#[test]
fn roundtrip_record_type() {
    assert_roundtrip("(type Point (record (x Int) (y Int)))");
}

#[test]
fn roundtrip_sum_type_with_deriving() {
    assert_roundtrip("(type Option [a] (| (Some a) None) deriving [Eq Show])");
}

#[test]
fn roundtrip_match_expr() {
    assert_roundtrip("(def f (fn [x] (match x ((Some v) v) (None 0))))");
}

#[test]
fn roundtrip_do_block_with_lets() {
    assert_roundtrip("(def main (fn [] (do (let x 1) (let y 2) (+ x y))))");
}

#[test]
fn roundtrip_trait_decl() {
    assert_roundtrip("(trait Eq [a] (def eq [a a] Bool))");
}

#[test]
fn roundtrip_trait_with_superclass() {
    assert_roundtrip("(trait Ord [a] : [Eq] (def compare [a a] Ordering))");
}

#[test]
fn roundtrip_impl() {
    assert_roundtrip("(impl Eq Point (def eq [a b] (== a b)))");
}

#[test]
fn roundtrip_import() {
    assert_roundtrip("(import core.option [Option Some None])");
}

#[test]
fn roundtrip_lambda() {
    assert_roundtrip("(def f (fn [x] (fn [y] (+ x y))))");
}

#[test]
fn roundtrip_list() {
    assert_roundtrip("(def f (fn [] (list 1 2 3)))");
}

#[test]
fn roundtrip_tuple() {
    assert_roundtrip("(def f (fn [] (tuple 1 2 3)))");
}

#[test]
fn roundtrip_field_access() {
    assert_roundtrip("(def f (fn [p] (. p x)))");
}

#[test]
fn roundtrip_question_mark() {
    assert_roundtrip("(def f (fn [x] (? x)))");
}

#[test]
fn roundtrip_recur() {
    assert_roundtrip("(def f (fn [n] (recur (- n 1))))");
}

#[test]
fn roundtrip_string_literal() {
    assert_roundtrip("(def f (fn [] \"hello world\"))");
}

#[test]
fn roundtrip_bool_literals() {
    assert_roundtrip("(def f (fn [] (if true 1 0)))");
}

#[test]
fn roundtrip_all_binops() {
    assert_roundtrip("(def f (fn [a b] (+ (- (* (/ a b) a) b) (== a (< b (!= a (> b (<= a (>= a b)))))))))");
}

#[test]
fn roundtrip_tuple_pattern() {
    assert_roundtrip("(def f (fn [x] (match x ((tuple a b) (+ a b)))))");
}

#[test]
fn roundtrip_let_pattern_tuple() {
    assert_roundtrip("(def f (fn [p] (do (let (tuple a b) p) a)))");
}

#[test]
fn roundtrip_wildcard_pattern() {
    assert_roundtrip("(def f (fn [x] (match x (_ 0))))");
}

#[test]
fn roundtrip_extern_java() {
    assert_roundtrip("(extern \"java.lang.Math\" (def abs [Int] Int) (def max [Int Int] Int))");
}

#[test]
fn roundtrip_extern_no_methods() {
    assert_roundtrip("(extern \"java.lang.Math\")");
}

// --- Snapshot test ---

#[test]
fn snapshot_multi_decl_program() {
    let input = "\
(import core.option [Option Some None])
(type Point (record (x Int) (y Int)))
(type Option [a] (| (Some a) None) deriving [Eq Show])
(trait Eq [a] (def eq [a a] Bool))
(impl Eq Point (def eq [a b] (== a b)))
(def add (fn [a b] [Int Int] Int (+ a b)))
(def main (fn [] (do (let x 1) (let y 2) (+ x y))))";

    let (module, errors) = parse(input);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let output = pretty_print(&module);
    assert_snapshot!(output);
}
