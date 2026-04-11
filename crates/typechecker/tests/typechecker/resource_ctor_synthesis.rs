//! Snapshot tests for M42-T7: resource-carrying constructor auto-synthesis.
//!
//! When a constructor runs without an expected type (or with an expected type
//! that is an unbound type variable), and the result type is structurally
//! resource-carrying, the typechecker wraps the result in `~` so that `~T` is
//! the only value form a user can observe.

use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_typechecker::infer;
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedModule};

fn typecheck(src: &str) -> TypedModule {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let (mut modules, _) = infer::infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    )
    .expect("inference failed");
    modules.remove(0)
}

/// Locate the `Let` binding whose name is `let_name` anywhere inside `expr`
/// and return a display string of the `value`'s inferred type.
fn find_let_type(expr: &TypedExpr, let_name: &str) -> Option<String> {
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        if let TypedExprKind::Let { name, value, body } = &cur.kind {
            if name == let_name {
                return Some(format!("{}", value.ty));
            }
            stack.push(value);
            if let Some(b) = body {
                stack.push(b);
            }
            continue;
        }
        match &cur.kind {
            TypedExprKind::App { func, args, .. } => {
                stack.push(func);
                stack.extend(args.iter());
            }
            TypedExprKind::If { cond, then_, else_ } => {
                stack.push(cond);
                stack.push(then_);
                stack.push(else_);
            }
            TypedExprKind::Do(exprs) => stack.extend(exprs.iter()),
            TypedExprKind::Match { scrutinee, arms } => {
                stack.push(scrutinee);
                for arm in arms {
                    if let Some(g) = &arm.guard {
                        stack.push(g);
                    }
                    stack.push(&arm.body);
                }
            }
            TypedExprKind::Lambda { body, .. } => stack.push(body),
            TypedExprKind::FieldAccess { expr, .. } => stack.push(expr),
            TypedExprKind::Tuple(items) | TypedExprKind::VecLit(items) => {
                stack.extend(items.iter())
            }
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                stack.push(lhs);
                stack.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => stack.push(operand),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, f) in fields {
                    stack.push(f);
                }
            }
            TypedExprKind::StructUpdate { base, fields } => {
                stack.push(base);
                for (_, f) in fields {
                    stack.push(f);
                }
            }
            TypedExprKind::LetPattern { value, body, .. } => {
                stack.push(value);
                if let Some(b) = body {
                    stack.push(b);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => stack.push(expr),
            TypedExprKind::TypeApp { expr, .. } => stack.push(expr),
            TypedExprKind::Recur(args) => stack.extend(args.iter()),
            _ => {}
        }
    }
    None
}

fn let_binding_type(src: &str, fn_name: &str, let_name: &str) -> String {
    let module = typecheck(src);
    let func = module
        .functions
        .iter()
        .find(|f| f.name == fn_name)
        .unwrap_or_else(|| panic!("fn {fn_name} not found"));
    find_let_type(&func.body, let_name)
        .unwrap_or_else(|| panic!("let binding `{let_name}` not found in fn `{fn_name}`"))
}

fn fn_scheme(src: &str, fn_name: &str) -> String {
    let module = typecheck(src);
    let entry = module
        .fn_types
        .iter()
        .find(|e| e.name == fn_name)
        .unwrap_or_else(|| panic!("fn {fn_name} not found"));
    format!("{}", entry.scheme)
}

const EXTERN_SOCKET: &str = r#"
extern java "net.Socket" as pub Socket lifts always {}
extern js "net.mjs"     as pub Socket lifts always {}
"#;

#[test]
fn record_ctor_no_annotation_auto_wraps_to_own() {
    let src = format!(
        r#"{EXTERN_SOCKET}
type Conn = {{ sock: ~Socket, name: String }}
fun mk(s: ~Socket) -> ~Conn = {{
  let c = Conn {{ sock = s, name = "foo" }}
  c
}}
"#
    );
    insta::assert_snapshot!(let_binding_type(&src, "mk", "c"), @"~Conn");
}

#[test]
fn plain_record_no_wrap() {
    let src = r#"
type Point = { x: Int, y: Int }
fun mk() -> Point = {
  let p = Point { x = 1, y = 2 }
  p
}
"#;
    insta::assert_snapshot!(let_binding_type(src, "mk", "p"), @"Point");
}

#[test]
fn explicit_own_annotation_still_wraps() {
    let src = format!(
        r#"{EXTERN_SOCKET}
type Conn = {{ sock: ~Socket, name: String }}
fun mk(s: ~Socket) -> ~Conn = {{
  let c: ~Conn = Conn {{ sock = s, name = "foo" }}
  c
}}
"#
    );
    insta::assert_snapshot!(let_binding_type(&src, "mk", "c"), @"~Conn");
}

#[test]
fn identity_passthrough_binds_generic_to_own() {
    let src = format!(
        r#"{EXTERN_SOCKET}
type Conn = {{ sock: ~Socket, name: String }}
fun identity[a](x: a) -> a = x
fun mk(s: ~Socket) -> ~Conn = identity(Conn {{ sock = s, name = "foo" }})
"#
    );
    // The function typechecks iff the inner ctor auto-wrapped to ~Conn,
    // letting the generic `a` bind to ~Conn and match the return annotation.
    insta::assert_snapshot!(fn_scheme(&src, "mk"), @"(~Socket) -> ~Conn");
}

#[test]
fn sum_constructor_with_own_field_auto_wraps() {
    let src = format!(
        r#"{EXTERN_SOCKET}
type ConnState = Open(~Socket) | Closed
fun mk(s: ~Socket) -> ~ConnState = {{
  let st = Open(s)
  st
}}
"#
    );
    insta::assert_snapshot!(let_binding_type(&src, "mk", "st"), @"~ConnState");
}

#[test]
fn nullary_variant_of_affine_sum_auto_wraps() {
    let src = format!(
        r#"{EXTERN_SOCKET}
type ConnState = Open(~Socket) | Closed
fun mk() -> ~ConnState = Closed
"#
    );
    // Whole-fn scheme: if Closed auto-wraps to ~ConnState, the return-type
    // unify succeeds and the scheme matches the annotation.
    insta::assert_snapshot!(fn_scheme(&src, "mk"), @"() -> ~ConnState");
}
