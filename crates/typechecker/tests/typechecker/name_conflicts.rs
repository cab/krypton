//! Tests for the two-namespace collision model:
//!   - Type namespace: types, type aliases, traits
//!   - Value namespace: functions, constructors, trait methods
//!
//! See implementation plan: "Fix silent name conflicts via a two-namespace model".

use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_typechecker::infer;

/// Typecheck `src` and expect it to fail with a specific error code.
fn expect_error_code(src: &str, expected_code: &str) {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    );
    let err = match result {
        Ok(_) => panic!("expected {expected_code}, but typechecking succeeded"),
        Err(mut errors) => errors.remove(0),
    };
    let actual = err
        .type_error()
        .unwrap_or_else(|| panic!("expected TypeError, got {:?}", err))
        .error
        .error_code()
        .to_string();
    assert_eq!(
        actual,
        expected_code,
        "expected error code {expected_code}, got {actual} (error: {})",
        err.type_error().unwrap().error
    );
}

/// Typecheck `src` and expect it to succeed.
fn expect_ok(src: &str) {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(
        &module,
        &CompositeResolver::stdlib_only(),
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    );
    if let Err(errors) = result {
        panic!(
            "expected success, got errors: {:?}",
            errors
                .iter()
                .map(|e| e.type_error().map(|te| te.error.to_string()))
                .collect::<Vec<_>>()
        );
    }
}

// ----------------------------------------------------------------------------
// Type namespace — negative cases
// ----------------------------------------------------------------------------

#[test]
fn e0002_two_type_decls_same_name() {
    // Baseline: existing coverage.
    expect_error_code(
        r#"
            type Foo = A
            type Foo = B
        "#,
        "E0002",
    );
}

#[test]
fn e0016_type_then_trait_same_name() {
    // The original repro: `type R = A` + `trait R[f[_]] { ... }`.
    expect_error_code(
        r#"
            type Foo = A
            trait Foo[a] { fun ignore(x: a) -> Unit }
        "#,
        "E0016",
    );
}

#[test]
fn e0318_two_trait_decls_same_name() {
    // Previously emitted as E0002 (wrong variant); now E0318.
    expect_error_code(
        r#"
            trait Foo[a] { fun ignore(x: a) -> Unit }
            trait Foo[a] { fun ignore2(x: a) -> Unit }
        "#,
        "E0318",
    );
}

// ----------------------------------------------------------------------------
// Value namespace — negative cases
// ----------------------------------------------------------------------------

#[test]
fn e0015_duplicate_constructor_across_types() {
    // The original repro: `type RR = A` + `type R = A`.
    expect_error_code(
        r#"
            type RR = A
            type R = A
        "#,
        "E0015",
    );
}

#[test]
fn e0015_duplicate_constructor_with_payloads() {
    expect_error_code(
        r#"
            type RR = A(Int)
            type R = A(String)
        "#,
        "E0015",
    );
}

#[test]
fn e0015_three_types_same_constructor_bails_on_first() {
    // Default behavior: bail on the first collision (matches other collision errors).
    expect_error_code(
        r#"
            type AA = X
            type BB = X
            type CC = X
        "#,
        "E0015",
    );
}

// ----------------------------------------------------------------------------
// Cross-namespace — must NOT error
// ----------------------------------------------------------------------------

#[test]
fn ok_type_show_and_fn_show() {
    // Different namespaces: type `Show` and fn `show` coexist.
    // (NB: `Show` here shadows the prelude trait, which is allowed.)
    expect_ok(
        r#"
            type Show = X
            fun show() -> Int = 0
            fun main() -> Int = show()
        "#,
    );
}

#[test]
fn ok_type_r_and_fn_r() {
    expect_ok(
        r#"
            type R = A
            fun r() -> Int = 0
            fun main() -> Int = r()
        "#,
    );
}

// ----------------------------------------------------------------------------
// Prelude shadowing — must NOT error (regression guards)
// ----------------------------------------------------------------------------

#[test]
fn ok_shadow_prelude_option_type() {
    expect_ok(
        r#"
            type Option = MyOpt(Int)
            fun main() -> Option = MyOpt(42)
        "#,
    );
}

#[test]
fn ok_shadow_prelude_println_extern() {
    expect_ok(
        r#"
            extern java "java/io/PrintStream" {
                fun println[a](x: a) -> Unit
            }
            fun main() -> Unit = println(42)
        "#,
    );
}

#[test]
fn ok_shadow_prelude_list_with_same_constructors() {
    // User's local `List` type replaces the prelude's cleanly, including
    // its `Nil`/`Cons` constructors. Must not raise a spurious E0015.
    expect_ok(
        r#"
            type List[a] = Nil | Cons(a, List[a])
            fun main() -> List[Int] = Cons(1, Nil)
        "#,
    );
}

#[test]
// ----------------------------------------------------------------------------
// Local overload sets
// ----------------------------------------------------------------------------

#[test]
fn ok_local_overload_non_overlapping() {
    expect_ok(
        r#"
            fun length(v: Vec[Int]) -> Int = 0
            fun length(l: List[Int]) -> Int = 0
            fun main() -> Int = 0
        "#,
    );
}

#[test]
fn e0514_local_overload_overlapping() {
    expect_error_code(
        r#"
            fun id[a](x: a) -> a = x
            fun id[b](y: b) -> b = y
            fun main() -> Int = 0
        "#,
        "E0514",
    );
}

#[test]
fn e0516_local_overload_arity_mismatch() {
    expect_error_code(
        r#"
            fun foo(x: Int) -> Int = x
            fun foo(x: Int, y: Int) -> Int = x
            fun main() -> Int = 0
        "#,
        "E0516",
    );
}

#[test]
fn e0514_local_overload_unannotated() {
    expect_error_code(
        r#"
            fun foo(x) = x
            fun foo(y) = y
            fun main() -> Int = 0
        "#,
        "E0514",
    );
}

#[test]
fn ok_user_type_named_after_prelude_constructor_name() {
    // A brand-new user type whose only constructor happens to reuse the name
    // of a prelude constructor (`Some`) must not collide — prelude
    // constructors are shadowable.
    expect_ok(
        r#"
            type Box = Some(Int)
            fun main() -> Box = Some(7)
        "#,
    );
}
