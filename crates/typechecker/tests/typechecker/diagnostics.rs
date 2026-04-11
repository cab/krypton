use krypton_diagnostics::{DiagnosticRenderer, PlainTextRenderer};
use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_typechecker::diagnostics::{lower_infer_error, lower_infer_errors};
use krypton_typechecker::infer::{self, InferError};

fn parse_and_infer_module_error(src: &str) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let errors = match infer::infer_module_single(&module, &CompositeResolver::stdlib_only()) {
        Ok(_) => panic!("expected a type error"),
        Err(errors) => errors,
    };
    let (diags, srcs) = lower_infer_errors("test.kr", src, &errors);
    diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect()
}

fn render_error(src: &str) -> String {
    let wrapped = format!("fun _test() = {src}");
    parse_and_infer_module_error(&wrapped)
}

#[test]
fn type_mismatch_diagnostic() {
    insta::assert_snapshot!(render_error("if true { 1 } else { \"hi\" }"));
}

#[test]
fn not_a_function_diagnostic() {
    insta::assert_snapshot!(render_error("42(1)"));
}

#[test]
fn wrong_arity_diagnostic() {
    insta::assert_snapshot!(render_error("{ let f = x -> x; f(1, 2) }"));
}

#[test]
fn infinite_type_diagnostic() {
    insta::assert_snapshot!(render_error("x -> x(x)"));
}

#[test]
fn own_wrapper_infinite_type_diagnostic() {
    insta::assert_snapshot!(parse_and_infer_module_error(
        "fun fabricate[a](x: a, y: a) -> ~a where a: Semigroup = x + y"
    ));
}

#[test]
fn own_wrapper_block_body_diagnostic() {
    insta::assert_snapshot!(parse_and_infer_module_error(
        "fun fabricate[a](x: a, y: a) -> ~a where a: Semigroup = {\n    let z = x + y;\n    z\n}"
    ));
}

#[test]
fn unknown_var_diagnostic() {
    insta::assert_snapshot!(render_error("x + 1"));
}

fn render_fixture_error(fixture: &str) -> String {
    let src = std::fs::read_to_string(fixture).unwrap();
    let (module, errors) = parse(&src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let errors = match infer::infer_module_single(&module, &CompositeResolver::stdlib_only()) {
        Ok(_) => panic!("expected a type error"),
        Err(errors) => errors,
    };
    let (diags, srcs) = lower_infer_errors(fixture, &src, &errors);
    diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect()
}

fn render_module_error_with_resolver(
    src: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let errors = match infer::infer_module(
        &module,
        resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    ) {
        Ok(_) => panic!("expected a type error"),
        Err(errors) => errors,
    };
    let (diags, srcs) = lower_infer_errors("test.kr", src, &errors);
    diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect()
}

fn render_module_error(src: &str) -> String {
    render_module_error_with_resolver(src, &CompositeResolver::stdlib_only())
}

#[test]
fn own_fn_vs_fn_help_text() {
    let src = "fun call_many(f: () -> String) -> String = f()\nfun bad(x: ~String) -> String = call_many(() -> x)";
    let output = render_module_error(src);
    assert!(
        output.contains("single-use closure"),
        "expected own fn help text in:\n{output}"
    );
}

#[test]
fn own_t_vs_t_help_text() {
    let src = "fun bad(x: String) -> ~String = x";
    let output = render_module_error(src);
    assert!(
        output.contains("ownership"),
        "expected ownership help text in:\n{output}"
    );
}

#[test]
fn no_own_mismatch_no_help() {
    let output = render_error("if true { 1 } else { \"hi\" }");
    assert!(
        !output.contains("single-use closure") && !output.contains("ownership"),
        "expected no ownership help text in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_e0101() {
    let src = "fun consume(buf: ~String) -> String = match buf { _ => \"\" }\nfun bad(x: ~String) -> String = { let f = () -> consume(x); f(); f() }";
    let output = render_module_error(src);
    assert!(
        output.contains("captures `~` value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_e0104() {
    let src = "fun call_many(f: () -> String) -> String = f()\nfun bad(x: ~String) -> String = call_many(() -> x)";
    let output = render_module_error(src);
    assert!(
        output.contains("captures `~` value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_correct_name() {
    let src = "fun consume(buf: ~String) -> String = match buf { _ => \"\" }\nfun bad(a: String, b: ~String) -> String = { let f = () -> consume(b); f(); f() }";
    let output = render_module_error(src);
    assert!(
        output.contains("captures `~` value `b`"),
        "expected own capture note mentioning `b` in:\n{output}"
    );
}


#[test]
fn own_fn_capture_note_return_site() {
    let output =
        render_fixture_error("../../tests/fixtures/closures/explain_own_fn_return_site.kr");
    assert!(
        output.contains("captures `~` value `r`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_let_site() {
    let output = render_fixture_error("../../tests/fixtures/closures/explain_own_fn_let_site.kr");
    assert!(
        output.contains("captures `~` value `r`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn test_qualifier_mismatch_diagnostic() {
    let output = render_fixture_error("../../tests/fixtures/ownership/qualifier_dup_error.kr");
    insta::assert_snapshot!(output);
    // No type-theory jargon in error/help lines (exclude file path lines)
    let message_lines: String = output
        .lines()
        .filter(|l| !l.contains("qualifier_dup_error.kr"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !message_lines.contains("affine"),
        "should not contain 'affine': {message_lines}"
    );
    assert!(
        !message_lines.contains("qualifier"),
        "should not contain 'qualifier': {message_lines}"
    );
    assert!(
        !message_lines.contains("unlimited"),
        "should not contain 'unlimited': {message_lines}"
    );
}

#[test]
fn test_e0101_shows_first_use() {
    let output = render_fixture_error("../../tests/fixtures/ownership/own_double_use.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("first use here"),
        "expected 'first use here' secondary label in:\n{output}"
    );
}

#[test]
fn test_e0102_shows_consuming_branch() {
    let output = render_fixture_error("../../tests/fixtures/ownership/branch_if_one.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("consumed here"),
        "expected 'consumed here' secondary label in:\n{output}"
    );
}

#[test]
fn test_e0103_shows_prior_use() {
    let output = render_fixture_error("../../tests/fixtures/closures/own_capture_moved.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("consumed here"),
        "expected 'consumed here' secondary label in:\n{output}"
    );
}

#[test]
fn error_codes_present() {
    // Verify each error code appears in at least one diagnostic
    let cases = [
        ("E0001", "if true { 1 } else { \"hi\" }"),
        ("E0003", "x + 1"),
        ("E0004", "42(1)"),
        ("E0005", "{ let f = x -> x; f(1, 2) }"),
        ("E0007", "x -> x(x)"),
    ];
    for (code, src) in cases {
        let output = render_error(src);
        assert!(
            output.contains(code),
            "expected error code {} in output:\n{}",
            code,
            output
        );
    }
}

#[test]
fn undeclared_typevar_suggestion() {
    let output = render_fixture_error("../../tests/fixtures/inference/undeclared_typevar.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("did you mean `String`?"),
        "expected 'did you mean `String`?' in:\n{output}"
    );
}

#[test]
fn circular_import_error() {
    use krypton_modules::module_resolver::ModuleResolver;

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
    let output = render_module_error_with_resolver(src, &CircularResolver);
    assert!(output.contains("E0502"), "expected E0502 in:\n{output}");
    assert!(
        output.contains("circular import"),
        "expected 'circular import' in:\n{output}"
    );
}

#[test]
fn module_qualifier_value_diagnostic() {
    use krypton_modules::module_resolver::ModuleResolver;

    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "helpers_a" => Some("pub fun compute(x: Int) -> Int = x + 10".to_string()),
                _ => None,
            }
        }
    }

    let src = "import helpers_a\nfun main() -> Int = { let m = helpers_a; 0 }";
    let output = render_module_error_with_resolver(src, &Resolver);
    assert!(output.contains("E0504"), "expected E0504 in:\n{output}");
    assert!(
        output.contains("compile-time only"),
        "expected compile-time wording in:\n{output}"
    );
    assert!(
        output.contains("not a runtime value"),
        "expected runtime value wording in:\n{output}"
    );
    assert!(
        output.contains("helpers_a."),
        "expected qualified export example in:\n{output}"
    );
}

#[test]
fn module_qualifier_value_diagnostic_noncallable_example_has_no_call_syntax() {
    use krypton_modules::module_resolver::ModuleResolver;

    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "choices" => Some("pub type Option[a] = Some(a) | None".to_string()),
                _ => None,
            }
        }
    }

    let src = "import choices\nfun main() -> Int = { let m = choices; 0 }";
    let output = render_module_error_with_resolver(src, &Resolver);
    assert!(
        !output.contains("choices.None(...)"),
        "non-callable constructor should not be shown as callable:\n{output}"
    );
}

#[test]
fn module_qualifier_value_diagnostic_hides_internal_export_names() {
    let src = "import core/option\nfun main() -> Int = { let m = option; 0 }";
    let output = render_module_error(src);
    assert!(
        !output.contains('$'),
        "internal lowered names should not appear in help text:\n{output}"
    );
}

#[test]
fn qualified_export_table_has_no_mangled_names() {
    use krypton_modules::module_resolver::ModuleResolver;

    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "tlib" => Some("pub type Color = Red | Green | Blue deriving (Show)".to_string()),
                _ => None,
            }
        }
    }

    // Use the module as a value to trigger a diagnostic that lists exports
    let src = "import tlib\nfun main() -> Int = { let m = tlib; 0 }";
    let output = render_module_error_with_resolver(src, &Resolver);
    assert!(
        !output.contains('$'),
        "mangled instance method names should not appear in export table:\n{output}"
    );
}

#[test]
fn reserved_name_error() {
    let src = "fun __krypton_intrinsic() = 42\nfun main() = __krypton_intrinsic()";
    let output = parse_and_infer_module_error(src);
    assert!(output.contains("E0012"), "expected E0012 in:\n{output}");
    assert!(
        output.contains("reserved compiler name"),
        "expected 'reserved compiler name' in:\n{output}"
    );
}

#[test]
fn import_ctor_no_parent_type_in_annotation() {
    use krypton_modules::module_resolver::ModuleResolver;

    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "shapes" => Some("pub type Shape = Circle(Float) | Square(Float)".to_string()),
                _ => None,
            }
        }
    }

    // Import only constructors — Shape should NOT be available in annotations
    let src =
        "import shapes.{Circle, Square}\nfun area(s: Shape) -> Float = 0.0\nfun main() -> Int = 0";
    let output = render_module_error_with_resolver(src, &Resolver);
    assert!(
        output.contains("E0011"),
        "expected E0011 (unknown type) for Shape when only constructors imported:\n{output}"
    );
}

#[test]
fn import_ctor_expr_ok() {
    use krypton_modules::module_resolver::ModuleResolver;
    use krypton_parser::parser::parse;

    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "shapes" => Some("pub type Shape = Circle(Float) | Square(Float)".to_string()),
                _ => None,
            }
        }
    }

    // Import only constructors — using them in expressions (no annotation) should work
    let src = "import shapes.{Circle}\nfun wrap(x) = Circle(x)\nfun main() -> Int = 0";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(
        &module,
        &Resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    );
    assert!(
        result.is_ok(),
        "importing constructors and using them in expressions should succeed: {:?}",
        result.err()
    );
}

#[test]
fn import_type_explicitly_allows_annotation() {
    use krypton_modules::module_resolver::ModuleResolver;
    use krypton_parser::parser::parse;

    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "shapes" => Some("pub type Shape = Circle(Float) | Square(Float)".to_string()),
                _ => None,
            }
        }
    }

    // Import the type explicitly — Shape should be available in annotations
    let src =
        "import shapes.{Shape, Circle}\nfun area(s: Shape) -> Float = 0.0\nfun main() -> Int = 0";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(
        &module,
        &Resolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    );
    assert!(
        result.is_ok(),
        "explicitly importing a type should allow it in annotations: {:?}",
        result.err()
    );
}

#[test]
fn parse_error_in_imported_module() {
    use krypton_modules::module_resolver::ModuleResolver;

    struct BadParseResolver;
    impl ModuleResolver for BadParseResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "bad" => Some("fun f( = 42".to_string()), // syntax error
                _ => None,
            }
        }
    }

    let src = "import bad.{f}\nfun main() -> Int = f()";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let errors = match infer::infer_module(
        &module,
        &BadParseResolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    ) {
        Ok(_) => panic!("expected a parse error from bad module"),
        Err(errors) => errors,
    };
    // Should be a ModuleParseError variant pointing at "bad"
    assert_eq!(errors.len(), 1, "expected exactly one error");
    match &errors[0] {
        InferError::ModuleParseError { path, .. } => {
            assert_eq!(path, "bad", "expected path 'bad', got '{path}'");
        }
        other => panic!("expected ModuleParseError, got: {other:?}"),
    }
    // Render and verify it references the module file with correct source
    let (diags, srcs) = lower_infer_error("test.kr", src, &errors[0]);
    let output: String = diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect();
    insta::assert_snapshot!(output);
    assert!(
        output.contains("bad"),
        "rendered diagnostic should reference 'bad':\n{output}"
    );
}

#[test]
fn type_error_in_imported_module() {
    use krypton_modules::module_resolver::ModuleResolver;

    struct BadTypeResolver;
    impl ModuleResolver for BadTypeResolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "badmod" => Some("pub fun f() -> Int = \"nope\"".to_string()),
                _ => None,
            }
        }
    }

    let src = "import badmod.{f}\nfun main() -> Int = f()";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let errors = match infer::infer_module(
        &module,
        &BadTypeResolver,
        "test".to_string(),
        krypton_parser::ast::CompileTarget::Jvm,
    ) {
        Ok(_) => panic!("expected a type error from badmod"),
        Err(errors) => errors,
    };
    // Should be a TypeError with error_source pointing at badmod
    assert_eq!(errors.len(), 1, "expected exactly one error");
    match &errors[0] {
        InferError::TypeError {
            error,
            error_source,
        } => {
            assert_eq!(
                error.source_file.as_deref(),
                Some("badmod"),
                "expected source_file 'badmod', got: {:?}",
                error.source_file
            );
            assert!(
                error_source.is_some(),
                "error_source should contain badmod's source"
            );
        }
        other => panic!("expected TypeError, got: {other:?}"),
    }
    // Render and verify it references the module file
    let (diags, srcs) = lower_infer_error("test.kr", src, &errors[0]);
    let output: String = diags
        .iter()
        .map(|d| PlainTextRenderer.render(d, &srcs))
        .collect();
    insta::assert_snapshot!(output);
    assert!(
        output.contains("badmod"),
        "rendered diagnostic should reference 'badmod':\n{output}"
    );
}

#[test]
fn nullary_constructor_call_diagnostic() {
    let output = render_fixture_error("../../tests/fixtures/ownership/nullary_ctor_call.kr");
    insta::assert_snapshot!(output);
    assert!(output.contains("E0004"), "expected E0004 in:\n{output}");
    assert!(
        output.contains("remove `()`"),
        "expected help text about removing () in:\n{output}"
    );
}

#[test]
fn nullary_constructor_call_qualified_diagnostic() {
    use krypton_modules::module_resolver::ModuleResolver;

    struct Resolver;
    impl ModuleResolver for Resolver {
        fn resolve(&self, module_path: &str) -> Option<String> {
            match module_path {
                "core/option" => Some("pub type Option[a] = Some(a) | None".to_string()),
                _ => None,
            }
        }
    }

    let src = "import core/option\nfun main() -> Int = option.None()";
    let output = render_module_error_with_resolver(src, &Resolver);
    assert!(
        output.contains("E0004"),
        "expected E0004 for qualified nullary ctor call in:\n{output}"
    );
    assert!(
        output.contains("remove `()`"),
        "expected help text about removing () in:\n{output}"
    );
}

#[test]
fn unsolved_type_var_diagnostic() {
    let output = render_fixture_error("../../tests/fixtures/ownership/unsolved_type_display.kr");
    insta::assert_snapshot!(output);
    // Should not contain raw inference variable names like z3, a4, etc.
    // Type vars in errors should be sequential: a, b, c, ...
    // The error should show clean type names
    let has_raw_var = output.lines().any(|line| {
        // Skip file path lines
        if line.contains(".kr") {
            return false;
        }
        // Look for patterns like single letter followed by digit (raw var names)
        let mut chars = line.chars().peekable();
        while let Some(c) = chars.next() {
            if c.is_ascii_lowercase() {
                if let Some(&next) = chars.peek() {
                    if next.is_ascii_digit() {
                        // Check it's not part of a larger word
                        return true;
                    }
                }
            }
        }
        false
    });
    assert!(
        !has_raw_var,
        "should not contain raw inference variable names in:\n{output}"
    );
}

#[test]
fn impl_fn_type_missing_method_diagnostic() {
    let src = "trait Apply[f] { fun apply(f: f, x: Int) -> Int }\nimpl Apply[() -> Int] { }";
    let output = parse_and_infer_module_error(src);
    insta::assert_snapshot!(output);
    // Should show `() -> Int` not `Fun0` in the error
    assert!(
        output.contains("() -> Int"),
        "expected `() -> Int` in error, got:\n{output}"
    );
    assert!(
        !output.contains("Fun0"),
        "should not contain JVM name `Fun0` in:\n{output}"
    );
}

#[test]
fn e0301_span_points_to_call_not_block() {
    let output = render_fixture_error("../../tests/fixtures/traits/no_show_in_block.kr");
    insta::assert_snapshot!(output);
    assert!(output.contains("E0301"), "expected E0301 in:\n{output}");
    // The span should point to the println call, not the enclosing block
    assert!(
        output.contains("println(Opaque)"),
        "expected span to underline `println(Opaque)`, not the enclosing block, in:\n{output}"
    );
}

#[test]
fn impl_method_mode_mismatch_diagnostic() {
    let src = "type File = { fd: Int }\n\
               trait Reader[a] { fun read(&this: ~a) -> Int }\n\
               impl Reader[File] { fun read(this: ~File) -> Int = 0 }";
    let output = parse_and_infer_module_error(src);
    insta::assert_snapshot!(output);
    assert!(
        output.contains("E0612"),
        "expected E0612 in error, got:\n{output}"
    );
    assert!(
        output.contains("parameter `this`"),
        "expected parameter name in error, got:\n{output}"
    );
    assert!(
        output.contains("borrow (`&~T`)") && output.contains("consume (`~T`)"),
        "expected both mode labels in error, got:\n{output}"
    );
}

#[test]
fn impl_return_type_mismatch_diagnostic() {
    let src = "trait Convert[a] { fun convert(x: a) -> String }\nimpl Convert[Int] { fun convert(x: Int) -> Int = x }";
    let output = parse_and_infer_module_error(src);
    insta::assert_snapshot!(output);
    // Should show type mismatch, not wrong arity
    assert!(
        output.contains("type mismatch"),
        "expected 'type mismatch' in error, got:\n{output}"
    );
    assert!(
        !output.contains("wrong arity"),
        "should not contain 'wrong arity' in:\n{output}"
    );
}

#[test]
fn e0108_scope_exit() {
    let output = render_fixture_error("../../tests/fixtures/linear/linear_scope_exit_leak.kr");
    insta::assert_snapshot!(output);
    assert!(output.contains("E0108"), "expected E0108 in:\n{output}");
}

#[test]
fn e0108_branch_missing() {
    let output = render_fixture_error("../../tests/fixtures/linear/linear_branch_asymmetric.kr");
    insta::assert_snapshot!(output);
    assert!(output.contains("E0108"), "expected E0108 in:\n{output}");
}

#[test]
fn e0108_recur_back() {
    let output = render_fixture_error("../../tests/fixtures/linear/linear_recur_leak.kr");
    insta::assert_snapshot!(output);
    assert!(output.contains("E0108"), "expected E0108 in:\n{output}");
}

#[test]
fn e0108_early_return_via_question() {
    let output =
        render_fixture_error("../../tests/fixtures/linear/linear_early_return_question_mark.kr");
    insta::assert_snapshot!(output);
    assert!(output.contains("E0108"), "expected E0108 in:\n{output}");
}

const E0109_EXTERN_RR: &str = r#"
extern java "net.Socket" as pub RR lifts always {}
extern js   "net.mjs"    as pub RR lifts always {}
"#;

#[test]
fn e0109_return_type_wording() {
    let src = format!("{E0109_EXTERN_RR}\nfun make(s: ~RR) -> RR = s\n");
    let output = render_module_error(&src);
    assert!(output.contains("E0109"), "expected E0109 in:\n{output}");
    assert!(
        output.contains("return type `RR` owns a resource and must be written `~RR`"),
        "expected return-type wording in:\n{output}"
    );
    assert!(
        output.contains("transfer ownership to the caller"),
        "expected return-specific help in:\n{output}"
    );
    assert!(
        !output.contains("borrow"),
        "return context must not suggest borrowing in:\n{output}"
    );
    assert!(
        !output.contains("Suggested:"),
        "help must not carry a trailing `Suggested:` in:\n{output}"
    );
    assert!(
        !output.contains("value-position"),
        "message must not leak `value-position` jargon in:\n{output}"
    );
}

#[test]
fn e0109_param_consume_wording_offers_borrow() {
    let src = format!("{E0109_EXTERN_RR}\nfun take(s: RR) -> Unit = ()\n");
    let output = render_module_error(&src);
    assert!(output.contains("E0109"), "expected E0109 in:\n{output}");
    assert!(
        output.contains("parameter type `RR` owns a resource and must be written `~RR`"),
        "expected parameter-type wording in:\n{output}"
    );
    assert!(
        output.contains("take ownership") && output.contains("borrow with `&`"),
        "expected param-specific help (ownership + borrow alternative) in:\n{output}"
    );
}

#[test]
fn e0109_record_field_wording() {
    let src = format!("{E0109_EXTERN_RR}\ntype Conn = {{ sock: RR }}\n");
    let output = render_module_error(&src);
    assert!(output.contains("E0109"), "expected E0109 in:\n{output}");
    assert!(
        output.contains("field type `RR` owns a resource and must be written `~RR`"),
        "expected field-type wording in:\n{output}"
    );
    assert!(
        output.contains("so the record owns the resource"),
        "expected record-specific help in:\n{output}"
    );
    assert!(
        !output.contains("borrow"),
        "field context must not suggest borrowing in:\n{output}"
    );
}

#[test]
fn e0109_variant_payload_wording() {
    let src = format!("{E0109_EXTERN_RR}\ntype Maybe = Some(RR) | None\n");
    let output = render_module_error(&src);
    assert!(output.contains("E0109"), "expected E0109 in:\n{output}");
    assert!(
        output.contains("variant payload type `RR` owns a resource and must be written `~RR`"),
        "expected variant-payload wording in:\n{output}"
    );
    assert!(
        output.contains("so the variant owns the resource"),
        "expected variant-specific help in:\n{output}"
    );
}

#[test]
fn e0109_let_binding_wording() {
    let src = format!(
        "{E0109_EXTERN_RR}\nfun mk() -> ~RR = RR {{}}\nfun go() -> Unit = {{\n  let s: RR = mk()\n  ()\n}}\n"
    );
    let output = render_module_error(&src);
    assert!(output.contains("E0109"), "expected E0109 in:\n{output}");
    assert!(
        output.contains("let-binding type `RR` owns a resource and must be written `~RR`"),
        "expected let-binding wording in:\n{output}"
    );
    assert!(
        output.contains("let-bindings consume the value"),
        "expected let-specific help in:\n{output}"
    );
}
