use krypton_modules::module_resolver::CompositeResolver;
use krypton_parser::parser::parse;
use krypton_typechecker::diagnostics::{render_infer_error, render_type_errors};
use krypton_typechecker::infer::{self, InferError};

fn parse_and_infer_module_error(src: &str) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let err = match infer::infer_module_single(&module, &CompositeResolver::stdlib_only()) {
        Ok(_) => panic!("expected a type error"),
        Err(e) => e,
    };
    let rendered = render_infer_error("test.kr", src, &err);
    strip_ansi_escapes(rendered)
}

fn render_error(src: &str) -> String {
    let wrapped = format!("fun _test() = {src}");
    parse_and_infer_module_error(&wrapped)
}

fn strip_ansi_escapes(s: String) -> String {
    let mut result = String::new();
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\x1b' {
            // Skip until we hit a letter (end of ANSI sequence)
            while let Some(&next) = chars.peek() {
                chars.next();
                if next.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            result.push(c);
        }
    }
    result
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
fn unknown_var_diagnostic() {
    insta::assert_snapshot!(render_error("x + 1"));
}

fn render_fixture_error(fixture: &str) -> String {
    let src = std::fs::read_to_string(fixture).unwrap();
    let (module, errors) = parse(&src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let err = match infer::infer_module_single(&module, &CompositeResolver::stdlib_only()) {
        Ok(_) => panic!("expected a type error"),
        Err(e) => e,
    };
    let rendered = render_infer_error(fixture, &src, &err);
    strip_ansi_escapes(rendered)
}

fn render_module_error_with_resolver(
    src: &str,
    resolver: &dyn krypton_modules::module_resolver::ModuleResolver,
) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let err = match infer::infer_module(&module, resolver) {
        Ok(_) => panic!("expected a type error"),
        Err(e) => e,
    };
    let rendered = render_infer_error("test.kr", src, &err);
    strip_ansi_escapes(rendered)
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
    let src = "fun consume(buf: ~String) -> String = buf\nfun bad(x: ~String) -> String = { let f = () -> consume(x); f(); f() }";
    let output = render_module_error(src);
    assert!(
        output.contains("captures `~` value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_e0001() {
    let src = "fun call_many(f: () -> String) -> String = f()\nfun bad(x: ~String) -> String = call_many(() -> x)";
    let output = render_module_error(src);
    assert!(
        output.contains("captures `~` value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_correct_name() {
    let src = "fun consume(buf: ~String) -> String = buf\nfun bad(a: String, b: ~String) -> String = { let f = () -> consume(b); f(); f() }";
    let output = render_module_error(src);
    assert!(
        output.contains("captures `~` value `b`"),
        "expected own capture note mentioning `b` in:\n{output}"
    );
}

#[test]
fn test_qualifier_mismatch_diagnostic() {
    let output = render_fixture_error("../../tests/fixtures/m6/qualifier_dup_error.kr");
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
    let output = render_fixture_error("../../tests/fixtures/m6/own_double_use.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("first use here"),
        "expected 'first use here' secondary label in:\n{output}"
    );
}

#[test]
fn test_e0102_shows_consuming_branch() {
    let output = render_fixture_error("../../tests/fixtures/m6/branch_if_one.kr");
    insta::assert_snapshot!(output);
    assert!(
        output.contains("consumed here"),
        "expected 'consumed here' secondary label in:\n{output}"
    );
}

#[test]
fn test_e0103_shows_prior_use() {
    let output = render_fixture_error("../../tests/fixtures/m6/own_capture_moved.kr");
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
    let output = render_fixture_error("../../tests/fixtures/m11/undeclared_typevar.kr");
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
                "tlib" => Some(
                    "pub type Color = Red | Green | Blue deriving (Show)".to_string(),
                ),
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
    let src = "import shapes.{Circle, Square}\nfun area(s: Shape) -> Float = 0.0\nfun main() -> Int = 0";
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
    let result = infer::infer_module(&module, &Resolver);
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
    let src = "import shapes.{Shape, Circle}\nfun area(s: Shape) -> Float = 0.0\nfun main() -> Int = 0";
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let result = infer::infer_module(&module, &Resolver);
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
    let err = match infer::infer_module(&module, &BadParseResolver) {
        Ok(_) => panic!("expected a parse error from bad module"),
        Err(e) => e,
    };
    // Should be a ModuleParseError variant pointing at "bad"
    match &err {
        InferError::ModuleParseError { path, .. } => {
            assert_eq!(path, "bad", "expected path 'bad', got '{path}'");
        }
        other => panic!("expected ModuleParseError, got: {other:?}"),
    }
    // Render and verify it references the module file with correct source
    let output = strip_ansi_escapes(render_infer_error("test.kr", src, &err));
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
    let err = match infer::infer_module(&module, &BadTypeResolver) {
        Ok(_) => panic!("expected a type error from badmod"),
        Err(e) => e,
    };
    // Should be a TypeError with error_source pointing at badmod
    match &err {
        InferError::TypeError { error, error_source } => {
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
    let output = strip_ansi_escapes(render_infer_error("test.kr", src, &err));
    insta::assert_snapshot!(output);
    assert!(
        output.contains("badmod"),
        "rendered diagnostic should reference 'badmod':\n{output}"
    );
}
