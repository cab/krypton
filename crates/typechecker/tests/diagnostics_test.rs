use krypton_parser::parser::parse;
use krypton_typechecker::diagnostics::render_type_errors;
use krypton_typechecker::infer;
use krypton_typechecker::module_resolver::CompositeResolver;

fn parse_and_infer_module_error(src: &str) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {:?}", errors);
    let err = match infer::infer_module_single(&module, &CompositeResolver::stdlib_only()) {
        Ok(_) => panic!("expected a type error"),
        Err(e) => e,
    };
    let rendered = render_type_errors("test.kr", src, &[err]);
    strip_ansi_escapes(rendered)
}

fn render_error(src: &str) -> String {
    let wrapped = format!("fun _() = {src}");
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
    insta::assert_snapshot!(render_error("{ let f = x => x; f(1, 2) }"));
}

#[test]
fn infinite_type_diagnostic() {
    insta::assert_snapshot!(render_error("x => x(x)"));
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
    let rendered = render_type_errors(fixture, &src, &[err]);
    strip_ansi_escapes(rendered)
}

fn render_module_error_with_resolver(src: &str, resolver: &dyn krypton_typechecker::module_resolver::ModuleResolver) -> String {
    let (module, errors) = parse(src);
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let err = match infer::infer_module(&module, resolver) {
        Ok(_) => panic!("expected a type error"),
        Err(e) => e,
    };
    let rendered = render_type_errors("test.kr", src, &[err]);
    strip_ansi_escapes(rendered)
}

fn render_module_error(src: &str) -> String {
    render_module_error_with_resolver(src, &CompositeResolver::stdlib_only())
}

#[test]
fn own_fn_vs_fn_help_text() {
    let src = "fun call_many(f: () -> String) -> String = f()\nfun bad(x: ~String) -> String = call_many(() => x)";
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
        output.contains("own"),
        "expected ownership help text in:\n{output}"
    );
}

#[test]
fn no_own_mismatch_no_help() {
    let output = render_error("if true { 1 } else { \"hi\" }");
    assert!(
        !output.contains("single-use closure") && !output.contains("own"),
        "expected no ownership help text in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_e0101() {
    let src = "fun consume(buf: ~String) -> String = buf\nfun bad(x: ~String) -> String = { let f = () => consume(x); f(); f() }";
    let output = render_module_error(src);
    assert!(
        output.contains("captures own value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_e0001() {
    let src = "fun call_many(f: () -> String) -> String = f()\nfun bad(x: ~String) -> String = call_many(() => x)";
    let output = render_module_error(src);
    assert!(
        output.contains("captures own value `x`"),
        "expected own capture note in:\n{output}"
    );
}

#[test]
fn own_fn_capture_note_correct_name() {
    let src = "fun consume(buf: ~String) -> String = buf\nfun bad(a: String, b: ~String) -> String = { let f = () => consume(b); f(); f() }";
    let output = render_module_error(src);
    assert!(
        output.contains("captures own value `b`"),
        "expected own capture note mentioning `b` in:\n{output}"
    );
}

#[test]
fn test_qualifier_mismatch_diagnostic() {
    let output = render_fixture_error("../../tests/fixtures/m6/qualifier_dup_error.kr");
    insta::assert_snapshot!(output);
    // No type-theory jargon in error/help lines (exclude file path lines)
    let message_lines: String = output.lines()
        .filter(|l| !l.contains("qualifier_dup_error.kr"))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(!message_lines.contains("affine"), "should not contain 'affine': {message_lines}");
    assert!(!message_lines.contains("qualifier"), "should not contain 'qualifier': {message_lines}");
    assert!(!message_lines.contains("unlimited"), "should not contain 'unlimited': {message_lines}");
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
        ("E0005", "{ let f = x => x; f(1, 2) }"),
        ("E0007", "x => x(x)"),
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
    use krypton_typechecker::module_resolver::ModuleResolver;

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
    assert!(output.contains("circular import"), "expected 'circular import' in:\n{output}");
}
