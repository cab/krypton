use alang_test_harness::{parse_expectations, Expectation};

#[test]
fn expect_ok() {
    let source = "# expect: ok\n";
    let expectations = parse_expectations(source);
    assert_eq!(expectations, vec![Expectation::Ok]);
}

#[test]
fn expect_error_code() {
    let source = "# expect: error E0001\n";
    let expectations = parse_expectations(source);
    assert_eq!(expectations, vec![Expectation::Error("E0001".to_string())]);
}

#[test]
fn expect_output_quoted_string() {
    let source = "# expect: output \"hello world\"\n";
    let expectations = parse_expectations(source);
    assert_eq!(
        expectations,
        vec![Expectation::Output("hello world".to_string())]
    );
}

#[test]
fn expect_output_number() {
    let source = "# expect: output 3628800\n";
    let expectations = parse_expectations(source);
    assert_eq!(
        expectations,
        vec![Expectation::Output("3628800".to_string())]
    );
}

#[test]
fn multiple_expectations() {
    let source = "# expect: ok\n# expect: error E0001\n# expect: output \"hi\"\n";
    let expectations = parse_expectations(source);
    assert_eq!(
        expectations,
        vec![
            Expectation::Ok,
            Expectation::Error("E0001".to_string()),
            Expectation::Output("hi".to_string()),
        ]
    );
}

#[test]
fn non_expect_lines_ignored() {
    let source = "# This is a comment\n(def main (fn [] \"hello\"))\n# expect: ok\n";
    let expectations = parse_expectations(source);
    assert_eq!(expectations, vec![Expectation::Ok]);
}

#[test]
fn empty_file_no_expectations() {
    let source = "";
    let expectations = parse_expectations(source);
    assert!(expectations.is_empty());
}

#[test]
fn expect_ok_case_insensitive() {
    let source = "# expect: OK\n";
    let expectations = parse_expectations(source);
    assert_eq!(expectations, vec![Expectation::Ok]);
}

#[test]
fn expect_with_extra_whitespace() {
    let source = "  # expect:   ok  \n";
    let expectations = parse_expectations(source);
    assert_eq!(expectations, vec![Expectation::Ok]);
}
