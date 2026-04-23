use krypton_package_manager::{VersionReq, VersionReqErrorCode};
use semver::Version;

fn v(s: &str) -> Version {
    Version::parse(s).expect("valid semver")
}

#[test]
fn parse_caret_default_full_version() {
    let req = VersionReq::parse("1.2.3").expect("parses");
    assert!(req.matches(&v("1.2.3")));
    assert!(req.matches(&v("1.99.99")));
    assert!(!req.matches(&v("2.0.0")));
    assert!(!req.matches(&v("1.2.2")));
}

#[test]
fn parse_caret_zero_minor() {
    let req = VersionReq::parse("0.3.0").expect("parses");
    assert!(req.matches(&v("0.3.0")));
    assert!(req.matches(&v("0.3.99")));
    assert!(!req.matches(&v("0.4.0")));
    assert!(!req.matches(&v("0.2.99")));
}

#[test]
fn parse_caret_zero_zero_patch() {
    let req = VersionReq::parse("0.0.7").expect("parses");
    assert!(req.matches(&v("0.0.7")));
    assert!(!req.matches(&v("0.0.8")));
    assert!(!req.matches(&v("0.0.6")));
}

#[test]
fn parse_exact_match() {
    let req = VersionReq::parse("=1.2.3").expect("parses");
    assert!(req.matches(&v("1.2.3")));
    assert!(!req.matches(&v("1.2.4")));
    assert!(!req.matches(&v("1.2.2")));
    assert!(!req.matches(&v("1.3.0")));
}

#[test]
fn parse_compound_range() {
    let req = VersionReq::parse(">=0.2.0, <0.4.0").expect("parses");
    assert!(req.matches(&v("0.2.0")));
    assert!(req.matches(&v("0.3.99")));
    assert!(!req.matches(&v("0.1.99")));
    assert!(!req.matches(&v("0.4.0")));
}

#[test]
fn error_empty_input() {
    let err = VersionReq::parse("").expect_err("empty should fail");
    assert_eq!(err.code, VersionReqErrorCode::V0001);
    assert_eq!(err.input, "");
    assert!(
        err.message.to_lowercase().contains("empty"),
        "message should mention empty input, got: {}",
        err.message
    );
}

#[test]
fn error_non_numeric() {
    let err = VersionReq::parse("abc").expect_err("non-numeric should fail");
    assert_eq!(err.code, VersionReqErrorCode::V0003);
    assert_eq!(err.input, "abc");
    assert!(
        err.message.contains("abc"),
        "message should quote input, got: {}",
        err.message
    );
}

#[test]
fn error_partial_version() {
    let err = VersionReq::parse("1.2").expect_err("partial should fail");
    assert_eq!(err.code, VersionReqErrorCode::V0002);
    assert_eq!(err.input, "1.2");
    assert!(
        err.message.contains("1.2"),
        "message should quote input, got: {}",
        err.message
    );
    assert!(
        err.message.contains("major.minor.patch"),
        "message should name the required form, got: {}",
        err.message
    );
}

#[test]
fn display_round_trips() {
    for input in &["1.2.3", "=1.2.3", ">=0.2.0, <0.4.0"] {
        let first = VersionReq::parse(input).expect("parses");
        let rendered = first.to_string();
        let second = VersionReq::parse(&rendered).expect("displayed form parses");
        assert_eq!(first, second, "round-trip mismatch for input {input:?}");
    }

    let caret = VersionReq::parse("1.2.3").expect("parses");
    assert_eq!(caret.to_string(), "^1.2.3");
}

#[test]
fn boundary_caret_one_two_three() {
    let req = VersionReq::parse("^1.2.3").expect("parses");
    assert!(req.matches(&v("1.99.99")));
    assert!(!req.matches(&v("2.0.0")));
}

#[test]
fn boundary_caret_zero_zero_seven() {
    let req = VersionReq::parse("^0.0.7").expect("parses");
    assert!(req.matches(&v("0.0.7")));
    assert!(!req.matches(&v("0.0.8")));
}
