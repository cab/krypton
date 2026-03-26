use krypton_test_harness::{discover_fixtures, load_fixture, Expectation};
use std::path::Path;

fn fixtures_dir() -> &'static Path {
    // Walk up from the crate directory to the repo root
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent() // crates/
        .unwrap()
        .parent() // repo root
        .unwrap()
}

#[test]
fn discovers_smoke_fixtures() {
    let dir = fixtures_dir().join("tests/fixtures/smoke");
    let paths = discover_fixtures(&dir);
    assert!(
        !paths.is_empty(),
        "should find at least one fixture in smoke/"
    );
    assert!(
        paths.iter().any(|p| p.ends_with("empty.kr")),
        "should find empty.kr"
    );
}

#[test]
fn loads_empty_fixture() {
    let path = fixtures_dir().join("tests/fixtures/smoke/empty.kr");
    let fixture = load_fixture(&path);
    assert_eq!(fixture.expectations, vec![Expectation::Ok]);
    assert!(fixture.source.contains("# expect: ok"));
}
