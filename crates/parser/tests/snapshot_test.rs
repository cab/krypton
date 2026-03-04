use insta::assert_yaml_snapshot;
use serde::Serialize;

#[derive(Debug, Serialize)]
struct Placeholder {
    kind: String,
    value: i64,
}

#[test]
fn test_placeholder_snapshot() {
    let node = Placeholder {
        kind: "IntLiteral".to_string(),
        value: 42,
    };
    assert_yaml_snapshot!(node);
}
