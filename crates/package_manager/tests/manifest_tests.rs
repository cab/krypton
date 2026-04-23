use std::path::PathBuf;

use krypton_package_manager::{DepSpec, ErrorCode, GitRef, Manifest};
use semver::Version;

const SPEC_EXAMPLE: &str = r#"[package]
name = "my-org/my-app"
version = "0.1.0"
description = "A short description"
license = "MIT"
krypton = ">=0.1.0"          # minimum compiler version
# targets = ["jvm"]          # optional narrowing/documentation

[dependencies]
http = { package = "clementine/http", version = "0.3.0" }
json = { package = "clementine/json", git = "https://github.com/clementine/krypton-json", tag = "v0.2.0" }
shared = { package = "my-org/shared", path = "../shared" }

[dev-dependencies]
test_utils = { package = "clementine/test-utils", version = "0.1.0" }

[jvm]
maven = [
    "org.postgresql:postgresql:42.7.1",
    "com.google.guava:guava:33.0.0-jre",
]
classpath = [
    "lib/proprietary-driver.jar",
]
"#;

const SPEC_EXAMPLE_JAVA_VERSION: &str = r#"[package]
name = "clementine/http"
version = "0.3.0"

[jvm]
maven = ["org.postgresql:postgresql:42.7.1"]
classpath = ["lib/some.jar"]
java-version = "21"
"#;

#[test]
fn parses_spec_example_verbatim() {
    let m = Manifest::from_str(SPEC_EXAMPLE).expect("should parse");

    assert_eq!(m.package.name, "my-org/my-app");
    assert_eq!(m.package.version, Version::parse("0.1.0").unwrap());
    assert_eq!(
        m.package.description.as_deref(),
        Some("A short description")
    );
    assert_eq!(m.package.license.as_deref(), Some("MIT"));
    assert_eq!(m.package.krypton.as_deref(), Some(">=0.1.0"));

    assert_eq!(m.dependencies.len(), 3);
    match m.dependencies.get("http").expect("http dep") {
        DepSpec::Version { package, version } => {
            assert_eq!(package, "clementine/http");
            assert_eq!(version, "0.3.0");
        }
        other => panic!("expected Version dep, got {other:?}"),
    }
    match m.dependencies.get("json").expect("json dep") {
        DepSpec::Git {
            package,
            url,
            reference,
        } => {
            assert_eq!(package, "clementine/json");
            assert_eq!(url, "https://github.com/clementine/krypton-json");
            assert_eq!(*reference, GitRef::Tag("v0.2.0".to_string()));
        }
        other => panic!("expected Git dep, got {other:?}"),
    }
    match m.dependencies.get("shared").expect("shared dep") {
        DepSpec::Path {
            package,
            path,
            version,
        } => {
            assert_eq!(package, "my-org/shared");
            assert_eq!(path, &PathBuf::from("../shared"));
            assert!(version.is_none());
        }
        other => panic!("expected Path dep, got {other:?}"),
    }

    assert_eq!(m.dev_dependencies.len(), 1);
    match m
        .dev_dependencies
        .get("test_utils")
        .expect("test_utils dep")
    {
        DepSpec::Version { package, version } => {
            assert_eq!(package, "clementine/test-utils");
            assert_eq!(version, "0.1.0");
        }
        other => panic!("expected Version dev dep, got {other:?}"),
    }

    let jvm = m.jvm.expect("jvm section present");
    assert_eq!(
        jvm.maven,
        vec![
            "org.postgresql:postgresql:42.7.1".to_string(),
            "com.google.guava:guava:33.0.0-jre".to_string(),
        ]
    );
    assert_eq!(
        jvm.classpath,
        vec![PathBuf::from("lib/proprietary-driver.jar")]
    );
    assert!(jvm.java_version.is_none());
}

#[test]
fn parses_java_version_rename() {
    let m = Manifest::from_str(SPEC_EXAMPLE_JAVA_VERSION).expect("should parse");
    let jvm = m.jvm.expect("jvm section");
    assert_eq!(
        jvm.maven,
        vec!["org.postgresql:postgresql:42.7.1".to_string()]
    );
    assert_eq!(jvm.classpath, vec![PathBuf::from("lib/some.jar")]);
    assert_eq!(jvm.java_version.as_deref(), Some("21"));
}

#[test]
fn missing_package_section() {
    let src = r#"
[dependencies]
http = { package = "clementine/http", version = "0.3.0" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0002);
    assert_eq!(err.field_path, "package");
}

#[test]
fn missing_package_name() {
    let src = r#"
[package]
version = "0.1.0"
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0003);
    assert_eq!(err.field_path, "package.name");
}

#[test]
fn invalid_package_name_uppercase() {
    let src = r#"
[package]
name = "MyOrg/app"
version = "0.1.0"
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0004);
    assert_eq!(err.field_path, "package.name");
}

#[test]
fn invalid_package_name_no_owner() {
    let src = r#"
[package]
name = "app"
version = "0.1.0"
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0004);
    assert_eq!(err.field_path, "package.name");
}

#[test]
fn invalid_package_name_trailing_hyphen() {
    let src = r#"
[package]
name = "a-/b"
version = "0.1.0"
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0004);
    assert_eq!(err.field_path, "package.name");
}

#[test]
fn invalid_package_version() {
    let src = r#"
[package]
name = "my-org/app"
version = "not-a-version"
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0005);
    assert_eq!(err.field_path, "package.version");
}

#[test]
fn dep_no_source() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
http = { package = "clementine/http" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0006);
    assert_eq!(err.field_path, "dependencies.http");
    assert_eq!(
        err.message,
        "must specify exactly one of 'git', 'path', or 'version'"
    );
    assert_eq!(
        err.to_string(),
        "dependencies.http: must specify exactly one of 'git', 'path', or 'version'"
    );
}

#[test]
fn dep_git_and_path() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
http = { package = "clementine/http", git = "https://x", path = "../x", tag = "v1" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0007);
    assert_eq!(err.field_path, "dependencies.http");
}

#[test]
fn dep_git_and_version() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
http = { package = "clementine/http", git = "https://x", version = "0.1.0" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0007);
    assert_eq!(err.field_path, "dependencies.http");
}

#[test]
fn dep_git_no_ref() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
http = { package = "clementine/http", git = "https://x" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0008);
    assert_eq!(err.field_path, "dependencies.http");
}

#[test]
fn dep_git_two_refs() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
http = { package = "clementine/http", git = "https://x", tag = "v1", branch = "main" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0008);
    assert_eq!(err.field_path, "dependencies.http");
}

#[test]
fn dep_missing_package_field() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
http = { version = "0.1.0" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0003);
    assert_eq!(err.field_path, "dependencies.http.package");
}

#[test]
fn dev_dep_validation_uses_dev_dependencies_path() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dev-dependencies]
tool = { package = "clementine/tool" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0006);
    assert!(err.field_path.starts_with("dev-dependencies."));
    assert_eq!(err.field_path, "dev-dependencies.tool");
}

#[test]
fn non_git_dep_with_stray_tag_errors() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
http = { package = "clementine/http", version = "0.1.0", tag = "v1" }
"#;
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0007);
    assert_eq!(err.field_path, "dependencies.http");
}

#[test]
fn path_dep_with_version_is_allowed() {
    let src = r#"
[package]
name = "my-org/app"
version = "0.1.0"

[dependencies]
shared = { package = "my-org/shared", path = "../shared", version = "0.1.0" }
"#;
    let m = Manifest::from_str(src).expect("should parse");
    match m.dependencies.get("shared").expect("shared dep") {
        DepSpec::Path {
            package,
            path,
            version,
        } => {
            assert_eq!(package, "my-org/shared");
            assert_eq!(path, &PathBuf::from("../shared"));
            assert_eq!(version.as_deref(), Some("0.1.0"));
        }
        other => panic!("expected Path dep, got {other:?}"),
    }
}

#[test]
fn from_path_happy() {
    let dir = tempfile::tempdir().expect("tempdir");
    let manifest_path = dir.path().join("krypton.toml");
    std::fs::write(&manifest_path, SPEC_EXAMPLE).expect("write manifest");
    let m = Manifest::from_path(&manifest_path).expect("should parse from path");
    assert_eq!(m.package.name, "my-org/my-app");
}

#[test]
fn from_path_missing_file() {
    let dir = tempfile::tempdir().expect("tempdir");
    let missing = dir.path().join("does-not-exist.toml");
    let err = Manifest::from_path(&missing).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0009);
}

#[test]
fn toml_syntax_error() {
    let src = "this is not { valid toml";
    let err = Manifest::from_str(src).expect_err("should fail");
    assert_eq!(err.code, ErrorCode::M0001);
    assert_eq!(err.field_path, "");
}
