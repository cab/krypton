use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

use semver::Version;
use serde::Deserialize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub package: PackageInfo,
    pub dependencies: BTreeMap<String, DepSpec>,
    pub dev_dependencies: BTreeMap<String, DepSpec>,
    pub jvm: Option<JvmConfig>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageInfo {
    pub name: String,
    pub version: Version,
    pub description: Option<String>,
    pub license: Option<String>,
    pub krypton: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DepSpec {
    Version {
        package: String,
        version: String,
    },
    Git {
        package: String,
        url: String,
        reference: GitRef,
    },
    Path {
        package: String,
        path: PathBuf,
        version: Option<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GitRef {
    Tag(String),
    Rev(String),
    Branch(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct JvmConfig {
    pub maven: Vec<String>,
    pub classpath: Vec<PathBuf>,
    pub java_version: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    M0001,
    M0002,
    M0003,
    M0004,
    M0005,
    M0006,
    M0007,
    M0008,
    M0009,
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorCode::M0001 => write!(f, "M0001"),
            ErrorCode::M0002 => write!(f, "M0002"),
            ErrorCode::M0003 => write!(f, "M0003"),
            ErrorCode::M0004 => write!(f, "M0004"),
            ErrorCode::M0005 => write!(f, "M0005"),
            ErrorCode::M0006 => write!(f, "M0006"),
            ErrorCode::M0007 => write!(f, "M0007"),
            ErrorCode::M0008 => write!(f, "M0008"),
            ErrorCode::M0009 => write!(f, "M0009"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ManifestError {
    pub code: ErrorCode,
    pub field_path: String,
    pub message: String,
}

impl ManifestError {
    fn new(code: ErrorCode, field_path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code,
            field_path: field_path.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.field_path.is_empty() {
            write!(f, "{}", self.message)
        } else {
            write!(f, "{}: {}", self.field_path, self.message)
        }
    }
}

impl std::error::Error for ManifestError {}

#[derive(Deserialize)]
struct RawManifest {
    package: Option<RawPackage>,
    #[serde(default)]
    dependencies: BTreeMap<String, RawDepSpec>,
    #[serde(rename = "dev-dependencies", default)]
    dev_dependencies: BTreeMap<String, RawDepSpec>,
    jvm: Option<RawJvmConfig>,
}

#[derive(Deserialize)]
struct RawPackage {
    name: Option<String>,
    version: Option<String>,
    description: Option<String>,
    license: Option<String>,
    krypton: Option<String>,
}

#[derive(Deserialize)]
struct RawDepSpec {
    package: Option<String>,
    version: Option<String>,
    git: Option<String>,
    tag: Option<String>,
    rev: Option<String>,
    branch: Option<String>,
    path: Option<PathBuf>,
}

#[derive(Deserialize)]
struct RawJvmConfig {
    #[serde(default)]
    maven: Vec<String>,
    #[serde(default)]
    classpath: Vec<PathBuf>,
    #[serde(rename = "java-version")]
    java_version: Option<String>,
}

impl Manifest {
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(src: &str) -> Result<Self, ManifestError> {
        let raw: RawManifest = toml::from_str(src)
            .map_err(|e| ManifestError::new(ErrorCode::M0001, "", e.to_string()))?;
        into_manifest(raw)
    }

    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, ManifestError> {
        let path = path.as_ref();
        let src = std::fs::read_to_string(path).map_err(|e| {
            ManifestError::new(
                ErrorCode::M0009,
                path.display().to_string(),
                format!("failed to read manifest file: {e}"),
            )
        })?;
        Self::from_str(&src)
    }
}

fn into_manifest(raw: RawManifest) -> Result<Manifest, ManifestError> {
    let pkg_raw = raw.package.ok_or_else(|| {
        ManifestError::new(ErrorCode::M0002, "package", "missing [package] section")
    })?;

    let name = pkg_raw.name.ok_or_else(|| {
        ManifestError::new(
            ErrorCode::M0003,
            "package.name",
            "missing required field 'name'",
        )
    })?;
    validate_owner_name(&name).map_err(|msg| {
        ManifestError::new(ErrorCode::M0004, "package.name", msg)
    })?;

    let version_str = pkg_raw.version.ok_or_else(|| {
        ManifestError::new(
            ErrorCode::M0003,
            "package.version",
            "missing required field 'version'",
        )
    })?;
    let version = Version::parse(&version_str).map_err(|e| {
        ManifestError::new(
            ErrorCode::M0005,
            "package.version",
            format!("invalid version '{version_str}': {e}"),
        )
    })?;

    let package = PackageInfo {
        name,
        version,
        description: pkg_raw.description,
        license: pkg_raw.license,
        krypton: pkg_raw.krypton,
    };

    let dependencies = convert_deps(raw.dependencies, "dependencies")?;
    let dev_dependencies = convert_deps(raw.dev_dependencies, "dev-dependencies")?;

    let jvm = raw.jvm.map(|j| JvmConfig {
        maven: j.maven,
        classpath: j.classpath,
        java_version: j.java_version,
    });

    Ok(Manifest {
        package,
        dependencies,
        dev_dependencies,
        jvm,
    })
}

fn convert_deps(
    raw: BTreeMap<String, RawDepSpec>,
    section: &str,
) -> Result<BTreeMap<String, DepSpec>, ManifestError> {
    let mut out = BTreeMap::new();
    for (key, dep) in raw {
        let base = format!("{section}.{key}");
        let spec = convert_dep(&base, dep)?;
        out.insert(key, spec);
    }
    Ok(out)
}

fn convert_dep(base: &str, dep: RawDepSpec) -> Result<DepSpec, ManifestError> {
    let package = dep.package.ok_or_else(|| {
        ManifestError::new(
            ErrorCode::M0003,
            format!("{base}.package"),
            "missing required field 'package'",
        )
    })?;
    validate_owner_name(&package).map_err(|msg| {
        ManifestError::new(ErrorCode::M0004, format!("{base}.package"), msg)
    })?;

    let has_git = dep.git.is_some();
    let has_path = dep.path.is_some();
    let has_version = dep.version.is_some();
    let has_tag = dep.tag.is_some();
    let has_rev = dep.rev.is_some();
    let has_branch = dep.branch.is_some();

    if has_git && has_path {
        return Err(ManifestError::new(
            ErrorCode::M0007,
            base.to_string(),
            "conflicting sources: 'git' and 'path'",
        ));
    }
    if has_git && has_version {
        return Err(ManifestError::new(
            ErrorCode::M0007,
            base.to_string(),
            "conflicting sources: 'git' and 'version' (use 'tag', 'rev', or 'branch')",
        ));
    }

    if has_git {
        let url = dep.git.unwrap();
        let ref_count =
            usize::from(has_tag) + usize::from(has_rev) + usize::from(has_branch);
        if ref_count != 1 {
            return Err(ManifestError::new(
                ErrorCode::M0008,
                base.to_string(),
                "git dependency requires exactly one of 'tag', 'rev', or 'branch'",
            ));
        }
        let reference = if let Some(t) = dep.tag {
            GitRef::Tag(t)
        } else if let Some(r) = dep.rev {
            GitRef::Rev(r)
        } else {
            GitRef::Branch(dep.branch.unwrap())
        };
        return Ok(DepSpec::Git {
            package,
            url,
            reference,
        });
    }

    let stray = stray_git_refs(has_tag, has_rev, has_branch);
    if !stray.is_empty() {
        return Err(ManifestError::new(
            ErrorCode::M0007,
            base.to_string(),
            format!(
                "non-git dependency has stray git reference field(s): {stray}"
            ),
        ));
    }

    if has_path {
        return Ok(DepSpec::Path {
            package,
            path: dep.path.unwrap(),
            version: dep.version,
        });
    }

    if has_version {
        return Ok(DepSpec::Version {
            package,
            version: dep.version.unwrap(),
        });
    }

    Err(ManifestError::new(
        ErrorCode::M0006,
        base.to_string(),
        "must specify exactly one of 'git', 'path', or 'version'",
    ))
}

fn stray_git_refs(has_tag: bool, has_rev: bool, has_branch: bool) -> String {
    let mut parts = Vec::new();
    if has_tag {
        parts.push("'tag'");
    }
    if has_rev {
        parts.push("'rev'");
    }
    if has_branch {
        parts.push("'branch'");
    }
    parts.join(", ")
}

fn validate_owner_name(s: &str) -> Result<(), String> {
    let mut parts = s.split('/');
    let owner = parts.next().unwrap_or("");
    let name = parts.next().unwrap_or("");
    if parts.next().is_some() {
        return Err(format!(
            "package name '{s}' must have exactly one '/' separating owner and name"
        ));
    }
    if owner.is_empty() || name.is_empty() {
        return Err(format!(
            "package name '{s}' must be of the form 'owner/name' with non-empty segments"
        ));
    }
    validate_segment(owner).map_err(|e| format!("invalid owner in '{s}': {e}"))?;
    validate_segment(name).map_err(|e| format!("invalid name in '{s}': {e}"))?;
    Ok(())
}

fn validate_segment(seg: &str) -> Result<(), String> {
    if seg.is_empty() {
        return Err("empty segment".into());
    }
    let bytes = seg.as_bytes();
    let mut prev_hyphen = false;
    for (i, &b) in bytes.iter().enumerate() {
        let is_lower = b.is_ascii_lowercase();
        let is_digit = b.is_ascii_digit();
        let is_hyphen = b == b'-';
        if !(is_lower || is_digit || is_hyphen) {
            return Err(format!(
                "segment '{seg}' contains invalid character '{}' (allowed: lowercase a-z, 0-9, '-')",
                seg[i..].chars().next().unwrap()
            ));
        }
        if is_hyphen {
            if i == 0 {
                return Err(format!("segment '{seg}' must not start with '-'"));
            }
            if prev_hyphen {
                return Err(format!(
                    "segment '{seg}' must not contain consecutive '-' characters"
                ));
            }
            prev_hyphen = true;
        } else {
            prev_hyphen = false;
        }
    }
    if bytes.last() == Some(&b'-') {
        return Err(format!("segment '{seg}' must not end with '-'"));
    }
    Ok(())
}
