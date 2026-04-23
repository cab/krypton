//! Formatting-preserving edits to `krypton.toml`.
//!
//! Backs the `krypton add` and `krypton remove` CLI commands. Uses
//! `toml_edit` so comments and whitespace outside the modified section
//! are preserved verbatim.

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use toml_edit::{DocumentMut, InlineTable, Item, Table, Value};

use crate::manifest::{validate_owner_name, ErrorCode, GitRef, ManifestError};
use crate::resolve::default_local_root_name;

/// The source a new dependency will be pinned to. Mirrors the `DepSpec`
/// tag in `manifest.rs` but carries only the fields that are inserted
/// into TOML (canonical name is passed separately to `add_dependency`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AddSource {
    Git { url: String, git_ref: GitRef },
    Path { path: PathBuf },
    Registry { version: String },
}

pub struct ManifestEditor {
    path: PathBuf,
    doc: DocumentMut,
}

#[derive(Debug)]
pub enum ManifestEditError {
    Io {
        path: PathBuf,
        source: io::Error,
    },
    Parse {
        path: PathBuf,
        message: String,
    },
    InvalidCanonical(ManifestError),
    InvalidLocalRoot {
        name: String,
        reason: String,
    },
    DuplicateDependency {
        local_root: String,
    },
    DependencyNotFound {
        local_root: String,
    },
    /// `[dependencies]` exists but is not a TOML table (e.g. somebody wrote
    /// `dependencies = "wat"`). We refuse to mutate it rather than silently
    /// replacing the value.
    MalformedDependenciesSection,
}

impl fmt::Display for ManifestEditError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ManifestEditError::Io { path, source } => {
                write!(f, "I/O error at '{}': {source}", path.display())
            }
            ManifestEditError::Parse { path, message } => {
                write!(f, "failed to parse manifest '{}': {message}", path.display())
            }
            ManifestEditError::InvalidCanonical(e) => {
                write!(f, "invalid package name: {e}")
            }
            ManifestEditError::InvalidLocalRoot { name, reason } => {
                write!(f, "invalid local root '{name}': {reason}")
            }
            ManifestEditError::DuplicateDependency { local_root } => {
                write!(f, "dependency '{local_root}' already exists")
            }
            ManifestEditError::DependencyNotFound { local_root } => {
                write!(f, "dependency '{local_root}' not found in [dependencies]")
            }
            ManifestEditError::MalformedDependenciesSection => {
                write!(
                    f,
                    "[dependencies] exists but is not a table; refusing to edit"
                )
            }
        }
    }
}

impl std::error::Error for ManifestEditError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ManifestEditError::Io { source, .. } => Some(source),
            ManifestEditError::InvalidCanonical(e) => Some(e),
            _ => None,
        }
    }
}

impl ManifestEditor {
    /// Parse an existing `krypton.toml` into an editable document. Does
    /// *not* validate via `Manifest::from_str` — shape validation is the
    /// caller's job after the edit.
    pub fn from_path(path: &Path) -> Result<Self, ManifestEditError> {
        let src = fs::read_to_string(path).map_err(|source| ManifestEditError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        let doc: DocumentMut = src.parse().map_err(|e: toml_edit::TomlError| {
            ManifestEditError::Parse {
                path: path.to_path_buf(),
                message: e.to_string(),
            }
        })?;
        Ok(Self {
            path: path.to_path_buf(),
            doc,
        })
    }

    /// Construct an editor from an in-memory string. Used by unit tests
    /// that don't want to round-trip through the filesystem.
    pub fn from_str_with_path(
        src: &str,
        path: impl Into<PathBuf>,
    ) -> Result<Self, ManifestEditError> {
        let path = path.into();
        let doc: DocumentMut = src.parse().map_err(|e: toml_edit::TomlError| {
            ManifestEditError::Parse {
                path: path.clone(),
                message: e.to_string(),
            }
        })?;
        Ok(Self { path, doc })
    }

    pub fn render(&self) -> String {
        self.doc.to_string()
    }

    pub fn write(&self, path: &Path) -> Result<(), ManifestEditError> {
        fs::write(path, self.render()).map_err(|source| ManifestEditError::Io {
            path: path.to_path_buf(),
            source,
        })
    }

    /// Append a dependency under `[dependencies]`, creating the section
    /// if it does not yet exist. Returns the local-root key that was
    /// actually inserted — useful for echoing to the user.
    pub fn add_dependency(
        &mut self,
        canonical: &str,
        source: AddSource,
        as_override: Option<&str>,
    ) -> Result<String, ManifestEditError> {
        validate_owner_name(canonical).map_err(|msg| {
            ManifestEditError::InvalidCanonical(ManifestError {
                code: ErrorCode::M0004,
                field_path: String::new(),
                message: msg,
            })
        })?;

        let local_root = match as_override {
            Some(name) => {
                validate_local_root(name)?;
                name.to_string()
            }
            None => {
                let leaf = canonical
                    .split('/')
                    .nth(1)
                    .expect("validate_owner_name ensures an owner/name split");
                let default = default_local_root_name(leaf);
                validate_local_root(&default)?;
                default
            }
        };

        let deps = ensure_dependencies_table(&mut self.doc)?;
        if deps.contains_key(&local_root) {
            return Err(ManifestEditError::DuplicateDependency { local_root });
        }

        let mut inline = InlineTable::new();
        inline.insert("package", Value::from(canonical));
        match &source {
            AddSource::Git { url, git_ref } => {
                inline.insert("git", Value::from(url.as_str()));
                match git_ref {
                    GitRef::Tag(t) => {
                        inline.insert("tag", Value::from(t.as_str()));
                    }
                    GitRef::Branch(b) => {
                        inline.insert("branch", Value::from(b.as_str()));
                    }
                    GitRef::Rev(r) => {
                        inline.insert("rev", Value::from(r.as_str()));
                    }
                }
            }
            AddSource::Path { path } => {
                inline.insert("path", Value::from(path_to_toml_string(path)));
            }
            AddSource::Registry { version } => {
                inline.insert("version", Value::from(version.as_str()));
            }
        }

        deps.insert(&local_root, Item::Value(Value::InlineTable(inline)));
        Ok(local_root)
    }

    pub fn remove_dependency(&mut self, local_root: &str) -> Result<(), ManifestEditError> {
        let root = self.doc.as_table_mut();
        let Some(item) = root.get_mut("dependencies") else {
            return Err(ManifestEditError::DependencyNotFound {
                local_root: local_root.to_string(),
            });
        };
        let deps = item
            .as_table_mut()
            .ok_or(ManifestEditError::MalformedDependenciesSection)?;
        if deps.remove(local_root).is_none() {
            return Err(ManifestEditError::DependencyNotFound {
                local_root: local_root.to_string(),
            });
        }
        Ok(())
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

/// Local-root identifier rule: `[a-z_][a-z0-9_]*`. Matches the module-root
/// identifier shape (per `package_manager.md`) with `_` explicitly
/// permitted since a project's dependency key is a Krypton module path.
fn validate_local_root(name: &str) -> Result<(), ManifestEditError> {
    if name.is_empty() {
        return Err(ManifestEditError::InvalidLocalRoot {
            name: name.to_string(),
            reason: "must not be empty".to_string(),
        });
    }
    let mut bytes = name.bytes();
    let first = bytes.next().unwrap();
    if !(first.is_ascii_lowercase() || first == b'_') {
        return Err(ManifestEditError::InvalidLocalRoot {
            name: name.to_string(),
            reason: "must start with a lowercase ASCII letter or underscore".to_string(),
        });
    }
    for b in bytes {
        if !(b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_') {
            return Err(ManifestEditError::InvalidLocalRoot {
                name: name.to_string(),
                reason: format!(
                    "contains invalid character '{}' (allowed: lowercase a-z, 0-9, '_')",
                    b as char
                ),
            });
        }
    }
    Ok(())
}

/// Locate or create `[dependencies]` as a rendered top-level table.
fn ensure_dependencies_table(doc: &mut DocumentMut) -> Result<&mut Table, ManifestEditError> {
    let root = doc.as_table_mut();
    if !root.contains_key("dependencies") {
        let mut t = Table::new();
        t.set_implicit(false);
        root.insert("dependencies", Item::Table(t));
    }
    let item = root
        .get_mut("dependencies")
        .expect("just inserted if absent");
    let table = item
        .as_table_mut()
        .ok_or(ManifestEditError::MalformedDependenciesSection)?;
    // A `[dependencies]` table written by `krypton add` must be rendered
    // with its header even when empty, so downstream edits see a concrete
    // section rather than an implicit ancestor of a dotted key.
    table.set_implicit(false);
    Ok(table)
}

/// Express a path for a TOML string value. We store the path verbatim as
/// the user provided it (no normalization); resolver canonicalization
/// happens at load time, not edit time. On Windows, backslashes would
/// need escaping inside a TOML basic string — convert to forward slashes,
/// which TOML accepts and Krypton's path loader normalizes.
fn path_to_toml_string(p: &Path) -> String {
    if std::path::MAIN_SEPARATOR == '/' {
        p.to_string_lossy().into_owned()
    } else {
        p.to_string_lossy().replace(std::path::MAIN_SEPARATOR, "/")
    }
}

