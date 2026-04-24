//! `krypton.lock` serialization, staleness detection, and rehydration.
//!
//! A lockfile pins every package in a resolved graph to a concrete on-disk
//! source (a git SHA or a path) together with an integrity hash over that
//! source tree. Re-entering the build with a current lockfile short-circuits
//! fetching and re-resolution.
//!
//! `[[maven]]` entries are shape-first: the lockfile reads and writes them
//! through unchanged, but this crate does not yet populate them. Coursier
//! integration (M35-T13) fills in the hashes and URLs.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io;
use std::path::{Component, Path, PathBuf};

use semver::Version;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use toml_edit::{value, ArrayOfTables, DocumentMut, Item, Table};

use crate::cache::CacheDir;
use crate::manifest::{DepSpec, GitRef, Manifest};
use crate::resolve::{CanonicalName, ResolvedGraph, ResolvedPackage, SourceType};
use crate::version::VersionReq;

/// A fully-materialized `krypton.lock` document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lockfile {
    pub packages: Vec<LockedPackage>,
    pub maven: Vec<LockedMaven>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockedPackage {
    pub name: CanonicalName,
    pub version: Version,
    pub source: LockedSource,
    /// `sha256:<hex>` digest over the canonical serialization of the source
    /// tree (see [`hash_source_tree`]).
    pub hash: String,
}

/// Where a locked package was materialized from, in a form suitable to
/// re-enter the cache without re-resolving.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LockedSource {
    /// A git remote pinned to a full 40-char commit SHA.
    Git { url: String, rev: String },
    /// A local path. Paths are serialized relative to the project root using
    /// forward slashes; `..` segments are permitted. When the resolved path
    /// is not under the project root and cannot be expressed as a
    /// `..`-prefixed relative path, the absolute path is stored instead.
    Path { path: PathBuf },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockedMaven {
    pub coord: String,
    pub url: String,
    pub hash: String,
}

/// Input to [`Lockfile::generate`] for populating `[[maven]]` rows. The
/// package manager does not yet compute these; the Coursier integration
/// produces them in M35-T13.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MavenArtifact {
    pub coord: String,
    pub url: String,
    pub hash: String,
}

#[derive(Debug)]
pub enum LockfileError {
    Io {
        path: PathBuf,
        source: io::Error,
    },
    Parse {
        path: PathBuf,
        message: String,
    },
    /// Shape/validation error on a parsed lockfile, or on rehydration when a
    /// locked package is missing from the cache.
    Invalid {
        message: String,
    },
}

impl fmt::Display for LockfileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LockfileError::Io { path, source } => {
                write!(f, "I/O error at '{}': {source}", path.display())
            }
            LockfileError::Parse { path, message } => {
                write!(
                    f,
                    "failed to parse lockfile '{}': {message}",
                    path.display()
                )
            }
            LockfileError::Invalid { message } => write!(f, "{message}"),
        }
    }
}

impl std::error::Error for LockfileError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            LockfileError::Io { source, .. } => Some(source),
            _ => None,
        }
    }
}

impl Lockfile {
    /// Build a lockfile from a resolved graph and the list of maven artifacts
    /// that `krypton-package-manager` has already materialized. `project_root`
    /// is used to compute the relative form of path sources; it does not need
    /// to be canonicalized by the caller.
    pub fn generate(
        graph: &ResolvedGraph,
        maven: &[MavenArtifact],
        project_root: &Path,
    ) -> Result<Self, LockfileError> {
        let project_root = canonicalize_for_display(project_root);

        let mut packages: Vec<LockedPackage> = Vec::with_capacity(graph.len());
        for (canonical, pkg) in graph.iter() {
            let hash = hash_source_tree(&pkg.source_path).map_err(|source| LockfileError::Io {
                path: pkg.source_path.clone(),
                source,
            })?;
            let source = match &pkg.source_type {
                SourceType::Git { url, sha, .. } => LockedSource::Git {
                    url: url.clone(),
                    rev: sha.clone(),
                },
                SourceType::Path { path } => LockedSource::Path {
                    path: relative_path(path, &project_root),
                },
            };
            packages.push(LockedPackage {
                name: canonical.clone(),
                version: pkg.version.clone(),
                source,
                hash,
            });
        }
        // `iter()` already yields in sorted canonical-name order because
        // `ResolvedGraph` is backed by a `BTreeMap`; we sort defensively so the
        // file is still deterministic if the backing store ever changes.
        packages.sort_by(|a, b| a.name.cmp(&b.name));

        let mut maven_rows: Vec<LockedMaven> = maven
            .iter()
            .map(|m| LockedMaven {
                coord: m.coord.clone(),
                url: m.url.clone(),
                hash: m.hash.clone(),
            })
            .collect();
        maven_rows.sort_by(|a, b| a.coord.cmp(&b.coord));

        Ok(Self {
            packages,
            maven: maven_rows,
        })
    }

    /// Read and parse a lockfile from disk.
    pub fn read(path: &Path) -> Result<Self, LockfileError> {
        let src = std::fs::read_to_string(path).map_err(|source| LockfileError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        Self::parse(&src, path)
    }

    /// Write the lockfile to `path`. Overwrites any existing file.
    pub fn write(&self, path: &Path) -> Result<(), LockfileError> {
        let rendered = self.to_toml_string();
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent).map_err(|source| LockfileError::Io {
                    path: parent.to_path_buf(),
                    source,
                })?;
            }
        }
        std::fs::write(path, rendered).map_err(|source| LockfileError::Io {
            path: path.to_path_buf(),
            source,
        })
    }

    /// Serialize this lockfile to a deterministic TOML string, including the
    /// `# This file is generated. Do not edit manually.` header.
    pub fn to_toml_string(&self) -> String {
        let mut doc = DocumentMut::new();
        doc.as_table_mut()
            .decor_mut()
            .set_prefix("# This file is generated. Do not edit manually.\n\n");

        if !self.packages.is_empty() {
            let mut aot = ArrayOfTables::new();
            for p in &self.packages {
                let mut t = Table::new();
                t.insert("name", value(p.name.as_str()));
                t.insert("version", value(p.version.to_string()));
                t.insert("source", value(encode_source(&p.source)));
                if let LockedSource::Git { rev, .. } = &p.source {
                    t.insert("rev", value(rev));
                }
                t.insert("hash", value(&p.hash));
                aot.push(t);
            }
            doc.insert("package", Item::ArrayOfTables(aot));
        }

        if !self.maven.is_empty() {
            let mut aot = ArrayOfTables::new();
            for m in &self.maven {
                let mut t = Table::new();
                t.insert("coord", value(&m.coord));
                t.insert("hash", value(&m.hash));
                t.insert("url", value(&m.url));
                aot.push(t);
            }
            doc.insert("maven", Item::ArrayOfTables(aot));
        }

        doc.to_string()
    }

    /// Decide whether this lockfile is still current for `manifest` rooted at
    /// `project_root`.
    ///
    /// A lockfile is current iff, for every direct dependency of the
    /// manifest, there is a locked package whose canonical name and source
    /// shape agree with the spec. Extra locked packages (transitives) are
    /// permitted. Moving git tag/branch targets are not detected here — per
    /// Cargo's convention, `krypton lock` is what chases them.
    pub fn is_current(&self, manifest: &Manifest, project_root: &Path) -> bool {
        let project_root = canonicalize_for_display(project_root);
        let by_name: BTreeMap<&CanonicalName, &LockedPackage> =
            self.packages.iter().map(|p| (&p.name, p)).collect();

        for dep in manifest.dependencies.values() {
            let canonical_str = dep_package_name(dep);
            let canonical = CanonicalName::from_validated(canonical_str);
            let Some(locked) = by_name.get(&canonical) else {
                return false;
            };
            if !dep_matches_locked(dep, locked, &project_root) {
                return false;
            }
        }
        true
    }

    /// Rehydrate a [`ResolvedGraph`] from this lockfile without invoking
    /// `git` or hitting the network. Git sources must already exist under
    /// `cache.package_source_dir(...)`; otherwise [`LockfileError::Invalid`]
    /// instructs the user to re-run `krypton lock` so the cache is
    /// repopulated.
    pub fn to_resolved_graph(
        &self,
        cache: &CacheDir,
        project_root: &Path,
    ) -> Result<ResolvedGraph, LockfileError> {
        let project_root = canonicalize_for_display(project_root);
        let mut packages: BTreeMap<CanonicalName, ResolvedPackage> = BTreeMap::new();
        for p in &self.packages {
            let (source_path, source_type) = match &p.source {
                LockedSource::Git { url, rev } => {
                    let source_path = cache.package_source_dir(p.name.owner(), p.name.name(), rev);
                    let manifest_path = source_path.join("krypton.toml");
                    if !manifest_path.exists() {
                        return Err(LockfileError::Invalid {
                            message: format!(
                                "cache miss for '{}@{}': no krypton.toml at '{}'; run `krypton lock`",
                                p.name,
                                rev,
                                manifest_path.display()
                            ),
                        });
                    }
                    let source_type = SourceType::Git {
                        url: url.clone(),
                        // The original tag/branch is not preserved in the
                        // lockfile; `Rev` is the faithful reconstruction.
                        reference: GitRef::Rev(rev.clone()),
                        sha: rev.clone(),
                    };
                    (source_path, source_type)
                }
                LockedSource::Path { path } => {
                    let absolute = if path.is_absolute() {
                        path.clone()
                    } else {
                        project_root.join(path)
                    };
                    let canonical_abs = std::fs::canonicalize(&absolute).unwrap_or(absolute);
                    (
                        canonical_abs.clone(),
                        SourceType::Path {
                            path: canonical_abs,
                        },
                    )
                }
            };

            let manifest_path = source_path.join("krypton.toml");
            let manifest =
                Manifest::from_path(&manifest_path).map_err(|source| LockfileError::Invalid {
                    message: format!(
                        "failed to load manifest for '{}' from '{}': {source}",
                        p.name,
                        manifest_path.display()
                    ),
                })?;

            packages.insert(
                p.name.clone(),
                ResolvedPackage {
                    canonical: p.name.clone(),
                    version: p.version.clone(),
                    source_path,
                    manifest,
                    source_type,
                },
            );
        }
        Ok(ResolvedGraph::from_packages(packages))
    }

    /// Parse a lockfile string. Used by [`Lockfile::read`]; exposed for tests
    /// that want to round-trip through [`to_toml_string`].
    fn parse(src: &str, origin: &Path) -> Result<Self, LockfileError> {
        let raw: RawLockfile = toml::from_str(src).map_err(|e| LockfileError::Parse {
            path: origin.to_path_buf(),
            message: e.to_string(),
        })?;

        let mut packages = Vec::with_capacity(raw.package.len());
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for p in raw.package {
            if !seen.insert(p.name.clone()) {
                return Err(LockfileError::Invalid {
                    message: format!("duplicate [[package]] entry '{}'", p.name),
                });
            }
            let version = Version::parse(&p.version).map_err(|e| LockfileError::Invalid {
                message: format!("invalid version '{}' for '{}': {e}", p.version, p.name),
            })?;
            let source =
                decode_source(&p).map_err(|msg| LockfileError::Invalid { message: msg })?;
            packages.push(LockedPackage {
                name: CanonicalName::from_validated(&p.name),
                version,
                source,
                hash: p.hash,
            });
        }
        packages.sort_by(|a, b| a.name.cmp(&b.name));

        let mut maven: Vec<LockedMaven> = raw
            .maven
            .into_iter()
            .map(|m| LockedMaven {
                coord: m.coord,
                url: m.url,
                hash: m.hash,
            })
            .collect();
        maven.sort_by(|a, b| a.coord.cmp(&b.coord));

        Ok(Self { packages, maven })
    }
}

#[derive(Deserialize)]
struct RawLockfile {
    #[serde(default)]
    package: Vec<RawLockedPackage>,
    #[serde(default)]
    maven: Vec<RawLockedMaven>,
}

#[derive(Deserialize)]
struct RawLockedPackage {
    name: String,
    version: String,
    source: String,
    #[serde(default)]
    rev: Option<String>,
    hash: String,
}

#[derive(Deserialize)]
struct RawLockedMaven {
    coord: String,
    url: String,
    hash: String,
}

fn encode_source(source: &LockedSource) -> String {
    match source {
        LockedSource::Git { url, .. } => format!("git+{url}"),
        LockedSource::Path { path } => format!("path+{}", path_to_forward_slashes(path)),
    }
}

fn decode_source(raw: &RawLockedPackage) -> Result<LockedSource, String> {
    if let Some(url) = raw.source.strip_prefix("git+") {
        let rev = raw.rev.clone().ok_or_else(|| {
            format!(
                "[[package]] '{}': git source requires a 'rev' field",
                raw.name
            )
        })?;
        if !is_full_sha(&rev) {
            return Err(format!(
                "[[package]] '{}': 'rev' must be a 40-char hex SHA (got '{rev}')",
                raw.name
            ));
        }
        Ok(LockedSource::Git {
            url: url.to_string(),
            rev,
        })
    } else if let Some(rel) = raw.source.strip_prefix("path+") {
        if raw.rev.is_some() {
            return Err(format!(
                "[[package]] '{}': path source must not carry a 'rev' field",
                raw.name
            ));
        }
        Ok(LockedSource::Path {
            path: forward_slashes_to_path(rel),
        })
    } else {
        Err(format!(
            "[[package]] '{}': unknown source scheme '{}' (expected 'git+…' or 'path+…')",
            raw.name, raw.source
        ))
    }
}

fn is_full_sha(s: &str) -> bool {
    s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

fn dep_package_name(dep: &DepSpec) -> &str {
    match dep {
        DepSpec::Git { package, .. }
        | DepSpec::Path { package, .. }
        | DepSpec::Version { package, .. } => package,
    }
}

fn dep_matches_locked(dep: &DepSpec, locked: &LockedPackage, project_root: &Path) -> bool {
    match dep {
        DepSpec::Git { url, reference, .. } => match &locked.source {
            LockedSource::Git {
                url: locked_url,
                rev: locked_rev,
            } => {
                if url != locked_url {
                    return false;
                }
                match reference {
                    GitRef::Rev(r) => r == locked_rev,
                    // Tag/branch updates are invisible to `is_current` by
                    // design; `krypton lock` is what re-resolves them.
                    GitRef::Tag(_) | GitRef::Branch(_) => true,
                }
            }
            _ => false,
        },
        DepSpec::Path {
            path,
            version: version_req,
            ..
        } => match &locked.source {
            LockedSource::Path { path: locked_rel } => {
                let abs_spec = if path.is_absolute() {
                    path.clone()
                } else {
                    project_root.join(path)
                };
                let abs_spec = std::fs::canonicalize(&abs_spec).unwrap_or(abs_spec);
                let abs_locked = if locked_rel.is_absolute() {
                    locked_rel.clone()
                } else {
                    project_root.join(locked_rel)
                };
                let abs_locked = std::fs::canonicalize(&abs_locked).unwrap_or(abs_locked);
                if abs_spec != abs_locked {
                    return false;
                }
                if let Some(req_str) = version_req {
                    let Ok(req) = VersionReq::parse(req_str) else {
                        return false;
                    };
                    if !req.matches(&locked.version) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        },
        // Registry deps are unsupported; force a re-resolve so the real error
        // surfaces there rather than silently passing `is_current`.
        DepSpec::Version { .. } => false,
    }
}

/// Canonicalize a path for display, falling back to the input on failure.
/// Lockfile generation needs a stable absolute path for relative-path
/// computation; resolver paths are already canonical, so this is mostly a
/// no-op in practice.
fn canonicalize_for_display(p: &Path) -> PathBuf {
    std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf())
}

/// Express `target` relative to `base`, using `..` segments as needed. If
/// the two paths share no common prefix (cross-drive on Windows, etc.),
/// fall back to the absolute target.
fn relative_path(target: &Path, base: &Path) -> PathBuf {
    if !target.is_absolute() || !base.is_absolute() {
        return target.to_path_buf();
    }
    let tc: Vec<Component<'_>> = target.components().collect();
    let bc: Vec<Component<'_>> = base.components().collect();

    // Require a shared root; otherwise fall back to absolute.
    if tc.first() != bc.first() {
        return target.to_path_buf();
    }

    let mut common = 0;
    while common < tc.len() && common < bc.len() && tc[common] == bc[common] {
        common += 1;
    }

    let mut out = PathBuf::new();
    for _ in common..bc.len() {
        out.push("..");
    }
    for c in &tc[common..] {
        out.push(c.as_os_str());
    }
    if out.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        out
    }
}

fn path_to_forward_slashes(p: &Path) -> String {
    let s = p.to_string_lossy();
    if std::path::MAIN_SEPARATOR == '/' {
        s.into_owned()
    } else {
        s.replace(std::path::MAIN_SEPARATOR, "/")
    }
}

fn forward_slashes_to_path(s: &str) -> PathBuf {
    if std::path::MAIN_SEPARATOR == '/' {
        PathBuf::from(s)
    } else {
        PathBuf::from(s.replace('/', std::path::MAIN_SEPARATOR_STR))
    }
}

/// Compute `sha256:<hex>` over a canonical serialization of the source tree
/// at `root`.
///
/// The serialization is:
///
/// 1. Recursively enumerate every file under `root`, skipping any directory
///    whose name is `.git` or `target` at any level.
/// 2. Collect `(relative_path, bytes)` pairs; sort by relative path so the
///    hash is independent of directory iteration order.
/// 3. For each pair, feed `[len(path) u64 LE][path utf-8][len(bytes) u64 LE][bytes]`
///    into the hasher. Length prefixes prevent ambiguity at the boundary.
pub(crate) fn hash_source_tree(root: &Path) -> io::Result<String> {
    let mut entries: Vec<(String, PathBuf)> = Vec::new();
    collect_files(root, root, &mut entries)?;
    entries.sort_by(|a, b| a.0.cmp(&b.0));

    let mut hasher = Sha256::new();
    for (rel, abs) in &entries {
        let bytes = std::fs::read(abs)?;
        hasher.update((rel.len() as u64).to_le_bytes());
        hasher.update(rel.as_bytes());
        hasher.update((bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    let digest = hasher.finalize();
    Ok(format!("sha256:{digest:x}"))
}

fn collect_files(root: &Path, dir: &Path, out: &mut Vec<(String, PathBuf)>) -> io::Result<()> {
    if !dir.exists() {
        return Ok(());
    }
    let mut children: Vec<(std::ffi::OsString, PathBuf, std::fs::FileType)> = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let ft = entry.file_type()?;
        children.push((entry.file_name(), entry.path(), ft));
    }
    children.sort_by(|a, b| a.0.cmp(&b.0));

    for (name, path, ft) in children {
        if ft.is_dir() {
            if name == "target" || name == ".git" {
                continue;
            }
            collect_files(root, &path, out)?;
        } else if ft.is_file() {
            let rel = path
                .strip_prefix(root)
                .map(|p| p.to_path_buf())
                .unwrap_or_else(|_| path.clone());
            let rel_str = path_to_forward_slashes(&rel);
            out.push((rel_str, path));
        }
        // Symlinks are currently ignored — path deps under active development
        // may contain them (e.g. editor swap files), but they aren't part of
        // the reproducible content.
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn hash_source_tree_ignores_git_and_target() {
        let a = tempdir().unwrap();
        let b = tempdir().unwrap();

        std::fs::create_dir_all(a.path().join("src")).unwrap();
        std::fs::write(a.path().join("src/lib.kr"), "x").unwrap();
        std::fs::create_dir_all(a.path().join(".git")).unwrap();
        std::fs::write(a.path().join(".git/HEAD"), "ref: refs/heads/main").unwrap();
        std::fs::create_dir_all(a.path().join("target/jvm")).unwrap();
        std::fs::write(a.path().join("target/jvm/foo.class"), b"bytecode").unwrap();

        std::fs::create_dir_all(b.path().join("src")).unwrap();
        std::fs::write(b.path().join("src/lib.kr"), "x").unwrap();

        let ha = hash_source_tree(a.path()).unwrap();
        let hb = hash_source_tree(b.path()).unwrap();
        assert_eq!(
            ha, hb,
            "`.git/` and `target/` must not contribute to the hash"
        );
    }

    #[test]
    fn hash_source_tree_detects_content_change() {
        let a = tempdir().unwrap();
        std::fs::write(a.path().join("f.kr"), "one").unwrap();
        let h1 = hash_source_tree(a.path()).unwrap();
        std::fs::write(a.path().join("f.kr"), "two").unwrap();
        let h2 = hash_source_tree(a.path()).unwrap();
        assert_ne!(h1, h2);
    }

    #[test]
    fn relative_path_descendant() {
        let base = PathBuf::from("/a/b");
        let target = PathBuf::from("/a/b/c/d");
        assert_eq!(relative_path(&target, &base), PathBuf::from("c/d"));
    }

    #[test]
    fn relative_path_sibling() {
        let base = PathBuf::from("/a/b");
        let target = PathBuf::from("/a/c");
        assert_eq!(relative_path(&target, &base), PathBuf::from("../c"));
    }

    #[test]
    fn relative_path_same_dir() {
        let base = PathBuf::from("/a/b");
        let target = PathBuf::from("/a/b");
        assert_eq!(relative_path(&target, &base), PathBuf::from("."));
    }

    #[test]
    fn relative_path_falls_back_to_absolute_when_not_absolute() {
        let base = PathBuf::from("relative/base");
        let target = PathBuf::from("/abs/target");
        assert_eq!(relative_path(&target, &base), PathBuf::from("/abs/target"));
    }

    #[test]
    fn is_full_sha_accepts_forty_hex() {
        assert!(is_full_sha(&"a".repeat(40)));
        assert!(!is_full_sha("abc"));
        assert!(!is_full_sha(&"z".repeat(40)));
    }

    #[test]
    fn encode_source_round_trip_git() {
        let s = LockedSource::Git {
            url: "https://example.invalid/x/y".to_string(),
            rev: "a".repeat(40),
        };
        assert_eq!(encode_source(&s), "git+https://example.invalid/x/y");
    }

    #[test]
    fn encode_source_round_trip_path() {
        let s = LockedSource::Path {
            path: PathBuf::from("../mylib"),
        };
        assert_eq!(encode_source(&s), "path+../mylib");
    }
}
