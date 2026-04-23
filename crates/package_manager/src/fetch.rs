use std::ffi::OsStr;
use std::fmt;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output};

use crate::cache::CacheDir;
use crate::manifest::{GitRef, Manifest, ManifestError};

/// The result of fetching a git dependency: the resolved 40-char commit SHA,
/// the on-disk source tree at that SHA, and the parsed `krypton.toml`.
#[derive(Debug)]
pub struct FetchedGitDep {
    pub sha: String,
    pub source_dir: PathBuf,
    pub manifest: Manifest,
}

#[derive(Debug)]
pub enum FetchError {
    /// `git` was not found on `PATH` when spawning a subprocess.
    GitNotFound,
    /// A `git` invocation exited with a non-zero status.
    GitCommand {
        args: Vec<String>,
        status: ExitStatus,
        stderr: String,
    },
    /// A filesystem operation against `path` failed.
    Io { path: PathBuf, source: io::Error },
    /// The cloned repository did not contain a `krypton.toml` at its root.
    MissingManifest { dep_key: String, url: String },
    /// The cloned repository's `krypton.toml` failed to parse.
    InvalidManifest {
        dep_key: String,
        url: String,
        source: ManifestError,
    },
    /// The requested ref could not be resolved to a commit in the clone.
    RefResolutionFailed {
        dep_key: String,
        url: String,
        git_ref: GitRef,
        stderr: String,
    },
}

impl fmt::Display for FetchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FetchError::GitNotFound => {
                write!(
                    f,
                    "git is required for git dependencies but was not found"
                )
            }
            FetchError::GitCommand {
                args,
                status,
                stderr,
            } => {
                write!(
                    f,
                    "git {} failed with {}: {}",
                    args.join(" "),
                    status,
                    stderr.trim_end()
                )
            }
            FetchError::Io { path, source } => {
                write!(f, "I/O error at {}: {source}", path.display())
            }
            FetchError::MissingManifest { dep_key, url } => {
                write!(
                    f,
                    "dependency '{dep_key}' (git: {url}) has no krypton.toml"
                )
            }
            FetchError::InvalidManifest {
                dep_key,
                url,
                source,
            } => {
                write!(
                    f,
                    "dependency '{dep_key}' (git: {url}) has an invalid krypton.toml: {source}"
                )
            }
            FetchError::RefResolutionFailed {
                dep_key,
                url,
                git_ref,
                stderr,
            } => {
                write!(
                    f,
                    "dependency '{dep_key}' (git: {url}) could not resolve {}: {}",
                    format_git_ref(git_ref),
                    stderr.trim_end()
                )
            }
        }
    }
}

impl std::error::Error for FetchError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            FetchError::Io { source, .. } => Some(source),
            FetchError::InvalidManifest { source, .. } => Some(source),
            _ => None,
        }
    }
}

fn format_git_ref(r: &GitRef) -> String {
    match r {
        GitRef::Tag(t) => format!("tag '{t}'"),
        GitRef::Rev(r) => format!("rev '{r}'"),
        GitRef::Branch(b) => format!("branch '{b}'"),
    }
}

/// Fetch a git dependency: clone (or reuse) the remote, resolve `git_ref` to a
/// commit SHA, materialize the source tree at that SHA under the cache, parse
/// the dependency's `krypton.toml`, and return the triple.
///
/// A second call with a SHA whose source already exists under
/// `<cache>/packages/<owner>/<name>/<sha>/` short-circuits without invoking
/// `git` at all (cache hit detected purely by filesystem).
pub fn fetch_git(
    cache: &CacheDir,
    dep_key: &str,
    owner: &str,
    name: &str,
    url: &str,
    git_ref: &GitRef,
) -> Result<FetchedGitDep, FetchError> {
    // Pre-fetch cache hit: when the caller already supplies a full-form
    // 40-char SHA (the lockfile-driven case), the SHA-keyed source directory
    // is sufficient to answer without spawning `git` at all.
    if let GitRef::Rev(rev) = git_ref {
        if is_full_sha(rev) {
            let sha_dir = cache.package_source_dir(owner, name, rev);
            let manifest_path = sha_dir.join("krypton.toml");
            if manifest_path.exists() {
                let manifest = load_manifest(&manifest_path, dep_key, url)?;
                return Ok(FetchedGitDep {
                    sha: rev.clone(),
                    source_dir: sha_dir,
                    manifest,
                });
            }
        }
    }

    let clone_dir = cache.git_clone_dir(owner, name);

    ensure_persistent_clone(&clone_dir, url)?;

    let sha = resolve_ref(&clone_dir, dep_key, url, git_ref)?;

    let sha_dir = cache.package_source_dir(owner, name, &sha);
    let manifest_path = sha_dir.join("krypton.toml");

    if !manifest_path.exists() {
        extract_sha(&clone_dir, &sha_dir, &sha)?;
    }

    let manifest = load_manifest(&manifest_path, dep_key, url)?;

    Ok(FetchedGitDep {
        sha,
        source_dir: sha_dir,
        manifest,
    })
}

fn is_full_sha(s: &str) -> bool {
    s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

fn ensure_persistent_clone(clone_dir: &Path, url: &str) -> Result<(), FetchError> {
    if clone_dir.join(".git").join("HEAD").exists() {
        run_git(
            &["fetch", "--tags", "--prune", "origin"],
            Some(clone_dir),
        )?;
        return Ok(());
    }

    if let Some(parent) = clone_dir.parent() {
        create_dir_all(parent)?;
    }

    run_git(&["clone", url, path_to_str(clone_dir)?], None)?;
    Ok(())
}

fn resolve_ref(
    clone_dir: &Path,
    dep_key: &str,
    url: &str,
    git_ref: &GitRef,
) -> Result<String, FetchError> {
    let rev_expr = match git_ref {
        GitRef::Tag(t) => format!("refs/tags/{t}"),
        GitRef::Branch(b) => format!("refs/remotes/origin/{b}"),
        GitRef::Rev(r) => r.clone(),
    };
    let with_commit = format!("{rev_expr}^{{commit}}");

    let result = run_git(
        &["rev-parse", "--verify", &with_commit],
        Some(clone_dir),
    );
    match result {
        Ok(output) => {
            let sha = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if sha.is_empty() {
                return Err(FetchError::RefResolutionFailed {
                    dep_key: dep_key.to_string(),
                    url: url.to_string(),
                    git_ref: git_ref.clone(),
                    stderr: "empty rev-parse output".to_string(),
                });
            }
            Ok(sha)
        }
        Err(FetchError::GitCommand { stderr, .. }) => Err(FetchError::RefResolutionFailed {
            dep_key: dep_key.to_string(),
            url: url.to_string(),
            git_ref: git_ref.clone(),
            stderr,
        }),
        Err(other) => Err(other),
    }
}

fn extract_sha(clone_dir: &Path, sha_dir: &Path, sha: &str) -> Result<(), FetchError> {
    if let Some(parent) = sha_dir.parent() {
        create_dir_all(parent)?;
    }
    // Remove any partial leftover directory so `git clone` can create the
    // target fresh. `git clone` requires the destination not to exist.
    if sha_dir.exists() {
        remove_dir_all(sha_dir)?;
    }

    run_git(
        &[
            "clone",
            "--shared",
            "--no-checkout",
            path_to_str(clone_dir)?,
            path_to_str(sha_dir)?,
        ],
        None,
    )?;
    run_git(&["checkout", "--detach", sha], Some(sha_dir))?;
    Ok(())
}

fn load_manifest(
    manifest_path: &Path,
    dep_key: &str,
    url: &str,
) -> Result<Manifest, FetchError> {
    if !manifest_path.exists() {
        return Err(FetchError::MissingManifest {
            dep_key: dep_key.to_string(),
            url: url.to_string(),
        });
    }
    let src = std::fs::read_to_string(manifest_path).map_err(|e| FetchError::Io {
        path: manifest_path.to_path_buf(),
        source: e,
    })?;
    Manifest::from_str(&src).map_err(|source| FetchError::InvalidManifest {
        dep_key: dep_key.to_string(),
        url: url.to_string(),
        source,
    })
}

fn run_git(args: &[&str], cwd: Option<&Path>) -> Result<Output, FetchError> {
    let mut cmd = Command::new("git");
    if let Some(dir) = cwd {
        cmd.arg("-C").arg(dir);
    }
    for a in args {
        cmd.arg(OsStr::new(a));
    }

    let output = cmd.output().map_err(|e| {
        if e.kind() == io::ErrorKind::NotFound {
            FetchError::GitNotFound
        } else {
            FetchError::Io {
                path: PathBuf::from("git"),
                source: e,
            }
        }
    })?;

    if !output.status.success() {
        let mut display_args = Vec::with_capacity(args.len() + 2);
        if let Some(dir) = cwd {
            display_args.push("-C".to_string());
            display_args.push(dir.display().to_string());
        }
        for a in args {
            display_args.push((*a).to_string());
        }
        return Err(FetchError::GitCommand {
            args: display_args,
            status: output.status,
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
        });
    }

    Ok(output)
}

fn create_dir_all(path: &Path) -> Result<(), FetchError> {
    std::fs::create_dir_all(path).map_err(|e| FetchError::Io {
        path: path.to_path_buf(),
        source: e,
    })
}

fn remove_dir_all(path: &Path) -> Result<(), FetchError> {
    std::fs::remove_dir_all(path).map_err(|e| FetchError::Io {
        path: path.to_path_buf(),
        source: e,
    })
}

fn path_to_str(path: &Path) -> Result<&str, FetchError> {
    path.to_str().ok_or_else(|| FetchError::Io {
        path: path.to_path_buf(),
        source: io::Error::new(
            io::ErrorKind::InvalidInput,
            "path is not valid UTF-8",
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn git_not_found_error_message() {
        let err = FetchError::GitNotFound;
        assert_eq!(
            err.to_string(),
            "git is required for git dependencies but was not found"
        );
    }

    #[test]
    fn missing_manifest_error_format() {
        let err = FetchError::MissingManifest {
            dep_key: "clementine/http".to_string(),
            url: "https://example.invalid/clementine/http".to_string(),
        };
        assert_eq!(
            err.to_string(),
            "dependency 'clementine/http' (git: https://example.invalid/clementine/http) has no krypton.toml"
        );
    }
}
