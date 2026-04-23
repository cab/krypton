use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::manifest::{Manifest, ManifestError};

const DEFAULT_MAIN_KR: &str = "fun main() = println(\"hello world\")\n";
const DEFAULT_GITIGNORE: &str = "target/\n";

#[derive(Debug)]
pub enum InitError {
    InvalidName(ManifestError),
    DirectoryExists(PathBuf),
    Io { path: PathBuf, source: io::Error },
}

impl fmt::Display for InitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InitError::InvalidName(e) => write!(f, "invalid package name: {e}"),
            InitError::DirectoryExists(p) => {
                write!(f, "target directory already exists: {}", p.display())
            }
            InitError::Io { path, source } => {
                write!(f, "I/O error at {}: {}", path.display(), source)
            }
        }
    }
}

impl std::error::Error for InitError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            InitError::InvalidName(e) => Some(e),
            InitError::DirectoryExists(_) => None,
            InitError::Io { source, .. } => Some(source),
        }
    }
}

/// Create a new Krypton project at `parent_dir/<name-part>/`.
///
/// `package_name` is an `owner/name` identifier; the directory name is the
/// segment after `/`. The generated `krypton.toml` is validated by round-tripping
/// through [`Manifest::from_str`] before any filesystem writes occur.
pub fn init_project(parent_dir: &Path, package_name: &str) -> Result<PathBuf, InitError> {
    let manifest_src = render_manifest(package_name);
    let manifest = Manifest::from_str(&manifest_src).map_err(InitError::InvalidName)?;

    let name_after_slash = manifest
        .package
        .name
        .split('/')
        .nth(1)
        .expect("Manifest::from_str validated owner/name format");
    let target_dir = parent_dir.join(name_after_slash);

    match fs::metadata(&target_dir) {
        Ok(_) => return Err(InitError::DirectoryExists(target_dir)),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(InitError::Io {
                path: target_dir,
                source: e,
            });
        }
    }

    let src_dir = target_dir.join("src");
    fs::create_dir_all(&src_dir).map_err(|e| InitError::Io {
        path: src_dir.clone(),
        source: e,
    })?;

    let manifest_path = target_dir.join("krypton.toml");
    fs::write(&manifest_path, &manifest_src).map_err(|e| InitError::Io {
        path: manifest_path,
        source: e,
    })?;

    let main_path = src_dir.join("main.kr");
    fs::write(&main_path, DEFAULT_MAIN_KR).map_err(|e| InitError::Io {
        path: main_path,
        source: e,
    })?;

    let gitignore_path = target_dir.join(".gitignore");
    fs::write(&gitignore_path, DEFAULT_GITIGNORE).map_err(|e| InitError::Io {
        path: gitignore_path,
        source: e,
    })?;

    Ok(target_dir)
}

fn render_manifest(package_name: &str) -> String {
    format!(
        "[package]\nname = \"{package_name}\"\nversion = \"0.1.0\"\n\n[dependencies]\n"
    )
}
