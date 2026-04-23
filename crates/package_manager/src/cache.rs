use std::env;
use std::ffi::OsString;
use std::fmt;
use std::path::{Path, PathBuf};

/// On-disk layout for fetched package sources, compiled artifacts, Maven jars,
/// and auxiliary tools.
///
/// Path-returning methods are pure: they never touch the filesystem. Directories
/// are created only when a caller performs an actual write against the returned
/// path, so constructing or querying a [`CacheDir`] has no observable side effect.
pub struct CacheDir {
    root: PathBuf,
}

#[derive(Debug)]
pub enum CacheError {
    /// Neither `KRYPTON_HOME` nor `HOME` was set in the process environment.
    HomeNotFound,
}

impl fmt::Display for CacheError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CacheError::HomeNotFound => write!(
                f,
                "cannot locate Krypton home: neither KRYPTON_HOME nor HOME is set"
            ),
        }
    }
}

impl std::error::Error for CacheError {}

impl CacheDir {
    /// Resolve the cache root from the process environment.
    ///
    /// Prefers `$KRYPTON_HOME` verbatim; otherwise falls back to
    /// `$HOME/.krypton`. Returns [`CacheError::HomeNotFound`] if neither
    /// variable is set.
    pub fn new() -> Result<Self, CacheError> {
        let root = resolve_root(env::var_os("KRYPTON_HOME"), env::var_os("HOME"))?;
        Ok(Self { root })
    }

    /// Construct a [`CacheDir`] with an explicit root. Primarily for tests and
    /// embedders that want to bypass environment resolution.
    pub fn with_root(root: PathBuf) -> Self {
        Self { root }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// `<root>/cache/packages/<owner>/<name>/<version>/`
    pub fn package_source_dir(&self, owner: &str, name: &str, version: &str) -> PathBuf {
        self.root
            .join("cache")
            .join("packages")
            .join(owner)
            .join(name)
            .join(version)
    }

    /// `<root>/cache/git/<owner>/<name>/` — persistent non-bare clone shared
    /// across every ref fetched from the same remote.
    pub fn git_clone_dir(&self, owner: &str, name: &str) -> PathBuf {
        self.root
            .join("cache")
            .join("git")
            .join(owner)
            .join(name)
    }

    /// `<root>/cache/packages/<owner>/<name>/<version>/target/jvm/<compiler_hash>/`
    pub fn package_compiled_dir(
        &self,
        owner: &str,
        name: &str,
        version: &str,
        compiler_hash: &str,
    ) -> PathBuf {
        self.package_source_dir(owner, name, version)
            .join("target")
            .join("jvm")
            .join(compiler_hash)
    }

    /// `<root>/cache/maven/<group-with-slashes>/<artifact>/<version>/<filename>`
    ///
    /// `group_id` uses dots in Maven coordinates (e.g. `org.postgresql`) but the
    /// on-disk layout uses path separators, so segments are split on `.` and
    /// joined via [`PathBuf::push`].
    pub fn maven_jar_path(
        &self,
        group_id: &str,
        artifact: &str,
        version: &str,
        filename: &str,
    ) -> PathBuf {
        let mut path = self.root.join("cache").join("maven");
        for segment in group_id.split('.') {
            path.push(segment);
        }
        path.push(artifact);
        path.push(version);
        path.push(filename);
        path
    }

    /// `<root>/tools/` — sibling of `cache/`, reserved for Coursier and other
    /// auxiliary binaries that should survive a cache wipe.
    pub fn tools_dir(&self) -> PathBuf {
        self.root.join("tools")
    }
}

fn resolve_root(
    krypton_home: Option<OsString>,
    home: Option<OsString>,
) -> Result<PathBuf, CacheError> {
    if let Some(kh) = krypton_home {
        return Ok(PathBuf::from(kh));
    }
    if let Some(h) = home {
        return Ok(PathBuf::from(h).join(".krypton"));
    }
    Err(CacheError::HomeNotFound)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_root_prefers_krypton_home() {
        let kh = OsString::from("/custom/krypton");
        let home = OsString::from("/home/user");
        let root = resolve_root(Some(kh), Some(home)).expect("both set");
        assert_eq!(root, PathBuf::from("/custom/krypton"));
    }

    #[test]
    fn resolve_root_falls_back_to_home() {
        let home = OsString::from("/home/user");
        let root = resolve_root(None, Some(home)).expect("home set");
        assert_eq!(root, PathBuf::from("/home/user/.krypton"));
    }

    #[test]
    fn resolve_root_errors_when_neither_set() {
        let err = resolve_root(None, None).expect_err("neither set");
        assert!(matches!(err, CacheError::HomeNotFound));
    }
}
