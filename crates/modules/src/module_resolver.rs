use std::fmt;
use std::path::PathBuf;

use crate::stdlib_loader::StdlibLoader;

/// Trait for resolving module source code by module path.
pub trait ModuleResolver {
    /// Given a module path like "math/vec", return the source code if found.
    fn resolve(&self, module_path: &str) -> Option<String>;
}

/// Resolves modules from the filesystem relative to a source root.
pub struct FileSystemResolver {
    pub source_root: PathBuf,
}

impl ModuleResolver for FileSystemResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        let file_path = self.source_root.join(format!("{}.kr", module_path));
        std::fs::read_to_string(&file_path).ok()
    }
}

/// Resolves modules from the embedded stdlib.
pub struct StdlibResolver;

impl ModuleResolver for StdlibResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        StdlibLoader::get_source(module_path).map(|s| s.to_string())
    }
}

/// Resolves modules by mapping an import-root prefix to an external `src/`
/// directory. Given `import http/client.{get}`, strips the `http` head
/// segment, looks up `http` in the registered roots, and reads
/// `<src_dir>/client.kr`. A bare `import http` reads `<src_dir>/lib.kr`.
///
/// When a name appears more than once in `roots`, the first entry wins. In
/// practice the TOML-driven construction path deduplicates before reaching
/// here, but the type stays total so callers aren't forced to validate.
pub struct DependencyResolver {
    roots: Vec<(String, PathBuf)>,
}

impl DependencyResolver {
    pub fn new(roots: Vec<(String, PathBuf)>) -> Self {
        Self { roots }
    }

    pub fn is_empty(&self) -> bool {
        self.roots.is_empty()
    }
}

impl ModuleResolver for DependencyResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        let (head, rest) = match module_path.split_once('/') {
            Some((h, r)) => (h, Some(r)),
            None => (module_path, None),
        };
        for (name, src_dir) in &self.roots {
            if name == head {
                let file_path = match rest {
                    Some(r) => src_dir.join(format!("{r}.kr")),
                    None => src_dir.join("lib.kr"),
                };
                return std::fs::read_to_string(&file_path).ok();
            }
        }
        None
    }
}

/// Errors produced when constructing a [`CompositeResolver`].
#[derive(Debug)]
pub enum ResolverError {
    /// A dependency import-root name collides with a local module under the
    /// project source root. `local_path` is the offending `<src>/<name>.kr`
    /// file or `<src>/<name>/` directory.
    ImportRootConflict { name: String, local_path: PathBuf },
}

impl fmt::Display for ResolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ResolverError::ImportRootConflict { name, local_path } => {
                let kind = if local_path.is_dir() { "/" } else { "" };
                write!(
                    f,
                    "import root '{name}' conflicts with local module '{}{kind}'",
                    local_path.display()
                )
            }
        }
    }
}

impl std::error::Error for ResolverError {}

/// Composite resolver: stdlib → project `src/` → dependencies. Within a tier,
/// the first match wins; tiers are strictly ordered (stdlib always beats
/// project, project always beats deps).
pub struct CompositeResolver {
    pub stdlib: StdlibResolver,
    pub filesystem: Option<FileSystemResolver>,
    pub dependencies: DependencyResolver,
}

impl CompositeResolver {
    pub fn stdlib_only() -> Self {
        Self::new(None, Vec::new()).expect("no deps cannot conflict")
    }

    pub fn with_source_root(source_root: PathBuf) -> Self {
        Self::new(Some(source_root), Vec::new()).expect("no deps cannot conflict")
    }

    /// Full constructor. `source_root` is the project `src/` directory when
    /// compiling a project; `None` for stdlib-only callers (REPL single-file
    /// paths). `deps` pairs each import-root name (the TOML `[dependencies]`
    /// key) with the dep's `src/` directory.
    ///
    /// Returns [`ResolverError::ImportRootConflict`] if any `deps` name
    /// collides with a local `<source_root>/<name>.kr` file or
    /// `<source_root>/<name>/` directory.
    pub fn new(
        source_root: Option<PathBuf>,
        deps: Vec<(String, PathBuf)>,
    ) -> Result<Self, ResolverError> {
        if let Some(ref root) = source_root {
            for (name, _) in &deps {
                let file = root.join(format!("{name}.kr"));
                if file.exists() {
                    return Err(ResolverError::ImportRootConflict {
                        name: name.clone(),
                        local_path: file,
                    });
                }
                let dir = root.join(name);
                if dir.is_dir() {
                    return Err(ResolverError::ImportRootConflict {
                        name: name.clone(),
                        local_path: dir,
                    });
                }
            }
        }
        Ok(Self {
            stdlib: StdlibResolver,
            filesystem: source_root.map(|source_root| FileSystemResolver { source_root }),
            dependencies: DependencyResolver::new(deps),
        })
    }
}

impl ModuleResolver for CompositeResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        if let Some(source) = self.stdlib.resolve(module_path) {
            return Some(source);
        }
        if let Some(ref fs) = self.filesystem {
            if let Some(source) = fs.resolve(module_path) {
                return Some(source);
            }
        }
        self.dependencies.resolve(module_path)
    }
}
