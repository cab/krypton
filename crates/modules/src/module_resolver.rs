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

/// Composite resolver: tries stdlib first (for core/* paths), then filesystem.
pub struct CompositeResolver {
    pub stdlib: StdlibResolver,
    pub filesystem: Option<FileSystemResolver>,
}

impl CompositeResolver {
    pub fn stdlib_only() -> Self {
        Self {
            stdlib: StdlibResolver,
            filesystem: None,
        }
    }

    pub fn with_source_root(source_root: PathBuf) -> Self {
        Self {
            stdlib: StdlibResolver,
            filesystem: Some(FileSystemResolver { source_root }),
        }
    }
}

impl ModuleResolver for CompositeResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        // Try stdlib first
        if let Some(source) = self.stdlib.resolve(module_path) {
            return Some(source);
        }
        // Then filesystem
        if let Some(ref fs) = self.filesystem {
            return fs.resolve(module_path);
        }
        None
    }
}
