// The error type carries diagnostic context (canonical names, two source
// descriptors, derivation-tree renderings) that we intentionally keep
// structured rather than stringly-typed. The `Ok` side is a heap-allocated
// `ResolvedGraph`, so the Result stays copy-light in practice.
#![allow(clippy::result_large_err)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

use pubgrub::{
    DefaultStringReporter, Dependencies, DependencyProvider, PackageResolutionStatistics,
    PubGrubError, Ranges, Reporter,
};
use semver::{BuildMetadata, Comparator, Op, Prerelease, Version};

use crate::cache::CacheDir;
use crate::fetch::{FetchError, FetchedGitDep, fetch_git};
use crate::manifest::{DepSpec, GitRef, Manifest, ManifestError};
use crate::version::{VersionReq, VersionReqError};

/// Canonical `owner/name` identity for a package. Constructed from a string
/// that has already been validated at manifest-parse time, so the `/`
/// separator and non-empty segments are invariants — accessors rely on this.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CanonicalName(String);

impl CanonicalName {
    /// Construct from a string whose shape was already validated by
    /// `manifest::validate_owner_name`. Callers outside this crate acquire
    /// canonical names from a parsed [`Manifest`] or [`ResolvedGraph`].
    pub(crate) fn from_validated(s: &str) -> Self {
        Self(s.to_string())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn owner(&self) -> &str {
        self.0
            .split('/')
            .next()
            .expect("canonical name has a '/' separator")
    }

    pub fn name(&self) -> &str {
        self.0
            .split('/')
            .nth(1)
            .expect("canonical name has exactly two '/'-separated segments")
    }
}

impl fmt::Display for CanonicalName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// The source a resolved package was materialized from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceType {
    Git {
        url: String,
        reference: GitRef,
        sha: String,
    },
    Path {
        path: PathBuf,
    },
}

#[derive(Debug, Clone)]
pub struct ResolvedPackage {
    pub canonical: CanonicalName,
    pub version: Version,
    pub source_path: PathBuf,
    pub manifest: Manifest,
    pub source_type: SourceType,
}

#[derive(Debug, Clone)]
pub struct ResolvedGraph {
    packages: BTreeMap<CanonicalName, ResolvedPackage>,
}

impl ResolvedGraph {
    /// Construct a graph directly from a prebuilt package map. Used by the
    /// lockfile rehydration path — ordinary graphs come back from [`resolve`].
    pub fn from_packages(packages: BTreeMap<CanonicalName, ResolvedPackage>) -> Self {
        Self { packages }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&CanonicalName, &ResolvedPackage)> {
        self.packages.iter()
    }

    pub fn get(&self, canonical: &CanonicalName) -> Option<&ResolvedPackage> {
        self.packages.get(canonical)
    }

    pub fn len(&self) -> usize {
        self.packages.len()
    }

    pub fn is_empty(&self) -> bool {
        self.packages.is_empty()
    }

    /// For each `[dependencies]` entry in `manifest`, map the local import
    /// root (the TOML key) to the resolved package's `src/` directory. Dev
    /// dependencies are intentionally omitted. Entries whose canonical name
    /// is not in the resolved graph are skipped — a post-`resolve()` graph
    /// contains every non-root dep, but skipping keeps the API total for
    /// graphs built by other means (e.g. lockfile rehydration).
    pub fn source_roots(&self, manifest: &Manifest) -> Vec<(String, PathBuf)> {
        let mut out = Vec::with_capacity(manifest.dependencies.len());
        for (dep_key, spec) in &manifest.dependencies {
            let canonical_str = dep_spec_canonical(spec);
            let canonical = CanonicalName::from_validated(canonical_str);
            if let Some(pkg) = self.packages.get(&canonical) {
                out.push((dep_key.clone(), pkg.source_path.join("src")));
            }
        }
        out
    }

    /// Hints used to distinguish "unknown module" from "module belongs to a
    /// transitive dep that isn't in your [dependencies]". Returns
    /// `(default_local_root_name, canonical)` for every package in the
    /// resolved graph that is not a direct dependency of `manifest`. The
    /// default local root is the package-name leaf with `-` normalized to
    /// `_` — the same derivation that `krypton add` uses when picking a
    /// default `[dependencies]` key.
    pub fn transitive_hints(&self, manifest: &Manifest) -> Vec<(String, String)> {
        let direct: std::collections::HashSet<&str> = manifest
            .dependencies
            .values()
            .map(dep_spec_canonical)
            .collect();

        let mut out = Vec::new();
        for (canonical, _) in self.packages.iter() {
            if direct.contains(canonical.as_str()) {
                continue;
            }
            let local_root = default_local_root_name(canonical.name());
            out.push((local_root, canonical.as_str().to_string()));
        }
        out
    }
}

fn dep_spec_canonical(spec: &DepSpec) -> &str {
    match spec {
        DepSpec::Git { package, .. }
        | DepSpec::Path { package, .. }
        | DepSpec::Version { package, .. } => package.as_str(),
    }
}

fn default_local_root_name(name_leaf: &str) -> String {
    name_leaf.replace('-', "_")
}

/// Lightweight description of a dependency's source, used both for cache keys
/// inside the resolver and for diagnostics on
/// [`ResolveError::SourceMismatch`]. `Path` sources are canonicalized so two
/// different relative paths that point to the same directory compare equal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceDescriptor {
    Git { url: String, reference: GitRef },
    Path { path: PathBuf },
}

impl fmt::Display for SourceDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceDescriptor::Git { url, reference } => match reference {
                GitRef::Tag(t) => write!(f, "git '{url}' (tag '{t}')"),
                GitRef::Rev(r) => write!(f, "git '{url}' (rev '{r}')"),
                GitRef::Branch(b) => write!(f, "git '{url}' (branch '{b}')"),
            },
            SourceDescriptor::Path { path } => {
                write!(f, "path '{}'", path.display())
            }
        }
    }
}

#[derive(Debug)]
pub enum ResolveError {
    Fetch(FetchError),
    Manifest {
        path: PathBuf,
        source: ManifestError,
    },
    Io {
        path: PathBuf,
        source: std::io::Error,
    },
    InvalidVersionReq {
        canonical: CanonicalName,
        requester: CanonicalName,
        source: VersionReqError,
    },
    SourceMismatch {
        canonical: CanonicalName,
        first: SourceDescriptor,
        second: SourceDescriptor,
    },
    RegistryUnsupported {
        canonical: CanonicalName,
    },
    Cycle {
        chain: Vec<CanonicalName>,
    },
    Unsatisfiable {
        rendered: String,
    },
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ResolveError::Fetch(e) => write!(f, "{e}"),
            ResolveError::Manifest { path, source } => {
                write!(
                    f,
                    "failed to parse manifest at '{}': {source}",
                    path.display()
                )
            }
            ResolveError::Io { path, source } => {
                write!(f, "I/O error at '{}': {source}", path.display())
            }
            ResolveError::InvalidVersionReq {
                canonical,
                requester,
                source,
            } => {
                write!(
                    f,
                    "invalid version requirement on '{canonical}' (required by '{requester}'): {source}"
                )
            }
            ResolveError::SourceMismatch {
                canonical,
                first,
                second,
            } => {
                write!(
                    f,
                    "package '{canonical}' is requested from two different sources: \
                     first {first}, then {second}"
                )
            }
            ResolveError::RegistryUnsupported { canonical } => {
                write!(
                    f,
                    "package '{canonical}' uses a registry `version = ...` dependency, \
                     but the Krypton package registry is not yet available; use `git` or `path`"
                )
            }
            ResolveError::Cycle { chain } => {
                let rendered: Vec<String> = chain.iter().map(ToString::to_string).collect();
                write!(f, "dependency cycle: {}", rendered.join(" -> "))
            }
            ResolveError::Unsatisfiable { rendered } => {
                write!(f, "dependency resolution failed:\n{rendered}")
            }
        }
    }
}

impl std::error::Error for ResolveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            ResolveError::Fetch(e) => Some(e),
            ResolveError::Manifest { source, .. } => Some(source),
            ResolveError::Io { source, .. } => Some(source),
            ResolveError::InvalidVersionReq { source, .. } => Some(source),
            _ => None,
        }
    }
}

impl From<FetchError> for ResolveError {
    fn from(e: FetchError) -> Self {
        ResolveError::Fetch(e)
    }
}

/// A source that has been fetched (for git) or simply located on disk (for
/// path) and parsed. Memoized by the provider so each canonical package is
/// materialized at most once per resolution.
struct FetchedSource {
    manifest: Manifest,
    source_dir: PathBuf,
    source_type: SourceType,
}

/// PubGrub [`DependencyProvider`] backed by Krypton manifests. Sources are
/// fetched lazily from `get_dependencies`, then reused by `choose_version`.
struct KryptonProvider<'a> {
    root_canonical: CanonicalName,
    cache: &'a CacheDir,
    sources: RefCell<BTreeMap<CanonicalName, FetchedSource>>,
    first_source: RefCell<BTreeMap<CanonicalName, SourceDescriptor>>,
}

impl<'a> KryptonProvider<'a> {
    fn new(root_canonical: CanonicalName, cache: &'a CacheDir) -> Self {
        Self {
            root_canonical,
            cache,
            sources: RefCell::new(BTreeMap::new()),
            first_source: RefCell::new(BTreeMap::new()),
        }
    }

    fn register_root(&self, root_dir: &Path, root_manifest: Manifest) {
        let canonical = self.root_canonical.clone();
        let abs = canonicalize_path(root_dir);
        self.sources.borrow_mut().insert(
            canonical.clone(),
            FetchedSource {
                manifest: root_manifest,
                source_dir: abs.clone(),
                source_type: SourceType::Path { path: abs.clone() },
            },
        );
        self.first_source
            .borrow_mut()
            .insert(canonical, SourceDescriptor::Path { path: abs });
    }

    /// Materialize the source for `canonical` if not yet present.
    fn ensure_source(
        &self,
        canonical: &CanonicalName,
        descriptor: &SourceDescriptor,
        dep_key: &str,
    ) -> Result<(), ResolveError> {
        if self.sources.borrow().contains_key(canonical) {
            return Ok(());
        }
        let fetched = match descriptor {
            SourceDescriptor::Git { url, reference } => {
                let FetchedGitDep {
                    sha,
                    source_dir,
                    manifest,
                } = fetch_git(
                    self.cache,
                    dep_key,
                    canonical.owner(),
                    canonical.name(),
                    url,
                    reference,
                )?;
                FetchedSource {
                    manifest,
                    source_dir,
                    source_type: SourceType::Git {
                        url: url.clone(),
                        reference: reference.clone(),
                        sha,
                    },
                }
            }
            SourceDescriptor::Path { path } => {
                let manifest_path = path.join("krypton.toml");
                let manifest = Manifest::from_path(&manifest_path).map_err(|source| {
                    ResolveError::Manifest {
                        path: manifest_path.clone(),
                        source,
                    }
                })?;
                FetchedSource {
                    manifest,
                    source_dir: path.clone(),
                    source_type: SourceType::Path { path: path.clone() },
                }
            }
        };
        self.sources.borrow_mut().insert(canonical.clone(), fetched);
        Ok(())
    }
}

impl<'a> DependencyProvider for KryptonProvider<'a> {
    type P = CanonicalName;
    type V = Version;
    type VS = Ranges<Version>;
    type M = String;
    type Err = ResolveError;
    type Priority = (i64, u32);

    fn prioritize(
        &self,
        _package: &CanonicalName,
        range: &Ranges<Version>,
        stats: &PackageResolutionStatistics,
    ) -> Self::Priority {
        // Decide narrower ranges (fewer segments) first so we fail fast on
        // conflicts. Ties break on conflict count (packages involved in more
        // conflicts are decided earlier to prune the search tree).
        let segments = range.iter().count() as i64;
        (-segments, stats.conflict_count())
    }

    fn choose_version(
        &self,
        package: &CanonicalName,
        range: &Ranges<Version>,
    ) -> Result<Option<Version>, ResolveError> {
        let sources = self.sources.borrow();
        let Some(src) = sources.get(package) else {
            // PubGrub asked about a package we never registered. Emit `None` so
            // the solver records a `NoVersions` incompatibility rather than
            // panicking; practically this shouldn't fire because we always
            // register before emitting deps.
            return Ok(None);
        };
        let v = src.manifest.package.version.clone();
        if range.contains(&v) {
            Ok(Some(v))
        } else {
            Ok(None)
        }
    }

    fn get_dependencies(
        &self,
        package: &CanonicalName,
        version: &Version,
    ) -> Result<Dependencies<CanonicalName, Ranges<Version>, String>, ResolveError> {
        let (manifest, source_dir) = {
            let sources = self.sources.borrow();
            let Some(src) = sources.get(package) else {
                return Ok(Dependencies::Unavailable(format!(
                    "no source materialized for '{package}'"
                )));
            };
            if &src.manifest.package.version != version {
                // This only fires on a genuine single-version conflict because
                // each source yields one `package.version`.
                return Ok(Dependencies::Unavailable(format!(
                    "'{package}' provides version {} but {version} was requested",
                    src.manifest.package.version
                )));
            }
            (src.manifest.clone(), src.source_dir.clone())
        };

        let mut constraints: Vec<(CanonicalName, Ranges<Version>)> = Vec::new();
        for (dep_key, dep_spec) in &manifest.dependencies {
            let (canonical, descriptor, range) = self.lower_dep(package, dep_spec, &source_dir)?;

            {
                let mut first = self.first_source.borrow_mut();
                if let Some(existing) = first.get(&canonical) {
                    if existing != &descriptor {
                        return Err(ResolveError::SourceMismatch {
                            canonical: canonical.clone(),
                            first: existing.clone(),
                            second: descriptor.clone(),
                        });
                    }
                } else {
                    first.insert(canonical.clone(), descriptor.clone());
                }
            }

            self.ensure_source(&canonical, &descriptor, dep_key)?;
            constraints.push((canonical, range));
        }

        Ok(Dependencies::Available(constraints.into_iter().collect()))
    }
}

impl<'a> KryptonProvider<'a> {
    /// Lower a single manifest [`DepSpec`] into the tuple pubgrub consumes:
    /// canonical identity, concrete source (for fetch + mismatch detection),
    /// and a version range.
    fn lower_dep(
        &self,
        requester: &CanonicalName,
        dep_spec: &DepSpec,
        requester_dir: &Path,
    ) -> Result<(CanonicalName, SourceDescriptor, Ranges<Version>), ResolveError> {
        match dep_spec {
            DepSpec::Git {
                package,
                url,
                reference,
            } => {
                let canonical = CanonicalName::from_validated(package);
                let descriptor = SourceDescriptor::Git {
                    url: url.clone(),
                    reference: reference.clone(),
                };
                // Git refs pin to a single SHA, which pins the version — no
                // additional range is expressible at the dep site.
                Ok((canonical, descriptor, Ranges::full()))
            }
            DepSpec::Path {
                package,
                path,
                version,
            } => {
                let canonical = CanonicalName::from_validated(package);
                let abs = if path.is_absolute() {
                    path.clone()
                } else {
                    requester_dir.join(path)
                };
                let descriptor = SourceDescriptor::Path {
                    path: canonicalize_path(&abs),
                };
                let range = match version {
                    Some(req_str) => {
                        let req = VersionReq::parse(req_str).map_err(|source| {
                            ResolveError::InvalidVersionReq {
                                canonical: canonical.clone(),
                                requester: requester.clone(),
                                source,
                            }
                        })?;
                        req_to_ranges(&req)
                    }
                    None => Ranges::full(),
                };
                Ok((canonical, descriptor, range))
            }
            DepSpec::Version { package, .. } => {
                let canonical = CanonicalName::from_validated(package);
                Err(ResolveError::RegistryUnsupported { canonical })
            }
        }
    }
}

/// Resolve the full dependency graph rooted at `root_manifest`.
///
/// The result excludes the root itself and contains every transitive
/// dependency mapped to exactly one version (v0.1 invariant: one version per
/// canonical `owner/name`).
pub fn resolve(
    root_dir: &Path,
    root_manifest: Manifest,
    cache: &CacheDir,
) -> Result<ResolvedGraph, ResolveError> {
    let root_canonical = CanonicalName::from_validated(&root_manifest.package.name);
    let root_version = root_manifest.package.version.clone();

    let provider = KryptonProvider::new(root_canonical.clone(), cache);
    provider.register_root(root_dir, root_manifest);

    let selected = match pubgrub::resolve(&provider, root_canonical.clone(), root_version) {
        Ok(s) => s,
        Err(PubGrubError::NoSolution(mut tree)) => {
            tree.collapse_no_versions();
            let rendered = DefaultStringReporter::report(&tree);
            return Err(ResolveError::Unsatisfiable { rendered });
        }
        Err(PubGrubError::ErrorRetrievingDependencies { source, .. }) => return Err(source),
        Err(PubGrubError::ErrorChoosingVersion { source, .. }) => return Err(source),
        Err(PubGrubError::ErrorInShouldCancel(source)) => return Err(source),
    };

    let sources = provider.sources.into_inner();
    let mut packages: BTreeMap<CanonicalName, ResolvedPackage> = BTreeMap::new();
    for (canonical, version) in selected.iter() {
        if canonical == &root_canonical {
            continue;
        }
        let src = sources
            .get(canonical)
            .expect("every resolved package was registered during resolution");
        packages.insert(
            canonical.clone(),
            ResolvedPackage {
                canonical: canonical.clone(),
                version: version.clone(),
                source_path: src.source_dir.clone(),
                manifest: src.manifest.clone(),
                source_type: src.source_type.clone(),
            },
        );
    }
    Ok(ResolvedGraph { packages })
}

fn canonicalize_path(p: &Path) -> PathBuf {
    std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf())
}

/// Lower a parsed [`VersionReq`] into a pubgrub [`Ranges`]. The set of
/// comparators in a `VersionReq` is combined with AND semantics, so we
/// intersect them.
fn req_to_ranges(req: &VersionReq) -> Ranges<Version> {
    req.comparators()
        .iter()
        .map(comparator_to_ranges)
        .fold(Ranges::full(), |acc, r| acc.intersection(&r))
}

fn comparator_to_ranges(c: &Comparator) -> Ranges<Version> {
    let major = c.major;
    let minor = c.minor;
    let patch = c.patch;
    let pre = c.pre.clone();
    match c.op {
        Op::Exact => exact_ranges(major, minor, patch, pre),
        Op::Greater => greater_ranges(major, minor, patch, pre),
        Op::GreaterEq => greater_eq_ranges(major, minor, patch, pre),
        Op::Less => less_ranges(major, minor, patch, pre),
        Op::LessEq => less_eq_ranges(major, minor, patch, pre),
        Op::Tilde => tilde_ranges(major, minor, patch, pre),
        Op::Caret => caret_ranges(major, minor, patch, pre),
        Op::Wildcard => wildcard_ranges(major, minor),
        _ => Ranges::full(),
    }
}

fn make_version(major: u64, minor: u64, patch: u64, pre: Prerelease) -> Version {
    Version {
        major,
        minor,
        patch,
        pre,
        build: BuildMetadata::EMPTY,
    }
}

fn exact_ranges(
    major: u64,
    minor: Option<u64>,
    patch: Option<u64>,
    pre: Prerelease,
) -> Ranges<Version> {
    match (minor, patch) {
        (Some(b), Some(c)) => Ranges::singleton(make_version(major, b, c, pre)),
        (Some(b), None) => Ranges::between(
            make_version(major, b, 0, Prerelease::EMPTY),
            make_version(major, b + 1, 0, Prerelease::EMPTY),
        ),
        (None, _) => Ranges::between(
            make_version(major, 0, 0, Prerelease::EMPTY),
            make_version(major + 1, 0, 0, Prerelease::EMPTY),
        ),
    }
}

fn greater_ranges(
    major: u64,
    minor: Option<u64>,
    patch: Option<u64>,
    pre: Prerelease,
) -> Ranges<Version> {
    match (minor, patch) {
        (Some(b), Some(c)) => Ranges::strictly_higher_than(make_version(major, b, c, pre)),
        (Some(b), None) => Ranges::higher_than(make_version(major, b + 1, 0, Prerelease::EMPTY)),
        (None, _) => Ranges::higher_than(make_version(major + 1, 0, 0, Prerelease::EMPTY)),
    }
}

fn greater_eq_ranges(
    major: u64,
    minor: Option<u64>,
    patch: Option<u64>,
    pre: Prerelease,
) -> Ranges<Version> {
    match (minor, patch) {
        (Some(b), Some(c)) => Ranges::higher_than(make_version(major, b, c, pre)),
        (Some(b), None) => Ranges::higher_than(make_version(major, b, 0, Prerelease::EMPTY)),
        (None, _) => Ranges::higher_than(make_version(major, 0, 0, Prerelease::EMPTY)),
    }
}

fn less_ranges(
    major: u64,
    minor: Option<u64>,
    patch: Option<u64>,
    pre: Prerelease,
) -> Ranges<Version> {
    match (minor, patch) {
        (Some(b), Some(c)) => Ranges::strictly_lower_than(make_version(major, b, c, pre)),
        (Some(b), None) => {
            Ranges::strictly_lower_than(make_version(major, b, 0, Prerelease::EMPTY))
        }
        (None, _) => Ranges::strictly_lower_than(make_version(major, 0, 0, Prerelease::EMPTY)),
    }
}

fn less_eq_ranges(
    major: u64,
    minor: Option<u64>,
    patch: Option<u64>,
    pre: Prerelease,
) -> Ranges<Version> {
    match (minor, patch) {
        (Some(b), Some(c)) => Ranges::lower_than(make_version(major, b, c, pre)),
        (Some(b), None) => {
            Ranges::strictly_lower_than(make_version(major, b + 1, 0, Prerelease::EMPTY))
        }
        (None, _) => Ranges::strictly_lower_than(make_version(major + 1, 0, 0, Prerelease::EMPTY)),
    }
}

fn tilde_ranges(
    major: u64,
    minor: Option<u64>,
    patch: Option<u64>,
    pre: Prerelease,
) -> Ranges<Version> {
    match (minor, patch) {
        (Some(b), Some(c)) => Ranges::between(
            make_version(major, b, c, pre),
            make_version(major, b + 1, 0, Prerelease::EMPTY),
        ),
        (Some(b), None) => Ranges::between(
            make_version(major, b, 0, Prerelease::EMPTY),
            make_version(major, b + 1, 0, Prerelease::EMPTY),
        ),
        (None, _) => Ranges::between(
            make_version(major, 0, 0, Prerelease::EMPTY),
            make_version(major + 1, 0, 0, Prerelease::EMPTY),
        ),
    }
}

fn caret_ranges(
    major: u64,
    minor: Option<u64>,
    patch: Option<u64>,
    pre: Prerelease,
) -> Ranges<Version> {
    // Caret allows changes to parts right of the first non-zero component.
    match (minor, patch) {
        (Some(b), Some(c)) => {
            if major > 0 {
                Ranges::between(
                    make_version(major, b, c, pre),
                    make_version(major + 1, 0, 0, Prerelease::EMPTY),
                )
            } else if b > 0 {
                Ranges::between(
                    make_version(0, b, c, pre),
                    make_version(0, b + 1, 0, Prerelease::EMPTY),
                )
            } else {
                // ^0.0.c → =0.0.c
                Ranges::singleton(make_version(0, 0, c, pre))
            }
        }
        (Some(b), None) => {
            if major > 0 || b > 0 {
                Ranges::between(
                    make_version(major, b, 0, Prerelease::EMPTY),
                    if major > 0 {
                        make_version(major + 1, 0, 0, Prerelease::EMPTY)
                    } else {
                        make_version(0, b + 1, 0, Prerelease::EMPTY)
                    },
                )
            } else {
                // ^0.0 → =0.0
                Ranges::between(
                    make_version(0, 0, 0, Prerelease::EMPTY),
                    make_version(0, 1, 0, Prerelease::EMPTY),
                )
            }
        }
        (None, _) => {
            // ^I → =I
            Ranges::between(
                make_version(major, 0, 0, Prerelease::EMPTY),
                make_version(major + 1, 0, 0, Prerelease::EMPTY),
            )
        }
    }
}

fn wildcard_ranges(major: u64, minor: Option<u64>) -> Ranges<Version> {
    match minor {
        Some(b) => Ranges::between(
            make_version(major, b, 0, Prerelease::EMPTY),
            make_version(major, b + 1, 0, Prerelease::EMPTY),
        ),
        None => Ranges::between(
            make_version(major, 0, 0, Prerelease::EMPTY),
            make_version(major + 1, 0, 0, Prerelease::EMPTY),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Version {
        Version::parse(s).unwrap()
    }

    fn req(s: &str) -> Ranges<Version> {
        req_to_ranges(&VersionReq::parse(s).unwrap())
    }

    #[test]
    fn caret_major_ge_one() {
        let r = req("^1.2.3");
        assert!(r.contains(&v("1.2.3")));
        assert!(r.contains(&v("1.99.0")));
        assert!(!r.contains(&v("2.0.0")));
        assert!(!r.contains(&v("1.2.2")));
    }

    #[test]
    fn caret_zero_minor() {
        let r = req("^0.2.3");
        assert!(r.contains(&v("0.2.3")));
        assert!(r.contains(&v("0.2.99")));
        assert!(!r.contains(&v("0.3.0")));
        assert!(!r.contains(&v("0.2.2")));
    }

    #[test]
    fn caret_zero_zero_patch() {
        let r = req("^0.0.5");
        assert!(r.contains(&v("0.0.5")));
        assert!(!r.contains(&v("0.0.4")));
        assert!(!r.contains(&v("0.0.6")));
    }

    #[test]
    fn tilde_major_minor_patch() {
        let r = req("~1.2.3");
        assert!(r.contains(&v("1.2.3")));
        assert!(r.contains(&v("1.2.99")));
        assert!(!r.contains(&v("1.3.0")));
        assert!(!r.contains(&v("1.2.2")));
    }

    #[test]
    fn tilde_major_minor() {
        let r = req("~1.2");
        assert!(r.contains(&v("1.2.0")));
        assert!(r.contains(&v("1.2.99")));
        assert!(!r.contains(&v("1.3.0")));
    }

    #[test]
    fn exact_pin() {
        let r = req("=1.2.3");
        assert!(r.contains(&v("1.2.3")));
        assert!(!r.contains(&v("1.2.4")));
        assert!(!r.contains(&v("1.2.2")));
    }

    #[test]
    fn compound_req_intersects() {
        let r = req(">=1.0.0, <2.0.0");
        assert!(r.contains(&v("1.0.0")));
        assert!(r.contains(&v("1.99.0")));
        assert!(!r.contains(&v("2.0.0")));
        assert!(!r.contains(&v("0.9.9")));
    }

    #[test]
    fn greater_eq_open_ended() {
        let r = req(">=1.2.3");
        assert!(r.contains(&v("1.2.3")));
        assert!(r.contains(&v("99.0.0")));
        assert!(!r.contains(&v("1.2.2")));
    }

    #[test]
    fn less_eq_inclusive() {
        let r = req("<=1.2.3");
        assert!(r.contains(&v("1.2.3")));
        assert!(r.contains(&v("0.0.1")));
        assert!(!r.contains(&v("1.2.4")));
    }

    #[test]
    fn source_descriptor_display_renders_git_and_path() {
        let git = SourceDescriptor::Git {
            url: "https://example.invalid/clementine/http".to_string(),
            reference: GitRef::Tag("v0.1.0".to_string()),
        };
        assert!(git.to_string().contains("tag 'v0.1.0'"));
        let path = SourceDescriptor::Path {
            path: PathBuf::from("/tmp/foo"),
        };
        assert!(path.to_string().contains("/tmp/foo"));
    }

    #[test]
    fn canonical_name_accessors() {
        let c = CanonicalName::from_validated("clementine/http");
        assert_eq!(c.owner(), "clementine");
        assert_eq!(c.name(), "http");
        assert_eq!(c.as_str(), "clementine/http");
        assert_eq!(c.to_string(), "clementine/http");
    }
}
