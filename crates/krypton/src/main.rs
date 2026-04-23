mod inspect;
mod repl;
mod repl_compile;

use clap::{ArgGroup, Parser, Subcommand, ValueEnum};
use krypton_diagnostics::{AriadneRenderer, DiagnosticRenderer};
use krypton_modules::module_resolver::CompositeResolver;
use krypton_package_manager::{
    AddSource, GitRef, Lockfile, Manifest, ManifestEditor,
};
use std::path::{Path, PathBuf};
use std::process;
use std::time::{Duration, Instant};
use tempfile::tempdir;
use tracing::{debug, info};
use tracing_subscriber::EnvFilter;

/// Derive a module path from a file path (e.g., "hello.kr" → "hello").
fn root_module_path(file: &str) -> String {
    std::path::Path::new(file)
        .file_stem()
        .and_then(|s| s.to_str())
        .map(|s| s.to_string())
        .unwrap_or_default()
}

fn find_runtime_jar() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("KRYPTON_RUNTIME") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../extern/jvm/runtime/build/libs/krypton-runtime.jar");
    if workspace_root.exists() {
        return Some(workspace_root);
    }
    None
}

/// Copy committed extern/js/dist/*.mjs files into the output directory so that
/// stdlib extern JS imports resolve at Node runtime.
fn copy_js_runtime(dest: &std::path::Path) {
    let extern_src = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../extern/js/dist");
    if !extern_src.exists() {
        return;
    }
    let extern_dest = dest.join("extern/js");
    std::fs::create_dir_all(&extern_dest).unwrap_or_else(|e| {
        eprintln!("Error creating runtime dir: {}", e);
        process::exit(1);
    });
    if let Ok(entries) = std::fs::read_dir(&extern_src) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("mjs") {
                std::fs::copy(&path, extern_dest.join(path.file_name().unwrap())).unwrap_or_else(
                    |e| {
                        eprintln!("Error copying runtime file: {}", e);
                        process::exit(1);
                    },
                );
            }
        }
    }
}

fn build_classpath(class_dir: &std::path::Path) -> String {
    let sep = if cfg!(windows) { ";" } else { ":" };
    match find_runtime_jar() {
        Some(jar) => format!("{}{}{}", class_dir.display(), sep, jar.display()),
        None => class_dir.display().to_string(),
    }
}

#[derive(Parser)]
#[command(name = "krypton")]
struct Cli {
    /// Print wall-clock duration for each compile phase
    #[arg(long, global = true)]
    timings: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Parse a file and print the AST
    Parse {
        file: String,
        #[arg(long, default_value = "debug")]
        format: OutputFormat,
    },
    /// Parse and pretty-print a file
    Fmt { file: String },
    /// Type-check a file, or the project in the current directory when no file is given.
    Check { file: Option<String> },
    /// Compile a file to a JVM .jar file or JS .mjs files
    Compile {
        file: String,
        /// Output path (default: <stem>.jar for JVM, out/ for JS)
        #[arg(short, long)]
        output: Option<String>,
        /// Compilation target
        #[arg(long, default_value = "jvm")]
        target: Target,
    },
    /// Compile and run a file, or the project in the current directory when no file is given.
    Run {
        file: Option<String>,
        /// Compilation target
        #[arg(long, default_value = "jvm")]
        target: Target,
    },
    /// Pretty-print the ANF intermediate representation
    DumpIr {
        file: String,
        /// Print all modules (including imports); default is main module only
        #[arg(long)]
        all: bool,
    },
    /// Inspect resource ownership: show close and move insertion points
    Inspect { file: String },
    /// Launch the interactive REPL
    Repl,
    /// Create a new Krypton project
    Init {
        /// Package identifier, e.g. `owner/my-app`
        name: String,
    },
    /// Re-resolve dependencies and write krypton.lock
    Lock,
    /// Build the project in the current directory
    Build {
        /// Compilation target
        #[arg(long, default_value = "jvm")]
        target: Target,
    },
    /// Discover and run project tests.
    Test {
        /// Optional file-level filter(s): module path relative to `src/`
        /// without the `.kr` extension (e.g. `math_test`, `parser/lexer_test`).
        filters: Vec<String>,
    },
    /// Add a dependency to krypton.toml and re-resolve.
    #[command(group(
        ArgGroup::new("source")
            .required(true)
            .multiple(false)
            .args(["git", "path", "version"]),
    ))]
    #[command(group(
        ArgGroup::new("git_ref")
            .multiple(false)
            .args(["tag", "branch", "rev"]),
    ))]
    Add {
        /// Canonical package name in `owner/name` form.
        name: String,

        #[arg(long)]
        git: Option<String>,
        #[arg(long)]
        path: Option<PathBuf>,
        #[arg(long)]
        version: Option<String>,

        #[arg(long, requires = "git")]
        tag: Option<String>,
        #[arg(long, requires = "git")]
        branch: Option<String>,
        #[arg(long, requires = "git")]
        rev: Option<String>,

        /// Override the default local import-root name.
        #[arg(long = "as")]
        as_name: Option<String>,
    },
    /// Remove a dependency from krypton.toml and re-resolve.
    Remove {
        /// The local import-root name (the key under [dependencies]).
        name: String,
    },
    /// Re-fetch moving refs and regenerate krypton.lock.
    Update,
}

#[derive(Clone, ValueEnum)]
enum OutputFormat {
    Debug,
    Surface,
}

#[derive(Clone, Copy, ValueEnum, Default)]
enum Target {
    #[default]
    Jvm,
    Js,
}

impl Target {
    fn to_compile_target(self) -> krypton_parser::ast::CompileTarget {
        match self {
            Target::Jvm => krypton_parser::ast::CompileTarget::Jvm,
            Target::Js => krypton_parser::ast::CompileTarget::Js,
        }
    }
}

fn do_parse(
    source: &str,
) -> (
    krypton_parser::ast::Module,
    Vec<krypton_parser::diagnostics::ParseError>,
) {
    krypton_parser::parser::parse(source)
}

fn format_duration(d: Duration) -> String {
    let micros = d.as_micros();
    if micros < 1000 {
        format!("{}μs", micros)
    } else {
        format!("{:.1}ms", d.as_secs_f64() * 1000.0)
    }
}

fn print_timings(phases: &[(&str, Duration)]) {
    let total: Duration = phases.iter().map(|(_, d)| *d).sum();
    for (name, dur) in phases {
        eprintln!("{:<12}{}", format!("{}:", name), format_duration(*dur));
    }
    eprintln!("{:<12}{}", "total:", format_duration(total));
}

/// Where a compiled program's artifacts should land.
enum CompileSink {
    /// Write a single JAR file. Parent directories are created as needed.
    Jar { path: PathBuf },
    /// Write every `.mjs` file produced by JS codegen into `dir`, creating
    /// it if needed. If `main_rename` is `Some`, the entry module's file is
    /// additionally emitted under that filename (copy, not move, so peer
    /// imports that still reference the old name keep resolving).
    JsDir {
        dir: PathBuf,
        main_rename: Option<String>,
    },
    /// Write class files to a freshly-created temp directory, then invoke
    /// `java -cp <dir> <class>` and `process::exit` with its status.
    JvmRunTemp,
    /// Write `.mjs` files to a freshly-created temp directory, then invoke
    /// `node <entry>` and `process::exit` with its status.
    JsRunTemp,
}

struct CompileInputs<'a> {
    /// Display path used for diagnostics (typically the source file path as
    /// the user provided it).
    diag_path: &'a str,
    source: &'a str,
    entry_module_path: String,
    entry_class_name: String,
    resolver: CompositeResolver,
    target: Target,
    require_main: bool,
    sink: CompileSink,
    /// Print phase timings before any `process::exit` inside the helper.
    /// For non-run sinks the helper returns normally and the caller prints.
    timings: bool,
}

/// Shared parse → typecheck → lower → codegen → emit pipeline used by both
/// `Compile` (single-file) and `Build` (project-aware). On any error this
/// renders diagnostics and calls `process::exit(1)` — preserving the current
/// user-facing behavior. On success, appends phase durations to `phases`.
fn compile_with_resolver(inputs: CompileInputs<'_>, phases: &mut Vec<(&'static str, Duration)>) {
    let CompileInputs {
        diag_path,
        source,
        entry_module_path,
        entry_class_name,
        resolver,
        target,
        require_main,
        sink,
        timings,
    } = inputs;
    // JS codegen uses the entry module's path as its `.mjs` filename stem
    // (e.g. "hello" for a single-file `hello.kr`, or "main"/"lib" for a
    // project build).
    let js_stem = entry_module_path.clone();

    let t = Instant::now();
    let (module, errors) = do_parse(source);
    phases.push(("parse", t.elapsed()));
    if !errors.is_empty() {
        let (diags, srcs) =
            krypton_parser::diagnostics::lower_parse_errors(diag_path, source, &errors);
        for d in &diags {
            eprint!("{}", AriadneRenderer.render(d, &srcs));
        }
        process::exit(1);
    }
    debug!("parsing complete");

    let t = Instant::now();
    let (typed_modules, interfaces) = match krypton_typechecker::infer::infer_module(
        &module,
        &resolver,
        entry_module_path,
        target.to_compile_target(),
    ) {
        Ok(result) => result,
        Err(errors) => {
            let (diags, srcs) =
                krypton_typechecker::diagnostics::lower_infer_errors(diag_path, source, &errors);
            for d in &diags {
                eprint!("{}", AriadneRenderer.render(d, &srcs));
            }
            process::exit(1);
        }
    };
    phases.push(("typecheck", t.elapsed()));
    debug!("type checking complete");

    let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);

    match target {
        Target::Jvm => {
            let t = Instant::now();
            let (ir_modules, module_sources) =
                krypton_ir::lower::lower_all(&typed_modules, &entry_class_name, &link_ctx)
                    .unwrap_or_else(|e| {
                        eprintln!("IR lowering error: {}", e);
                        process::exit(1);
                    });
            phases.push(("lower", t.elapsed()));

            let t = Instant::now();
            let classes = match krypton_codegen::emit::compile_modules(
                &ir_modules,
                &entry_class_name,
                require_main,
                &link_ctx,
                &module_sources,
            ) {
                Ok(classes) => classes,
                Err(e) => {
                    let (diags, srcs) =
                        krypton_codegen::diagnostics::lower_codegen_error(diag_path, source, &e);
                    for d in &diags {
                        eprint!("{}", AriadneRenderer.render(d, &srcs));
                    }
                    process::exit(1);
                }
            };
            phases.push(("codegen", t.elapsed()));
            info!(classes = classes.len(), "codegen complete");

            let t = Instant::now();
            match sink {
                CompileSink::Jar { path } => {
                    if let Some(parent) = path.parent() {
                        if !parent.as_os_str().is_empty() {
                            std::fs::create_dir_all(parent).unwrap_or_else(|e| {
                                eprintln!(
                                    "Error creating directory {}: {}",
                                    parent.display(),
                                    e
                                );
                                process::exit(1);
                            });
                        }
                    }
                    let main_class = if require_main {
                        Some(entry_class_name.as_str())
                    } else {
                        None
                    };
                    let jar_bytes = krypton_codegen::jar::write_jar(
                        &classes,
                        main_class,
                        find_runtime_jar().as_deref(),
                    )
                    .unwrap_or_else(|e| {
                        eprintln!("Error creating jar: {}", e);
                        process::exit(1);
                    });
                    std::fs::write(&path, jar_bytes).unwrap_or_else(|e| {
                        eprintln!("Error writing {}: {}", path.display(), e);
                        process::exit(1);
                    });
                    phases.push(("emit", t.elapsed()));
                }
                CompileSink::JvmRunTemp => {
                    let dir = tempdir().unwrap_or_else(|e| {
                        eprintln!("Error creating temp dir: {}", e);
                        process::exit(1);
                    });
                    for (name, bytes) in &classes {
                        let class_path = dir.path().join(format!("{name}.class"));
                        if let Some(parent) = class_path.parent() {
                            std::fs::create_dir_all(parent).unwrap();
                        }
                        std::fs::write(&class_path, bytes).unwrap_or_else(|e| {
                            eprintln!("Error writing class file: {}", e);
                            process::exit(1);
                        });
                    }
                    phases.push(("emit", t.elapsed()));

                    let classpath = build_classpath(dir.path());
                    info!(class = %entry_class_name, "invoking JVM");
                    let t = Instant::now();
                    let status = process::Command::new("java")
                        .arg("-cp")
                        .arg(&classpath)
                        .arg(&entry_class_name)
                        .status()
                        .unwrap_or_else(|e| {
                            eprintln!("Error running java: {}", e);
                            process::exit(1);
                        });
                    phases.push(("jvm", t.elapsed()));
                    if timings {
                        print_timings(phases);
                    }
                    process::exit(status.code().unwrap_or(1));
                }
                _ => unreachable!("JVM target requires Jar or JvmRunTemp sink"),
            }
        }
        Target::Js => {
            let stem = js_stem.as_str();
            let t = Instant::now();
            let (ir_modules, module_sources) =
                krypton_ir::lower::lower_all(&typed_modules, stem, &link_ctx).unwrap_or_else(
                    |e| {
                        eprintln!("IR lowering error: {}", e);
                        process::exit(1);
                    },
                );
            let js_module_sources: std::collections::HashMap<String, Option<String>> =
                module_sources
                    .into_iter()
                    .map(|(k, v)| (k, Some(v)))
                    .collect();
            phases.push(("lower", t.elapsed()));

            let t = Instant::now();
            let files = match krypton_codegen_js::compile_modules_js(
                &ir_modules,
                stem,
                require_main,
                &link_ctx,
                &js_module_sources,
            ) {
                Ok(files) => files,
                Err(e) => {
                    let (diags, srcs) =
                        krypton_codegen_js::diagnostics::lower_js_codegen_error(
                            diag_path, source, &e,
                        );
                    for d in &diags {
                        eprint!("{}", AriadneRenderer.render(d, &srcs));
                    }
                    process::exit(1);
                }
            };
            phases.push(("codegen", t.elapsed()));
            info!(files = files.len(), "JS codegen complete");

            let t = Instant::now();
            match sink {
                CompileSink::JsDir { dir, main_rename } => {
                    std::fs::create_dir_all(&dir).unwrap_or_else(|e| {
                        eprintln!("Error creating directory {}: {}", dir.display(), e);
                        process::exit(1);
                    });
                    let entry_filename = format!("{}.mjs", stem);
                    for (filename, js_source) in &files {
                        let file_path = dir.join(filename);
                        if let Some(parent) = file_path.parent() {
                            std::fs::create_dir_all(parent).unwrap_or_else(|e| {
                                eprintln!(
                                    "Error creating directory {}: {}",
                                    parent.display(),
                                    e
                                );
                                process::exit(1);
                            });
                        }
                        std::fs::write(&file_path, js_source).unwrap_or_else(|e| {
                            eprintln!("Error writing {}: {}", file_path.display(), e);
                            process::exit(1);
                        });
                        if let Some(ref rename) = main_rename {
                            if filename == &entry_filename {
                                let renamed_path = dir.join(rename);
                                std::fs::write(&renamed_path, js_source).unwrap_or_else(|e| {
                                    eprintln!(
                                        "Error writing {}: {}",
                                        renamed_path.display(),
                                        e
                                    );
                                    process::exit(1);
                                });
                            }
                        }
                    }
                    copy_js_runtime(&dir);
                    println!("compiled to {}", dir.display());
                    phases.push(("emit", t.elapsed()));
                }
                CompileSink::JsRunTemp => {
                    let debug_js = std::env::var_os("KRYPTON_DEBUG_JS").is_some();
                    let dir = tempdir().unwrap_or_else(|e| {
                        eprintln!("Error creating temp dir: {}", e);
                        process::exit(1);
                    });
                    let entry_file = files
                        .first()
                        .map(|(name, _)| dir.path().join(name))
                        .unwrap_or_else(|| {
                            eprintln!("No JS files generated");
                            process::exit(1);
                        });
                    for (filename, js_source) in &files {
                        let file_path = dir.path().join(filename);
                        if let Some(parent) = file_path.parent() {
                            std::fs::create_dir_all(parent).unwrap();
                        }
                        std::fs::write(&file_path, js_source).unwrap_or_else(|e| {
                            eprintln!("Error writing {}: {}", file_path.display(), e);
                            process::exit(1);
                        });
                    }
                    copy_js_runtime(dir.path());
                    if debug_js {
                        eprintln!(
                            "KRYPTON_DEBUG_JS: generated JS dir: {}",
                            dir.path().display()
                        );
                        eprintln!(
                            "KRYPTON_DEBUG_JS: entry module: {}",
                            entry_file.display()
                        );
                    }
                    phases.push(("emit", t.elapsed()));

                    info!("invoking node");
                    let t = Instant::now();
                    let status = process::Command::new("node")
                        .arg(&entry_file)
                        .status()
                        .unwrap_or_else(|e| {
                            eprintln!("Error running node: {}", e);
                            process::exit(1);
                        });
                    phases.push(("node", t.elapsed()));

                    if !status.success() && debug_js {
                        let kept_dir = dir.keep();
                        eprintln!(
                            "KRYPTON_DEBUG_JS: preserved generated JS in {}",
                            kept_dir.display()
                        );
                    }
                    if timings {
                        print_timings(phases);
                    }
                    process::exit(status.code().unwrap_or(1));
                }
                _ => unreachable!("JS target requires JsDir or JsRunTemp sink"),
            }
        }
    }
}

fn class_name_from_stem(stem: &str) -> String {
    let mut c = stem.chars();
    let base = match c.next() {
        None => "Main".to_string(),
        Some(first) => first.to_uppercase().to_string() + c.as_str(),
    };
    format!("Kr${base}")
}

/// Walk up from `start` looking for a `krypton.toml`; the first ancestor
/// (including `start` itself) that contains one is the project root. Returns
/// `None` if we reach the filesystem root without finding one.
fn find_project_root(start: &Path) -> Option<PathBuf> {
    let mut cur = start.to_path_buf();
    loop {
        if cur.join("krypton.toml").is_file() {
            return Some(cur);
        }
        if !cur.pop() {
            return None;
        }
    }
}

/// Resolve the dependency graph for `manifest` rooted at `project_root` and
/// write `krypton.lock`. Prints errors and exits with code 1 on failure.
fn resolve_and_write_lockfile(project_root: &Path, manifest: Manifest) {
    let cache = krypton_package_manager::CacheDir::new().unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });
    let graph = krypton_package_manager::resolve(project_root, manifest, &cache)
        .unwrap_or_else(|e| {
            eprintln!("Error: {e}");
            process::exit(1);
        });
    let lockfile =
        Lockfile::generate(&graph, &[], project_root).unwrap_or_else(|e| {
            eprintln!("Error: {e}");
            process::exit(1);
        });
    let lock_path = project_root.join("krypton.lock");
    lockfile.write(&lock_path).unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });
}

/// Locate `krypton.toml` from the current directory and return the project
/// root and manifest path. Exits with code 1 if no manifest is found.
fn find_project_root_or_exit() -> PathBuf {
    let cwd = std::env::current_dir().unwrap_or_else(|e| {
        eprintln!("Error: could not resolve current directory: {e}");
        process::exit(1);
    });
    find_project_root(&cwd).unwrap_or_else(|| {
        eprintln!(
            "Error: project has no krypton.toml (searched from {})",
            cwd.display()
        );
        process::exit(1);
    })
}

/// Shared preamble for project-aware commands (`build`, `run`, `check`):
/// locate the project root, load `krypton.toml`, and either reuse a current
/// lockfile or resolve-and-regenerate it. `resolve_duration` is appended to
/// caller's phase list when `Some`.
struct ProjectContext {
    project_root: PathBuf,
    manifest: krypton_package_manager::Manifest,
    graph: krypton_package_manager::ResolvedGraph,
}

fn load_project_context() -> (ProjectContext, Duration) {
    let cwd = std::env::current_dir().unwrap_or_else(|e| {
        eprintln!("Error: could not resolve current directory: {e}");
        process::exit(1);
    });
    let project_root = find_project_root(&cwd).unwrap_or_else(|| {
        eprintln!(
            "Error: project has no krypton.toml (searched from {})",
            cwd.display()
        );
        process::exit(1);
    });
    let manifest_path = project_root.join("krypton.toml");
    let manifest = krypton_package_manager::Manifest::from_path(&manifest_path).unwrap_or_else(
        |e| {
            eprintln!("Error: failed to read '{}': {e}", manifest_path.display());
            process::exit(1);
        },
    );

    let t = Instant::now();
    let cache = krypton_package_manager::CacheDir::new().unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });
    let lock_path = project_root.join("krypton.lock");
    let graph = if lock_path.is_file() {
        let lockfile = krypton_package_manager::Lockfile::read(&lock_path).unwrap_or_else(|e| {
            eprintln!("Error: {e}");
            process::exit(1);
        });
        if lockfile.is_current(&manifest, &project_root) {
            lockfile
                .to_resolved_graph(&cache, &project_root)
                .unwrap_or_else(|e| {
                    eprintln!("Error: {e}");
                    process::exit(1);
                })
        } else {
            let graph =
                krypton_package_manager::resolve(&project_root, manifest.clone(), &cache)
                    .unwrap_or_else(|e| {
                        eprintln!("Error: {e}");
                        process::exit(1);
                    });
            let regenerated =
                krypton_package_manager::Lockfile::generate(&graph, &[], &project_root)
                    .unwrap_or_else(|e| {
                        eprintln!("Error: {e}");
                        process::exit(1);
                    });
            regenerated.write(&lock_path).unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });
            graph
        }
    } else {
        let graph = krypton_package_manager::resolve(&project_root, manifest.clone(), &cache)
            .unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });
        let lockfile = krypton_package_manager::Lockfile::generate(&graph, &[], &project_root)
            .unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });
        lockfile.write(&lock_path).unwrap_or_else(|e| {
            eprintln!("Error: {e}");
            process::exit(1);
        });
        graph
    };
    let resolve_duration = t.elapsed();

    (
        ProjectContext {
            project_root,
            manifest,
            graph,
        },
        resolve_duration,
    )
}

/// Entry module descriptor used by project-mode commands.
struct EntrySpec {
    path: PathBuf,
    module_path: String,
    class_name: String,
}

/// Project entry selection. Prefers `src/main.kr` (executable, `is_main=true`)
/// then falls back to `src/lib.kr` (library, `is_main=false`). Errors when
/// neither exists.
fn select_project_entry(project_root: &Path) -> Result<(EntrySpec, bool), String> {
    let main_path = project_root.join("src/main.kr");
    if main_path.is_file() {
        return Ok((
            EntrySpec {
                path: main_path,
                module_path: "main".to_string(),
                class_name: "Kr$Main".to_string(),
            },
            true,
        ));
    }
    let lib_path = project_root.join("src/lib.kr");
    if lib_path.is_file() {
        return Ok((
            EntrySpec {
                path: lib_path,
                module_path: "lib".to_string(),
                class_name: "Kr$Lib".to_string(),
            },
            false,
        ));
    }
    Err(format!(
        "project has no src/main.kr or src/lib.kr (searched {})",
        project_root.join("src").display()
    ))
}

/// Like `select_project_entry` but requires an executable (`src/main.kr`).
/// Used by `run`, which cannot start a library.
fn select_executable_entry(project_root: &Path) -> Result<EntrySpec, String> {
    let main_path = project_root.join("src/main.kr");
    if main_path.is_file() {
        return Ok(EntrySpec {
            path: main_path,
            module_path: "main".to_string(),
            class_name: "Kr$Main".to_string(),
        });
    }
    Err("no entry point: src/main.kr not found".to_string())
}

/// Assemble the `-cp` string for `java`. Composed (in order) of:
///   1. the emitted program JAR,
///   2. every entry in `[jvm].classpath` (absolutized against the project root,
///      validated to exist),
///   3. the Krypton runtime JAR (when discoverable).
///
/// Resolved Maven JARs land here in M35-T13 once the lockfile `[[maven]]`
/// section is populated; today the resolved graph carries no Maven entries,
/// so that branch is intentionally absent rather than a silent no-op.
fn assemble_jvm_runtime_classpath(
    ctx: &ProjectContext,
    program_jar: &Path,
) -> Result<String, String> {
    let sep = if cfg!(windows) { ";" } else { ":" };
    let mut parts: Vec<String> = vec![program_jar.display().to_string()];
    if let Some(jvm) = &ctx.manifest.jvm {
        for entry in &jvm.classpath {
            let abs = if entry.is_absolute() {
                entry.clone()
            } else {
                ctx.project_root.join(entry)
            };
            if !abs.exists() {
                return Err(format!(
                    "classpath entry not found: {}",
                    entry.display()
                ));
            }
            parts.push(abs.display().to_string());
        }
    }
    if let Some(rt) = find_runtime_jar() {
        parts.push(rt.display().to_string());
    }
    Ok(parts.join(sep))
}

/// Project-mode `run`: build the program, then invoke `java`/`node` and exit
/// with the subprocess status code. Fails if the project has no executable
/// entry (AC 5).
fn run_project(target: Target, timings: bool) -> ! {
    let (ctx, resolve_dur) = load_project_context();

    let entry = select_executable_entry(&ctx.project_root).unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });
    let source = std::fs::read_to_string(&entry.path).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", entry.path.display(), e);
        process::exit(1);
    });

    let source_root = ctx.project_root.join("src");
    let deps = ctx.graph.source_roots(&ctx.manifest);
    let resolver = CompositeResolver::new(Some(source_root), deps).unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });

    let leaf = ctx
        .manifest
        .package
        .name
        .rsplit('/')
        .next()
        .expect("canonical package name has owner/leaf form")
        .to_string();

    let sink = match target {
        Target::Jvm => CompileSink::Jar {
            path: ctx
                .project_root
                .join("target")
                .join("jvm")
                .join(format!("{leaf}.jar")),
        },
        Target::Js => CompileSink::JsDir {
            dir: ctx.project_root.join("target").join("js"),
            main_rename: Some(format!("{leaf}.mjs")),
        },
    };

    let mut phases: Vec<(&str, Duration)> = vec![("resolve", resolve_dur)];
    let diag_path = entry.path.to_string_lossy().to_string();
    compile_with_resolver(
        CompileInputs {
            diag_path: &diag_path,
            source: &source,
            entry_module_path: entry.module_path.clone(),
            entry_class_name: entry.class_name.clone(),
            resolver,
            target,
            require_main: true,
            sink,
            timings,
        },
        &mut phases,
    );

    // Invoke the built artifact.
    let t = Instant::now();
    let status = match target {
        Target::Jvm => {
            let jar_path = ctx
                .project_root
                .join("target")
                .join("jvm")
                .join(format!("{leaf}.jar"));
            let classpath =
                assemble_jvm_runtime_classpath(&ctx, &jar_path).unwrap_or_else(|e| {
                    eprintln!("Error: {e}");
                    process::exit(1);
                });
            info!(class = %entry.class_name, "invoking JVM");
            process::Command::new("java")
                .arg("-cp")
                .arg(&classpath)
                .arg(&entry.class_name)
                .status()
                .unwrap_or_else(|e| {
                    eprintln!("Error running java: {}", e);
                    process::exit(1);
                })
        }
        Target::Js => {
            let entry_mjs = ctx
                .project_root
                .join("target")
                .join("js")
                .join(format!("{}.mjs", entry.module_path));
            info!("invoking node");
            process::Command::new("node")
                .arg(&entry_mjs)
                .status()
                .unwrap_or_else(|e| {
                    eprintln!("Error running node: {}", e);
                    process::exit(1);
                })
        }
    };
    phases.push((
        match target {
            Target::Jvm => "jvm",
            Target::Js => "node",
        },
        t.elapsed(),
    ));
    if timings {
        print_timings(&phases);
    }
    process::exit(status.code().unwrap_or(1));
}

/// Project-mode `check`: manifest load + dep resolution + parse + typecheck.
/// No codegen, no JDK required. Exits 0 on success, 1 on any error.
fn check_project(timings: bool) -> ! {
    let (ctx, resolve_dur) = load_project_context();

    let (entry, _is_main) = select_project_entry(&ctx.project_root).unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });

    let source = std::fs::read_to_string(&entry.path).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", entry.path.display(), e);
        process::exit(1);
    });

    let source_root = ctx.project_root.join("src");
    let deps = ctx.graph.source_roots(&ctx.manifest);
    let resolver = CompositeResolver::new(Some(source_root), deps).unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    });

    // Use a project-relative path for diagnostics (e.g. "src/main.kr") so
    // error output is readable rather than an absolute temp-dir path.
    let diag_path = entry
        .path
        .strip_prefix(&ctx.project_root)
        .unwrap_or(&entry.path)
        .to_string_lossy()
        .to_string();

    let mut phases: Vec<(&str, Duration)> = vec![("resolve", resolve_dur)];

    let t = Instant::now();
    let (module, errors) = do_parse(&source);
    phases.push(("parse", t.elapsed()));
    if !errors.is_empty() {
        let (diags, srcs) =
            krypton_parser::diagnostics::lower_parse_errors(&diag_path, &source, &errors);
        for d in &diags {
            eprint!("{}", AriadneRenderer.render(d, &srcs));
        }
        process::exit(1);
    }

    let t = Instant::now();
    match krypton_typechecker::infer::infer_module(
        &module,
        &resolver,
        entry.module_path.clone(),
        krypton_parser::ast::CompileTarget::Jvm,
    ) {
        Ok(_) => {
            phases.push(("typecheck", t.elapsed()));
        }
        Err(errors) => {
            let (diags, srcs) = krypton_typechecker::diagnostics::lower_infer_errors(
                &diag_path, &source, &errors,
            );
            for d in &diags {
                eprint!("{}", AriadneRenderer.render(d, &srcs));
            }
            process::exit(1);
        }
    }

    if timings {
        print_timings(&phases);
    }
    process::exit(0);
}

/// Project-mode `test`: skeleton handler. Loads the manifest and resolves
/// dependencies so manifest/lockfile errors surface here, then prints
/// "no tests yet" and exits 0. `filters` is accepted and ignored for forward
/// compatibility with the full discovery + execution pipeline.
fn test_project(_filters: Vec<String>, timings: bool) -> ! {
    let (_ctx, resolve_dur) = load_project_context();

    if timings {
        print_timings(&[("resolve", resolve_dur)]);
    }
    println!("no tests yet");
    process::exit(0);
}

fn main() {
    std::panic::set_hook(Box::new(|info| {
        let message = if let Some(s) = info.payload().downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = info.payload().downcast_ref::<String>() {
            s.clone()
        } else {
            "unknown panic".to_string()
        };

        eprintln!("error: internal compiler error: {message}");
        if let Some(loc) = info.location() {
            eprintln!("  --> {}:{}:{}", loc.file(), loc.line(), loc.column());
        }
        eprintln!();
        eprintln!("This is a bug in the Krypton compiler. Please report it.");
        process::exit(101);
    }));

    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::try_from_env("KRYPTON_LOG")
                .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
                .unwrap_or_else(|_| EnvFilter::new("warn")),
        )
        .with_target(true)
        .with_writer(std::io::stderr)
        .init();

    let cli = Cli::parse();
    let timings = cli.timings;
    match cli.command {
        Commands::Parse { file, format } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = do_parse(&source);
            if !errors.is_empty() {
                let (diags, srcs) =
                    krypton_parser::diagnostics::lower_parse_errors(&file, &source, &errors);
                for d in &diags {
                    eprint!("{}", AriadneRenderer.render(d, &srcs));
                }
                process::exit(1);
            }
            match format {
                OutputFormat::Debug => println!("{:#?}", module),
                OutputFormat::Surface => {
                    println!("{}", krypton_parser::pretty::pretty_print(&module))
                }
            }
        }
        Commands::Fmt { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = do_parse(&source);
            if !errors.is_empty() {
                let (diags, srcs) =
                    krypton_parser::diagnostics::lower_parse_errors(&file, &source, &errors);
                for d in &diags {
                    eprint!("{}", AriadneRenderer.render(d, &srcs));
                }
                process::exit(1);
            }
            println!("{}", krypton_parser::pretty::pretty_print(&module));
        }
        Commands::Compile {
            file,
            output,
            target,
        } => {
            info!(file = %file, "starting compilation");
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let stem = std::path::Path::new(&file)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Main")
                .to_string();
            let entry_class_name = class_name_from_stem(&stem);

            let file_path = std::path::Path::new(&file);
            let source_root = file_path.parent().unwrap_or(std::path::Path::new("."));
            let resolver = CompositeResolver::with_source_root(source_root.to_path_buf());

            let sink = match target {
                Target::Jvm => CompileSink::Jar {
                    path: output
                        .map(PathBuf::from)
                        .unwrap_or_else(|| PathBuf::from(format!("{}.jar", stem))),
                },
                Target::Js => CompileSink::JsDir {
                    dir: output.map(PathBuf::from).unwrap_or_else(|| PathBuf::from("./out")),
                    main_rename: None,
                },
            };

            let mut phases: Vec<(&str, Duration)> = Vec::new();
            compile_with_resolver(
                CompileInputs {
                    diag_path: &file,
                    source: &source,
                    entry_module_path: root_module_path(&file),
                    entry_class_name,
                    resolver,
                    target,
                    require_main: true,
                    sink,
                    timings,
                },
                &mut phases,
            );

            if timings {
                print_timings(&phases);
            }
        }
        Commands::Run { file, target } => {
            let Some(file) = file else {
                run_project(target, timings);
            };
            info!(file = %file, "starting compilation");
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let stem = std::path::Path::new(&file)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Main")
                .to_string();
            let entry_class_name = class_name_from_stem(&stem);

            let file_path = std::path::Path::new(&file);
            let source_root = file_path.parent().unwrap_or(std::path::Path::new("."));
            let resolver = CompositeResolver::with_source_root(source_root.to_path_buf());

            let sink = match target {
                Target::Jvm => CompileSink::JvmRunTemp,
                Target::Js => CompileSink::JsRunTemp,
            };

            let mut phases: Vec<(&str, Duration)> = Vec::new();
            compile_with_resolver(
                CompileInputs {
                    diag_path: &file,
                    source: &source,
                    entry_module_path: root_module_path(&file),
                    entry_class_name,
                    resolver,
                    target,
                    require_main: true,
                    sink,
                    timings,
                },
                &mut phases,
            );
            // Unreachable: run sinks exit from inside the helper.
            unreachable!("run sinks must exit inside compile_with_resolver");
        }
        Commands::Check { file } => {
            let Some(file) = file else {
                check_project(timings);
            };
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let mut phases: Vec<(&str, Duration)> = Vec::new();

            let t = Instant::now();
            let (module, errors) = do_parse(&source);
            phases.push(("parse", t.elapsed()));
            if !errors.is_empty() {
                let (diags, srcs) =
                    krypton_parser::diagnostics::lower_parse_errors(&file, &source, &errors);
                for d in &diags {
                    eprint!("{}", AriadneRenderer.render(d, &srcs));
                }
                process::exit(1);
            }

            let file_path = std::path::Path::new(&file);
            let source_root = file_path.parent().unwrap_or(std::path::Path::new("."));
            let resolver = CompositeResolver::with_source_root(source_root.to_path_buf());

            let t = Instant::now();
            match krypton_typechecker::infer::infer_module(
                &module,
                &resolver,
                root_module_path(&file),
                krypton_parser::ast::CompileTarget::Jvm,
            ) {
                Ok((modules, _)) => {
                    phases.push(("typecheck", t.elapsed()));
                    let info = &modules[0];
                    for entry in &info.fn_types {
                        println!("{} : {}", entry.name, entry.scheme);
                    }
                }
                Err(errors) => {
                    let (diags, srcs) = krypton_typechecker::diagnostics::lower_infer_errors(
                        &file, &source, &errors,
                    );
                    for d in &diags {
                        eprint!("{}", AriadneRenderer.render(d, &srcs));
                    }
                    process::exit(1);
                }
            }

            if timings {
                print_timings(&phases);
            }
        }
        Commands::DumpIr { file, all } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let mut phases: Vec<(&str, Duration)> = Vec::new();

            let t = Instant::now();
            let (module, errors) = do_parse(&source);
            phases.push(("parse", t.elapsed()));
            if !errors.is_empty() {
                let (diags, srcs) =
                    krypton_parser::diagnostics::lower_parse_errors(&file, &source, &errors);
                for d in &diags {
                    eprint!("{}", AriadneRenderer.render(d, &srcs));
                }
                process::exit(1);
            }

            let file_path = std::path::Path::new(&file);
            let source_root = file_path.parent().unwrap_or(std::path::Path::new("."));
            let resolver = CompositeResolver::with_source_root(source_root.to_path_buf());

            let t = Instant::now();
            let (typed_modules, interfaces) = match krypton_typechecker::infer::infer_module(
                &module,
                &resolver,
                root_module_path(&file),
                krypton_parser::ast::CompileTarget::Jvm,
            ) {
                Ok(result) => result,
                Err(errors) => {
                    let (diags, srcs) = krypton_typechecker::diagnostics::lower_infer_errors(
                        &file, &source, &errors,
                    );
                    for d in &diags {
                        eprint!("{}", AriadneRenderer.render(d, &srcs));
                    }
                    process::exit(1);
                }
            };
            phases.push(("typecheck", t.elapsed()));

            let stem = std::path::Path::new(&file)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("main");

            let mut lower_dur = Duration::ZERO;
            let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
            for (i, typed) in typed_modules.iter().enumerate() {
                if !all && i > 0 {
                    continue;
                }
                let mod_name = if i == 0 {
                    stem.to_string()
                } else {
                    typed.module_path.clone()
                };
                let view = link_ctx
                    .view_for(&krypton_typechecker::module_interface::ModulePath::new(
                        &typed.module_path,
                    ))
                    .unwrap_or_else(|| {
                        panic!(
                            "ICE: no LinkContext view for module '{}'",
                            typed.module_path
                        )
                    });
                let t = Instant::now();
                match krypton_ir::lower::lower_module(typed, &mod_name, &view) {
                    Ok(ir_module) => {
                        lower_dur += t.elapsed();
                        print!("{}", ir_module);
                    }
                    Err(e) => {
                        eprintln!("IR lowering error (module {}): {}", mod_name, e);
                        process::exit(1);
                    }
                }
            }
            phases.push(("lower", lower_dur));

            if timings {
                print_timings(&phases);
            }
        }
        Commands::Repl => {
            repl::run_repl().unwrap_or_else(|e| {
                eprintln!("error: {}", e);
                process::exit(1);
            });
        }
        Commands::Init { name } => {
            let cwd = std::env::current_dir().unwrap_or_else(|e| {
                eprintln!("Error: could not resolve current directory: {e}");
                process::exit(1);
            });
            match krypton_package_manager::init_project(&cwd, &name) {
                Ok(dir) => println!("created {}", dir.display()),
                Err(e) => {
                    eprintln!("Error: {e}");
                    process::exit(1);
                }
            }
        }
        Commands::Lock => {
            let cwd = std::env::current_dir().unwrap_or_else(|e| {
                eprintln!("Error: could not resolve current directory: {e}");
                process::exit(1);
            });
            let manifest_path = cwd.join("krypton.toml");
            let manifest = krypton_package_manager::Manifest::from_path(&manifest_path)
                .unwrap_or_else(|e| {
                    eprintln!("Error: failed to read '{}': {e}", manifest_path.display());
                    process::exit(1);
                });
            let cache = krypton_package_manager::CacheDir::new().unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });
            let graph =
                krypton_package_manager::resolve(&cwd, manifest, &cache).unwrap_or_else(|e| {
                    eprintln!("Error: {e}");
                    process::exit(1);
                });
            let lockfile =
                krypton_package_manager::Lockfile::generate(&graph, &[], &cwd).unwrap_or_else(
                    |e| {
                        eprintln!("Error: {e}");
                        process::exit(1);
                    },
                );
            let lock_path = cwd.join("krypton.lock");
            lockfile.write(&lock_path).unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });
            println!("wrote {}", lock_path.display());
        }
        Commands::Build { target } => {
            let (ctx, resolve_dur) = load_project_context();
            let mut phases: Vec<(&str, Duration)> = vec![("resolve", resolve_dur)];

            let (entry, is_main) =
                select_project_entry(&ctx.project_root).unwrap_or_else(|e| {
                    eprintln!("Error: {e}");
                    process::exit(1);
                });

            let source = std::fs::read_to_string(&entry.path).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", entry.path.display(), e);
                process::exit(1);
            });

            let source_root = ctx.project_root.join("src");
            let deps = ctx.graph.source_roots(&ctx.manifest);
            let resolver = CompositeResolver::new(Some(source_root), deps).unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });

            let leaf = ctx
                .manifest
                .package
                .name
                .rsplit('/')
                .next()
                .expect("canonical package name has owner/leaf form");

            let sink = match target {
                Target::Jvm => CompileSink::Jar {
                    path: ctx
                        .project_root
                        .join("target")
                        .join("jvm")
                        .join(format!("{leaf}.jar")),
                },
                Target::Js => CompileSink::JsDir {
                    dir: ctx.project_root.join("target").join("js"),
                    main_rename: Some(format!("{leaf}.mjs")),
                },
            };

            let diag_path = entry.path.to_string_lossy().to_string();
            compile_with_resolver(
                CompileInputs {
                    diag_path: &diag_path,
                    source: &source,
                    entry_module_path: entry.module_path,
                    entry_class_name: entry.class_name,
                    resolver,
                    target,
                    require_main: is_main,
                    sink,
                    timings,
                },
                &mut phases,
            );

            if timings {
                print_timings(&phases);
            }
        }
        Commands::Test { filters } => test_project(filters, timings),
        Commands::Inspect { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });

            let (module, errors) = do_parse(&source);
            if !errors.is_empty() {
                let (diags, srcs) =
                    krypton_parser::diagnostics::lower_parse_errors(&file, &source, &errors);
                for d in &diags {
                    eprint!("{}", AriadneRenderer.render(d, &srcs));
                }
                process::exit(1);
            }

            let file_path = std::path::Path::new(&file);
            let source_root = file_path.parent().unwrap_or(std::path::Path::new("."));
            let resolver = CompositeResolver::with_source_root(source_root.to_path_buf());

            match krypton_typechecker::infer::infer_module(
                &module,
                &resolver,
                root_module_path(&file),
                krypton_parser::ast::CompileTarget::Jvm,
            ) {
                Ok((modules, _)) => {
                    let info = &modules[0];
                    let output = inspect::render_inspect(
                        &module,
                        &info.auto_close,
                        &info.functions,
                        &info.fn_types,
                        &info.instance_defs,
                    );
                    print!("{}", output);
                }
                Err(errors) => {
                    // AC6: on error, print source with line numbers and show the error
                    let lines: Vec<&str> = source.lines().collect();
                    let width = lines.len().to_string().len().max(4);
                    for (i, line) in lines.iter().enumerate() {
                        println!("{:>width$} | {}", i + 1, line, width = width);
                    }
                    println!();
                    let (diags, srcs) = krypton_typechecker::diagnostics::lower_infer_errors(
                        &file, &source, &errors,
                    );
                    for d in &diags {
                        eprint!("{}", AriadneRenderer.render(d, &srcs));
                    }
                    process::exit(1);
                }
            }
        }
        Commands::Add {
            name,
            git,
            path,
            version,
            tag,
            branch,
            rev,
            as_name,
        } => {
            let source = match (git, path, version) {
                (Some(url), None, None) => {
                    let git_ref = match (tag, branch, rev) {
                        (Some(t), None, None) => GitRef::Tag(t),
                        (None, Some(b), None) => GitRef::Branch(b),
                        (None, None, Some(r)) => GitRef::Rev(r),
                        _ => {
                            eprintln!(
                                "Error: --git requires exactly one of --tag, --branch, or --rev"
                            );
                            process::exit(2);
                        }
                    };
                    AddSource::Git { url, git_ref }
                }
                (None, Some(path), None) => AddSource::Path { path },
                (None, None, Some(version)) => AddSource::Registry { version },
                // clap's ArgGroup enforces exactly-one; this branch is for
                // coverage in case that constraint is ever weakened.
                _ => {
                    eprintln!(
                        "Error: exactly one of --git, --path, or --version is required"
                    );
                    process::exit(2);
                }
            };

            let project_root = find_project_root_or_exit();
            let manifest_path = project_root.join("krypton.toml");

            let mut editor = ManifestEditor::from_path(&manifest_path).unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });
            let local_root = editor
                .add_dependency(&name, source, as_name.as_deref())
                .unwrap_or_else(|e| {
                    eprintln!("Error: {e}");
                    process::exit(1);
                });

            // Defensive validation: re-parse the edited manifest before
            // touching the filesystem. Normal writes always produce valid
            // TOML, but this guards against editor bugs cheaply.
            let edited = editor.render();
            let manifest = Manifest::from_str(&edited).unwrap_or_else(|e| {
                eprintln!(
                    "Error: internal error: edited manifest is invalid: {e}"
                );
                process::exit(1);
            });

            std::fs::write(&manifest_path, &edited).unwrap_or_else(|e| {
                eprintln!(
                    "Error: failed to write '{}': {e}",
                    manifest_path.display()
                );
                process::exit(1);
            });

            resolve_and_write_lockfile(&project_root, manifest);
            println!("added '{local_root}' ({name})");
        }
        Commands::Remove { name } => {
            let project_root = find_project_root_or_exit();
            let manifest_path = project_root.join("krypton.toml");

            let mut editor = ManifestEditor::from_path(&manifest_path).unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });
            editor.remove_dependency(&name).unwrap_or_else(|e| {
                eprintln!("Error: {e}");
                process::exit(1);
            });

            let edited = editor.render();
            let manifest = Manifest::from_str(&edited).unwrap_or_else(|e| {
                eprintln!(
                    "Error: internal error: edited manifest is invalid: {e}"
                );
                process::exit(1);
            });

            std::fs::write(&manifest_path, &edited).unwrap_or_else(|e| {
                eprintln!(
                    "Error: failed to write '{}': {e}",
                    manifest_path.display()
                );
                process::exit(1);
            });

            resolve_and_write_lockfile(&project_root, manifest);
            println!("removed '{name}'");
        }
        Commands::Update => {
            let project_root = find_project_root_or_exit();
            let manifest_path = project_root.join("krypton.toml");
            let manifest = Manifest::from_path(&manifest_path).unwrap_or_else(|e| {
                eprintln!("Error: failed to read '{}': {e}", manifest_path.display());
                process::exit(1);
            });
            // `resolve` re-fetches git sources via `fetch_git::ensure_persistent_clone`,
            // so branch refs naturally advance to current HEAD here.
            resolve_and_write_lockfile(&project_root, manifest);
            let lock_path = project_root.join("krypton.lock");
            println!("updated {}", lock_path.display());
        }
    }
}
