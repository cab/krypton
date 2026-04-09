mod inspect;
mod repl;
mod repl_compile;

use clap::{Parser, Subcommand, ValueEnum};
use krypton_diagnostics::{AriadneRenderer, DiagnosticRenderer};
use krypton_modules::module_resolver::CompositeResolver;
use std::path::PathBuf;
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
    /// Type-check a file and print inferred types
    Check { file: String },
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
    /// Compile and run a file
    Run {
        file: String,
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
}

#[derive(Clone, ValueEnum)]
enum OutputFormat {
    Debug,
    Surface,
}

#[derive(Clone, ValueEnum, Default)]
enum Target {
    #[default]
    Jvm,
    Js,
}

impl Target {
    fn to_compile_target(&self) -> krypton_parser::ast::CompileTarget {
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
            debug!("parsing complete");

            let file_path = std::path::Path::new(&file);
            let source_root = file_path.parent().unwrap_or(std::path::Path::new("."));
            let resolver = CompositeResolver::with_source_root(source_root.to_path_buf());

            let t = Instant::now();
            let (typed_modules, interfaces) = match krypton_typechecker::infer::infer_module(
                &module,
                &resolver,
                root_module_path(&file),
                target.to_compile_target(),
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
            debug!("type checking complete");

            // Derive class name from filename, prefixed to avoid collisions
            // with type names (e.g., hello.kr → Kr$Hello)
            let stem = std::path::Path::new(&file)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Main");
            let class_name = {
                let mut c = stem.chars();
                let base = match c.next() {
                    None => "Main".to_string(),
                    Some(first) => first.to_uppercase().to_string() + c.as_str(),
                };
                format!("Kr${base}")
            };

            let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
            match target {
                Target::Jvm => {
                    let t = Instant::now();
                    let (ir_modules, module_sources) =
                        krypton_ir::lower::lower_all(&typed_modules, &class_name, &link_ctx)
                            .unwrap_or_else(|e| {
                                eprintln!("IR lowering error: {}", e);
                                process::exit(1);
                            });
                    phases.push(("lower", t.elapsed()));

                    let t = Instant::now();
                    match krypton_codegen::emit::compile_modules(
                        &ir_modules,
                        &class_name,
                        &link_ctx,
                        &module_sources,
                    ) {
                        Ok(classes) => {
                            phases.push(("codegen", t.elapsed()));
                            info!(classes = classes.len(), "codegen complete");

                            let t = Instant::now();
                            let out_path = match &output {
                                Some(o) => PathBuf::from(o),
                                None => PathBuf::from(format!("{}.jar", stem)),
                            };
                            if let Some(parent) = out_path.parent() {
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
                            let jar_bytes = krypton_codegen::jar::write_jar(
                                &classes,
                                &class_name,
                                find_runtime_jar().as_deref(),
                            )
                            .unwrap_or_else(|e| {
                                eprintln!("Error creating jar: {}", e);
                                process::exit(1);
                            });
                            std::fs::write(&out_path, jar_bytes).unwrap_or_else(|e| {
                                eprintln!("Error writing {}: {}", out_path.display(), e);
                                process::exit(1);
                            });
                            phases.push(("emit", t.elapsed()));
                        }
                        Err(e) => {
                            let (diags, srcs) = krypton_codegen::diagnostics::lower_codegen_error(
                                &file, &source, &e,
                            );
                            for d in &diags {
                                eprint!("{}", AriadneRenderer.render(d, &srcs));
                            }
                            process::exit(1);
                        }
                    }
                }
                Target::Js => {
                    let t = Instant::now();
                    let (ir_modules, module_sources) =
                        krypton_ir::lower::lower_all(&typed_modules, stem, &link_ctx)
                            .unwrap_or_else(|e| {
                                eprintln!("IR lowering error: {}", e);
                                process::exit(1);
                            });
                    let js_module_sources: std::collections::HashMap<String, Option<String>> =
                        module_sources
                            .into_iter()
                            .map(|(k, v)| (k, Some(v)))
                            .collect();
                    phases.push(("lower", t.elapsed()));

                    let t = Instant::now();
                    match krypton_codegen_js::compile_modules_js(
                        &ir_modules,
                        stem,
                        true,
                        &link_ctx,
                        &js_module_sources,
                    ) {
                        Ok(files) => {
                            phases.push(("codegen", t.elapsed()));
                            info!(files = files.len(), "JS codegen complete");

                            let t = Instant::now();
                            let out_dir = match &output {
                                Some(o) => PathBuf::from(o),
                                None => PathBuf::from("./out"),
                            };
                            std::fs::create_dir_all(&out_dir).unwrap_or_else(|e| {
                                eprintln!("Error creating directory {}: {}", out_dir.display(), e);
                                process::exit(1);
                            });
                            for (filename, js_source) in &files {
                                let file_path = out_dir.join(filename);
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
                            }
                            copy_js_runtime(&out_dir);
                            println!("compiled to {}", &out_dir.display());
                            phases.push(("emit", t.elapsed()));
                        }
                        Err(e) => {
                            let (diags, srcs) =
                                krypton_codegen_js::diagnostics::lower_js_codegen_error(
                                    &file, &source, &e,
                                );
                            for d in &diags {
                                eprint!("{}", AriadneRenderer.render(d, &srcs));
                            }
                            process::exit(1);
                        }
                    }
                }
            }

            if timings {
                print_timings(&phases);
            }
        }
        Commands::Run { file, target } => {
            info!(file = %file, "starting compilation");
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
            debug!("parsing complete");

            let file_path = std::path::Path::new(&file);
            let source_root = file_path.parent().unwrap_or(std::path::Path::new("."));
            let resolver = CompositeResolver::with_source_root(source_root.to_path_buf());

            let t = Instant::now();
            let (typed_modules, interfaces) = match krypton_typechecker::infer::infer_module(
                &module,
                &resolver,
                root_module_path(&file),
                target.to_compile_target(),
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
            debug!("type checking complete");

            let stem = std::path::Path::new(&file)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Main");
            let class_name = {
                let mut c = stem.chars();
                let base = match c.next() {
                    None => "Main".to_string(),
                    Some(first) => first.to_uppercase().to_string() + c.as_str(),
                };
                format!("Kr${base}")
            };

            let link_ctx = krypton_typechecker::link_context::LinkContext::build(interfaces);
            match target {
                Target::Jvm => {
                    let t = Instant::now();
                    let (ir_modules, module_sources) =
                        krypton_ir::lower::lower_all(&typed_modules, &class_name, &link_ctx)
                            .unwrap_or_else(|e| {
                                eprintln!("IR lowering error: {}", e);
                                process::exit(1);
                            });
                    phases.push(("lower", t.elapsed()));

                    let t = Instant::now();
                    match krypton_codegen::emit::compile_modules(
                        &ir_modules,
                        &class_name,
                        &link_ctx,
                        &module_sources,
                    ) {
                        Ok(classes) => {
                            phases.push(("codegen", t.elapsed()));
                            info!(classes = classes.len(), "codegen complete");

                            let t = Instant::now();
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
                            info!(class = %class_name, "invoking JVM");
                            let t = Instant::now();
                            let status = process::Command::new("java")
                                .arg("-cp")
                                .arg(&classpath)
                                .arg(&class_name)
                                .status()
                                .unwrap_or_else(|e| {
                                    eprintln!("Error running java: {}", e);
                                    process::exit(1);
                                });
                            phases.push(("jvm", t.elapsed()));

                            if timings {
                                print_timings(&phases);
                            }
                            process::exit(status.code().unwrap_or(1));
                        }
                        Err(e) => {
                            let (diags, srcs) = krypton_codegen::diagnostics::lower_codegen_error(
                                &file, &source, &e,
                            );
                            for d in &diags {
                                eprint!("{}", AriadneRenderer.render(d, &srcs));
                            }
                            process::exit(1);
                        }
                    }
                }
                Target::Js => {
                    let t = Instant::now();
                    let (ir_modules, module_sources) =
                        krypton_ir::lower::lower_all(&typed_modules, stem, &link_ctx)
                            .unwrap_or_else(|e| {
                                eprintln!("IR lowering error: {}", e);
                                process::exit(1);
                            });
                    let js_module_sources: std::collections::HashMap<String, Option<String>> =
                        module_sources
                            .into_iter()
                            .map(|(k, v)| (k, Some(v)))
                            .collect();
                    phases.push(("lower", t.elapsed()));

                    let t = Instant::now();
                    match krypton_codegen_js::compile_modules_js(
                        &ir_modules,
                        stem,
                        true,
                        &link_ctx,
                        &js_module_sources,
                    ) {
                        Ok(files) => {
                            let debug_js = std::env::var_os("KRYPTON_DEBUG_JS").is_some();
                            phases.push(("codegen", t.elapsed()));
                            info!(files = files.len(), "JS codegen complete");

                            let t = Instant::now();
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
                                print_timings(&phases);
                            }
                            process::exit(status.code().unwrap_or(1));
                        }
                        Err(e) => {
                            let (diags, srcs) =
                                krypton_codegen_js::diagnostics::lower_js_codegen_error(
                                    &file, &source, &e,
                                );
                            for d in &diags {
                                eprint!("{}", AriadneRenderer.render(d, &srcs));
                            }
                            process::exit(1);
                        }
                    }
                }
            }
        }
        Commands::Check { file } => {
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
    }
}
