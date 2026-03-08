use clap::{Parser, Subcommand, ValueEnum};
use std::path::PathBuf;
use std::process;
use std::time::{Duration, Instant};
use tempfile::tempdir;
use tracing::{debug, info};
use tracing_subscriber::EnvFilter;

fn find_runtime_jar() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("KRYPTON_RUNTIME") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../runtime/build/libs/krypton-runtime.jar");
    if workspace_root.exists() {
        return Some(workspace_root);
    }
    None
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
    Fmt {
        file: String,
    },
    /// Type-check a file and print inferred types
    Check {
        file: String,
    },
    /// Compile a file to a JVM .class file
    Compile {
        file: String,
    },
    /// Compile and run a file on the JVM
    Run {
        file: String,
    },
}

#[derive(Clone, ValueEnum)]
enum OutputFormat {
    Debug,
    Surface,
}

fn do_parse(source: &str) -> (krypton_parser::ast::Module, Vec<krypton_parser::diagnostics::ParseError>) {
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
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            match format {
                OutputFormat::Debug => println!("{:#?}", module),
                OutputFormat::Surface => println!("{}", krypton_parser::pretty::pretty_print(&module)),
            }
        }
        Commands::Fmt { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = do_parse(&source);
            if !errors.is_empty() {
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            println!("{}", krypton_parser::pretty::pretty_print(&module));
        }
        Commands::Compile { file } => {
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
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            debug!("parsing complete");

            let t = Instant::now();
            if let Err(e) = krypton_typechecker::infer::infer_module(&module) {
                let diag =
                    krypton_typechecker::diagnostics::render_type_errors(&file, &source, &[e]);
                eprint!("{}", diag);
                process::exit(1);
            }
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
                    Some(first) => {
                        first.to_uppercase().to_string() + c.as_str()
                    }
                };
                format!("Kr${base}")
            };

            let t = Instant::now();
            match krypton_codegen::emit::compile_module(&module, &class_name) {
                Ok(classes) => {
                    phases.push(("codegen", t.elapsed()));
                    info!(classes = classes.len(), "codegen complete");

                    let t = Instant::now();
                    for (name, bytes) in &classes {
                        let out_path = format!("{}.class", name);
                        std::fs::write(&out_path, bytes).unwrap_or_else(|e| {
                            eprintln!("Error writing {}: {}", out_path, e);
                            process::exit(1);
                        });
                    }
                    phases.push(("emit", t.elapsed()));
                }
                Err(e) => {
                    eprintln!("Codegen error: {}", e);
                    process::exit(1);
                }
            }

            if timings {
                print_timings(&phases);
            }
        }
        Commands::Run { file } => {
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
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            debug!("parsing complete");

            let t = Instant::now();
            if let Err(e) = krypton_typechecker::infer::infer_module(&module) {
                let diag =
                    krypton_typechecker::diagnostics::render_type_errors(&file, &source, &[e]);
                eprint!("{}", diag);
                process::exit(1);
            }
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

            let t = Instant::now();
            match krypton_codegen::emit::compile_module(&module, &class_name) {
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
                    eprintln!("Codegen error: {}", e);
                    process::exit(1);
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
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }

            let t = Instant::now();
            match krypton_typechecker::infer::infer_module(&module) {
                Ok(info) => {
                    phases.push(("typecheck", t.elapsed()));
                    for (name, scheme) in &info.fn_types {
                        println!("{} : {}", name, scheme);
                    }
                }
                Err(e) => {
                    let diag =
                        krypton_typechecker::diagnostics::render_type_errors(&file, &source, &[e]);
                    eprint!("{}", diag);
                    process::exit(1);
                }
            }

            if timings {
                print_timings(&phases);
            }
        }
    }
}
