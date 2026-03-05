use clap::{Parser, Subcommand, ValueEnum};
use std::process;
use tempfile::tempdir;

#[derive(Parser)]
#[command(name = "krypton")]
struct Cli {
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
    /// Compile a file to a JVM .class file
    Compile { file: String },
    /// Compile and run a file on the JVM
    Run { file: String },
}

#[derive(Clone, ValueEnum)]
enum OutputFormat {
    Debug,
    Sexp,
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Commands::Parse { file, format } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = krypton_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            match format {
                OutputFormat::Debug => println!("{:#?}", module),
                OutputFormat::Sexp => println!("{}", krypton_parser::pretty::pretty_print(&module)),
            }
        }
        Commands::Fmt { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = krypton_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            println!("{}", krypton_parser::pretty::pretty_print(&module));
        }
        Commands::Compile { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = krypton_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            // Typecheck for error reporting
            if let Err(e) = krypton_typechecker::infer::infer_module(&module) {
                let diag =
                    krypton_typechecker::diagnostics::render_type_errors(&file, &source, &[e]);
                eprint!("{}", diag);
                process::exit(1);
            }
            // Derive class name from filename (e.g., hello.kr → Hello)
            let stem = std::path::Path::new(&file)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Main");
            let class_name = {
                let mut c = stem.chars();
                match c.next() {
                    None => "Main".to_string(),
                    Some(first) => {
                        first.to_uppercase().to_string() + c.as_str()
                    }
                }
            };
            match krypton_codegen::emit::compile_module(&module, &class_name) {
                Ok(classes) => {
                    for (name, bytes) in &classes {
                        let out_path = format!("{}.class", name);
                        std::fs::write(&out_path, bytes).unwrap_or_else(|e| {
                            eprintln!("Error writing {}: {}", out_path, e);
                            process::exit(1);
                        });
                        println!("Wrote {}", out_path);
                    }
                }
                Err(e) => {
                    eprintln!("Codegen error: {}", e);
                    process::exit(1);
                }
            }
        }
        Commands::Run { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = krypton_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            if let Err(e) = krypton_typechecker::infer::infer_module(&module) {
                let diag =
                    krypton_typechecker::diagnostics::render_type_errors(&file, &source, &[e]);
                eprint!("{}", diag);
                process::exit(1);
            }
            let stem = std::path::Path::new(&file)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Main");
            let class_name = {
                let mut c = stem.chars();
                match c.next() {
                    None => "Main".to_string(),
                    Some(first) => first.to_uppercase().to_string() + c.as_str(),
                }
            };
            match krypton_codegen::emit::compile_module(&module, &class_name) {
                Ok(classes) => {
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
                    let status = process::Command::new("java")
                        .arg("-cp")
                        .arg(dir.path())
                        .arg(&class_name)
                        .status()
                        .unwrap_or_else(|e| {
                            eprintln!("Error running java: {}", e);
                            process::exit(1);
                        });
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
            let (module, errors) = krypton_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = krypton_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            match krypton_typechecker::infer::infer_module(&module) {
                Ok(info) => {
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
        }
    }
}
