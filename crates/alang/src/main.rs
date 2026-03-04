use clap::{Parser, Subcommand, ValueEnum};
use std::process;

#[derive(Parser)]
#[command(name = "alang")]
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
            let (module, errors) = alang_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = alang_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            match format {
                OutputFormat::Debug => println!("{:#?}", module),
                OutputFormat::Sexp => println!("{}", alang_parser::pretty::pretty_print(&module)),
            }
        }
        Commands::Fmt { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = alang_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = alang_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            println!("{}", alang_parser::pretty::pretty_print(&module));
        }
        Commands::Compile { file } => {
            let source = std::fs::read_to_string(&file).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file, e);
                process::exit(1);
            });
            let (module, errors) = alang_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = alang_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            // Typecheck for error reporting
            if let Err(e) = alang_typechecker::infer::infer_module(&module) {
                let diag =
                    alang_typechecker::diagnostics::render_type_errors(&file, &source, &[e]);
                eprint!("{}", diag);
                process::exit(1);
            }
            // Derive class name from filename (e.g., hello.al → Hello)
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
            match alang_codegen::emit::compile_module(&module, &class_name) {
                Ok(bytes) => {
                    let out_path = format!("{}.class", class_name);
                    std::fs::write(&out_path, &bytes).unwrap_or_else(|e| {
                        eprintln!("Error writing {}: {}", out_path, e);
                        process::exit(1);
                    });
                    println!("Wrote {}", out_path);
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
            let (module, errors) = alang_parser::parser::parse(&source);
            if !errors.is_empty() {
                let diag = alang_parser::diagnostics::render_errors(&file, &source, &errors);
                eprint!("{}", diag);
                process::exit(1);
            }
            match alang_typechecker::infer::infer_module(&module) {
                Ok(schemes) => {
                    for (name, scheme) in &schemes {
                        println!("{} : {}", name, scheme);
                    }
                }
                Err(e) => {
                    let diag =
                        alang_typechecker::diagnostics::render_type_errors(&file, &source, &[e]);
                    eprint!("{}", diag);
                    process::exit(1);
                }
            }
        }
    }
}
