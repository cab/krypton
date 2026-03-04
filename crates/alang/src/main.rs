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
    }
}
