use alang_parser::parse_program_with_filename;
use std::env;
use std::fs;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("Usage: {} <file.al>", args[0]);
        process::exit(1);
    }

    let filename = &args[1];
    let source = fs::read_to_string(filename).unwrap_or_else(|err| {
        eprintln!("Error reading file '{}': {}", filename, err);
        process::exit(1);
    });

    match parse_program_with_filename(&source, filename) {
        Ok(program) => {
            println!("Successfully parsed {} declarations!", program.decls.len());
        }
        Err(error) => {
            eprint!("{}", error);
            process::exit(1);
        }
    }
}
