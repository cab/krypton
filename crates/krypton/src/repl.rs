use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

/// Count net open brackets in a line, skipping string literals and comments.
fn bracket_delta(line: &str) -> i32 {
    let mut delta: i32 = 0;
    let chars: Vec<char> = line.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            // Line comment — skip rest
            '/' if i + 1 < chars.len() && chars[i + 1] == '/' => break,
            // String literal — skip to closing quote
            '"' => {
                i += 1;
                while i < chars.len() {
                    if chars[i] == '\\' {
                        i += 1; // skip escaped char
                    } else if chars[i] == '"' {
                        break;
                    }
                    i += 1;
                }
            }
            '(' | '[' | '{' => delta += 1,
            ')' | ']' | '}' => delta -= 1,
            _ => {}
        }
        i += 1;
    }
    delta
}

#[derive(Debug, PartialEq)]
enum ReplCommand {
    Quit,
    Help,
    Reset,
    Type(String),
    Kill(String),
    Env,
    Load(String),
    Unknown(String),
}

fn parse_command(input: &str) -> Option<ReplCommand> {
    if !input.starts_with(':') {
        return None;
    }
    let trimmed = input[1..].trim();
    let (cmd, arg) = match trimmed.split_once(char::is_whitespace) {
        Some((c, a)) => (c, a.trim().to_string()),
        None => (trimmed, String::new()),
    };
    Some(match cmd {
        "quit" | "q" => ReplCommand::Quit,
        "help" | "h" => ReplCommand::Help,
        "reset" => ReplCommand::Reset,
        "type" | "t" => ReplCommand::Type(arg),
        "kill" => ReplCommand::Kill(arg),
        "env" => ReplCommand::Env,
        "load" | "l" => ReplCommand::Load(arg),
        other => ReplCommand::Unknown(other.to_string()),
    })
}

fn print_help() {
    println!("Commands:");
    println!("  :help, :h       Show this help message");
    println!("  :quit, :q       Exit the REPL");
    println!("  :reset          Clear the current environment");
    println!("  :type, :t <e>   Show the type of an expression");
    println!("  :env            Show all bindings in scope");
    println!("  :load, :l <f>   Load and evaluate a file");
    println!("  :kill <name>    Remove a binding from scope");
}

fn history_path() -> Option<std::path::PathBuf> {
    std::env::var("HOME")
        .ok()
        .map(|h| std::path::PathBuf::from(h).join(".krypton/repl_history"))
}

pub fn run_repl() -> Result<(), Box<dyn std::error::Error>> {
    println!("Krypton v0.1 — interactive REPL");
    println!("Type :help for commands.");

    let hist_path = history_path();

    let mut rl = DefaultEditor::new()?;
    if let Some(ref path) = hist_path {
        let _ = rl.load_history(path);
    }

    let mut bracket_depth: i32 = 0;
    let mut input_buffer = String::new();

    loop {
        let prompt = if bracket_depth > 0 { ".. " } else { "> " };
        match rl.readline(prompt) {
            Ok(line) => {
                bracket_depth += bracket_delta(&line);
                if !input_buffer.is_empty() {
                    input_buffer.push('\n');
                }
                input_buffer.push_str(&line);

                if bracket_depth <= 0 {
                    bracket_depth = 0;
                    let input = input_buffer.trim().to_string();
                    input_buffer.clear();

                    if input.is_empty() {
                        continue;
                    }

                    let _ = rl.add_history_entry(&input);

                    if let Some(cmd) = parse_command(&input) {
                        match cmd {
                            ReplCommand::Quit => break,
                            ReplCommand::Help => print_help(),
                            ReplCommand::Reset => println!("Environment reset."),
                            ReplCommand::Env => println!("(no bindings)"),
                            ReplCommand::Type(expr) => {
                                println!("(type of: {})", expr);
                            }
                            ReplCommand::Kill(name) => {
                                println!("(killed: {})", name);
                            }
                            ReplCommand::Load(file) => {
                                println!("(loading: {})", file);
                            }
                            ReplCommand::Unknown(cmd) => {
                                println!("Unknown command: :{}", cmd);
                                println!("Type :help for a list of commands.");
                            }
                        }
                    } else {
                        // Stub eval: echo raw input
                        println!("{}", input);
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                // Ctrl-C: clear current input
                bracket_depth = 0;
                input_buffer.clear();
            }
            Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("Error: {}", e);
                break;
            }
        }
    }

    if let Some(ref path) = hist_path {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).ok();
        }
        rl.save_history(path).ok();
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bracket_delta_balanced() {
        assert_eq!(bracket_delta("let x = 1"), 0);
        assert_eq!(bracket_delta("{ x + 1 }"), 0);
        assert_eq!(bracket_delta("(a, b)"), 0);
    }

    #[test]
    fn test_bracket_delta_open() {
        assert_eq!(bracket_delta("let f = fun(x) {"), 1);
        assert_eq!(bracket_delta("{"), 1);
        assert_eq!(bracket_delta("(["), 2);
    }

    #[test]
    fn test_bracket_delta_close() {
        assert_eq!(bracket_delta("}"), -1);
        assert_eq!(bracket_delta("})"), -2);
        assert_eq!(bracket_delta("x + 1 }"), -1);
    }

    #[test]
    fn test_bracket_delta_skips_strings() {
        assert_eq!(bracket_delta(r#"let s = "hello { world""#), 0);
        assert_eq!(bracket_delta(r#"let s = "escaped \" brace {""#), 0);
    }

    #[test]
    fn test_bracket_delta_skips_comments() {
        assert_eq!(bracket_delta("let x = 1 // { not a bracket"), 0);
    }

    #[test]
    fn test_is_complete() {
        // Balanced input is complete (delta == 0)
        assert_eq!(bracket_delta("let x = { 1 + 2 }"), 0);
        // Unbalanced input is incomplete (delta > 0)
        assert!(bracket_delta("let f = fun(x) {") > 0);
    }

    #[test]
    fn test_parse_command_quit() {
        assert_eq!(parse_command(":quit"), Some(ReplCommand::Quit));
        assert_eq!(parse_command(":q"), Some(ReplCommand::Quit));
    }

    #[test]
    fn test_parse_command_help() {
        assert_eq!(parse_command(":help"), Some(ReplCommand::Help));
        assert_eq!(parse_command(":h"), Some(ReplCommand::Help));
    }

    #[test]
    fn test_parse_command_reset() {
        assert_eq!(parse_command(":reset"), Some(ReplCommand::Reset));
    }

    #[test]
    fn test_parse_command_with_args() {
        assert_eq!(
            parse_command(":type x + 1"),
            Some(ReplCommand::Type("x + 1".to_string()))
        );
        assert_eq!(
            parse_command(":load foo.kr"),
            Some(ReplCommand::Load("foo.kr".to_string()))
        );
    }

    #[test]
    fn test_parse_command_unknown() {
        assert_eq!(
            parse_command(":foobar"),
            Some(ReplCommand::Unknown("foobar".to_string()))
        );
    }

    #[test]
    fn test_parse_command_not_a_command() {
        assert_eq!(parse_command("1 + 2"), None);
        assert_eq!(parse_command("let x = 1"), None);
    }
}
