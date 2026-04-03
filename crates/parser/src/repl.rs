//! Backend-agnostic REPL helpers: input classification and synthetic source generation.
//!
//! These operate purely on source text — no IR or typechecker types involved.

/// Classification of a REPL input line.
#[derive(Debug, PartialEq)]
pub enum ReplInputKind {
    LetBinding { name: String, rhs: String },
    FunDef { name: String, source: String },
    BareExpr { source: String },
}

/// Classify REPL input into its kind.
pub fn classify_input(input: &str) -> ReplInputKind {
    let trimmed = input.trim();

    // Check for let binding: "let <name> = <rhs>"
    if trimmed.starts_with("let ") {
        let rest = trimmed[4..].trim_start();
        if let Some(eq_pos) = rest.find('=') {
            let name = rest[..eq_pos].trim();
            if !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_') {
                let rhs = rest[eq_pos + 1..].trim();
                return ReplInputKind::LetBinding {
                    name: name.to_string(),
                    rhs: rhs.to_string(),
                };
            }
        }
    }

    // Check for function def: "fun <name>..."
    if trimmed.starts_with("fun ") {
        let rest = trimmed[4..].trim_start();
        let name_end = rest
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(rest.len());
        let name = &rest[..name_end];
        if !name.is_empty() {
            return ReplInputKind::FunDef {
                name: name.to_string(),
                source: trimmed.to_string(),
            };
        }
    }

    ReplInputKind::BareExpr {
        source: trimmed.to_string(),
    }
}

/// Build synthetic module source that wraps user input for compilation.
///
/// `bindings` is `(name, type_annotation_str)` for each prior let-binding.
/// `fun_defs` is `(name, source, type_display)` for each prior function def.
pub fn build_synthetic_source(
    kind: &ReplInputKind,
    bindings: &[(String, String)],
    fun_defs: &[(String, String, String)],
) -> String {
    let mut source = String::new();

    // Emit all prior function definitions as top-level functions
    for (_name, fsrc, _type_display) in fun_defs {
        source.push_str(fsrc);
        source.push('\n');
    }

    // Build parameter list from prior let-bindings
    let params: Vec<String> = bindings
        .iter()
        .map(|(name, type_str)| format!("{}: {}", name, type_str))
        .collect();
    let param_str = params.join(", ");

    match kind {
        ReplInputKind::LetBinding { name: _, rhs } => {
            source.push_str(&format!("fun __eval({}) = {}\n", param_str, rhs));
        }
        ReplInputKind::FunDef { name: _, source: fsrc } => {
            source.push_str(fsrc);
            source.push('\n');
            source.push_str(&format!("fun __eval({}) -> Unit = ()\n", param_str));
        }
        ReplInputKind::BareExpr { source: expr } => {
            source.push_str(&format!("fun __eval({}) = {}\n", param_str, expr));
        }
    }

    source
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_let_binding() {
        assert_eq!(
            classify_input("let x = 42"),
            ReplInputKind::LetBinding {
                name: "x".to_string(),
                rhs: "42".to_string(),
            }
        );
    }

    #[test]
    fn classify_fun_def() {
        assert_eq!(
            classify_input("fun f(x) = x + 1"),
            ReplInputKind::FunDef {
                name: "f".to_string(),
                source: "fun f(x) = x + 1".to_string(),
            }
        );
    }

    #[test]
    fn classify_bare_expr() {
        assert_eq!(
            classify_input("1 + 2"),
            ReplInputKind::BareExpr {
                source: "1 + 2".to_string(),
            }
        );
    }

    #[test]
    fn wrap_bare_expr_parses() {
        let kind = ReplInputKind::BareExpr {
            source: "1 + 2".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_let_parses() {
        let kind = ReplInputKind::LetBinding {
            name: "x".to_string(),
            rhs: "42".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_fun_def_parses() {
        let kind = ReplInputKind::FunDef {
            name: "f".to_string(),
            source: "fun f(x: Int) -> Int = x + 1".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_with_prior_bindings() {
        let kind = ReplInputKind::BareExpr {
            source: "x + 1".to_string(),
        };
        let bindings = vec![("x".to_string(), "Int".to_string())];
        let source = build_synthetic_source(&kind, &bindings, &[]);
        assert!(source.contains("fun __eval(x: Int) = x + 1"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_with_prior_fun_defs() {
        let kind = ReplInputKind::BareExpr {
            source: "add(1, 2)".to_string(),
        };
        let fun_defs = vec![(
            "add".to_string(),
            "fun add(a: Int, b: Int) -> Int = a + b".to_string(),
            "(Int, Int) -> Int".to_string(),
        )];
        let source = build_synthetic_source(&kind, &[], &fun_defs);
        assert!(source.contains("fun add(a: Int, b: Int) -> Int = a + b"));
        assert!(source.contains("fun __eval() = add(1, 2)"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_fun_def_does_not_return_function_name() {
        let kind = ReplInputKind::FunDef {
            name: "a".to_string(),
            source: "fun a(x: Int, y: Int) -> Int = x + y".to_string(),
        };
        let source = build_synthetic_source(&kind, &[], &[]);
        assert!(!source.contains("= a\n"));
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }
}
