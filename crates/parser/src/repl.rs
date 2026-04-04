//! Backend-agnostic REPL helpers: input classification and synthetic source generation.
//!
//! These operate purely on source text — no IR or typechecker types involved.

/// Classification of a REPL input line.
#[derive(Debug, PartialEq)]
pub enum ReplInputKind {
    LetBinding { name: String, rhs: String },
    FunDef { name: String, source: String },
    TypeDef { name: String, source: String },
    TraitDef { name: String, source: String },
    ImplDef { key: String, source: String },
    Import { source: String },
    ExternDef { source: String },
    BareExpr { source: String },
}

/// All prior REPL declarations, passed to `build_synthetic_source`.
#[derive(Debug, Default)]
pub struct ReplDeclarations {
    pub imports: Vec<String>,
    pub type_defs: Vec<(String, String)>,
    pub trait_defs: Vec<(String, String)>,
    pub impl_defs: Vec<(String, String)>,
    pub extern_defs: Vec<String>,
    pub fun_defs: Vec<(String, String, String)>,
    pub bindings: Vec<(String, String)>,
}

/// Extract the first identifier after skipping a keyword prefix.
fn extract_ident_after(s: &str, prefix: &str) -> Option<String> {
    let rest = s.strip_prefix(prefix)?.trim_start();
    let end = rest
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(rest.len());
    let name = &rest[..end];
    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
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

    // Type def: "type ", "pub type ", "opaque type "
    if trimmed.starts_with("type ")
        || trimmed.starts_with("pub type ")
        || trimmed.starts_with("opaque type ")
    {
        let keyword = if trimmed.starts_with("pub type ") {
            "pub type "
        } else if trimmed.starts_with("opaque type ") {
            "opaque type "
        } else {
            "type "
        };
        if let Some(name) = extract_ident_after(trimmed, keyword) {
            return ReplInputKind::TypeDef {
                name,
                source: trimmed.to_string(),
            };
        }
    }

    // Trait def: "trait ", "pub trait "
    if trimmed.starts_with("trait ") || trimmed.starts_with("pub trait ") {
        let keyword = if trimmed.starts_with("pub trait ") {
            "pub trait "
        } else {
            "trait "
        };
        if let Some(name) = extract_ident_after(trimmed, keyword) {
            return ReplInputKind::TraitDef {
                name,
                source: trimmed.to_string(),
            };
        }
    }

    // Impl def: "impl "
    if trimmed.starts_with("impl ") {
        let key = trimmed
            .find('{')
            .map(|i| trimmed[5..i].trim())
            .unwrap_or(&trimmed[5..])
            .to_string();
        return ReplInputKind::ImplDef {
            key,
            source: trimmed.to_string(),
        };
    }

    // Import: "import ", "pub import "
    if trimmed.starts_with("import ") || trimmed.starts_with("pub import ") {
        return ReplInputKind::Import {
            source: trimmed.to_string(),
        };
    }

    // Extern: "extern "
    if trimmed.starts_with("extern ") {
        return ReplInputKind::ExternDef {
            source: trimmed.to_string(),
        };
    }

    ReplInputKind::BareExpr {
        source: trimmed.to_string(),
    }
}

/// Build synthetic module source that wraps user input for compilation.
///
/// `show_bare_expr`: when `true` and input is `BareExpr`, wraps the expression
/// to return `(__r, show(__r))` so the REPL can display via the Show trait.
pub fn build_synthetic_source(
    kind: &ReplInputKind,
    decls: &ReplDeclarations,
    show_bare_expr: bool,
) -> String {
    let mut source = String::new();

    // 1. Imports (stored + current)
    for src in &decls.imports {
        source.push_str(src);
        source.push('\n');
    }
    if let ReplInputKind::Import { source: src } = kind {
        source.push_str(src);
        source.push('\n');
    }

    // 2. Type defs
    for (_name, src) in &decls.type_defs {
        source.push_str(src);
        source.push('\n');
    }
    if let ReplInputKind::TypeDef { source: src, .. } = kind {
        source.push_str(src);
        source.push('\n');
    }

    // 3. Trait defs
    for (_name, src) in &decls.trait_defs {
        source.push_str(src);
        source.push('\n');
    }
    if let ReplInputKind::TraitDef { source: src, .. } = kind {
        source.push_str(src);
        source.push('\n');
    }

    // 4. Impl defs
    for (_key, src) in &decls.impl_defs {
        source.push_str(src);
        source.push('\n');
    }
    if let ReplInputKind::ImplDef { source: src, .. } = kind {
        source.push_str(src);
        source.push('\n');
    }

    // 5. Extern defs
    for src in &decls.extern_defs {
        source.push_str(src);
        source.push('\n');
    }
    if let ReplInputKind::ExternDef { source: src } = kind {
        source.push_str(src);
        source.push('\n');
    }

    // 6. Fun defs (stored + current)
    for (_name, fsrc, _type_display) in &decls.fun_defs {
        source.push_str(fsrc);
        source.push('\n');
    }
    if let ReplInputKind::FunDef { source: fsrc, .. } = kind {
        source.push_str(fsrc);
        source.push('\n');
    }

    // 7. __eval wrapper
    let params: Vec<String> = decls
        .bindings
        .iter()
        .map(|(name, type_str)| format!("{}: {}", name, type_str))
        .collect();
    let param_str = params.join(", ");

    match kind {
        ReplInputKind::LetBinding { rhs, .. } => {
            source.push_str(&format!("fun __eval({}) = {}\n", param_str, rhs));
        }
        ReplInputKind::BareExpr { source: expr } => {
            if show_bare_expr {
                source.push_str(&format!(
                    "fun __eval({}) = {{\n  let __r = {}\n  (__r, show(__r))\n}}\n",
                    param_str, expr
                ));
            } else {
                source.push_str(&format!("fun __eval({}) = {}\n", param_str, expr));
            }
        }
        // All declaration kinds: __eval returns Unit
        ReplInputKind::FunDef { .. }
        | ReplInputKind::TypeDef { .. }
        | ReplInputKind::TraitDef { .. }
        | ReplInputKind::ImplDef { .. }
        | ReplInputKind::Import { .. }
        | ReplInputKind::ExternDef { .. } => {
            source.push_str(&format!("fun __eval({}) -> Unit = ()\n", param_str));
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
    fn classify_type_def() {
        assert_eq!(
            classify_input("type Color = Red | Green | Blue"),
            ReplInputKind::TypeDef {
                name: "Color".to_string(),
                source: "type Color = Red | Green | Blue".to_string(),
            }
        );
    }

    #[test]
    fn classify_pub_type_def() {
        assert_eq!(
            classify_input("pub type Foo = Bar"),
            ReplInputKind::TypeDef {
                name: "Foo".to_string(),
                source: "pub type Foo = Bar".to_string(),
            }
        );
    }

    #[test]
    fn classify_opaque_type_def() {
        assert_eq!(
            classify_input("opaque type Id = Int"),
            ReplInputKind::TypeDef {
                name: "Id".to_string(),
                source: "opaque type Id = Int".to_string(),
            }
        );
    }

    #[test]
    fn classify_trait_def() {
        assert_eq!(
            classify_input("trait Show[a] { fun show(x: a) -> String }"),
            ReplInputKind::TraitDef {
                name: "Show".to_string(),
                source: "trait Show[a] { fun show(x: a) -> String }".to_string(),
            }
        );
    }

    #[test]
    fn classify_pub_trait_def() {
        assert_eq!(
            classify_input("pub trait Eq[a] { fun eq(x: a, y: a) -> Bool }"),
            ReplInputKind::TraitDef {
                name: "Eq".to_string(),
                source: "pub trait Eq[a] { fun eq(x: a, y: a) -> Bool }".to_string(),
            }
        );
    }

    #[test]
    fn classify_impl_def() {
        assert_eq!(
            classify_input("impl Show[Int] { fun show(x: Int) -> String = int_to_string(x) }"),
            ReplInputKind::ImplDef {
                key: "Show[Int]".to_string(),
                source: "impl Show[Int] { fun show(x: Int) -> String = int_to_string(x) }"
                    .to_string(),
            }
        );
    }

    #[test]
    fn classify_import() {
        assert_eq!(
            classify_input("import core/list.{List}"),
            ReplInputKind::Import {
                source: "import core/list.{List}".to_string(),
            }
        );
    }

    #[test]
    fn classify_pub_import() {
        assert_eq!(
            classify_input("pub import core/list.{List}"),
            ReplInputKind::Import {
                source: "pub import core/list.{List}".to_string(),
            }
        );
    }

    #[test]
    fn classify_extern_def() {
        assert_eq!(
            classify_input("extern jvm \"java.lang.Math\" { fun abs(x: Int) -> Int }"),
            ReplInputKind::ExternDef {
                source: "extern jvm \"java.lang.Math\" { fun abs(x: Int) -> Int }".to_string(),
            }
        );
    }

    #[test]
    fn wrap_bare_expr_parses() {
        let kind = ReplInputKind::BareExpr {
            source: "1 + 2".to_string(),
        };
        let source = build_synthetic_source(&kind, &ReplDeclarations::default(), false);
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_let_parses() {
        let kind = ReplInputKind::LetBinding {
            name: "x".to_string(),
            rhs: "42".to_string(),
        };
        let source = build_synthetic_source(&kind, &ReplDeclarations::default(), false);
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_fun_def_parses() {
        let kind = ReplInputKind::FunDef {
            name: "f".to_string(),
            source: "fun f(x: Int) -> Int = x + 1".to_string(),
        };
        let source = build_synthetic_source(&kind, &ReplDeclarations::default(), false);
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_with_prior_bindings() {
        let kind = ReplInputKind::BareExpr {
            source: "x + 1".to_string(),
        };
        let decls = ReplDeclarations {
            bindings: vec![("x".to_string(), "Int".to_string())],
            ..Default::default()
        };
        let source = build_synthetic_source(&kind, &decls, false);
        assert!(source.contains("fun __eval(x: Int) = x + 1"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_with_prior_fun_defs() {
        let kind = ReplInputKind::BareExpr {
            source: "add(1, 2)".to_string(),
        };
        let decls = ReplDeclarations {
            fun_defs: vec![(
                "add".to_string(),
                "fun add(a: Int, b: Int) -> Int = a + b".to_string(),
                "(Int, Int) -> Int".to_string(),
            )],
            ..Default::default()
        };
        let source = build_synthetic_source(&kind, &decls, false);
        assert!(source.contains("fun add(a: Int, b: Int) -> Int = a + b"));
        assert!(source.contains("fun __eval() = add(1, 2)"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_bare_expr_show() {
        let kind = ReplInputKind::BareExpr {
            source: "1 + 2".to_string(),
        };
        let source = build_synthetic_source(&kind, &ReplDeclarations::default(), true);
        assert!(source.contains("let __r = 1 + 2"));
        assert!(source.contains("(__r, show(__r))"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_bare_expr_show_with_bindings() {
        let kind = ReplInputKind::BareExpr {
            source: "x + 1".to_string(),
        };
        let decls = ReplDeclarations {
            bindings: vec![("x".to_string(), "Int".to_string())],
            ..Default::default()
        };
        let source = build_synthetic_source(&kind, &decls, true);
        assert!(source.contains("fun __eval(x: Int)"));
        assert!(source.contains("let __r = x + 1"));
        assert!(source.contains("(__r, show(__r))"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_fun_def_does_not_return_function_name() {
        let kind = ReplInputKind::FunDef {
            name: "a".to_string(),
            source: "fun a(x: Int, y: Int) -> Int = x + y".to_string(),
        };
        let source = build_synthetic_source(&kind, &ReplDeclarations::default(), false);
        assert!(!source.contains("= a\n"));
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_type_def_parses() {
        let kind = ReplInputKind::TypeDef {
            name: "Color".to_string(),
            source: "type Color = Red | Green | Blue".to_string(),
        };
        let source = build_synthetic_source(&kind, &ReplDeclarations::default(), false);
        assert!(source.contains("type Color = Red | Green | Blue"));
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn wrap_import_parses() {
        let kind = ReplInputKind::Import {
            source: "import core/list.{List, map}".to_string(),
        };
        let source = build_synthetic_source(&kind, &ReplDeclarations::default(), false);
        assert!(source.contains("import core/list.{List, map}"));
        assert!(source.contains("fun __eval() -> Unit = ()"));
        let (_, errors) = crate::parser::parse(&source);
        assert!(errors.is_empty(), "Parse errors: {:?}", errors);
    }

    #[test]
    fn synthetic_source_emit_order() {
        let decls = ReplDeclarations {
            imports: vec!["import core/list.{List}".to_string()],
            type_defs: vec![("Color".to_string(), "type Color = Red".to_string())],
            trait_defs: vec![(
                "Describe".to_string(),
                "trait Describe[a] { fun describe(x: a) -> String }".to_string(),
            )],
            impl_defs: vec![(
                "Describe[Color]".to_string(),
                "impl Describe[Color] { fun describe(x: Color) -> String = \"color\" }".to_string(),
            )],
            extern_defs: vec!["extern jvm \"Foo\" { fun bar() -> Int }".to_string()],
            fun_defs: vec![(
                "helper".to_string(),
                "fun helper() -> Int = 1".to_string(),
                "() -> Int".to_string(),
            )],
            bindings: vec![("x".to_string(), "Int".to_string())],
        };
        let kind = ReplInputKind::BareExpr {
            source: "x".to_string(),
        };
        let source = build_synthetic_source(&kind, &decls, false);

        // Verify ordering: imports < types < traits < impls < externs < funs < __eval
        let import_pos = source.find("import core/list").unwrap();
        let type_pos = source.find("type Color").unwrap();
        let trait_pos = source.find("trait Describe").unwrap();
        let impl_pos = source.find("impl Describe").unwrap();
        let extern_pos = source.find("extern jvm").unwrap();
        let fun_pos = source.find("fun helper").unwrap();
        let eval_pos = source.find("fun __eval").unwrap();

        assert!(import_pos < type_pos);
        assert!(type_pos < trait_pos);
        assert!(trait_pos < impl_pos);
        assert!(impl_pos < extern_pos);
        assert!(extern_pos < fun_pos);
        assert!(fun_pos < eval_pos);
    }

    #[test]
    fn type_def_with_prior_decls() {
        let decls = ReplDeclarations {
            type_defs: vec![("Foo".to_string(), "type Foo = A | B".to_string())],
            ..Default::default()
        };
        let kind = ReplInputKind::TypeDef {
            name: "Bar".to_string(),
            source: "type Bar = X | Y".to_string(),
        };
        let source = build_synthetic_source(&kind, &decls, false);
        assert!(source.contains("type Foo = A | B"));
        assert!(source.contains("type Bar = X | Y"));
        assert!(source.contains("fun __eval() -> Unit = ()"));
    }
}
