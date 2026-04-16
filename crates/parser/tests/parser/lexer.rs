use chumsky::Parser;
use insta::assert_yaml_snapshot;
use krypton_parser::lexer::lexer;
use krypton_parser::lexer::Token;

fn surface_lex(input: &str) -> Vec<Token<'_>> {
    let (tokens, errors) = lexer().parse(input).into_output_errors();
    assert!(errors.is_empty(), "unexpected lex errors: {errors:?}");
    tokens
        .unwrap()
        .into_iter()
        .map(|(tok, _span)| tok)
        .collect()
}

fn surface_lex_with_errors(input: &str) -> (Vec<Token<'_>>, usize) {
    let (tokens, errors) = lexer().parse(input).into_output_errors();
    let toks: Vec<_> = tokens
        .unwrap_or_default()
        .into_iter()
        .map(|(tok, _span)| tok)
        .collect();
    (toks, errors.len())
}

// --- Literals ---

#[test]
fn test_integer_literals() {
    assert_yaml_snapshot!(surface_lex("42 0 100"));
}

#[test]
fn test_float_literals() {
    assert_yaml_snapshot!(surface_lex("3.14 0.5"));
}

#[test]
fn test_bool_literals() {
    assert_yaml_snapshot!(surface_lex("true false"));
}

#[test]
fn test_string_literal() {
    assert_yaml_snapshot!(surface_lex("\"hello\""));
}

#[test]
fn test_string_escape_newline() {
    assert_yaml_snapshot!(surface_lex("\"hello\\nworld\""));
}

#[test]
fn test_string_escape_tab() {
    assert_yaml_snapshot!(surface_lex("\"a\\tb\""));
}

#[test]
fn test_string_escape_quote() {
    assert_yaml_snapshot!(surface_lex("\"say \\\"hi\\\"\""));
}

#[test]
fn test_string_escape_backslash() {
    assert_yaml_snapshot!(surface_lex("\"a\\\\b\""));
}

#[test]
fn test_string_escape_null() {
    assert_yaml_snapshot!(surface_lex("\"a\\0b\""));
}

#[test]
fn test_string_escape_carriage_return() {
    assert_yaml_snapshot!(surface_lex("\"a\\rb\""));
}

#[test]
fn test_string_invalid_escape() {
    let (_, error_count) = surface_lex_with_errors("\"a\\qb\"");
    assert!(error_count > 0, "expected error for invalid escape \\q");
}

#[test]
fn test_unit_literal() {
    assert_yaml_snapshot!(surface_lex("()"));
}

// --- Keywords ---

#[test]
fn test_surface_keywords() {
    assert_yaml_snapshot!(surface_lex(
        "fun let if else match type trait impl import use pub opaque where recur own deriving extern as"
    ));
}

// --- Operators ---

#[test]
fn test_multi_char_operators() {
    assert_yaml_snapshot!(surface_lex("== != <= >= => -> && ||"));
}

#[test]
fn test_single_char_operators() {
    assert_yaml_snapshot!(surface_lex("+ - * / < > = ! ? | . : , ; ~ _"));
}

// --- Punctuation / Delimiters ---

#[test]
fn test_delimiters() {
    assert_yaml_snapshot!(surface_lex("{ } ( ) [ ]"));
}

// --- Identifiers ---

#[test]
fn test_identifiers() {
    assert_yaml_snapshot!(surface_lex("foo bar MyType x1 snake_case"));
}

// --- Comments ---

#[test]
fn test_line_comment() {
    assert_yaml_snapshot!(surface_lex("# this is a comment\n42"));
}

#[test]
fn test_comment_after_token() {
    assert_yaml_snapshot!(surface_lex("42 # trailing comment"));
}

// --- Doc comments ---

#[test]
fn test_doc_comment_single_line() {
    assert_eq!(
        surface_lex("## hello world\n"),
        vec![Token::DocComment("hello world".to_string()), Token::Newline]
    );
}

#[test]
fn test_doc_comment_bare() {
    assert_eq!(
        surface_lex("##\n"),
        vec![Token::DocComment(String::new()), Token::Newline]
    );
}

#[test]
fn test_doc_comment_eof_no_newline() {
    assert_eq!(
        surface_lex("## trailing"),
        vec![Token::DocComment("trailing".to_string())]
    );
}

#[test]
fn test_doc_comment_bare_eof() {
    assert_eq!(surface_lex("##"), vec![Token::DocComment(String::new())]);
}

#[test]
fn test_doc_comment_triple_hash_is_regular() {
    assert_eq!(
        surface_lex("### not a doc\n42"),
        vec![Token::Newline, Token::Int(42)]
    );
}

#[test]
fn test_doc_comment_no_space_is_regular() {
    assert_eq!(
        surface_lex("##nospace\n42"),
        vec![Token::Newline, Token::Int(42)]
    );
}

#[test]
fn test_regular_comment_still_trivia() {
    assert_eq!(
        surface_lex("# this is a comment\n42"),
        vec![Token::Newline, Token::Int(42)]
    );
}

#[test]
fn test_doc_comment_attached_to_decl() {
    assert_eq!(
        surface_lex("## doc\nfun foo"),
        vec![
            Token::DocComment("doc".to_string()),
            Token::Newline,
            Token::Fun,
            Token::Ident("foo"),
        ]
    );
}

// --- Edge cases: operator disambiguation ---

#[test]
fn test_eq_vs_assign_vs_fat_arrow() {
    assert_yaml_snapshot!(surface_lex("== = =>"));
}

#[test]
fn test_arrow_vs_minus() {
    assert_yaml_snapshot!(surface_lex("-> -"));
}

#[test]
fn test_or_vs_pipe() {
    assert_yaml_snapshot!(surface_lex("|| |"));
}

#[test]
fn test_adjacent_tokens() {
    assert_yaml_snapshot!(surface_lex("foo(42)"));
}

// --- Error recovery ---

#[test]
fn test_error_recovery() {
    let (tokens, error_count) = surface_lex_with_errors("foo $ bar");
    assert!(error_count > 0, "expected at least one error for '$'");
    let non_error: Vec<_> = tokens
        .iter()
        .filter(|t| !matches!(t, Token::Error))
        .collect();
    assert!(
        non_error.len() >= 2,
        "expected at least 2 valid tokens, got {non_error:?}"
    );
}

// --- Borrow-mode `&` ---

#[test]
fn test_amp_single() {
    let toks = surface_lex("&");
    assert_eq!(toks, vec![Token::Amp]);
}

#[test]
fn test_amp_amp_still_one_token() {
    let toks = surface_lex("&&");
    assert_eq!(toks, vec![Token::And]);
}

#[test]
fn test_amp_then_amp() {
    let toks = surface_lex("& &");
    assert_eq!(toks, vec![Token::Amp, Token::Amp]);
}

// --- Spans ---

#[test]
fn test_spans() {
    let (tokens, _) = lexer().parse("fun foo").into_output_errors();
    let tokens = tokens.unwrap();
    // 'fun' at 0..3
    assert_eq!(tokens[0].1.start, 0);
    assert_eq!(tokens[0].1.end, 3);
    // 'foo' at 4..7
    assert_eq!(tokens[1].1.start, 4);
    assert_eq!(tokens[1].1.end, 7);
}

#[test]
fn test_multi_char_operator_spans() {
    let (tokens, _) = lexer().parse("== =>").into_output_errors();
    let tokens = tokens.unwrap();
    // '==' at 0..2
    assert_eq!(tokens[0].1.start, 0);
    assert_eq!(tokens[0].1.end, 2);
    // '=>' at 3..5
    assert_eq!(tokens[1].1.start, 3);
    assert_eq!(tokens[1].1.end, 5);
}
