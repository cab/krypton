// Lexer for S-expression syntax
// Tokenizes input into a stream for the parser

use chumsky::prelude::*;

pub type Span = SimpleSpan<usize>;
pub type Spanned<T> = (T, Span);

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,

    // Literals
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),

    // Identifiers and keywords
    Ident(String),

    // Special symbols
    Caret,      // ^
    Pipe,       // |
    Colon,      // :
    Arrow,      // ->
    FatArrow,   // =>
    Dot,        // .
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::Int(n) => write!(f, "{}", n),
            Token::Float(n) => write!(f, "{}", n),
            Token::String(s) => write!(f, "\"{}\"", s),
            Token::Bool(b) => write!(f, "{}", b),
            Token::Ident(s) => write!(f, "{}", s),
            Token::Caret => write!(f, "^"),
            Token::Pipe => write!(f, "|"),
            Token::Colon => write!(f, ":"),
            Token::Arrow => write!(f, "->"),
            Token::FatArrow => write!(f, "=>"),
            Token::Dot => write!(f, "."),
        }
    }
}

pub fn lexer<'src>() -> impl Parser<'src, &'src str, Vec<Spanned<Token>>, extra::Err<Rich<'src, char>>>
{
    // Operators and symbols - try longer tokens FIRST before numbers
    let arrow = just("->").to(Token::Arrow);
    let fat_arrow = just("=>").to(Token::FatArrow);

    // Integer literal: digits only (no negative sign - that's an operator)
    let int = text::int(10)
        .to_slice()
        .map(|s: &str| s.parse::<i64>().unwrap())
        .map(Token::Int);

    // Float literal: digits, dot, digits (no negative sign)
    let float = text::int(10)
        .then(just('.'))
        .then(text::int(10))
        .to_slice()
        .map(|s: &str| s.parse::<f64>().unwrap())
        .map(Token::Float);

    // String literal: quoted text with escape sequences
    let escape = just('\\')
        .then(choice((
            just('\\'),
            just('"'),
            just('n').to('\n'),
            just('r').to('\r'),
            just('t').to('\t'),
        )))
        .map(|(_, c)| c);

    let string = none_of("\\\"")
        .or(escape)
        .repeated()
        .collect::<String>()
        .delimited_by(just('"'), just('"'))
        .map(Token::String);

    // Operators as identifiers (for S-expressions, + - * / etc are just names)
    // Note: We exclude | and ^ here since they have special token types
    let op_ident = one_of("+-*/=<>!&")
        .repeated()
        .at_least(1)
        .to_slice()
        .map(|s: &str| Token::Ident(s.to_string()));

    // Keywords and identifiers
    let ident = text::ident().map(|s: &str| match s {
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        _ => Token::Ident(s.to_string()),
    });

    // Other symbols
    let caret = just('^').to(Token::Caret);
    let pipe = just('|').to(Token::Pipe);
    let colon = just(':').to(Token::Colon);
    let dot = just('.').to(Token::Dot);

    // Delimiters
    let lparen = just('(').to(Token::LParen);
    let rparen = just(')').to(Token::RParen);
    let lbracket = just('[').to(Token::LBracket);
    let rbracket = just(']').to(Token::RBracket);
    let lbrace = just('{').to(Token::LBrace);
    let rbrace = just('}').to(Token::RBrace);

    // Single token parser - try in priority order
    // IMPORTANT: arrow must come before op_ident to prevent parsing "->" as operator
    let token = choice((
        arrow,
        fat_arrow,
        float,
        int,
        string,
        ident,
        op_ident,
        caret,
        pipe,
        colon,
        dot,
        lparen,
        rparen,
        lbracket,
        rbracket,
        lbrace,
        rbrace,
    ));

    // Comments: ; to end of line
    let comment = just(';')
        .then(any().and_is(text::newline().not()).repeated())
        .padded();

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .repeated()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_integers() {
        let tokens = lexer().parse("42 0").unwrap();
        assert_eq!(tokens[0].0, Token::Int(42));
        assert_eq!(tokens[1].0, Token::Int(0));
    }

    #[test]
    fn test_lex_floats() {
        let tokens = lexer().parse("3.14 1.0").unwrap();
        assert_eq!(tokens[0].0, Token::Float(3.14));
        assert_eq!(tokens[1].0, Token::Float(1.0));
    }

    #[test]
    fn test_lex_negative_as_operator() {
        // Negative sign is lexed as an operator, not part of the number
        let tokens = lexer().parse("- 17").unwrap();
        assert_eq!(tokens[0].0, Token::Ident("-".to_string()));
        assert_eq!(tokens[1].0, Token::Int(17));
    }

    #[test]
    fn test_lex_strings() {
        let tokens = lexer().parse(r#""hello" "world" "with\nnewline""#).unwrap();
        assert_eq!(tokens[0].0, Token::String("hello".to_string()));
        assert_eq!(tokens[1].0, Token::String("world".to_string()));
        assert_eq!(tokens[2].0, Token::String("with\nnewline".to_string()));
    }

    #[test]
    fn test_lex_booleans() {
        let tokens = lexer().parse("true false").unwrap();
        assert_eq!(tokens[0].0, Token::Bool(true));
        assert_eq!(tokens[1].0, Token::Bool(false));
    }

    #[test]
    fn test_lex_identifiers() {
        let tokens = lexer().parse("x foo bar_baz Point").unwrap();
        assert_eq!(tokens[0].0, Token::Ident("x".to_string()));
        assert_eq!(tokens[1].0, Token::Ident("foo".to_string()));
        assert_eq!(tokens[2].0, Token::Ident("bar_baz".to_string()));
        assert_eq!(tokens[3].0, Token::Ident("Point".to_string()));
    }

    #[test]
    fn test_lex_delimiters() {
        let tokens = lexer().parse("( ) [ ] { }").unwrap();
        assert_eq!(tokens[0].0, Token::LParen);
        assert_eq!(tokens[1].0, Token::RParen);
        assert_eq!(tokens[2].0, Token::LBracket);
        assert_eq!(tokens[3].0, Token::RBracket);
        assert_eq!(tokens[4].0, Token::LBrace);
        assert_eq!(tokens[5].0, Token::RBrace);
    }

    #[test]
    fn test_lex_symbols() {
        let tokens = lexer().parse("^ : -> =>").unwrap();
        assert_eq!(tokens[0].0, Token::Caret);
        assert_eq!(tokens[1].0, Token::Colon);
        assert_eq!(tokens[2].0, Token::Arrow);
        assert_eq!(tokens[3].0, Token::FatArrow);
    }

    #[test]
    fn test_lex_pipe_in_context() {
        // Pipe is used in sum types: (| variant1 variant2)
        let tokens = lexer().parse("(| A B)").unwrap();
        assert_eq!(tokens[0].0, Token::LParen);
        assert_eq!(tokens[1].0, Token::Pipe);
        assert_eq!(tokens[2].0, Token::Ident("A".to_string()));
        assert_eq!(tokens[3].0, Token::Ident("B".to_string()));
        assert_eq!(tokens[4].0, Token::RParen);
    }

    #[test]
    fn test_lex_comments() {
        let tokens = lexer()
            .parse(
                "; This is a comment\n\
                 42 ; inline comment\n\
                 ; another comment\n\
                 x",
            )
            .unwrap();
        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].0, Token::Int(42));
        assert_eq!(tokens[1].0, Token::Ident("x".to_string()));
    }

    #[test]
    fn test_lex_sexpr() {
        let tokens = lexer().parse("(fn [x y] (+ x y))").unwrap();
        assert_eq!(tokens[0].0, Token::LParen);
        assert_eq!(tokens[1].0, Token::Ident("fn".to_string()));
        assert_eq!(tokens[2].0, Token::LBracket);
        assert_eq!(tokens[3].0, Token::Ident("x".to_string()));
        assert_eq!(tokens[4].0, Token::Ident("y".to_string()));
        assert_eq!(tokens[5].0, Token::RBracket);
        assert_eq!(tokens[6].0, Token::LParen);
        assert_eq!(tokens[7].0, Token::Ident("+".to_string()));
        assert_eq!(tokens[8].0, Token::Ident("x".to_string()));
        assert_eq!(tokens[9].0, Token::Ident("y".to_string()));
        assert_eq!(tokens[10].0, Token::RParen);
        assert_eq!(tokens[11].0, Token::RParen);
    }
}
