use chumsky::prelude::*;
use serde::Serialize;
use std::fmt;

pub type Span = SimpleSpan;
pub type Spanned<T> = (T, Span);

#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Token<'src> {
    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    // Literals
    Int(i64),
    Float(f64),
    String(&'src str),
    Bool(bool),
    // Identifiers & keywords
    Ident(&'src str),
    // Keywords
    Def,
    Fn,
    Let,
    If,
    Match,
    Type,
    Do,
    Receive,
    Recur,
    Send,
    Spawn,
    Self_,
    Own,
    Trait,
    Impl,
    Import,
    List,
    Tuple,
    Deriving,
    // Operators & punctuation
    Plus,
    Minus,
    Star,
    Slash,
    Eq,
    Neq,
    Lt,
    Gt,
    Le,
    Ge,
    Question,
    Pipe,
    Dot,
    Colon,
    Underscore,
    // Error recovery
    Error,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::Int(n) => write!(f, "{n}"),
            Token::Float(n) => write!(f, "{n}"),
            Token::String(s) => write!(f, "\"{s}\""),
            Token::Bool(b) => write!(f, "{b}"),
            Token::Ident(s) => write!(f, "{s}"),
            Token::Def => write!(f, "def"),
            Token::Fn => write!(f, "fn"),
            Token::Let => write!(f, "let"),
            Token::If => write!(f, "if"),
            Token::Match => write!(f, "match"),
            Token::Type => write!(f, "type"),
            Token::Do => write!(f, "do"),
            Token::Receive => write!(f, "receive"),
            Token::Recur => write!(f, "recur"),
            Token::Send => write!(f, "send"),
            Token::Spawn => write!(f, "spawn"),
            Token::Self_ => write!(f, "self"),
            Token::Own => write!(f, "own"),
            Token::Trait => write!(f, "trait"),
            Token::Impl => write!(f, "impl"),
            Token::Import => write!(f, "import"),
            Token::List => write!(f, "list"),
            Token::Tuple => write!(f, "tuple"),
            Token::Deriving => write!(f, "deriving"),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Eq => write!(f, "=="),
            Token::Neq => write!(f, "!="),
            Token::Lt => write!(f, "<"),
            Token::Gt => write!(f, ">"),
            Token::Le => write!(f, "<="),
            Token::Ge => write!(f, ">="),
            Token::Question => write!(f, "?"),
            Token::Pipe => write!(f, "|"),
            Token::Dot => write!(f, "."),
            Token::Colon => write!(f, ":"),
            Token::Underscore => write!(f, "_"),
            Token::Error => write!(f, "<error>"),
        }
    }
}

pub fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, Span>>> {
    // Number literals: integers and floats
    let num = text::int(10)
        .then(just('.').then(text::digits(10)).or_not())
        .to_slice()
        .map(|s: &str| {
            if s.contains('.') {
                Token::Float(s.parse().unwrap())
            } else {
                Token::Int(s.parse().unwrap())
            }
        });

    // String literals
    let string = just('"')
        .ignore_then(none_of('"').repeated().to_slice())
        .then_ignore(just('"'))
        .map(Token::String);

    // Identifiers and keywords
    let ident = text::ascii::ident().map(|s: &str| match s {
        "def" => Token::Def,
        "fn" => Token::Fn,
        "let" => Token::Let,
        "if" => Token::If,
        "match" => Token::Match,
        "type" => Token::Type,
        "do" => Token::Do,
        "receive" => Token::Receive,
        "recur" => Token::Recur,
        "send" => Token::Send,
        "spawn" => Token::Spawn,
        "self" => Token::Self_,
        "own" => Token::Own,
        "trait" => Token::Trait,
        "impl" => Token::Impl,
        "import" => Token::Import,
        "list" => Token::List,
        "tuple" => Token::Tuple,
        "deriving" => Token::Deriving,
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        _ => Token::Ident(s),
    });

    // Multi-char operators (must come before single-char)
    let multi_op = choice((
        just("==").to(Token::Eq),
        just("!=").to(Token::Neq),
        just("<=").to(Token::Le),
        just(">=").to(Token::Ge),
    ));

    // Single-char operators
    let single_op = choice((
        just('+').to(Token::Plus),
        just('-').to(Token::Minus),
        just('*').to(Token::Star),
        just('/').to(Token::Slash),
        just('<').to(Token::Lt),
        just('>').to(Token::Gt),
        just('?').to(Token::Question),
        just('|').to(Token::Pipe),
        just('.').to(Token::Dot),
        just(':').to(Token::Colon),
        just('_').to(Token::Underscore),
    ));

    // Delimiters
    let delim = choice((
        just('(').to(Token::LParen),
        just(')').to(Token::RParen),
        just('[').to(Token::LBracket),
        just(']').to(Token::RBracket),
    ));

    // Comments: # to end of line
    let comment = just('#')
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    let token = choice((num, string, multi_op, single_op, delim, ident));

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}
