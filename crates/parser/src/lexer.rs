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
    LBrace,
    RBrace,
    Newline,
    // Literals
    Int(i64),
    Float(f64),
    String(String),
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
    Recur,
    Self_,
    Own,
    Trait,
    Impl,
    Import,
    Tuple,
    Deriving,
    Extern,
    Fun,
    Where,
    Else,
    Pub,
    Opaque,
    Use,
    As,
    Shared,
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
    DotDot,
    Dot,
    Colon,
    Underscore,
    FatArrow,
    Arrow,
    Assign,
    Comma,
    Semicolon,
    And,
    Or,
    Bang,
    Tilde,
    At,
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
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::Newline => write!(f, "\\n"),
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
            Token::Recur => write!(f, "recur"),
            Token::Self_ => write!(f, "self"),
            Token::Own => write!(f, "own"),
            Token::Trait => write!(f, "trait"),
            Token::Impl => write!(f, "impl"),
            Token::Import => write!(f, "import"),
            Token::Tuple => write!(f, "tuple"),
            Token::Deriving => write!(f, "deriving"),
            Token::Extern => write!(f, "extern"),
            Token::Fun => write!(f, "fun"),
            Token::Where => write!(f, "where"),
            Token::Else => write!(f, "else"),
            Token::Pub => write!(f, "pub"),
            Token::Opaque => write!(f, "opaque"),
            Token::Use => write!(f, "use"),
            Token::As => write!(f, "as"),
            Token::Shared => write!(f, "shared"),
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
            Token::DotDot => write!(f, ".."),
            Token::Dot => write!(f, "."),
            Token::Colon => write!(f, ":"),
            Token::Underscore => write!(f, "_"),
            Token::FatArrow => write!(f, "=>"),
            Token::Arrow => write!(f, "->"),
            Token::Assign => write!(f, "="),
            Token::Comma => write!(f, ","),
            Token::Semicolon => write!(f, ";"),
            Token::And => write!(f, "&&"),
            Token::Or => write!(f, "||"),
            Token::Bang => write!(f, "!"),
            Token::Tilde => write!(f, "~"),
            Token::At => write!(f, "@"),
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

    // String literals with escape sequences
    let escape = just('\\').ignore_then(
        choice((
            just('\\').to('\\'),
            just('"').to('"'),
            just('n').to('\n'),
            just('t').to('\t'),
            just('r').to('\r'),
            just('0').to('\0'),
        ))
        .or(any().validate(|c, e, emitter| {
            emitter.emit(Rich::custom(
                e.span(),
                format!("invalid escape sequence: \\{c}"),
            ));
            c
        })),
    );

    let string_char = none_of("\\\"").or(escape);

    let string = string_char
        .repeated()
        .collect::<String>()
        .delimited_by(just('"'), just('"'))
        .map(Token::String);

    // Identifiers and keywords (including _prefixed like _foo, _0)
    let ident = just('_')
        .then(any().filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_').repeated().at_least(1))
        .to_slice()
        .map(|s: &str| Token::Ident(s))
        .or(text::ascii::ident().map(|s: &str| match s {
        "fun" => Token::Fun,
        "def" => Token::Def,
        "fn" => Token::Fn,
        "let" => Token::Let,
        "if" => Token::If,
        "else" => Token::Else,
        "match" => Token::Match,
        "type" => Token::Type,
        "trait" => Token::Trait,
        "impl" => Token::Impl,
        "import" => Token::Import,
        "use" => Token::Use,
        "pub" => Token::Pub,
        "opaque" => Token::Opaque,
        "where" => Token::Where,
        "recur" => Token::Recur,
        "own" => Token::Own,
        "deriving" => Token::Deriving,
        "extern" => Token::Extern,
        "as" => Token::As,
        "shared" => Token::Shared,
        "do" => Token::Do,
        "self" => Token::Self_,
        "tuple" => Token::Tuple,
        "true" => Token::Bool(true),
        "false" => Token::Bool(false),
        "_" => Token::Underscore,
        _ => Token::Ident(s),
    }));

    // Multi-char operators (must come before single-char)
    let multi_op = choice((
        just("==").to(Token::Eq),
        just("!=").to(Token::Neq),
        just("<=").to(Token::Le),
        just(">=").to(Token::Ge),
        just("=>").to(Token::FatArrow),
        just("->").to(Token::Arrow),
        just("&&").to(Token::And),
        just("||").to(Token::Or),
        just("..").to(Token::DotDot),
    ));

    // Single-char operators and punctuation
    let single_op = choice((
        just('+').to(Token::Plus),
        just('-').to(Token::Minus),
        just('*').to(Token::Star),
        just('/').to(Token::Slash),
        just('<').to(Token::Lt),
        just('>').to(Token::Gt),
        just('=').to(Token::Assign),
        just('!').to(Token::Bang),
        just('?').to(Token::Question),
        just('|').to(Token::Pipe),
        just('.').to(Token::Dot),
        just(':').to(Token::Colon),
        just(',').to(Token::Comma),
        just(';').to(Token::Semicolon),
        just('~').to(Token::Tilde),
        just('@').to(Token::At),
        just('_').to(Token::Underscore),
    ));

    // Delimiters
    let delim = choice((
        just('(').to(Token::LParen),
        just(')').to(Token::RParen),
        just('[').to(Token::LBracket),
        just(']').to(Token::RBracket),
        just('{').to(Token::LBrace),
        just('}').to(Token::RBrace),
    ));

    // Significant newlines are emitted as tokens. Horizontal whitespace and comments are trivia.
    let newline = just('\n').to(Token::Newline);

    // Comments: # to end of line, but do not consume the newline itself.
    let comment = just('#')
        .then(any().and_is(just('\n').not()).repeated())
        .ignored();

    let trivia = choice((
        one_of(" \t\r").ignored(),
        comment,
    ))
    .repeated();

    let token = choice((newline, num, string, multi_op, ident, single_op, delim));

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(trivia)
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}
