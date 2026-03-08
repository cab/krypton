use chumsky::prelude::*;

use crate::lexer::{Span, Spanned, Token};

pub fn surface_lexer<'src>(
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
        "open" => Token::Open,
        "where" => Token::Where,
        "recur" => Token::Recur,
        "own" => Token::Own,
        "deriving" => Token::Deriving,
        "extern" => Token::Extern,
        "as" => Token::As,
        "do" => Token::Do,
        "self" => Token::Self_,
        "list" => Token::List,
        "tuple" => Token::Tuple,
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
