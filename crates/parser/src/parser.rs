use chumsky::input::ValueInput;
use chumsky::prelude::*;

use crate::ast::*;
use crate::lexer::{Span as LexSpan, Token};

fn to_span(s: LexSpan) -> Span {
    (s.start, s.end)
}

fn pattern_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Pattern, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    recursive(|pattern| {
        let wildcard = select! { Token::Underscore => () }.map_with(|_, e| Pattern::Wildcard {
            span: to_span(e.span()),
        });

        let lit_pat = select! {
            Token::Int(n) => Lit::Int(n),
            Token::Float(n) => Lit::Float(n),
            Token::String(s) => Lit::String(s.to_string()),
            Token::Bool(b) => Lit::Bool(b),
        }
        .map_with(|value, e| Pattern::Lit {
            value,
            span: to_span(e.span()),
        });

        let var_pat = select! { Token::Ident(s) => s.to_string() }.map_with(|name, e| {
            Pattern::Var {
                name,
                span: to_span(e.span()),
            }
        });

        // (tuple p1 p2 ...)
        let tuple_pat = just(Token::Tuple)
            .ignore_then(pattern.clone().repeated().at_least(1).collect::<Vec<_>>())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|elements, e| Pattern::Tuple {
                elements,
                span: to_span(e.span()),
            });

        // (Constructor args...)
        let constructor_pat = select! { Token::Ident(s) => s.to_string() }
            .then(pattern.repeated().collect::<Vec<_>>())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|(name, args), e| Pattern::Constructor {
                name,
                args,
                span: to_span(e.span()),
            });

        choice((wildcard, lit_pat, tuple_pat, constructor_pat, var_pat))
    })
}

pub fn expr_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Expr, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    recursive(|expr| {
        // --- Atoms ---
        let lit = select! {
            Token::Int(n) => Lit::Int(n),
            Token::Float(n) => Lit::Float(n),
            Token::String(s) => Lit::String(s.to_string()),
            Token::Bool(b) => Lit::Bool(b),
        }
        .map_with(|value, e| Expr::Lit {
            value,
            span: to_span(e.span()),
        });

        let var = select! { Token::Ident(s) => s.to_string() }.map_with(|name, e| Expr::Var {
            name,
            span: to_span(e.span()),
        });

        let self_ = just(Token::Self_).map_with(|_, e| Expr::Self_ {
            span: to_span(e.span()),
        });

        let atom = choice((lit, self_, var));

        // --- Operator token to BinOp ---
        let bin_op_token = select! {
            Token::Plus => BinOp::Add,
            Token::Minus => BinOp::Sub,
            Token::Star => BinOp::Mul,
            Token::Slash => BinOp::Div,
            Token::Eq => BinOp::Eq,
            Token::Neq => BinOp::Neq,
            Token::Lt => BinOp::Lt,
            Token::Gt => BinOp::Gt,
            Token::Le => BinOp::Le,
            Token::Ge => BinOp::Ge,
        };

        // --- Param parser for lambda ---
        let param = select! { Token::Ident(s) => s.to_string() }.map_with(|name, e| Param {
            name,
            ty: None,
            span: to_span(e.span()),
        });

        let params_list = param
            .repeated()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LBracket), just(Token::RBracket));

        // --- Pattern parser ---
        let pattern = pattern_parser();

        // --- Match arm: (pattern body) ---
        let match_arm = pattern
            .clone()
            .then(expr.clone())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|(pattern, body), e| MatchArm {
                pattern,
                body,
                span: to_span(e.span()),
            });

        // --- Parenthesized forms (each returns a closure |Span| -> Expr) ---
        type Builder = Box<dyn FnOnce(Span) -> Expr>;

        // (op lhs rhs)
        let binary_op = bin_op_token
            .then(expr.clone())
            .then(expr.clone())
            .map(|((op, lhs), rhs)| -> Builder {
                Box::new(move |span| Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span,
                })
            });

        // (fn [params] body)
        let fn_form = just(Token::Fn)
            .ignore_then(params_list)
            .then(expr.clone())
            .map(|(params, body)| -> Builder {
                Box::new(move |span| Expr::Lambda {
                    params,
                    return_type: None,
                    body: Box::new(body),
                    span,
                })
            });

        // (let name value)
        let let_form = just(Token::Let)
            .ignore_then(select! { Token::Ident(s) => s.to_string() })
            .then(expr.clone())
            .map(|(name, value)| -> Builder {
                Box::new(move |span| Expr::Let {
                    name,
                    value: Box::new(value),
                    body: None,
                    span,
                })
            });

        // (do expr...)
        let do_form = just(Token::Do)
            .ignore_then(expr.clone().repeated().at_least(1).collect::<Vec<_>>())
            .map(|exprs| -> Builder { Box::new(move |span| Expr::Do { exprs, span }) });

        // (if cond then else)
        let if_form = just(Token::If)
            .ignore_then(expr.clone())
            .then(expr.clone())
            .then(expr.clone())
            .map(|((cond, then_), else_)| -> Builder {
                Box::new(move |span| Expr::If {
                    cond: Box::new(cond),
                    then_: Box::new(then_),
                    else_: Box::new(else_),
                    span,
                })
            });

        // (match scrutinee (pat body)...)
        let match_form = just(Token::Match)
            .ignore_then(expr.clone())
            .then(match_arm.clone().repeated().at_least(1).collect::<Vec<_>>())
            .map(|(scrutinee, arms)| -> Builder {
                Box::new(move |span| Expr::Match {
                    scrutinee: Box::new(scrutinee),
                    arms,
                    span,
                })
            });

        // (. expr field)
        let dot_form = just(Token::Dot)
            .ignore_then(expr.clone())
            .then(select! { Token::Ident(s) => s.to_string() })
            .map(|(target, field)| -> Builder {
                Box::new(move |span| Expr::FieldAccess {
                    expr: Box::new(target),
                    field,
                    span,
                })
            });

        // (? expr)
        let question_form = just(Token::Question)
            .ignore_then(expr.clone())
            .map(|inner| -> Builder {
                Box::new(move |span| Expr::QuestionMark {
                    expr: Box::new(inner),
                    span,
                })
            });

        // (list expr...)
        let list_form = just(Token::List)
            .ignore_then(expr.clone().repeated().collect::<Vec<_>>())
            .map(|elements| -> Builder { Box::new(move |span| Expr::List { elements, span }) });

        // (tuple expr...)
        let tuple_form = just(Token::Tuple)
            .ignore_then(expr.clone().repeated().collect::<Vec<_>>())
            .map(|elements| -> Builder { Box::new(move |span| Expr::Tuple { elements, span }) });

        // (recur args...)
        let recur_form = just(Token::Recur)
            .ignore_then(expr.clone().repeated().collect::<Vec<_>>())
            .map(|args| -> Builder { Box::new(move |span| Expr::Recur { args, span }) });

        // (send target message)
        let send_form = just(Token::Send)
            .ignore_then(expr.clone())
            .then(expr.clone())
            .map(|(target, message)| -> Builder {
                Box::new(move |span| Expr::Send {
                    target: Box::new(target),
                    message: Box::new(message),
                    span,
                })
            });

        // (spawn func args...)
        let spawn_form = just(Token::Spawn)
            .ignore_then(expr.clone())
            .then(expr.clone().repeated().collect::<Vec<_>>())
            .map(|(func, args)| -> Builder {
                Box::new(move |span| Expr::Spawn {
                    func: Box::new(func),
                    args,
                    span,
                })
            });

        // (receive (pat body)...)
        let receive_form = just(Token::Receive)
            .ignore_then(match_arm.repeated().at_least(1).collect::<Vec<_>>())
            .map(|arms| -> Builder {
                Box::new(move |span| Expr::Receive {
                    arms,
                    timeout: None,
                    span,
                })
            });

        // (f args...) — application, must be last
        let app_form = expr
            .clone()
            .then(expr.clone().repeated().collect::<Vec<_>>())
            .map(|(func, args)| -> Builder {
                Box::new(move |span| Expr::App {
                    func: Box::new(func),
                    args,
                    span,
                })
            });

        let paren_form = choice((
            binary_op,
            fn_form,
            let_form,
            do_form,
            if_form,
            match_form,
            dot_form,
            question_form,
            list_form,
            tuple_form,
            recur_form,
            send_form,
            spawn_form,
            receive_form,
            app_form,
        ))
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|builder, e| builder(to_span(e.span())))
        .recover_with(via_parser(nested_delimiters(
            Token::LParen,
            Token::RParen,
            [(Token::LBracket, Token::RBracket)],
            |span| Expr::Lit {
                value: Lit::Unit,
                span: to_span(span),
            },
        )));

        atom.or(paren_form)
    })
}

pub fn parse_expr<'tokens, 'src: 'tokens>(
    tokens: &'tokens [(Token<'src>, LexSpan)],
) -> (Option<Expr>, Vec<Rich<'tokens, Token<'src>, LexSpan>>) {
    let eoi: LexSpan = tokens
        .last()
        .map(|(_, s)| (s.end..s.end).into())
        .unwrap_or((0..0).into());
    let input = tokens.map(eoi, |(t, s)| (t, s));
    expr_parser().parse(input).into_output_errors()
}
