use chumsky::input::{MapExtra, ValueInput};
use chumsky::pratt::*;
use chumsky::prelude::*;

use crate::ast::*;
use crate::diagnostics::{ErrorCode, ParseError};
use crate::lexer::{self, Span as LexSpan, Token};

fn ignored_newlines<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, (), extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    just(Token::Newline).repeated().ignored()
}

fn symbol<'tokens, 'src: 'tokens, I>(
    tok: Token<'src>,
) -> impl Parser<'tokens, I, Token<'src>, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    ignored_newlines()
        .ignore_then(just(tok))
        .then_ignore(ignored_newlines())
}

fn closing_symbol<'tokens, 'src: 'tokens, I>(
    tok: Token<'src>,
) -> impl Parser<'tokens, I, Token<'src>, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    ignored_newlines().ignore_then(just(tok))
}

fn stmt_sep<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, (), extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    choice((
        just(Token::Semicolon).ignored(),
        just(Token::Newline).repeated().at_least(1).ignored(),
    ))
    .repeated()
    .at_least(1)
    .ignored()
}

fn to_span(s: LexSpan) -> Span {
    (s.start, s.end)
}

fn is_uppercase(s: &str) -> bool {
    s.starts_with(|c: char| c.is_uppercase())
}

fn type_expr_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, TypeExpr, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    recursive(|ty| {
        // Named/Var/Qualified: bare ident, or module.Type
        let named_or_var = select! { Token::Ident(s) => s.to_string() }
            .then(
                symbol(Token::Dot)
                    .ignore_then(select! { Token::Ident(s) => s.to_string() })
                    .or_not(),
            )
            .map_with(|(name, qualified), e| {
                if let Some(member) = qualified {
                    TypeExpr::Qualified {
                        module: name,
                        name: member,
                        span: to_span(e.span()),
                    }
                } else if is_uppercase(&name) {
                    TypeExpr::Named {
                        name,
                        span: to_span(e.span()),
                    }
                } else {
                    TypeExpr::Var {
                        name,
                        span: to_span(e.span()),
                    }
                }
            });

        // ~Type → Own
        let own_type = symbol(Token::Tilde)
            .ignore_then(ty.clone())
            .map_with(|inner, e| TypeExpr::Own {
                inner: Box::new(inner),
                span: to_span(e.span()),
            });

        // Parenthesized: tuple type or fn type or grouping
        // (Type, Type) → Tuple
        // (Type, Type) -> RetType → Fn
        let paren_type = ty
            .clone()
            .separated_by(symbol(Token::Comma))
            .collect::<Vec<_>>()
            .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen))
            .then(symbol(Token::Arrow).ignore_then(ty.clone()).or_not())
            .map_with(|(params, ret), e| {
                if let Some(ret) = ret {
                    TypeExpr::Fn {
                        params,
                        ret: Box::new(ret),
                        span: to_span(e.span()),
                    }
                } else {
                    TypeExpr::Tuple {
                        elements: params,
                        span: to_span(e.span()),
                    }
                }
            });

        // Wildcard: _ in type position (for partial application in impl heads)
        let wildcard_type = symbol(Token::Underscore).map_with(|_, e| TypeExpr::Wildcard {
            span: to_span(e.span()),
        });

        // Base type (without generic application)
        let base_type = choice((own_type, paren_type, wildcard_type, named_or_var));

        // Generic application: Name[args]
        base_type
            .clone()
            .then(
                ty.clone()
                    .separated_by(symbol(Token::Comma))
                    .at_least(1)
                    .collect::<Vec<_>>()
                    .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
                    .or_not(),
            )
            .map_with(|(base, args), e| match args {
                Some(args) => {
                    if let TypeExpr::Named { name, .. }
                    | TypeExpr::Var { name, .. }
                    | TypeExpr::Qualified { name, .. } = base
                    {
                        TypeExpr::App {
                            name,
                            args,
                            span: to_span(e.span()),
                        }
                    } else {
                        base
                    }
                }
                None => base,
            })
    })
}

fn pattern_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Pattern, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    recursive(|pattern| {
        let wildcard = symbol(Token::Underscore).map_with(|_, e| Pattern::Wildcard {
            span: to_span(e.span()),
        });

        let lit_pat = select! {
            Token::Int(n) => Lit::Int(n),
            Token::Float(n) => Lit::Float(n),
            Token::String(s) => Lit::String(s),
            Token::Bool(b) => Lit::Bool(b),
        }
        .map_with(|value, e| Pattern::Lit {
            value,
            span: to_span(e.span()),
        });

        // Constructor: Name(args) or bare Name (uppercase)
        let constructor_pat = select! { Token::Ident(s) if is_uppercase(s) => s.to_string() }
            .then(
                pattern
                    .clone()
                    .separated_by(symbol(Token::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen))
                    .or_not(),
            )
            .map_with(|(name, args), e| Pattern::Constructor {
                name,
                args: args.unwrap_or_default(),
                span: to_span(e.span()),
            });

        // Struct pattern: Name { field1, field2, .. }
        let struct_field = select! { Token::Ident(s) => s.to_string() }
            .then(symbol(Token::Colon).ignore_then(pattern.clone()).or_not())
            .map(|(name, pat)| {
                let p = pat.unwrap_or_else(|| Pattern::Var {
                    name: name.clone(),
                    span: (0, 0),
                });
                (name, p)
            });

        let struct_pat = select! { Token::Ident(s) if is_uppercase(s) => s.to_string() }
            .then(
                struct_field
                    .separated_by(symbol(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .then(
                        symbol(Token::Comma)
                            .ignore_then(symbol(Token::DotDot))
                            .or_not(),
                    )
                    .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace)),
            )
            .map_with(|(name, (fields, rest)), e| Pattern::StructPat {
                name,
                fields,
                rest: rest.is_some(),
                span: to_span(e.span()),
            });

        // Tuple pattern: (a, b)
        let tuple_pat = pattern
            .clone()
            .separated_by(symbol(Token::Comma))
            .at_least(2)
            .collect::<Vec<_>>()
            .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen))
            .map_with(|elements, e| Pattern::Tuple {
                elements,
                span: to_span(e.span()),
            });

        // Variable pattern: lowercase ident
        let var_pat =
            select! { Token::Ident(s) if !is_uppercase(s) => s.to_string() }.map_with(|name, e| {
                Pattern::Var {
                    name,
                    span: to_span(e.span()),
                }
            });

        // Unit pattern: ()
        let unit_pat = symbol(Token::LParen)
            .then(closing_symbol(Token::RParen))
            .map_with(|_, e| Pattern::Lit {
                value: Lit::Unit,
                span: to_span(e.span()),
            });

        // Atomic pattern (without or-patterns)
        let atomic = choice((
            wildcard,
            lit_pat,
            unit_pat,
            struct_pat,
            tuple_pat,
            constructor_pat,
            var_pat,
        ));

        // Or-pattern: A | B
        atomic.clone().foldl(
            symbol(Token::Pipe).ignore_then(atomic).repeated(),
            |_lhs, _rhs| {
                // For now, or-patterns are not in the AST — just return the rhs
                // TODO: Add OrPattern to AST
                _rhs
            },
        )
    })
}

#[allow(clippy::type_complexity)]
fn expr_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Expr, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    recursive(|expr| {
        let ty = type_expr_parser();
        let pattern = pattern_parser();

        // --- Atoms ---

        // Unit literal: ()
        let unit_lit = symbol(Token::LParen)
            .then(closing_symbol(Token::RParen))
            .map_with(|_, e| Expr::Lit {
                value: Lit::Unit,
                span: to_span(e.span()),
            });

        let lit = select! {
            Token::Int(n) => Lit::Int(n),
            Token::Float(n) => Lit::Float(n),
            Token::String(s) => Lit::String(s),
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

        // Block: { stmt; stmt; expr }
        let block_expr = {
            // Statement in a block: let binding or expression
            let let_stmt = symbol(Token::Let)
                .ignore_then(
                    // Try pattern destructuring first
                    pattern
                        .clone()
                        .then(symbol(Token::Colon).ignore_then(ty.clone()).or_not())
                        .then_ignore(symbol(Token::Assign))
                        .then(expr.clone())
                        .map(|((pat, ty_ann), value)| {
                            // Check if it's a simple var pattern
                            if let Pattern::Var { name, .. } = &pat {
                                Expr::Let {
                                    name: name.clone(),
                                    ty: ty_ann,
                                    value: Box::new(value),
                                    body: None,
                                    span: (0, 0), // will be overwritten
                                }
                            } else {
                                Expr::LetPattern {
                                    pattern: pat,
                                    ty: ty_ann,
                                    value: Box::new(value),
                                    body: None,
                                    span: (0, 0),
                                }
                            }
                        }),
                )
                .map_with(|mut e, extra| {
                    match &mut e {
                        Expr::Let { span, .. } | Expr::LetPattern { span, .. } => {
                            *span = to_span(extra.span());
                        }
                        _ => {}
                    }
                    e
                });

            let stmt = let_stmt.or(expr.clone());

            stmt.clone()
                .separated_by(stmt_sep())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace))
                .map_with(|exprs, e| {
                    if exprs.is_empty() {
                        Expr::Lit {
                            value: Lit::Unit,
                            span: to_span(e.span()),
                        }
                    } else if exprs.len() == 1 {
                        // Single expression block — just return the expr with the block span
                        let mut single = exprs.into_iter().next().unwrap();
                        // For consistency, wrap in Do if it's a let
                        match &single {
                            Expr::Let { .. } | Expr::LetPattern { .. } => Expr::Do {
                                exprs: vec![single],
                                span: to_span(e.span()),
                            },
                            _ => {
                                // Update span to cover the block
                                set_span(&mut single, to_span(e.span()));
                                single
                            }
                        }
                    } else {
                        Expr::Do {
                            exprs,
                            span: to_span(e.span()),
                        }
                    }
                })
        };

        // If expression: if cond { then } else { else }
        let if_expr = symbol(Token::If)
            .ignore_then(expr.clone())
            .then(expr.clone())
            .then(symbol(Token::Else).ignore_then(expr.clone()).or_not())
            .map_with(|((cond, then_), else_), e| Expr::If {
                cond: Box::new(cond),
                then_: Box::new(then_),
                else_: Box::new(else_.unwrap_or(Expr::Lit {
                    value: Lit::Unit,
                    span: to_span(e.span()),
                })),
                span: to_span(e.span()),
            });

        // Match expression: match expr { pat => body, pat if guard => body }
        let match_arm = pattern
            .clone()
            .then(symbol(Token::If).ignore_then(expr.clone()).or_not())
            .then_ignore(symbol(Token::FatArrow))
            .then(expr.clone())
            .map_with(|((pat, guard), body), e| MatchArm {
                pattern: pat,
                guard: guard.map(Box::new),
                body,
                span: to_span(e.span()),
            });

        let match_expr = symbol(Token::Match)
            .ignore_then(expr.clone())
            .then(
                match_arm
                    .separated_by(symbol(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace)),
            )
            .map_with(|(scrutinee, arms), e| Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms,
                span: to_span(e.span()),
            });

        // Recur: recur(args)
        let recur_expr = symbol(Token::Recur)
            .ignore_then(
                expr.clone()
                    .separated_by(symbol(Token::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen)),
            )
            .map_with(|args, e| Expr::Recur {
                args,
                span: to_span(e.span()),
            });

        // List literal: [1, 2, 3]
        let list_lit = expr
            .clone()
            .separated_by(symbol(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
            .map_with(|elements, e| Expr::List {
                elements,
                span: to_span(e.span()),
            });

        // Struct literal: Name { field = val, ... }
        let struct_field = select! { Token::Ident(s) => s.to_string() }
            .then(symbol(Token::Assign).ignore_then(expr.clone()).or_not())
            .map(|(name, val)| {
                let v = val.unwrap_or_else(|| Expr::Var {
                    name: name.clone(),
                    span: (0, 0),
                });
                (name, v)
            });

        let struct_lit = select! { Token::Ident(s) if is_uppercase(s) => s.to_string() }
            .then(
                struct_field
                    .clone()
                    .separated_by(symbol(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace)),
            )
            .map_with(|(name, fields), e| Expr::StructLit {
                name,
                fields,
                span: to_span(e.span()),
            });

        // Struct update: { base | field = val, ... }
        let struct_update = symbol(Token::LBrace)
            .ignore_then(expr.clone())
            .then_ignore(symbol(Token::Pipe))
            .then(
                struct_field
                    .clone()
                    .separated_by(symbol(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(closing_symbol(Token::RBrace))
            .map_with(|(base, fields), e| Expr::StructUpdate {
                base: Box::new(base),
                fields,
                span: to_span(e.span()),
            });

        // Lambda: x -> body, (x, y) -> body, (x: Int) -> body
        // Lambda params with optional type annotation
        let lambda_param = select! { Token::Ident(s) => s.to_string() }
            .then(symbol(Token::Colon).ignore_then(ty.clone()).or_not())
            .map_with(|(name, ty_ann), e| Param {
                name,
                ty: ty_ann,
                span: to_span(e.span()),
            });

        // Zero-arg lambda: () -> body
        let zero_lambda = symbol(Token::LParen)
            .then(closing_symbol(Token::RParen))
            .then_ignore(symbol(Token::Arrow))
            .then(expr.clone())
            .map_with(|(_, body), e| Expr::Lambda {
                params: vec![],
                body: Box::new(body),
                span: to_span(e.span()),
            });

        // Multi-param lambda: (x, y) -> body or (x: Int, y: Int) -> body
        let multi_lambda = lambda_param
            .clone()
            .separated_by(symbol(Token::Comma))
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen))
            .then_ignore(symbol(Token::Arrow))
            .then(expr.clone())
            .map_with(|(params, body), e| Expr::Lambda {
                params,
                body: Box::new(body),
                span: to_span(e.span()),
            });

        // Single-param lambda: x -> body
        let single_lambda = select! { Token::Ident(s) => s.to_string() }
            .map_with(|name, e| Param {
                name,
                ty: None,
                span: to_span(e.span()),
            })
            .then_ignore(symbol(Token::Arrow))
            .then(expr.clone())
            .map_with(|(param, body), e| Expr::Lambda {
                params: vec![param],
                body: Box::new(body),
                span: to_span(e.span()),
            });

        // Parenthesized expression or tuple: (expr) or (expr, expr)
        let paren_or_tuple = expr
            .clone()
            .separated_by(symbol(Token::Comma))
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen))
            .map_with(|mut elements, e| {
                if elements.len() == 1 {
                    elements.remove(0)
                } else {
                    Expr::Tuple {
                        elements,
                        span: to_span(e.span()),
                    }
                }
            });

        let raw_atom = choice((
            zero_lambda,
            unit_lit,
            lit,
            recur_expr,
            if_expr,
            match_expr,
            struct_update,
            list_lit,
            struct_lit,
            multi_lambda,
            single_lambda,
            block_expr,
            paren_or_tuple,
            var,
        ));

        // --- Postfix chain: call, field access, UFCS, ? ---
        // Applied to atoms BEFORE Pratt so that `a.x == b.y` works correctly.
        #[derive(Clone, Debug)]
        enum Postfix {
            Call(Vec<Expr>, LexSpan),
            TypeArgs(Vec<TypeExpr>, LexSpan),
            FieldAccess(String, LexSpan),
            Ufcs(String, Vec<TypeExpr>, Vec<Expr>, LexSpan),
            Question(LexSpan),
        }

        // Function call: expr(args)
        let call_postfix = expr
            .clone()
            .separated_by(symbol(Token::Comma))
            .collect::<Vec<_>>()
            .delimited_by(
                just(Token::LParen).then_ignore(ignored_newlines()),
                closing_symbol(Token::RParen),
            )
            .map_with(|args, e| Postfix::Call(args, e.span()));

        let type_args_postfix = ty
            .clone()
            .separated_by(symbol(Token::Comma))
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(
                just(Token::LBracket).then_ignore(ignored_newlines()),
                closing_symbol(Token::RBracket),
            )
            .map_with(|type_args, e| Postfix::TypeArgs(type_args, e.span()));

        // Dot access: .ident or .ident(args)
        let dot_postfix = symbol(Token::Dot)
            .ignore_then(select! { Token::Ident(s) => s.to_string() })
            .then(
                ty.clone()
                    .separated_by(symbol(Token::Comma))
                    .at_least(1)
                    .collect::<Vec<_>>()
                    .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
                    .or_not(),
            )
            .then(
                expr.clone()
                    .separated_by(symbol(Token::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen))
                    .or_not(),
            )
            .map_with(|((field, type_args), args), e| {
                if let Some(args) = args {
                    Postfix::Ufcs(field, type_args.unwrap_or_default(), args, e.span())
                } else {
                    Postfix::FieldAccess(field, e.span())
                }
            });

        // Question mark: expr?
        let question_postfix =
            closing_symbol(Token::Question).map_with(|_, e| Postfix::Question(e.span()));

        let postfix = choice((
            dot_postfix,
            type_args_postfix,
            call_postfix,
            question_postfix,
        ));

        let atom = raw_atom.foldl(postfix.repeated(), |lhs, op| match op {
            Postfix::Call(args, span) => {
                let full_span = (get_span(&lhs).0, span.end);
                Expr::App {
                    func: Box::new(lhs),
                    args,
                    is_ufcs: false,
                    span: full_span,
                }
            }
            Postfix::TypeArgs(type_args, span) => {
                let full_span = (get_span(&lhs).0, span.end);
                Expr::TypeApp {
                    expr: Box::new(lhs),
                    type_args,
                    span: full_span,
                }
            }
            Postfix::FieldAccess(field, span) => {
                let full_span = (get_span(&lhs).0, span.end);
                Expr::FieldAccess {
                    expr: Box::new(lhs),
                    field,
                    span: full_span,
                }
            }
            Postfix::Ufcs(method, type_args, extra_args, span) => {
                let full_span = (get_span(&lhs).0, span.end);
                let mut args = vec![lhs];
                args.extend(extra_args);
                let func = if type_args.is_empty() {
                    Expr::Var {
                        name: method,
                        span: to_span(span),
                    }
                } else {
                    Expr::TypeApp {
                        expr: Box::new(Expr::Var {
                            name: method,
                            span: to_span(span),
                        }),
                        type_args,
                        span: to_span(span),
                    }
                };
                Expr::App {
                    func: Box::new(func),
                    args,
                    is_ufcs: true,
                    span: full_span,
                }
            }
            Postfix::Question(span) => {
                let full_span = (get_span(&lhs).0, span.end);
                Expr::QuestionMark {
                    expr: Box::new(lhs),
                    span: full_span,
                }
            }
        });

        // --- Pratt expression with operators ---
        let pratt_expr = atom.pratt((
            // Precedence 1: || (lowest)
            infix(
                left(1),
                symbol(Token::Or),
                |lhs, _, rhs, e: &mut MapExtra<'_, '_, I, _>| Expr::BinaryOp {
                    op: BinOp::Or,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                },
            ),
            // Precedence 2: &&
            infix(
                left(2),
                symbol(Token::And),
                |lhs, _, rhs, e: &mut MapExtra<'_, '_, I, _>| Expr::BinaryOp {
                    op: BinOp::And,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                },
            ),
            // Precedence 3: comparison (non-associative)
            infix(
                none(3),
                ignored_newlines()
                    .ignore_then(select! {
                        Token::Eq => BinOp::Eq,
                        Token::Neq => BinOp::Neq,
                        Token::Lt => BinOp::Lt,
                        Token::Gt => BinOp::Gt,
                        Token::Le => BinOp::Le,
                        Token::Ge => BinOp::Ge,
                    })
                    .then_ignore(ignored_newlines()),
                |lhs, op, rhs, e: &mut MapExtra<'_, '_, I, _>| Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                },
            ),
            // Precedence 4: + -
            infix(
                left(4),
                ignored_newlines()
                    .ignore_then(select! {
                        Token::Plus => BinOp::Add,
                        Token::Minus => BinOp::Sub,
                    })
                    .then_ignore(ignored_newlines()),
                |lhs, op, rhs, e: &mut MapExtra<'_, '_, I, _>| Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                },
            ),
            // Precedence 5: * /
            infix(
                left(5),
                ignored_newlines()
                    .ignore_then(select! {
                        Token::Star => BinOp::Mul,
                        Token::Slash => BinOp::Div,
                    })
                    .then_ignore(ignored_newlines()),
                |lhs, op, rhs, e: &mut MapExtra<'_, '_, I, _>| Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                },
            ),
            // Precedence 6: prefix - and !
            prefix(
                6,
                symbol(Token::Minus),
                |_, rhs, e: &mut MapExtra<'_, '_, I, _>| Expr::UnaryOp {
                    op: UnaryOp::Neg,
                    operand: Box::new(rhs),
                    span: to_span(e.span()),
                },
            ),
            prefix(
                6,
                symbol(Token::Bang),
                |_, rhs, e: &mut MapExtra<'_, '_, I, _>| Expr::UnaryOp {
                    op: UnaryOp::Not,
                    operand: Box::new(rhs),
                    span: to_span(e.span()),
                },
            ),
        ));

        pratt_expr
    })
}

fn get_span(expr: &Expr) -> Span {
    match expr {
        Expr::Lit { span, .. }
        | Expr::Var { span, .. }
        | Expr::App { span, .. }
        | Expr::TypeApp { span, .. }
        | Expr::If { span, .. }
        | Expr::Let { span, .. }
        | Expr::Do { span, .. }
        | Expr::Match { span, .. }
        | Expr::Lambda { span, .. }
        | Expr::FieldAccess { span, .. }
        | Expr::Recur { span, .. }
        | Expr::QuestionMark { span, .. }
        | Expr::List { span, .. }
        | Expr::Tuple { span, .. }
        | Expr::BinaryOp { span, .. }
        | Expr::UnaryOp { span, .. }
        | Expr::StructLit { span, .. }
        | Expr::StructUpdate { span, .. }
        | Expr::LetPattern { span, .. } => *span,
    }
}

fn set_span(expr: &mut Expr, new_span: Span) {
    match expr {
        Expr::Lit { span, .. }
        | Expr::Var { span, .. }
        | Expr::App { span, .. }
        | Expr::TypeApp { span, .. }
        | Expr::If { span, .. }
        | Expr::Let { span, .. }
        | Expr::Do { span, .. }
        | Expr::Match { span, .. }
        | Expr::Lambda { span, .. }
        | Expr::FieldAccess { span, .. }
        | Expr::Recur { span, .. }
        | Expr::QuestionMark { span, .. }
        | Expr::List { span, .. }
        | Expr::Tuple { span, .. }
        | Expr::BinaryOp { span, .. }
        | Expr::UnaryOp { span, .. }
        | Expr::StructLit { span, .. }
        | Expr::StructUpdate { span, .. }
        | Expr::LetPattern { span, .. } => *span = new_span,
    }
}

fn where_clause_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Vec<TypeConstraint>, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    let bound_name = select! {
        Token::Ident(s) => s.to_string(),
        Token::Shared => "shared".to_string(),
    };
    let type_constraint_group = select! { Token::Ident(s) => s.to_string() }
        .then_ignore(symbol(Token::Colon))
        .then(
            bound_name
                .separated_by(symbol(Token::Plus))
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .map_with(|(type_var, bounds), e| {
            let span = to_span(e.span());
            bounds
                .into_iter()
                .map(|trait_name| TypeConstraint {
                    type_var: type_var.clone(),
                    trait_name,
                    span,
                })
                .collect::<Vec<_>>()
        });

    symbol(Token::Where)
        .ignore_then(
            type_constraint_group
                .separated_by(symbol(Token::Comma))
                .collect::<Vec<Vec<_>>>(),
        )
        .or_not()
        .map(|c| {
            c.unwrap_or_default()
                .into_iter()
                .flatten()
                .collect::<Vec<_>>()
        })
}

fn visibility_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Visibility, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    symbol(Token::Pub)
        .ignore_then(symbol(Token::Opaque).or_not())
        .map(|opaque| {
            if opaque.is_some() {
                Visibility::Opaque
            } else {
                Visibility::Pub
            }
        })
        .or_not()
        .map(|v| v.unwrap_or(Visibility::Private))
}

#[allow(clippy::type_complexity)]
fn decl_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Decl, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    let expr = expr_parser();
    let ty = type_expr_parser();
    let vis = visibility_parser();

    let where_clause = where_clause_parser();

    // --- Param: name or name: Type ---
    let param = select! { Token::Ident(s) => s.to_string() }
        .then(symbol(Token::Colon).ignore_then(ty.clone()).or_not())
        .map_with(|(name, ty_ann), e| Param {
            name,
            ty: ty_ann,
            span: to_span(e.span()),
        });

    // --- Type params: [a, f[_], g[_, _]] ---
    let type_param = select! { Token::Ident(s) => s.to_string() }
        .then(
            symbol(Token::Underscore)
                .separated_by(symbol(Token::Comma))
                .at_least(1)
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
                .or_not(),
        )
        .map_with(|(name, holes), e| TypeParam {
            arity: holes.map(|h| h.len()).unwrap_or(0),
            name,
            span: to_span(e.span()),
        });

    let fn_type_params = type_param
        .clone()
        .separated_by(symbol(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
        .or_not()
        .map(|tp| tp.unwrap_or_default());

    let type_decl_params = select! { Token::Ident(s) => s.to_string() }
        .separated_by(symbol(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
        .or_not()
        .map(|tp| tp.unwrap_or_default());

    // --- Function declaration ---
    // fun name[tparams](params) -> RetType where constraints = expr
    // fun name(params) { body }
    let fun_decl = vis
        .clone()
        .then_ignore(symbol(Token::Fun))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(fn_type_params.clone())
        .then(
            param
                .clone()
                .separated_by(symbol(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen)),
        )
        .then(symbol(Token::Arrow).ignore_then(ty.clone()).or_not())
        .then(where_clause.clone())
        .then(
            // = expr or { block }
            symbol(Token::Assign)
                .ignore_then(expr.clone())
                .or(expr.clone()),
        )
        .map_with(
            |((((((visibility, name), type_params), params), return_type), constraints), body),
             e| {
                Decl::DefFn(FnDecl {
                    name,
                    visibility,
                    type_params,
                    params,
                    constraints,
                    return_type,
                    body: Box::new(body),
                    span: to_span(e.span()),
                })
            },
        );

    // --- Type declaration ---
    // type Name[params] = { fields } (record)
    // type Name[params] = Variant1 | Variant2 (sum)
    let record_field = select! { Token::Ident(s) => s.to_string() }
        .then_ignore(symbol(Token::Colon))
        .then(ty.clone());

    let record_kind = record_field
        .separated_by(symbol(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace))
        .map(|fields| TypeDeclKind::Record { fields });

    // Sum variant: Name(types) or bare Name
    let variant = select! { Token::Ident(s) => s.to_string() }
        .then(
            ty.clone()
                .separated_by(symbol(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen))
                .or_not(),
        )
        .map_with(|(name, fields), e| Variant {
            name,
            fields: fields.unwrap_or_default(),
            span: to_span(e.span()),
        });

    let sum_kind = variant
        .separated_by(symbol(Token::Pipe))
        .at_least(1)
        .collect::<Vec<_>>()
        .map(|variants| TypeDeclKind::Sum { variants });

    // Optional deriving
    let deriving = symbol(Token::Deriving)
        .ignore_then(
            select! { Token::Ident(s) => s.to_string() }
                .separated_by(symbol(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen)),
        )
        .or_not()
        .map(|d| d.unwrap_or_default());

    let type_decl = vis
        .clone()
        .then_ignore(symbol(Token::Type))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(type_decl_params.clone())
        .then_ignore(symbol(Token::Assign))
        .then(record_kind.or(sum_kind))
        .then(deriving)
        .map_with(|((((visibility, name), type_params), kind), deriving), e| {
            Decl::DefType(TypeDecl {
                name,
                visibility,
                type_params,
                kind,
                deriving,
                span: to_span(e.span()),
            })
        });

    // --- Trait declaration ---
    // trait Name[tvar] { methods } or trait Name[tvar] where tvar: Super { methods }
    let trait_method_param = select! {
        Token::Ident(s) => s.to_string(),
        Token::Self_ => "self".to_string(),
    }
    .then_ignore(
        symbol(Token::Colon)
            .labelled("type annotation — trait method parameters require types, e.g. (x: a, y: a)"),
    )
    .then(ty.clone())
    .map_with(|(name, ty_ann), e| Param {
        name,
        ty: Some(ty_ann),
        span: to_span(e.span()),
    });

    let trait_method = symbol(Token::Fun)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(fn_type_params.clone())
        .then(
            trait_method_param
                .separated_by(symbol(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen)),
        )
        .then(symbol(Token::Arrow).ignore_then(ty.clone()).or_not())
        .then(
            symbol(Token::Assign)
                .ignore_then(expr.clone())
                .or(expr.clone())
                .or_not(),
        )
        .map_with(
            |((((name, type_params), params), return_type), body), e| FnDecl {
                name,
                visibility: Visibility::Private,
                type_params,
                params,
                constraints: vec![],
                return_type,
                body: Box::new(body.unwrap_or(Expr::Lit {
                    value: Lit::Unit,
                    span: to_span(e.span()),
                })),
                span: to_span(e.span()),
            },
        );

    let trait_superclasses = symbol(Token::Where)
        .ignore_then(
            select! { Token::Ident(s) => s.to_string() }
                .then_ignore(symbol(Token::Colon))
                .ignore_then(
                    select! { Token::Ident(s) => s.to_string() }
                        .separated_by(symbol(Token::Plus).or(symbol(Token::Comma)))
                        .collect::<Vec<_>>(),
                ),
        )
        .or_not()
        .map(|s| s.unwrap_or_default());

    let trait_decl = vis
        .clone()
        .then_ignore(symbol(Token::Trait))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(type_param.delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket)))
        .then(trait_superclasses)
        .then(
            trait_method
                .clone()
                .separated_by(stmt_sep().or_not())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace)),
        )
        .map_with(
            |((((visibility, name), type_param), superclasses), methods), e| Decl::DefTrait {
                visibility,
                name,
                type_param,
                superclasses,
                methods,
                span: to_span(e.span()),
            },
        );

    // --- Impl declaration ---
    // impl Trait[Type] { methods } or impl Trait[Type] where constraints { methods }
    let impl_method = symbol(Token::Fun)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(fn_type_params.clone())
        .then(
            param
                .separated_by(symbol(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen)),
        )
        .then(symbol(Token::Arrow).ignore_then(ty.clone()).or_not())
        .then(
            symbol(Token::Assign)
                .ignore_then(expr.clone())
                .or(expr.clone()),
        )
        .map_with(
            |((((name, type_params), params), return_type), body), e| FnDecl {
                name,
                visibility: Visibility::Private,
                type_params,
                params,
                constraints: vec![],
                return_type,
                body: Box::new(body),
                span: to_span(e.span()),
            },
        );

    let impl_constraints = where_clause_parser();

    let impl_decl = symbol(Token::Impl)
        .ignore_then(fn_type_params.clone())
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(
            ty.clone()
                .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket)),
        )
        .then(impl_constraints)
        .then(
            impl_method
                .separated_by(stmt_sep().or_not())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace)),
        )
        .map_with(
            |((((type_params, trait_name), target_type), type_constraints), methods), e| {
                Decl::DefImpl {
                    trait_name,
                    target_type,
                    type_params,
                    type_constraints,
                    methods,
                    span: to_span(e.span()),
                }
            },
        );

    // --- Import declaration ---
    // import path/to/mod.{Name1, Name2 as alias}
    // import path/to/mod
    // Import path segments: accept idents and keywords that might be valid module names
    let path_segment = select! {
        Token::Ident(s) => s.to_string(),
        Token::Type => "type".to_string(),
        Token::Match => "match".to_string(),
        Token::If => "if".to_string(),
        Token::Let => "let".to_string(),
        Token::Fn => "fn".to_string(),
        Token::Do => "do".to_string(),
    };
    let import_path = path_segment
        .separated_by(just(Token::Slash).or(just(Token::Dot)))
        .at_least(1)
        .collect::<Vec<_>>()
        .map(|parts| parts.join("/"));

    let import_name = select! { Token::Ident(s) => s.to_string() }
        .then(
            symbol(Token::As)
                .ignore_then(select! { Token::Ident(s) => s.to_string() })
                .or_not(),
        )
        .map(|(name, alias)| ImportName { name, alias });

    let import_names = import_name
        .separated_by(symbol(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(
            symbol(Token::Dot).then(symbol(Token::LBrace)),
            closing_symbol(Token::RBrace),
        )
        .or_not()
        .map(|n| n.unwrap_or_default());

    let pub_import_decl = symbol(Token::Pub)
        .ignore_then(symbol(Token::Import))
        .ignore_then(import_path.clone())
        .then(import_names.clone())
        .map_with(|(path, names), e| Decl::Import {
            is_pub: true,
            path,
            names,
            span: to_span(e.span()),
        });

    let import_decl = symbol(Token::Import)
        .ignore_then(import_path)
        .then(import_names)
        .map_with(|(path, names), e| Decl::Import {
            is_pub: false,
            path,
            names,
            span: to_span(e.span()),
        });

    // --- Extern declaration ---
    // extern java "class.Name" { fun method(params) -> Ret }
    // extern js "./path.mjs" { fun method(params) -> Ret }
    let extern_param = select! { Token::Ident(s) => s.to_string() }
        .then_ignore(symbol(Token::Colon))
        .then(ty.clone());

    let extern_params = extern_param
        .separated_by(symbol(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(symbol(Token::LParen), closing_symbol(Token::RParen));

    let extern_method_type_params = select! { Token::Ident(s) => s.to_string() }
        .separated_by(symbol(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
        .or_not()
        .map(|opt| opt.unwrap_or_default());

    let extern_where_clause = where_clause_parser();

    let extern_nullable = symbol(Token::At)
        .then(select! { Token::Ident(s) if s == "nullable" => () })
        .or_not();

    let extern_method = extern_nullable
        .then(symbol(Token::Pub).or_not())
        .then_ignore(symbol(Token::Fun))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(extern_method_type_params)
        .then(extern_params)
        .then(symbol(Token::Arrow).ignore_then(ty.clone()))
        .then(extern_where_clause)
        .map_with(
            |(
                (((((nullable_opt, pub_opt), name), method_type_params), params), return_type),
                where_clauses,
            ),
             e| ExternMethod {
                nullable: nullable_opt.is_some(),
                visibility: if pub_opt.is_some() {
                    Visibility::Pub
                } else {
                    Visibility::Private
                },
                name,
                type_params: method_type_params,
                params,
                return_type,
                where_clauses,
                span: to_span(e.span()),
            },
        );

    let extern_target = select! {
        Token::Ident(s) if s == "java" => ExternTarget::Java,
        Token::Ident(s) if s == "js" => ExternTarget::Js,
    };

    let extern_as_clause = symbol(Token::As)
        .ignore_then(symbol(Token::Pub).or_not())
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(
            select! { Token::Ident(s) => s.to_string() }
                .separated_by(symbol(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LBracket), closing_symbol(Token::RBracket))
                .or_not()
                .map(|opt| opt.unwrap_or_default()),
        )
        .or_not();

    let extern_decl = symbol(Token::Extern)
        .ignore_then(extern_target)
        .then(select! { Token::String(s) => s.to_string() })
        .then(extern_as_clause)
        .then(
            extern_method
                .separated_by(stmt_sep().or_not())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(symbol(Token::LBrace), closing_symbol(Token::RBrace)),
        )
        .map_with(|(((target, module_path), as_clause), methods), e| {
            let (alias, alias_visibility, type_params) = match as_clause {
                Some(((is_pub, name), params)) => {
                    let vis = if is_pub.is_some() {
                        Visibility::Pub
                    } else {
                        Visibility::Private
                    };
                    (Some(name), Some(vis), params)
                }
                None => (None, None, vec![]),
            };
            Decl::Extern {
                target,
                module_path,
                alias,
                alias_visibility,
                type_params,
                methods,
                span: to_span(e.span()),
            }
        });

    // --- Combined ---
    // pub_import_decl must come before fun_decl since both start with `pub`
    choice((
        pub_import_decl,
        fun_decl,
        type_decl,
        trait_decl,
        impl_decl,
        import_decl,
        extern_decl,
    ))
}

fn module_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Module, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    ignored_newlines()
        .ignore_then(
            decl_parser()
                .separated_by(stmt_sep().or_not())
                .allow_trailing()
                .collect::<Vec<_>>()
                .map(|decls| Module { decls }),
        )
        .then_ignore(ignored_newlines())
}

fn classify_parse_error(e: &Rich<Token, LexSpan>) -> ErrorCode {
    if let chumsky::error::RichReason::ExpectedFound { expected, found } = e.reason() {
        if found.is_none() {
            return ErrorCode::P0002;
        }
        for pat in expected {
            if let chumsky::error::RichPattern::Token(tok) = pat {
                let tok: &Token = tok;
                if matches!(tok, Token::RParen | Token::RBracket | Token::RBrace) {
                    return ErrorCode::P0002;
                }
            }
        }
    }
    ErrorCode::P0001
}

#[tracing::instrument(skip(source), fields(len = source.len()))]
pub fn parse(source: &str) -> (Module, Vec<ParseError>) {
    // Chumsky uses stacker internally (64KB red zone), but in debug builds
    // combinator frames are large enough to overshoot that guard. Use a larger
    // red zone so stacker grows the stack before chumsky's check is too late.
    stacker::maybe_grow(4 * 1024 * 1024, 8 * 1024 * 1024, || parse_inner(source))
}

fn parse_inner(source: &str) -> (Module, Vec<ParseError>) {
    let (tokens, lex_errors) = lexer::lexer().parse(source).into_output_errors();
    let tokens = tokens.unwrap_or_default();
    tracing::debug!(
        tokens = tokens.len(),
        lex_errors = lex_errors.len(),
        "lexing complete"
    );

    let mut errors: Vec<ParseError> = lex_errors
        .into_iter()
        .map(|e| {
            let span = e.span();
            ParseError {
                code: ErrorCode::P0003,
                message: e.to_string(),
                span: (span.start, span.end),
            }
        })
        .collect();

    let eoi: LexSpan = tokens
        .last()
        .map(|(_, s)| (s.end..s.end).into())
        .unwrap_or((0..0).into());
    let input = tokens.map(eoi, |(t, s)| (t, s));

    let (module, parse_errors) = module_parser().parse(input).into_output_errors();

    errors.extend(parse_errors.into_iter().map(|e| {
        let span = e.span();
        let code = classify_parse_error(&e);
        ParseError {
            code,
            message: e.to_string(),
            span: (span.start, span.end),
        }
    }));

    let module = module.unwrap_or(Module { decls: vec![] });
    tracing::debug!(
        decls = module.decls.len(),
        errors = errors.len(),
        "parsing complete"
    );
    (module, errors)
}
