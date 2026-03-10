use chumsky::input::{MapExtra, ValueInput};
use chumsky::pratt::*;
use chumsky::prelude::*;

use crate::ast::*;
use crate::diagnostics::{ErrorCode, ParseError};
use crate::lexer::{self, Span as LexSpan, Spanned, Token};

/// Insert synthetic semicolons at newline boundaries (automatic semicolon insertion).
///
/// A semicolon is inserted between two adjacent tokens when:
/// 1. The previous token can end a statement (ASI-triggering)
/// 2. There is a newline in the source between the two tokens
/// 3. The next token is not a continuation token
fn insert_semicolons<'src>(
    source: &str,
    tokens: Vec<Spanned<Token<'src>>>,
) -> Vec<Spanned<Token<'src>>> {
    if tokens.is_empty() {
        return tokens;
    }

    let mut result: Vec<Spanned<Token<'src>>> = Vec::with_capacity(tokens.len() * 2);

    for i in 0..tokens.len() {
        result.push(tokens[i].clone());

        // Check if we should insert a semicolon after this token
        if i + 1 < tokens.len() {
            let (ref prev_tok, ref prev_span) = tokens[i];
            let (ref next_tok, _) = tokens[i + 1];

            let prev_triggers_asi = matches!(
                prev_tok,
                Token::Ident(_)
                    | Token::Int(_)
                    | Token::Float(_)
                    | Token::String(_)
                    | Token::Bool(_)
                    | Token::RParen
                    | Token::RBracket
                    | Token::RBrace
                    | Token::Underscore
            );

            if !prev_triggers_asi {
                continue;
            }

            let next_is_continuation = matches!(
                next_tok,
                Token::Else
                    | Token::FatArrow
                    | Token::Arrow
                    | Token::Where
                    | Token::Dot
                    | Token::Pipe
            );

            if next_is_continuation {
                continue;
            }

            // Check for newline between the two tokens
            let between_start = prev_span.end;
            let between_end = tokens[i + 1].1.start;
            if between_start < between_end
                && source[between_start..between_end].contains('\n')
            {
                // Insert synthetic semicolon with zero-width span at end of previous token
                let semi_span: LexSpan = (prev_span.end..prev_span.end).into();
                result.push((Token::Semicolon, semi_span));
            }
        }
    }

    result
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
        // Named/Var: bare ident
        let named_or_var =
            select! { Token::Ident(s) => s.to_string() }.map_with(|name, e| {
                if is_uppercase(&name) {
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
        let own_type = just(Token::Tilde)
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
            .separated_by(just(Token::Comma))
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .then(
                just(Token::Arrow)
                    .ignore_then(ty.clone())
                    .or_not(),
            )
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

        // Base type (without generic application)
        let base_type = choice((own_type, paren_type, named_or_var));

        // Generic application: Name[args]
        base_type.clone().then(
            ty.clone()
                .separated_by(just(Token::Comma))
                .at_least(1)
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBracket), just(Token::RBracket))
                .or_not(),
        ).map_with(|(base, args), e| {
            match args {
                Some(args) => {
                    if let TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } = base {
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
            }
        })
    })
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

        // Constructor: Name(args) or bare Name (uppercase)
        let constructor_pat = select! { Token::Ident(s) if is_uppercase(s) => s.to_string() }
            .then(
                pattern
                    .clone()
                    .separated_by(just(Token::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not(),
            )
            .map_with(|(name, args), e| Pattern::Constructor {
                name,
                args: args.unwrap_or_default(),
                span: to_span(e.span()),
            });

        // Struct pattern: Name { field1, field2, .. }
        let struct_field = select! { Token::Ident(s) => s.to_string() }
            .then(
                just(Token::Colon)
                    .ignore_then(pattern.clone())
                    .or_not(),
            )
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
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .then(
                        just(Token::Comma)
                            .ignore_then(just(Token::DotDot))
                            .or_not(),
                    )
                    .delimited_by(just(Token::LBrace), just(Token::RBrace)),
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
            .separated_by(just(Token::Comma))
            .at_least(2)
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|elements, e| Pattern::Tuple {
                elements,
                span: to_span(e.span()),
            });

        // Variable pattern: lowercase ident
        let var_pat = select! { Token::Ident(s) if !is_uppercase(s) => s.to_string() }
            .map_with(|name, e| Pattern::Var {
                name,
                span: to_span(e.span()),
            });

        // Unit pattern: ()
        let unit_pat = just(Token::LParen)
            .then(just(Token::RParen))
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
        atomic
            .clone()
            .foldl(
                just(Token::Pipe).ignore_then(atomic).repeated(),
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
        let unit_lit = just(Token::LParen)
            .then(just(Token::RParen))
            .map_with(|_, e| Expr::Lit {
                value: Lit::Unit,
                span: to_span(e.span()),
            });

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

        // Block: { stmt; stmt; expr }
        let block_expr = {
            // Statement in a block: let binding or expression
            let let_stmt = just(Token::Let)
                .ignore_then(
                    // Try pattern destructuring first
                    pattern.clone()
                        .then(just(Token::Colon).ignore_then(ty.clone()).or_not())
                        .then_ignore(just(Token::Assign))
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
                .separated_by(just(Token::Semicolon))
                .allow_trailing()
                .at_least(1)
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBrace), just(Token::RBrace))
                .map_with(|exprs, e| {
                    if exprs.len() == 1 {
                        // Single expression block — just return the expr with the block span
                        let mut single = exprs.into_iter().next().unwrap();
                        // For consistency, wrap in Do if it's a let
                        match &single {
                            Expr::Let { .. } | Expr::LetPattern { .. } => {
                                Expr::Do {
                                    exprs: vec![single],
                                    span: to_span(e.span()),
                                }
                            }
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
        let if_expr = just(Token::If)
            .ignore_then(expr.clone())
            .then(expr.clone())
            .then(
                just(Token::Else)
                    .ignore_then(expr.clone())
                    .or_not(),
            )
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
            .then(
                just(Token::If)
                    .ignore_then(expr.clone())
                    .or_not(),
            )
            .then_ignore(just(Token::FatArrow))
            .then(expr.clone())
            .map_with(|((pat, guard), body), e| MatchArm {
                pattern: pat,
                guard: guard.map(Box::new),
                body,
                span: to_span(e.span()),
            });

        let match_expr = just(Token::Match)
            .ignore_then(expr.clone())
            .then(
                match_arm
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LBrace), just(Token::RBrace)),
            )
            .map_with(|(scrutinee, arms), e| Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms,
                span: to_span(e.span()),
            });

        // Recur: recur(args)
        let recur_expr = just(Token::Recur)
            .ignore_then(
                expr.clone()
                    .separated_by(just(Token::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .map_with(|args, e| Expr::Recur {
                args,
                span: to_span(e.span()),
            });

        // List literal: [1, 2, 3]
        let list_lit = expr
            .clone()
            .separated_by(just(Token::Comma))
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LBracket), just(Token::RBracket))
            .map_with(|elements, e| Expr::List {
                elements,
                span: to_span(e.span()),
            });

        // Struct literal: Name { field = val, ... }
        let struct_field = select! { Token::Ident(s) => s.to_string() }
            .then(
                just(Token::Assign)
                    .ignore_then(expr.clone())
                    .or_not(),
            )
            .map(|(name, val)| {
                let v = val.unwrap_or_else(|| Expr::Var {
                    name: name.clone(),
                    span: (0, 0),
                });
                (name, v)
            });

        let struct_lit = select! { Token::Ident(s) if is_uppercase(s) => s.to_string() }
            .then(
                struct_field.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LBrace), just(Token::RBrace)),
            )
            .map_with(|(name, fields), e| Expr::StructLit {
                name,
                fields,
                span: to_span(e.span()),
            });

        // Struct update: { base | field = val, ... }
        let struct_update = just(Token::LBrace)
            .ignore_then(expr.clone())
            .then_ignore(just(Token::Pipe))
            .then(
                struct_field.clone()
                    .separated_by(just(Token::Comma))
                    .allow_trailing()
                    .collect::<Vec<_>>(),
            )
            .then_ignore(just(Token::RBrace))
            .map_with(|(base, fields), e| Expr::StructUpdate {
                base: Box::new(base),
                fields,
                span: to_span(e.span()),
            });

        // Lambda: x => body, (x, y) => body, (x: Int) => body
        // Lambda params with optional type annotation
        let lambda_param = select! { Token::Ident(s) => s.to_string() }
            .then(
                just(Token::Colon)
                    .ignore_then(ty.clone())
                    .or_not(),
            )
            .map_with(|(name, ty_ann), e| Param {
                name,
                ty: ty_ann,
                span: to_span(e.span()),
            });

        // Zero-arg lambda: () => body
        let zero_lambda = just(Token::LParen)
            .then(just(Token::RParen))
            .then_ignore(just(Token::FatArrow))
            .then(expr.clone())
            .map_with(|(_, body), e| Expr::Lambda {
                params: vec![],
                return_type: None,
                body: Box::new(body),
                span: to_span(e.span()),
            });

        // Multi-param lambda: (x, y) => body or (x: Int, y: Int) => body
        let multi_lambda = lambda_param
            .clone()
            .separated_by(just(Token::Comma))
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .then_ignore(just(Token::FatArrow))
            .then(expr.clone())
            .map_with(|(params, body), e| Expr::Lambda {
                params,
                return_type: None,
                body: Box::new(body),
                span: to_span(e.span()),
            });

        // Single-param lambda: x => body
        let single_lambda = select! { Token::Ident(s) => s.to_string() }
            .map_with(|name, e| Param {
                name,
                ty: None,
                span: to_span(e.span()),
            })
            .then_ignore(just(Token::FatArrow))
            .then(expr.clone())
            .map_with(|(param, body), e| Expr::Lambda {
                params: vec![param],
                return_type: None,
                body: Box::new(body),
                span: to_span(e.span()),
            });

        // Parenthesized expression or tuple: (expr) or (expr, expr)
        let paren_or_tuple = expr
            .clone()
            .separated_by(just(Token::Comma))
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
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
            FieldAccess(String, LexSpan),
            Ufcs(String, Vec<Expr>, LexSpan),
            Question(LexSpan),
        }

        // Function call: expr(args)
        let call_postfix = expr
            .clone()
            .separated_by(just(Token::Comma))
            .collect::<Vec<_>>()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|args, e| Postfix::Call(args, e.span()));

        // Dot access: .ident or .ident(args)
        let dot_postfix = just(Token::Dot)
            .ignore_then(select! { Token::Ident(s) => s.to_string() })
            .then(
                expr.clone()
                    .separated_by(just(Token::Comma))
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LParen), just(Token::RParen))
                    .or_not(),
            )
            .map_with(|(field, args), e| {
                if let Some(args) = args {
                    Postfix::Ufcs(field, args, e.span())
                } else {
                    Postfix::FieldAccess(field, e.span())
                }
            });

        // Question mark: expr?
        let question_postfix = just(Token::Question)
            .map_with(|_, e| Postfix::Question(e.span()));

        let postfix = choice((dot_postfix, call_postfix, question_postfix));

        let atom = raw_atom.foldl(postfix.repeated(), |lhs, op| {
            match op {
                Postfix::Call(args, span) => {
                    let full_span = (get_span(&lhs).0, span.end);
                    Expr::App {
                        func: Box::new(lhs),
                        args,
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
                Postfix::Ufcs(method, extra_args, span) => {
                    let full_span = (get_span(&lhs).0, span.end);
                    let mut args = vec![lhs];
                    args.extend(extra_args);
                    Expr::App {
                        func: Box::new(Expr::Var {
                            name: method,
                            span: to_span(span),
                        }),
                        args,
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
            }
        });

        // --- Pratt expression with operators ---
        let pratt_expr = atom.pratt((
            // Precedence 1: || (lowest)
            infix(left(1), just(Token::Or), |lhs, _, rhs, e: &mut MapExtra<'_, '_, I, _>| {
                Expr::BinaryOp {
                    op: BinOp::Or,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                }
            }),
            // Precedence 2: &&
            infix(left(2), just(Token::And), |lhs, _, rhs, e: &mut MapExtra<'_, '_, I, _>| {
                Expr::BinaryOp {
                    op: BinOp::And,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                }
            }),
            // Precedence 3: comparison (non-associative)
            infix(none(3), select! {
                Token::Eq => BinOp::Eq,
                Token::Neq => BinOp::Neq,
                Token::Lt => BinOp::Lt,
                Token::Gt => BinOp::Gt,
                Token::Le => BinOp::Le,
                Token::Ge => BinOp::Ge,
            }, |lhs, op, rhs, e: &mut MapExtra<'_, '_, I, _>| {
                Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                }
            }),
            // Precedence 4: + -
            infix(left(4), select! {
                Token::Plus => BinOp::Add,
                Token::Minus => BinOp::Sub,
            }, |lhs, op, rhs, e: &mut MapExtra<'_, '_, I, _>| {
                Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                }
            }),
            // Precedence 5: * /
            infix(left(5), select! {
                Token::Star => BinOp::Mul,
                Token::Slash => BinOp::Div,
            }, |lhs, op, rhs, e: &mut MapExtra<'_, '_, I, _>| {
                Expr::BinaryOp {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                    span: to_span(e.span()),
                }
            }),
            // Precedence 6: prefix - and !
            prefix(6, just(Token::Minus), |_, rhs, e: &mut MapExtra<'_, '_, I, _>| {
                Expr::UnaryOp {
                    op: UnaryOp::Neg,
                    operand: Box::new(rhs),
                    span: to_span(e.span()),
                }
            }),
            prefix(6, just(Token::Bang), |_, rhs, e: &mut MapExtra<'_, '_, I, _>| {
                Expr::UnaryOp {
                    op: UnaryOp::Not,
                    operand: Box::new(rhs),
                    span: to_span(e.span()),
                }
            }),
        ));

        pratt_expr
    })
}

fn get_span(expr: &Expr) -> Span {
    match expr {
        Expr::Lit { span, .. }
        | Expr::Var { span, .. }
        | Expr::App { span, .. }
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

fn visibility_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Visibility, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    just(Token::Pub)
        .ignore_then(just(Token::Open).or_not())
        .map(|open| {
            if open.is_some() {
                Visibility::PubOpen
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

    // --- Type constraint: a: Trait ---
    let type_constraint = select! { Token::Ident(s) => s.to_string() }
        .then_ignore(just(Token::Colon))
        .then(select! { Token::Ident(s) => s.to_string() })
        .map_with(|(type_var, trait_name), e| TypeConstraint {
            type_var,
            trait_name,
            span: to_span(e.span()),
        });

    // --- Where clause: where a: Ord, b: Eq ---
    let where_clause = just(Token::Where)
        .ignore_then(
            type_constraint
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>(),
        )
        .or_not()
        .map(|c| c.unwrap_or_default());

    // --- Param: name or name: Type ---
    let param = select! { Token::Ident(s) => s.to_string() }
        .then(
            just(Token::Colon)
                .ignore_then(ty.clone())
                .or_not(),
        )
        .map_with(|(name, ty_ann), e| Param {
            name,
            ty: ty_ann,
            span: to_span(e.span()),
        });

    // --- Type params: [a, b] ---
    let type_params = select! { Token::Ident(s) => s.to_string() }
        .separated_by(just(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBracket), just(Token::RBracket))
        .or_not()
        .map(|tp| tp.unwrap_or_default());

    // --- Function declaration ---
    // fun name[tparams](params) -> RetType where constraints = expr
    // fun name(params) { body }
    let fun_decl = vis
        .clone()
        .then_ignore(just(Token::Fun))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(type_params.clone())
        .then(
            param
                .clone()
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        )
        .then(
            just(Token::Arrow)
                .ignore_then(ty.clone())
                .or_not(),
        )
        .then(where_clause.clone())
        .then(
            // = expr or { block }
            just(Token::Assign)
                .ignore_then(expr.clone())
                .or(expr.clone()),
        )
        .map_with(|((((((visibility, name), type_params), params), return_type), constraints), body), e| {
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
        });

    // --- Type declaration ---
    // type Name[params] = { fields } (record)
    // type Name[params] = Variant1 | Variant2 (sum)
    let record_field = select! { Token::Ident(s) => s.to_string() }
        .then_ignore(just(Token::Colon))
        .then(ty.clone());

    let record_kind = record_field
        .separated_by(just(Token::Comma))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBrace), just(Token::RBrace))
        .map(|fields| TypeDeclKind::Record { fields });

    // Sum variant: Name(types) or bare Name
    let variant = select! { Token::Ident(s) => s.to_string() }
        .then(
            ty.clone()
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .or_not(),
        )
        .map_with(|(name, fields), e| Variant {
            name,
            fields: fields.unwrap_or_default(),
            span: to_span(e.span()),
        });

    let sum_kind = variant
        .separated_by(just(Token::Pipe))
        .at_least(1)
        .collect::<Vec<_>>()
        .map(|variants| TypeDeclKind::Sum { variants });

    // Optional deriving
    let deriving = just(Token::Deriving)
        .ignore_then(
            select! { Token::Ident(s) => s.to_string() }
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        )
        .or_not()
        .map(|d| d.unwrap_or_default());

    let type_decl = vis
        .clone()
        .then_ignore(just(Token::Type))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(type_params.clone())
        .then_ignore(just(Token::Assign))
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
        .then_ignore(just(Token::Colon).labelled("type annotation — trait method parameters require types, e.g. (x: a, y: a)"))
        .then(ty.clone())
        .map_with(|(name, ty_ann), e| Param {
            name,
            ty: Some(ty_ann),
            span: to_span(e.span()),
        });

    let trait_method = just(Token::Fun)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(type_params.clone())
        .then(
            trait_method_param
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        )
        .then(
            just(Token::Arrow)
                .ignore_then(ty.clone())
                .or_not(),
        )
        .then(
            just(Token::Assign)
                .ignore_then(expr.clone())
                .or(expr.clone())
                .or_not(),
        )
        .map_with(|((((name, type_params), params), return_type), body), e| {
            FnDecl {
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
            }
        });

    let trait_superclasses = just(Token::Where)
        .ignore_then(
            select! { Token::Ident(s) => s.to_string() }
                .then_ignore(just(Token::Colon))
                .ignore_then(
                    select! { Token::Ident(s) => s.to_string() }
                        .separated_by(just(Token::Plus).or(just(Token::Comma)))
                        .collect::<Vec<_>>(),
                ),
        )
        .or_not()
        .map(|s| s.unwrap_or_default());

    // Parse trait type parameter: `a` (arity 0) or `f[_]` (arity 1) or `f[_, _]` (arity 2)
    let trait_type_param = select! { Token::Ident(s) => s.to_string() }
        .then(
            just(Token::Underscore)
                .separated_by(just(Token::Comma))
                .at_least(1)
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBracket), just(Token::RBracket))
                .or_not(),
        )
        .map_with(|(name, holes), e| TraitTypeParam {
            arity: holes.map(|h| h.len()).unwrap_or(0),
            name,
            span: to_span(e.span()),
        });

    let trait_decl = vis.clone()
        .then_ignore(just(Token::Trait))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(
            trait_type_param
                .delimited_by(just(Token::LBracket), just(Token::RBracket)),
        )
        .then(trait_superclasses)
        .then(
            trait_method
                .clone()
                .separated_by(just(Token::Semicolon).or_not())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map_with(|((((visibility, name), type_param), superclasses), methods), e| Decl::DefTrait {
            visibility,
            name,
            type_param,
            superclasses,
            methods,
            span: to_span(e.span()),
        });

    // --- Impl declaration ---
    // impl Trait[Type] { methods } or impl Trait[Type] where constraints { methods }
    let impl_method = just(Token::Fun)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(type_params.clone())
        .then(
            param
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LParen), just(Token::RParen)),
        )
        .then(
            just(Token::Arrow)
                .ignore_then(ty.clone())
                .or_not(),
        )
        .then(
            just(Token::Assign)
                .ignore_then(expr.clone())
                .or(expr.clone()),
        )
        .map_with(|((((name, type_params), params), return_type), body), e| FnDecl {
            name,
            visibility: Visibility::Private,
            type_params,
            params,
            constraints: vec![],
            return_type,
            body: Box::new(body),
            span: to_span(e.span()),
        });

    let impl_type_constraint = select! { Token::Ident(s) => s.to_string() }
        .then_ignore(just(Token::Colon))
        .then(select! { Token::Ident(s) => s.to_string() })
        .map_with(|(type_var, trait_name), e| TypeConstraint {
            type_var,
            trait_name,
            span: to_span(e.span()),
        });

    let impl_constraints = just(Token::Where)
        .ignore_then(
            impl_type_constraint
                .separated_by(just(Token::Comma))
                .collect::<Vec<_>>(),
        )
        .or_not()
        .map(|c| c.unwrap_or_default());

    let impl_decl = just(Token::Impl)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(
            ty.clone()
                .delimited_by(just(Token::LBracket), just(Token::RBracket)),
        )
        .then(impl_constraints)
        .then(
            impl_method
                .separated_by(just(Token::Semicolon).or_not())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map_with(|(((trait_name, target_type), type_constraints), methods), e| Decl::DefImpl {
            trait_name,
            target_type,
            type_constraints,
            methods,
            span: to_span(e.span()),
        });

    // --- Import declaration ---
    // import path/to/mod.{Name1, Name2 as alias}
    // import path/to/mod
    // Import path segments: accept idents and keywords that might be valid module names
    let path_segment = select! {
        Token::Ident(s) => s.to_string(),
        Token::List => "list".to_string(),
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
            just(Token::As)
                .ignore_then(select! { Token::Ident(s) => s.to_string() })
                .or_not(),
        )
        .map(|(name, alias)| ImportName { name, alias });

    let import_names = import_name
        .separated_by(just(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(just(Token::Dot).then(just(Token::LBrace)), just(Token::RBrace))
        .or_not()
        .map(|n| n.unwrap_or_default());

    let pub_import_decl = just(Token::Pub)
        .ignore_then(just(Token::Import))
        .ignore_then(import_path.clone())
        .then(import_names.clone())
        .map_with(|(path, names), e| Decl::Import {
            is_pub: true,
            path,
            names,
            span: to_span(e.span()),
        });

    let import_decl = just(Token::Import)
        .ignore_then(import_path)
        .then(import_names)
        .map_with(|(path, names), e| Decl::Import {
            is_pub: false,
            path,
            names,
            span: to_span(e.span()),
        });

    // --- Extern declaration ---
    // extern "class.Name" { fun method(params) -> Ret }
    let extern_param_types = ty
        .clone()
        .separated_by(just(Token::Comma))
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LParen), just(Token::RParen));

    let extern_method = just(Token::Pub).or_not()
        .then_ignore(just(Token::Fun))
        .then(select! { Token::Ident(s) => s.to_string() })
        .then(extern_param_types)
        .then(
            just(Token::Arrow)
                .ignore_then(ty.clone()),
        )
        .map_with(|(((pub_opt, name), param_types), return_type), e| ExternMethod {
            visibility: if pub_opt.is_some() { Visibility::Pub } else { Visibility::Private },
            name,
            param_types,
            return_type,
            span: to_span(e.span()),
        });

    let extern_decl = just(Token::Extern)
        .ignore_then(select! { Token::String(s) => s.to_string() })
        .then(
            extern_method
                .separated_by(just(Token::Semicolon).or_not())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBrace), just(Token::RBrace)),
        )
        .map_with(|(class_name, methods), e| Decl::ExternJava {
            class_name,
            methods,
            span: to_span(e.span()),
        });

    // --- Combined ---
    // pub_import_decl must come before fun_decl since both start with `pub`
    choice((pub_import_decl, fun_decl, type_decl, trait_decl, impl_decl, import_decl, extern_decl))
}

fn module_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Module, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    decl_parser()
        .separated_by(just(Token::Semicolon).or_not())
        .allow_trailing()
        .collect::<Vec<_>>()
        .map(|decls| Module { decls })
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
    let (tokens, lex_errors) = lexer::lexer().parse(source).into_output_errors();
    let tokens = tokens.unwrap_or_default();
    let tokens = insert_semicolons(source, tokens);
    tracing::debug!(tokens = tokens.len(), lex_errors = lex_errors.len(), "lexing complete");

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
    tracing::debug!(decls = module.decls.len(), errors = errors.len(), "parsing complete");
    (module, errors)
}
