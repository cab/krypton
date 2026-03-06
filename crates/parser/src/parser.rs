use chumsky::input::ValueInput;
use chumsky::prelude::*;
use serde::Serialize;

use crate::ast::*;
use crate::lexer::{self, Span as LexSpan, Token};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum ErrorCode {
    P0001, // Unexpected token
    P0002, // Unclosed delimiter
    P0003, // Invalid literal / lex error
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ErrorCode::P0001 => write!(f, "P0001"),
            ErrorCode::P0002 => write!(f, "P0002"),
            ErrorCode::P0003 => write!(f, "P0003"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ParseError {
    pub code: ErrorCode,
    pub message: String,
    pub span: Span,
}

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
) -> impl Parser<'tokens, I, Expr, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
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

        let atom = choice((lit, var));

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

        // (op lhs rhs) or (- expr) for unary negation
        let binary_op = bin_op_token
            .then(expr.clone())
            .then(expr.clone().or_not())
            .map(|((op, lhs), rhs)| -> Builder {
                Box::new(move |span| match rhs {
                    Some(rhs) => Expr::BinaryOp {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                        span,
                    },
                    None => Expr::UnaryOp {
                        op: UnaryOp::Neg,
                        operand: Box::new(lhs),
                        span,
                    },
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

        // (let (tuple a b) value) — destructuring let with a paren-delimited pattern
        // Only matches patterns that start with '(' (tuple, constructor), so it's
        // unambiguous with let_form which expects a bare ident after 'let'.
        let paren_pattern = {
            let pat = pattern.clone();
            // tuple pattern: (tuple p1 p2 ...)
            let tuple_pat = just(Token::Tuple)
                .ignore_then(pat.clone().repeated().at_least(1).collect::<Vec<_>>())
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .map_with(|elements, e| Pattern::Tuple {
                    elements,
                    span: to_span(e.span()),
                });
            // constructor pattern: (Name args...)
            let constructor_pat = select! { Token::Ident(s) => s.to_string() }
                .then(pat.repeated().collect::<Vec<_>>())
                .delimited_by(just(Token::LParen), just(Token::RParen))
                .map_with(|(name, args), e| Pattern::Constructor {
                    name,
                    args,
                    span: to_span(e.span()),
                });
            choice((tuple_pat, constructor_pat))
        };

        let let_pattern_form = just(Token::Let)
            .ignore_then(paren_pattern)
            .then(expr.clone())
            .map(|(pat, value)| -> Builder {
                Box::new(move |span| Expr::LetPattern {
                    pattern: pat,
                    value: Box::new(value),
                    body: None,
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

        // (.. base (field val) ...) — struct update
        let field_pair = select! { Token::Ident(s) => s.to_string() }
            .then(expr.clone())
            .delimited_by(just(Token::LParen), just(Token::RParen));

        let struct_update_form = just(Token::DotDot)
            .ignore_then(expr.clone())
            .then(field_pair.repeated().at_least(1).collect::<Vec<_>>())
            .map(|(base, fields)| -> Builder {
                Box::new(move |span| Expr::StructUpdate {
                    base: Box::new(base),
                    fields,
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
            let_pattern_form,
            let_form,
            do_form,
            if_form,
            match_form,
            dot_form,
            question_form,
            list_form,
            tuple_form,
            recur_form,
            struct_update_form,
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

fn is_uppercase(s: &str) -> bool {
    s.starts_with(|c: char| c.is_uppercase())
}

fn type_expr_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, TypeExpr, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>> + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    recursive(|ty| {
        // Uppercase ident → Named, lowercase → Var
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

        // (fn [param_types] return_type)
        let fn_type = just(Token::Fn)
            .ignore_then(
                ty.clone()
                    .repeated()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::LBracket), just(Token::RBracket)),
            )
            .then(ty.clone())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|(params, ret), e| TypeExpr::Fn {
                params,
                ret: Box::new(ret),
                span: to_span(e.span()),
            });

        // (own inner_type)
        let own_type = just(Token::Own)
            .ignore_then(ty.clone())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|inner, e| TypeExpr::Own {
                inner: Box::new(inner),
                span: to_span(e.span()),
            });

        // (tuple types...)
        let tuple_type = just(Token::Tuple)
            .ignore_then(ty.clone().repeated().collect::<Vec<_>>())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|elements, e| TypeExpr::Tuple {
                elements,
                span: to_span(e.span()),
            });

        // (Name types...) → App
        let app_type = select! { Token::Ident(s) => s.to_string() }
            .then(ty.clone().repeated().at_least(1).collect::<Vec<_>>())
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map_with(|(name, args), e| TypeExpr::App {
                name,
                args,
                span: to_span(e.span()),
            });

        choice((fn_type, own_type, tuple_type, app_type, named_or_var))
    })
}

#[allow(clippy::type_complexity)]
fn decl_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Decl, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    let expr = expr_parser();
    let ty = type_expr_parser();

    // --- def_fn_parser ---
    // (def name (fn [params] body))
    // (def name (fn [params] [param_types] RetType body))
    let param_names = select! { Token::Ident(s) => s.to_string() }
        .map_with(|name, e| (name, to_span(e.span())))
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBracket), just(Token::RBracket));

    let param_types = ty
        .clone()
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBracket), just(Token::RBracket));

    let fn_inner = just(Token::Fn)
        .ignore_then(param_names)
        .then(
            // Optional: [param_types] RetType before body
            param_types
                .then(ty.clone())
                .or_not(),
        )
        .then(expr.clone())
        .delimited_by(just(Token::LParen), just(Token::RParen));

    let def_fn = just(Token::Def)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(fn_inner)
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|(name, ((param_names, type_info), body)): (String, ((Vec<(String, Span)>, Option<(Vec<TypeExpr>, TypeExpr)>), Expr)), e| {
            let params = if let Some((ref ptypes, _)) = type_info {
                param_names
                    .into_iter()
                    .zip(ptypes.iter().cloned().map(Some).chain(std::iter::repeat(None)))
                    .map(|((pname, pspan), pty)| Param {
                        name: pname,
                        ty: pty,
                        span: pspan,
                    })
                    .collect()
            } else {
                param_names
                    .into_iter()
                    .map(|(pname, pspan)| Param {
                        name: pname,
                        ty: None,
                        span: pspan,
                    })
                    .collect()
            };
            let return_type = type_info.map(|(_, ret)| ret);
            Decl::DefFn(FnDecl {
                name,
                params,
                constraints: vec![],
                return_type,
                body: Box::new(body),
                span: to_span(e.span()),
            })
        });

    // --- type_parser ---
    // Record field: (name Type)
    let record_field = select! { Token::Ident(s) => s.to_string() }
        .then(ty.clone())
        .delimited_by(just(Token::LParen), just(Token::RParen));

    // (record (field Type)...)
    let record_kind = just(Token::Ident("record"))
        .ignore_then(record_field.repeated().at_least(1).collect::<Vec<_>>())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map(|fields| TypeDeclKind::Record { fields });

    // Sum variant: bare ident or (Name types...)
    let variant_bare = select! { Token::Ident(s) => s.to_string() }
        .map_with(|name, e| Variant {
            name,
            fields: vec![],
            span: to_span(e.span()),
        });

    let variant_paren = select! { Token::Ident(s) => s.to_string() }
        .then(ty.clone().repeated().collect::<Vec<_>>())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|(name, fields), e| Variant {
            name,
            fields,
            span: to_span(e.span()),
        });

    let variant = variant_paren.or(variant_bare);

    // (| variants...)
    let sum_kind = just(Token::Pipe)
        .ignore_then(variant.repeated().at_least(1).collect::<Vec<_>>())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map(|variants| TypeDeclKind::Sum { variants });

    // Optional type params [a b ...]
    let type_params = select! { Token::Ident(s) => s.to_string() }
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBracket), just(Token::RBracket));

    // Optional deriving [Trait1 Trait2 ...]
    let deriving = just(Token::Deriving)
        .ignore_then(
            select! { Token::Ident(s) => s.to_string() }
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBracket), just(Token::RBracket)),
        )
        .or_not()
        .map(|d| d.unwrap_or_default());

    let type_decl = just(Token::Type)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(type_params.or_not().map(|tp| tp.unwrap_or_default()))
        .then(record_kind.or(sum_kind))
        .then(deriving.clone())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|(((name, type_params), kind), deriving), e| {
            Decl::DefType(TypeDecl {
                name,
                type_params,
                kind,
                deriving,
                span: to_span(e.span()),
            })
        });

    // --- trait method: (def name [param_types] RetType? body?) ---
    let trait_method_param_types = ty
        .clone()
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBracket), just(Token::RBracket));

    let trait_method = just(Token::Def)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(trait_method_param_types)
        .then(ty.clone().or_not())
        .then(expr.clone().or_not())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|(((name, ptypes), ret_type), body), e| {
            let params = ptypes
                .into_iter()
                .enumerate()
                .map(|(i, t)| Param {
                    name: format!("_{i}"),
                    ty: Some(t),
                    span: to_span(e.span()),
                })
                .collect();
            FnDecl {
                name,
                params,
                constraints: vec![],
                return_type: ret_type,
                body: Box::new(body.unwrap_or(Expr::Lit {
                    value: Lit::Unit,
                    span: to_span(e.span()),
                })),
                span: to_span(e.span()),
            }
        });

    // --- trait_parser ---
    // (trait Name [tvar] :? [superclasses]? methods...)
    let superclasses = just(Token::Colon)
        .ignore_then(
            select! { Token::Ident(s) => s.to_string() }
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBracket), just(Token::RBracket)),
        )
        .or_not()
        .map(|s| s.unwrap_or_default());

    let trait_decl = just(Token::Trait)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(
            select! { Token::Ident(s) => s.to_string() }
                .delimited_by(just(Token::LBracket), just(Token::RBracket)),
        )
        .then(superclasses.clone())
        .then(trait_method.clone().repeated().collect::<Vec<_>>())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|(((name, type_var), superclasses), methods), e| Decl::DefTrait {
            name,
            type_var,
            superclasses,
            methods,
            span: to_span(e.span()),
        });

    // --- impl_parser ---
    // (impl TraitName TargetType :? [constraints]? methods...)
    // impl method: (def name [params] body)
    let impl_method_params = select! { Token::Ident(s) => s.to_string() }
        .map_with(|name, e| Param {
            name,
            ty: None,
            span: to_span(e.span()),
        })
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBracket), just(Token::RBracket));

    let impl_method = just(Token::Def)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(impl_method_params)
        .then(expr.clone())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|((name, params), body), e| FnDecl {
            name,
            params,
            constraints: vec![],
            return_type: None,
            body: Box::new(body),
            span: to_span(e.span()),
        });

    let impl_constraints = just(Token::Colon)
        .ignore_then(
            select! { Token::Ident(s) => s.to_string() }
                .then(select! { Token::Ident(s) => s.to_string() })
                .map_with(|(trait_name, type_var), e| TypeConstraint {
                    trait_name,
                    type_var,
                    span: to_span(e.span()),
                })
                .repeated()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::LBracket), just(Token::RBracket)),
        )
        .or_not()
        .map(|c| c.unwrap_or_default());

    let impl_decl = just(Token::Impl)
        .ignore_then(select! { Token::Ident(s) => s.to_string() })
        .then(ty.clone())
        .then(impl_constraints)
        .then(impl_method.repeated().collect::<Vec<_>>())
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|(((trait_name, target_type), type_constraints), methods), e| {
            Decl::DefImpl {
                trait_name,
                target_type,
                type_constraints,
                methods,
                span: to_span(e.span()),
            }
        });

    // --- import_parser ---
    // (import dotted.path [name1 name2 ...])
    let import_path = select! { Token::Ident(s) => s.to_string() }
        .separated_by(just(Token::Dot))
        .at_least(1)
        .collect::<Vec<_>>()
        .map(|parts| parts.join("."));

    let import_names = select! { Token::Ident(s) => s.to_string() }
        .repeated()
        .collect::<Vec<_>>()
        .delimited_by(just(Token::LBracket), just(Token::RBracket));

    let import_decl = just(Token::Import)
        .ignore_then(import_path)
        .then(import_names)
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map_with(|(path, names), e| Decl::Import {
            path,
            names,
            span: to_span(e.span()),
        });

    // --- Combined decl parser with error recovery ---
    choice((def_fn, type_decl, trait_decl, impl_decl, import_decl)).recover_with(via_parser(
        nested_delimiters(
            Token::LParen,
            Token::RParen,
            [(Token::LBracket, Token::RBracket)],
            |_span| Decl::Import {
                path: String::new(),
                names: vec![],
                span: (0, 0),
            },
        ),
    ))
}

fn module_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Module, extra::Err<Rich<'tokens, Token<'src>, LexSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = LexSpan>,
{
    decl_parser()
        .repeated()
        .collect::<Vec<_>>()
        .map(|decls| {
            // Filter out recovery placeholders
            let decls = decls
                .into_iter()
                .filter(|d| {
                    !matches!(d, Decl::Import { path, names, .. } if path.is_empty() && names.is_empty())
                })
                .collect();
            Module { decls }
        })
}

fn classify_parse_error(e: &Rich<Token, LexSpan>) -> ErrorCode {
    if let chumsky::error::RichReason::ExpectedFound { expected, found } = e.reason() {
        // If we hit end-of-input and expected a closing delimiter, it's unclosed
        if found.is_none() {
            return ErrorCode::P0002;
        }
        // If expected tokens include closing delimiters, it's unclosed
        for pat in expected {
            if let chumsky::error::RichPattern::Token(tok) = pat {
                let tok: &Token = tok;
                if matches!(tok, Token::RParen | Token::RBracket) {
                    return ErrorCode::P0002;
                }
            }
        }
    }
    ErrorCode::P0001
}

pub fn parse(source: &str) -> (Module, Vec<ParseError>) {
    let (tokens, lex_errors) = lexer::lexer().parse(source).into_output_errors();
    let tokens = tokens.unwrap_or_default();

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

    (module.unwrap_or(Module { decls: vec![] }), errors)
}
