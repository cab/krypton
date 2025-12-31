// Parser for S-expression syntax
// Implements the grammar from spec/types.md

use crate::ast::*;
use crate::lexer::{Span, Token};
use chumsky::{input::ValueInput, prelude::*};

/// Parse a complete program (sequence of declarations)
pub fn program_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Program, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    decl_parser()
        .repeated()
        .at_least(1)
        .collect()
        .map(|decls| Program { decls })
}

/// Parse a top-level declaration
fn decl_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Decl, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    choice((type_decl_parser(), def_decl_parser()))
}

/// Parse a type declaration: (type Name [params] body)
fn type_decl_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Decl, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    just(Token::LParen)
        .ignore_then(ident("type"))
        .ignore_then(ident_parser())
        .then(type_params_parser().or_not())
        .then(type_body_parser())
        .then_ignore(just(Token::RParen))
        .map_with(|((name, params), body), e| {
            let span: Span = e.span();
            Decl::Type {
                name,
                params: params.unwrap_or_default(),
                body,
                span: crate::ast::Span::new(span.start, span.end),
            }
        })
}

/// Parse type parameters: [a b c]
fn type_params_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Vec<String>, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    ident_parser()
        .repeated()
        .at_least(1)
        .collect()
        .delimited_by(just(Token::LBracket), just(Token::RBracket))
}

/// Parse type body: struct, sum, or alias
fn type_body_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, TypeBody, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    choice((
        struct_body_parser(),
        sum_body_parser(),
        type_expr_parser().map(TypeBody::Alias),
    ))
}

/// Parse struct body: (struct [field1 type1] [field2 type2] ...)
fn struct_body_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, TypeBody, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    just(Token::LParen)
        .ignore_then(ident("struct"))
        .ignore_then(field_parser().repeated().collect())
        .then_ignore(just(Token::RParen))
        .map(TypeBody::Struct)
}

/// Parse a field: [name type]
fn field_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Field, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    ident_parser()
        .then(type_expr_parser())
        .delimited_by(just(Token::LBracket), just(Token::RBracket))
        .map(|(name, ty)| Field { name, ty })
}

/// Parse sum type body: (| variant1 variant2 ...)
fn sum_body_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, TypeBody, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    just(Token::LParen)
        .ignore_then(just(Token::Pipe))
        .ignore_then(variant_parser().repeated().at_least(1).collect())
        .then_ignore(just(Token::RParen))
        .map(TypeBody::Sum)
}

/// Parse a sum type variant
fn variant_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Variant, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    // Tuple variant: (Name type1 type2 ...)
    let tuple_variant = just(Token::LParen)
        .ignore_then(ident_parser())
        .then(type_expr_parser().repeated().at_least(1).collect())
        .then_ignore(just(Token::RParen))
        .map(|(name, types)| Variant::Tuple(name, types));

    // Struct variant: (Name [field1 type1] ...)
    let struct_variant = just(Token::LParen)
        .ignore_then(ident_parser())
        .then(field_parser().repeated().at_least(1).collect())
        .then_ignore(just(Token::RParen))
        .map(|(name, fields)| Variant::Struct(name, fields));

    // Unit variant: Name
    let unit_variant = ident_parser().map(Variant::Unit);

    choice((tuple_variant, struct_variant, unit_variant))
}

/// Parse a type expression
fn type_expr_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Type, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    recursive(|ty| {
        // Affine type: (^move Type)
        let move_type = just(Token::LParen)
            .ignore_then(just(Token::Caret))
            .ignore_then(ident("move"))
            .ignore_then(ty.clone())
            .then_ignore(just(Token::RParen))
            .map(|t| Type::Move(Box::new(t)));

        // Function type: (fn (arg1 arg2) return)
        let fn_type = just(Token::LParen)
            .ignore_then(ident("fn"))
            .ignore_then(
                ty.clone()
                    .repeated()
                    .collect()
                    .delimited_by(just(Token::LParen), just(Token::RParen)),
            )
            .then(ty.clone())
            .then_ignore(just(Token::RParen))
            .map(|(params, ret)| Type::Function(params, Box::new(ret)));

        // Generic instantiation: (Name type1 type2 ...)
        let generic_type = just(Token::LParen)
            .ignore_then(ident_parser())
            .then(ty.clone().repeated().at_least(1).collect())
            .then_ignore(just(Token::RParen))
            .map(|(name, args)| Type::Generic(name, args));

        // Tuple type: (type1 type2 type3)
        let tuple_type = ty
            .clone()
            .repeated()
            .at_least(2)
            .collect()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(Type::Tuple);

        // Named type: Int, String, Point, etc.
        let named_type = ident_parser().map(Type::Named);

        choice((move_type, fn_type, generic_type, tuple_type, named_type))
    })
}

/// Parse function definition: (def name [params] body) or (def name [type-params] [params] body)
fn def_decl_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Decl, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    // Parse name first
    let name_parser = just(Token::LParen)
        .ignore_then(ident("def"))
        .ignore_then(ident_parser());

    // Try to parse two bracket lists (type params + params) or just one (params only)
    let params_and_type_params = type_params_parser()
        .then(param_list_parser())
        .map(|(tp, p)| (Some(tp), p))
        .or(param_list_parser().map(|p| (None, p)));

    name_parser
        .then(params_and_type_params)
        .then(just(Token::Arrow).ignore_then(type_expr_parser()).or_not())
        .then(expr_parser())
        .then_ignore(just(Token::RParen))
        .map_with(|(((name, (type_params, params)), return_type), body), e| {
            let span: Span = e.span();
            Decl::Def {
                name,
                type_params: type_params.unwrap_or_default(),
                params,
                return_type,
                body,
                span: crate::ast::Span::new(span.start, span.end),
            }
        })
}

/// Parse parameter list: [param1 param2 ...]
fn param_list_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Vec<Param>, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    param_parser()
        .repeated()
        .collect()
        .delimited_by(just(Token::LBracket), just(Token::RBracket))
}

/// Parse a single parameter
fn param_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Param, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    // (^move name type) or (^move name)
    let move_param_typed = just(Token::LParen)
        .ignore_then(just(Token::Caret))
        .ignore_then(ident("move"))
        .ignore_then(ident_parser())
        .then(type_expr_parser())
        .then_ignore(just(Token::RParen))
        .map(|(name, ty)| Param {
            name,
            ty: Some(ty),
            is_move: true,
        });

    let move_param = just(Token::LParen)
        .ignore_then(just(Token::Caret))
        .ignore_then(ident("move"))
        .ignore_then(ident_parser())
        .then_ignore(just(Token::RParen))
        .map(|name| Param {
            name,
            ty: None,
            is_move: true,
        });

    // (name type)
    let typed_param = just(Token::LParen)
        .ignore_then(ident_parser())
        .then(type_expr_parser())
        .then_ignore(just(Token::RParen))
        .map(|(name, ty)| Param {
            name,
            ty: Some(ty),
            is_move: false,
        });

    // name
    let simple_param = ident_parser().map(|name| Param {
        name,
        ty: None,
        is_move: false,
    });

    choice((move_param_typed, move_param, typed_param, simple_param))
}

/// Parse an expression
fn expr_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Expr, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    recursive(|expr| {
        // Literals
        let int_lit = select! {
            Token::Int(n) => n
        }
        .map_with(|n, e| {
            let span: Span = e.span();
            Expr::Int(n, crate::ast::Span::new(span.start, span.end))
        });

        let float_lit = select! {
            Token::Float(f) => f
        }
        .map_with(|f, e| {
            let span: Span = e.span();
            Expr::Float(f, crate::ast::Span::new(span.start, span.end))
        });

        let string_lit = select! {
            Token::String(s) => s
        }
        .map_with(|s, e| {
            let span: Span = e.span();
            Expr::String(s, crate::ast::Span::new(span.start, span.end))
        });

        let bool_lit = select! {
            Token::Bool(b) => b
        }
        .map_with(|b, e| {
            let span: Span = e.span();
            Expr::Bool(b, crate::ast::Span::new(span.start, span.end))
        });

        // Unit: ()
        let unit_lit = just(Token::LParen)
            .then_ignore(just(Token::RParen))
            .map_with(|_, e| {
                let span: Span = e.span();
                Expr::Unit(crate::ast::Span::new(span.start, span.end))
            });

        // Variable
        let var = ident_parser().map_with(|name, e| {
            let span: Span = e.span();
            Expr::Var(name, crate::ast::Span::new(span.start, span.end))
        });

        // Function: (fn [params] body)
        let function = just(Token::LParen)
            .ignore_then(ident("fn"))
            .ignore_then(param_list_parser())
            .then(expr.clone())
            .then_ignore(just(Token::RParen))
            .map_with(|(params, body), e| {
                let span: Span = e.span();
                Expr::Function(params, Box::new(body), crate::ast::Span::new(span.start, span.end))
            });

        // Let: (let [bindings] body)
        let let_expr = just(Token::LParen)
            .ignore_then(ident("let"))
            .ignore_then(binding_parser(expr.clone()).repeated().at_least(1).collect())
            .then(expr.clone())
            .then_ignore(just(Token::RParen))
            .map_with(|(bindings, body), e| {
                let span: Span = e.span();
                Expr::Let(bindings, Box::new(body), crate::ast::Span::new(span.start, span.end))
            });

        // If: (if cond then else)
        let if_expr = just(Token::LParen)
            .ignore_then(ident("if"))
            .ignore_then(expr.clone())
            .then(expr.clone())
            .then(expr.clone())
            .then_ignore(just(Token::RParen))
            .map_with(|((cond, then_br), else_br), e| {
                let span: Span = e.span();
                Expr::If(
                    Box::new(cond),
                    Box::new(then_br),
                    Box::new(else_br),
                    crate::ast::Span::new(span.start, span.end),
                )
            });

        // Match: (match scrutinee branches...)
        let match_expr = just(Token::LParen)
            .ignore_then(ident("match"))
            .ignore_then(expr.clone())
            .then(match_branch_parser(expr.clone()).repeated().at_least(1).collect())
            .then_ignore(just(Token::RParen))
            .map_with(|(scrutinee, branches), e| {
                let span: Span = e.span();
                Expr::Match(
                    Box::new(scrutinee),
                    branches,
                    crate::ast::Span::new(span.start, span.end),
                )
            });

        // Field access: (. obj field)
        let field_access = just(Token::LParen)
            .ignore_then(just(Token::Dot))
            .ignore_then(expr.clone())
            .then(ident_parser())
            .then_ignore(just(Token::RParen))
            .map_with(|(obj, field), e| {
                let span: Span = e.span();
                Expr::FieldAccess(Box::new(obj), field, crate::ast::Span::new(span.start, span.end))
            });

        // Struct literal: (TypeName field1: val1 field2: val2)
        let struct_lit = just(Token::LParen)
            .ignore_then(ident_parser())
            .then(
                ident_parser()
                    .then_ignore(just(Token::Colon))
                    .then(expr.clone())
                    .repeated()
                    .at_least(1)
                    .collect(),
            )
            .then_ignore(just(Token::RParen))
            .map_with(|(name, fields), e| {
                let span: Span = e.span();
                Expr::StructLit(name, fields, crate::ast::Span::new(span.start, span.end))
            });

        // Function call: (f arg1 arg2 ...)
        let call = just(Token::LParen)
            .ignore_then(expr.clone())
            .then(expr.clone().repeated().collect())
            .then_ignore(just(Token::RParen))
            .map_with(|(func, args), e| {
                let span: Span = e.span();
                Expr::Call(Box::new(func), args, crate::ast::Span::new(span.start, span.end))
            });

        choice((
            int_lit,
            float_lit,
            string_lit,
            bool_lit,
            unit_lit,
            function,
            let_expr,
            if_expr,
            match_expr,
            field_access,
            struct_lit,
            call,
            var,
        ))
    })
}

/// Parse a let binding: [name expr] or [name type expr]
fn binding_parser<'tokens, 'src: 'tokens, I>(
    expr: impl Parser<'tokens, I, Expr, extra::Err<Rich<'tokens, Token, Span>>> + Clone + 'tokens,
) -> impl Parser<'tokens, I, Binding, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    ident_parser()
        .then(type_expr_parser().or_not())
        .then(expr)
        .delimited_by(just(Token::LBracket), just(Token::RBracket))
        .map(|((name, ty), value)| Binding { name, ty, value })
}

/// Parse a match branch: (pattern body) or (pattern if guard body)
fn match_branch_parser<'tokens, 'src: 'tokens, I>(
    expr: impl Parser<'tokens, I, Expr, extra::Err<Rich<'tokens, Token, Span>>> + Clone + 'tokens,
) -> impl Parser<'tokens, I, MatchBranch, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    pattern_parser()
        .then(ident("if").ignore_then(expr.clone()).or_not())
        .then(expr)
        .delimited_by(just(Token::LParen), just(Token::RParen))
        .map(|((pattern, guard), body)| MatchBranch {
            pattern,
            guard,
            body,
        })
}

/// Parse a pattern
fn pattern_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, Pattern, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    recursive(|pattern| {
        // Wildcard: _
        let wildcard = ident("_").to(Pattern::Wildcard);

        // Unit: ()
        let unit = just(Token::LParen)
            .then_ignore(just(Token::RParen))
            .to(Pattern::Unit);

        // Int literal
        let int_pat = select! {
            Token::Int(n) => Pattern::Int(n)
        };

        // String literal
        let string_pat = select! {
            Token::String(s) => Pattern::String(s)
        };

        // Bool literal
        let bool_pat = select! {
            Token::Bool(b) => Pattern::Bool(b)
        };

        // Struct pattern: (Name field1: p1 field2: p2)
        let struct_pat = just(Token::LParen)
            .ignore_then(ident_parser())
            .then(
                ident_parser()
                    .then_ignore(just(Token::Colon))
                    .then(pattern.clone())
                    .repeated()
                    .at_least(1)
                    .collect(),
            )
            .then_ignore(just(Token::RParen))
            .map(|(name, fields)| Pattern::Struct(name, fields));

        // Constructor pattern: (Name patterns...)
        let constructor = just(Token::LParen)
            .ignore_then(ident_parser())
            .then(pattern.clone().repeated().collect())
            .then_ignore(just(Token::RParen))
            .map(|(name, patterns)| Pattern::Constructor(name, patterns));

        // Tuple pattern: (p1 p2 p3) - needs at least 2 patterns
        let tuple_pat = pattern
            .clone()
            .repeated()
            .at_least(2)
            .collect()
            .delimited_by(just(Token::LParen), just(Token::RParen))
            .map(Pattern::Tuple);

        // Variable
        let var_pat = ident_parser().map(Pattern::Var);

        choice((
            wildcard,
            unit,
            int_pat,
            string_pat,
            bool_pat,
            struct_pat,
            constructor,
            tuple_pat,
            var_pat,
        ))
    })
}

/// Helper: parse a specific identifier
fn ident<'tokens, 'src: 'tokens, I>(
    s: &'static str,
) -> impl Parser<'tokens, I, String, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    select! {
        Token::Ident(id) if id == s => id
    }
}

/// Helper: parse any identifier
fn ident_parser<'tokens, 'src: 'tokens, I>(
) -> impl Parser<'tokens, I, String, extra::Err<Rich<'tokens, Token, Span>>> + Clone
where
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    select! {
        Token::Ident(id) => id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lexer;

    fn parse_type(input: &str) -> Type {
        let tokens = lexer().parse(input).into_result().unwrap();
        let len = input.len();
        type_expr_parser()
            .parse(tokens.as_slice().map((len..len).into(), |(t, s)| (t, s)))
            .into_result()
            .unwrap()
    }

    fn parse_expr(input: &str) -> Expr {
        let tokens = lexer().parse(input).into_result().unwrap();
        let len = input.len();
        expr_parser()
            .parse(tokens.as_slice().map((len..len).into(), |(t, s)| (t, s)))
            .into_result()
            .unwrap()
    }

    #[test]
    fn test_parse_named_type() {
        let ty = parse_type("Int");
        assert_eq!(ty, Type::Named("Int".to_string()));
    }

    #[test]
    fn test_parse_generic_type() {
        let ty = parse_type("(Option Int)");
        assert_eq!(
            ty,
            Type::Generic("Option".to_string(), vec![Type::Named("Int".to_string())])
        );
    }

    #[test]
    fn test_parse_function_type() {
        let ty = parse_type("(fn (Int String) Bool)");
        assert_eq!(
            ty,
            Type::Function(
                vec![
                    Type::Named("Int".to_string()),
                    Type::Named("String".to_string())
                ],
                Box::new(Type::Named("Bool".to_string()))
            )
        );
    }

    #[test]
    fn test_parse_move_type() {
        let ty = parse_type("(^move Buffer)");
        assert_eq!(
            ty,
            Type::Move(Box::new(Type::Named("Buffer".to_string())))
        );
    }

    #[test]
    fn test_parse_int_literal() {
        let expr = parse_expr("42");
        assert!(matches!(expr, Expr::Int(42, _)));
    }

    #[test]
    fn test_parse_string_literal() {
        let expr = parse_expr(r#""hello""#);
        assert!(matches!(expr, Expr::String(s, _) if s == "hello"));
    }

    #[test]
    fn test_parse_variable() {
        let expr = parse_expr("x");
        assert!(matches!(expr, Expr::Var(name, _) if name == "x"));
    }

    #[test]
    fn test_parse_function() {
        let expr = parse_expr("(fn [x y] x)");
        assert!(matches!(expr, Expr::Function(_, _, _)));
    }

    #[test]
    fn test_parse_call() {
        let expr = parse_expr("(add 1 2)");
        assert!(matches!(expr, Expr::Call(_, _, _)));
    }

    #[test]
    fn test_parse_if() {
        let expr = parse_expr("(if true 1 2)");
        assert!(matches!(expr, Expr::If(_, _, _, _)));
    }

    #[test]
    fn test_parse_let() {
        let expr = parse_expr("(let [x 42] x)");
        assert!(matches!(expr, Expr::Let(_, _, _)));
    }
}
