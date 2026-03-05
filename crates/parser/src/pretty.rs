use crate::ast::*;

pub fn pretty_print(module: &Module) -> String {
    let mut parts: Vec<String> = Vec::new();
    for decl in &module.decls {
        parts.push(pp_decl(decl));
    }
    parts.join("\n")
}

fn pp_decl(decl: &Decl) -> String {
    match decl {
        Decl::DefFn(f) => pp_def_fn(f),
        Decl::DefType(t) => pp_def_type(t),
        Decl::DefTrait {
            name,
            type_var,
            superclasses,
            methods,
            ..
        } => pp_trait(name, type_var, superclasses, methods),
        Decl::DefImpl {
            trait_name,
            target_type,
            type_constraints,
            methods,
            ..
        } => pp_impl(trait_name, target_type, type_constraints, methods),
        Decl::Import { path, names, .. } => {
            let names_str = names.join(" ");
            format!("(import {path} [{names_str}])")
        }
    }
}

fn pp_def_fn(f: &FnDecl) -> String {
    let params_str = f.params.iter().map(|p| p.name.clone()).collect::<Vec<_>>().join(" ");
    let has_types = f.params.iter().any(|p| p.ty.is_some());

    if has_types {
        let type_strs: Vec<String> = f.params.iter().map(|p| {
            p.ty.as_ref().map(pp_type_expr).unwrap_or_else(|| "_".to_string())
        }).collect();
        let types_str = type_strs.join(" ");
        let ret = f.return_type.as_ref().map(pp_type_expr).unwrap_or_else(|| "Unit".to_string());
        let body = pp_expr(&f.body);
        format!("(def {} (fn [{}] [{}] {} {}))", f.name, params_str, types_str, ret, body)
    } else {
        let body = pp_expr(&f.body);
        format!("(def {} (fn [{}] {}))", f.name, params_str, body)
    }
}

fn pp_def_type(t: &TypeDecl) -> String {
    let mut s = String::from("(type ");
    s.push_str(&t.name);
    if !t.type_params.is_empty() {
        s.push_str(" [");
        s.push_str(&t.type_params.join(" "));
        s.push(']');
    }
    s.push(' ');
    match &t.kind {
        TypeDeclKind::Record { fields } => {
            s.push_str("(record");
            for (name, ty) in fields {
                s.push_str(&format!(" ({} {})", name, pp_type_expr(ty)));
            }
            s.push(')');
        }
        TypeDeclKind::Sum { variants } => {
            s.push_str("(|");
            for v in variants {
                s.push(' ');
                if v.fields.is_empty() {
                    s.push_str(&v.name);
                } else {
                    s.push('(');
                    s.push_str(&v.name);
                    for f in &v.fields {
                        s.push(' ');
                        s.push_str(&pp_type_expr(f));
                    }
                    s.push(')');
                }
            }
            s.push(')');
        }
    }
    if !t.deriving.is_empty() {
        s.push_str(" deriving [");
        s.push_str(&t.deriving.join(" "));
        s.push(']');
    }
    s.push(')');
    s
}

fn pp_trait(name: &str, type_var: &str, superclasses: &[String], methods: &[FnDecl]) -> String {
    let mut s = format!("(trait {} [{}]", name, type_var);
    if !superclasses.is_empty() {
        s.push_str(" : [");
        s.push_str(&superclasses.join(" "));
        s.push(']');
    }
    for m in methods {
        s.push(' ');
        s.push_str(&pp_trait_method(m));
    }
    s.push(')');
    s
}

fn pp_trait_method(m: &FnDecl) -> String {
    let type_strs: Vec<String> = m.params.iter().map(|p| {
        p.ty.as_ref().map(pp_type_expr).unwrap_or_else(|| "_".to_string())
    }).collect();
    let types_str = type_strs.join(" ");

    let is_unit_body = matches!(&*m.body, Expr::Lit { value: Lit::Unit, .. });

    let mut s = format!("(def {} [{}]", m.name, types_str);
    if let Some(ret) = &m.return_type {
        s.push(' ');
        s.push_str(&pp_type_expr(ret));
    }
    if !is_unit_body {
        s.push(' ');
        s.push_str(&pp_expr(&m.body));
    }
    s.push(')');
    s
}

fn pp_impl(
    trait_name: &str,
    target_type: &TypeExpr,
    constraints: &[TypeConstraint],
    methods: &[FnDecl],
) -> String {
    let mut s = format!("(impl {} {}", trait_name, pp_type_expr(target_type));
    if !constraints.is_empty() {
        s.push_str(" : [");
        let cs: Vec<String> = constraints.iter().map(|c| format!("{} {}", c.trait_name, c.type_var)).collect();
        s.push_str(&cs.join(" "));
        s.push(']');
    }
    for m in methods {
        s.push(' ');
        s.push_str(&pp_impl_method(m));
    }
    s.push(')');
    s
}

fn pp_impl_method(m: &FnDecl) -> String {
    let params_str = m.params.iter().map(|p| p.name.clone()).collect::<Vec<_>>().join(" ");
    let body = pp_expr(&m.body);
    format!("(def {} [{}] {})", m.name, params_str, body)
}

fn pp_expr(expr: &Expr) -> String {
    match expr {
        Expr::Lit { value, .. } => pp_lit(value),
        Expr::Var { name, .. } => name.clone(),
        Expr::BinaryOp { op, lhs, rhs, .. } => {
            format!("({} {} {})", pp_binop(op), pp_expr(lhs), pp_expr(rhs))
        }
        Expr::UnaryOp { op, operand, .. } => match op {
            UnaryOp::Neg => format!("(- {})", pp_expr(operand)),
        },
        Expr::Lambda { params, body, .. } => {
            let params_str = params.iter().map(|p| p.name.clone()).collect::<Vec<_>>().join(" ");
            format!("(fn [{}] {})", params_str, pp_expr(body))
        }
        Expr::Let { name, value, .. } => {
            format!("(let {} {})", name, pp_expr(value))
        }
        Expr::Do { exprs, .. } => {
            let parts: Vec<String> = exprs.iter().map(pp_expr).collect();
            format!("(do {})", parts.join(" "))
        }
        Expr::If { cond, then_, else_, .. } => {
            format!("(if {} {} {})", pp_expr(cond), pp_expr(then_), pp_expr(else_))
        }
        Expr::App { func, args, .. } => {
            let mut parts = vec![pp_expr(func)];
            parts.extend(args.iter().map(pp_expr));
            format!("({})", parts.join(" "))
        }
        Expr::Match { scrutinee, arms, .. } => {
            let mut s = format!("(match {}", pp_expr(scrutinee));
            for arm in arms {
                s.push_str(&format!(" ({} {})", pp_pattern(&arm.pattern), pp_expr(&arm.body)));
            }
            s.push(')');
            s
        }
        Expr::FieldAccess { expr, field, .. } => {
            format!("(. {} {})", pp_expr(expr), field)
        }
        Expr::QuestionMark { expr, .. } => {
            format!("(? {})", pp_expr(expr))
        }
        Expr::List { elements, .. } => {
            let parts: Vec<String> = elements.iter().map(pp_expr).collect();
            format!("(list {})", parts.join(" "))
        }
        Expr::Tuple { elements, .. } => {
            let parts: Vec<String> = elements.iter().map(pp_expr).collect();
            format!("(tuple {})", parts.join(" "))
        }
        Expr::Recur { args, .. } => {
            let parts: Vec<String> = args.iter().map(pp_expr).collect();
            format!("(recur {})", parts.join(" "))
        }
        Expr::StructLit { name, fields, .. } => {
            let mut s = format!("({}", name);
            for (fname, fval) in fields {
                s.push_str(&format!(" ({} {})", fname, pp_expr(fval)));
            }
            s.push(')');
            s
        }
        Expr::LetPattern { pattern, value, .. } => {
            format!("(let {} {})", pp_pattern(pattern), pp_expr(value))
        }
        Expr::StructUpdate { base, fields, .. } => {
            let mut s = format!("(.. {}", pp_expr(base));
            for (fname, fval) in fields {
                s.push_str(&format!(" ({} {})", fname, pp_expr(fval)));
            }
            s.push(')');
            s
        }
    }
}

fn pp_lit(lit: &Lit) -> String {
    match lit {
        Lit::Int(n) => n.to_string(),
        Lit::Float(f) => {
            let s = f.to_string();
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Lit::Bool(b) => b.to_string(),
        Lit::String(s) => format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\"")),
        Lit::Unit => "()".to_string(),
    }
}

fn pp_binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Eq => "==",
        BinOp::Neq => "!=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::Le => "<=",
        BinOp::Ge => ">=",
    }
}

fn pp_pattern(pat: &Pattern) -> String {
    match pat {
        Pattern::Wildcard { .. } => "_".to_string(),
        Pattern::Var { name, .. } => name.clone(),
        Pattern::Constructor { name, args, .. } => {
            if args.is_empty() {
                name.clone()
            } else {
                let mut parts = vec![name.clone()];
                parts.extend(args.iter().map(pp_pattern));
                format!("({})", parts.join(" "))
            }
        }
        Pattern::Lit { value, .. } => pp_lit(value),
        Pattern::Tuple { elements, .. } => {
            let parts: Vec<String> = elements.iter().map(pp_pattern).collect();
            format!("(tuple {})", parts.join(" "))
        }
        Pattern::StructPat { name, fields, .. } => {
            let mut s = format!("({}", name);
            for (fname, fpat) in fields {
                s.push_str(&format!(" ({} {})", fname, pp_pattern(fpat)));
            }
            s.push(')');
            s
        }
    }
}

fn pp_type_expr(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named { name, .. } => name.clone(),
        TypeExpr::Var { name, .. } => name.clone(),
        TypeExpr::App { name, args, .. } => {
            let mut parts = vec![name.clone()];
            parts.extend(args.iter().map(pp_type_expr));
            format!("({})", parts.join(" "))
        }
        TypeExpr::Fn { params, ret, .. } => {
            let params_str: Vec<String> = params.iter().map(pp_type_expr).collect();
            format!("(fn [{}] {})", params_str.join(" "), pp_type_expr(ret))
        }
        TypeExpr::Own { inner, .. } => {
            format!("(own {})", pp_type_expr(inner))
        }
        TypeExpr::Tuple { elements, .. } => {
            let parts: Vec<String> = elements.iter().map(pp_type_expr).collect();
            format!("(tuple {})", parts.join(" "))
        }
    }
}
