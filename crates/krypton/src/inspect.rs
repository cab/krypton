use krypton_parser::ast::{Decl, Module, TypeExpr};
use krypton_typechecker::typed_ast::{
    AutoCloseInfo, FnTypeEntry, InstanceDefInfo, TypedExpr, TypedExprKind, TypedFnDecl,
    TypedPattern,
};
use krypton_typechecker::types::Type;

/// Convert a Type to Krypton source syntax.
/// Differences from Display: `own X` → `~X`, `fn(X) -> Y` → `(X) -> Y`
/// When `var_names` is provided, uses those names for type variables instead of
/// the default display_name().
fn type_to_source(ty: &Type, var_names: Option<&[String]>) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Float => "Float".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::String => "String".to_string(),
        Type::Unit => "Unit".to_string(),
        Type::Var(id) => {
            if let Some(names) = var_names {
                let idx = id.index();
                if idx < names.len() {
                    return names[idx].clone();
                }
            }
            id.display_name()
        }
        Type::Own(inner) => format!("~{}", type_to_source(inner, var_names)),
        Type::Fn(params, ret) => {
            let ps: Vec<String> = params.iter().map(|p| type_to_source(p, var_names)).collect();
            format!("({}) -> {}", ps.join(", "), type_to_source(ret, var_names))
        }
        Type::Named(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let as_: Vec<String> = args.iter().map(|a| type_to_source(a, var_names)).collect();
                format!("{}[{}]", name, as_.join(", "))
            }
        }
        Type::App(ctor, args) => {
            let base = type_to_source(ctor, var_names);
            if args.is_empty() {
                base
            } else {
                let as_: Vec<String> = args.iter().map(|a| type_to_source(a, var_names)).collect();
                format!("{}[{}]", base, as_.join(", "))
            }
        }
        Type::Tuple(elems) => {
            let es: Vec<String> = elems.iter().map(|e| type_to_source(e, var_names)).collect();
            format!("({})", es.join(", "))
        }
        Type::FnHole => "_".to_string(),
    }
}

struct TypedFormatter<'a> {
    indent_level: usize,
    buf: String,
    auto_close: &'a AutoCloseInfo,
    /// Display names for type variables, computed from the scheme's display_var_names().
    var_names: Option<Vec<String>>,
}

impl<'a> TypedFormatter<'a> {
    fn type_str(&self, ty: &Type) -> String {
        type_to_source(ty, self.var_names.as_deref())
    }

    fn indent(&mut self) {
        for _ in 0..self.indent_level * 4 {
            self.buf.push(' ');
        }
    }

    fn push_indent_comment(&mut self, text: &str) {
        self.indent();
        self.buf.push_str("# ");
        self.buf.push_str(text);
        self.buf.push('\n');
    }

    /// Emit close comments for a given span key and close type.
    fn emit_close_comments_for_span(&mut self, span: &(usize, usize), reason: &str) {
        // shadow_closes
        if reason == "shadow" {
            if let Some(binding) = self.auto_close.shadow_closes.get(span) {
                self.push_indent_comment(&format!("close({}) [shadow]", binding.name));
            }
        }
        // early_returns
        if reason == "early return" {
            if let Some(bindings) = self.auto_close.early_returns.get(span) {
                for binding in bindings {
                    self.push_indent_comment(&format!("close({}) [early return]", binding.name));
                }
            }
        }
        // recur_closes
        if reason == "recur" {
            if let Some(bindings) = self.auto_close.recur_closes.get(span) {
                for binding in bindings {
                    self.push_indent_comment(&format!("close({}) [recur]", binding.name));
                }
            }
        }
    }

    fn emit_move_comments_for_span(&mut self, span: &(usize, usize)) {
        if let Some(bindings) = self.auto_close.consumptions.get(span) {
            for binding in bindings {
                self.push_indent_comment(&format!("move: {}", binding.name));
            }
        }
    }

    fn fmt_fn_decl(
        &mut self,
        typed_fn: &TypedFnDecl,
        fn_type: &Type,
    ) {
        let (param_types, ret_type) = match fn_type {
            Type::Fn(params, ret) => (params.clone(), self.type_str(ret)),
            _ => (vec![], self.type_str(fn_type)),
        };

        self.buf.push_str("fun ");
        self.buf.push_str(&typed_fn.name);
        self.buf.push('(');
        for (i, param_name) in typed_fn.params.iter().enumerate() {
            if i > 0 {
                self.buf.push_str(", ");
            }
            self.buf.push_str(param_name);
            if let Some(ty) = param_types.get(i) {
                self.buf.push_str(": ");
                self.buf.push_str(&self.type_str(ty));
            }
        }
        self.buf.push_str(") -> ");
        self.buf.push_str(&ret_type);

        // Body
        match &typed_fn.body.kind {
            TypedExprKind::Do(exprs) => {
                self.buf.push_str(" {\n");
                self.indent_level += 1;
                self.fmt_block_stmts(exprs, &typed_fn.name);
                // Scope exit closes before closing brace
                if let Some(bindings) = self.auto_close.fn_exits.get(&typed_fn.name) {
                    for binding in bindings {
                        self.push_indent_comment(&format!("close({}) [scope exit]", binding.name));
                    }
                }
                self.indent_level -= 1;
                self.indent();
                self.buf.push('}');
            }
            _ => {
                self.buf.push_str(" = ");
                self.fmt_expr(&typed_fn.body);
            }
        }
    }

    /// Format an impl method with types from the TypedAST.
    fn fmt_impl_method(
        &mut self,
        display_name: &str,
        typed_fn: &TypedFnDecl,
        fn_type: &Type,
    ) {
        let (param_types, ret_type) = match fn_type {
            Type::Fn(params, ret) => (params.clone(), self.type_str(ret)),
            _ => (vec![], self.type_str(fn_type)),
        };

        self.buf.push_str("fun ");
        self.buf.push_str(display_name);
        self.buf.push('(');
        for (i, param_name) in typed_fn.params.iter().enumerate() {
            if i > 0 {
                self.buf.push_str(", ");
            }
            self.buf.push_str(param_name);
            if let Some(ty) = param_types.get(i) {
                self.buf.push_str(": ");
                self.buf.push_str(&self.type_str(ty));
            }
        }
        self.buf.push_str(") -> ");
        self.buf.push_str(&ret_type);

        match &typed_fn.body.kind {
            TypedExprKind::Do(exprs) => {
                self.buf.push_str(" {\n");
                self.indent_level += 1;
                self.fmt_block_stmts(exprs, &typed_fn.name);
                self.indent_level -= 1;
                self.indent();
                self.buf.push('}');
            }
            _ => {
                self.buf.push_str(" = ");
                self.fmt_expr(&typed_fn.body);
            }
        }
    }

    /// Emit early return close comments for any QuestionMark nested in a value expr.
    fn emit_early_return_closes_in_value(&mut self, expr: &TypedExpr) {
        match &expr.kind {
            TypedExprKind::QuestionMark { .. } => {
                self.emit_close_comments_for_span(&expr.span, "early return");
            }
            TypedExprKind::App { func, args } => {
                self.emit_early_return_closes_in_value(func);
                for arg in args {
                    self.emit_early_return_closes_in_value(arg);
                }
            }
            _ => {}
        }
    }

    fn fmt_block_stmts(&mut self, exprs: &[TypedExpr], fn_name: &str) {
        for (i, expr) in exprs.iter().enumerate() {
            let is_last = i == exprs.len() - 1;

            // Check for shadow closes on Let expressions
            if matches!(&expr.kind, TypedExprKind::Let { .. } | TypedExprKind::LetPattern { .. }) {
                self.emit_close_comments_for_span(&expr.span, "shadow");
            }

            // Check for early return closes on expressions with ? in their value
            match &expr.kind {
                TypedExprKind::Let { value, .. } | TypedExprKind::LetPattern { value, .. } => {
                    self.emit_early_return_closes_in_value(value);
                }
                TypedExprKind::QuestionMark { .. } => {
                    self.emit_close_comments_for_span(&expr.span, "early return");
                }
                _ => {}
            }

            self.indent();
            self.fmt_stmt(expr, fn_name);

            // Semicolons between statements (not after last)
            if !is_last {
                // Don't add semicolons after let statements — they end at the newline
                match &expr.kind {
                    TypedExprKind::Let { body: None, .. }
                    | TypedExprKind::LetPattern { body: None, .. } => {}
                    _ => {}
                }
            }
            self.buf.push('\n');

            // Move comments after consuming expressions
            self.emit_move_comments_for_span(&expr.span);

            // Check inner expressions for moves too
            self.emit_nested_moves(expr);
        }
    }

    fn emit_nested_moves(&mut self, expr: &TypedExpr) {
        match &expr.kind {
            TypedExprKind::App { func, args } => {
                self.emit_move_comments_for_span(&func.span);
                for arg in args {
                    self.emit_move_comments_for_span(&arg.span);
                    self.emit_nested_moves(arg);
                }
            }
            TypedExprKind::Let { value, .. } | TypedExprKind::LetPattern { value, .. } => {
                self.emit_move_comments_for_span(&value.span);
                self.emit_nested_moves(value);
            }
            _ => {}
        }
    }

    fn fmt_stmt(&mut self, expr: &TypedExpr, fn_name: &str) {
        match &expr.kind {
            TypedExprKind::Let { name, value, body: None } => {
                self.buf.push_str("let ");
                self.buf.push_str(name);
                self.buf.push_str(": ");
                self.buf.push_str(&self.type_str(&value.ty));
                self.buf.push_str(" = ");
                self.fmt_expr(value);
            }
            TypedExprKind::Let { name, value, body: Some(body) } => {
                self.buf.push_str("let ");
                self.buf.push_str(name);
                self.buf.push_str(": ");
                self.buf.push_str(&self.type_str(&value.ty));
                self.buf.push_str(" = ");
                self.fmt_expr(value);
                self.buf.push('\n');
                self.emit_move_comments_for_span(&value.span);
                self.emit_nested_moves(value);
                self.indent();
                self.fmt_stmt(body, fn_name);
            }
            TypedExprKind::LetPattern { pattern, value, body: None } => {
                self.buf.push_str("let ");
                self.fmt_typed_pattern(pattern);
                self.buf.push_str(": ");
                self.buf.push_str(&self.type_str(&value.ty));
                self.buf.push_str(" = ");
                self.fmt_expr(value);
            }
            TypedExprKind::LetPattern { pattern, value, body: Some(body) } => {
                self.buf.push_str("let ");
                self.fmt_typed_pattern(pattern);
                self.buf.push_str(": ");
                self.buf.push_str(&self.type_str(&value.ty));
                self.buf.push_str(" = ");
                self.fmt_expr(value);
                self.buf.push('\n');
                self.emit_move_comments_for_span(&value.span);
                self.emit_nested_moves(value);
                self.indent();
                self.fmt_stmt(body, fn_name);
            }
            _ => self.fmt_expr(expr),
        }
    }

    fn fmt_expr(&mut self, expr: &TypedExpr) {
        self.fmt_expr_prec(expr, 0);
    }

    fn fmt_expr_prec(&mut self, expr: &TypedExpr, parent_prec: u8) {
        match &expr.kind {
            TypedExprKind::Lit(lit) => self.fmt_lit(lit),
            TypedExprKind::Var(name) => self.buf.push_str(name),
            TypedExprKind::App { func, args } => {
                self.fmt_expr_prec(func, 7);
                self.buf.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_expr(arg);
                }
                self.buf.push(')');
            }
            TypedExprKind::TypeApp { expr, .. } => {
                self.fmt_expr_prec(expr, parent_prec);
            }
            TypedExprKind::If { cond, then_, else_ } => {
                self.buf.push_str("if ");
                self.fmt_expr(cond);
                self.buf.push_str(" { ");
                self.fmt_expr(then_);
                self.buf.push_str(" }");
                if !matches!(&else_.kind, TypedExprKind::Lit(krypton_parser::ast::Lit::Unit)) {
                    self.buf.push_str(" else { ");
                    self.fmt_expr(else_);
                    self.buf.push_str(" }");
                }
            }
            TypedExprKind::Let { name, value, body } => {
                // Let appearing as expression (not as statement in Do block)
                match body {
                    Some(body_expr) => {
                        self.buf.push_str("{ let ");
                        self.buf.push_str(name);
                        self.buf.push_str(": ");
                        self.buf.push_str(&self.type_str(&value.ty));
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                        self.buf.push_str("; ");
                        self.fmt_expr(body_expr);
                        self.buf.push_str(" }");
                    }
                    None => {
                        self.buf.push_str("let ");
                        self.buf.push_str(name);
                        self.buf.push_str(": ");
                        self.buf.push_str(&self.type_str(&value.ty));
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                    }
                }
            }
            TypedExprKind::LetPattern { pattern, value, body } => {
                match body {
                    Some(body_expr) => {
                        self.buf.push_str("{ let ");
                        self.fmt_typed_pattern(pattern);
                        self.buf.push_str(": ");
                        self.buf.push_str(&self.type_str(&value.ty));
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                        self.buf.push_str("; ");
                        self.fmt_expr(body_expr);
                        self.buf.push_str(" }");
                    }
                    None => {
                        self.buf.push_str("let ");
                        self.fmt_typed_pattern(pattern);
                        self.buf.push_str(": ");
                        self.buf.push_str(&self.type_str(&value.ty));
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                    }
                }
            }
            TypedExprKind::Do(exprs) => {
                self.buf.push_str("{\n");
                self.indent_level += 1;
                self.fmt_block_stmts(exprs, "");
                self.indent_level -= 1;
                self.indent();
                self.buf.push('}');
            }
            TypedExprKind::Match { scrutinee, arms } => {
                self.buf.push_str("match ");
                self.fmt_expr(scrutinee);
                self.buf.push_str(" {\n");
                self.indent_level += 1;
                for arm in arms {
                    self.indent();
                    self.fmt_typed_pattern(&arm.pattern);
                    self.buf.push_str(" => ");
                    self.fmt_expr(&arm.body);
                    self.buf.push_str(",\n");
                }
                self.indent_level -= 1;
                self.indent();
                self.buf.push('}');
            }
            TypedExprKind::Lambda { params, body } => {
                if params.is_empty() {
                    self.buf.push_str("() -> ");
                    self.fmt_expr(body);
                } else {
                    // Extract param types from the lambda's own type
                    let param_types = match &expr.ty {
                        Type::Fn(pts, _) => Some(pts.clone()),
                        _ => None,
                    };
                    if params.len() == 1 && param_types.is_none() {
                        self.buf.push_str(&params[0]);
                        self.buf.push_str(" -> ");
                        self.fmt_expr(body);
                    } else {
                        self.buf.push('(');
                        for (i, p) in params.iter().enumerate() {
                            if i > 0 {
                                self.buf.push_str(", ");
                            }
                            self.buf.push_str(p);
                            if let Some(ref pts) = param_types {
                                if let Some(ty) = pts.get(i) {
                                    self.buf.push_str(": ");
                                    self.buf.push_str(&self.type_str(ty));
                                }
                            }
                        }
                        self.buf.push_str(") -> ");
                        self.fmt_expr(body);
                    }
                }
            }
            TypedExprKind::FieldAccess { expr: inner, field } => {
                self.fmt_expr_prec(inner, 7);
                self.buf.push('.');
                self.buf.push_str(field);
            }
            TypedExprKind::BinaryOp { op, lhs, rhs } => {
                let prec = binop_precedence(op);
                let need_parens = prec < parent_prec;
                if need_parens {
                    self.buf.push('(');
                }
                self.fmt_expr_prec(lhs, prec);
                self.buf.push(' ');
                self.buf.push_str(binop_str(op));
                self.buf.push(' ');
                let right_prec = if is_left_assoc(op) || is_non_assoc(op) {
                    prec + 1
                } else {
                    prec
                };
                self.fmt_expr_prec(rhs, right_prec);
                if need_parens {
                    self.buf.push(')');
                }
            }
            TypedExprKind::UnaryOp { op, operand } => {
                let prec = 6;
                let need_parens = prec < parent_prec;
                if need_parens {
                    self.buf.push('(');
                }
                match op {
                    krypton_parser::ast::UnaryOp::Neg => self.buf.push('-'),
                    krypton_parser::ast::UnaryOp::Not => self.buf.push('!'),
                }
                self.fmt_expr_prec(operand, prec);
                if need_parens {
                    self.buf.push(')');
                }
            }
            TypedExprKind::QuestionMark { expr: inner, .. } => {
                self.fmt_expr_prec(inner, 7);
                self.buf.push('?');
            }
            TypedExprKind::Recur(args) => {
                // Emit recur closes before the recur call
                self.emit_close_comments_for_span(&expr.span, "recur");
                self.buf.push_str("recur(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_expr(arg);
                }
                self.buf.push(')');
            }
            TypedExprKind::Tuple(elems) => {
                self.buf.push('(');
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_expr(e);
                }
                self.buf.push(')');
            }
            TypedExprKind::VecLit(elems) => {
                self.buf.push('[');
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_expr(e);
                }
                self.buf.push(']');
            }
            TypedExprKind::StructLit { name, fields } => {
                self.buf.push_str(name);
                self.buf.push_str(" { ");
                for (i, (fname, fval)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    if is_punnable_typed(fname, fval) {
                        self.buf.push_str(fname);
                    } else {
                        self.buf.push_str(fname);
                        self.buf.push_str(" = ");
                        self.fmt_expr(fval);
                    }
                }
                self.buf.push_str(" }");
            }
            TypedExprKind::StructUpdate { base, fields } => {
                self.buf.push_str("{ ");
                self.fmt_expr(base);
                self.buf.push_str(" | ");
                for (i, (fname, fval)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    if is_punnable_typed(fname, fval) {
                        self.buf.push_str(fname);
                    } else {
                        self.buf.push_str(fname);
                        self.buf.push_str(" = ");
                        self.fmt_expr(fval);
                    }
                }
                self.buf.push_str(" }");
            }
        }
    }

    fn fmt_lit(&mut self, lit: &krypton_parser::ast::Lit) {
        use krypton_parser::ast::Lit;
        match lit {
            Lit::Int(n) => self.buf.push_str(&n.to_string()),
            Lit::Float(f) => {
                let s = f.to_string();
                if s.contains('.') {
                    self.buf.push_str(&s);
                } else {
                    self.buf.push_str(&format!("{s}.0"));
                }
            }
            Lit::Bool(b) => self.buf.push_str(&b.to_string()),
            Lit::String(s) => {
                self.buf.push('"');
                self.buf
                    .push_str(&s.replace('\\', "\\\\").replace('"', "\\\""));
                self.buf.push('"');
            }
            Lit::Unit => self.buf.push_str("()"),
        }
    }

    fn fmt_typed_pattern(&mut self, pat: &TypedPattern) {
        match pat {
            TypedPattern::Wildcard { .. } => self.buf.push('_'),
            TypedPattern::Var { name, .. } => self.buf.push_str(name),
            TypedPattern::Constructor { name, args, .. } => {
                self.buf.push_str(name);
                if !args.is_empty() {
                    self.buf.push('(');
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.buf.push_str(", ");
                        }
                        self.fmt_typed_pattern(arg);
                    }
                    self.buf.push(')');
                }
            }
            TypedPattern::Lit { value, .. } => self.fmt_lit(value),
            TypedPattern::Tuple { elements, .. } => {
                self.buf.push('(');
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_typed_pattern(e);
                }
                self.buf.push(')');
            }
            TypedPattern::StructPat {
                name,
                fields,
                rest,
                ..
            } => {
                self.buf.push_str(name);
                self.buf.push_str(" { ");
                for (i, (fname, fpat)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    if matches!(fpat, TypedPattern::Var { name: vname, span: (0, 0), .. } if vname == fname)
                    {
                        self.buf.push_str(fname);
                    } else {
                        self.buf.push_str(fname);
                        self.buf.push_str(": ");
                        self.fmt_typed_pattern(fpat);
                    }
                }
                if *rest {
                    if !fields.is_empty() {
                        self.buf.push_str(", ");
                    }
                    self.buf.push_str("..");
                }
                self.buf.push_str(" }");
            }
        }
    }
}

fn is_punnable_typed(field_name: &str, val: &TypedExpr) -> bool {
    matches!(&val.kind, TypedExprKind::Var(name) if name == field_name && val.span == (0, 0))
}

fn binop_precedence(op: &krypton_parser::ast::BinOp) -> u8 {
    use krypton_parser::ast::BinOp;
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => 3,
        BinOp::Add | BinOp::Sub => 4,
        BinOp::Mul | BinOp::Div => 5,
    }
}

fn is_left_assoc(op: &krypton_parser::ast::BinOp) -> bool {
    use krypton_parser::ast::BinOp;
    matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Or | BinOp::And
    )
}

fn is_non_assoc(op: &krypton_parser::ast::BinOp) -> bool {
    use krypton_parser::ast::BinOp;
    matches!(
        op,
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    )
}

fn binop_str(op: &krypton_parser::ast::BinOp) -> &'static str {
    use krypton_parser::ast::BinOp;
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
        BinOp::And => "&&",
        BinOp::Or => "||",
    }
}

/// Format a parser TypeExpr to source syntax.
fn fmt_type_expr_source(ty: &TypeExpr) -> String {
    match ty {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => name.clone(),
        TypeExpr::Qualified { module, name, .. } => format!("{module}.{name}"),
        TypeExpr::App { name, args, .. } => {
            let as_: Vec<String> = args.iter().map(|a| fmt_type_expr_source(a)).collect();
            format!("{}[{}]", name, as_.join(", "))
        }
        TypeExpr::Fn { params, ret, .. } => {
            let ps: Vec<String> = params.iter().map(|p| fmt_type_expr_source(p)).collect();
            format!("({}) -> {}", ps.join(", "), fmt_type_expr_source(ret))
        }
        TypeExpr::Own { inner, .. } => format!("~{}", fmt_type_expr_source(inner)),
        TypeExpr::Tuple { elements, .. } => {
            let es: Vec<String> = elements.iter().map(|e| fmt_type_expr_source(e)).collect();
            format!("({})", es.join(", "))
        }
        TypeExpr::Wildcard { .. } => "_".to_string(),
    }
}

/// Extract the base type name from a TypeExpr (for mangled name lookup).
fn type_expr_base_name(ty: &TypeExpr) -> &str {
    match ty {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } | TypeExpr::App { name, .. } | TypeExpr::Qualified { name, .. } => name,
        TypeExpr::Own { inner, .. } => type_expr_base_name(inner),
        _ => "",
    }
}

/// Render fully-expanded inspect output from the TypedAST.
pub fn render_inspect(
    module: &Module,
    auto_close: &AutoCloseInfo,
    functions: &[TypedFnDecl],
    fn_types: &[FnTypeEntry],
    instance_defs: &[InstanceDefInfo],
) -> String {
    let mut output = String::new();

    for (i, decl) in module.decls.iter().enumerate() {
        if i > 0 {
            output.push('\n');
        }
        match decl {
            Decl::DefFn(f) => {
                // Find the matching TypedFnDecl and FnTypeEntry
                if let Some(typed_fn) = functions.iter().find(|tf| tf.name == f.name) {
                    if let Some(entry) = fn_types.iter().find(|e| e.name == f.name) {
                        let (display_ty, var_names) = if entry.scheme.vars.is_empty() {
                            (entry.scheme.ty.clone(), None)
                        } else {
                            let (ty, names) = entry.scheme.display_var_names();
                            (ty, Some(names))
                        };
                        let mut formatter = TypedFormatter {
                            indent_level: 0,
                            buf: String::new(),
                            auto_close,
                            var_names,
                        };
                        formatter.fmt_fn_decl(typed_fn, &display_ty);
                        output.push_str(&formatter.buf);
                    } else {
                        output.push_str(&krypton_parser::pretty::pretty_print_decl(decl));
                    }
                } else {
                    output.push_str(&krypton_parser::pretty::pretty_print_decl(decl));
                }
            }
            Decl::DefImpl {
                trait_name,
                target_type,
                type_constraints,
                methods,
                ..
            } => {
                let target_name = type_expr_base_name(target_type);
                // Print impl header using pretty printer's type formatting
                output.push_str("impl ");
                output.push_str(trait_name);
                output.push('[');
                output.push_str(&fmt_type_expr_source(target_type));
                output.push(']');
                if !type_constraints.is_empty() {
                    output.push_str(" where ");
                    for (i, c) in type_constraints.iter().enumerate() {
                        if i > 0 {
                            output.push_str(", ");
                        }
                        output.push_str(&c.type_var);
                        output.push_str(": ");
                        output.push_str(&c.trait_name);
                    }
                }
                output.push_str(" {\n");
                // Find the matching InstanceDefInfo
                let inst = instance_defs.iter().find(|i| {
                    i.trait_name == *trait_name && i.target_type_name == target_name
                });
                for m in methods {
                    if let Some(inst) = inst {
                        if let Some(im) = inst.methods.iter().find(|im| im.name == m.name) {
                            let mut formatter = TypedFormatter {
                                indent_level: 1,
                                buf: String::new(),
                                auto_close,
                                var_names: None,
                            };
                            formatter.indent();
                            let typed_fn = TypedFnDecl {
                                name: m.name.clone(),
                                visibility: krypton_parser::ast::Visibility::Private,
                                params: im.params.clone(),
                                body: im.body.clone(),
                                close_self_type: None,
                            };
                            formatter.fmt_impl_method(&m.name, &typed_fn, &im.scheme.ty);
                            output.push_str(&formatter.buf);
                            output.push('\n');
                            continue;
                        }
                    }
                    output.push_str("    ");
                    output.push_str(&krypton_parser::pretty::pretty_print_decl(
                        &Decl::DefFn(m.clone()),
                    ));
                    output.push('\n');
                }
                output.push('}');
            }
            _ => {
                output.push_str(&krypton_parser::pretty::pretty_print_decl(decl));
            }
        }
        output.push('\n');
    }

    // Remove trailing newline for consistency
    if output.ends_with('\n') {
        output.pop();
    }

    output
}
