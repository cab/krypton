use crate::ast::*;

pub struct PrettyConfig {
    pub indent_width: usize,
}

impl Default for PrettyConfig {
    fn default() -> Self {
        Self { indent_width: 4 }
    }
}

pub fn pretty_print(module: &Module) -> String {
    pretty_print_with(module, &PrettyConfig::default())
}

pub fn pretty_print_with(module: &Module, config: &PrettyConfig) -> String {
    let mut f = Formatter {
        config,
        indent_level: 0,
        buf: String::new(),
    };
    for (i, decl) in module.decls.iter().enumerate() {
        if i > 0 {
            f.buf.push('\n');
        }
        f.fmt_decl(decl);
        f.buf.push('\n');
    }
    // Remove trailing newline for consistency
    if f.buf.ends_with('\n') {
        f.buf.pop();
    }
    f.buf
}

struct Formatter<'a> {
    config: &'a PrettyConfig,
    indent_level: usize,
    buf: String,
}

impl<'a> Formatter<'a> {
    fn indent(&mut self) {
        for _ in 0..self.indent_level * self.config.indent_width {
            self.buf.push(' ');
        }
    }

    fn fmt_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::DefFn(f) => self.fmt_fn_decl(f),
            Decl::DefType(t) => self.fmt_type_decl(t),
            Decl::DefTrait {
                visibility,
                name,
                type_param,
                superclasses,
                methods,
                ..
            } => {
                self.fmt_visibility(visibility);
                self.fmt_trait(name, type_param, superclasses, methods);
            }
            Decl::DefImpl {
                trait_name,
                target_type,
                type_constraints,
                methods,
                ..
            } => self.fmt_impl(trait_name, target_type, type_constraints, methods),
            Decl::Import { is_pub, path, names, .. } => self.fmt_import(*is_pub, path, names),
            Decl::ExternJava {
                class_name,
                methods,
                ..
            } => self.fmt_extern(class_name, methods),
        }
    }

    fn fmt_visibility(&mut self, vis: &Visibility) {
        match vis {
            Visibility::Private => {}
            Visibility::Pub => self.buf.push_str("pub "),
            Visibility::PubOpen => self.buf.push_str("pub open "),
        }
    }

    fn fmt_fn_decl(&mut self, f: &FnDecl) {
        self.fmt_visibility(&f.visibility);
        self.buf.push_str("fun ");
        self.buf.push_str(&f.name);
        self.fmt_type_params(&f.type_params);
        self.buf.push('(');
        for (i, p) in f.params.iter().enumerate() {
            if i > 0 {
                self.buf.push_str(", ");
            }
            self.fmt_param(p);
        }
        self.buf.push(')');
        if let Some(ret) = &f.return_type {
            self.buf.push_str(" -> ");
            self.fmt_type_expr(ret);
        }
        if !f.constraints.is_empty() {
            self.buf.push_str(" where ");
            // Group constraints by type_var, preserving order
            let mut groups: Vec<(String, Vec<String>)> = Vec::new();
            for c in &f.constraints {
                if let Some(group) = groups.iter_mut().find(|(tv, _)| tv == &c.type_var) {
                    group.1.push(c.trait_name.clone());
                } else {
                    groups.push((c.type_var.clone(), vec![c.trait_name.clone()]));
                }
            }
            for (i, (type_var, bounds)) in groups.iter().enumerate() {
                if i > 0 {
                    self.buf.push_str(", ");
                }
                self.buf.push_str(type_var);
                self.buf.push_str(": ");
                self.buf.push_str(&bounds.join(" + "));
            }
        }
        // Determine body style: block body (Do) vs expression body
        match &*f.body {
            Expr::Do { exprs, .. } => {
                self.buf.push_str(" {");
                self.fmt_block_body(exprs);
                self.buf.push('}');
            }
            body => {
                self.buf.push_str(" = ");
                self.fmt_expr(body);
            }
        }
    }

    fn fmt_param(&mut self, p: &Param) {
        self.buf.push_str(&p.name);
        if let Some(ty) = &p.ty {
            self.buf.push_str(": ");
            self.fmt_type_expr(ty);
        }
    }

    fn fmt_type_expr(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => {
                self.buf.push_str(name);
            }
            TypeExpr::App { name, args, .. } => {
                self.buf.push_str(name);
                self.buf.push('[');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_type_expr(arg);
                }
                self.buf.push(']');
            }
            TypeExpr::Fn { params, ret, .. } => {
                self.buf.push('(');
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_type_expr(p);
                }
                self.buf.push_str(") -> ");
                self.fmt_type_expr(ret);
            }
            TypeExpr::Own { inner, .. } => {
                self.buf.push('~');
                self.fmt_type_expr(inner);
            }
            TypeExpr::Tuple { elements, .. } => {
                self.buf.push('(');
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_type_expr(e);
                }
                self.buf.push(')');
            }
        }
    }

    fn fmt_type_params(&mut self, params: &[TypeParam]) {
        if params.is_empty() {
            return;
        }
        self.buf.push('[');
        for (i, param) in params.iter().enumerate() {
            if i > 0 {
                self.buf.push_str(", ");
            }
            self.buf.push_str(&param.name);
            if param.arity > 0 {
                self.buf.push('[');
                for hole_idx in 0..param.arity {
                    if hole_idx > 0 {
                        self.buf.push_str(", ");
                    }
                    self.buf.push('_');
                }
                self.buf.push(']');
            }
        }
        self.buf.push(']');
    }

    fn fmt_type_decl(&mut self, t: &TypeDecl) {
        self.fmt_visibility(&t.visibility);
        self.buf.push_str("type ");
        self.buf.push_str(&t.name);
        if !t.type_params.is_empty() {
            self.buf.push('[');
            self.buf.push_str(&t.type_params.join(", "));
            self.buf.push(']');
        }
        self.buf.push_str(" = ");
        match &t.kind {
            TypeDeclKind::Record { fields } => {
                self.buf.push_str("{ ");
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.buf.push_str(name);
                    self.buf.push_str(": ");
                    self.fmt_type_expr(ty);
                }
                self.buf.push_str(" }");
            }
            TypeDeclKind::Sum { variants } => {
                for (i, v) in variants.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(" | ");
                    }
                    self.buf.push_str(&v.name);
                    if !v.fields.is_empty() {
                        self.buf.push('(');
                        for (j, f) in v.fields.iter().enumerate() {
                            if j > 0 {
                                self.buf.push_str(", ");
                            }
                            self.fmt_type_expr(f);
                        }
                        self.buf.push(')');
                    }
                }
            }
        }
        if !t.deriving.is_empty() {
            self.buf.push_str(" deriving (");
            self.buf.push_str(&t.deriving.join(", "));
            self.buf.push(')');
        }
    }

    fn fmt_trait(
        &mut self,
        name: &str,
        type_param: &TypeParam,
        superclasses: &[String],
        methods: &[FnDecl],
    ) {
        self.buf.push_str("trait ");
        self.buf.push_str(name);
        self.fmt_type_params(std::slice::from_ref(type_param));
        if !superclasses.is_empty() {
            self.buf.push_str(" where ");
            self.buf.push_str(&type_param.name);
            self.buf.push_str(": ");
            self.buf.push_str(&superclasses.join(", "));
        }
        self.buf.push_str(" {");
        self.indent_level += 1;
        for m in methods {
            self.buf.push('\n');
            self.indent();
            self.fmt_trait_method(m);
        }
        self.indent_level -= 1;
        self.buf.push('\n');
        self.buf.push('}');
    }

    fn fmt_trait_method(&mut self, m: &FnDecl) {
        self.buf.push_str("fun ");
        self.buf.push_str(&m.name);
        self.fmt_type_params(&m.type_params);
        self.buf.push('(');
        for (i, p) in m.params.iter().enumerate() {
            if i > 0 {
                self.buf.push_str(", ");
            }
            // Trait methods always have typed params
            self.fmt_param(p);
        }
        self.buf.push(')');
        if let Some(ret) = &m.return_type {
            self.buf.push_str(" -> ");
            self.fmt_type_expr(ret);
        }
        let is_unit_body = matches!(&*m.body, Expr::Lit { value: Lit::Unit, .. });
        if !is_unit_body {
            match &*m.body {
                Expr::Do { exprs, .. } => {
                    self.buf.push_str(" {");
                    self.fmt_block_body(exprs);
                    self.buf.push('}');
                }
                body => {
                    self.buf.push_str(" = ");
                    self.fmt_expr(body);
                }
            }
        }
    }

    fn fmt_impl(
        &mut self,
        trait_name: &str,
        target_type: &TypeExpr,
        constraints: &[TypeConstraint],
        methods: &[FnDecl],
    ) {
        self.buf.push_str("impl ");
        self.buf.push_str(trait_name);
        self.buf.push('[');
        self.fmt_type_expr(target_type);
        self.buf.push(']');
        if !constraints.is_empty() {
            self.buf.push_str(" where ");
            for (i, c) in constraints.iter().enumerate() {
                if i > 0 {
                    self.buf.push_str(", ");
                }
                self.buf.push_str(&c.type_var);
                self.buf.push_str(": ");
                self.buf.push_str(&c.trait_name);
            }
        }
        self.buf.push_str(" {");
        self.indent_level += 1;
        for m in methods {
            self.buf.push('\n');
            self.indent();
            self.fmt_impl_method(m);
        }
        self.indent_level -= 1;
        self.buf.push('\n');
        self.buf.push('}');
    }

    fn fmt_impl_method(&mut self, m: &FnDecl) {
        self.buf.push_str("fun ");
        self.buf.push_str(&m.name);
        self.fmt_type_params(&m.type_params);
        self.buf.push('(');
        for (i, p) in m.params.iter().enumerate() {
            if i > 0 {
                self.buf.push_str(", ");
            }
            self.fmt_param(p);
        }
        self.buf.push(')');
        match &*m.body {
            Expr::Do { exprs, .. } => {
                self.buf.push_str(" {");
                self.fmt_block_body(exprs);
                self.buf.push('}');
            }
            body => {
                self.buf.push_str(" = ");
                self.fmt_expr(body);
            }
        }
    }

    fn fmt_import(&mut self, is_pub: bool, path: &str, names: &[ImportName]) {
        if is_pub {
            self.buf.push_str("pub ");
        }
        self.buf.push_str("import ");
        self.buf.push_str(path);
        if !names.is_empty() {
            self.buf.push_str(".{");
            for (i, n) in names.iter().enumerate() {
                if i > 0 {
                    self.buf.push_str(", ");
                }
                self.buf.push_str(&n.name);
                if let Some(alias) = &n.alias {
                    self.buf.push_str(" as ");
                    self.buf.push_str(alias);
                }
            }
            self.buf.push('}');
        }
    }

    fn fmt_extern(&mut self, class_name: &str, methods: &[ExternMethod]) {
        self.buf.push_str("extern \"");
        self.buf.push_str(class_name);
        self.buf.push_str("\" {");
        self.indent_level += 1;
        for m in methods {
            self.buf.push('\n');
            self.indent();
            self.buf.push_str("fun ");
            self.buf.push_str(&m.name);
            self.buf.push('(');
            for (i, ty) in m.param_types.iter().enumerate() {
                if i > 0 {
                    self.buf.push_str(", ");
                }
                self.fmt_type_expr(ty);
            }
            self.buf.push_str(") -> ");
            self.fmt_type_expr(&m.return_type);
        }
        self.indent_level -= 1;
        self.buf.push('\n');
        self.buf.push('}');
    }

    fn fmt_block_body(&mut self, exprs: &[Expr]) {
        self.indent_level += 1;
        for (i, expr) in exprs.iter().enumerate() {
            self.buf.push('\n');
            self.indent();
            self.fmt_expr(expr);
            // Add semicolons between statements (not after last)
            if i < exprs.len() - 1 {
                self.buf.push(';');
            }
        }
        self.indent_level -= 1;
        self.buf.push('\n');
        self.indent();
    }

    fn fmt_expr(&mut self, expr: &Expr) {
        self.fmt_expr_prec(expr, 0);
    }

    fn fmt_expr_prec(&mut self, expr: &Expr, parent_prec: u8) {
        match expr {
            Expr::Lit { value, .. } => self.fmt_lit(value),
            Expr::Var { name, .. } => self.buf.push_str(name),
            Expr::BinaryOp { op, lhs, rhs, .. } => {
                let prec = binop_precedence(op);
                let need_parens = prec < parent_prec;
                if need_parens {
                    self.buf.push('(');
                }
                // Left child: parens if child prec < this prec
                self.fmt_expr_prec(lhs, prec);
                self.buf.push(' ');
                self.buf.push_str(binop_str(op));
                self.buf.push(' ');
                // Right child of left-assoc: parens if child prec <= this prec
                // Comparison ops are non-assoc, same rule applies
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
            Expr::UnaryOp { op, operand, .. } => {
                let prec = 6;
                let need_parens = prec < parent_prec;
                if need_parens {
                    self.buf.push('(');
                }
                match op {
                    UnaryOp::Neg => self.buf.push('-'),
                    UnaryOp::Not => self.buf.push('!'),
                }
                self.fmt_expr_prec(operand, prec);
                if need_parens {
                    self.buf.push(')');
                }
            }
            Expr::App { func, args, .. } => {
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
            Expr::TypeApp { expr, type_args, .. } => {
                self.fmt_expr_prec(expr, 7);
                self.buf.push('[');
                for (i, arg) in type_args.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_type_expr(arg);
                }
                self.buf.push(']');
            }
            Expr::If {
                cond,
                then_,
                else_,
                ..
            } => {
                self.buf.push_str("if ");
                self.fmt_expr(cond);
                self.buf.push_str(" { ");
                self.fmt_expr(then_);
                self.buf.push_str(" }");
                // Omit else if Unit
                if !matches!(&**else_, Expr::Lit { value: Lit::Unit, .. }) {
                    self.buf.push_str(" else { ");
                    self.fmt_expr(else_);
                    self.buf.push_str(" }");
                }
            }
            Expr::Let {
                name, ty, value, body, ..
            } => {
                match body {
                    Some(body_expr) => {
                        // let with body → wrap in block: { let x = val; body }
                        self.buf.push_str("{ let ");
                        self.buf.push_str(name);
                        if let Some(ty) = ty {
                            self.buf.push_str(": ");
                            self.fmt_type_expr(ty);
                        }
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                        self.buf.push_str("; ");
                        self.fmt_expr(body_expr);
                        self.buf.push_str(" }");
                    }
                    None => {
                        self.buf.push_str("let ");
                        self.buf.push_str(name);
                        if let Some(ty) = ty {
                            self.buf.push_str(": ");
                            self.fmt_type_expr(ty);
                        }
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                    }
                }
            }
            Expr::LetPattern {
                pattern,
                ty,
                value,
                body,
                ..
            } => {
                match body {
                    Some(body_expr) => {
                        self.buf.push_str("{ let ");
                        self.fmt_pattern(pattern);
                        if let Some(ty) = ty {
                            self.buf.push_str(": ");
                            self.fmt_type_expr(ty);
                        }
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                        self.buf.push_str("; ");
                        self.fmt_expr(body_expr);
                        self.buf.push_str(" }");
                    }
                    None => {
                        self.buf.push_str("let ");
                        self.fmt_pattern(pattern);
                        if let Some(ty) = ty {
                            self.buf.push_str(": ");
                            self.fmt_type_expr(ty);
                        }
                        self.buf.push_str(" = ");
                        self.fmt_expr(value);
                    }
                }
            }
            Expr::Do { exprs, .. } => {
                self.buf.push('{');
                self.fmt_block_body(exprs);
                self.buf.push('}');
            }
            Expr::Match {
                scrutinee, arms, ..
            } => {
                self.buf.push_str("match ");
                self.fmt_expr(scrutinee);
                self.buf.push_str(" {");
                self.indent_level += 1;
                for arm in arms.iter() {
                    self.buf.push('\n');
                    self.indent();
                    self.fmt_pattern(&arm.pattern);
                    if let Some(guard) = &arm.guard {
                        self.buf.push_str(" if ");
                        self.fmt_expr(guard);
                    }
                    self.buf.push_str(" => ");
                    self.fmt_expr(&arm.body);
                    self.buf.push(',');
                }
                self.indent_level -= 1;
                self.buf.push('\n');
                self.indent();
                self.buf.push('}');
            }
            Expr::Lambda { params, body, .. } => {
                if params.is_empty() {
                    // Zero-arg lambda: () -> body
                    self.buf.push_str("() -> ");
                    self.fmt_expr(body);
                } else if params.len() == 1 && params[0].ty.is_none() {
                    // Single untyped param: x -> body
                    self.buf.push_str(&params[0].name);
                    self.buf.push_str(" -> ");
                    self.fmt_expr(body);
                } else {
                    // Multi or typed params: (x, y) -> body
                    self.buf.push('(');
                    for (i, p) in params.iter().enumerate() {
                        if i > 0 {
                            self.buf.push_str(", ");
                        }
                        self.fmt_param(p);
                    }
                    self.buf.push_str(") -> ");
                    self.fmt_expr(body);
                }
            }
            Expr::FieldAccess { expr, field, .. } => {
                self.fmt_expr_prec(expr, 7);
                self.buf.push('.');
                self.buf.push_str(field);
            }
            Expr::QuestionMark { expr, .. } => {
                self.fmt_expr_prec(expr, 7);
                self.buf.push('?');
            }
            Expr::Recur { args, .. } => {
                self.buf.push_str("recur(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_expr(arg);
                }
                self.buf.push(')');
            }
            Expr::List { elements, .. } => {
                self.buf.push('[');
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_expr(e);
                }
                self.buf.push(']');
            }
            Expr::Tuple { elements, .. } => {
                self.buf.push('(');
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_expr(e);
                }
                self.buf.push(')');
            }
            Expr::StructLit { name, fields, .. } => {
                self.buf.push_str(name);
                self.buf.push_str(" { ");
                for (i, (fname, fval)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    // Detect punning: field name == var name with span (0,0)
                    if is_punnable(fname, fval) {
                        self.buf.push_str(fname);
                    } else {
                        self.buf.push_str(fname);
                        self.buf.push_str(" = ");
                        self.fmt_expr(fval);
                    }
                }
                self.buf.push_str(" }");
            }
            Expr::StructUpdate { base, fields, .. } => {
                self.buf.push_str("{ ");
                self.fmt_expr(base);
                self.buf.push_str(" | ");
                for (i, (fname, fval)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    if is_punnable(fname, fval) {
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

    fn fmt_lit(&mut self, lit: &Lit) {
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

    fn fmt_pattern(&mut self, pat: &Pattern) {
        match pat {
            Pattern::Wildcard { .. } => self.buf.push('_'),
            Pattern::Var { name, .. } => self.buf.push_str(name),
            Pattern::Constructor { name, args, .. } => {
                self.buf.push_str(name);
                if !args.is_empty() {
                    self.buf.push('(');
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.buf.push_str(", ");
                        }
                        self.fmt_pattern(arg);
                    }
                    self.buf.push(')');
                }
            }
            Pattern::Lit { value, .. } => self.fmt_lit(value),
            Pattern::Tuple { elements, .. } => {
                self.buf.push('(');
                for (i, e) in elements.iter().enumerate() {
                    if i > 0 {
                        self.buf.push_str(", ");
                    }
                    self.fmt_pattern(e);
                }
                self.buf.push(')');
            }
            Pattern::StructPat {
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
                    // Detect struct pattern punning: field binds to variable of same name
                    if matches!(fpat, Pattern::Var { name: vname, span: (0, 0) } if vname == fname)
                    {
                        self.buf.push_str(fname);
                    } else {
                        self.buf.push_str(fname);
                        self.buf.push_str(": ");
                        self.fmt_pattern(fpat);
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

fn is_punnable(field_name: &str, val: &Expr) -> bool {
    matches!(val, Expr::Var { name, span: (0, 0) } if name == field_name)
}

fn binop_precedence(op: &BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => 3,
        BinOp::Add | BinOp::Sub => 4,
        BinOp::Mul | BinOp::Div => 5,
    }
}

fn is_left_assoc(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Or | BinOp::And
    )
}

fn is_non_assoc(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge
    )
}

fn binop_str(op: &BinOp) -> &'static str {
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
