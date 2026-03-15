use krypton_typechecker::typed_ast::{
    AutoCloseInfo, FnTypeEntry, TypedExpr, TypedExprKind, TypedFnDecl, TypedPattern,
};

/// Annotation to attach below a source line.
enum Annotation {
    /// Function type: `# : fn(Int) -> String`
    FnType(String),
    /// Let binding type: `# name : own Handle`
    LetType(String, String),
    /// Auto-close insertion: `# <- close(var) inserted [reason]`
    Close(String, String),
    /// Move/consumption: `# ^ move: var`
    Move(String),
}

/// Byte offset → line number (0-based).
fn offset_to_line(line_starts: &[usize], offset: usize) -> usize {
    match line_starts.binary_search(&offset) {
        Ok(i) => i,
        Err(i) => i.saturating_sub(1),
    }
}

/// Build a mapping from byte offset to line number.
fn build_line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, ch) in source.char_indices() {
        if ch == '\n' {
            starts.push(i + 1);
        }
    }
    starts
}

/// Collect let-binding type annotations from a typed expression tree.
fn collect_let_types(expr: &TypedExpr, line_starts: &[usize], annotations: &mut Vec<(usize, Annotation)>) {
    let mut work: Vec<&TypedExpr> = vec![expr];
    while let Some(expr) = work.pop() {
        match &expr.kind {
            TypedExprKind::Let { name, value, body } => {
                let line = offset_to_line(line_starts, expr.span.0);
                let ty_str = format!("{}", value.ty);
                annotations.push((line, Annotation::LetType(name.clone(), ty_str)));
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::LetPattern { pattern, value, body } => {
                collect_pattern_types(pattern, line_starts, annotations, expr.span.0);
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::App { func, args } => {
                work.push(func);
                work.extend(args.iter());
            }
            TypedExprKind::TypeApp { expr } => work.push(expr),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Do(exprs) => work.extend(exprs.iter()),
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms {
                    work.push(&arm.body);
                }
            }
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::Recur(args) | TypedExprKind::Tuple(args) | TypedExprKind::VecLit(args) => {
                work.extend(args.iter());
            }
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::StructUpdate { base, fields } => {
                work.push(base);
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::Var(_) | TypedExprKind::Lit(_) => {}
        }
    }
}

/// Collect type annotations from destructured pattern bindings.
fn collect_pattern_types(
    pattern: &TypedPattern,
    line_starts: &[usize],
    annotations: &mut Vec<(usize, Annotation)>,
    span_start: usize,
) {
    match pattern {
        TypedPattern::Var { name, ty, .. } => {
            let line = offset_to_line(line_starts, span_start);
            annotations.push((line, Annotation::LetType(name.clone(), format!("{}", ty))));
        }
        TypedPattern::Constructor { args, .. } => {
            for arg in args {
                collect_pattern_types(arg, line_starts, annotations, span_start);
            }
        }
        TypedPattern::Tuple { elements, .. } => {
            for elem in elements {
                collect_pattern_types(elem, line_starts, annotations, span_start);
            }
        }
        TypedPattern::StructPat { fields, .. } => {
            for (_, field_pat) in fields {
                collect_pattern_types(field_pat, line_starts, annotations, span_start);
            }
        }
        TypedPattern::Wildcard { .. } | TypedPattern::Lit { .. } => {}
    }
}

/// Find the line of the last token in a function body.
fn fn_body_last_line(expr: &TypedExpr, line_starts: &[usize]) -> usize {
    offset_to_line(line_starts, expr.span.1.saturating_sub(1))
}

/// Render annotated source output for the inspect command.
pub fn render_inspect(
    source: &str,
    auto_close: &AutoCloseInfo,
    functions: &[TypedFnDecl],
    fn_types: &[FnTypeEntry],
) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let line_starts = build_line_starts(source);

    // Collect all annotations keyed by line number.
    // Use Vec to allow multiple annotations per line, with ordering.
    let mut annotations: Vec<(usize, Annotation)> = Vec::new();

    // 1. Function type annotations — placed on the `fun` declaration line
    for decl in functions {
        let fn_line = offset_to_line(&line_starts, decl.body.span.0);
        // Find the actual `fun` line — walk backwards from body to find the fun keyword
        // Use the fn_types entry to get the type scheme
        if let Some(entry) = fn_types.iter().find(|e| e.name == decl.name) {
            // Find the fun keyword line by looking at the source before the body
            let fun_line = find_fun_line(&lines, &decl.name, fn_line);
            annotations.push((fun_line, Annotation::FnType(format!("{}", entry.scheme))));
        }

        // 2. Let binding types from the function body
        collect_let_types(&decl.body, &line_starts, &mut annotations);
    }

    // 3. Auto-close annotations

    // fn_exits: close at end of function
    for (fn_name, bindings) in &auto_close.fn_exits {
        if let Some(decl) = functions.iter().find(|d| &d.name == fn_name) {
            let last_line = fn_body_last_line(&decl.body, &line_starts);
            for binding in bindings {
                annotations.push((
                    last_line,
                    Annotation::Close(binding.name.clone(), "scope exit".to_string()),
                ));
            }
        }
    }

    // shadow_closes: close at shadow point (the let that shadows)
    for (span, binding) in &auto_close.shadow_closes {
        let line = offset_to_line(&line_starts, span.0);
        annotations.push((
            line,
            Annotation::Close(binding.name.clone(), "shadow".to_string()),
        ));
    }

    // early_returns: close before ? early return
    for (span, bindings) in &auto_close.early_returns {
        let line = offset_to_line(&line_starts, span.0);
        for binding in bindings {
            annotations.push((
                line,
                Annotation::Close(binding.name.clone(), "early return".to_string()),
            ));
        }
    }

    // recur_closes: close before recur
    for (span, bindings) in &auto_close.recur_closes {
        let line = offset_to_line(&line_starts, span.0);
        for binding in bindings {
            annotations.push((
                line,
                Annotation::Close(binding.name.clone(), "recur".to_string()),
            ));
        }
    }

    // consumptions: move annotations
    for (span, bindings) in &auto_close.consumptions {
        let line = offset_to_line(&line_starts, span.0);
        for binding in bindings {
            annotations.push((line, Annotation::Move(binding.name.clone())));
        }
    }

    // Sort annotations by line number for stable output
    annotations.sort_by_key(|(line, _)| *line);

    // Render output
    let mut output = String::new();
    let width = lines.len().to_string().len().max(4);

    for (i, line_text) in lines.iter().enumerate() {
        output.push_str(&format!("{:>width$} | {}\n", i + 1, line_text, width = width));

        // Append annotations for this line
        let indent = " ".repeat(width + 3);
        for (line_num, ann) in &annotations {
            if *line_num != i {
                continue;
            }
            match ann {
                Annotation::FnType(ty) => {
                    output.push_str(&format!("{}# : {}\n", indent, ty));
                }
                Annotation::LetType(name, ty) => {
                    output.push_str(&format!("{}# {} : {}\n", indent, name, ty));
                }
                Annotation::Close(var, reason) => {
                    output.push_str(&format!(
                        "{}\u{2190} close({}) inserted [{}]\n",
                        indent, var, reason
                    ));
                }
                Annotation::Move(var) => {
                    output.push_str(&format!(
                        "{}\u{2191} move: {}\n",
                        indent, var
                    ));
                }
            }
        }
    }

    output
}

/// Find the line containing `fun <name>` at or before `max_line`.
fn find_fun_line(lines: &[&str], name: &str, max_line: usize) -> usize {
    // For trait instance methods like `Resource$Handle$close`, look for the original method name
    let search_name = if let Some(pos) = name.rfind('$') {
        &name[pos + 1..]
    } else {
        name
    };
    let pattern = format!("fun {}", search_name);
    for i in (0..=max_line.min(lines.len().saturating_sub(1))).rev() {
        if lines[i].contains(&pattern) {
            return i;
        }
    }
    max_line
}
