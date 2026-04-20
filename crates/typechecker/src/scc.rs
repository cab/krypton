use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Expr, FnDecl};

/// Collect references to top-level names in an expression.
fn collect_refs(expr: &Expr, names: &FxHashSet<String>, refs: &mut FxHashSet<String>) {
    match expr {
        Expr::Var { name, .. } => {
            if names.contains(name) {
                refs.insert(name.clone());
            }
        }
        Expr::Lit { .. } => {}
        Expr::App { func, args, .. } => {
            collect_refs(func, names, refs);
            for a in args {
                collect_refs(a, names, refs);
            }
        }
        Expr::TypeApp { expr, .. } => collect_refs(expr, names, refs),
        Expr::If {
            cond, then_, else_, ..
        } => {
            collect_refs(cond, names, refs);
            collect_refs(then_, names, refs);
            collect_refs(else_, names, refs);
        }
        Expr::Let { value, body, .. } => {
            collect_refs(value, names, refs);
            if let Some(body) = body {
                collect_refs(body, names, refs);
            }
        }
        Expr::LetPattern { value, body, .. } => {
            collect_refs(value, names, refs);
            if let Some(body) = body {
                collect_refs(body, names, refs);
            }
        }
        Expr::Do { exprs, .. } => {
            for e in exprs {
                collect_refs(e, names, refs);
            }
        }
        Expr::Lambda { body, .. } => {
            collect_refs(body, names, refs);
        }
        Expr::BinaryOp { lhs, rhs, .. } => {
            collect_refs(lhs, names, refs);
            collect_refs(rhs, names, refs);
        }
        Expr::UnaryOp { operand, .. } => {
            collect_refs(operand, names, refs);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            collect_refs(scrutinee, names, refs);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_refs(guard, names, refs);
                }
                collect_refs(&arm.body, names, refs);
            }
        }
        Expr::FieldAccess { expr, .. } => {
            collect_refs(expr, names, refs);
        }
        Expr::Recur { args, .. } => {
            for a in args {
                collect_refs(a, names, refs);
            }
        }
        Expr::QuestionMark { expr, .. } => {
            collect_refs(expr, names, refs);
        }
        Expr::List { elements, .. } | Expr::Tuple { elements, .. } => {
            for e in elements {
                collect_refs(e, names, refs);
            }
        }
        Expr::StructLit { fields, .. } => {
            for (_, e) in fields {
                collect_refs(e, names, refs);
            }
        }
        Expr::StructUpdate { base, fields, .. } => {
            collect_refs(base, names, refs);
            for (_, e) in fields {
                collect_refs(e, names, refs);
            }
        }
        Expr::IfLet {
            scrutinee,
            guard,
            then_,
            else_,
            ..
        } => {
            collect_refs(scrutinee, names, refs);
            if let Some(guard) = guard {
                collect_refs(guard, names, refs);
            }
            collect_refs(then_, names, refs);
            if let Some(else_) = else_ {
                collect_refs(else_, names, refs);
            }
        }
    }
}

/// Build an adjacency list for top-level function declarations.
/// `adj[i]` contains the indices of functions that function `i` references.
pub fn build_dependency_graph(fn_decls: &[&FnDecl]) -> Vec<Vec<usize>> {
    let names: FxHashSet<String> = fn_decls.iter().map(|d| d.name.clone()).collect();
    let mut name_to_indices: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
    for (i, d) in fn_decls.iter().enumerate() {
        name_to_indices.entry(d.name.as_str()).or_default().push(i);
    }

    fn_decls
        .iter()
        .enumerate()
        .map(|(i, decl)| {
            let mut refs = FxHashSet::default();
            collect_refs(&decl.body, &names, &mut refs);
            let mut edges: Vec<usize> = refs
                .iter()
                .flat_map(|r| name_to_indices.get(r.as_str()).into_iter().flatten().copied())
                .collect();
            // Add synthetic edges between same-named overloads so they
            // land in the same SCC and get registered as an overload set.
            if let Some(siblings) = name_to_indices.get(decl.name.as_str()) {
                if siblings.len() > 1 {
                    edges.extend(siblings.iter().copied().filter(|&j| j != i));
                }
            }
            edges.sort();
            edges.dedup();
            edges
        })
        .collect()
}

/// Tarjan's SCC algorithm. Returns SCCs in reverse topological order
/// (dependencies come first).
pub fn tarjan_scc(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct State<'a> {
        adj: &'a [Vec<usize>],
        index_counter: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        index: Vec<usize>,
        lowlink: Vec<usize>,
        result: Vec<Vec<usize>>,
    }

    impl State<'_> {
        fn strongconnect(&mut self, v: usize) {
            self.index[v] = self.index_counter;
            self.lowlink[v] = self.index_counter;
            self.index_counter += 1;
            self.stack.push(v);
            self.on_stack[v] = true;

            for i in 0..self.adj[v].len() {
                let w = self.adj[v][i];
                if self.index[w] == usize::MAX {
                    self.strongconnect(w);
                    self.lowlink[v] = self.lowlink[v].min(self.lowlink[w]);
                } else if self.on_stack[w] {
                    self.lowlink[v] = self.lowlink[v].min(self.index[w]);
                }
            }

            if self.lowlink[v] == self.index[v] {
                let mut component = Vec::new();
                loop {
                    let w = self.stack.pop().unwrap();
                    self.on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                component.sort();
                self.result.push(component);
            }
        }
    }

    let n = adj.len();
    let mut state = State {
        adj,
        index_counter: 0,
        stack: Vec::new(),
        on_stack: vec![false; n],
        index: vec![usize::MAX; n],
        lowlink: vec![0; n],
        result: Vec::new(),
    };

    for v in 0..n {
        if state.index[v] == usize::MAX {
            state.strongconnect(v);
        }
    }

    state.result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scc_unit_test() {
        // Graph: a(0) -> b(1), b(1) -> a(0), c(2) -> a(0)
        // SCCs: {a, b} (mutual recursion) and {c} (depends on a)
        let adj = vec![
            vec![1], // a -> b
            vec![0], // b -> a
            vec![0], // c -> a
        ];
        let sccs = tarjan_scc(&adj);
        // Should be in dependency order: {a,b} first, then {c}
        assert_eq!(sccs.len(), 2);
        assert_eq!(sccs[0], vec![0, 1]); // {a, b}
        assert_eq!(sccs[1], vec![2]); // {c}
    }
}
