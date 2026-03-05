use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Expr, FnDecl};

/// Collect references to top-level names in an expression.
fn collect_refs(expr: &Expr, names: &HashSet<String>, refs: &mut HashSet<String>) {
    match expr {
        Expr::Var { name, .. } => {
            if names.contains(name) {
                refs.insert(name.clone());
            }
        }
        Expr::Lit { .. } | Expr::Self_ { .. } => {}
        Expr::App { func, args, .. } => {
            collect_refs(func, names, refs);
            for a in args {
                collect_refs(a, names, refs);
            }
        }
        Expr::If {
            cond,
            then_,
            else_,
            ..
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
        Expr::Receive { arms, timeout, .. } => {
            for arm in arms {
                collect_refs(&arm.body, names, refs);
            }
            if let Some(t) = timeout {
                collect_refs(&t.duration, names, refs);
                collect_refs(&t.body, names, refs);
            }
        }
        Expr::Send {
            target, message, ..
        } => {
            collect_refs(target, names, refs);
            collect_refs(message, names, refs);
        }
        Expr::Spawn { func, args, .. } => {
            collect_refs(func, names, refs);
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
    }
}

/// Build an adjacency list for top-level function declarations.
/// `adj[i]` contains the indices of functions that function `i` references.
pub fn build_dependency_graph(fn_decls: &[&FnDecl]) -> Vec<Vec<usize>> {
    let names: HashSet<String> = fn_decls.iter().map(|d| d.name.clone()).collect();
    let name_to_idx: HashMap<&str, usize> = fn_decls
        .iter()
        .enumerate()
        .map(|(i, d)| (d.name.as_str(), i))
        .collect();

    fn_decls
        .iter()
        .map(|decl| {
            let mut refs = HashSet::new();
            collect_refs(&decl.body, &names, &mut refs);
            let mut edges: Vec<usize> = refs
                .iter()
                .filter_map(|r| name_to_idx.get(r.as_str()).copied())
                .collect();
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
            vec![1],    // a -> b
            vec![0],    // b -> a
            vec![0],    // c -> a
        ];
        let sccs = tarjan_scc(&adj);
        // Should be in dependency order: {a,b} first, then {c}
        assert_eq!(sccs.len(), 2);
        assert_eq!(sccs[0], vec![0, 1]); // {a, b}
        assert_eq!(sccs[1], vec![2]);    // {c}
    }
}
