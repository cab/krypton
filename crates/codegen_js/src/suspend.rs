use std::collections::{HashMap, HashSet};

use krypton_ir::*;

/// Qualified function reference: (module_index, FnId).
/// FnIds are per-module (each `lower_module` starts its counter at 0),
/// so we need the module index to disambiguate.
type QualFn = (usize, FnId);

/// Names of the actor primitives that actually block (need `await`).
const SUSPEND_SEEDS: &[&str] = &["raw_receive", "raw_receive_timeout", "raw_ask"];

/// Summary of which functions may suspend across all modules.
pub struct SuspendSummary {
    /// Per-module set of suspending FnIds.
    suspending: HashMap<usize, HashSet<FnId>>,
}

impl SuspendSummary {
    /// Create an empty summary (nothing suspends).
    pub fn empty() -> Self {
        SuspendSummary {
            suspending: HashMap::new(),
        }
    }

    /// Does the given function in the given module suspend?
    pub fn fn_suspends(&self, module_index: usize, id: FnId) -> bool {
        self.suspending
            .get(&module_index)
            .map_or(false, |s| s.contains(&id))
    }

    /// All suspending FnIds in a module (empty set if none).
    pub fn module_suspending_fns(&self, module_index: usize) -> HashSet<FnId> {
        self.suspending
            .get(&module_index)
            .cloned()
            .unwrap_or_default()
    }
}

/// Per-function edge info collected during the body walk.
struct FnEdges {
    call_targets: Vec<QualFn>,
    has_unresolved_closure_call: bool,
    has_unresolved_trait_call: bool,
}

/// Compute which functions may suspend across all modules.
///
/// Seeded by the three actor primitives (`raw_receive`, `raw_receive_timeout`,
/// `raw_ask`) from `core/actor`, then propagated transitively through the call
/// graph via fixed-point iteration.
pub fn analyze_suspend(modules: &[Module]) -> SuspendSummary {
    let mut suspending: HashSet<QualFn> = HashSet::new();

    // Phase 1 — Seed: find core/actor module and seed the suspending set.
    let actor_mod_idx = modules
        .iter()
        .position(|m| m.module_path.as_str() == "core/actor");

    if actor_mod_idx.is_none() {
        // No actor module → nothing suspends.
        return SuspendSummary {
            suspending: HashMap::new(),
        };
    }
    let actor_mod_idx = actor_mod_idx.unwrap();
    let actor_mod = &modules[actor_mod_idx];

    for ext in &actor_mod.extern_fns {
        if matches!(&ext.target, ExternTarget::Js { .. }) && SUSPEND_SEEDS.contains(&ext.name.as_str())
        {
            suspending.insert((actor_mod_idx, ext.id));
        }
    }

    // Phase 2 + 3 — Build call edges for every function in every module.
    let mut edges: HashMap<QualFn, FnEdges> = HashMap::new();

    // Build module path → index lookup for cross-module resolution.
    let mod_path_to_idx: HashMap<&str, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, m)| (m.module_path.as_str(), i))
        .collect();

    for (mod_idx, module) in modules.iter().enumerate() {
        // Phase 3 — Import edges: for each imported fn, add an edge to the
        // original function in the source module.
        for imp in &module.imported_fns {
            if let Some(identity) = module.fn_identities.get(&imp.id) {
                if let FnIdentity::Imported { canonical, .. } = identity {
                    let source_path = canonical.module.as_str();
                    if let Some(&source_mod_idx) = mod_path_to_idx.get(source_path) {
                        let source_mod = &modules[source_mod_idx];
                        let original_name = canonical.symbol.local_name();
                        // Find the FnId in the source module by name.
                        if let Some((&src_fn_id, _)) = source_mod
                            .fn_identities
                            .iter()
                            .find(|(_, fi)| fi.name() == original_name)
                        {
                            let entry = edges
                                .entry((mod_idx, imp.id))
                                .or_insert_with(|| FnEdges {
                                    call_targets: Vec::new(),
                                    has_unresolved_closure_call: false,
                                    has_unresolved_trait_call: false,
                                });
                            entry.call_targets.push((source_mod_idx, src_fn_id));
                        }
                    }
                }
            }
        }

        // Phase 2 — Walk each function body to collect call edges.
        for func in &module.functions {
            let mut fn_edges = FnEdges {
                call_targets: Vec::new(),
                has_unresolved_closure_call: false,
                has_unresolved_trait_call: false,
            };
            let mut closure_origins: HashMap<VarId, FnId> = HashMap::new();
            let mut var_types: HashMap<VarId, Type> = HashMap::new();

            // Record param types.
            for (var_id, ty) in &func.params {
                var_types.insert(*var_id, ty.clone());
            }

            walk_expr(
                &func.body,
                module,
                mod_idx,
                &mut closure_origins,
                &mut var_types,
                &mut fn_edges,
            );

            edges.insert((mod_idx, func.id), fn_edges);
        }
    }

    // Phase 5 — Fixed-point iteration.
    loop {
        let mut changed = false;
        for (qual_fn, fn_edges) in &edges {
            if suspending.contains(qual_fn) {
                continue;
            }
            if fn_edges.has_unresolved_closure_call || fn_edges.has_unresolved_trait_call {
                suspending.insert(*qual_fn);
                changed = true;
                continue;
            }
            if fn_edges
                .call_targets
                .iter()
                .any(|target| suspending.contains(target))
            {
                suspending.insert(*qual_fn);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Convert to per-module sets.
    let mut per_module: HashMap<usize, HashSet<FnId>> = HashMap::new();
    for (mod_idx, fn_id) in suspending {
        per_module.entry(mod_idx).or_default().insert(fn_id);
    }

    SuspendSummary {
        suspending: per_module,
    }
}

/// Recursively walk an expression, collecting call edges and tracking
/// closure origins and variable types.
fn walk_expr(
    expr: &Expr,
    module: &Module,
    mod_idx: usize,
    closure_origins: &mut HashMap<VarId, FnId>,
    var_types: &mut HashMap<VarId, Type>,
    fn_edges: &mut FnEdges,
) {
    match &expr.kind {
        ExprKind::Let {
            bind,
            ty,
            value,
            body,
        } => {
            var_types.insert(*bind, ty.clone());
            walk_simple_expr(
                &value.kind,
                *bind,
                module,
                mod_idx,
                closure_origins,
                var_types,
                fn_edges,
            );
            walk_expr(body, module, mod_idx, closure_origins, var_types, fn_edges);
        }
        ExprKind::LetRec { bindings, body } => {
            for (var_id, _ty, fn_id, _captures) in bindings {
                closure_origins.insert(*var_id, *fn_id);
            }
            walk_expr(body, module, mod_idx, closure_origins, var_types, fn_edges);
        }
        ExprKind::LetJoin {
            name: _,
            params,
            join_body,
            body,
            is_recur,
        } => {
            for (var_id, ty) in params {
                var_types.insert(*var_id, ty.clone());
            }
            // Both recur and non-recur join bodies are inlined (as
            // while(true) loops or helper functions), so if the join body
            // suspends, the enclosing function suspends.
            walk_expr(
                join_body,
                module,
                mod_idx,
                closure_origins,
                var_types,
                fn_edges,
            );
            walk_expr(body, module, mod_idx, closure_origins, var_types, fn_edges);
        }
        ExprKind::BoolSwitch {
            scrutinee: _,
            true_body,
            false_body,
        } => {
            walk_expr(
                true_body,
                module,
                mod_idx,
                closure_origins,
                var_types,
                fn_edges,
            );
            walk_expr(
                false_body,
                module,
                mod_idx,
                closure_origins,
                var_types,
                fn_edges,
            );
        }
        ExprKind::Switch {
            scrutinee: _,
            branches,
            default,
        } => {
            for branch in branches {
                for (var_id, ty) in &branch.bindings {
                    var_types.insert(*var_id, ty.clone());
                }
                walk_expr(
                    &branch.body,
                    module,
                    mod_idx,
                    closure_origins,
                    var_types,
                    fn_edges,
                );
            }
            if let Some(default_body) = default {
                walk_expr(
                    default_body,
                    module,
                    mod_idx,
                    closure_origins,
                    var_types,
                    fn_edges,
                );
            }
        }
        ExprKind::AutoClose { body, .. } => {
            walk_expr(body, module, mod_idx, closure_origins, var_types, fn_edges);
        }
        ExprKind::Jump { .. } | ExprKind::Atom(_) => {}
    }
}

/// Inspect a simple expression for call edges, closure origins, etc.
fn walk_simple_expr(
    kind: &SimpleExprKind,
    bind: VarId,
    module: &Module,
    mod_idx: usize,
    closure_origins: &mut HashMap<VarId, FnId>,
    var_types: &HashMap<VarId, Type>,
    fn_edges: &mut FnEdges,
) {
    match kind {
        SimpleExprKind::Call { func, .. } => {
            fn_edges.call_targets.push((mod_idx, *func));
        }
        SimpleExprKind::MakeClosure { func, .. } => {
            closure_origins.insert(bind, *func);
        }
        SimpleExprKind::CallClosure { closure, .. } => {
            if let Atom::Var(v) = closure {
                if let Some(&fn_id) = closure_origins.get(v) {
                    fn_edges.call_targets.push((mod_idx, fn_id));
                } else {
                    fn_edges.has_unresolved_closure_call = true;
                }
            } else {
                fn_edges.has_unresolved_closure_call = true;
            }
        }
        SimpleExprKind::TraitCall {
            trait_name: _,
            method_name,
            args,
        } => {
            // Phase 4 — Trait call resolution.
            // args[0] is the dict. Try to resolve to a concrete method
            // using the dict's type (which carries the trait name and target).
            if let Some(Atom::Var(dict_var)) = args.first() {
                if let Some(dict_type) = var_types.get(dict_var) {
                    if let Type::Dict {
                        trait_name: dict_trait,
                        target,
                    } = dict_type
                    {
                        if let Some(fn_id) =
                            resolve_trait_method(module, dict_trait, target, method_name)
                        {
                            fn_edges.call_targets.push((mod_idx, fn_id));
                            return;
                        }
                    }
                }
            }
            fn_edges.has_unresolved_trait_call = true;
        }
        _ => {}
    }
}

/// Try to resolve a trait method call to a concrete FnId via instance lookup.
fn resolve_trait_method(
    module: &Module,
    trait_name: &TraitName,
    target: &Type,
    method_name: &str,
) -> Option<FnId> {
    for inst in &module.instances {
        if inst.trait_name != *trait_name {
            continue;
        }
        // Try exact match first.
        if inst.target_type == *target {
            return inst
                .method_fn_ids
                .iter()
                .find(|(name, _)| name == method_name)
                .map(|(_, id)| *id);
        }
        // Try parametric match via bind_type_vars.
        let mut bindings = HashMap::new();
        if bind_type_vars(&inst.target_type, target, &mut bindings) {
            return inst
                .method_fn_ids
                .iter()
                .find(|(name, _)| name == method_name)
                .map(|(_, id)| *id);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeSet, HashMap};
    use krypton_typechecker::types::TypeVarGen;

    fn expr(ty: Type, kind: ExprKind) -> Expr {
        Expr::new((0, 0), ty, kind)
    }

    fn simple(kind: SimpleExprKind) -> SimpleExpr {
        SimpleExpr::new((0, 0), kind)
    }

    fn make_module(name: &str) -> Module {
        Module {
            name: name.to_string(),
            structs: vec![],
            sum_types: vec![],
            functions: vec![],
            fn_identities: HashMap::new(),
            extern_fns: vec![],
            extern_types: vec![],
            extern_traits: vec![],
            imported_fns: vec![],
            traits: vec![],
            instances: vec![],
            tuple_arities: BTreeSet::new(),
            module_path: ModulePath::new(name),
            fn_dict_requirements: HashMap::new(),
            fn_exit_closes: HashMap::new(),
        }
    }

    /// Build a core/actor module with standard extern fns.
    /// Uses simplified types (Int everywhere) since the analysis only cares
    /// about function names and call structure, not types.
    fn make_actor_module() -> Module {
        let mut m = make_module("core/actor");

        let js_target = ExternTarget::Js {
            module: "../extern/js/actor.mjs".to_string(),
        };

        let seeds: &[(&str, FnId, bool)] = &[
            ("raw_receive", FnId(0), false),
            ("raw_receive_timeout", FnId(1), true),
            ("raw_ask", FnId(2), true),
            ("raw_send", FnId(3), false),
        ];

        for &(name, id, nullable) in seeds {
            m.extern_fns.push(ExternFnDef {
                id,
                name: name.to_string(),
                declaring_module_path: "core/actor".to_string(),
                span: (0, 0),
                target: js_target.clone(),
                nullable,
                throws: false,
                call_kind: ExternCallKind::Static,
                param_types: vec![Type::Int],
                return_type: Type::Int,
                bridge_params: vec![],
            });
            m.fn_identities.insert(
                id,
                FnIdentity::Extern {
                    canonical: CanonicalRef {
                        module: ModulePath::new("core/actor"),
                        symbol: LocalSymbolKey::Function(name.to_string()),
                    },
                    target: js_target.clone(),
                    name: name.to_string(),
                },
            );
        }

        m
    }

    // -----------------------------------------------------------------------
    // Seed tests
    // -----------------------------------------------------------------------

    #[test]
    fn seed_raw_receive_suspends() {
        let actor = make_actor_module();
        let summary = analyze_suspend(&[actor]);
        assert!(summary.fn_suspends(0, FnId(0)));
    }

    #[test]
    fn seed_raw_receive_timeout_suspends() {
        let actor = make_actor_module();
        let summary = analyze_suspend(&[actor]);
        assert!(summary.fn_suspends(0, FnId(1)));
    }

    #[test]
    fn seed_raw_ask_suspends() {
        let actor = make_actor_module();
        let summary = analyze_suspend(&[actor]);
        assert!(summary.fn_suspends(0, FnId(2)));
    }

    #[test]
    fn raw_send_does_not_suspend() {
        let actor = make_actor_module();
        let summary = analyze_suspend(&[actor]);
        assert!(!summary.fn_suspends(0, FnId(3)));
    }

    // -----------------------------------------------------------------------
    // Transitive tests
    // -----------------------------------------------------------------------

    #[test]
    fn direct_call_transitive() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // FnId(0) in user module calls raw_receive (FnId(0) in actor module)
        // via an imported fn.
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );

        // FnId(1): caller that calls the imported raw_receive
        user.functions.push(FnDef {
            id: FnId(1),
            name: "my_receive".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "my_receive".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        // The imported fn should suspend (via import edge).
        assert!(summary.fn_suspends(1, FnId(0)));
        // The caller should suspend transitively.
        assert!(summary.fn_suspends(1, FnId(1)));
    }

    #[test]
    fn two_hop_transitive() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // Import raw_receive as FnId(0).
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );

        // FnId(1): middle — calls imported raw_receive
        user.functions.push(FnDef {
            id: FnId(1),
            name: "middle".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "middle".to_string(),
            },
        );

        // FnId(2): outer — calls middle
        user.functions.push(FnDef {
            id: FnId(2),
            name: "outer".to_string(),
            params: vec![(VarId(10), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(11),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(1),
                        args: vec![Atom::Var(VarId(10))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(11))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "outer".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(summary.fn_suspends(1, FnId(1)), "middle should suspend");
        assert!(summary.fn_suspends(1, FnId(2)), "outer should suspend");
    }

    #[test]
    fn non_suspending_chain() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // Import raw_send as FnId(0).
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_send".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_send".to_string(),
            param_types: vec![
                Type::Named("Ref".to_string(), vec![Type::Int]),
                Type::Int,
            ],
            return_type: Type::Unit,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_send".to_string()),
                },
                local_alias: "raw_send".to_string(),
            },
        );

        // FnId(1): calls raw_send
        user.functions.push(FnDef {
            id: FnId(1),
            name: "sender".to_string(),
            params: vec![
                (VarId(0), Type::Named("Ref".to_string(), vec![Type::Int])),
                (VarId(1), Type::Int),
            ],
            return_type: Type::Unit,
            body: expr(
                Type::Unit,
                ExprKind::Let {
                    bind: VarId(2),
                    ty: Type::Unit,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0)), Atom::Var(VarId(1))],
                    }),
                    body: Box::new(expr(Type::Unit, ExprKind::Atom(Atom::Lit(Literal::Unit)))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "sender".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(!summary.fn_suspends(1, FnId(0)), "imported raw_send should not suspend");
        assert!(!summary.fn_suspends(1, FnId(1)), "caller of raw_send should not suspend");
    }

    // -----------------------------------------------------------------------
    // Closure tests
    // -----------------------------------------------------------------------

    #[test]
    fn make_closure_then_call() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // Import raw_receive as FnId(0).
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );

        // FnId(1): a function that calls raw_receive (the closure body)
        user.functions.push(FnDef {
            id: FnId(1),
            name: "recv_closure".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "recv_closure".to_string(),
            },
        );

        // FnId(2): makes a closure from FnId(1), then calls it
        user.functions.push(FnDef {
            id: FnId(2),
            name: "caller".to_string(),
            params: vec![(VarId(10), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(11),
                    ty: Type::Fn(
                        vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
                        Box::new(Type::Int),
                    ),
                    value: simple(SimpleExprKind::MakeClosure {
                        func: FnId(1),
                        captures: vec![],
                    }),
                    body: Box::new(expr(
                        Type::Int,
                        ExprKind::Let {
                            bind: VarId(12),
                            ty: Type::Int,
                            value: simple(SimpleExprKind::CallClosure {
                                closure: Atom::Var(VarId(11)),
                                args: vec![Atom::Var(VarId(10))],
                            }),
                            body: Box::new(expr(
                                Type::Int,
                                ExprKind::Atom(Atom::Var(VarId(12))),
                            )),
                        },
                    )),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "caller".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(summary.fn_suspends(1, FnId(2)), "caller via closure should suspend");
    }

    #[test]
    fn conservative_unknown_closure() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // FnId(0): takes a closure parameter and calls it — unknown origin
        user.functions.push(FnDef {
            id: FnId(0),
            name: "apply".to_string(),
            params: vec![
                (
                    VarId(0),
                    Type::Fn(vec![Type::Unit], Box::new(Type::Int)),
                ),
            ],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::CallClosure {
                        closure: Atom::Var(VarId(0)),
                        args: vec![Atom::Lit(Literal::Unit)],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "apply".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(
            summary.fn_suspends(1, FnId(0)),
            "CallClosure on unknown var should conservatively suspend"
        );
    }

    // -----------------------------------------------------------------------
    // LetRec tests
    // -----------------------------------------------------------------------

    #[test]
    fn letrec_suspending() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // Import raw_receive as FnId(0).
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );

        // FnId(1): the underlying function for the letrec closure — calls raw_receive
        user.functions.push(FnDef {
            id: FnId(1),
            name: "recv_loop".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "recv_loop".to_string(),
            },
        );

        // FnId(2): uses LetRec to bind recv_loop as a closure, then calls it
        user.functions.push(FnDef {
            id: FnId(2),
            name: "main".to_string(),
            params: vec![(VarId(10), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::LetRec {
                    bindings: vec![(VarId(11), Type::Fn(vec![Type::Named("Mailbox".to_string(), vec![Type::Int])], Box::new(Type::Int)), FnId(1), vec![])],
                    body: Box::new(expr(
                        Type::Int,
                        ExprKind::Let {
                            bind: VarId(12),
                            ty: Type::Int,
                            value: simple(SimpleExprKind::CallClosure {
                                closure: Atom::Var(VarId(11)),
                                args: vec![Atom::Var(VarId(10))],
                            }),
                            body: Box::new(expr(
                                Type::Int,
                                ExprKind::Atom(Atom::Var(VarId(12))),
                            )),
                        },
                    )),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "main".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(summary.fn_suspends(1, FnId(2)), "caller via LetRec-bound closure should suspend");
    }

    #[test]
    fn mutual_recursion() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // Import raw_receive as FnId(0).
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );

        // FnId(1): fn_a calls fn_b
        user.functions.push(FnDef {
            id: FnId(1),
            name: "fn_a".to_string(),
            params: vec![(VarId(0), Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(2),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "fn_a".to_string(),
            },
        );

        // FnId(2): fn_b calls raw_receive (FnId(0)) and fn_a (FnId(1))
        user.functions.push(FnDef {
            id: FnId(2),
            name: "fn_b".to_string(),
            params: vec![(VarId(10), Type::Int)],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(11),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(10))],
                    }),
                    body: Box::new(expr(
                        Type::Int,
                        ExprKind::Let {
                            bind: VarId(12),
                            ty: Type::Int,
                            value: simple(SimpleExprKind::Call {
                                func: FnId(1),
                                args: vec![Atom::Var(VarId(11))],
                            }),
                            body: Box::new(expr(
                                Type::Int,
                                ExprKind::Atom(Atom::Var(VarId(12))),
                            )),
                        },
                    )),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "fn_b".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(summary.fn_suspends(1, FnId(1)), "fn_a should suspend (mutual recursion)");
        assert!(summary.fn_suspends(1, FnId(2)), "fn_b should suspend (calls raw_receive)");
    }

    // -----------------------------------------------------------------------
    // Join point tests
    // -----------------------------------------------------------------------

    #[test]
    fn non_recur_join_suspends() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // Import raw_receive as FnId(0).
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );

        // FnId(1): has a non-recur LetJoin whose body calls raw_receive
        user.functions.push(FnDef {
            id: FnId(1),
            name: "with_join".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::LetJoin {
                    name: VarId(10),
                    params: vec![(VarId(11), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
                    join_body: Box::new(expr(
                        Type::Int,
                        ExprKind::Let {
                            bind: VarId(12),
                            ty: Type::Int,
                            value: simple(SimpleExprKind::Call {
                                func: FnId(0),
                                args: vec![Atom::Var(VarId(11))],
                            }),
                            body: Box::new(expr(
                                Type::Int,
                                ExprKind::Atom(Atom::Var(VarId(12))),
                            )),
                        },
                    )),
                    body: Box::new(expr(
                        Type::Int,
                        ExprKind::Jump {
                            target: VarId(10),
                            args: vec![Atom::Var(VarId(0))],
                        },
                    )),
                    is_recur: false,
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "with_join".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(
            summary.fn_suspends(1, FnId(1)),
            "function with suspending non-recur join body should suspend"
        );
    }

    // -----------------------------------------------------------------------
    // Trait call tests
    // -----------------------------------------------------------------------

    #[test]
    fn trait_call_resolved() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        // Import raw_receive as FnId(0).
        user.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );

        let trait_name = TraitName::new("app/main".to_string(), "Handler".to_string());

        // FnId(1): the instance method — calls raw_receive
        user.functions.push(FnDef {
            id: FnId(1),
            name: "Handler$Int$handle".to_string(),
            params: vec![
                (VarId(0), Type::Dict {
                    trait_name: trait_name.clone(),
                    target: Box::new(Type::Int),
                }),
                (VarId(1), Type::Named("Mailbox".to_string(), vec![Type::Int])),
            ],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(2),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(1))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(2))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "Handler$Int$handle".to_string(),
            },
        );

        // Instance: Handler for Int
        user.instances.push(InstanceDef {
            trait_name: trait_name.clone(),
            target_type: Type::Int,
            target_type_name: "Int".to_string(),
            method_fn_ids: vec![("handle".to_string(), FnId(1))],
            sub_dict_requirements: vec![],
            is_intrinsic: false,
            is_imported: false,
        });

        // FnId(2): calls handle via TraitCall with a known dict type
        user.functions.push(FnDef {
            id: FnId(2),
            name: "caller".to_string(),
            params: vec![(VarId(10), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(11),
                    ty: Type::Dict {
                        trait_name: trait_name.clone(),
                        target: Box::new(Type::Int),
                    },
                    value: simple(SimpleExprKind::GetDict {
                        instance_ref: CanonicalRef {
                            module: ModulePath::new("app/main"),
                            symbol: LocalSymbolKey::Instance {
                                trait_name: "Handler".to_string(),
                                target_type: "Int".to_string(),
                            },
                        },
                        trait_name: trait_name.clone(),
                        ty: Type::Int,
                    }),
                    body: Box::new(expr(
                        Type::Int,
                        ExprKind::Let {
                            bind: VarId(12),
                            ty: Type::Int,
                            value: simple(SimpleExprKind::TraitCall {
                                trait_name: trait_name.clone(),
                                method_name: "handle".to_string(),
                                args: vec![Atom::Var(VarId(11)), Atom::Var(VarId(10))],
                            }),
                            body: Box::new(expr(
                                Type::Int,
                                ExprKind::Atom(Atom::Var(VarId(12))),
                            )),
                        },
                    )),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(2),
            FnIdentity::Local {
                name: "caller".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(
            summary.fn_suspends(1, FnId(2)),
            "caller via resolved TraitCall should suspend"
        );
    }

    #[test]
    fn trait_call_unresolved_conservative() {
        let actor = make_actor_module();
        let mut user = make_module("app/main");

        let trait_name = TraitName::new("app/main".to_string(), "Handler".to_string());
        let mut gen = TypeVarGen::new();
        let tv = gen.fresh();

        // FnId(0): receives a dict parameter and does a TraitCall — no instance
        // in this module, so resolution fails → conservative suspend.
        user.functions.push(FnDef {
            id: FnId(0),
            name: "generic_call".to_string(),
            params: vec![
                (VarId(0), Type::Dict {
                    trait_name: trait_name.clone(),
                    target: Box::new(Type::Var(tv)),
                }),
                (VarId(1), Type::Int),
            ],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(2),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::TraitCall {
                        trait_name: trait_name.clone(),
                        method_name: "handle".to_string(),
                        args: vec![Atom::Var(VarId(0)), Atom::Var(VarId(1))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(2))))),
                },
            ),
        });
        user.fn_identities.insert(
            FnId(0),
            FnIdentity::Local {
                name: "generic_call".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, user]);
        assert!(
            summary.fn_suspends(1, FnId(0)),
            "unresolved TraitCall should conservatively suspend"
        );
    }

    // -----------------------------------------------------------------------
    // Cross-module tests
    // -----------------------------------------------------------------------

    #[test]
    fn cross_module_imported_fn() {
        let actor = make_actor_module();

        // Middle module: imports raw_receive and wraps it.
        let mut middle = make_module("lib/handler");
        middle.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "raw_receive".to_string(),
            source_module: "core/actor".to_string(),
            original_name: "raw_receive".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        middle.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("core/actor"),
                    symbol: LocalSymbolKey::Function("raw_receive".to_string()),
                },
                local_alias: "raw_receive".to_string(),
            },
        );
        middle.functions.push(FnDef {
            id: FnId(1),
            name: "handle".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        middle.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "handle".to_string(),
            },
        );

        // App module: imports handle from middle.
        let mut app = make_module("app/main");
        app.imported_fns.push(ImportedFnDef {
            id: FnId(0),
            name: "handle".to_string(),
            source_module: "lib/handler".to_string(),
            original_name: "handle".to_string(),
            param_types: vec![Type::Named("Mailbox".to_string(), vec![Type::Int])],
            return_type: Type::Int,
        });
        app.fn_identities.insert(
            FnId(0),
            FnIdentity::Imported {
                canonical: CanonicalRef {
                    module: ModulePath::new("lib/handler"),
                    symbol: LocalSymbolKey::Function("handle".to_string()),
                },
                local_alias: "handle".to_string(),
            },
        );

        // FnId(1): calls imported handle
        app.functions.push(FnDef {
            id: FnId(1),
            name: "main".to_string(),
            params: vec![(VarId(0), Type::Named("Mailbox".to_string(), vec![Type::Int]))],
            return_type: Type::Int,
            body: expr(
                Type::Int,
                ExprKind::Let {
                    bind: VarId(1),
                    ty: Type::Int,
                    value: simple(SimpleExprKind::Call {
                        func: FnId(0),
                        args: vec![Atom::Var(VarId(0))],
                    }),
                    body: Box::new(expr(Type::Int, ExprKind::Atom(Atom::Var(VarId(1))))),
                },
            ),
        });
        app.fn_identities.insert(
            FnId(1),
            FnIdentity::Local {
                name: "main".to_string(),
            },
        );

        let summary = analyze_suspend(&[actor, middle, app]);
        // middle::handle should suspend (calls raw_receive).
        assert!(summary.fn_suspends(1, FnId(1)), "middle::handle should suspend");
        // app::handle (imported) should suspend.
        assert!(summary.fn_suspends(2, FnId(0)), "app's imported handle should suspend");
        // app::main should suspend.
        assert!(summary.fn_suspends(2, FnId(1)), "app::main should suspend");
    }
}
