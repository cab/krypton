use std::collections::{HashMap, HashSet};

use crate::expr::{Atom, Expr, ExprKind, SimpleExpr, SwitchBranch};
use crate::{FnDef, FnId, Module, StructDef, SumTypeDef, VarId};

/// Merge N per-module IR modules into a single whole-program module with
/// globally unique `FnId`s and `VarId`s, resolved cross-module references,
/// and deduplicated type definitions.
pub fn link(modules: Vec<Module>) -> Module {
    if modules.is_empty() {
        return Module {
            name: String::new(),
            structs: Vec::new(),
            sum_types: Vec::new(),
            functions: Vec::new(),
            fn_names: HashMap::new(),
            extern_fn_types: HashMap::new(),
        };
    }
    if modules.len() == 1 {
        return modules.into_iter().next().unwrap();
    }

    let name = modules[0].name.clone();

    // Step 1: Compute per-module offsets for FnId and VarId.
    let mut fn_offsets: Vec<u32> = Vec::with_capacity(modules.len());
    let mut var_offsets: Vec<u32> = Vec::with_capacity(modules.len());
    let mut running_fn: u32 = 0;
    let mut running_var: u32 = 0;
    for module in &modules {
        fn_offsets.push(running_fn);
        var_offsets.push(running_var);
        running_fn += max_fn_id(module) + 1;
        running_var += max_var_id(module) + 1;
    }

    // Step 2: Build global name->FnId table. Locally-defined functions take priority.
    let mut global_name_to_fn: HashMap<String, FnId> = HashMap::new();
    for (i, module) in modules.iter().enumerate() {
        let offset = fn_offsets[i];
        let local_ids: HashSet<FnId> = module.functions.iter().map(|f| f.id).collect();
        for (&old_id, debug_name) in &module.fn_names {
            if local_ids.contains(&old_id) {
                let new_id = FnId(old_id.0 + offset);
                global_name_to_fn.entry(debug_name.clone()).or_insert(new_id);
            }
        }
    }
    // Second pass: register extern-only names not yet in the table.
    for (i, module) in modules.iter().enumerate() {
        let offset = fn_offsets[i];
        let local_ids: HashSet<FnId> = module.functions.iter().map(|f| f.id).collect();
        for (&old_id, debug_name) in &module.fn_names {
            if !local_ids.contains(&old_id) {
                let new_id = FnId(old_id.0 + offset);
                global_name_to_fn.entry(debug_name.clone()).or_insert(new_id);
            }
        }
    }

    // Collect names of all locally-defined functions across all modules.
    let mut defined_fn_names: HashSet<String> = HashSet::new();
    for module in &modules {
        let local_ids: HashSet<FnId> = module.functions.iter().map(|f| f.id).collect();
        for (&old_id, debug_name) in &module.fn_names {
            if local_ids.contains(&old_id) {
                defined_fn_names.insert(debug_name.clone());
            }
        }
    }

    // Step 3 & 4: Renumber each module, merge functions, types, and extern_fn_types.
    let mut all_functions: Vec<FnDef> = Vec::new();
    let mut merged_fn_names: HashMap<FnId, String> = HashMap::new();
    let mut merged_extern_fn_types: HashMap<FnId, crate::Type> = HashMap::new();
    let mut seen_struct_names: HashSet<String> = HashSet::new();
    let mut merged_structs: Vec<StructDef> = Vec::new();
    let mut seen_sum_names: HashSet<String> = HashSet::new();
    let mut merged_sum_types: Vec<SumTypeDef> = Vec::new();

    for (i, module) in modules.into_iter().enumerate() {
        let fn_offset = fn_offsets[i];
        let var_offset = var_offsets[i];

        // Deduplicate structs (first occurrence by name wins).
        for s in module.structs {
            if seen_struct_names.insert(s.name.clone()) {
                merged_structs.push(s);
            }
        }
        // Deduplicate sum types.
        for s in module.sum_types {
            if seen_sum_names.insert(s.name.clone()) {
                merged_sum_types.push(s);
            }
        }

        let local_ids: HashSet<FnId> = module.functions.iter().map(|f| f.id).collect();

        // Build old_FnId -> new_FnId map for this module.
        let mut fn_map: HashMap<FnId, FnId> = HashMap::new();
        for (&old_id, debug_name) in &module.fn_names {
            if local_ids.contains(&old_id) {
                fn_map.insert(old_id, FnId(old_id.0 + fn_offset));
            } else {
                let resolved = global_name_to_fn
                    .get(debug_name)
                    .copied()
                    .unwrap_or(FnId(old_id.0 + fn_offset));
                fn_map.insert(old_id, resolved);
            }
        }

        // Register fn_names.
        for func in &module.functions {
            let new_id = fn_map[&func.id];
            merged_fn_names
                .entry(new_id)
                .or_insert_with(|| func.debug_name.clone());
        }
        for (&old_id, debug_name) in &module.fn_names {
            let new_id = fn_map[&old_id];
            merged_fn_names
                .entry(new_id)
                .or_insert_with(|| debug_name.clone());
        }

        // Merge extern_fn_types: only keep truly external functions (not defined
        // in any module).
        for (&old_id, ty) in &module.extern_fn_types {
            if let Some(debug_name) = module.fn_names.get(&old_id) {
                if defined_fn_names.contains(debug_name) {
                    continue;
                }
            }
            let new_id = fn_map
                .get(&old_id)
                .copied()
                .unwrap_or(FnId(old_id.0 + fn_offset));
            merged_extern_fn_types
                .entry(new_id)
                .or_insert_with(|| ty.clone());
        }

        // Renumber and collect functions.
        for mut func in module.functions {
            func.id = fn_map[&func.id];
            rewrite_params(&mut func.params, var_offset);
            rewrite_expr(&mut func.body, &fn_map, var_offset);
            all_functions.push(func);
        }
    }

    Module {
        name,
        structs: merged_structs,
        sum_types: merged_sum_types,
        functions: all_functions,
        fn_names: merged_fn_names,
        extern_fn_types: merged_extern_fn_types,
    }
}

fn max_fn_id(module: &Module) -> u32 {
    let from_functions = module.functions.iter().map(|f| f.id.0).max().unwrap_or(0);
    let from_names = module.fn_names.keys().map(|id| id.0).max().unwrap_or(0);
    let from_externs = module
        .extern_fn_types
        .keys()
        .map(|id| id.0)
        .max()
        .unwrap_or(0);
    from_functions.max(from_names).max(from_externs)
}

fn max_var_id(module: &Module) -> u32 {
    let mut max_id: u32 = 0;
    for func in &module.functions {
        for &(var, _) in &func.params {
            max_id = max_id.max(var.0);
        }
        max_var_in_expr(&func.body, &mut max_id);
    }
    max_id
}

fn max_var_in_expr(expr: &Expr, max_id: &mut u32) {
    match &expr.kind {
        ExprKind::Let {
            bind, value, body, ..
        } => {
            *max_id = (*max_id).max(bind.0);
            max_var_in_simple_expr(value, max_id);
            max_var_in_expr(body, max_id);
        }
        ExprKind::LetRec { bindings, body } => {
            for (var, _, _, captures) in bindings {
                *max_id = (*max_id).max(var.0);
                for atom in captures {
                    max_var_in_atom(atom, max_id);
                }
            }
            max_var_in_expr(body, max_id);
        }
        ExprKind::LetJoin {
            name,
            params,
            join_body,
            body,
        } => {
            *max_id = (*max_id).max(name.0);
            for &(var, _) in params {
                *max_id = (*max_id).max(var.0);
            }
            max_var_in_expr(join_body, max_id);
            max_var_in_expr(body, max_id);
        }
        ExprKind::Jump { target, args } => {
            *max_id = (*max_id).max(target.0);
            for atom in args {
                max_var_in_atom(atom, max_id);
            }
        }
        ExprKind::Switch {
            scrutinee,
            branches,
            default,
        } => {
            max_var_in_atom(scrutinee, max_id);
            for branch in branches {
                for &(var, _) in &branch.bindings {
                    *max_id = (*max_id).max(var.0);
                }
                max_var_in_expr(&branch.body, max_id);
            }
            if let Some(d) = default {
                max_var_in_expr(d, max_id);
            }
        }
        ExprKind::Atom(atom) => {
            max_var_in_atom(atom, max_id);
        }
    }
}

fn max_var_in_simple_expr(expr: &SimpleExpr, max_id: &mut u32) {
    match expr {
        SimpleExpr::Call { args, .. } => {
            for atom in args {
                max_var_in_atom(atom, max_id);
            }
        }
        SimpleExpr::CallClosure { closure, args } => {
            max_var_in_atom(closure, max_id);
            for atom in args {
                max_var_in_atom(atom, max_id);
            }
        }
        SimpleExpr::MakeClosure { captures, .. } => {
            for atom in captures {
                max_var_in_atom(atom, max_id);
            }
        }
        SimpleExpr::Construct { fields, .. } | SimpleExpr::ConstructVariant { fields, .. } => {
            for atom in fields {
                max_var_in_atom(atom, max_id);
            }
        }
        SimpleExpr::Project { value, .. } | SimpleExpr::Tag { value } => {
            max_var_in_atom(value, max_id);
        }
        SimpleExpr::MakeTuple { elements } | SimpleExpr::MakeVec { elements, .. } => {
            for atom in elements {
                max_var_in_atom(atom, max_id);
            }
        }
        SimpleExpr::TupleProject { value, .. } => {
            max_var_in_atom(value, max_id);
        }
        SimpleExpr::PrimOp { args, .. } => {
            for atom in args {
                max_var_in_atom(atom, max_id);
            }
        }
        SimpleExpr::GetDict { .. } => {}
        SimpleExpr::MakeDict { sub_dicts, .. } => {
            for atom in sub_dicts {
                max_var_in_atom(atom, max_id);
            }
        }
        SimpleExpr::Atom(atom) => {
            max_var_in_atom(atom, max_id);
        }
    }
}

fn max_var_in_atom(atom: &Atom, max_id: &mut u32) {
    if let Atom::Var(var) = atom {
        *max_id = (*max_id).max(var.0);
    }
}

fn rewrite_params(params: &mut [(VarId, crate::Type)], var_offset: u32) {
    for (var, _) in params.iter_mut() {
        var.0 += var_offset;
    }
}

fn rewrite_expr(expr: &mut Expr, fn_map: &HashMap<FnId, FnId>, var_offset: u32) {
    match &mut expr.kind {
        ExprKind::Let {
            bind, value, body, ..
        } => {
            bind.0 += var_offset;
            rewrite_simple_expr(value, fn_map, var_offset);
            rewrite_expr(body, fn_map, var_offset);
        }
        ExprKind::LetRec { bindings, body } => {
            for (var, _, fn_id, captures) in bindings.iter_mut() {
                var.0 += var_offset;
                if let Some(&new_id) = fn_map.get(fn_id) {
                    *fn_id = new_id;
                }
                for atom in captures.iter_mut() {
                    rewrite_atom(atom, var_offset);
                }
            }
            rewrite_expr(body, fn_map, var_offset);
        }
        ExprKind::LetJoin {
            name,
            params,
            join_body,
            body,
        } => {
            name.0 += var_offset;
            rewrite_params(params, var_offset);
            rewrite_expr(join_body, fn_map, var_offset);
            rewrite_expr(body, fn_map, var_offset);
        }
        ExprKind::Jump { target, args } => {
            target.0 += var_offset;
            for atom in args.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        ExprKind::Switch {
            scrutinee,
            branches,
            default,
        } => {
            rewrite_atom(scrutinee, var_offset);
            for branch in branches.iter_mut() {
                rewrite_branch(branch, fn_map, var_offset);
            }
            if let Some(d) = default {
                rewrite_expr(d, fn_map, var_offset);
            }
        }
        ExprKind::Atom(atom) => {
            rewrite_atom(atom, var_offset);
        }
    }
}

fn rewrite_branch(branch: &mut SwitchBranch, fn_map: &HashMap<FnId, FnId>, var_offset: u32) {
    rewrite_params(&mut branch.bindings, var_offset);
    rewrite_expr(&mut branch.body, fn_map, var_offset);
}

fn rewrite_simple_expr(
    expr: &mut SimpleExpr,
    fn_map: &HashMap<FnId, FnId>,
    var_offset: u32,
) {
    match expr {
        SimpleExpr::Call { func, args } => {
            if let Some(&new_id) = fn_map.get(func) {
                *func = new_id;
            }
            for atom in args.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        SimpleExpr::CallClosure { closure, args } => {
            rewrite_atom(closure, var_offset);
            for atom in args.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        SimpleExpr::MakeClosure { func, captures } => {
            if let Some(&new_id) = fn_map.get(func) {
                *func = new_id;
            }
            for atom in captures.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        SimpleExpr::Construct { fields, .. } | SimpleExpr::ConstructVariant { fields, .. } => {
            for atom in fields.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        SimpleExpr::Project { value, .. } | SimpleExpr::Tag { value } => {
            rewrite_atom(value, var_offset);
        }
        SimpleExpr::MakeTuple { elements } | SimpleExpr::MakeVec { elements, .. } => {
            for atom in elements.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        SimpleExpr::TupleProject { value, .. } => {
            rewrite_atom(value, var_offset);
        }
        SimpleExpr::PrimOp { args, .. } => {
            for atom in args.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        SimpleExpr::GetDict { .. } => {}
        SimpleExpr::MakeDict { sub_dicts, .. } => {
            for atom in sub_dicts.iter_mut() {
                rewrite_atom(atom, var_offset);
            }
        }
        SimpleExpr::Atom(atom) => {
            rewrite_atom(atom, var_offset);
        }
    }
}

fn rewrite_atom(atom: &mut Atom, var_offset: u32) {
    if let Atom::Var(var) = atom {
        var.0 += var_offset;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Literal;
    use crate::Type;

    fn make_module(name: &str, fn_id: u32, var_id: u32, debug_name: &str) -> Module {
        let fid = FnId(fn_id);
        let vid = VarId(var_id);
        Module {
            name: name.into(),
            structs: vec![],
            sum_types: vec![],
            functions: vec![FnDef {
                id: fid,
                debug_name: debug_name.into(),
                params: vec![(vid, Type::Int)],
                return_type: Type::Int,
                body: Expr {
                    kind: ExprKind::Atom(Atom::Var(vid)),
                    ty: Type::Int,
                },
            }],
            fn_names: HashMap::from([(fid, debug_name.into())]),
            extern_fn_types: HashMap::new(),
        }
    }

    #[test]
    fn link_two_modules_unique_ids() {
        let m1 = make_module("mod_a", 0, 0, "foo");
        let m2 = make_module("mod_b", 0, 0, "bar");

        let linked = link(vec![m1, m2]);

        assert_eq!(linked.functions.len(), 2);
        let ids: Vec<u32> = linked.functions.iter().map(|f| f.id.0).collect();
        assert_ne!(ids[0], ids[1], "FnIds must be globally unique");

        let var0 = linked.functions[0].params[0].0;
        let var1 = linked.functions[1].params[0].0;
        assert_ne!(var0, var1, "VarIds must be globally unique");
    }

    #[test]
    fn link_resolves_cross_module_refs() {
        let helper_fn = FnId(0);
        let main_fn = FnId(1);
        let mod_a = Module {
            name: "mod_a".into(),
            structs: vec![],
            sum_types: vec![],
            functions: vec![
                FnDef {
                    id: helper_fn,
                    debug_name: "helper".into(),
                    params: vec![(VarId(0), Type::Int)],
                    return_type: Type::Int,
                    body: Expr {
                        kind: ExprKind::Atom(Atom::Var(VarId(0))),
                        ty: Type::Int,
                    },
                },
                FnDef {
                    id: main_fn,
                    debug_name: "main".into(),
                    params: vec![],
                    return_type: Type::Int,
                    body: Expr {
                        kind: ExprKind::Let {
                            bind: VarId(1),
                            ty: Type::Int,
                            value: SimpleExpr::Call {
                                func: helper_fn,
                                args: vec![Atom::Lit(Literal::Int(42))],
                            },
                            body: Box::new(Expr {
                                kind: ExprKind::Atom(Atom::Var(VarId(1))),
                                ty: Type::Int,
                            }),
                        },
                        ty: Type::Int,
                    },
                },
            ],
            fn_names: HashMap::from([
                (helper_fn, "helper".into()),
                (main_fn, "main".into()),
            ]),
            extern_fn_types: HashMap::new(),
        };

        // Module B references "helper" as extern.
        let extern_helper = FnId(0);
        let use_helper_fn = FnId(1);
        let mod_b = Module {
            name: "mod_b".into(),
            structs: vec![],
            sum_types: vec![],
            functions: vec![FnDef {
                id: use_helper_fn,
                debug_name: "use_helper".into(),
                params: vec![],
                return_type: Type::Int,
                body: Expr {
                    kind: ExprKind::Let {
                        bind: VarId(0),
                        ty: Type::Int,
                        value: SimpleExpr::Call {
                            func: extern_helper,
                            args: vec![Atom::Lit(Literal::Int(99))],
                        },
                        body: Box::new(Expr {
                            kind: ExprKind::Atom(Atom::Var(VarId(0))),
                            ty: Type::Int,
                        }),
                    },
                    ty: Type::Int,
                },
            }],
            fn_names: HashMap::from([
                (extern_helper, "helper".into()),
                (use_helper_fn, "use_helper".into()),
            ]),
            extern_fn_types: HashMap::from([(
                extern_helper,
                Type::Fn(vec![Type::Int], Box::new(Type::Int)),
            )]),
        };

        let linked = link(vec![mod_a, mod_b]);

        let helper_def = linked
            .functions
            .iter()
            .find(|f| f.debug_name == "helper")
            .expect("helper should exist");
        let use_helper_def = linked
            .functions
            .iter()
            .find(|f| f.debug_name == "use_helper")
            .expect("use_helper should exist");

        // The call in use_helper should resolve to helper's global FnId.
        if let ExprKind::Let {
            value: SimpleExpr::Call { func, .. },
            ..
        } = &use_helper_def.body.kind
        {
            assert_eq!(
                *func, helper_def.id,
                "cross-module ref should resolve to helper's global FnId"
            );
        } else {
            panic!("expected Let/Call in use_helper body");
        }

        // "helper" should NOT be in extern_fn_types since it's defined.
        assert!(
            !linked.extern_fn_types.contains_key(&helper_def.id),
            "resolved cross-module fn should not remain in extern_fn_types"
        );
    }

    #[test]
    fn link_deduplicates_types() {
        let s1 = crate::StructDef {
            name: "Point".into(),
            type_params: vec![],
            fields: vec![("x".into(), Type::Int), ("y".into(), Type::Int)],
        };
        let s2 = s1.clone();

        let m1 = Module {
            name: "a".into(),
            structs: vec![s1],
            sum_types: vec![],
            functions: vec![],
            fn_names: HashMap::new(),
            extern_fn_types: HashMap::new(),
        };
        let m2 = Module {
            name: "b".into(),
            structs: vec![s2],
            sum_types: vec![],
            functions: vec![],
            fn_names: HashMap::new(),
            extern_fn_types: HashMap::new(),
        };

        let linked = link(vec![m1, m2]);
        assert_eq!(
            linked.structs.len(),
            1,
            "duplicate struct should be deduplicated"
        );
        assert_eq!(linked.structs[0].name, "Point");
    }

    #[test]
    fn link_single_module_passthrough() {
        let m = make_module("only", 0, 0, "main");
        let linked = link(vec![m]);
        assert_eq!(linked.functions.len(), 1);
        assert_eq!(linked.name, "only");
    }

    #[test]
    fn link_empty() {
        let linked = link(vec![]);
        assert!(linked.functions.is_empty());
    }
}
