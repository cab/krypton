// TypeExpr → Type resolution and `TypeVarGen` seeding. Free helpers used
// during the pre-context registration phase to allocate type-param ids
// for private types and to bump the IR-side fresh allocator past every
// id the typechecker has already issued.

use rustc_hash::FxHashMap;

use krypton_typechecker::typed_ast::{ExportedTypeKind, TypedModule};
use krypton_typechecker::types::{Type, TypeVarGen, TypeVarId};

/// Build a TypeVarId map from type parameter names using a shared TypeVarGen.
pub(super) fn build_type_param_map(
    type_params: &[String],
    gen: &mut TypeVarGen,
) -> FxHashMap<String, TypeVarId> {
    type_params
        .iter()
        .map(|name| (name.clone(), gen.fresh()))
        .collect()
}

/// Walk every TypeVarId reachable from `typed` and ensure `gen` produces
/// strictly higher ids on subsequent `.fresh()` calls. Run once after
/// `LowerCtx::new` so IR-side fresh allocations do not collide with
/// typechecker-allocated ids that flow through `exported_type_infos`,
/// fn schemes, instance defs, or trait defs.
pub(super) fn seed_type_var_gen_past_typed(typed: &TypedModule, gen: &mut TypeVarGen) {
    fn collect(ty: &Type, out: &mut impl FnMut(TypeVarId)) {
        match ty {
            Type::Var(id) => out(*id),
            Type::Fn(params, ret) => {
                for (_, p) in params {
                    collect(p, out);
                }
                collect(ret, out);
            }
            Type::Named(_, args) => {
                for a in args {
                    collect(a, out);
                }
            }
            Type::App(head, args) => {
                collect(head, out);
                for a in args {
                    collect(a, out);
                }
            }
            Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => collect(inner, out),
            Type::Tuple(elts) => {
                for e in elts {
                    collect(e, out);
                }
            }
            Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit | Type::FnHole => {}
        }
    }

    let mut bump = |id: TypeVarId| gen.reserve_past(id);

    for info in typed.exported_type_infos.values() {
        for &id in &info.type_param_vars {
            bump(id);
        }
        match &info.kind {
            ExportedTypeKind::Record { fields } => {
                for (_, t) in fields {
                    collect(t, &mut bump);
                }
            }
            ExportedTypeKind::Sum { variants } => {
                for v in variants {
                    for t in &v.fields {
                        collect(t, &mut bump);
                    }
                }
            }
            ExportedTypeKind::Opaque => {}
        }
    }

    for entry in &typed.fn_types {
        for &id in &entry.scheme.vars {
            bump(id);
        }
        collect(&entry.scheme.ty, &mut bump);
    }

    for inst in &typed.instance_defs {
        for &id in inst.type_var_ids.values() {
            bump(id);
        }
        for t in &inst.target_types {
            collect(t, &mut bump);
        }
        for m in &inst.methods {
            for &id in &m.scheme.vars {
                bump(id);
            }
            collect(&m.scheme.ty, &mut bump);
        }
    }

    for td in &typed.trait_defs {
        bump(td.type_var_id);
        for &id in &td.type_var_ids {
            bump(id);
        }
        for (params, ret) in td.method_tc_types.values() {
            for (_, p) in params {
                collect(p, &mut bump);
            }
            collect(ret, &mut bump);
        }
    }
}

/// Simple TypeExpr → Type conversion for private types.
pub(super) fn resolve_type_expr_simple(
    texpr: &krypton_parser::ast::TypeExpr,
    type_param_map: &FxHashMap<String, TypeVarId>,
) -> Type {
    use krypton_parser::ast::TypeExpr;
    match texpr {
        TypeExpr::Named { name, .. } => match name.as_str() {
            "Int" => Type::Int,
            "Float" => Type::Float,
            "Bool" => Type::Bool,
            "String" => Type::String,
            "Unit" => Type::Unit,
            _ => Type::Named(name.clone(), vec![]),
        },
        TypeExpr::Var { name, .. } => {
            if let Some(&id) = type_param_map.get(name) {
                Type::Var(id)
            } else {
                Type::Named(name.clone(), vec![])
            }
        }
        TypeExpr::App { name, args, .. } => {
            // Check if the name is a type variable
            if let Some(&id) = type_param_map.get(name) {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_simple(a, type_param_map))
                    .collect();
                Type::App(Box::new(Type::Var(id)), resolved_args)
            } else {
                let resolved_args: Vec<Type> = args
                    .iter()
                    .map(|a| resolve_type_expr_simple(a, type_param_map))
                    .collect();
                Type::Named(name.clone(), resolved_args)
            }
        }
        TypeExpr::Fn { params, ret, .. } => {
            let param_types: Vec<Type> = params
                .iter()
                .map(|p| resolve_type_expr_simple(&p.ty, type_param_map))
                .collect();
            let ret_type = resolve_type_expr_simple(ret, type_param_map);
            Type::fn_consuming(param_types, ret_type)
        }
        TypeExpr::Own { inner, .. } => {
            Type::Own(Box::new(resolve_type_expr_simple(inner, type_param_map)))
        }
        TypeExpr::Shape { inner, .. } => resolve_type_expr_simple(inner, type_param_map),
        TypeExpr::Tuple { elements, .. } => {
            let elem_types: Vec<Type> = elements
                .iter()
                .map(|e| resolve_type_expr_simple(e, type_param_map))
                .collect();
            Type::Tuple(elem_types)
        }
        TypeExpr::Wildcard { .. } | TypeExpr::Qualified { .. } => Type::Unit,
    }
}
