//! Eager multi-parameter trait resolution with deferral.
//!
//! Walks the typed bodies of a single SCC and, for every trait method call whose
//! callee belongs to a multi-parameter trait, builds a position-tuple of types
//! (one per trait type variable, in declaration order) and tries to resolve it
//! via `find_instance_multi_partial`. A unique partial match pins free positions
//! by unification (similar to functional dependencies). Ambiguous and zero-match
//! entries are deferred — repeated to a fixed point so that pinning by one entry
//! can unblock others. No errors are emitted here; validation is left to
//! `checks::check_trait_instances`.
//!
//! Inserted into the SCC pipeline *between* the body inference (`scc_result?`)
//! and `generalize`, so that pinned secondary trait params (e.g. `?b = String`
//! resolved by `Convert[Int, String]`) are not erroneously generalized into the
//! function's scheme.

use std::collections::HashMap;

use crate::trait_registry::{freshen_type, PartialMatch, TraitRegistry};
use crate::typed_ast::{
    ResolvedBindingRef, ResolvedTraitMethodRef, TraitName, TypedExpr, TypedExprKind,
};
use crate::types::{Substitution, Type, TypeVarGen, TypeVarId};
use crate::unify::unify;

use super::checks::collect_type_var_bindings_strict;

/// One pending multi-parameter constraint discovered at a call site.
struct Entry {
    trait_name: TraitName,
    /// Trait type-var positions in declaration order. Each entry is the type
    /// observed at the call site for the corresponding trait type variable.
    positions: Vec<Type>,
}

/// Resolve all multi-parameter trait method calls within a fresh SCC.
///
/// Mutates `subst` to pin free positions whenever a unique candidate exists.
pub(super) fn resolve_multi_param_constraints(
    fn_bodies: &[Option<TypedExpr>],
    trait_registry: &TraitRegistry,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) {
    // 1. Collect entries.
    let mut entries: Vec<Entry> = Vec::new();
    for body in fn_bodies.iter().flatten() {
        collect_entries(body, trait_registry, subst, &mut entries);
    }
    if entries.is_empty() {
        return;
    }

    // 2. Fixed-point loop. Each pass tries to make progress on at least one
    //    entry. If no entry resolves, we stop.
    loop {
        let mut progressed = false;
        for entry in &entries {
            // Re-apply the current substitution to each position.
            let resolved: Vec<Type> =
                entry.positions.iter().map(|t| subst.apply(t)).collect();
            // If every position is fully concrete (no free vars), validation
            // will handle it. Skip — there's nothing to pin here.
            let any_var = resolved.iter().any(contains_type_var);
            if !any_var {
                continue;
            }
            match trait_registry.find_instance_multi_partial(&entry.trait_name, &resolved) {
                PartialMatch::Unique(inst) => {
                    // Freshen the instance's free type vars so we don't
                    // accidentally pollute the substitution with stale ids,
                    // then unify each position with the freshened target.
                    let mut var_map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
                    let fresh_targets: Vec<Type> = inst
                        .target_types
                        .iter()
                        .map(|t| freshen_type(t, &mut var_map, gen))
                        .collect();
                    let mut local_progress = false;
                    for (pos, target) in resolved.iter().zip(fresh_targets.iter()) {
                        if matches!(pos, Type::Var(_)) {
                            // Pinning a previously-free position counts as progress.
                            if unify(pos, target, subst).is_ok() {
                                local_progress = true;
                            }
                        } else {
                            // Concrete position — unification should already
                            // succeed (the partial match implied compatibility).
                            // If it doesn't, validation will catch it later.
                            let _ = unify(pos, target, subst);
                        }
                    }
                    if local_progress {
                        progressed = true;
                    }
                }
                PartialMatch::Multiple | PartialMatch::None_ => {
                    // Defer — leave for the next pass or validation.
                }
            }
        }
        if !progressed {
            break;
        }
    }
}

/// Walk a body and append one `Entry` per multi-parameter trait method call.
fn collect_entries(
    expr: &TypedExpr,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    out: &mut Vec<Entry>,
) {
    let mut work: Vec<&TypedExpr> = Vec::with_capacity(16);
    work.push(expr);
    while let Some(expr) = work.pop() {
        if let TypedExprKind::App { func, args } = &expr.kind {
            if let Some(ResolvedBindingRef::TraitMethod(ResolvedTraitMethodRef {
                trait_name, ..
            })) = typed_callee_resolved_ref(func)
            {
                if let Some(info) = trait_registry.lookup_trait(trait_name) {
                    if info.type_var_ids.len() > 1 {
                        // Find the named method (by name lookup).
                        let method_name = match typed_callee_resolved_ref(func) {
                            Some(ResolvedBindingRef::TraitMethod(ResolvedTraitMethodRef {
                                method_name,
                                ..
                            })) => method_name.as_str(),
                            _ => unreachable!(),
                        };
                        if let Some(method) =
                            info.methods.iter().find(|m| m.name == method_name)
                        {
                            // Collect bindings: trait_type_var_id -> Type.
                            let mut bindings: HashMap<TypeVarId, Type> = HashMap::new();
                            for ((_, pattern), arg) in
                                method.param_types.iter().zip(args.iter())
                            {
                                collect_type_var_bindings_strict(
                                    pattern,
                                    &subst.apply(&arg.ty),
                                    &mut bindings,
                                );
                            }
                            let ret_ty = subst.apply(&func.ty);
                            let actual_ret = match &ret_ty {
                                Type::Fn(_, ret) => ret.as_ref().clone(),
                                other => other.clone(),
                            };
                            collect_type_var_bindings_strict(
                                &method.return_type,
                                &actual_ret,
                                &mut bindings,
                            );
                            // Build positions in declaration order. If a trait
                            // type var didn't appear anywhere in this method,
                            // skip the entry — there's nothing to constrain.
                            let mut positions: Vec<Type> =
                                Vec::with_capacity(info.type_var_ids.len());
                            let mut all_present = true;
                            for tv_id in &info.type_var_ids {
                                if let Some(t) = bindings.get(tv_id) {
                                    positions.push(t.clone());
                                } else {
                                    all_present = false;
                                    break;
                                }
                            }
                            if all_present {
                                out.push(Entry {
                                    trait_name: trait_name.clone(),
                                    positions,
                                });
                            }
                        }
                    }
                }
            }
            work.push(func);
            for a in args {
                work.push(a);
            }
            continue;
        }
        // Generic recursion
        match &expr.kind {
            TypedExprKind::TypeApp { expr, .. } => work.push(expr),
            TypedExprKind::Lambda { body, .. } => work.push(body),
            TypedExprKind::If { cond, then_, else_ } => {
                work.push(cond);
                work.push(then_);
                work.push(else_);
            }
            TypedExprKind::Let { value, body, .. }
            | TypedExprKind::LetPattern { value, body, .. } => {
                work.push(value);
                if let Some(body) = body {
                    work.push(body);
                }
            }
            TypedExprKind::Do(exprs) => {
                for e in exprs {
                    work.push(e);
                }
            }
            TypedExprKind::Match { scrutinee, arms } => {
                work.push(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        work.push(guard);
                    }
                    work.push(&arm.body);
                }
            }
            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                work.push(lhs);
                work.push(rhs);
            }
            TypedExprKind::UnaryOp { operand, .. } => work.push(operand),
            TypedExprKind::FieldAccess { expr, .. } => work.push(expr),
            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::StructUpdate { base, fields, .. } => {
                work.push(base);
                for (_, e) in fields {
                    work.push(e);
                }
            }
            TypedExprKind::Tuple(elems)
            | TypedExprKind::Recur(elems)
            | TypedExprKind::VecLit(elems) => {
                for e in elems {
                    work.push(e);
                }
            }
            TypedExprKind::QuestionMark { expr, .. } => work.push(expr),
            TypedExprKind::App { .. } => unreachable!("handled above"),
            TypedExprKind::Lit(_) | TypedExprKind::Var(_) => {}
        }
    }
}

/// Mirror of the helper in `checks.rs` (kept private to that module).
fn typed_callee_resolved_ref(expr: &TypedExpr) -> Option<&ResolvedBindingRef> {
    match &expr.kind {
        TypedExprKind::Var(_) => expr.resolved_ref.as_ref(),
        TypedExprKind::TypeApp { expr: inner, .. } => expr
            .resolved_ref
            .as_ref()
            .or_else(|| typed_callee_resolved_ref(inner)),
        _ => expr.resolved_ref.as_ref(),
    }
}

/// True iff `ty` contains any free `Type::Var`.
fn contains_type_var(ty: &Type) -> bool {
    match ty {
        Type::Var(_) => true,
        Type::Fn(params, ret) => {
            params.iter().any(|(_, p)| contains_type_var(p)) || contains_type_var(ret)
        }
        Type::Named(_, args) => args.iter().any(contains_type_var),
        Type::App(ctor, args) => contains_type_var(ctor) || args.iter().any(contains_type_var),
        Type::Tuple(elems) => elems.iter().any(contains_type_var),
        Type::Own(inner) | Type::MaybeOwn(_, inner) => contains_type_var(inner),
        Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit | Type::FnHole => false,
    }
}
