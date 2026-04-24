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

use rustc_hash::{FxHashMap, FxHashSet};

use crate::trait_registry::{freshen_type, PartialMatch, TraitRegistry};
use crate::typed_ast::{
    DeferredId, ResolvedBindingRef, ResolvedTraitMethodRef, TraitName, TypedExpr, TypedExprKind,
};
use crate::types::{ParamMode, Substitution, Type, TypeVarGen, TypeVarId};
use crate::unify::unify;
use crate::visit::{walk_app, TypedExprVisitor};

use super::checks::collect_type_var_bindings_strict;

/// One pending multi-parameter constraint discovered at a call site.
struct Entry {
    trait_name: TraitName,
    /// Trait type-var positions in declaration order. Each entry is the type
    /// observed at the call site for the corresponding trait type variable.
    positions: Vec<Type>,
    /// Index of the enclosing top-level function in the SCC's `fn_bodies`.
    /// Used to look up the set of declared type-parameter vars that must
    /// remain abstract — pinning them would monomorphize the enclosing
    /// polymorphic function and drop its declared `where` constraint.
    owning_fn: usize,
}

/// Resolve all multi-parameter trait method calls within a fresh SCC.
///
/// Mutates `subst` to pin free positions whenever a unique candidate exists.
pub(super) fn resolve_multi_param_constraints(
    fn_bodies: &[Option<TypedExpr>],
    protected_type_vars: &[FxHashSet<TypeVarId>],
    trait_registry: &TraitRegistry,
    subst: &mut Substitution,
    gen: &mut TypeVarGen,
) {
    // 1. Collect entries, tagging each with the index of the enclosing
    //    function so we can look up its declared type-parameter var set.
    let mut entries: Vec<Entry> = Vec::new();
    for (idx, body_opt) in fn_bodies.iter().enumerate() {
        if let Some(body) = body_opt {
            collect_entries(body, idx, trait_registry, subst, &mut entries);
        }
    }
    if entries.is_empty() {
        return;
    }

    // 2. Fixed-point loop. Each pass tries to make progress on at least one
    //    entry. If no entry resolves, we stop.
    loop {
        // Compute the "live" protected set for each function as the union
        // of `free_vars(subst.apply(Var(id)))` over every originally-declared
        // id. This captures the full equivalence class of each declared type
        // parameter, regardless of whether body inference left it as a bare
        // var (`fn_b → ?c2` via join_types) or unified it with a structural
        // type (`fn_b := Tuple([?c1, ?c2])` for fns returning tuples). In
        // either case, all the free vars belong semantically to the enclosing
        // fn's declared type params and must stay abstract.
        let live_protected: Vec<FxHashSet<TypeVarId>> = protected_type_vars
            .iter()
            .map(|original| {
                let mut out: FxHashSet<TypeVarId> = FxHashSet::default();
                for &id in original {
                    out.extend(super::free_vars(&subst.apply(&Type::Var(id))));
                }
                out
            })
            .collect();

        let mut progressed = false;
        for entry in &entries {
            // Re-apply the current substitution to each position.
            let resolved: Vec<Type> = entry.positions.iter().map(|t| subst.apply(t)).collect();
            // If every position is fully concrete (no free vars), validation
            // will handle it. Skip — there's nothing to pin here.
            let any_var = resolved.iter().any(contains_type_var);
            if !any_var {
                continue;
            }
            match trait_registry.find_instance_multi_partial(&entry.trait_name, &resolved) {
                PartialMatch::Unique(inst) => {
                    // If every free position is a type variable belonging to
                    // the enclosing function's declared type parameters, this
                    // is a forwarding constraint (e.g. `fun f[a, b](x: a) -> b
                    // where Convert[a, b] = convert(x)`). Pinning would
                    // monomorphize `f` and drop its declared `where` clause
                    // before generalization can preserve it. Skip entirely —
                    // the constraint will be dispatched at `f`'s caller.
                    let protected = live_protected
                        .get(entry.owning_fn)
                        .map(|s| s as &FxHashSet<TypeVarId>);
                    // "Protected" is a property of individual free vars, not
                    // positions. A free var is protected iff it belongs to
                    // the enclosing fn's declared type-parameter equivalence
                    // class (computed above, incl. structurally-unified
                    // members). We use two closures:
                    //   - `contains_protected_free`: position cannot be
                    //     pinned without polluting a protected var — even
                    //     one protected free var anywhere in the position
                    //     is enough to disqualify the entire unify call,
                    //     because `unify` walks structurally.
                    //   - `contains_unprotected_free`: position has at least
                    //     one var worth trying to pin.
                    let contains_protected_free = |t: &Type| {
                        super::free_vars(t)
                            .iter()
                            .any(|v| protected.map(|s| s.contains(v)).unwrap_or(false))
                    };
                    let contains_unprotected_free = |t: &Type| {
                        super::free_vars(t)
                            .iter()
                            .any(|v| !protected.map(|s| s.contains(v)).unwrap_or(false))
                    };
                    // If no position has an unprotected free var, there's
                    // nothing to pin without polluting forwarded
                    // constraints. Skip the entry entirely (also avoids
                    // the cost of freshening the instance).
                    let any_unprotected = resolved.iter().any(&contains_unprotected_free);
                    if !any_unprotected {
                        continue;
                    }

                    // Freshen the instance's free type vars so we don't
                    // accidentally pollute the substitution with stale ids,
                    // then unify each position with the freshened target.
                    let mut var_map: FxHashMap<TypeVarId, TypeVarId> = FxHashMap::default();
                    let fresh_targets: Vec<Type> = inst
                        .target_types
                        .iter()
                        .map(|t| freshen_type(t, &mut var_map, gen))
                        .collect();
                    let mut local_progress = false;
                    for (pos, target) in resolved.iter().zip(fresh_targets.iter()) {
                        if contains_protected_free(pos) {
                            // Has at least one protected var — unify would
                            // walk structurally and pollute that var.
                            // Leave the whole position abstract.
                            continue;
                        }
                        if matches!(pos, Type::Var(_)) {
                            // Pinning a previously-free position counts as progress.
                            if unify(pos, target, subst).is_ok() {
                                local_progress = true;
                            }
                        } else {
                            // Concrete (or structural-with-no-protected-frees)
                            // position — unification should already succeed
                            // (the partial match implied compatibility).
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
    owning_fn: usize,
    trait_registry: &TraitRegistry,
    subst: &Substitution,
    out: &mut Vec<Entry>,
) {
    let mut collector = EntryCollector {
        owning_fn,
        trait_registry,
        subst,
        out,
    };
    collector.visit_expr(expr);
}

struct EntryCollector<'a> {
    owning_fn: usize,
    trait_registry: &'a TraitRegistry,
    subst: &'a Substitution,
    out: &'a mut Vec<Entry>,
}

impl<'a> TypedExprVisitor for EntryCollector<'a> {
    type Result = ();

    fn visit_app(
        &mut self,
        func: &TypedExpr,
        args: &[TypedExpr],
        _param_modes: &[ParamMode],
        _deferred_id: Option<DeferredId>,
        _expr: &TypedExpr,
    ) {
        if let Some(ResolvedBindingRef::TraitMethod(ResolvedTraitMethodRef {
            trait_name,
            method_name,
        })) = typed_callee_resolved_ref(func)
        {
            if let Some(info) = self.trait_registry.lookup_trait(trait_name) {
                if info.type_var_ids.len() > 1 {
                    if let Some(method) =
                        info.methods.iter().find(|m| m.name == method_name.as_str())
                    {
                        // Collect bindings: trait_type_var_id -> Type.
                        let mut bindings: FxHashMap<TypeVarId, Type> = FxHashMap::default();
                        for ((_, pattern), arg) in method.param_types.iter().zip(args.iter()) {
                            collect_type_var_bindings_strict(
                                pattern,
                                &self.subst.apply(&arg.ty),
                                &mut bindings,
                            );
                        }
                        let ret_ty = self.subst.apply(&func.ty);
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
                        let mut positions: Vec<Type> = Vec::with_capacity(info.type_var_ids.len());
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
                            self.out.push(Entry {
                                trait_name: trait_name.clone(),
                                positions,
                                owning_fn: self.owning_fn,
                            });
                        }
                    }
                }
            }
        }
        walk_app(self, func, args);
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
        Type::Own(inner) | Type::Shape(inner) | Type::MaybeOwn(_, inner) => {
            contains_type_var(inner)
        }
        Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit | Type::FnHole => false,
    }
}
