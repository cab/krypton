// Trait-dictionary resolution and superclass projection. Methods here
// produce dict atoms (or `(Vec<LetBinding>, Atom)` pairs) for trait
// constraints at call sites — synthesizing `MakeDict`/`GetDict` simple
// expressions, navigating superclass parents to recover narrower dict
// references, and turning trait-method or constrained-fn references into
// closures that capture their dict args.

use rustc_hash::{FxHashMap, FxHashSet};

use krypton_typechecker::typed_ast::{QualifiedName, TraitName, TypedExpr};
use krypton_typechecker::types::{SchemeVarId, Type, TypeVarId};

use super::bind::{bind_instance_targets, bind_type_vars, ice_bind_conflict};
use super::ctx::{LetBinding, LowerCtx, SuperclassProjectionHop, SuperclassProjectionPlan};
use super::op_resolve::strip_own;
use super::util::{atom_expr_at, expr_at, simple_at, substitute_ir_type};
use super::LowerError;
use crate::Type as IrType;
use crate::{
    Atom, CanonicalRef, ExprKind, FnDef, FnId, LocalSymbolKey, ModulePath, SimpleExpr,
    SimpleExprKind, VarId,
};

impl<'a> LowerCtx<'a> {
    // -----------------------------------------------------------------------
    // Dict resolution
    // -----------------------------------------------------------------------

    /// Resolve a trait dictionary for a given trait and concrete type.
    /// Returns let-bindings and an atom referencing the dict value.
    pub(super) fn resolve_dict(
        &mut self,
        trait_name: &TraitName,
        tys: &[Type],
    ) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        const MAX_DICT_DEPTH: u32 = 64;
        if self.dict_depth >= MAX_DICT_DEPTH {
            let joined = tys
                .iter()
                .map(|t| format!("{t}"))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(LowerError::InternalError(format!(
                "dict resolution depth exceeded for {}[{joined}]",
                trait_name.local_name
            )));
        }
        self.dict_depth += 1;
        let result = self.resolve_dict_inner(trait_name, tys);
        self.dict_depth -= 1;
        result
    }

    pub(super) fn resolve_dict_inner(
        &mut self,
        trait_name: &TraitName,
        tys: &[Type],
    ) -> Result<(Vec<LetBinding>, Atom), LowerError> {
        let stripped: Vec<Type> = tys.iter().map(|t| strip_own(t).clone()).collect();

        // Strategy 1: Type variable — look up dict param
        if let Some(var_id) = self.lookup_dict_var(trait_name, &stripped) {
            return Ok((vec![], Atom::Var(var_id)));
        }

        // Strategy 1.5: Superclass projection. If an in-scope dict param holds
        // a descendant trait whose transitive superclass closure includes the
        // requested trait (at matching target type vars), project the stored
        // slot. Transitive hops are emitted as a chain of ProjectDictField
        // nodes — one Getfield per hop at runtime.
        if let Some(result) = self.try_project_superclass_dict(trait_name, &stripped)? {
            return Ok(result);
        }

        // Strategy 2: Check for parameterized instance with where-constraints
        if let Some(result) = self.try_resolve_parameterized_dict(trait_name, &stripped)? {
            return Ok(result);
        }

        // Strategy 3: Concrete singleton dict
        let var = self.fresh_var();
        let ir_target_types: Vec<IrType> = stripped.iter().map(|t| t.clone().into()).collect();
        Ok((
            vec![LetBinding {
                bind: var,
                ty: IrType::Dict {
                    trait_name: trait_name.clone(),
                    target_types: ir_target_types.clone(),
                },
                value: simple_at(
                    (0, 0),
                    SimpleExprKind::GetDict {
                        instance_ref: self.instance_canonical_ref(trait_name, &stripped),
                        trait_name: trait_name.clone(),
                        target_types: ir_target_types,
                    },
                ),
            }],
            Atom::Var(var),
        ))
    }

    /// Strategy 1.5: If an in-scope dict param holds a descendant trait whose
    /// transitive superclass closure reaches `trait_name` at types that
    /// substitute to the requested `tys`, emit a chain of ProjectDictField
    /// reads to project the slot.
    ///
    /// Works for both single- and multi-parameter traits. Candidate selection
    /// substitutes the dict param's target vars through the descendant's
    /// stored superclass args and checks equality against the request. The
    /// field index at each hop is `position_of(next, cur.direct_superclasses)`,
    /// matching the dict-layout rule in `InstanceDef`. The projected dict's
    /// target types at each hop are derived by composing substitutions.
    pub(super) fn try_project_superclass_dict(
        &mut self,
        trait_name: &TraitName,
        tys: &[Type],
    ) -> Result<Option<(Vec<LetBinding>, Atom)>, LowerError> {
        // Projection only applies when every requested target is a type var —
        // concrete targets resolve through GetDict on the concrete singleton.
        let target_ids: Option<Vec<TypeVarId>> = tys
            .iter()
            .map(|t| match t {
                Type::Var(id) => Some(*id),
                _ => None,
            })
            .collect();
        let Some(target_ids) = target_ids else {
            return Ok(None);
        };

        // Cache hit (positive or negative). Lookup without allocating a key:
        // the inner map is keyed on `Vec<TypeVarId>` which borrows as
        // `[TypeVarId]`. Split-borrow the cache and `next_var` so emission
        // can read the plan in place and allocate VarIds without a clone.
        let cached = self
            .superclass_projection_cache
            .get(trait_name)
            .and_then(|inner| inner.get(target_ids.as_slice()));
        if let Some(slot) = cached {
            let Some(plan) = slot else { return Ok(None) };
            return Ok(Some(Self::emit_from_plan(&mut self.next_var, plan)));
        }

        // Cache miss — run the analysis once and memoize. `dict_params` and
        // the `link_view` data we read here are both function-local invariants
        // (see invalidation in `lower_fn` and the save/restore around
        // `lower_lambda`), so a single plan serves every repeat call.
        let plan = self.plan_superclass_projection(trait_name, &target_ids)?;
        let result = plan
            .as_ref()
            .map(|p| Self::emit_from_plan(&mut self.next_var, p));
        self.superclass_projection_cache
            .entry(trait_name.clone())
            .or_default()
            .insert(target_ids, plan);
        Ok(result)
    }

    /// Analysis half of the superclass projection: picks the best in-scope
    /// dict param and the hop chain that reaches `trait_name` at the
    /// requested targets. Returns `None` if no in-scope dict has `trait_name`
    /// in its transitive superclass closure at the requested targets. Does
    /// not allocate `VarId`s — emission happens in
    /// `emit_superclass_projection`.
    pub(super) fn plan_superclass_projection(
        &self,
        trait_name: &TraitName,
        target_ids: &[TypeVarId],
    ) -> Result<Option<SuperclassProjectionPlan>, LowerError> {
        let target_ir_expected: Vec<IrType> = target_ids.iter().copied().map(IrType::Var).collect();

        // Find the best in-scope descendant: shortest closure distance to
        // `trait_name` at the correctly-substituted targets, tie-break by
        // trait name for determinism.
        let mut best: Option<(TraitName, Vec<TypeVarId>, VarId, usize)> = None;
        for ((d_trait, d_tvs), &var_id) in &self.dict_params {
            if d_trait == trait_name && d_tvs.as_slice() == target_ids {
                continue; // Exact match handled by Strategy 1.
            }
            let Some(closure) = self.link_view.trait_superclass_closure(d_trait) else {
                continue;
            };
            let Some(d_params) = self.link_view.trait_type_var_ids(d_trait) else {
                continue;
            };
            if d_params.len() != d_tvs.len() {
                continue;
            }
            let d_tvs_ir: Vec<IrType> = d_tvs.iter().copied().map(IrType::Var).collect();
            let hop_distance = closure.iter().position(|(a, a_args)| {
                if a != trait_name {
                    return false;
                }
                // Closure entries live in the trait's canonical TcType namespace
                // and are bounded per-trait (small, typically 1-3 entries); convert
                // to IrType at comparison time rather than mirroring the whole map.
                let substituted: Vec<IrType> = a_args
                    .iter()
                    .map(|t| substitute_ir_type(&IrType::from(t.clone()), d_params, &d_tvs_ir))
                    .collect();
                substituted == target_ir_expected
            });
            let Some(hop_distance) = hop_distance else {
                continue;
            };
            let better = match &best {
                Some((cur_trait, _, _, cur_dist)) => {
                    hop_distance < *cur_dist
                        || (hop_distance == *cur_dist && d_trait.local_name < cur_trait.local_name)
                }
                None => true,
            };
            if better {
                best = Some((d_trait.clone(), d_tvs.clone(), var_id, hop_distance));
            }
        }
        let Some((descendant_trait, descendant_tvs, dict_var, _)) = best else {
            return Ok(None);
        };

        // Build the hop path descendant → ... → trait_name through direct
        // superclasses. BFS parent pointers so we emit one Getfield per hop.
        let Some(path) = self.path_through_superclasses(&descendant_trait, trait_name) else {
            return Ok(None);
        };

        // Walk the path, composing substitutions. At each hop, look up the
        // direct-superclass entry for `next_trait`, substitute the current
        // trait's type params with `cur_args`, and use the result as the
        // next hop's target types.
        let mut hops: Vec<SuperclassProjectionHop> = Vec::with_capacity(path.len());
        let mut cur_trait = descendant_trait;
        let mut cur_args: Vec<IrType> = descendant_tvs.iter().copied().map(IrType::Var).collect();
        for next_trait in &path {
            let (field_index, stored_next_args) = {
                let direct = self
                    .link_view
                    .trait_direct_superclasses(&cur_trait)
                    .unwrap_or(&[]);
                let Some(idx) = direct.iter().position(|(t, _)| t == next_trait) else {
                    return Err(LowerError::InternalError(format!(
                        "ICE: superclass path hop {} → {} not in direct superclasses",
                        cur_trait.local_name, next_trait.local_name
                    )));
                };
                let stored: Vec<IrType> = direct[idx].1.iter().cloned().map(IrType::from).collect();
                (idx, stored)
            };
            let cur_params: Vec<TypeVarId> = match self.link_view.trait_type_var_ids(&cur_trait) {
                Some(p) => p.to_vec(),
                None => {
                    return Err(LowerError::InternalError(format!(
                        "ICE: no type_var_ids for trait {}",
                        cur_trait.local_name
                    )));
                }
            };
            if cur_params.len() != cur_args.len() {
                return Err(LowerError::InternalError(format!(
                    "ICE: trait {} has {} type params but {} args supplied at projection hop",
                    cur_trait.local_name,
                    cur_params.len(),
                    cur_args.len()
                )));
            }
            let next_args: Vec<IrType> = stored_next_args
                .iter()
                .map(|t| substitute_ir_type(t, &cur_params, &cur_args))
                .collect();
            hops.push(SuperclassProjectionHop {
                field_index,
                next_trait: next_trait.clone(),
                next_args: next_args.clone(),
            });
            cur_trait = next_trait.clone();
            cur_args = next_args;
        }

        Ok(Some(SuperclassProjectionPlan {
            start_var: dict_var,
            hops,
        }))
    }

    /// Emission half of the superclass projection: materializes one
    /// `ProjectDictField` let-binding per hop, allocating a fresh `VarId` at
    /// each step. Takes `&mut u32` rather than `&mut self` so the cache-hit
    /// path can split-borrow `next_var` from the cache without cloning the
    /// plan. The sequence of `VarId` allocations matches the pre-cache
    /// behavior one-for-one, keeping IR output byte-identical.
    pub(super) fn emit_from_plan(
        next_var: &mut u32,
        plan: &SuperclassProjectionPlan,
    ) -> (Vec<LetBinding>, Atom) {
        let mut bindings: Vec<LetBinding> = Vec::with_capacity(plan.hops.len());
        let mut cur_atom = Atom::Var(plan.start_var);
        for hop in &plan.hops {
            let projected_var = VarId(*next_var);
            *next_var += 1;
            bindings.push(LetBinding {
                bind: projected_var,
                ty: IrType::Dict {
                    trait_name: hop.next_trait.clone(),
                    target_types: hop.next_args.clone(),
                },
                value: simple_at(
                    (0, 0),
                    SimpleExprKind::ProjectDictField {
                        dict: cur_atom,
                        field_index: hop.field_index,
                        result_trait: hop.next_trait.clone(),
                        result_target_types: hop.next_args.clone(),
                    },
                ),
            });
            cur_atom = Atom::Var(projected_var);
        }
        (bindings, cur_atom)
    }

    /// BFS through `trait_direct_superclasses` from `from` to `to`, returning
    /// the sequence of trait hops (exclusive of `from`, inclusive of `to`).
    pub(super) fn path_through_superclasses(
        &self,
        from: &TraitName,
        to: &TraitName,
    ) -> Option<Vec<TraitName>> {
        use std::collections::VecDeque;
        let mut queue: VecDeque<TraitName> = VecDeque::new();
        let mut parent: FxHashMap<TraitName, TraitName> = FxHashMap::default();
        let mut visited: FxHashSet<TraitName> = FxHashSet::default();
        visited.insert(from.clone());
        queue.push_back(from.clone());
        while let Some(cur) = queue.pop_front() {
            let Some(direct) = self.link_view.trait_direct_superclasses(&cur) else {
                continue;
            };
            for (sc, _) in direct {
                if visited.contains(sc) {
                    continue;
                }
                parent.insert(sc.clone(), cur.clone());
                if sc == to {
                    // Reconstruct path from `to` back to `from`.
                    let mut chain: Vec<TraitName> = vec![sc.clone()];
                    let mut p = cur.clone();
                    while p != *from {
                        chain.push(p.clone());
                        p = parent.get(&p)?.clone();
                    }
                    chain.reverse();
                    return Some(chain);
                }
                visited.insert(sc.clone());
                queue.push_back(sc.clone());
            }
        }
        None
    }

    /// Look up a dict param VarId for a type variable tuple.
    pub(super) fn lookup_dict_var(&self, trait_name: &TraitName, tys: &[Type]) -> Option<VarId> {
        // Only dispatch through a dict param if every position is a type var.
        let ids: Option<Vec<TypeVarId>> = tys
            .iter()
            .map(|t| match t {
                Type::Var(id) => Some(*id),
                _ => None,
            })
            .collect();
        let ids = ids?;
        // Exact match first
        if let Some(&var_id) = self.dict_params.get(&(trait_name.clone(), ids.clone())) {
            return Some(var_id);
        }
        // Single-match heuristic: fresh instantiation TypeVarIds may differ from
        // the enclosing constraint's. Sound when exactly one dict param exists
        // for this trait **at the requested arity** — we must not silently
        // match a `Display[a]` dict when looking up `Convert[a, b]`.
        let matches: Vec<_> = self
            .dict_params
            .iter()
            .filter(|((tn, tvs), _)| tn == trait_name && tvs.len() == tys.len())
            .collect();
        if matches.len() == 1 {
            debug_assert_eq!(
                matches[0].0 .1.len(),
                tys.len(),
                "lookup_dict_var: arity mismatch despite filter"
            );
            Some(*matches[0].1)
        } else {
            None
        }
    }

    /// Try to resolve a parameterized instance dict (e.g., Show[Option[a]] where a: Show).
    pub(super) fn try_resolve_parameterized_dict(
        &mut self,
        trait_name: &TraitName,
        tys: &[Type],
    ) -> Result<Option<(Vec<LetBinding>, Atom)>, LowerError> {
        // Find a matching instance with constraints, keeping the bindings
        let matching = self.param_instances.iter().find_map(|inst| {
            if &inst.trait_name != trait_name {
                return None;
            }
            let mut bindings = FxHashMap::default();
            if bind_instance_targets(&inst.target_types, tys, &mut bindings) {
                Some((inst.clone(), bindings))
            } else {
                None
            }
        });

        let Some((inst, type_bindings)) = matching else {
            return Ok(None);
        };

        // Resolve sub-dicts for each constraint. The stored targets are
        // IR-level types — substitute the descendant's type_bindings (lifted
        // to IR) and convert the result to TC-level Types for resolve_dict.
        // Substituting at the IR layer keeps a single substitution helper
        // instead of a parallel IR-walking converter.
        let ir_type_bindings: FxHashMap<TypeVarId, IrType> = type_bindings
            .iter()
            .map(|(k, v)| (*k, IrType::from(v.clone())))
            .collect();
        let mut all_bindings = vec![];
        let mut sub_dict_atoms = vec![];
        for (constraint_trait, constraint_targets) in &inst.constraints {
            let sub_tys: Vec<Type> = constraint_targets
                .iter()
                .map(|t| crate::substitute_over_bindings(t, &ir_type_bindings).into())
                .collect();
            let (bs, atom) = self.resolve_dict(constraint_trait, &sub_tys)?;
            all_bindings.extend(bs);
            sub_dict_atoms.push(atom);
        }

        let var = self.fresh_var();
        let ir_target_types: Vec<IrType> = tys.iter().map(|t| t.clone().into()).collect();
        all_bindings.push(LetBinding {
            bind: var,
            ty: IrType::Dict {
                trait_name: trait_name.clone(),
                target_types: ir_target_types.clone(),
            },
            value: simple_at(
                (0, 0),
                SimpleExprKind::MakeDict {
                    instance_ref: CanonicalRef {
                        module: ModulePath::new(inst.source_module.clone()),
                        symbol: LocalSymbolKey::Instance {
                            trait_name: inst.trait_name.local_name.clone(),
                            target_type: inst.target_type_name.clone(),
                        },
                    },
                    trait_name: trait_name.clone(),
                    target_types: ir_target_types,
                    sub_dicts: sub_dict_atoms,
                },
            ),
        });
        Ok(Some((all_bindings, Atom::Var(var))))
    }

    /// Resolve dict arguments for a call to a constrained function.
    /// Returns let-bindings and dict atom args to prepend.
    pub(super) fn resolve_call_dicts(
        &mut self,
        qn: &QualifiedName,
        args: &[TypedExpr],
        user_type_bindings: &[(SchemeVarId, Type)],
        callee_concrete_ty: Option<&Type>,
    ) -> Result<(Vec<LetBinding>, Vec<Atom>), LowerError> {
        let constraints = match self.fn_constraints.get(qn) {
            Some(c) if !c.is_empty() => c.clone(),
            _ => return Ok((vec![], vec![])),
        };

        // Get the function's type scheme to extract param type patterns
        let scheme = self.fn_schemes.get(qn).cloned();

        // Build type var bindings: seed with the user's explicit pairs, then
        // let `bind_type_vars` fill in the rest from the scheme/arg types.
        let mut type_bindings: FxHashMap<TypeVarId, Type> = FxHashMap::default();
        for (svid, ty) in user_type_bindings {
            type_bindings.insert(svid.as_type_var(), ty.clone());
        }

        if let Some(ref scheme) = scheme {
            // Bind from argument types matched against param patterns
            if let Type::Fn(ref param_patterns, _) = scheme.ty {
                for ((_, pattern), arg) in param_patterns.iter().zip(args.iter()) {
                    bind_type_vars(pattern, &arg.ty, &mut type_bindings)
                        .map_err(|bc| ice_bind_conflict("resolve_call_dicts param match", bc))?;
                }
            }

            // Also match the full scheme type (including return) against the
            // callee's concrete type if the caller supplied it. This covers
            // constraint type vars that only appear in the return position
            // (e.g. `fn f[a, b](x: a) -> b where Convert[a, b]`).
            if let Some(callee_ty) = callee_concrete_ty {
                let stripped = strip_own(callee_ty);
                bind_type_vars(&scheme.ty, stripped, &mut type_bindings)
                    .map_err(|bc| ice_bind_conflict("resolve_call_dicts callee scheme", bc))?;
            }
        }

        let mut all_bindings = vec![];
        let mut dict_atoms = vec![];

        for (trait_name, type_var_ids) in &constraints {
            let concrete_tys: Vec<Type> = type_var_ids
                .iter()
                .map(|id| type_bindings.get(id).cloned().unwrap_or(Type::Var(*id)))
                .collect();
            let (bs, atom) = self.resolve_dict(trait_name, &concrete_tys)?;
            all_bindings.extend(bs);
            dict_atoms.push(atom);
        }

        Ok((all_bindings, dict_atoms))
    }

    /// Resolve the dispatch type for a trait method from its concrete (fully-specialized) type.
    /// Matches the method's type patterns (params + return) against `concrete_method_ty`
    /// to bind the trait's type variable.
    /// Resolve the dispatch type for a trait method, returning the trait's dispatch type
    /// and full type var bindings (including method-level type vars).
    /// Matches the method's type patterns against the concrete expression type,
    /// with explicit type args as fallback for phantom type vars (trait type var
    /// not appearing in the method signature, e.g. `name() -> String` on `Test[e]`).
    pub(super) fn resolve_dispatch_type(
        &self,
        trait_name: &TraitName,
        method_name: &str,
        concrete_method_ty: &Type,
        user_type_bindings: &[(SchemeVarId, Type)],
    ) -> Result<Vec<Type>, LowerError> {
        let (dispatch_tys, _bindings) = self.resolve_dispatch_type_with_bindings(
            trait_name,
            method_name,
            concrete_method_ty,
            user_type_bindings,
        )?;
        Ok(dispatch_tys)
    }

    pub(super) fn resolve_dispatch_type_with_bindings(
        &self,
        trait_name: &TraitName,
        method_name: &str,
        concrete_method_ty: &Type,
        user_type_bindings: &[(SchemeVarId, Type)],
    ) -> Result<(Vec<Type>, FxHashMap<TypeVarId, Type>), LowerError> {
        let (type_var_ids, method_types) =
            self.trait_method_types.get(trait_name).ok_or_else(|| {
                LowerError::InternalError(format!(
                    "ICE: no trait_method_types for trait {}",
                    trait_name.local_name
                ))
            })?;
        let type_var_ids = type_var_ids.clone();

        let (param_patterns, ret_pattern) = method_types.get(method_name).ok_or_else(|| {
            LowerError::InternalError(format!(
                "ICE: no method type patterns for {}.{}",
                trait_name.local_name, method_name
            ))
        })?;

        // Seed bindings from the user's explicit scheme-var → type pairs.
        // The typechecker already resolved which scheme vars the user pinned;
        // those land on their vars by id (including phantom trait vars that
        // don't appear in the method signature).
        let mut bindings: FxHashMap<TypeVarId, Type> = FxHashMap::default();
        for (svid, ty) in user_type_bindings {
            bindings.insert(svid.as_type_var(), ty.clone());
        }

        // Fill in the remaining vars by matching the method signature against
        // the concrete typechecker-produced type. `bind_type_vars` checks
        // existing bindings for consistency and only inserts when missing, so
        // user pins are preserved.
        let stripped_params: Vec<Type> = param_patterns.iter().map(|(_, t)| t.clone()).collect();
        let pattern_fn_ty = Type::fn_consuming(stripped_params, ret_pattern.clone());
        let concrete = strip_own(concrete_method_ty);
        let matched = bind_type_vars(&pattern_fn_ty, concrete, &mut bindings)
            .map_err(|bc| ice_bind_conflict("resolve_dispatch_type method signature", bc))?;

        // For zero-arg methods the concrete type is usually just the return
        // type — `Fn([], ret)` didn't match above, so match `ret_pattern`
        // directly. When the concrete *is* `Fn([], ret)` the first call
        // already bound everything; retrying against `ret_pattern` would
        // pair the return var with the full `Fn([], …)`, producing a
        // spurious conflict on any var that appears in both positions.
        if !matched && param_patterns.is_empty() {
            bind_type_vars(ret_pattern, concrete, &mut bindings)
                .map_err(|bc| ice_bind_conflict("resolve_dispatch_type zero-arg return", bc))?;
        }

        let dispatch_tys: Vec<Type> = type_var_ids
            .iter()
            .map(|tv| {
                bindings.get(tv).cloned().ok_or_else(|| {
                    LowerError::InternalError(format!(
                        "ICE: could not resolve dispatch type var for {}.{}",
                        trait_name.local_name, method_name
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok((dispatch_tys, bindings))
    }

    /// Lower a constrained function reference used as a value (not directly called).
    /// Creates a wrapper function that captures resolved dicts and forwards to the original fn.
    pub(super) fn lower_constrained_fn_as_value(
        &mut self,
        qn: &QualifiedName,
        fn_id: FnId,
        constraints: &[(TraitName, Vec<TypeVarId>)],
        user_type_bindings: &[(SchemeVarId, Type)],
        expr_ty: &Type,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // Seed with user-supplied pairs, then match the scheme against the
        // expression's concrete type for the remaining vars.
        let mut type_bindings: FxHashMap<TypeVarId, Type> = FxHashMap::default();
        for (svid, ty) in user_type_bindings {
            type_bindings.insert(svid.as_type_var(), ty.clone());
        }

        if let Some(scheme) = self.fn_schemes.get(qn).cloned() {
            let concrete = strip_own(expr_ty);
            bind_type_vars(&scheme.ty, concrete, &mut type_bindings)
                .map_err(|bc| ice_bind_conflict("lower_constrained_fn_as_value", bc))?;
        }

        // Resolve dicts for each constraint
        let mut all_bindings = vec![];
        let mut dict_atoms = vec![];
        for (trait_name, type_var_ids) in constraints {
            let concrete_tys: Vec<Type> = type_var_ids
                .iter()
                .map(|id| type_bindings.get(id).cloned().unwrap_or(Type::Var(*id)))
                .collect();
            let (bs, atom) = self.resolve_dict(trait_name, &concrete_tys)?;
            all_bindings.extend(bs);
            dict_atoms.push(atom);
        }

        // Extract user param types from expr_ty
        let unwrapped = strip_own(expr_ty);
        let (user_param_types, return_type): (Vec<Type>, Type) = match unwrapped {
            Type::Fn(params, ret) => (
                params.iter().map(|(_, t)| t.clone()).collect(),
                ret.as_ref().clone(),
            ),
            other => (vec![], other.clone()),
        };

        // Allocate wrapper function
        let wrapper_fn_id = self.fresh_fn();
        let wrapper_name = format!("fn_ref${}", wrapper_fn_id.0);

        // Dict capture params
        let mut dict_capture_vars = vec![];
        let mut lifted_params = vec![];
        for (trait_name, type_var_ids) in constraints {
            let var = self.fresh_var();
            dict_capture_vars.push(var);
            // Dict IR type carries the full tuple of concrete target types.
            // For each trait type parameter, resolve it through the current
            // bindings, falling back to its fresh TypeVarId if unbound.
            if type_var_ids.is_empty() {
                return Err(LowerError::InternalError(format!(
                    "constraint {} has empty type-var tuple during dict capture",
                    trait_name.local_name
                )));
            }
            let concrete_tys: Vec<IrType> = type_var_ids
                .iter()
                .map(|id| {
                    type_bindings
                        .get(id)
                        .cloned()
                        .unwrap_or(Type::Var(*id))
                        .into()
                })
                .collect();
            lifted_params.push((
                var,
                IrType::Dict {
                    trait_name: trait_name.clone(),
                    target_types: concrete_tys,
                },
            ));
        }

        // User params
        let mut user_param_vars = vec![];
        for ty in &user_param_types {
            let var = self.fresh_var();
            user_param_vars.push(var);
            lifted_params.push((var, ty.clone().into()));
        }

        // Build body: Call fn_id(dict_captures..., user_params...)
        let mut call_args: Vec<Atom> = dict_capture_vars.iter().map(|v| Atom::Var(*v)).collect();
        for var in &user_param_vars {
            call_args.push(Atom::Var(*var));
        }

        let result_var = self.fresh_var();
        let body = expr_at(
            (0, 0),
            return_type.clone().into(),
            ExprKind::Let {
                bind: result_var,
                ty: return_type.clone().into(),
                value: simple_at(
                    (0, 0),
                    SimpleExprKind::Call {
                        func: fn_id,
                        args: call_args,
                    },
                ),
                body: Box::new(atom_expr_at(
                    (0, 0),
                    return_type.clone().into(),
                    Atom::Var(result_var),
                )),
            },
        );

        // Push lifted FnDef
        self.lifted_fns.push(FnDef {
            id: wrapper_fn_id,
            name: wrapper_name.clone(),
            exported_symbol: wrapper_name.clone(),
            params: lifted_params,
            return_type: return_type.into(),
            body,
        });
        self.insert_synthetic_fn_id(wrapper_name, wrapper_fn_id);

        // Return MakeClosure capturing the dicts
        Ok((
            all_bindings,
            simple_at(
                (0, 0),
                SimpleExprKind::MakeClosure {
                    func: wrapper_fn_id,
                    captures: dict_atoms,
                },
            ),
        ))
    }

    /// Lower a trait method reference used as a value (not directly called).
    /// Creates a wrapper function that captures the dict and forwards to the dispatch FnId.
    pub(super) fn lower_trait_method_as_value(
        &mut self,
        trait_name: &TraitName,
        method_name: &str,
        expr_ty: &Type,
        user_type_bindings: &[(SchemeVarId, Type)],
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // 1. Resolve the dispatch type(s) — multi-parameter traits return one
        //    type per trait type parameter.
        let dispatch_tys =
            self.resolve_dispatch_type(trait_name, method_name, expr_ty, user_type_bindings)?;
        if dispatch_tys.is_empty() {
            return Err(LowerError::InternalError(format!(
                "trait {} has zero type parameters at dispatch site",
                trait_name.local_name
            )));
        }

        // 2. Resolve the dict (using the full tuple for multi-param traits).
        let (dict_bindings, dict_atom) = self.resolve_dict(trait_name, &dispatch_tys)?;

        // 3. Extract user param types from expr_ty
        let unwrapped = strip_own(expr_ty);
        let (user_param_types, return_type): (Vec<Type>, Type) = match unwrapped {
            Type::Fn(params, ret) => (
                params.iter().map(|(_, t)| t.clone()).collect(),
                ret.as_ref().clone(),
            ),
            other => (vec![], other.clone()),
        };

        // 4. Allocate wrapper function
        let wrapper_fn_id = self.fresh_fn();
        let wrapper_name = format!("trait_ref${}", wrapper_fn_id.0);

        // Dict capture param
        let dict_capture_var = self.fresh_var();
        let dict_ty_ir = IrType::Dict {
            trait_name: trait_name.clone(),
            target_types: dispatch_tys.iter().map(|t| t.clone().into()).collect(),
        };

        // User params
        let mut user_param_vars = vec![];
        let mut lifted_params = vec![(dict_capture_var, dict_ty_ir)];
        for ty in &user_param_types {
            let var = self.fresh_var();
            user_param_vars.push(var);
            lifted_params.push((var, ty.clone().into()));
        }

        // 5. Build body: TraitCall trait_name.method_name(dict_capture_var, user_params...)
        let mut call_args = vec![Atom::Var(dict_capture_var)];
        for var in &user_param_vars {
            call_args.push(Atom::Var(*var));
        }

        let result_var = self.fresh_var();
        let body = expr_at(
            (0, 0),
            return_type.clone().into(),
            ExprKind::Let {
                bind: result_var,
                ty: return_type.clone().into(),
                value: simple_at(
                    (0, 0),
                    SimpleExprKind::TraitCall {
                        trait_name: trait_name.clone(),
                        method_name: method_name.to_string(),
                        args: call_args,
                    },
                ),
                body: Box::new(atom_expr_at(
                    (0, 0),
                    return_type.clone().into(),
                    Atom::Var(result_var),
                )),
            },
        );

        // 6. Push lifted FnDef
        self.lifted_fns.push(FnDef {
            id: wrapper_fn_id,
            name: wrapper_name.clone(),
            exported_symbol: wrapper_name.clone(),
            params: lifted_params,
            return_type: return_type.into(),
            body,
        });
        self.insert_synthetic_fn_id(wrapper_name, wrapper_fn_id);

        // 7. Return MakeClosure capturing the dict
        Ok((
            dict_bindings,
            simple_at(
                (0, 0),
                SimpleExprKind::MakeClosure {
                    func: wrapper_fn_id,
                    captures: vec![dict_atom],
                },
            ),
        ))
    }
}
