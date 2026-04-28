// Scope, lookup, and auto-close emission methods. ID generation
// (`fresh_var`/`fresh_fn`), variable scoping (`push_var`/`pop_var`/
// `enter_scope`/`exit_scope`/`bind_resource`), name resolution
// (`lookup_var`/`lookup_callable`/`insert_fn_id`), type and instance
// canonical refs, struct/variant lookups, and the auto-close emission
// suite (`emit_close_calls`, `emit_shadow_close`, `resolve_close_bindings`,
// `emit_resolved_close_calls`, `wrap_tail_with_closes`,
// `resource_dict_ty`, `resource_type_name`).

use rustc_hash::FxHashMap;

use krypton_typechecker::overload::types_overlap;
use krypton_typechecker::typed_ast::{
    AutoCloseBinding, OverloadSignature, QualifiedName, ResolvedTypeRef, ResolvedVariantRef,
    ScopeId, TraitName,
};
use krypton_typechecker::types::Type;

use super::bind::bind_instance_targets;
use super::ctx::{CloseMode, LowerCtx, ResolvedClose, ScopeTrack};
use super::util::expr_at;
use super::LowerError;
use crate::Type as IrType;
use crate::{
    CanonicalRef, Expr, ExprKind, FinallyClose, FnId, LocalSymbolKey, ModulePath, SwitchBranch,
    VarId,
};

impl<'a> LowerCtx<'a> {
    pub(super) fn fresh_var(&mut self) -> VarId {
        let id = VarId(self.next_var);
        self.next_var += 1;
        id
    }

    pub(super) fn fresh_fn(&mut self) -> FnId {
        let id = FnId(self.next_fn);
        self.next_fn += 1;
        id
    }

    /// Build a CanonicalRef for a type from its ResolvedTypeRef.
    pub(super) fn type_canonical_ref(&self, type_ref: &ResolvedTypeRef) -> CanonicalRef {
        CanonicalRef {
            module: ModulePath::new(type_ref.qualified_name.module_path.clone()),
            symbol: LocalSymbolKey::Type(type_ref.qualified_name.local_name.clone()),
        }
    }

    /// Build a CanonicalRef for a type from its bare local name,
    /// looking up the defining module from sum_variants/struct_fields.
    pub(super) fn type_canonical_ref_for_name(&self, local_name: &str) -> CanonicalRef {
        // Try sum_variants
        for variant_ref in self.sum_variants.keys() {
            if variant_ref.type_ref.qualified_name.local_name == local_name {
                return self.type_canonical_ref(&variant_ref.type_ref);
            }
        }
        // Try struct_fields
        for type_ref in self.struct_fields.keys() {
            if type_ref.qualified_name.local_name == local_name {
                return self.type_canonical_ref(type_ref);
            }
        }
        panic!(
            "ICE: type '{}' not found in sum_variants or struct_fields",
            local_name
        )
    }

    /// Build a CanonicalRef for an instance from trait + type info.
    /// Resolve the CanonicalRef for an instance given a trait and concrete target type.
    /// First tries exact match by canonical type name, then structural match via
    /// bind_type_vars (for parameterized instances like `Convert[(a) -> Int]`).
    pub(super) fn instance_canonical_ref(
        &self,
        trait_name: &TraitName,
        target_types: &[Type],
    ) -> CanonicalRef {
        // Canonical names are computed position-by-position with a fresh
        // var_map per position. That matches the typechecker's canonical
        // form (see `InstanceDefInfo.target_type_name` in infer/mod.rs),
        // which joins `type_to_canonical_name(t)` over each position with
        // "$$" — each position independently renumbers type vars from 0.
        let canonical_name = target_types
            .iter()
            .map(|t| {
                let ir_type: IrType = t.clone().into();
                crate::canonical_type_name(&ir_type)
            })
            .collect::<Vec<_>>()
            .join("$$");

        // Fast path: exact match via pre-built index
        let key = (trait_name.local_name.clone(), canonical_name.clone());
        let matched = if let Some(&idx) = self.instance_exact_index.get(&key) {
            &self.all_instances[idx]
        } else {
            // Slow path: structural match for parameterized instances
            self.all_instances
                .iter()
                .filter(|info| info.trait_name == *trait_name)
                .find(|info| {
                    let mut bindings = FxHashMap::default();
                    bind_instance_targets(&info.target_types, target_types, &mut bindings)
                })
                .unwrap_or_else(|| {
                    panic!(
                        "ICE: no instance source for {}[{}] — \
                         all_instances should contain all local + imported instances",
                        trait_name.local_name, canonical_name
                    )
                })
        };

        CanonicalRef {
            module: ModulePath::new(matched.source_module.clone()),
            symbol: LocalSymbolKey::Instance {
                trait_name: trait_name.local_name.clone(),
                target_type: matched.target_type_name.clone(),
            },
        }
    }

    /// Introduce a binding into scope.
    ///
    /// For disposable bindings (`~T` where `T: Disposable`), callers must use
    /// [`bind_resource`] so the function-wide finally handler and the
    /// innermost scope tracker learn about the new slot.
    ///
    /// In addition to maintaining the name → VarId stack, `push_var` also
    /// updates any active scope tracker that has *already* resolved this
    /// name to point at the new VarId. This handles two cases uniformly:
    ///
    /// - **Same-scope same-type shadow** (`let h: ~H = …; let h: ~H = …`):
    ///   the second `bind_resource` reaches `push_var`, sees that some
    ///   outer tracker already has `h` resolved (from the first binding),
    ///   and updates it to the new VarId. The scope-exit `auto_close` then
    ///   targets the live binding rather than the already-shadow-closed one.
    ///
    /// - **Recur-join shadow of a fn param**: after `bind_resource` records
    ///   the param VarId in the fn scope's `resolved` map, the recur-join
    ///   setup calls `push_var` with the join var. That update flows into
    ///   `resolved`, so `exit_scope` closes the join var (which holds the
    ///   actual current resource after recur iterations).
    pub(super) fn push_var(&mut self, name: &str, id: VarId) {
        self.var_scope.entry(name.to_string()).or_default().push(id);
        for scope in self.scope_track_stack.iter_mut() {
            if scope.resolved.contains_key(name) {
                scope.resolved.insert(name.to_string(), id);
            }
        }
    }

    /// Introduce a disposable binding (`~T` where `T: Disposable`) into scope.
    /// Wraps `push_var` and additionally registers the binding with the
    /// innermost scope tracker that expects it (so the scope's exit path
    /// can emit an AutoClose) and with `fn_block_scoped_closes` so the
    /// function-wide exception handler pre-allocates the slot and unwinds
    /// correctly on panic.
    ///
    /// The `type_name` is the concrete target type of the resource (e.g.
    /// `"Handle"`), used both for dict lookup and for the exception table.
    pub(super) fn bind_resource(&mut self, name: &str, id: VarId, type_name: &str) {
        self.push_var(name, id);
        // Match the innermost scope entry that expects this (name, type)
        // pair. Matching on `type_name` too is essential: when a scope
        // shadows a resource binding with a *different* type (e.g.
        // `let h: ~H1 = …; let h: ~H2 = …`), the typechecker records only
        // the survivor in `scope_exits` (here: H2). The earlier H1 binding
        // is handled via `emit_shadow_close` at the shadow point and must
        // NOT claim the scope's `h` slot, or `exit_scope` would emit an
        // AutoClose using the wrong VarId.
        for scope in self.scope_track_stack.iter_mut().rev() {
            let matches = scope
                .expected
                .iter()
                .any(|(n, t)| n == name && t == type_name);
            if matches && !scope.resolved.contains_key(name) {
                scope.resolved.insert(name.to_string(), id);
                break;
            }
        }
        let resource_ty_tc: Type = self
            .var_types
            .get(&id)
            .cloned()
            .map(|t| match t {
                Type::Own(inner) => (*inner).clone(),
                other => other,
            })
            .unwrap_or_else(|| Type::Named(type_name.to_string(), vec![]));
        self.fn_block_scoped_closes.push(FinallyClose {
            resource_var: id,
            type_name: type_name.to_string(),
            resource_ty: resource_ty_tc.into(),
        });
    }

    /// Reconstruct the full resource type for a `Disposable` dict lookup.
    ///
    /// `AutoCloseBinding` carries only the resource's head type name (e.g.
    /// `"Box"`), which is insufficient for parameterized instances like
    /// `Disposable[Box[a]] where a: Disposable`: matching against such an
    /// instance requires the full `Box[Resource]`, not a bare `Box`. We
    /// therefore look up the variable's recorded type in `var_types` and
    /// strip the outer `Own` wrapper, falling back to the head-only form
    /// only if the variable has no recorded type (should not happen for a
    /// tracked resource binding).
    pub(super) fn resource_dict_ty(&self, var: VarId, head_name: &str) -> Type {
        match self.var_types.get(&var) {
            Some(Type::Own(inner)) => (**inner).clone(),
            Some(other) => other.clone(),
            None => Type::Named(head_name.to_string(), vec![]),
        }
    }

    /// Return the disposable type name if `ty` is `~T` and `T` has a
    /// `Disposable` instance; otherwise `None`.
    pub(super) fn resource_type_name(&self, ty: &Type) -> Option<String> {
        let inner = match ty {
            Type::Own(inner) => inner.as_ref(),
            _ => return None,
        };
        let name = match inner {
            Type::Named(n, _) => n.as_str(),
            _ => return None,
        };
        let disposable_trait = TraitName::core_disposable();
        let key = (disposable_trait.local_name.clone(), name.to_string());
        if self.instance_exact_index.contains_key(&key) {
            Some(name.to_string())
        } else {
            None
        }
    }

    /// Enter a new block scope identified by its stable `ScopeId`. If the
    /// typechecker recorded scope_exits for it, start tracking the expected
    /// bindings so push_var can capture their VarIds for us to emit close
    /// calls at exit. Synthetic scope nodes (no ScopeId) are no-ops.
    pub(super) fn enter_scope(&mut self, scope_id: Option<ScopeId>) {
        let Some(scope_id) = scope_id else { return };
        if let Some(bindings) = self.auto_close.scope_exits.get(&scope_id) {
            let expected: Vec<(String, String)> = bindings
                .iter()
                .map(|b| (b.name.clone(), b.type_name.clone()))
                .collect();
            self.scope_track_stack.push(ScopeTrack {
                scope_id,
                expected,
                resolved: FxHashMap::default(),
            });
        }
    }

    /// Exit the block scope identified by `scope_id`. If the scope was
    /// tracked, wrap `body`'s tail positions with close+null calls for each
    /// resolved binding and register them in `fn_block_scoped_closes` for
    /// the function-wide finally handler.
    pub(super) fn exit_scope(&mut self, scope_id: Option<ScopeId>, body: Expr) -> Result<Expr, LowerError> {
        let Some(scope_id) = scope_id else {
            return Ok(body);
        };
        let Some(idx) = self
            .scope_track_stack
            .iter()
            .rposition(|s| s.scope_id == scope_id)
        else {
            return Ok(body);
        };
        let track = self.scope_track_stack.remove(idx);

        // Build resolved closes in the typechecker's LIFO order (reverse of
        // declaration). emit_resolved_close_calls processes in reverse, so
        // the last-pushed binding (first-declared) becomes the outermost let
        // — closes run innermost-first (LIFO).
        let trait_name = TraitName::core_disposable();
        let mut resolved: Vec<ResolvedClose> = Vec::new();
        for (name, type_name) in &track.expected {
            let Some(&var_id) = track.resolved.get(name) else {
                // The expected binding was never actually bound (e.g. the
                // control flow that introduces it was dead). Skip.
                continue;
            };
            let dict_ty = self.resource_dict_ty(var_id, type_name);
            let (dict_bindings, dict_atom) =
                self.resolve_dict(&trait_name, std::slice::from_ref(&dict_ty))?;
            resolved.push(ResolvedClose {
                trait_name: trait_name.clone(),
                binding_var: var_id,
                type_name: type_name.clone(),
                dict_bindings,
                dict_atom,
            });
        }
        if resolved.is_empty() {
            return Ok(body);
        }
        self.wrap_tail_with_closes(body, &resolved, CloseMode::NullSlot)
    }

    pub(super) fn pop_var(&mut self, name: &str) {
        if let Some(stack) = self.var_scope.get_mut(name) {
            stack.pop();
            if stack.is_empty() {
                self.var_scope.remove(name);
            }
        }
    }

    pub(super) fn lookup_var(&self, name: &str) -> Option<VarId> {
        self.var_scope.get(name).and_then(|s| s.last().copied())
    }

    /// Resolve a qualified callable ref to an FnId, using `sig` to pick
    /// among overloads. Single-candidate groups resolve without consulting
    /// `sig`. Multi-candidate groups require `sig` — an absent signature on
    /// a multi-candidate group is an ICE because the typechecker must
    /// publish `OverloadSignature` on `ResolvedCallableRef` whenever it
    /// chose among overloads.
    pub(super) fn lookup_callable(&self, qn: &QualifiedName, sig: Option<&OverloadSignature>) -> Option<FnId> {
        let candidates = self.callable_ids.get(qn)?;
        if candidates.len() == 1 {
            return Some(candidates[0].1);
        }
        let sig = sig.unwrap_or_else(|| {
            panic!(
                "ICE: callable `{}` has {} overload candidates but resolver provided no signature",
                qn.local_name,
                candidates.len()
            )
        });
        for (stored_params, fn_id) in candidates {
            if types_overlap(stored_params, &sig.param_types) {
                return Some(*fn_id);
            }
        }
        panic!(
            "ICE: typechecker/IR disagree on overload dispatch for `{}`: \
             no candidate matches signature {:?}; stored = {:?}",
            qn.local_name,
            sig.param_types,
            candidates.iter().map(|(p, _)| p).collect::<Vec<_>>(),
        );
    }

    /// Insert an FnId into `fn_ids` (by name) and `callable_ids` (by
    /// qualified name). `sig_key` is the canonical parameter-type list used
    /// to disambiguate overloads. Singletons (externs, intrinsics, lifted
    /// synthetics) pass an empty vec.
    pub(super) fn insert_fn_id(&mut self, name: String, qn: QualifiedName, sig_key: Vec<Type>, fn_id: FnId) {
        self.fn_ids
            .entry(name)
            .or_default()
            .push((sig_key.clone(), fn_id));
        self.callable_ids
            .entry(qn)
            .or_default()
            .push((sig_key, fn_id));
    }

    /// Insert a synthetic FnId under a unique generated name (lifted
    /// lambdas, constructor wrappers, fn-ref wrappers, trait-ref wrappers).
    /// The name is guaranteed unique by the lifting scheme so there's no
    /// overload group to disambiguate.
    pub(super) fn insert_synthetic_fn_id(&mut self, name: String, fn_id: FnId) {
        self.fn_ids
            .entry(name)
            .or_default()
            .push((Vec::new(), fn_id));
    }

    /// Emit close() calls for a list of AutoCloseBindings, wrapping `inner`.
    /// Resolves variable names and dicts from current scope.
    ///
    /// `mode` determines whether each emitted AutoClose nulls its resource
    /// slot (block-scoped normal-path exits that coexist with the fn-wide
    /// exception handler) or keeps it (recur back-edges, early returns).
    pub(super) fn emit_close_calls(
        &mut self,
        bindings: &[AutoCloseBinding],
        inner: Expr,
        mode: CloseMode,
    ) -> Result<Expr, LowerError> {
        let resolved = self.resolve_close_bindings(bindings)?;
        self.emit_resolved_close_calls(&resolved, inner, mode)
    }

    /// Emit a close call for a shadowed binding, wrapping `body`. Shadowed
    /// bindings are always nulled so the fn-wide finally handler skips the
    /// now-dead slot — this is what fixes the "two `let x = r` in one scope
    /// double-closes on exception" bug (#1 in the architecture cleanup).
    pub(super) fn emit_shadow_close(
        &mut self,
        binding: &AutoCloseBinding,
        old_var: VarId,
        body: Expr,
    ) -> Result<Expr, LowerError> {
        let dict_ty = self.resource_dict_ty(old_var, &binding.type_name);
        let trait_name = TraitName::core_disposable();
        let (dict_bindings, dict_atom) =
            self.resolve_dict(&trait_name, std::slice::from_ref(&dict_ty))?;
        let span = body.span;
        let ty = body.ty.clone();
        let close_expr = expr_at(
            span,
            ty,
            ExprKind::AutoClose {
                resource: old_var,
                dict: dict_atom,
                type_name: binding.type_name.clone(),
                null_slot: true,
                body: Box::new(body),
            },
        );
        Ok(Self::wrap_bindings(dict_bindings, close_expr))
    }

    /// Pre-resolve AutoCloseBindings to VarIds and dict info.
    /// Resolves variable names via the current var_scope.
    pub(super) fn resolve_close_bindings(
        &mut self,
        bindings: &[AutoCloseBinding],
    ) -> Result<Vec<ResolvedClose>, LowerError> {
        let trait_name = TraitName::core_disposable();
        let mut resolved = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let binding_var = self.lookup_var(&binding.name).ok_or_else(|| {
                LowerError::InternalError(format!(
                    "auto-close: variable '{}' not in scope",
                    binding.name
                ))
            })?;
            let dict_ty = self.resource_dict_ty(binding_var, &binding.type_name);
            let (dict_bindings, dict_atom) =
                self.resolve_dict(&trait_name, std::slice::from_ref(&dict_ty))?;
            resolved.push(ResolvedClose {
                trait_name: trait_name.clone(),
                binding_var,
                type_name: binding.type_name.clone(),
                dict_bindings,
                dict_atom,
            });
        }
        Ok(resolved)
    }

    /// Emit close calls from pre-resolved info, wrapping `inner`. Each close
    /// becomes one `ExprKind::AutoClose` IR node, so cleanup is first-class
    /// in the IR. `mode` selects whether to null the resource slot after
    /// each close (see `CloseMode`).
    ///
    /// Dict bindings (from `resolve_dict`) are emitted as outer `Let`s via
    /// `wrap_bindings` so the dict atom is in scope when the AutoClose node
    /// reads it.
    pub(super) fn emit_resolved_close_calls(
        &mut self,
        resolved: &[ResolvedClose],
        inner: Expr,
        mode: CloseMode,
    ) -> Result<Expr, LowerError> {
        let mut result = inner;
        // Process in reverse: the first binding becomes the outermost
        // AutoClose, so it runs (closes) first — LIFO declaration order.
        for rc in resolved.iter().rev() {
            let span = result.span;
            let ty = result.ty.clone();
            let close_expr = expr_at(
                span,
                ty,
                ExprKind::AutoClose {
                    resource: rc.binding_var,
                    dict: rc.dict_atom.clone(),
                    type_name: rc.type_name.clone(),
                    null_slot: mode.null_slot(),
                    body: Box::new(result),
                },
            );
            result = Self::wrap_bindings(rc.dict_bindings.clone(), close_expr);
        }
        Ok(result)
    }

    /// Walk tail positions of an expression and wrap each terminal Atom with
    /// close calls. `mode` is threaded unchanged through the recursive cases.
    pub(super) fn wrap_tail_with_closes(
        &mut self,
        expr: Expr,
        resolved: &[ResolvedClose],
        mode: CloseMode,
    ) -> Result<Expr, LowerError> {
        match expr.kind {
            ExprKind::Atom(_) => self.emit_resolved_close_calls(resolved, expr, mode),
            ExprKind::Let {
                bind,
                ty,
                value,
                body,
            } => {
                let new_body = self.wrap_tail_with_closes(*body, resolved, mode)?;
                Ok(expr_at(
                    value.span,
                    new_body.ty.clone(),
                    ExprKind::Let {
                        bind,
                        ty,
                        value,
                        body: Box::new(new_body),
                    },
                ))
            }
            ExprKind::LetRec {
                bindings: rec_bindings,
                body,
            } => {
                let new_body = self.wrap_tail_with_closes(*body, resolved, mode)?;
                Ok(expr_at(
                    new_body.span,
                    new_body.ty.clone(),
                    ExprKind::LetRec {
                        bindings: rec_bindings,
                        body: Box::new(new_body),
                    },
                ))
            }
            ExprKind::LetJoin {
                name,
                params,
                join_body,
                body,
                is_recur,
            } => {
                let new_join_body = self.wrap_tail_with_closes(*join_body, resolved, mode)?;
                let new_body = self.wrap_tail_with_closes(*body, resolved, mode)?;
                Ok(expr_at(
                    new_body.span,
                    new_body.ty.clone(),
                    ExprKind::LetJoin {
                        name,
                        params,
                        join_body: Box::new(new_join_body),
                        body: Box::new(new_body),
                        is_recur,
                    },
                ))
            }
            ExprKind::BoolSwitch {
                scrutinee,
                true_body,
                false_body,
            } => {
                let new_true = self.wrap_tail_with_closes(*true_body, resolved, mode)?;
                let new_false = self.wrap_tail_with_closes(*false_body, resolved, mode)?;
                Ok(expr_at(
                    new_true.span,
                    new_true.ty.clone(),
                    ExprKind::BoolSwitch {
                        scrutinee,
                        true_body: Box::new(new_true),
                        false_body: Box::new(new_false),
                    },
                ))
            }
            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                let new_branches = branches
                    .into_iter()
                    .map(|br| {
                        let new_body = self.wrap_tail_with_closes(br.body, resolved, mode)?;
                        Ok(SwitchBranch {
                            tag: br.tag,
                            bindings: br.bindings,
                            body: new_body,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                let new_default = match default {
                    Some(d) => Some(Box::new(self.wrap_tail_with_closes(*d, resolved, mode)?)),
                    None => None,
                };
                let ty = new_branches
                    .first()
                    .map(|b| b.body.ty.clone())
                    .or_else(|| new_default.as_ref().map(|d| d.ty.clone()))
                    .ok_or_else(|| {
                        LowerError::InternalError(
                            "switch expression has no arms and no default".to_string(),
                        )
                    })?;
                let span = new_branches
                    .first()
                    .map(|b| b.body.span)
                    .or_else(|| new_default.as_ref().map(|d| d.span))
                    .unwrap_or((0, 0));
                Ok(expr_at(
                    span,
                    ty,
                    ExprKind::Switch {
                        scrutinee,
                        branches: new_branches,
                        default: new_default,
                    },
                ))
            }
            ExprKind::AutoClose {
                resource,
                dict,
                type_name,
                null_slot,
                body,
            } => {
                // AutoClose body is a scope point — recurse into it only.
                // The close itself is not a tail position.
                let new_body = self.wrap_tail_with_closes(*body, resolved, mode)?;
                Ok(expr_at(
                    expr.span,
                    new_body.ty.clone(),
                    ExprKind::AutoClose {
                        resource,
                        dict,
                        type_name,
                        null_slot,
                        body: Box::new(new_body),
                    },
                ))
            }
            ExprKind::Jump { .. } => {
                // Jump targets handle their own cleanup
                Ok(expr)
            }
        }
    }

    /// Return the struct's fields with their declared field types substituted
    /// at the given concrete type (`scrut_ty`, which may be `Own(Named(..))`).
    ///
    /// `struct_fields` stores field types parameterized by the struct's
    /// declared type-parameter vars (allocated fresh by the IR lowering
    /// context for private types, or taken from the typechecker for exported
    /// types). A use-site like `match b: ~Box[Resource] { Box { value } => … }`
    /// projects `value` at `~Resource`, not the unsubstituted `~a` stored in
    /// `struct_fields`. Without this substitution, downstream dict lookups
    /// that recurse into the field type (e.g. `Disposable[a]` for the
    /// projected binding) would fail to resolve against concrete instances.
    pub(super) fn substituted_struct_fields(
        &self,
        type_ref: &ResolvedTypeRef,
        scrut_ty: &Type,
    ) -> Result<Vec<(String, Type)>, LowerError> {
        let fields = self
            .struct_fields
            .get(type_ref)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_ref.qualified_name.to_string()))?
            .clone();
        let params = match self.struct_type_params.get(type_ref) {
            Some(p) if !p.is_empty() => p.clone(),
            _ => return Ok(fields),
        };
        let args: Vec<Type> = match scrut_ty.strip_own() {
            Type::Named(_, args) => args,
            _ => return Ok(fields),
        };
        if args.len() != params.len() {
            return Ok(fields);
        }
        let mut subst = krypton_typechecker::types::Substitution::new();
        for (&id, ty) in params.iter().zip(args.iter()) {
            // Skip identity mappings — both sides now share the
            // typechecker's TypeVarId namespace after IR private-type
            // unification, so a struct accessed through its own type
            // params produces `Var(id) -> Var(id)` pairs that would
            // otherwise self-cycle in `Substitution::apply`.
            if let Type::Var(arg_id) = ty {
                if *arg_id == id {
                    continue;
                }
            }
            subst.insert(id, ty.clone());
        }
        Ok(fields
            .into_iter()
            .map(|(n, ty)| (n, subst.apply(&ty)))
            .collect())
    }

    pub(super) fn field_index(
        &self,
        type_ref: &ResolvedTypeRef,
        field_name: &str,
    ) -> Result<usize, LowerError> {
        let fields = self
            .struct_fields
            .get(type_ref)
            .ok_or_else(|| LowerError::UnresolvedStruct(type_ref.qualified_name.to_string()))?;
        fields
            .iter()
            .position(|(n, _)| n == field_name)
            .ok_or_else(|| {
                LowerError::UnresolvedField(
                    type_ref.qualified_name.to_string(),
                    field_name.to_string(),
                )
            })
    }

    pub(super) fn variant_info(
        &self,
        variant_ref: &ResolvedVariantRef,
    ) -> Result<(u32, Vec<Type>), LowerError> {
        self.sum_variants.get(variant_ref).cloned().ok_or_else(|| {
            LowerError::InternalError(format!(
                "unknown variant ref in lowering: {}.{}",
                variant_ref.type_ref.qualified_name, variant_ref.variant_name
            ))
        })
    }

    pub(super) fn fallback_type_ref(&self, type_name: &str) -> Option<ResolvedTypeRef> {
        self.struct_fields
            .keys()
            .find(|type_ref| type_ref.qualified_name.local_name == type_name)
            .cloned()
            .or_else(|| {
                self.sum_variants.keys().find_map(|variant_ref| {
                    (variant_ref.type_ref.qualified_name.local_name == type_name)
                        .then(|| variant_ref.type_ref.clone())
                })
            })
    }

    pub(super) fn fallback_variant_ref(&self, variant_name: &str) -> Option<ResolvedVariantRef> {
        self.sum_variants
            .keys()
            .find(|variant_ref| variant_ref.variant_name == variant_name)
            .cloned()
    }

    pub(super) fn resolved_type_ref_from_type(&self, ty: &Type) -> Option<ResolvedTypeRef> {
        match ty {
            Type::Named(name, _) => self.fallback_type_ref(name),
            Type::Own(inner) => self.resolved_type_ref_from_type(inner),
            _ => None,
        }
    }
}
