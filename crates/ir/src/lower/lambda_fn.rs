// Lambda lifting (closure conversion) and per-`TypedFnDecl` body
// lowering. `lower_lambda` captures free vars, lifts the body to a
// fresh `FnDef`, and produces a `MakeClosure` simple expression;
// `lower_fn` produces the top-level `FnDef` for a single decl, threading
// dict params and the function-wide auto-close handler.

use rustc_hash::{FxHashMap, FxHashSet};

use krypton_typechecker::typed_ast::{QualifiedName, TraitName, TypedExpr, TypedFnDecl};
use krypton_typechecker::types::{Type, TypeVarId};

use super::ctx::{LetBinding, LowerCtx, TraitConstraintList};
use super::util::{
    atom_expr_at, contains_question_mark, contains_recur, expr_at, free_vars,
    referenced_vars_in_expr, simple_at,
};
use super::LowerError;
use crate::Type as IrType;
use crate::{Atom, ExprKind, FnDef, FnId, SimpleExpr, SimpleExprKind, VarId};

impl<'a> LowerCtx<'a> {
    // -----------------------------------------------------------------------
    // Lambda lifting (closure conversion)
    // -----------------------------------------------------------------------

    pub(super) fn lower_lambda(
        &mut self,
        params: &[String],
        body: &TypedExpr,
        lambda_ty: &Type,
    ) -> Result<(Vec<LetBinding>, SimpleExpr), LowerError> {
        // 1. Extract param types and return type from the lambda's function type
        let unwrapped_ty = match lambda_ty {
            Type::Own(inner) => inner.as_ref(),
            other => other,
        };
        let (param_types, return_type): (Vec<Type>, Type) = match unwrapped_ty {
            Type::Fn(param_tys, ret_ty) => (
                param_tys.iter().map(|(_, t)| t.clone()).collect(),
                ret_ty.as_ref().clone(),
            ),
            other => {
                return Err(LowerError::InternalError(format!(
                    "lambda has non-function type: {other:?}"
                )))
            }
        };

        // 2. Compute free variables (names not bound by lambda params)
        let param_set: FxHashSet<String> = params.iter().cloned().collect();
        let fv_names = free_vars(body, &param_set);

        // 3. Resolve each free var to its current VarId
        let mut capture_params = vec![];
        let mut capture_atoms = vec![];
        for name in &fv_names {
            if let Some(var_id) = self.lookup_var(name) {
                capture_atoms.push(Atom::Var(var_id));
                capture_params.push((name.clone(), var_id));
            }
            // Names not in var_scope are top-level functions, not captures
        }

        // 4. Collect dict captures (sorted for deterministic output)
        let saved_dict_params = self.dict_params.clone();
        let mut dict_entries: Vec<_> = saved_dict_params.iter().collect();
        dict_entries.sort_by_key(|((trait_name, tv_ids), _)| (trait_name.clone(), tv_ids.clone()));
        let mut dict_capture_atoms = vec![];
        let mut dict_capture_keys: TraitConstraintList = vec![];
        for ((trait_name, type_var_ids), var_id) in &dict_entries {
            dict_capture_atoms.push(Atom::Var(**var_id));
            dict_capture_keys.push(((*trait_name).clone(), (*type_var_ids).clone()));
        }

        // 5. Allocate a fresh FnId for the lifted function
        let fn_id = self.fresh_fn();
        let name = format!("lambda${}", fn_id.0);

        // 6. Allocate new VarIds for the lifted fn's scope

        // Capture params — look up real types from var_types
        let mut capture_var_mappings = vec![];
        for (name, old_var_id) in &capture_params {
            let new_var = self.fresh_var();
            let ty = self
                .var_types
                .get(old_var_id)
                .cloned()
                .unwrap_or_else(|| Type::Var(self.type_var_gen.fresh()));
            capture_var_mappings.push((name.clone(), new_var, *old_var_id, ty));
        }

        // Dict capture params — allocate new VarIds
        let mut new_dict_params: FxHashMap<(TraitName, Vec<TypeVarId>), VarId> =
            FxHashMap::default();
        let mut dict_var_mappings: Vec<((TraitName, Vec<TypeVarId>), VarId)> = vec![];
        for key in &dict_capture_keys {
            let new_var = self.fresh_var();
            new_dict_params.insert(key.clone(), new_var);
            dict_var_mappings.push((key.clone(), new_var));
        }

        // Lambda params — allocate new VarIds
        let mut lambda_var_mappings = vec![];
        for (i, param_name) in params.iter().enumerate() {
            let new_var = self.fresh_var();
            let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                eprintln!(
                    "ICE: lambda param {} has no type (param_types len={})",
                    i,
                    param_types.len()
                );
                Type::Unit
            });
            lambda_var_mappings.push((param_name.clone(), new_var, ty));
        }

        // Push capture params and lambda params into var_scope
        for (name, new_var, _, ty) in &capture_var_mappings {
            self.var_types.insert(*new_var, ty.clone());
            self.push_var(name, *new_var);
        }
        for (name, new_var, ty) in &lambda_var_mappings {
            self.var_types.insert(*new_var, ty.clone());
            self.push_var(name, *new_var);
        }

        // Set dict_params to the captured dicts (mapped to new VarIds)
        let old_dict_params = std::mem::replace(&mut self.dict_params, new_dict_params);
        // Lambda dict scope is independent; drop the parent's projection
        // cache for the duration of the body and restore it on exit.
        let old_superclass_projection_cache = std::mem::take(&mut self.superclass_projection_cache);

        // Save and clear recur/early-return join points — these belong to the
        // enclosing function and must not leak into the lifted lambda.
        let old_recur_join = self.recur_join.take();
        let old_early_return_join = self.early_return_join.take();

        // Set up recur join point if the lambda body contains recur
        let has_recur = contains_recur(body);
        let recur_join_info = if has_recur {
            let join_name = self.fresh_var();
            let mut join_param_vars = vec![];
            for (param_name, _, ty) in &lambda_var_mappings {
                let join_var = self.fresh_var();
                self.var_types.insert(join_var, ty.clone());
                self.push_var(param_name, join_var);
                join_param_vars.push(join_var);
            }
            self.recur_join = Some((join_name, join_param_vars.clone()));
            Some((join_name, join_param_vars))
        } else {
            None
        };

        // Lower body
        let mut lowered_body = self.lower_expr(body)?;

        // Pop recur join params (they shadow lambda params)
        if recur_join_info.is_some() {
            for (name, _, _) in lambda_var_mappings.iter().rev() {
                self.pop_var(name);
            }
        }
        self.recur_join = None;

        // Pop all from var_scope, restore dict_params and join points
        for (name, _, _) in lambda_var_mappings.iter().rev() {
            self.pop_var(name);
        }
        for (name, _, _, _) in capture_var_mappings.iter().rev() {
            self.pop_var(name);
        }
        self.dict_params = old_dict_params;
        self.superclass_projection_cache = old_superclass_projection_cache;
        self.recur_join = old_recur_join;
        self.early_return_join = old_early_return_join;

        // 7. Filter dict captures to only those actually used in the body
        let used_vars = referenced_vars_in_expr(&lowered_body);
        let dict_var_mappings: Vec<_> = dict_var_mappings
            .into_iter()
            .filter(|(_, new_var)| used_vars.contains(new_var))
            .collect();
        let dict_capture_atoms: Vec<_> = dict_entries
            .iter()
            .filter(|((trait_name, tv_ids), _)| {
                dict_var_mappings
                    .iter()
                    .any(|((tn, tids), _)| tn == trait_name && tids == tv_ids)
            })
            .map(|(_, var_id)| Atom::Var(**var_id))
            .collect();

        // 8. Build the param list: captures ++ filtered dict captures ++ lambda params
        let mut lifted_params = vec![];
        for (_, new_var, _, ty) in &capture_var_mappings {
            lifted_params.push((*new_var, ty.clone().into()));
        }
        for (key, new_var) in &dict_var_mappings {
            // Dict carries the full tuple of trait type-param vars.
            if key.1.is_empty() {
                return Err(LowerError::InternalError(format!(
                    "dict capture for {} has empty type-var tuple",
                    key.0.local_name
                )));
            }
            let target_types: Vec<IrType> = key.1.iter().map(|id| IrType::Var(*id)).collect();
            lifted_params.push((
                *new_var,
                IrType::Dict {
                    trait_name: key.0.clone(),
                    target_types,
                },
            ));
        }
        for (_, new_var, ty) in &lambda_var_mappings {
            lifted_params.push((*new_var, ty.clone().into()));
        }

        // 9. Wrap body with recur join if needed
        if let Some((join_name, join_param_vars)) = recur_join_info {
            let join_params: Vec<(VarId, IrType)> = join_param_vars
                .iter()
                .enumerate()
                .map(|(i, &v)| {
                    let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                        panic!(
                            "ICE: recur join: param_types index {i} out of range (len={})",
                            param_types.len()
                        )
                    });
                    (v, ty.into())
                })
                .collect();
            let original_atoms: Vec<Atom> = lambda_var_mappings
                .iter()
                .map(|(_, new_var, _)| Atom::Var(*new_var))
                .collect();
            let body_span = lowered_body.span;
            lowered_body = expr_at(
                body_span,
                return_type.clone().into(),
                ExprKind::LetJoin {
                    name: join_name,
                    params: join_params,
                    join_body: Box::new(lowered_body),
                    body: Box::new(expr_at(
                        body_span,
                        return_type.clone().into(),
                        ExprKind::Jump {
                            target: join_name,
                            args: original_atoms,
                        },
                    )),
                    is_recur: true,
                },
            );
        }

        // 10. Push FnDef onto lifted_fns
        let lowered_body_span = lowered_body.span;
        self.lifted_fns.push(FnDef {
            id: fn_id,
            name: name.clone(),
            exported_symbol: name.clone(),
            params: lifted_params,
            return_type: return_type.into(),
            body: lowered_body,
        });

        // 10. Register in fn_ids for fn_names resolution
        self.insert_synthetic_fn_id(name, fn_id);

        // 11. Return MakeClosure with capture atoms
        let mut all_captures = capture_atoms;
        all_captures.extend(dict_capture_atoms);

        Ok((
            vec![],
            simple_at(
                lowered_body_span,
                SimpleExprKind::MakeClosure {
                    func: fn_id,
                    captures: all_captures,
                },
            ),
        ))
    }

    // -----------------------------------------------------------------------
    // Function lowering
    // -----------------------------------------------------------------------

    pub(super) fn lower_fn(
        &mut self,
        decl: &TypedFnDecl,
        fn_id: FnId,
        param_types: Vec<Type>,
        return_type: Type,
        exported_symbol: String,
    ) -> Result<FnDef, LowerError> {
        // Clear dict_params from any previous function
        self.dict_params.clear();
        self.superclass_projection_cache.clear();

        // Prepend dict params for constrained functions
        let mut params = vec![];
        let fn_qn = QualifiedName::new(self.module_path.clone(), decl.name.clone());
        if let Some(constraints) = self.fn_constraints.get(&fn_qn).cloned() {
            for (trait_name, type_var_ids) in &constraints {
                let var = self.fresh_var();
                self.dict_params
                    .insert((trait_name.clone(), type_var_ids.clone()), var);
                if type_var_ids.is_empty() {
                    return Err(LowerError::InternalError(format!(
                        "constraint {} on fn {} has empty type-var tuple",
                        trait_name.local_name, decl.name
                    )));
                }
                let target_types: Vec<IrType> =
                    type_var_ids.iter().map(|id| IrType::Var(*id)).collect();
                params.push((
                    var,
                    IrType::Dict {
                        trait_name: trait_name.clone(),
                        target_types,
                    },
                ));
            }
        }

        // Enter the fn-level scope BEFORE binding params, so disposable params
        // are recorded against this scope's tracker. The scope_id is the one
        // allocated by the typechecker's `scope_ids::stamp_functions`.
        let prev_block_closes = std::mem::take(&mut self.fn_block_scoped_closes);
        let prev_scope_stack = std::mem::take(&mut self.scope_track_stack);
        self.enter_scope(Some(decl.fn_scope_id));

        // Allocate VarIds for regular params. Disposable params route through
        // `bind_resource` so they enroll in the fn-level scope tracker AND
        // in `fn_block_scoped_closes` for the function-wide finally handler.
        let mut regular_param_vars = vec![];
        for (i, param) in decl.params.iter().enumerate() {
            let param_name = &param.name;
            let var = self.fresh_var();
            let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                eprintln!(
                    "ICE: fn param {} has no type (param_types len={})",
                    i,
                    param_types.len()
                );
                Type::Unit
            });
            self.var_types.insert(var, ty.clone());
            // Skip disposable registration for the `self` parameter of a
            // Disposable dispose impl: disposing the receiver from inside `dispose`
            // would either recurse infinitely or double-dispose on exception.
            // The typechecker already drops it from `scope_exits[fn_scope_id]`.
            let is_close_self = decl.close_self_type.is_some()
                && self.resource_type_name(&ty).as_deref() == decl.close_self_type.as_deref();
            if let Some(type_name) = self.resource_type_name(&ty) {
                if is_close_self {
                    self.push_var(param_name, var);
                } else {
                    self.bind_resource(param_name, var, &type_name);
                }
            } else {
                self.push_var(param_name, var);
            }
            params.push((var, ty.into()));
            regular_param_vars.push(var);
        }

        let has_recur = contains_recur(&decl.body);
        let has_qm = contains_question_mark(&decl.body);

        // Set up recur join point if needed
        let recur_join_info = if has_recur {
            let join_name = self.fresh_var();
            let mut join_param_vars = vec![];
            for (i, param) in decl.params.iter().enumerate() {
                let join_var = self.fresh_var();
                let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                    panic!(
                        "ICE: recur join: param_types index {i} out of range (len={})",
                        param_types.len()
                    )
                });
                self.var_types.insert(join_var, ty);
                // Shadow the original param with the join param
                self.push_var(&param.name, join_var);
                join_param_vars.push(join_var);
            }
            self.recur_join = Some((join_name, join_param_vars.clone()));
            Some((join_name, join_param_vars))
        } else {
            None
        };

        // Set up early return join point if needed
        let early_return_info = if has_qm {
            let join_name = self.fresh_var();
            let result_var = self.fresh_var();
            self.early_return_join = Some(join_name);
            Some((join_name, result_var))
        } else {
            None
        };

        let mut body = self.lower_expr(&decl.body)?;

        // Exit the fn-level scope: emits close+null calls in tail positions
        // for any resource params still live at function end (the typechecker
        // recorded them under `scope_exits[fn_scope_id]`).
        body = self.exit_scope(Some(decl.fn_scope_id), body)?;

        // `fn_block_scoped_closes` now holds the single, unified record of
        // all resource bindings introduced anywhere in this function (params
        // bound via `bind_resource` above, plus body locals bound via
        // `bind_resource` in `lower_let` / `lower_do_slice`). Codegen turns
        // these into the function-wide exception-table finally handler.
        let finally_closes = std::mem::take(&mut self.fn_block_scoped_closes);
        if !finally_closes.is_empty() {
            self.fn_exit_closes.insert(fn_id, finally_closes);
        }

        // Restore tracking state
        self.fn_block_scoped_closes = prev_block_closes;
        self.scope_track_stack = prev_scope_stack;

        // Pop recur join params (they were pushed on top of regular params)
        if recur_join_info.is_some() {
            for param in decl.params.iter().rev() {
                self.pop_var(&param.name);
            }
        }
        self.recur_join = None;
        self.early_return_join = None;

        // Pop regular params
        for param in decl.params.iter().rev() {
            self.pop_var(&param.name);
        }

        // Wrap body with early return join if needed
        if let Some((join_name, result_var)) = early_return_info {
            body = expr_at(
                body.span,
                return_type.clone().into(),
                ExprKind::LetJoin {
                    name: join_name,
                    params: vec![(result_var, return_type.clone().into())],
                    join_body: Box::new(atom_expr_at(
                        body.span,
                        return_type.clone().into(),
                        Atom::Var(result_var),
                    )),
                    body: Box::new(body),
                    is_recur: false,
                },
            );
        }

        // Wrap body with recur join if needed
        if let Some((join_name, join_param_vars)) = recur_join_info {
            let join_params: Vec<(VarId, Type)> = join_param_vars
                .iter()
                .enumerate()
                .map(|(i, &v)| {
                    let ty = param_types.get(i).cloned().unwrap_or_else(|| {
                        panic!(
                            "ICE: recur join: param_types index {i} out of range (len={})",
                            param_types.len()
                        )
                    });
                    (v, ty)
                })
                .collect();
            // Original param atoms for the initial jump
            let original_atoms: Vec<Atom> =
                regular_param_vars.iter().map(|&v| Atom::Var(v)).collect();
            let body_span = body.span;
            body = expr_at(
                body_span,
                return_type.clone().into(),
                ExprKind::LetJoin {
                    name: join_name,
                    params: join_params
                        .into_iter()
                        .map(|(v, t)| (v, t.into()))
                        .collect(),
                    join_body: Box::new(body),
                    body: Box::new(expr_at(
                        body_span,
                        return_type.clone().into(),
                        ExprKind::Jump {
                            target: join_name,
                            args: original_atoms,
                        },
                    )),
                    is_recur: true,
                },
            );
        }

        Ok(FnDef {
            id: fn_id,
            name: decl.name.clone(),
            exported_symbol,
            params,
            return_type: return_type.into(),
            body,
        })
    }
}
