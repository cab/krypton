// Pattern-match compilation. Implements the standard clause-matrix
// algorithm: each call to `compile_clauses` picks a column (pick_column),
// classifies its head constructors (classify_column), and dispatches to
// the matching specialization helper. Or-patterns are flattened lazily
// at the active column; var patterns are eagerly bound and rewritten
// to wildcards before specialization runs.

use rustc_hash::{FxHashMap, FxHashSet};
use std::rc::Rc;

use krypton_parser::ast::Lit;
use krypton_typechecker::typed_ast::{TypedExpr, TypedExprKind, TypedMatchArm, TypedPattern};
use krypton_typechecker::types::Type;

use super::ctx::{Clause, ClausePayload, ColumnKind, LetBinding, LowerCtx};
use super::module_pipeline::convert_lit;
use super::util::{atom_expr_at, expr_at, flatten_or_at_column, is_wildcard_or_var, pattern_type, simple_at};
use super::LowerError;
use crate::{Atom, Expr, ExprKind, Literal, PrimOp, SimpleExprKind, SwitchBranch, VarId};

impl<'a> LowerCtx<'a> {
    // -----------------------------------------------------------------------
    // Pattern match compilation (clause-matrix algorithm)
    // -----------------------------------------------------------------------

    /// Lower a match expression into a Switch decision tree.
    pub(super) fn lower_match(
        &mut self,
        scrutinee: &TypedExpr,
        arms: &[TypedMatchArm],
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let result_ty = result_ty.clone();
        let arms = arms.to_vec();
        self.lower_to_atom_then(scrutinee, |ctx, scrut_atom| {
            let clauses: Vec<Clause> = arms
                .iter()
                .flat_map(|arm| {
                    let payload = Rc::new(ClausePayload {
                        guard: arm.guard.clone(),
                        body: arm.body.clone(),
                    });
                    match &arm.pattern {
                        TypedPattern::Or { alternatives, .. } => alternatives
                            .iter()
                            .map(|alt| Clause {
                                patterns: vec![alt.clone()],
                                payload: Rc::clone(&payload),
                                extra_bindings: vec![],
                            })
                            .collect::<Vec<_>>(),
                        _ => vec![Clause {
                            patterns: vec![arm.pattern.clone()],
                            payload,
                            extra_bindings: vec![],
                        }],
                    }
                })
                .collect();
            ctx.compile_clauses(vec![scrut_atom], clauses, &result_ty)
        })
    }

    /// Lower a let-pattern binding as an irrefutable single-arm match.
    pub(super) fn lower_let_pattern(
        &mut self,
        pattern: &TypedPattern,
        value: &TypedExpr,
        body: Option<&TypedExpr>,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let result_ty = result_ty.clone();
        let pattern = pattern.clone();
        let body_expr = if let Some(body) = body {
            body.clone()
        } else {
            TypedExpr {
                kind: TypedExprKind::Lit(Lit::Unit),
                ty: Type::Unit,
                span: (0, 0),
                resolved_ref: None,
                scope_id: None,
            }
        };

        self.lower_to_atom_then(value, |ctx, val_atom| {
            let clause = Clause {
                patterns: vec![pattern],
                payload: Rc::new(ClausePayload {
                    guard: None,
                    body: body_expr,
                }),
                extra_bindings: vec![],
            };
            ctx.compile_clauses(vec![val_atom], vec![clause], &result_ty)
        })
    }

    /// Core clause-matrix compilation.
    ///
    /// `scrutinees` - atoms to match against (one per column)
    /// `clauses` - rows of patterns + body
    /// `result_ty` - type of the overall match expression
    pub(super) fn compile_clauses(
        &mut self,
        scrutinees: Vec<Atom>,
        clauses: Vec<Clause>,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Base case: no clauses — unreachable (typechecker ensures exhaustiveness)
        if clauses.is_empty() {
            // Emit a unit atom as a placeholder for unreachable code
            return Ok(atom_expr_at(
                (0, 0),
                result_ty.clone().into(),
                Atom::Lit(Literal::Unit),
            ));
        }

        // Base case: first row is all wildcards/vars — it matches
        if clauses[0].patterns.iter().all(is_wildcard_or_var) {
            if clauses[0].guard().is_some() {
                return self.compile_guarded_clause(scrutinees, clauses, result_ty);
            }
            return self.bind_and_lower_body(&scrutinees, &clauses[0]);
        }

        // Pick the first column with a non-wildcard pattern
        let col = self.pick_column(&clauses);

        // Flatten any or-patterns at the picked column before classification
        let clauses = flatten_or_at_column(clauses, col);

        // Determine what kind of head constructors appear in this column
        let head_kind = self.classify_column(&clauses, col);

        match head_kind {
            ColumnKind::Constructor => {
                self.compile_constructor_column(&scrutinees, clauses, col, result_ty)
            }
            ColumnKind::Literal => {
                self.compile_literal_column(&scrutinees, clauses, col, result_ty)
            }
            ColumnKind::Tuple(arity) => {
                self.compile_tuple_column(&scrutinees, clauses, col, result_ty, arity)
            }
            ColumnKind::Struct(name) => {
                self.compile_struct_column(&scrutinees, clauses, col, result_ty, &name)
            }
        }
    }

    /// Bind variables from an all-wildcard/var row, then lower the body.
    pub(super) fn bind_and_lower_body(
        &mut self,
        scrutinees: &[Atom],
        clause: &Clause,
    ) -> Result<Expr, LowerError> {
        let mut bound_names = Vec::new();
        let mut lit_bindings: Vec<LetBinding> = Vec::new();

        // First, bind extra_bindings accumulated from specialization of Var patterns
        for (name, atom, ty) in &clause.extra_bindings {
            let maybe_res = self.resource_type_name(ty);
            match atom {
                Atom::Var(id) => {
                    self.var_types.insert(*id, ty.clone());
                    if let Some(type_name) = &maybe_res {
                        self.bind_resource(name, *id, type_name);
                    } else {
                        self.push_var(name, *id);
                    }
                    bound_names.push(name.clone());
                }
                Atom::Lit(lit) => {
                    let var = self.fresh_var();
                    self.var_types.insert(var, ty.clone());
                    if let Some(type_name) = &maybe_res {
                        self.bind_resource(name, var, type_name);
                    } else {
                        self.push_var(name, var);
                    }
                    bound_names.push(name.clone());
                    lit_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(
                            clause.span(),
                            SimpleExprKind::Atom(crate::Atom::Lit(lit.clone())),
                        ),
                    });
                }
            }
        }

        // Push variable bindings from the remaining pattern row
        for (pat, scrut) in clause.patterns.iter().zip(scrutinees.iter()) {
            if let TypedPattern::Var { name, ty, .. } = pat {
                let maybe_res = self.resource_type_name(ty);
                match scrut {
                    Atom::Var(scrut_id) => {
                        self.var_types.insert(*scrut_id, ty.clone());
                        if let Some(type_name) = &maybe_res {
                            self.bind_resource(name, *scrut_id, type_name);
                        } else {
                            self.push_var(name, *scrut_id);
                        }
                        bound_names.push(name.clone());
                    }
                    Atom::Lit(lit) => {
                        let var = self.fresh_var();
                        self.var_types.insert(var, ty.clone());
                        if let Some(type_name) = &maybe_res {
                            self.bind_resource(name, var, type_name);
                        } else {
                            self.push_var(name, var);
                        }
                        bound_names.push(name.clone());
                        lit_bindings.push(LetBinding {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                clause.span(),
                                SimpleExprKind::Atom(crate::Atom::Lit(lit.clone())),
                            ),
                        });
                    }
                }
            }
        }

        let body_expr = self.lower_expr(clause.body())?;

        // Pop variable bindings
        for name in bound_names.iter().rev() {
            self.pop_var(name);
        }

        // Wrap with literal bindings if any
        if lit_bindings.is_empty() {
            Ok(body_expr)
        } else {
            Ok(Self::wrap_bindings(lit_bindings, body_expr))
        }
    }

    /// Compile a guarded clause: bind vars, evaluate guard, BoolSwitch to body or fallthrough.
    pub(super) fn compile_guarded_clause(
        &mut self,
        scrutinees: Vec<Atom>,
        clauses: Vec<Clause>,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Extract what we need from the first clause before splitting the vec
        let mut clauses = clauses;
        let first = clauses.remove(0);
        let span = first.span();
        let payload = Rc::clone(&first.payload);
        let extra_bindings = first.extra_bindings;
        let patterns = first.patterns;
        let remaining = clauses; // rest after removing first

        // Bind variables (same logic as bind_and_lower_body)
        let mut bound_names = Vec::new();
        let mut lit_bindings: Vec<LetBinding> = Vec::new();

        for (name, atom, ty) in &extra_bindings {
            let maybe_res = self.resource_type_name(ty);
            match atom {
                Atom::Var(id) => {
                    self.var_types.insert(*id, ty.clone());
                    if let Some(type_name) = &maybe_res {
                        self.bind_resource(name, *id, type_name);
                    } else {
                        self.push_var(name, *id);
                    }
                    bound_names.push(name.clone());
                }
                Atom::Lit(lit) => {
                    let var = self.fresh_var();
                    self.var_types.insert(var, ty.clone());
                    if let Some(type_name) = &maybe_res {
                        self.bind_resource(name, var, type_name);
                    } else {
                        self.push_var(name, var);
                    }
                    bound_names.push(name.clone());
                    lit_bindings.push(LetBinding {
                        bind: var,
                        ty: ty.clone().into(),
                        value: simple_at(span, SimpleExprKind::Atom(crate::Atom::Lit(lit.clone()))),
                    });
                }
            }
        }

        for (pat, scrut) in patterns.iter().zip(scrutinees.iter()) {
            if let TypedPattern::Var { name, ty, .. } = pat {
                let maybe_res = self.resource_type_name(ty);
                match scrut {
                    Atom::Var(scrut_id) => {
                        self.var_types.insert(*scrut_id, ty.clone());
                        if let Some(type_name) = &maybe_res {
                            self.bind_resource(name, *scrut_id, type_name);
                        } else {
                            self.push_var(name, *scrut_id);
                        }
                        bound_names.push(name.clone());
                    }
                    Atom::Lit(lit) => {
                        let var = self.fresh_var();
                        self.var_types.insert(var, ty.clone());
                        if let Some(type_name) = &maybe_res {
                            self.bind_resource(name, var, type_name);
                        } else {
                            self.push_var(name, var);
                        }
                        bound_names.push(name.clone());
                        lit_bindings.push(LetBinding {
                            bind: var,
                            ty: ty.clone().into(),
                            value: simple_at(
                                span,
                                SimpleExprKind::Atom(crate::Atom::Lit(lit.clone())),
                            ),
                        });
                    }
                }
            }
        }

        // Lower guard via lower_to_atom_then so complex guards get bound to a temp var
        let result_ty_clone = result_ty.clone();
        let guard_typed = payload
            .guard
            .as_deref()
            .expect("guarded clause must have a guard");
        let payload_for_body = Rc::clone(&payload);
        let guard_and_branches = self.lower_to_atom_then(guard_typed, move |ctx, guard_atom| {
            let body_expr = ctx.lower_expr(&payload_for_body.body)?;

            // Pop variable bindings before compiling fallthrough
            for name in bound_names.iter().rev() {
                ctx.pop_var(name);
            }

            let fallthrough = ctx.compile_clauses(scrutinees, remaining, &result_ty_clone)?;

            Ok(Expr {
                kind: ExprKind::BoolSwitch {
                    scrutinee: guard_atom,
                    true_body: Box::new(body_expr),
                    false_body: Box::new(fallthrough),
                },
                ty: result_ty_clone.clone().into(),
                span,
            })
        })?;

        if lit_bindings.is_empty() {
            Ok(guard_and_branches)
        } else {
            Ok(Self::wrap_bindings(lit_bindings, guard_and_branches))
        }
    }

    /// Pick the first column that has a non-wildcard/var pattern.
    pub(super) fn pick_column(&self, clauses: &[Clause]) -> usize {
        let ncols = clauses[0].patterns.len();
        for col in 0..ncols {
            for clause in clauses {
                if !is_wildcard_or_var(&clause.patterns[col]) {
                    return col;
                }
            }
        }
        0 // fallback (shouldn't happen — handled by all-wildcards base case)
    }

    /// Classify what kind of patterns appear in a column.
    pub(super) fn classify_column(&self, clauses: &[Clause], col: usize) -> ColumnKind {
        for clause in clauses {
            match &clause.patterns[col] {
                TypedPattern::Constructor { .. } => return ColumnKind::Constructor,
                TypedPattern::Lit { .. } => return ColumnKind::Literal,
                TypedPattern::Tuple { elements, .. } => return ColumnKind::Tuple(elements.len()),
                TypedPattern::StructPat { name, .. } => return ColumnKind::Struct(name.clone()),
                TypedPattern::Wildcard { .. } | TypedPattern::Var { .. } => continue,
                TypedPattern::Or { .. } => continue, // flattened before reaching here
            }
        }
        // All wildcards — shouldn't happen since we chose a non-wildcard column
        ColumnKind::Constructor
    }

    /// Compile a column with constructor patterns into a Switch.
    pub(super) fn compile_constructor_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        // Collect all constructor heads that appear
        let mut seen_tags: Vec<(String, u32, Vec<Type>)> = Vec::new();
        let mut seen_names: FxHashSet<String> = FxHashSet::default();
        for clause in &clauses {
            if let TypedPattern::Constructor {
                name,
                resolved_variant_ref,
                ..
            } = &clause.patterns[col]
            {
                if seen_names.insert(name.clone()) {
                    let variant_ref = resolved_variant_ref
                        .clone()
                        .or_else(|| self.fallback_variant_ref(name))
                        .ok_or_else(|| {
                            LowerError::InternalError(format!(
                                "unknown variant ref in pattern: {name}"
                            ))
                        })?;
                    let (tag, field_types) = self.variant_info(&variant_ref)?;
                    seen_tags.push((name.clone(), tag, field_types));
                }
            }
        }

        let scrut = scrutinees[col].clone();
        let mut branches = Vec::new();

        for (ctor_name, tag, field_types) in &seen_tags {
            // Create fresh bindings for variant fields
            let mut field_bindings = Vec::new();
            let mut field_atoms = Vec::new();
            for ft in field_types {
                let v = self.fresh_var();
                self.var_types.insert(v, ft.clone());
                field_bindings.push((v, ft.clone()));
                field_atoms.push(Atom::Var(v));
            }

            // Specialize the clause matrix for this constructor
            let specialized =
                self.specialize_for_constructor(&clauses, col, ctor_name, field_types, &scrut);

            // Build new scrutinee list: replace col with field atoms
            let mut new_scrutinees = Vec::new();
            for (i, s) in scrutinees.iter().enumerate() {
                if i == col {
                    new_scrutinees.extend(field_atoms.clone());
                } else {
                    new_scrutinees.push(s.clone());
                }
            }

            let body = self.compile_clauses(new_scrutinees, specialized, result_ty)?;

            // Use concrete types updated during lowering, not abstract field types
            let concrete_bindings: Vec<(VarId, Type)> = field_bindings
                .iter()
                .map(|(v, abstract_t)| {
                    (
                        *v,
                        self.var_types
                            .get(v)
                            .cloned()
                            .unwrap_or_else(|| abstract_t.clone()),
                    )
                })
                .collect();

            branches.push(SwitchBranch {
                tag: *tag,
                bindings: concrete_bindings
                    .into_iter()
                    .map(|(v, t)| (v, t.into()))
                    .collect(),
                body,
            });
        }

        // Default matrix: rows with wildcard/var at col, remove that column
        let default_clauses = self.default_matrix(&clauses, col, &scrut);
        let default = if default_clauses.is_empty() {
            None
        } else {
            let mut new_scrutinees: Vec<Atom> = Vec::new();
            for (i, s) in scrutinees.iter().enumerate() {
                if i != col {
                    new_scrutinees.push(s.clone());
                }
            }
            Some(Box::new(self.compile_clauses(
                new_scrutinees,
                default_clauses,
                result_ty,
            )?))
        };

        Ok(expr_at(
            clauses[0].span(),
            result_ty.clone().into(),
            ExprKind::Switch {
                scrutinee: scrut,
                branches,
                default,
            },
        ))
    }

    /// Compile a column with literal patterns into chained equality checks.
    pub(super) fn compile_literal_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
    ) -> Result<Expr, LowerError> {
        let scrut = scrutinees[col].clone();

        // Collect distinct literals
        let mut lit_values: Vec<Lit> = Vec::new();
        for clause in &clauses {
            if let TypedPattern::Lit { value, .. } = &clause.patterns[col] {
                if !lit_values.iter().any(|l| l == value) {
                    lit_values.push(value.clone());
                }
            }
        }

        // Build from the bottom up: start with default, then chain if-else for each literal
        let default_clauses = self.default_matrix(&clauses, col, &scrut);
        let mut new_scrutinees_for_default: Vec<Atom> = Vec::new();
        for (i, s) in scrutinees.iter().enumerate() {
            if i != col {
                new_scrutinees_for_default.push(s.clone());
            }
        }

        let mut result = if default_clauses.is_empty() {
            // Unreachable
            atom_expr_at((0, 0), result_ty.clone().into(), Atom::Lit(Literal::Unit))
        } else {
            self.compile_clauses(
                new_scrutinees_for_default.clone(),
                default_clauses,
                result_ty,
            )?
        };

        // Chain literals in reverse order so the first literal tested is the first one encountered
        for lit in lit_values.iter().rev() {
            let specialized = self.specialize_for_literal(&clauses, col, lit, &scrut);
            // Literals have no sub-patterns, so just remove the column
            let mut new_scrutinees: Vec<Atom> = Vec::new();
            for (i, s) in scrutinees.iter().enumerate() {
                if i != col {
                    new_scrutinees.push(s.clone());
                }
            }
            let then_body = self.compile_clauses(new_scrutinees, specialized, result_ty)?;

            // Emit: let eq = EqInt(scrut, lit_val) in switch eq { 1 -> then | _ -> else }
            let eq_op = self.eq_op_for_lit(lit)?;
            let lit_atom = Atom::Lit(convert_lit(lit));
            let eq_var = self.fresh_var();

            result = expr_at(
                then_body.span,
                result_ty.clone().into(),
                ExprKind::Let {
                    bind: eq_var,
                    ty: Type::Bool.into(),
                    value: simple_at(
                        then_body.span,
                        SimpleExprKind::PrimOp {
                            op: eq_op,
                            args: vec![scrut.clone(), lit_atom],
                        },
                    ),
                    body: Box::new(expr_at(
                        then_body.span,
                        result_ty.clone().into(),
                        ExprKind::BoolSwitch {
                            scrutinee: Atom::Var(eq_var),
                            true_body: Box::new(then_body),
                            false_body: Box::new(result),
                        },
                    )),
                },
            );
        }

        Ok(result)
    }

    /// Compile a column with tuple patterns — expand with projections, no Switch needed.
    pub(super) fn compile_tuple_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
        arity: usize,
    ) -> Result<Expr, LowerError> {
        let scrut = scrutinees[col].clone();

        // Get the scrutinee type for fallback in tuple_element_type
        let scrut_ty = if let Atom::Var(id) = &scrut {
            self.var_types
                .get(id)
                .cloned()
                .unwrap_or_else(|| pattern_type(&clauses[0].patterns[col]))
        } else {
            pattern_type(&clauses[0].patterns[col])
        };

        // Project each element
        let mut proj_vars = Vec::new();
        let mut proj_bindings = Vec::new();
        for i in 0..arity {
            let elem_ty = self.tuple_element_type(&clauses, col, i, &scrut_ty);
            let v = self.fresh_var();
            self.var_types.insert(v, elem_ty.clone());
            proj_bindings.push(LetBinding {
                bind: v,
                ty: elem_ty.into(),
                value: simple_at(
                    clauses[0].span(),
                    SimpleExprKind::TupleProject {
                        value: scrut.clone(),
                        index: i,
                    },
                ),
            });
            proj_vars.push(Atom::Var(v));
        }

        // Expand columns: replace col with element sub-patterns
        let expanded: Vec<Clause> = clauses
            .into_iter()
            .map(|c| self.expand_tuple_clause(c, col, arity, &scrut))
            .collect();

        // Build new scrutinee list
        let mut new_scrutinees = Vec::new();
        for (i, s) in scrutinees.iter().enumerate() {
            if i == col {
                new_scrutinees.extend(proj_vars.clone());
            } else {
                new_scrutinees.push(s.clone());
            }
        }

        let body = self.compile_clauses(new_scrutinees, expanded, result_ty)?;
        Ok(Self::wrap_bindings(proj_bindings, body))
    }

    /// Compile a column with struct patterns — expand with field projections.
    pub(super) fn compile_struct_column(
        &mut self,
        scrutinees: &[Atom],
        clauses: Vec<Clause>,
        col: usize,
        result_ty: &Type,
        struct_name: &str,
    ) -> Result<Expr, LowerError> {
        let scrut = scrutinees[col].clone();
        let type_ref = clauses
            .iter()
            .find_map(|clause| match &clause.patterns[col] {
                TypedPattern::StructPat {
                    resolved_type_ref, ..
                } => resolved_type_ref.clone(),
                _ => None,
            })
            .or_else(|| self.fallback_type_ref(struct_name))
            .ok_or_else(|| LowerError::UnresolvedStruct(struct_name.to_string()))?;

        let scrut_ty = match &scrut {
            Atom::Var(v) => self
                .var_types
                .get(v)
                .cloned()
                .unwrap_or_else(|| Type::Named(struct_name.to_string(), vec![])),
            _ => Type::Named(struct_name.to_string(), vec![]),
        };
        let canonical_fields = self.substituted_struct_fields(&type_ref, &scrut_ty)?;

        // Project each field
        let mut proj_vars = Vec::new();
        let mut proj_bindings = Vec::new();
        for (i, (_, fty)) in canonical_fields.iter().enumerate() {
            let v = self.fresh_var();
            self.var_types.insert(v, fty.clone());
            proj_bindings.push(LetBinding {
                bind: v,
                ty: fty.clone().into(),
                value: simple_at(
                    clauses[0].span(),
                    SimpleExprKind::Project {
                        value: scrut.clone(),
                        field_index: i,
                    },
                ),
            });
            proj_vars.push(Atom::Var(v));
        }

        // Expand columns: replace col with field sub-patterns in canonical order
        let expanded: Vec<Clause> = clauses
            .into_iter()
            .map(|c| self.expand_struct_clause(c, col, &canonical_fields, &scrut))
            .collect();

        let mut new_scrutinees = Vec::new();
        for (i, s) in scrutinees.iter().enumerate() {
            if i == col {
                new_scrutinees.extend(proj_vars.clone());
            } else {
                new_scrutinees.push(s.clone());
            }
        }

        let body = self.compile_clauses(new_scrutinees, expanded, result_ty)?;
        Ok(Self::wrap_bindings(proj_bindings, body))
    }

    /// Specialize clause matrix for a given constructor.
    pub(super) fn specialize_for_constructor(
        &self,
        clauses: &[Clause],
        col: usize,
        ctor_name: &str,
        field_types: &[Type],
        scrut_at_col: &Atom,
    ) -> Vec<Clause> {
        let mut result = Vec::new();
        for clause in clauses {
            match &clause.patterns[col] {
                TypedPattern::Constructor { name, args, .. } if name == ctor_name => {
                    // Replace column with sub-patterns
                    let mut new_pats = Vec::new();
                    for (i, p) in clause.patterns.iter().enumerate() {
                        if i == col {
                            new_pats.extend(args.clone());
                        } else {
                            new_pats.push(p.clone());
                        }
                    }
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Wildcard { span, .. } => {
                    // Expand wildcard to `arity` wildcards with correct field types
                    let mut new_pats = Vec::new();
                    for (i, p) in clause.patterns.iter().enumerate() {
                        if i == col {
                            for ft in field_types {
                                new_pats.push(TypedPattern::Wildcard {
                                    ty: ft.clone(),
                                    span: *span,
                                });
                            }
                        } else {
                            new_pats.push(p.clone());
                        }
                    }
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Var { name, ty, span } => {
                    // Expand to wildcards but record binding for the whole scrutinee
                    let mut new_pats = Vec::new();
                    for (i, p) in clause.patterns.iter().enumerate() {
                        if i == col {
                            for ft in field_types {
                                new_pats.push(TypedPattern::Wildcard {
                                    ty: ft.clone(),
                                    span: *span,
                                });
                            }
                        } else {
                            new_pats.push(p.clone());
                        }
                    }
                    let mut extra = clause.extra_bindings.clone();
                    extra.push((name.clone(), scrut_at_col.clone(), ty.clone()));
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: extra,
                    });
                }
                _ => {
                    // Different constructor — skip this row
                }
            }
        }
        result
    }

    /// Specialize clause matrix for a given literal value.
    pub(super) fn specialize_for_literal(
        &self,
        clauses: &[Clause],
        col: usize,
        lit: &Lit,
        scrut_at_col: &Atom,
    ) -> Vec<Clause> {
        let mut result = Vec::new();
        for clause in clauses {
            match &clause.patterns[col] {
                TypedPattern::Lit { value, .. } if value == lit => {
                    // Literals have no sub-patterns; just remove the column
                    let new_pats: Vec<_> = clause
                        .patterns
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != col)
                        .map(|(_, p)| p.clone())
                        .collect();
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Wildcard { .. } => {
                    let new_pats: Vec<_> = clause
                        .patterns
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != col)
                        .map(|(_, p)| p.clone())
                        .collect();
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: clause.extra_bindings.clone(),
                    });
                }
                TypedPattern::Var { name, ty, .. } => {
                    let new_pats: Vec<_> = clause
                        .patterns
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != col)
                        .map(|(_, p)| p.clone())
                        .collect();
                    let mut extra = clause.extra_bindings.clone();
                    extra.push((name.clone(), scrut_at_col.clone(), ty.clone()));
                    result.push(Clause {
                        patterns: new_pats,
                        payload: Rc::clone(&clause.payload),
                        extra_bindings: extra,
                    });
                }
                _ => {}
            }
        }
        result
    }

    /// Default matrix: keep rows with wildcard/var at col, remove that column.
    pub(super) fn default_matrix(&self, clauses: &[Clause], col: usize, scrut_at_col: &Atom) -> Vec<Clause> {
        let mut result = Vec::new();
        for clause in clauses {
            let pat = &clause.patterns[col];
            if is_wildcard_or_var(pat) {
                let new_pats: Vec<_> = clause
                    .patterns
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != col)
                    .map(|(_, p)| p.clone())
                    .collect();
                let mut extra = clause.extra_bindings.clone();
                if let TypedPattern::Var { name, ty, .. } = pat {
                    extra.push((name.clone(), scrut_at_col.clone(), ty.clone()));
                }
                result.push(Clause {
                    patterns: new_pats,
                    payload: Rc::clone(&clause.payload),
                    extra_bindings: extra,
                });
            }
        }
        result
    }

    /// Expand a clause's tuple pattern at `col` into element sub-patterns.
    pub(super) fn expand_tuple_clause(
        &self,
        clause: Clause,
        col: usize,
        arity: usize,
        scrut_at_col: &Atom,
    ) -> Clause {
        let mut new_pats = Vec::new();
        let mut extra = clause.extra_bindings;
        for (i, p) in clause.patterns.into_iter().enumerate() {
            if i == col {
                match p {
                    TypedPattern::Tuple { elements, .. } => {
                        new_pats.extend(elements);
                    }
                    TypedPattern::Var { name, ty, span } => {
                        extra.push((name, scrut_at_col.clone(), ty.clone()));
                        for _ in 0..arity {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: ty.clone(),
                                span,
                            });
                        }
                    }
                    TypedPattern::Wildcard { ty, span } => {
                        for _ in 0..arity {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: ty.clone(),
                                span,
                            });
                        }
                    }
                    _ => {
                        // Shouldn't happen
                        new_pats.push(p);
                    }
                }
            } else {
                new_pats.push(p);
            }
        }
        Clause {
            patterns: new_pats,
            payload: clause.payload,
            extra_bindings: extra,
        }
    }

    /// Expand a clause's struct pattern at `col` into field sub-patterns (canonical order).
    pub(super) fn expand_struct_clause(
        &self,
        clause: Clause,
        col: usize,
        canonical_fields: &[(String, Type)],
        scrut_at_col: &Atom,
    ) -> Clause {
        let mut new_pats = Vec::new();
        let mut extra = clause.extra_bindings;
        for (i, p) in clause.patterns.into_iter().enumerate() {
            if i == col {
                match p {
                    TypedPattern::StructPat { fields, span, .. } => {
                        let field_map: FxHashMap<String, TypedPattern> =
                            fields.into_iter().collect();
                        for (fname, fty) in canonical_fields {
                            if let Some(fp) = field_map.get(fname) {
                                new_pats.push(fp.clone());
                            } else {
                                new_pats.push(TypedPattern::Wildcard {
                                    ty: fty.clone(),
                                    span,
                                });
                            }
                        }
                    }
                    TypedPattern::Var { name, ty, span } => {
                        extra.push((name, scrut_at_col.clone(), ty));
                        for (_, fty) in canonical_fields {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: fty.clone(),
                                span,
                            });
                        }
                    }
                    TypedPattern::Wildcard { ty: _, span } => {
                        for (_, fty) in canonical_fields {
                            new_pats.push(TypedPattern::Wildcard {
                                ty: fty.clone(),
                                span,
                            });
                        }
                    }
                    _ => {
                        new_pats.push(p);
                    }
                }
            } else {
                new_pats.push(p);
            }
        }
        Clause {
            patterns: new_pats,
            payload: clause.payload,
            extra_bindings: extra,
        }
    }

    /// Get the type of a tuple element from the patterns in a column.
    pub(super) fn tuple_element_type(
        &self,
        clauses: &[Clause],
        col: usize,
        index: usize,
        scrut_ty: &Type,
    ) -> Type {
        for clause in clauses {
            if let TypedPattern::Tuple { elements, .. } = &clause.patterns[col] {
                if let Some(elem) = elements.get(index) {
                    return pattern_type(elem);
                }
            }
        }
        // Fallback: extract from scrutinee type
        if let Type::Tuple(elems) = scrut_ty {
            if let Some(ty) = elems.get(index) {
                return ty.clone();
            }
        }
        Type::Unit
    }

    /// Get the equality PrimOp for a literal pattern.
    pub(super) fn eq_op_for_lit(&self, lit: &Lit) -> Result<PrimOp, LowerError> {
        match lit {
            Lit::Int(_) => Ok(PrimOp::EqInt),
            Lit::Float(_) => Ok(PrimOp::EqFloat),
            Lit::Bool(_) => Ok(PrimOp::EqInt), // booleans compared as ints
            Lit::String(_) => Ok(PrimOp::EqString),
            Lit::Unit => Err(LowerError::UnsupportedOp(
                "matching on Unit literal".to_string(),
            )),
        }
    }

}
