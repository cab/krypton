use std::collections::HashSet;

use crate::expr::{Atom, Expr, ExprKind, PrimOp, SimpleExpr};
use crate::pass::{IrPass, IrPassError};
use crate::{FnDef, FnId, Module, Type, VarId};

/// Validates structural invariants of an IR module.
pub struct LintPass;

impl IrPass for LintPass {
    fn name(&self) -> &str {
        "ir_lint"
    }

    fn run(self, module: Module) -> Result<Module, IrPassError> {
        let mut ctx = LintContext::new(&module);
        for func in &module.functions {
            ctx.check_function(func)?;
        }
        Ok(module)
    }
}

struct LintContext {
    bound_vars: HashSet<VarId>,
    join_points: HashSet<VarId>,
    known_fns: HashSet<FnId>,
}

impl LintContext {
    fn new(module: &Module) -> Self {
        let known_fns: HashSet<FnId> = module
            .fn_names
            .keys()
            .copied()
            .collect();

        LintContext {
            bound_vars: HashSet::new(),
            join_points: HashSet::new(),
            known_fns,
        }
    }

    fn err(&self, message: String) -> IrPassError {
        IrPassError {
            pass: "ir_lint".into(),
            message,
        }
    }

    fn check_function(&mut self, func: &FnDef) -> Result<(), IrPassError> {
        // Each function gets a fresh binding scope.
        self.bound_vars.clear();
        self.join_points.clear();

        // Bind params.
        for &(var, _) in &func.params {
            self.bind_var(var)?;
        }

        self.check_expr(&func.body)
    }

    fn bind_var(&mut self, var: VarId) -> Result<(), IrPassError> {
        if !self.bound_vars.insert(var) {
            return Err(self.err(format!("duplicate VarId binding: v{}", var.0)));
        }
        Ok(())
    }

    fn check_expr(&mut self, expr: &Expr) -> Result<(), IrPassError> {
        match &expr.kind {
            ExprKind::Let {
                bind,
                ty,
                value,
                body,
            } => {
                self.check_simple_expr(value, Some(ty))?;
                self.bind_var(*bind)?;
                self.check_expr(body)
            }

            ExprKind::LetRec { bindings, body } => {
                // All FnIds in LetRec must reference known functions.
                for (var, _, fn_id, _) in bindings {
                    if !self.known_fns.contains(fn_id) {
                        return Err(self.err(format!(
                            "LetRec references unknown FnId({})",
                            fn_id.0
                        )));
                    }
                    self.bind_var(*var)?;
                }
                // Check captures.
                for (_, _, _, captures) in bindings {
                    for atom in captures {
                        self.check_atom_not_join(atom)?;
                    }
                }
                self.check_expr(body)
            }

            ExprKind::LetJoin {
                name,
                params,
                join_body,
                body,
            } => {
                self.bind_var(*name)?;
                self.join_points.insert(*name);

                // Join params scope only over join_body, not body.
                let saved_vars = self.bound_vars.clone();
                for &(var, _) in params {
                    self.bind_var(var)?;
                }
                self.check_expr(join_body)?;

                self.bound_vars = saved_vars;
                self.check_expr(body)
            }

            ExprKind::Jump { target, args } => {
                if !self.join_points.contains(target) {
                    return Err(self.err(format!(
                        "Jump target v{} is not a join point",
                        target.0
                    )));
                }
                for atom in args {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                self.check_atom_not_join(scrutinee)?;
                for branch in branches {
                    // Branch bindings scope only over this branch's body.
                    let saved_vars = self.bound_vars.clone();
                    for &(var, _) in &branch.bindings {
                        self.bind_var(var)?;
                    }
                    self.check_expr(&branch.body)?;
                    self.bound_vars = saved_vars;
                }
                if let Some(d) = default {
                    self.check_expr(d)?;
                }
                Ok(())
            }

            ExprKind::Atom(atom) => {
                self.check_atom_not_join(atom)?;
                Ok(())
            }
        }
    }

    fn check_simple_expr(
        &self,
        expr: &SimpleExpr,
        let_ty: Option<&Type>,
    ) -> Result<(), IrPassError> {
        match expr {
            SimpleExpr::Call { func, args } => {
                if !self.known_fns.contains(func) {
                    return Err(self.err(format!(
                        "Call references unknown FnId({})",
                        func.0
                    )));
                }
                for atom in args {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            SimpleExpr::CallClosure { closure, args } => {
                self.check_atom_not_join(closure)?;
                for atom in args {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            SimpleExpr::MakeClosure { func, captures } => {
                if !self.known_fns.contains(func) {
                    return Err(self.err(format!(
                        "MakeClosure references unknown FnId({})",
                        func.0
                    )));
                }
                for atom in captures {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            SimpleExpr::PrimOp { op, args } => {
                if let Some(let_ty) = let_ty {
                    let expected_ret = primop_return_type(*op);
                    check_type_match(let_ty, &expected_ret, &format!("PrimOp {op:?}"))
                        .map_err(|msg| self.err(msg))?;
                }
                for atom in args {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            SimpleExpr::Construct { fields, .. }
            | SimpleExpr::ConstructVariant { fields, .. } => {
                for atom in fields {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            SimpleExpr::Project { value, .. } | SimpleExpr::Tag { value } => {
                self.check_atom_not_join(value)
            }

            SimpleExpr::MakeTuple { elements } | SimpleExpr::MakeVec { elements, .. } => {
                for atom in elements {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            SimpleExpr::TupleProject { value, .. } => self.check_atom_not_join(value),

            SimpleExpr::GetDict { .. } => Ok(()),

            SimpleExpr::MakeDict { sub_dicts, .. } => {
                for atom in sub_dicts {
                    self.check_atom_not_join(atom)?;
                }
                Ok(())
            }

            SimpleExpr::Atom(atom) => self.check_atom_not_join(atom),
        }
    }

    /// Check that an atom used as a value is not a join point.
    fn check_atom_not_join(&self, atom: &Atom) -> Result<(), IrPassError> {
        if let Atom::Var(var) = atom {
            if self.join_points.contains(var) {
                return Err(self.err(format!(
                    "join point v{} used as a value (only Jump targets allowed)",
                    var.0
                )));
            }
        }
        Ok(())
    }
}

/// Check that two types match structurally. Returns Ok(()) if they match or if
/// either type contains type variables (we can't fully check polymorphic code).
fn check_type_match(actual: &Type, expected: &Type, context: &str) -> Result<(), String> {
    if types_compatible(actual, expected) {
        Ok(())
    } else {
        Err(format!(
            "type mismatch in {context}: expected {expected:?}, got {actual:?}"
        ))
    }
}

/// Conservative type compatibility check. Returns true if types are structurally
/// equal or if either contains type variables (which we can't resolve here).
fn types_compatible(a: &Type, b: &Type) -> bool {
    // If either side has type vars or App, we can't fully check — be lenient.
    if contains_type_var(a) || contains_type_var(b) {
        return true;
    }
    match (a, b) {
        (Type::Int, Type::Int)
        | (Type::Float, Type::Float)
        | (Type::Bool, Type::Bool)
        | (Type::String, Type::String)
        | (Type::Unit, Type::Unit) => true,
        (Type::Fn(a_args, a_ret), Type::Fn(b_args, b_ret)) => {
            a_args.len() == b_args.len()
                && a_args.iter().zip(b_args).all(|(x, y)| types_compatible(x, y))
                && types_compatible(a_ret, b_ret)
        }
        (Type::Named(a_name, a_args), Type::Named(b_name, b_args)) => {
            a_name == b_name
                && a_args.len() == b_args.len()
                && a_args.iter().zip(b_args).all(|(x, y)| types_compatible(x, y))
        }
        (Type::Tuple(a_elts), Type::Tuple(b_elts)) => {
            a_elts.len() == b_elts.len()
                && a_elts.iter().zip(b_elts).all(|(x, y)| types_compatible(x, y))
        }
        (Type::Own(a_inner), Type::Own(b_inner)) => types_compatible(a_inner, b_inner),
        _ => false,
    }
}

fn contains_type_var(ty: &Type) -> bool {
    match ty {
        Type::Var(_) | Type::App(_, _) | Type::FnHole => true,
        Type::Int | Type::Float | Type::Bool | Type::String | Type::Unit => false,
        Type::Fn(args, ret) => args.iter().any(contains_type_var) || contains_type_var(ret),
        Type::Named(_, args) => args.iter().any(contains_type_var),
        Type::Tuple(elts) => elts.iter().any(contains_type_var),
        Type::Own(inner) => contains_type_var(inner),
    }
}

fn primop_return_type(op: PrimOp) -> Type {
    match op {
        PrimOp::AddInt
        | PrimOp::SubInt
        | PrimOp::MulInt
        | PrimOp::DivInt
        | PrimOp::ModInt
        | PrimOp::NegInt
        | PrimOp::FloatToInt => Type::Int,

        PrimOp::AddFloat
        | PrimOp::SubFloat
        | PrimOp::MulFloat
        | PrimOp::DivFloat
        | PrimOp::NegFloat
        | PrimOp::IntToFloat => Type::Float,

        PrimOp::EqInt
        | PrimOp::NeqInt
        | PrimOp::LtInt
        | PrimOp::LeInt
        | PrimOp::GtInt
        | PrimOp::GeInt
        | PrimOp::EqFloat
        | PrimOp::NeqFloat
        | PrimOp::LtFloat
        | PrimOp::LeFloat
        | PrimOp::GtFloat
        | PrimOp::GeFloat
        | PrimOp::Not
        | PrimOp::And
        | PrimOp::Or
        | PrimOp::EqString
        | PrimOp::NeqString => Type::Bool,

        PrimOp::ConcatString
        | PrimOp::IntToString
        | PrimOp::FloatToString
        | PrimOp::BoolToString => Type::String,
    }
}
