// Operator and literal resolution helpers. Free functions that map
// parser-side `Lit`/`BinOp`/`UnaryOp` to IR primitives, plus the small
// `Type` wrapper utilities (`strip_own`, `extract_vec_element_type`)
// that the operator-resolution paths rely on.

use krypton_parser::ast::{BinOp, Lit, UnaryOp};
use krypton_typechecker::types::Type;

use super::LowerError;
use crate::{Literal, PrimOp};

/// Convert a parser Lit to an IR Literal.
pub(super) fn convert_lit(lit: &Lit) -> Literal {
    match lit {
        Lit::Int(n) => Literal::Int(*n),
        Lit::Float(f) => Literal::Float(*f),
        Lit::Bool(b) => Literal::Bool(*b),
        Lit::String(s) => Literal::String(s.clone()),
        Lit::Unit => Literal::Unit,
    }
}

/// Strip Own wrappers to get the underlying type for operation resolution.
pub(super) fn strip_own(ty: &Type) -> &Type {
    match ty {
        Type::Own(inner) => strip_own(inner),
        other => other,
    }
}

/// Extract the element type from a Vec type (Named or Own(Named)).
pub(super) fn extract_vec_element_type(ty: &Type) -> Result<Type, LowerError> {
    let named = match ty {
        Type::Named(_, args) => args,
        Type::Own(inner) => match inner.as_ref() {
            Type::Named(_, args) => args,
            other => {
                return Err(LowerError::InternalError(format!(
                    "Vec element type: expected Own(Named), got Own({other:?})"
                )))
            }
        },
        other => {
            return Err(LowerError::InternalError(format!(
                "Vec element type: expected Named or Own(Named), got {other:?}"
            )))
        }
    };
    named
        .first()
        .cloned()
        .ok_or_else(|| LowerError::InternalError(format!("Vec type has no type args: {ty:?}")))
}

/// Resolve BinOp + operand type to PrimOp.
pub(super) fn resolve_binop(op: &BinOp, operand_ty: &Type) -> Result<PrimOp, LowerError> {
    let operand_ty = strip_own(operand_ty);
    match (op, operand_ty) {
        (BinOp::Add, Type::Int) => Ok(PrimOp::AddInt),
        (BinOp::Add, Type::Float) => Ok(PrimOp::AddFloat),
        (BinOp::Add, Type::String) => Ok(PrimOp::ConcatString),
        (BinOp::Sub, Type::Int) => Ok(PrimOp::SubInt),
        (BinOp::Sub, Type::Float) => Ok(PrimOp::SubFloat),
        (BinOp::Mul, Type::Int) => Ok(PrimOp::MulInt),
        (BinOp::Mul, Type::Float) => Ok(PrimOp::MulFloat),
        (BinOp::Div, Type::Int) => Ok(PrimOp::DivInt),
        (BinOp::Div, Type::Float) => Ok(PrimOp::DivFloat),
        // Comparison ops (Eq/Neq/Lt/Le/Gt/Ge) are desugared to trait calls in lower_trait_comparison.
        // And/Or handled as Switch in lower_expr (short-circuit semantics).
        _ => Err(LowerError::UnsupportedOp(format!(
            "{op:?} on {operand_ty:?}"
        ))),
    }
}

/// Resolve UnaryOp + operand type to PrimOp.
pub(super) fn resolve_unaryop(op: &UnaryOp, operand_ty: &Type) -> Result<PrimOp, LowerError> {
    let operand_ty = strip_own(operand_ty);
    match (op, operand_ty) {
        (UnaryOp::Neg, Type::Int) => Ok(PrimOp::NegInt),
        (UnaryOp::Neg, Type::Float) => Ok(PrimOp::NegFloat),
        (UnaryOp::Not, _) => Ok(PrimOp::Not),
        _ => Err(LowerError::UnsupportedOp(format!(
            "{op:?} on {operand_ty:?}"
        ))),
    }
}
