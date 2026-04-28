// Lowering pass: TypedExpr → IR. Module-scoped state lives in `ctx::LowerCtx`
// (with internal types and tests in `ctx`); free helpers in `util` and
// `module_pipeline`. The `LowerCtx` impl block is reopened across one file
// per conceptual chunk:
//
//   - register      — `LowerCtx::new` + struct/sum-variant/fn-id registration
//   - scope         — variable scoping, lookup, auto-close emission
//   - anf           — ANF construction (atom/simple/compound bridges)
//   - expr          — `lower_expr` dispatcher + per-`TypedExprKind` lowering
//   - patmat        — pattern-match clause-matrix compilation
//   - control       — do blocks, short-circuit, trait-routed primitives
//   - call          — function application, struct lit, struct update
//   - dict          — trait dictionary resolution and superclass projection
//   - lambda_fn     — `lower_lambda` (closure conversion) and `lower_fn`
//
// The public surface is just `lower_module`, `lower_all`, and `LowerError`.

mod anf;
mod bind;
mod call;
mod control;
mod ctx;
mod dict;
mod expr;
mod lambda_fn;
mod module_pipeline;
mod op_resolve;
mod patmat;
mod register;
mod resolved;
mod scope;
mod type_expr;
mod util;

pub use module_pipeline::{lower_all, lower_module};

#[derive(Debug)]
pub enum LowerError {
    NotYetLowered(String),
    UnresolvedVar(String),
    UnresolvedStruct(String),
    UnresolvedField(String, String),
    UnsupportedOp(String),
    CompoundInAtom,
    InternalError(String),
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::NotYetLowered(s) => write!(f, "not yet lowered: {s}"),
            LowerError::UnresolvedVar(s) => write!(f, "unresolved variable: {s}"),
            LowerError::UnresolvedStruct(s) => write!(f, "unresolved struct: {s}"),
            LowerError::UnresolvedField(t, field) => {
                write!(f, "unresolved field {field} on {t}")
            }
            LowerError::UnsupportedOp(s) => write!(f, "unsupported op: {s}"),
            LowerError::CompoundInAtom => write!(f, "compound expression in atom position"),
            LowerError::InternalError(s) => write!(f, "internal error: {s}"),
        }
    }
}
