// Lowering context: the shared mutable state every IR-lowering method
// reads and writes. Co-located here with all internal types it references
// (let-binding rows, ANF results, pattern-matrix rows, scope trackers,
// auto-close plans) plus a `#[cfg(test)] mod tests` that constructs the
// context by field literal.

use rustc_hash::FxHashMap;
#[cfg(test)]
use rustc_hash::FxHashSet;
use std::rc::Rc;

use krypton_parser::ast::Span;
use krypton_typechecker::typed_ast::{
    AutoCloseInfo, QualifiedName, ResolvedTypeRef, ResolvedVariantRef, ScopeId, TraitName,
    TypedExpr, TypedPattern,
};
use krypton_typechecker::types::{self as types, Type, TypeScheme, TypeVarGen, TypeVarId};

use crate::Type as IrType;
use crate::{Atom, Expr, FinallyClose, FnDef, FnId, SimpleExpr, VarId};

// ---------------------------------------------------------------------------
// Helper: intermediate let-binding produced during ANF normalization
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub(super) struct LetBinding {
    pub(super) bind: VarId,
    pub(super) ty: IrType,
    pub(super) value: SimpleExpr,
}

/// Result of trying to lower a value expression.
pub(super) enum LoweredValue {
    /// A SimpleExpr with prefix bindings (for atomic/call/primop values).
    Simple(Vec<LetBinding>, SimpleExpr),
    /// A full Expr tree (for If, Do, nested Let).
    Expr(Expr),
}

/// Cached analysis of a `try_project_superclass_dict` request. Stores the
/// dict param to start from and the sequence of hops (direct-superclass
/// field indices + substituted target types) needed to reach the
/// requested trait. `VarId` allocation still happens per-call in
/// `emit_superclass_projection` so IR output is byte-identical whether
/// the cache hits or misses.
#[derive(Debug, Clone)]
pub(super) struct SuperclassProjectionPlan {
    pub(super) start_var: VarId,
    pub(super) hops: Vec<SuperclassProjectionHop>,
}

#[derive(Debug, Clone)]
pub(super) struct SuperclassProjectionHop {
    pub(super) field_index: usize,
    pub(super) next_trait: TraitName,
    pub(super) next_args: Vec<IrType>,
}

/// Extracted info about a parameterized trait instance (for dict construction).
#[derive(Clone)]
pub(super) struct ParamInstanceInfo {
    pub(super) trait_name: TraitName,
    /// Type arguments. Length 1 for single-parameter traits; N for multi-parameter.
    pub(super) target_types: Vec<Type>,
    /// Sub-dict requirements for this instance: superclass slots first
    /// (trait-wide layout, with targets substituted from the descendant's
    /// `target_types`), then impl-head constraints. Targets are IR-level
    /// types so parameterized superclass targets like `Semigroup[Vec[a]]`
    /// survive here as `[Named("Vec", [Var(a)])]`; see
    /// `InstanceDef::sub_dict_requirements`.
    pub(super) constraints: Vec<(TraitName, Vec<IrType>)>,
    pub(super) source_module: String, // module defining this instance
    pub(super) target_type_name: String, // for building CanonicalRef
}

/// Source info for all instances (concrete and parameterized), used to
/// resolve instance CanonicalRefs during GetDict emission.
pub(super) struct InstanceSourceInfo {
    pub(super) trait_name: TraitName,
    /// Type arguments. May contain type vars for parameterized instances.
    pub(super) target_types: Vec<Type>,
    pub(super) target_type_name: String, // type_to_canonical_name output
    pub(super) source_module: String,
}

/// Per-decl FnId allocation info captured during `allocate_fn_ids` and
/// consumed by `lower_function_bodies`. Keeps overload siblings paired with
/// their resolved parameter and return types so the body-lowering pass does
/// not need to re-scan `fn_types` by name (which would collapse overloads).
pub(super) struct LocalFnAlloc {
    pub(super) fn_id: FnId,
    pub(super) param_types: Vec<Type>,
    pub(super) return_type: Type,
}

// ---------------------------------------------------------------------------
// Pattern match compilation types
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub(super) struct ClausePayload {
    pub(super) guard: Option<Box<TypedExpr>>,
    pub(super) body: TypedExpr,
}

/// A clause in the pattern matrix: a structural row plus shared RHS payload.
#[derive(Clone)]
pub(super) struct Clause {
    pub(super) patterns: Vec<TypedPattern>,
    pub(super) payload: Rc<ClausePayload>,
    /// Bindings accumulated during specialization for Var patterns that were
    /// expanded to wildcards. Each entry is (name, scrutinee_atom, type).
    pub(super) extra_bindings: Vec<(String, Atom, Type)>,
}

impl Clause {
    pub(super) fn guard(&self) -> Option<&TypedExpr> {
        self.payload.guard.as_deref()
    }

    pub(super) fn body(&self) -> &TypedExpr {
        &self.payload.body
    }

    pub(super) fn span(&self) -> Span {
        self.payload.body.span
    }
}

/// What kind of head constructors appear in a column.
pub(super) enum ColumnKind {
    Constructor,
    Literal,
    Tuple(usize),
    Struct(String),
}

// ---------------------------------------------------------------------------
// Auto-close support types
// ---------------------------------------------------------------------------

/// Whether emitting an AutoClose should null the resource's slot after the
/// close call. Used to unify the "normal path after scope exit" case
/// (`NullSlot` — fn-wide finally handler skips the already-closed slot)
/// with the "early-return / question-mark" case (`Keep` — slot stays
/// alive for any later handlers).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CloseMode {
    Keep,
    NullSlot,
}

impl CloseMode {
    pub(super) fn null_slot(self) -> bool {
        matches!(self, CloseMode::NullSlot)
    }
}

/// Pre-resolved auto-close info for a single binding.
pub(super) struct ResolvedClose {
    #[allow(dead_code)]
    pub(super) trait_name: TraitName,
    pub(super) binding_var: VarId,
    pub(super) type_name: String,
    pub(super) dict_bindings: Vec<LetBinding>,
    pub(super) dict_atom: Atom,
}

/// One level of scope tracking for block-scoped resource auto-close.
/// Created on `enter_scope(scope_id)` and drained by
/// `exit_scope(scope_id, body)`. Identity is the stable `ScopeId`
/// allocated by the typechecker's `scope_ids` pre-pass, not the span.
pub(super) struct ScopeTrack {
    pub(super) scope_id: ScopeId,
    /// Expected resource names (in scope_exits LIFO order) → type_name.
    pub(super) expected: Vec<(String, String)>,
    /// VarIds resolved for each expected name, recorded via push_var.
    pub(super) resolved: FxHashMap<String, VarId>,
}

// ---------------------------------------------------------------------------
// Lowering context
// ---------------------------------------------------------------------------

/// Per-trait method signature info: (type_var_id, method_name → (param_types, return_type)).
/// `param_types` carries `ParamMode` alongside each parameter type so the mode flows
/// from `TraitMethod` through `TraitDefInfo` into IR; IR itself still strips modes at
/// point of use (see consumer sites below).
pub(super) type TraitMethodTypeInfo = (
    Vec<TypeVarId>,
    FxHashMap<String, (Vec<(types::ParamMode, Type)>, Type)>,
);
pub(super) type TraitConstraintInfo = (TraitName, Vec<TypeVarId>);
pub(super) type TraitConstraintList = Vec<TraitConstraintInfo>;
pub(super) type TraitMethodConstraintInfo = FxHashMap<String, TraitConstraintList>;

/// Sub-dict requirements on `InstanceDef`: superclass slots + impl-head
/// constraints, where each slot's target positions carry full substituted
/// types (not just type-var ids). A parameterized superclass target like
/// `Semigroup[Vec[a]]` records `[IrType::Named("Vec", [Var(a)])]` so the
/// type info survives to codegen.
pub(super) type InstanceSubDictList = Vec<(TraitName, Vec<IrType>)>;

pub(super) struct LowerCtx<'a> {
    /// Link-context view for the module being lowered. Source of trait
    /// metadata (direct + transitive superclasses, trait type param ids).
    /// Scope-filtered instances are still read through its `all_instances`
    /// accessor during ctx construction.
    pub(super) link_view: &'a krypton_typechecker::link_context::ModuleLinkView<'a>,
    pub(super) next_var: u32,
    pub(super) next_fn: u32,
    /// For generating TypeVarIds for private type definitions
    pub(super) type_var_gen: TypeVarGen,
    /// name → stack of VarIds (supports nested scopes)
    pub(super) var_scope: FxHashMap<String, Vec<VarId>>,
    /// top-level function name → overload candidates. Most names map to a
    /// singleton vec; names with top-level overloading (e.g. two `push`
    /// overloads in core/vec) map to multiple entries. The key in each tuple
    /// is a canonical parameter-type list (ParamMode stripped, polymorphic
    /// vars preserved) used with `types_overlap` to disambiguate. Lifted
    /// synthetics have unique names and carry an empty key.
    pub(super) fn_ids: FxHashMap<String, Vec<(Vec<Type>, FnId)>>,
    /// Canonical qualified name → overload candidates. Mirrors `fn_ids` but
    /// keyed by the fully qualified name. Same shape/rules.
    pub(super) callable_ids: FxHashMap<QualifiedName, Vec<(Vec<Type>, FnId)>>,
    /// Resolved type ref → ordered fields with resolved types
    pub(super) struct_fields: FxHashMap<ResolvedTypeRef, Vec<(String, Type)>>,
    /// Resolved type ref → ordered declared type-parameter vars. Paired with
    /// `struct_fields`: each entry's `TypeVarId`s are the vars the field types
    /// reference. Used to substitute actual type arguments into field types
    /// when lowering uses at a concrete type (record construction, struct
    /// update, struct-pattern projection).
    pub(super) struct_type_params: FxHashMap<ResolvedTypeRef, Vec<TypeVarId>>,
    /// Resolved variant ref → (tag, field_types)
    pub(super) sum_variants: FxHashMap<ResolvedVariantRef, (u32, Vec<Type>)>,
    /// Cached type_params for private types (avoids double build_type_param_map)
    pub(super) private_type_params: FxHashMap<String, Vec<TypeVarId>>,
    /// qualified name → [(trait_name, type_vars)] — required trait dicts
    pub(super) fn_constraints: FxHashMap<QualifiedName, TraitConstraintList>,
    /// (trait_name, type_vars) → VarId — dict param variables for the current function
    pub(super) dict_params: FxHashMap<(TraitName, Vec<TypeVarId>), VarId>,
    /// Cache for `try_project_superclass_dict`: `requested_trait → requested
    /// target TypeVarIds → analysis result`. `None` caches a negative result
    /// (no in-scope dict produces the requested superclass). Emission still
    /// allocates fresh VarIds per call so IR output is byte-identical.
    /// Nested rather than tuple-keyed so lookups can borrow
    /// `&[TypeVarId]` and avoid cloning the key on the hot path (the original
    /// scan over `dict_params` did not allocate per call).
    /// Cleared at `lower_fn` entry and swap/restored across `lower_lambda`
    /// alongside `dict_params` (they share the same invalidation points).
    pub(super) superclass_projection_cache:
        FxHashMap<TraitName, FxHashMap<Vec<TypeVarId>, Option<SuperclassProjectionPlan>>>,
    /// qualified name → TypeScheme for resolving type var bindings at call sites
    pub(super) fn_schemes: FxHashMap<QualifiedName, TypeScheme>,
    /// Instance defs for parameterized dict resolution:
    /// (trait_name, target_type, type_var_ids, constraints)
    pub(super) param_instances: Vec<ParamInstanceInfo>,
    /// trait_name → (type_var_id, method_name → (param_types, return_type))
    pub(super) trait_method_types: FxHashMap<TraitName, TraitMethodTypeInfo>,
    /// trait_name → method_name → required trait dicts for method-level where constraints
    pub(super) trait_method_constraints: FxHashMap<TraitName, TraitMethodConstraintInfo>,
    /// Recursion depth counter for dict resolution (cycle detection)
    pub(super) dict_depth: u32,
    /// Lifted lambda definitions accumulated during lowering
    pub(super) lifted_fns: Vec<FnDef>,
    /// VarId → Type, populated at binding sites for capture type lookups
    pub(super) var_types: FxHashMap<VarId, Type>,
    /// Join point for `recur` jumps in the current function
    pub(super) recur_join: Option<(VarId, Vec<VarId>)>,
    /// Join point for `?` early returns in the current function
    pub(super) early_return_join: Option<VarId>,
    /// Auto-close info from the typechecker
    pub(super) auto_close: AutoCloseInfo,
    /// Active block-scope tracking stack. Each entry records the scope's span,
    /// the names it expects to bind (→ type_name), and VarIds resolved for
    /// those names as push_var runs inside the scope. On scope exit we drain
    /// the entry and emit close+null for each resolved binding.
    pub(super) scope_track_stack: Vec<ScopeTrack>,
    /// All block-scoped disposables bound within the current function. These
    /// accumulate into fn_exit_closes at function end so the function-wide
    /// finally handler pre-allocates slots and handles exception unwinds.
    pub(super) fn_block_scoped_closes: Vec<FinallyClose>,
    /// Accumulated fn_exit_closes for the module (FnId → disposables to close on unwind).
    /// Keyed by FnId so overload siblings track independently.
    pub(super) fn_exit_closes: FxHashMap<FnId, Vec<FinallyClose>>,
    /// Module path of the module being lowered (for filtering local dict refs).
    pub(super) module_path: String,
    /// All known instances with source module and target type info,
    /// for resolving instance CanonicalRefs during GetDict/MakeDict emission.
    pub(super) all_instances: Vec<InstanceSourceInfo>,
    /// (trait_local_name, canonical_type_name) → index into all_instances.
    /// Fast path for exact-match instance resolution; parameterized instances
    /// fall through to the linear structural scan.
    pub(super) instance_exact_index: FxHashMap<(String, String), usize>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::LowerError;
    use krypton_parser::ast::{Lit, ParamMode};
    use krypton_typechecker::link_context::ModuleLinkView;
    use krypton_typechecker::module_interface::{ModuleInterface, ModulePath as LinkModulePath};
    use krypton_typechecker::typed_ast::TypedExprKind;

    /// Build a minimal [`LowerCtx`] sufficient to drive `resolve_call_dicts`
    /// into its `bind_type_vars` path. Unused subsystems are left empty.
    fn empty_ctx<'a>(link_view: &'a ModuleLinkView<'a>) -> LowerCtx<'a> {
        LowerCtx {
            link_view,
            next_var: 0,
            next_fn: 0,
            type_var_gen: TypeVarGen::new(),
            var_scope: FxHashMap::default(),
            fn_ids: FxHashMap::default(),
            callable_ids: FxHashMap::default(),
            struct_fields: FxHashMap::default(),
            struct_type_params: FxHashMap::default(),
            sum_variants: FxHashMap::default(),
            private_type_params: FxHashMap::default(),
            fn_constraints: FxHashMap::default(),
            dict_params: FxHashMap::default(),
            superclass_projection_cache: FxHashMap::default(),
            fn_schemes: FxHashMap::default(),
            param_instances: Vec::new(),
            trait_method_types: FxHashMap::default(),
            trait_method_constraints: FxHashMap::default(),
            dict_depth: 0,
            lifted_fns: Vec::new(),
            var_types: FxHashMap::default(),
            recur_join: None,
            early_return_join: None,
            auto_close: AutoCloseInfo::default(),
            scope_track_stack: Vec::new(),
            fn_block_scoped_closes: Vec::new(),
            fn_exit_closes: FxHashMap::default(),
            module_path: "test".to_string(),
            all_instances: Vec::new(),
            instance_exact_index: FxHashMap::default(),
        }
    }

    /// Single-module LinkContext for tests that only need a view to satisfy
    /// the `LowerCtx.link_view` field — no traits/instances required.
    fn test_link_ctx() -> krypton_typechecker::link_context::LinkContext {
        let iface = ModuleInterface {
            module_path: LinkModulePath::new("test"),
            direct_deps: vec![],
            exported_fns: vec![],
            reexported_fns: vec![],
            exported_types: vec![],
            reexported_types: vec![],
            exported_traits: vec![],
            exported_instances: vec![],
            extern_types: vec![],
            exported_fn_qualifiers: FxHashMap::default(),
            type_visibility: FxHashMap::default(),
            private_names: FxHashSet::default(),
            private_fns: vec![],
            private_types: vec![],
            private_friend_module: None,
        };
        krypton_typechecker::link_context::LinkContext::build(vec![iface])
    }

    fn typed_expr(ty: Type) -> TypedExpr {
        TypedExpr {
            kind: TypedExprKind::Lit(Lit::Unit),
            ty,
            span: (0, 0),
            resolved_ref: None,
            scope_id: None,
        }
    }

    #[test]
    fn resolve_call_dicts_conflict_is_internal_error() {
        let link_ctx = test_link_ctx();
        let view = link_ctx.view_for(&LinkModulePath::new("test")).unwrap();
        let mut ctx = empty_ctx(&view);
        let tv = ctx.type_var_gen.fresh();
        let qn = QualifiedName::new("test".into(), "f".into());
        let trait_name = TraitName::new("test".into(), "T".into());

        // Scheme: fn f[a](x: a, y: a) -> Unit where T[a]
        // A call with args (Int, String) asks bind_type_vars to bind `a` twice
        // to incompatible types — the exact regression the ICE guard catches.
        let scheme = TypeScheme {
            vars: vec![tv],
            constraints: vec![(trait_name.clone(), vec![tv])],
            ty: Type::Fn(
                vec![
                    (ParamMode::Consume, Type::Var(tv)),
                    (ParamMode::Consume, Type::Var(tv)),
                ],
                Box::new(Type::Unit),
            ),
            var_names: FxHashMap::default(),
        };
        ctx.fn_schemes.insert(qn.clone(), scheme);
        ctx.fn_constraints
            .insert(qn.clone(), vec![(trait_name, vec![tv])]);

        let args = vec![typed_expr(Type::Int), typed_expr(Type::String)];

        let err = match ctx.resolve_call_dicts(&qn, &args, &[], None) {
            Err(e) => e,
            Ok(_) => panic!("conflicting bindings must raise LowerError"),
        };
        let msg = match err {
            LowerError::InternalError(m) => m,
            other => panic!("expected InternalError, got {other:?}"),
        };
        assert!(
            msg.contains("bind conflict"),
            "message must name the failure mode: {msg}"
        );
        let tv_debug = format!("{:?}", tv);
        assert!(
            msg.contains(&tv_debug),
            "message must name the offending var ({tv_debug}): {msg}"
        );
        assert!(
            msg.contains("Int"),
            "message must name existing binding: {msg}"
        );
        assert!(
            msg.contains("String"),
            "message must name proposed binding: {msg}"
        );
    }
}
