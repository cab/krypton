use krypton_parser::ast::Span;

use crate::types::{format_type_with_var_map, renumber_types_for_display, ParamMode, Type, TypeVarId};
use std::collections::HashMap;
use std::fmt;

/// Human-readable label for a parameter mode.
fn mode_label(m: ParamMode) -> &'static str {
    match m {
        ParamMode::Consume => "consume (`~T`)",
        ParamMode::Borrow => "borrow (`&~T`)",
    }
}

/// Check if the infinite type is just an ownership wrapper around the variable itself,
/// e.g. `a` vs `~a`. This is not a genuine recursive type — it's an ownership mismatch.
pub(crate) fn is_own_wrapper_of(var: TypeVarId, ty: &Type) -> bool {
    match ty {
        Type::Own(inner) | Type::MaybeOwn(_, inner) => {
            matches!(inner.as_ref(), Type::Var(v) if *v == var)
        }
        _ => false,
    }
}

/// Error codes for type errors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeErrorCode {
    E0001, // Type mismatch
    E0002, // Duplicate type
    E0003, // Unknown variable
    E0004, // Not a function
    E0005, // Wrong arity
    E0006, // Non-exhaustive match
    E0007, // Infinite type
    E0008, // Unknown field
    E0009, // Missing fields
    E0010, // Not a struct
    E0101, // Value already moved
    E0102, // Value may have been moved in a branch
    E0103, // Capture of moved value
    E0104, // Qualifier mismatch
    E0301, // No trait instance
    E0302, // Orphan / duplicate instance
    E0303, // Missing superclass instance
    E0304, // Cannot derive trait (field missing required instance)
    E0305, // Definition conflicts with trait method
    E0306, // Invalid impl method set
    E0011, // Unknown type
    E0401, // ? in function not returning Result or Option
    E0402, // ? on non-Result/Option
    E0403, // ? cross-use (Option in Result context or vice versa)
    E0501, // Unknown module
    E0502, // Circular import
    E0503, // Private name in import
    E0504, // Bare import (no selective names)
    E0505, // Cannot re-export name (not in scope or private)
    E0506, // Parse error in imported module
    E0507, // Kind mismatch (type applied with wrong number of type args)
    E0508, // Unknown qualified export
    E0105, // Disposable branch leak (consumed in some branches but not all)
    E0106, // Qualifier bound violation (shared + ~T)
    E0012, // Reserved name
    E0509, // Duplicate import name (same name from different modules)
    E0510, // Unknown export (name does not exist in module)
    E0013, // Redundant match arm
    E0015, // Duplicate constructor across types (value namespace)
    E0016, // Type/trait name collision (type namespace)
    E0318, // Duplicate trait (type namespace)
    E0511, // Wildcard not allowed in this position
    E0512, // Nested wildcard in impl head
    E0307, // Unknown trait
    E0308, // Self outside impl block
    E0309, // Duplicate instance
    E0310, // Missing pub type annotation
    E0311, // Trait method collision
    E0312, // Missing trait bound
    E0313, // Ambiguous trait name
    E0314, // Ambiguous type (could not infer trait dispatch type)
    E0315, // Missing return type annotation on trait method
    E0602, // Invalid @nullable return type
    E0513, // Definition conflicts with explicit import
    E0514, // Duplicate function definition
    E0316, // Cannot implement trait for owned type
    E0014, // Or-pattern binding mismatch
    E0603, // Invalid @throws return type
    E0604, // Extern trait on JS target (Java-only feature)
    E0605, // Invalid @instance first param
    E0606, // Invalid @constructor return type
    E0607, // @instance + @constructor conflict
    E0608, // @constructor with self param
    E0609, // @instance/@constructor on JS target
    E0107, // Owned value consumed in match guard
    E0108, // Linear `~T` value not consumed before scope exit (T not Disposable)
    E0610, // Duplicate parameter name
    E0611, // Function-type parameter mode mismatch (consume vs borrow)
    E0317, // Unsupported trait constraint shape (e.g. multi-parameter)
}

/// Why a linear `~T` binding was flagged as unconsumed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeakReason {
    /// Binding reached the end of its enclosing scope without being consumed.
    ScopeExit,
    /// Binding was consumed in some branches of an if/match but not others.
    BranchMissing,
    /// Binding was live when `recur` jumped back to the loop head.
    RecurBack,
    /// Binding was live at a `?` early-return point.
    EarlyReturnViaQuestion,
}

impl fmt::Display for TypeErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// Errors that can occur during type unification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    Mismatch {
        expected: Type,
        actual: Type,
    },
    InfiniteType {
        var: TypeVarId,
        ty: Type,
    },
    WrongArity {
        expected: usize,
        actual: usize,
    },
    UnknownVariable {
        name: String,
    },
    NotAFunction {
        actual: Type,
    },
    DuplicateType {
        name: String,
    },
    DuplicateConstructor {
        name: String,
        first_type: String,
        second_type: String,
    },
    DuplicateTrait {
        name: String,
    },
    TypeTraitNameConflict {
        name: String,
    },
    UnknownField {
        type_name: String,
        field_name: String,
    },
    MissingFields {
        type_name: String,
        fields: Vec<String>,
    },
    NotAStruct {
        actual: Type,
    },
    NonExhaustive {
        missing: Vec<String>,
    },
    AlreadyMoved {
        name: String,
    },
    MovedInBranch {
        name: String,
    },
    CapturedMoved {
        name: String,
    },
    QualifierMismatch {
        name: String,
        callee: String,
        param: String,
    },
    OwnershipMismatch {
        expected: Type,
        actual: Type,
    },
    UnsupportedExpr {
        description: String,
    },
    ConstrainedFunctionRef {
        name: String,
        constraints: Vec<(String, String)>, // (trait_name, type_param_name)
    },
    NoInstance {
        trait_name: String,
        ty: String,
        required_by: Option<String>,
    },
    OrphanInstance {
        trait_name: String,
        ty: String,
        /// Modules that were consulted during the orphan check (trait module +
        /// each type argument's defining module). Empty when the check wasn't
        /// performed (e.g. well-formedness failure before orphan resolution).
        modules_checked: Vec<String>,
    },
    OwnedTypeImpl {
        trait_name: String,
        ty: String,
    },
    DuplicateInstance {
        trait_name: String,
        ty: String,
        existing_ty: String,
    },
    CannotDerive {
        trait_name: String,
        type_name: String,
        field_type: String,
    },
    DefinitionConflictsWithTraitMethod {
        def_name: String,
        trait_name: String,
    },
    InvalidImpl {
        trait_name: String,
        target_type: String,
        missing_methods: Vec<String>,
        extra_methods: Vec<String>,
    },
    UnknownType {
        name: String,
        suggestion: Option<String>,
        variant_of: Option<String>,
        is_value: bool,
    },
    QuestionMarkBadReturn {
        actual: Type,
    },
    QuestionMarkBadOperand {
        actual: Type,
    },
    QuestionMarkMismatch {
        expr_kind: String,
        return_kind: String,
    },
    UnknownModule {
        path: String,
    },
    CircularImport {
        cycle: Vec<String>,
    },
    PrivateName {
        name: String,
        module_path: String,
    },
    BareImport {
        path: String,
    },
    ModuleQualifierUsedAsValue {
        qualifier: String,
        suggested_usage: Option<String>,
    },
    UnknownQualifiedExport {
        qualifier: String,
        module_path: String,
        name: String,
    },
    PrivateReexport {
        name: String,
    },
    ModuleParseError {
        path: String,
        errors: Vec<String>,
    },
    KindMismatch {
        type_name: String,
        expected_arity: usize,
        actual_arity: usize,
    },
    DisposableBranchLeak {
        name: String,
        type_name: String,
    },
    ReservedName {
        name: String,
    },
    QualifierBoundViolation {
        type_var: String,
        param_name: String,
    },
    DuplicateImport {
        name: String,
        modules: Vec<String>,
    },
    UnknownExport {
        name: String,
        module_path: String,
    },
    RedundantPattern,
    WildcardNotAllowed {
        span: Span,
    },
    NestedWildcard {
        span: Span,
    },
    UnknownTrait {
        name: String,
    },
    SelfOutsideImpl,
    MissingPubAnnotation {
        fn_name: String,
        missing: Vec<String>,
    },
    MissingTraitMethodAnnotation {
        trait_name: String,
        method_name: String,
    },
    TraitMethodCollision {
        method_name: String,
        trait1: String,
        trait2: String,
    },
    MissingTraitBound {
        fn_name: String,
        trait_name: String,
        type_var: Option<String>,
    },
    AmbiguousTraitName {
        name: String,
        existing_module: String,
        new_module: String,
    },
    InvalidNullableReturn {
        name: String,
        actual_return_type: Type,
    },
    InvalidThrowsReturn {
        name: String,
        actual_return_type: Type,
    },
    AmbiguousType {
        trait_name: String,
        method_name: String,
    },
    /// A multi-parameter trait method call left one or more trait type
    /// parameters unresolved after the deferral solver finished. Reported
    /// under E0301 (NoInstance / unresolved instance).
    UnresolvedMultiParamConstraint {
        trait_name: String,
        params: Vec<String>,
    },
    DefinitionConflictsWithImport {
        def_name: String,
        source_module: String,
    },
    DuplicateFunction {
        name: String,
    },
    DuplicateParam {
        name: String,
    },
    OrPatternBindingMismatch {
        alt_index: usize,
        expected_names: Vec<String>,
        actual_names: Vec<String>,
    },
    ExternTraitOnJsTarget {
        name: String,
    },
    InvalidInstanceFirstParam {
        name: String,
        expected_type: String,
    },
    InvalidConstructorReturn {
        name: String,
        expected_type: String,
        actual_return_type: Type,
    },
    InstanceConstructorConflict {
        name: String,
    },
    ConstructorWithSelf {
        name: String,
    },
    InstanceConstructorOnJsTarget {
        name: String,
    },
    MovedInGuard {
        name: String,
    },
    QualifierConflict {
        existing: String,
        incoming: String,
    },
    /// `~fn` (single-use closure) used where bare `fn` (multi-use function)
    /// is expected. Specialized form of ownership mismatch in the coerce path:
    /// a single-use closure cannot satisfy a multi-use function slot.
    FnCapabilityMismatch {
        expected: Type,
        actual: Type,
    },
    /// Function-type slot mode mismatch: `(~T) -> U` vs `(&~T) -> U`.
    /// Consume and borrow are distinct per-slot capabilities and do not
    /// adapt to each other; unification must compare modes structurally.
    ParamModeMismatch {
        expected: Type,
        actual: Type,
        param_index: usize,
        expected_mode: ParamMode,
        actual_mode: ParamMode,
    },
    /// A `~T` binding was never consumed before reaching a function exit
    /// point, and `T` does not implement `Disposable` (so auto-close
    /// cannot synthesize a dispose call).
    LinearValueNotConsumed {
        name: String,
        type_name: String,
        reason: LeakReason,
        /// Optional hint for an explicit-consume function the user could
        /// call, e.g. `"free"` → renders as `free(x)`.
        consume_hint: Option<String>,
    },
    UnsupportedConstraint {
        trait_name: String,
        reason: &'static str,
    },
}

impl TypeError {
    /// Return the error code for this error.
    pub fn error_code(&self) -> TypeErrorCode {
        match self {
            TypeError::Mismatch { .. } => TypeErrorCode::E0001,
            TypeError::DuplicateType { .. } => TypeErrorCode::E0002,
            TypeError::DuplicateConstructor { .. } => TypeErrorCode::E0015,
            TypeError::TypeTraitNameConflict { .. } => TypeErrorCode::E0016,
            TypeError::DuplicateTrait { .. } => TypeErrorCode::E0318,
            TypeError::UnknownVariable { .. } => TypeErrorCode::E0003,
            TypeError::NotAFunction { .. } => TypeErrorCode::E0004,
            TypeError::WrongArity { .. } => TypeErrorCode::E0005,
            TypeError::InfiniteType { .. } => TypeErrorCode::E0007,
            TypeError::UnknownField { .. } => TypeErrorCode::E0008,
            TypeError::MissingFields { .. } => TypeErrorCode::E0009,
            TypeError::NotAStruct { .. } => TypeErrorCode::E0010,
            TypeError::NonExhaustive { .. } => TypeErrorCode::E0006,
            TypeError::AlreadyMoved { .. } => TypeErrorCode::E0101,
            TypeError::MovedInBranch { .. } => TypeErrorCode::E0102,
            TypeError::CapturedMoved { .. } => TypeErrorCode::E0103,
            TypeError::QualifierMismatch { .. } => TypeErrorCode::E0104,
            TypeError::OwnershipMismatch { .. } => TypeErrorCode::E0104,
            TypeError::UnsupportedExpr { .. } => TypeErrorCode::E0001,
            TypeError::ConstrainedFunctionRef { .. } => TypeErrorCode::E0001,
            TypeError::NoInstance {
                required_by: None, ..
            } => TypeErrorCode::E0301,
            TypeError::NoInstance {
                required_by: Some(_),
                ..
            } => TypeErrorCode::E0303,
            TypeError::OrphanInstance { .. } => TypeErrorCode::E0302,
            TypeError::OwnedTypeImpl { .. } => TypeErrorCode::E0316,
            TypeError::DuplicateInstance { .. } => TypeErrorCode::E0309,
            TypeError::CannotDerive { .. } => TypeErrorCode::E0304,
            TypeError::DefinitionConflictsWithTraitMethod { .. } => TypeErrorCode::E0305,
            TypeError::InvalidImpl { .. } => TypeErrorCode::E0306,
            TypeError::UnknownType { .. } => TypeErrorCode::E0011,
            TypeError::QuestionMarkBadReturn { .. } => TypeErrorCode::E0401,
            TypeError::QuestionMarkBadOperand { .. } => TypeErrorCode::E0402,
            TypeError::QuestionMarkMismatch { .. } => TypeErrorCode::E0403,
            TypeError::UnknownModule { .. } => TypeErrorCode::E0501,
            TypeError::CircularImport { .. } => TypeErrorCode::E0502,
            TypeError::PrivateName { .. } => TypeErrorCode::E0503,
            TypeError::BareImport { .. } => TypeErrorCode::E0504,
            TypeError::ModuleQualifierUsedAsValue { .. } => TypeErrorCode::E0504,
            TypeError::UnknownQualifiedExport { .. } => TypeErrorCode::E0508,
            TypeError::PrivateReexport { .. } => TypeErrorCode::E0505,
            TypeError::ModuleParseError { .. } => TypeErrorCode::E0506,
            TypeError::KindMismatch { .. } => TypeErrorCode::E0507,
            TypeError::DisposableBranchLeak { .. } => TypeErrorCode::E0105,
            TypeError::QualifierBoundViolation { .. } => TypeErrorCode::E0106,
            TypeError::ReservedName { .. } => TypeErrorCode::E0012,
            TypeError::DuplicateImport { .. } => TypeErrorCode::E0509,
            TypeError::UnknownExport { .. } => TypeErrorCode::E0510,
            TypeError::RedundantPattern => TypeErrorCode::E0013,
            TypeError::WildcardNotAllowed { .. } => TypeErrorCode::E0511,
            TypeError::NestedWildcard { .. } => TypeErrorCode::E0512,
            TypeError::UnknownTrait { .. } => TypeErrorCode::E0307,
            TypeError::SelfOutsideImpl => TypeErrorCode::E0308,
            TypeError::MissingPubAnnotation { .. } => TypeErrorCode::E0310,
            TypeError::MissingTraitMethodAnnotation { .. } => TypeErrorCode::E0315,
            TypeError::TraitMethodCollision { .. } => TypeErrorCode::E0311,
            TypeError::MissingTraitBound { .. } => TypeErrorCode::E0312,
            TypeError::AmbiguousTraitName { .. } => TypeErrorCode::E0313,
            TypeError::InvalidNullableReturn { .. } => TypeErrorCode::E0602,
            TypeError::InvalidThrowsReturn { .. } => TypeErrorCode::E0603,
            TypeError::AmbiguousType { .. } => TypeErrorCode::E0314,
            TypeError::UnresolvedMultiParamConstraint { .. } => TypeErrorCode::E0301,
            TypeError::DefinitionConflictsWithImport { .. } => TypeErrorCode::E0513,
            TypeError::DuplicateFunction { .. } => TypeErrorCode::E0514,
            TypeError::DuplicateParam { .. } => TypeErrorCode::E0610,
            TypeError::OrPatternBindingMismatch { .. } => TypeErrorCode::E0014,
            TypeError::ExternTraitOnJsTarget { .. } => TypeErrorCode::E0604,
            TypeError::InvalidInstanceFirstParam { .. } => TypeErrorCode::E0605,
            TypeError::InvalidConstructorReturn { .. } => TypeErrorCode::E0606,
            TypeError::InstanceConstructorConflict { .. } => TypeErrorCode::E0607,
            TypeError::ConstructorWithSelf { .. } => TypeErrorCode::E0608,
            TypeError::InstanceConstructorOnJsTarget { .. } => TypeErrorCode::E0609,
            TypeError::MovedInGuard { .. } => TypeErrorCode::E0107,
            TypeError::QualifierConflict { .. } => TypeErrorCode::E0104,
            TypeError::FnCapabilityMismatch { .. } => TypeErrorCode::E0104,
            TypeError::ParamModeMismatch { .. } => TypeErrorCode::E0611,
            TypeError::LinearValueNotConsumed { .. } => TypeErrorCode::E0108,
            TypeError::UnsupportedConstraint { .. } => TypeErrorCode::E0317,
        }
    }

    /// Return optional help text for this error.
    pub fn help(&self) -> Option<String> {
        match self {
            TypeError::Mismatch { expected, actual } => {
                match (expected, actual) {
                    (Type::Own(_), _) | (_, Type::Own(_)) => {
                        Some("a `~` (owned) value must be passed to a parameter that requires ownership".to_string())
                    }
                    _ => None,
                }
            }
            TypeError::FnCapabilityMismatch { .. } => {
                Some("a single-use closure (`~fn`) cannot be used where a multi-use function (`fn`) is expected".to_string())
            }
            TypeError::ParamModeMismatch { expected_mode, actual_mode, .. } => {
                let (exp, act) = (mode_label(*expected_mode), mode_label(*actual_mode));
                Some(format!(
                    "consume (`~T`) and borrow (`&~T`) are distinct slot capabilities — expected {exp} slot does not adapt from {act} slot, and vice versa"
                ))
            }
            TypeError::DuplicateType { name } => {
                Some(format!("type `{}` is already defined", name))
            }
            TypeError::DuplicateConstructor { name, first_type, second_type } => {
                Some(format!(
                    "constructor `{name}` is already defined by type `{first_type}`; rename the constructor in `{second_type}` or qualify it"
                ))
            }
            TypeError::DuplicateTrait { name } => {
                Some(format!("trait `{name}` is already defined; rename this trait or remove the earlier definition"))
            }
            TypeError::TypeTraitNameConflict { name } => {
                Some(format!(
                    "`{name}` is already declared as a type in this module; types and traits share a namespace — rename one to disambiguate"
                ))
            }
            TypeError::UnknownVariable { name } => {
                Some(format!("did you mean to define `{}` first?", name))
            }
            TypeError::NotAFunction { actual } => {
                let actual = actual.renumber_for_display();
                let inner = match &actual {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                if matches!(inner, Type::Named(_, _)) {
                    Some(format!("`{}` is a value, not a function — remove `()` to use it directly", actual))
                } else {
                    Some(format!("the expression has type `{}`, which is not callable", actual))
                }
            }
            TypeError::WrongArity { expected, .. } => {
                Some(format!("this function expects {} argument(s)", expected))
            }
            TypeError::InfiniteType { var, ty } => {
                if is_own_wrapper_of(*var, ty) {
                    Some("`~` makes a distinct type — consider removing `~` from the annotation".to_string())
                } else {
                    Some("this creates a type that contains itself".to_string())
                }
            }
            TypeError::UnknownField { type_name, field_name } => {
                Some(format!("type `{}` has no field `{}`", type_name, field_name))
            }
            TypeError::MissingFields { type_name, fields } => {
                Some(format!("type `{}` requires fields: {}", type_name, fields.join(", ")))
            }
            TypeError::NotAStruct { actual } => {
                let actual = actual.renumber_for_display();
                Some(format!("the expression has type `{}`, which is not a struct", actual))
            }
            TypeError::NonExhaustive { missing } => {
                Some(format!("add arms for: {}", missing.join(", ")))
            }
            TypeError::AlreadyMoved { name } => {
                Some(format!("`{}` was already consumed by a previous use", name))
            }
            TypeError::MovedInBranch { name } => {
                Some(format!("`{}` was consumed in some but not all branches of a conditional", name))
            }
            TypeError::CapturedMoved { name } => {
                Some(format!("`{}` was already consumed before the closure was created", name))
            }
            TypeError::QualifierMismatch { callee, param, .. } => {
                Some(format!("`{callee}` uses parameter `{param}` more than once, so it cannot accept `~` (owned) values. Consider cloning first, or use a function that consumes its argument at most once."))
            }
            TypeError::OwnershipMismatch { expected, .. } => {
                if let Type::Own(_) = expected {
                    Some("a `~` (owned) value must be passed to a parameter that requires ownership".to_string())
                } else {
                    None
                }
            }
            TypeError::UnsupportedExpr { .. } => None,
            TypeError::ConstrainedFunctionRef { name, .. } => {
                Some(format!("call `{name}` directly with arguments, or pass it where the type can be inferred"))
            }
            TypeError::NoInstance { required_by: Some(bound), .. } => {
                Some(format!("required by a bound in `{}`", bound))
            }
            TypeError::NoInstance { .. } => None,
            TypeError::OrphanInstance { trait_name, ty, modules_checked } => {
                let mut msg = format!("cannot implement `{}` for `{}`: only user-defined types can have trait implementations", trait_name, ty);
                if !modules_checked.is_empty() {
                    msg.push_str(&format!(" (checked modules: {})", modules_checked.join(", ")));
                }
                Some(msg)
            }
            TypeError::OwnedTypeImpl { trait_name, ty } => {
                Some(format!("implement `{}` for `{}` instead; the `~` ownership qualifier is erased for trait resolution", trait_name, ty))
            }
            TypeError::DuplicateInstance { existing_ty, .. } => {
                Some(format!("conflicts with existing implementation for `{}`", existing_ty))
            }
            TypeError::CannotDerive { trait_name, field_type, .. } => {
                Some(format!("field type `{}` does not implement `{}`", field_type, trait_name))
            }
            TypeError::DefinitionConflictsWithTraitMethod { .. } => {
                Some("trait methods are bound as module-level names; choose a different name for this definition".to_string())
            }
            TypeError::InvalidImpl {
                missing_methods,
                extra_methods,
                ..
            } => {
                let mut parts = Vec::new();
                if !missing_methods.is_empty() {
                    parts.push(format!(
                        "missing method(s): {}",
                        missing_methods.join(", ")
                    ));
                }
                if !extra_methods.is_empty() {
                    parts.push(format!(
                        "unknown method(s): {}",
                        extra_methods.join(", ")
                    ));
                }
                Some(parts.join("; "))
            }
            TypeError::UnknownType { name, suggestion, variant_of, is_value } => {
                if let Some(parent) = variant_of {
                    Some(format!("`{name}` is a variant of type `{parent}`, not a type. Did you mean `{parent}`?"))
                } else if *is_value {
                    Some(format!("`{name}` is a value, not a type"))
                } else if let Some(s) = suggestion {
                    Some(format!("did you mean `{s}`?"))
                } else {
                    Some(format!("type `{}` is not defined", name))
                }
            }
            TypeError::QuestionMarkBadReturn { actual } => {
                let actual = actual.renumber_for_display();
                Some(format!("function returns `{}`, but `?` requires `Result` or `Option`", actual))
            }
            TypeError::QuestionMarkBadOperand { actual } => {
                let actual = actual.renumber_for_display();
                Some(format!("`?` can only be applied to `Result` or `Option`, found `{}`", actual))
            }
            TypeError::QuestionMarkMismatch { expr_kind, return_kind } => {
                Some(format!("cannot use `?` on `{}` in a function returning `{}`", expr_kind, return_kind))
            }
            TypeError::UnknownModule { path } => {
                Some(format!("module `{}` does not exist in the stdlib", path))
            }
            TypeError::CircularImport { cycle } => {
                Some(format!("import cycle: {}", cycle.join(" → ")))
            }
            TypeError::PrivateName { name, module_path } => {
                Some(format!("`{}` is private in module `{}`; add `pub` to export it", name, module_path))
            }
            TypeError::BareImport { path } => {
                let last = path.rsplit('/').next().unwrap_or(path);
                Some(format!("use `import {path}.{{name1, name2}}` to import specific names — qualified imports (`{last}.foo()`) are not yet supported"))
            }
            TypeError::ModuleQualifierUsedAsValue {
                suggested_usage, ..
            } => {
                let example = suggested_usage
                    .as_ref()
                    .map(|usage| format!("`{usage}`"))
                    .unwrap_or_else(|| "`qualifier.some_export`".to_string());
                Some(format!(
                    "module qualifiers are compile-time only, not runtime values; call an exported name directly, for example {example}"
                ))
            }
            TypeError::UnknownQualifiedExport {
                qualifier,
                module_path,
                name,
            } => Some(format!(
                "`{qualifier}.{name}` does not exist: module `{module_path}` has no public export named `{name}`"
            )),
            TypeError::PrivateReexport { .. } => {
                Some("only names that are imported and public can be re-exported with `pub import`".to_string())
            }
            TypeError::ModuleParseError { path, errors } => {
                Some(format!("module `{}` has parse errors: {}", path, errors.join("; ")))
            }
            TypeError::KindMismatch { type_name, expected_arity, actual_arity } => {
                Some(format!("`{}` expects {} type argument(s) but was given {}", type_name, expected_arity, actual_arity))
            }
            TypeError::DisposableBranchLeak { name, type_name } => {
                Some(format!("`~{}` disposable `{}` is disposed in some branches but not all — this will leak the disposable", type_name, name))
            }
            TypeError::ReservedName { name } => {
                Some(format!("names starting with `__krypton_` are reserved for compiler internals; rename `{}`", name))
            }
            TypeError::QualifierBoundViolation { .. } => {
                Some("remove the `~` from the parameter type, or remove the `shared` bound".to_string())
            }
            TypeError::DuplicateImport { name, modules } => {
                Some(format!("rename one import with an alias: `import {}.{{{} as alias}}`", modules[1], name))
            }
            TypeError::UnknownExport { name, module_path } => {
                Some(format!("module `{}` has no export named `{}`", module_path, name))
            }
            TypeError::RedundantPattern => {
                Some("this arm can never be reached".to_string())
            }
            TypeError::WildcardNotAllowed { .. } => {
                Some("type wildcards `_` are only allowed in impl heads for partial application".to_string())
            }
            TypeError::NestedWildcard { .. } => {
                Some("wildcards must appear at the outermost type application level, not nested inside type arguments".to_string())
            }
            TypeError::UnknownTrait { .. } => None,
            TypeError::SelfOutsideImpl => None,
            TypeError::MissingPubAnnotation { .. } => {
                Some("public functions must have explicit type annotations on all parameters and the return type".to_string())
            }
            TypeError::MissingTraitMethodAnnotation { .. } => {
                Some("trait methods must have explicit return type annotations".to_string())
            }
            TypeError::TraitMethodCollision { trait1, trait2, method_name } => {
                Some(format!("traits `{}` and `{}` both define method `{}`; use qualified imports or rename to disambiguate", trait1, trait2, method_name))
            }
            TypeError::MissingTraitBound { type_var, trait_name, fn_name } => {
                match type_var {
                    Some(name) => Some(format!("add `where {}: {}` to the function signature", name, trait_name)),
                    None => Some(format!("add type parameters with a constraint, e.g. `fun {}[t](...) -> t where t: {}`", fn_name, trait_name)),
                }
            }
            TypeError::AmbiguousTraitName { name, .. } => {
                Some(format!("use `import module.{{{}  as Alias}}` to disambiguate", name))
            }
            TypeError::InvalidNullableReturn { .. } => {
                Some("@nullable functions must return Option[T] so the compiler can wrap null values".to_string())
            }
            TypeError::InvalidThrowsReturn { .. } => {
                Some("@throws functions must return Result[String, T] so the compiler can wrap exceptions".to_string())
            }
            TypeError::AmbiguousType { .. } => {
                Some("add a type annotation to constrain the type, e.g., `let x: Int = default()`".to_string())
            }
            TypeError::UnresolvedMultiParamConstraint { trait_name, params } => {
                Some(format!(
                    "add a type annotation that pins parameter(s) {} of trait `{}`",
                    params.iter().map(|p| format!("`{p}`")).collect::<Vec<_>>().join(", "),
                    trait_name,
                ))
            }
            TypeError::DefinitionConflictsWithImport { def_name, source_module } => {
                Some(format!("use `import {source_module}.{{{def_name} as alias}}` to import under a different name"))
            }
            TypeError::DuplicateFunction { name } => {
                Some(format!("function `{name}` is already defined in this module; use a trait for type-based dispatch"))
            }
            TypeError::DuplicateParam { name } => {
                Some(format!("parameter `{name}` is already defined in this function"))
            }
            TypeError::OrPatternBindingMismatch { .. } => {
                Some("all alternatives in an or-pattern must bind the same set of variables".to_string())
            }
            TypeError::ExternTraitOnJsTarget { .. } => {
                Some("extern traits generate JVM bridge classes and are only supported with `extern java`".to_string())
            }
            TypeError::InvalidInstanceFirstParam { expected_type, .. } => {
                Some(format!("@instance methods must take the extern type `{expected_type}` as their first parameter"))
            }
            TypeError::InvalidConstructorReturn { expected_type, .. } => {
                Some(format!("@constructor methods must return `~{expected_type}`"))
            }
            TypeError::InstanceConstructorConflict { .. } => {
                Some("a method cannot be both @instance and @constructor".to_string())
            }
            TypeError::ConstructorWithSelf { .. } => {
                Some("@constructor methods create new instances and should not take the extern type as a parameter".to_string())
            }
            TypeError::InstanceConstructorOnJsTarget { .. } => {
                Some("@instance and @constructor use JVM invocation instructions and are only supported with `extern java`".to_string())
            }
            TypeError::MovedInGuard { name } => {
                Some(format!("`{name}` is consumed in a match guard; guards may fail and fall through, so they cannot move owned values"))
            }
            TypeError::QualifierConflict { .. } => {
                Some("a value cannot be both owned (~) and shared in the same position".to_string())
            }
            TypeError::LinearValueNotConsumed { name, type_name, reason, consume_hint } => {
                let base = match reason {
                    LeakReason::ScopeExit => format!(
                        "`~{type_name}` value `{name}` is never consumed before it goes out of scope"
                    ),
                    LeakReason::BranchMissing => format!(
                        "`~{type_name}` value `{name}` is consumed in some branches but not all"
                    ),
                    LeakReason::RecurBack => format!(
                        "`~{type_name}` value `{name}` is still live when `recur` jumps back to the loop head"
                    ),
                    LeakReason::EarlyReturnViaQuestion => format!(
                        "`~{type_name}` value `{name}` is still live at this early return (`?`)"
                    ),
                };
                let mut parts = vec![base];
                parts.push(format!(
                    "consume `{name}` explicitly (e.g. by passing it to a function that takes `~{type_name}`), or `impl Disposable[{type_name}]` so the compiler can auto-close it"
                ));
                if let Some(hint) = consume_hint {
                    parts.push(format!("e.g. `{hint}({name})`"));
                }
                Some(parts.join("; "))
            }
            TypeError::UnsupportedConstraint { reason, .. } => Some((*reason).to_string()),
        }
    }

    /// Format with user var name context. Falls back to Display for non-type fields.
    pub fn format_with_names(&self, names: &HashMap<TypeVarId, &str>) -> String {
        match self {
            TypeError::Mismatch { expected, actual } => {
                format!(
                    "type mismatch: expected {}, found {}",
                    format_type_with_var_map(expected, names),
                    format_type_with_var_map(actual, names),
                )
            }
            TypeError::InfiniteType { var, ty } => {
                let var_name = format_type_with_var_map(&Type::Var(*var), names);
                let ty_name = format_type_with_var_map(ty, names);
                if is_own_wrapper_of(*var, ty) {
                    format!("type mismatch: expected `{}`, found `{}`", var_name, ty_name)
                } else {
                    format!("infinite type: variable {} occurs in {}", var_name, ty_name)
                }
            }
            TypeError::NotAFunction { actual } => {
                format!(
                    "not a function: type {} is not callable",
                    format_type_with_var_map(actual, names),
                )
            }
            TypeError::NotAStruct { actual } => {
                format!(
                    "not a struct: type {} is not a record",
                    format_type_with_var_map(actual, names),
                )
            }
            TypeError::OwnershipMismatch { expected, actual } => {
                format!(
                    "ownership mismatch: expected `{}`, found `{}`",
                    format_type_with_var_map(expected, names),
                    format_type_with_var_map(actual, names),
                )
            }
            TypeError::FnCapabilityMismatch { expected, actual } => {
                format!(
                    "closure capability mismatch: expected `{}`, found `{}`",
                    format_type_with_var_map(expected, names),
                    format_type_with_var_map(actual, names),
                )
            }
            TypeError::ParamModeMismatch {
                expected,
                actual,
                param_index,
                expected_mode,
                actual_mode,
            } => {
                format!(
                    "function type mode mismatch at parameter {}: expected {} slot, found {} slot in `{}` vs `{}` — slot modes must match exactly",
                    param_index,
                    mode_label(*expected_mode),
                    mode_label(*actual_mode),
                    format_type_with_var_map(expected, names),
                    format_type_with_var_map(actual, names),
                )
            }
            TypeError::InvalidImpl {
                trait_name,
                target_type,
                ..
            } => {
                format!(
                    "invalid impl: `{}` for `{}` does not match trait requirements",
                    trait_name, target_type,
                )
            }
            // All other variants don't contain Type fields that need var mapping
            other => other.to_string(),
        }
    }

    /// Help text with user var name context.
    pub fn help_with_names(&self, names: &HashMap<TypeVarId, &str>) -> Option<String> {
        match self {
            TypeError::NotAFunction { actual } => {
                let inner = match actual {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                if matches!(inner, Type::Named(_, _)) {
                    Some(format!(
                        "`{}` is a value, not a function — remove `()` to use it directly",
                        format_type_with_var_map(actual, names),
                    ))
                } else {
                    Some(format!(
                        "the expression has type `{}`, which is not callable",
                        format_type_with_var_map(actual, names),
                    ))
                }
            }
            TypeError::NotAStruct { actual } => Some(format!(
                "the expression has type `{}`, which is not a struct",
                format_type_with_var_map(actual, names),
            )),
            TypeError::QuestionMarkBadReturn { actual } => Some(format!(
                "function returns `{}`, but `?` requires `Result` or `Option`",
                format_type_with_var_map(actual, names),
            )),
            TypeError::QuestionMarkBadOperand { actual } => Some(format!(
                "`?` can only be applied to `Result` or `Option`, found `{}`",
                format_type_with_var_map(actual, names),
            )),
            // All other variants: delegate to help()
            other => other.help(),
        }
    }

    /// If this is an `UnknownType` error and the name exists as a value binding
    /// in the given environment, set `is_value = true`.
    pub fn enrich_unknown_type_with_env(self, env: &crate::types::TypeEnv) -> Self {
        match self {
            TypeError::UnknownType {
                ref name,
                is_value: false,
                ..
            } if env.lookup(name).is_some() => {
                if let TypeError::UnknownType {
                    name,
                    suggestion,
                    variant_of,
                    ..
                } = self
                {
                    TypeError::UnknownType {
                        name,
                        suggestion,
                        variant_of,
                        is_value: true,
                    }
                } else {
                    unreachable!()
                }
            }
            other => other,
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::Mismatch { expected, actual } => {
                let renamed = renumber_types_for_display(&[expected, actual]);
                write!(
                    f,
                    "type mismatch: expected {}, found {}",
                    renamed[0], renamed[1]
                )
            }
            TypeError::InfiniteType { var, ty } => {
                let renamed = renumber_types_for_display(&[&Type::Var(*var), ty]);
                if is_own_wrapper_of(*var, ty) {
                    write!(f, "type mismatch: expected `{}`, found `{}`", renamed[0], renamed[1])
                } else {
                    write!(f, "infinite type: variable {} occurs in {}", renamed[0], renamed[1])
                }
            }
            TypeError::WrongArity { expected, actual } => {
                write!(
                    f,
                    "wrong arity: expected {} arguments, found {}",
                    expected, actual
                )
            }
            TypeError::UnknownVariable { name } => {
                write!(f, "unknown variable: {}", name)
            }
            TypeError::DuplicateType { name } => {
                write!(f, "duplicate type definition: {}", name)
            }
            TypeError::DuplicateConstructor { name, first_type, second_type } => {
                write!(
                    f,
                    "duplicate constructor `{name}`: already defined by type `{first_type}`, redefined by type `{second_type}`"
                )
            }
            TypeError::DuplicateTrait { name } => {
                write!(f, "duplicate trait definition: {}", name)
            }
            TypeError::TypeTraitNameConflict { name } => {
                write!(f, "name `{}` conflicts: declared as both a type and a trait", name)
            }
            TypeError::NotAFunction { actual } => {
                let actual = actual.renumber_for_display();
                write!(f, "not a function: type {} is not callable", actual)
            }
            TypeError::UnknownField {
                type_name,
                field_name,
            } => {
                write!(
                    f,
                    "unknown field: type {} has no field {}",
                    type_name, field_name
                )
            }
            TypeError::MissingFields { type_name, fields } => {
                write!(f, "missing fields on {}: {}", type_name, fields.join(", "))
            }
            TypeError::NotAStruct { actual } => {
                let actual = actual.renumber_for_display();
                write!(f, "not a struct: type {} is not a record", actual)
            }
            TypeError::NonExhaustive { missing } => {
                write!(f, "non-exhaustive match: missing {}", missing.join(", "))
            }
            TypeError::AlreadyMoved { name } => {
                write!(f, "value already moved: `{}`", name)
            }
            TypeError::MovedInBranch { name } => {
                write!(f, "value may have been moved in a prior branch: `{}`", name)
            }
            TypeError::CapturedMoved { name } => {
                write!(f, "capture of moved value: `{}`", name)
            }
            TypeError::QualifierMismatch { name, callee, .. } => {
                write!(f, "cannot pass `{name}` to `{callee}`: `{callee}` uses its argument multiple times, but `{name}` is single-use (`~`)")
            }
            TypeError::OwnershipMismatch { expected, actual } => {
                let renamed = renumber_types_for_display(&[expected, actual]);
                write!(
                    f,
                    "ownership mismatch: expected `{}`, found `{}`",
                    renamed[0], renamed[1]
                )
            }
            TypeError::FnCapabilityMismatch { expected, actual } => {
                let renamed = renumber_types_for_display(&[expected, actual]);
                write!(
                    f,
                    "closure capability mismatch: expected `{}`, found `{}`",
                    renamed[0], renamed[1]
                )
            }
            TypeError::ParamModeMismatch {
                expected,
                actual,
                param_index,
                expected_mode,
                actual_mode,
            } => {
                let renamed = renumber_types_for_display(&[expected, actual]);
                write!(
                    f,
                    "function type mode mismatch at parameter {}: expected {} slot, found {} slot in `{}` vs `{}` — slot modes must match exactly",
                    param_index,
                    mode_label(*expected_mode),
                    mode_label(*actual_mode),
                    renamed[0],
                    renamed[1]
                )
            }
            TypeError::UnsupportedExpr { description } => {
                write!(f, "not yet implemented: {}", description)
            }
            TypeError::ConstrainedFunctionRef { name, constraints } => {
                let constraint_list = constraints
                    .iter()
                    .map(|(trait_name, type_param)| format!("`{type_param}: {trait_name}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    f,
                    "`{name}` has trait constraints that can't be resolved here: {constraint_list}"
                )
            }
            TypeError::NoInstance { trait_name, ty, .. } => {
                write!(
                    f,
                    "the trait `{}` is not implemented for `{}`",
                    trait_name, ty
                )
            }
            TypeError::OrphanInstance { trait_name, ty, modules_checked } => {
                if modules_checked.is_empty() {
                    write!(
                        f,
                        "orphan instance: cannot implement `{}` for `{}`",
                        trait_name, ty
                    )
                } else {
                    write!(
                        f,
                        "orphan instance: cannot implement `{}` for `{}` \u{2014} neither the trait nor any of its type arguments is defined in this module (checked: {})",
                        trait_name,
                        ty,
                        modules_checked.join(", ")
                    )
                }
            }
            TypeError::OwnedTypeImpl { trait_name, ty } => {
                write!(
                    f,
                    "cannot implement `{}` for owned type `~{}`",
                    trait_name, ty
                )
            }
            TypeError::DuplicateInstance { trait_name, ty, .. } => {
                write!(
                    f,
                    "duplicate instance: `{}` is already implemented for `{}`",
                    trait_name, ty
                )
            }
            TypeError::CannotDerive {
                trait_name,
                type_name,
                field_type,
            } => {
                write!(
                    f,
                    "cannot derive `{}` for `{}`: field type `{}` does not implement `{}`",
                    trait_name, type_name, field_type, trait_name
                )
            }
            TypeError::DefinitionConflictsWithTraitMethod {
                def_name,
                trait_name,
            } => {
                write!(
                    f,
                    "definition `{}` conflicts with trait method `{}.{}`",
                    def_name, trait_name, def_name
                )
            }
            TypeError::InvalidImpl {
                trait_name,
                target_type,
                ..
            } => {
                write!(
                    f,
                    "invalid impl: `{}` for `{}` does not match trait requirements",
                    trait_name, target_type
                )
            }
            TypeError::UnknownType { name, .. } => {
                write!(f, "unknown type: {}", name)
            }
            TypeError::QuestionMarkBadReturn { actual } => {
                let actual = actual.renumber_for_display();
                write!(
                    f,
                    "`?` operator in function returning `{}` (expected Result or Option)",
                    actual
                )
            }
            TypeError::QuestionMarkBadOperand { actual } => {
                let actual = actual.renumber_for_display();
                write!(
                    f,
                    "`?` operator on `{}` (expected Result or Option)",
                    actual
                )
            }
            TypeError::QuestionMarkMismatch {
                expr_kind,
                return_kind,
            } => {
                write!(
                    f,
                    "`?` on `{}` in function returning `{}`",
                    expr_kind, return_kind
                )
            }
            TypeError::UnknownModule { path } => {
                write!(f, "unknown module: {}", path)
            }
            TypeError::CircularImport { cycle } => {
                write!(f, "circular import detected: {}", cycle.join(" → "))
            }
            TypeError::PrivateName { name, module_path } => {
                write!(f, "name `{}` is private in module `{}`", name, module_path)
            }
            TypeError::BareImport { path } => {
                write!(f, "bare import of module `{}` is not supported", path)
            }
            TypeError::ModuleQualifierUsedAsValue { qualifier, .. } => {
                write!(
                    f,
                    "module qualifier `{}` cannot be used as a value: it is compile-time only, not a runtime value",
                    qualifier
                )
            }
            TypeError::UnknownQualifiedExport {
                qualifier,
                module_path,
                name,
            } => {
                write!(
                    f,
                    "qualified export `{qualifier}.{name}` not found in module `{module_path}`"
                )
            }
            TypeError::PrivateReexport { name } => {
                write!(
                    f,
                    "cannot re-export `{}`: name is not in scope or is private",
                    name
                )
            }
            TypeError::ModuleParseError { path, .. } => {
                write!(f, "parse error in imported module `{}`", path)
            }
            TypeError::KindMismatch {
                type_name,
                expected_arity,
                actual_arity,
            } => {
                write!(
                    f,
                    "kind mismatch: `{}` expects {} type argument(s) but was given {}",
                    type_name, expected_arity, actual_arity
                )
            }
            TypeError::DisposableBranchLeak { name, type_name } => {
                write!(
                    f,
                    "disposable `{}` (~{}) consumed in some branches but not all",
                    name, type_name
                )
            }
            TypeError::ReservedName { name } => {
                write!(
                    f,
                    "`{}` is a reserved compiler name and cannot be used",
                    name
                )
            }
            TypeError::QualifierBoundViolation {
                type_var,
                param_name,
            } => {
                write!(
                    f,
                    "qualifier bound violation: type variable `{}` is constrained to `shared` but parameter `{}` uses `~{}`",
                    type_var, param_name, type_var
                )
            }
            TypeError::DuplicateImport { name, modules } => {
                write!(
                    f,
                    "duplicate import: `{}` is already imported from `{}`; use `import {}.{{{} as alias}}` to disambiguate",
                    name, modules[0], modules[1], name
                )
            }
            TypeError::UnknownExport { name, module_path } => {
                write!(f, "unknown export `{}` from module `{}`", name, module_path)
            }
            TypeError::RedundantPattern => {
                write!(f, "redundant match arm: pattern is already covered")
            }
            TypeError::WildcardNotAllowed { .. } => {
                write!(f, "type wildcard `_` is not allowed in this position")
            }
            TypeError::NestedWildcard { .. } => {
                write!(f, "nested wildcard `_` in impl head is not allowed")
            }
            TypeError::UnknownTrait { name } => {
                write!(f, "unknown trait `{}`", name)
            }
            TypeError::SelfOutsideImpl => {
                write!(f, "`Self` can only be used inside impl blocks")
            }
            TypeError::MissingPubAnnotation { fn_name, missing } => {
                write!(
                    f,
                    "public function `{}` is missing type annotations for: {}",
                    fn_name,
                    missing.join(", ")
                )
            }
            TypeError::MissingTraitMethodAnnotation {
                trait_name,
                method_name,
            } => {
                write!(
                    f,
                    "trait method `{}` in trait `{}` is missing a return type annotation",
                    method_name, trait_name
                )
            }
            TypeError::TraitMethodCollision {
                method_name,
                trait1,
                trait2,
            } => {
                write!(
                    f,
                    "trait method collision: `{}` is defined by both `{}` and `{}`",
                    method_name, trait1, trait2
                )
            }
            TypeError::MissingTraitBound {
                fn_name,
                trait_name,
                type_var,
            } => {
                match type_var {
                    Some(name) => write!(
                        f,
                        "function `{}` uses trait method from `{}` on type variable `{}` without a corresponding bound",
                        fn_name, trait_name, name
                    ),
                    None => write!(
                        f,
                        "function `{}` requires trait `{}` but has no declared type parameters",
                        fn_name, trait_name
                    ),
                }
            }
            TypeError::AmbiguousTraitName {
                name,
                existing_module,
                new_module,
            } => {
                write!(
                    f,
                    "ambiguous trait name `{}`: defined in both `{}` and `{}`",
                    name, existing_module, new_module
                )
            }
            TypeError::InvalidNullableReturn {
                name,
                actual_return_type,
            } => {
                let actual = actual_return_type.renumber_for_display();
                write!(
                    f,
                    "@nullable on extern function `{}` requires return type Option[T], found {}",
                    name, actual
                )
            }
            TypeError::InvalidThrowsReturn {
                name,
                actual_return_type,
            } => {
                let actual = actual_return_type.renumber_for_display();
                write!(
                    f,
                    "@throws on extern function `{}` requires return type Result[String, T], found {}",
                    name, actual
                )
            }
            TypeError::AmbiguousType {
                trait_name,
                method_name,
            } => {
                write!(
                    f,
                    "ambiguous type: could not infer the type for trait `{}` in call to `{}`",
                    trait_name, method_name
                )
            }
            TypeError::UnresolvedMultiParamConstraint { trait_name, params } => {
                let joined = params
                    .iter()
                    .map(|p| format!("`{p}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    f,
                    "unresolved trait `{trait_name}`: could not determine type parameter(s) {joined}",
                )
            }
            TypeError::DefinitionConflictsWithImport {
                def_name,
                source_module,
            } => {
                write!(
                    f,
                    "definition `{}` conflicts with imported function from `{}`",
                    def_name, source_module
                )
            }
            TypeError::DuplicateFunction { name } => {
                write!(f, "duplicate function definition: {}", name)
            }
            TypeError::DuplicateParam { name } => {
                write!(f, "duplicate parameter name: {}", name)
            }
            TypeError::OrPatternBindingMismatch {
                alt_index,
                expected_names,
                actual_names,
            } => {
                write!(
                    f,
                    "or-pattern alternative {} binds different variables: expected [{}], found [{}]",
                    alt_index,
                    expected_names.join(", "),
                    actual_names.join(", ")
                )
            }
            TypeError::ExternTraitOnJsTarget { name } => {
                write!(
                    f,
                    "extern trait `{}` is not supported on the JS target; extern traits are Java-only",
                    name
                )
            }
            TypeError::InvalidInstanceFirstParam { name, expected_type } => {
                write!(
                    f,
                    "@instance extern function `{}` must have first parameter of type `{}`",
                    name, expected_type
                )
            }
            TypeError::InvalidConstructorReturn { name, expected_type, actual_return_type } => {
                let actual = actual_return_type.renumber_for_display();
                write!(
                    f,
                    "@constructor extern function `{}` must return `~{}`, found {}",
                    name, expected_type, actual
                )
            }
            TypeError::InstanceConstructorConflict { name } => {
                write!(
                    f,
                    "extern function `{}` cannot have both @instance and @constructor",
                    name
                )
            }
            TypeError::ConstructorWithSelf { name } => {
                write!(
                    f,
                    "@constructor extern function `{}` must not take the extern type as a parameter",
                    name
                )
            }
            TypeError::InstanceConstructorOnJsTarget { name } => {
                write!(
                    f,
                    "@instance/@constructor on extern function `{}` is not supported on the JS target",
                    name
                )
            }
            TypeError::MovedInGuard { name } => {
                write!(f, "cannot consume owned value `{}` in match guard", name)
            }
            TypeError::QualifierConflict { existing, incoming } => {
                write!(
                    f,
                    "conflicting ownership requirements: already constrained to {existing}, but also required to be {incoming}"
                )
            }
            TypeError::LinearValueNotConsumed { name, type_name, reason, .. } => {
                let where_ = match reason {
                    LeakReason::ScopeExit => "at scope exit",
                    LeakReason::BranchMissing => "in some branches",
                    LeakReason::RecurBack => "before `recur`",
                    LeakReason::EarlyReturnViaQuestion => "at `?` early return",
                };
                write!(
                    f,
                    "linear `~{}` value `{}` is never consumed {}",
                    type_name, name, where_
                )
            }
            TypeError::UnsupportedConstraint { trait_name, .. } => {
                write!(
                    f,
                    "unsupported trait constraint shape for `{}`",
                    trait_name
                )
            }
        }
    }
}

/// A secondary diagnostic label with optional cross-file source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SecondaryLabel {
    pub span: Span,
    pub message: String,
    pub source_file: Option<String>, // None = same file as primary span
}

/// A type error paired with the source span where it occurred.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedTypeError {
    pub error: Box<TypeError>,
    pub span: Span,
    pub note: Option<String>,
    pub secondary_span: Option<Box<SecondaryLabel>>,
    /// The module path where this error originated (None = root/user file).
    pub source_file: Option<String>,
    /// User-written type parameter names for rendering (e.g., from `impl Trait[Vec[a]]`).
    pub var_names: Option<Vec<(TypeVarId, String)>>,
}

impl SpannedTypeError {
    /// Format the error message, using user var names if available.
    pub fn format_message(&self) -> String {
        match &self.var_names {
            Some(names) => {
                let map: HashMap<TypeVarId, &str> =
                    names.iter().map(|(id, n)| (*id, n.as_str())).collect();
                self.error.format_with_names(&map)
            }
            None => self.error.to_string(),
        }
    }

    /// Format help text, using user var names if available.
    pub fn format_help(&self) -> Option<String> {
        match &self.var_names {
            Some(names) => {
                let map: HashMap<TypeVarId, &str> =
                    names.iter().map(|(id, n)| (*id, n.as_str())).collect();
                self.error.help_with_names(&map)
            }
            None => self.error.help(),
        }
    }
}

impl fmt::Display for SpannedTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} [{}]", self.error, self.error.error_code())
    }
}

impl std::error::Error for TypeError {}
