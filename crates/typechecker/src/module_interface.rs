use std::collections::{HashMap, HashSet};
use std::fmt;

use krypton_parser::ast::{ExternTarget, Span, Visibility};

use crate::typed_ast::{
    ExportedFn, ExportedTypeKind, ExternTypeInfo, InstanceDefInfo, ParamQualifier, TraitName,
    TypedModule,
};
use crate::types::{Type, TypeScheme, TypeVarId};

// ---------------------------------------------------------------------------
// Canonical module identity
// ---------------------------------------------------------------------------

/// Canonical module path (e.g., "core/semigroup", "myapp/utils").
/// Newtype over String to prevent mixing with arbitrary strings.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModulePath(pub String);

impl ModulePath {
    pub fn new(path: impl Into<String>) -> Self {
        ModulePath(path.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

// ---------------------------------------------------------------------------
// Stable local symbol keys
// ---------------------------------------------------------------------------

/// Stable path-based local identity for a symbol within a module.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LocalSymbolKey {
    /// Top-level function: `fn/<name>`
    Function(String),
    /// Type: `type/<name>`
    Type(String),
    /// Trait: `trait/<name>`
    Trait(String),
    /// Constructor/variant: `type/<parent_type>/ctor/<name>`
    Constructor { parent_type: String, name: String },
    /// Instance: `instance/<trait_name>/<target_type>`
    Instance {
        trait_name: String,
        target_type: String,
    },
}

impl LocalSymbolKey {
    /// Extract the bare local name from any key variant.
    pub fn local_name(&self) -> String {
        match self {
            LocalSymbolKey::Function(name) => name.clone(),
            LocalSymbolKey::Type(name) => name.clone(),
            LocalSymbolKey::Trait(name) => name.clone(),
            LocalSymbolKey::Constructor { name, .. } => name.clone(),
            LocalSymbolKey::Instance { trait_name, .. } => trait_name.clone(),
        }
    }
}

impl fmt::Display for LocalSymbolKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LocalSymbolKey::Function(name) => write!(f, "fn/{name}"),
            LocalSymbolKey::Type(name) => write!(f, "type/{name}"),
            LocalSymbolKey::Trait(name) => write!(f, "trait/{name}"),
            LocalSymbolKey::Constructor { parent_type, name } => {
                write!(f, "type/{parent_type}/ctor/{name}")
            }
            LocalSymbolKey::Instance {
                trait_name,
                target_type,
            } => write!(f, "instance/{trait_name}/{target_type}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Canonical reference (module + local key)
// ---------------------------------------------------------------------------

/// A fully-qualified canonical symbol reference: module + local key.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CanonicalRef {
    pub module: ModulePath,
    pub symbol: LocalSymbolKey,
}

impl fmt::Display for CanonicalRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{}", self.module, self.symbol)
    }
}

// ---------------------------------------------------------------------------
// ModuleInterface and sub-types
// ---------------------------------------------------------------------------

/// A module's cross-module interface artifact.
/// Contains only references and summaries — no bodies, no transitive deps.
#[derive(Clone, Debug)]
pub struct ModuleInterface {
    pub module_path: ModulePath,
    pub direct_deps: Vec<ModulePath>,
    pub exported_fns: Vec<ExportedFnSummary>,
    pub reexported_fns: Vec<ReexportedFnEntry>,
    pub exported_types: Vec<TypeSummary>,
    pub reexported_types: Vec<ReexportedTypeEntry>,
    pub exported_traits: Vec<TraitSummary>,
    pub exported_instances: Vec<InstanceSummary>,
    pub extern_types: Vec<ExternTypeSummary>,
    pub exported_fn_qualifiers: HashMap<String, Vec<(ParamQualifier, String)>>,
    pub type_visibility: HashMap<String, Visibility>,
    /// All top-level names that exist but aren't exported — enables "exists but private" diagnostics.
    pub private_names: HashSet<String>,
}

/// Summary of an exported function.
///
/// `exported_symbol` is the mangled wire-format name used by codegen to
/// distinguish overload siblings at the module boundary. For non-overloaded
/// functions it equals `name`. For a group of overloads sharing a name, the
/// earliest (by source order) keeps the bare name and each sibling is
/// suffixed with `_<hash16>`, where `hash16` is the full 64-bit FNV-1a
/// digest (16 lowercase hex chars) over the canonical parameter-type
/// fingerprint. The hash keys on type structure rather than declaration
/// position, so reordering or renaming existing overloads does not change
/// wire names.
#[derive(Clone, Debug)]
pub struct ExportedFnSummary {
    pub key: LocalSymbolKey,
    pub name: String,
    pub exported_symbol: String,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
    pub def_span: Option<Span>,
}

/// A reexported function — points back to the canonical defining module.
#[derive(Clone, Debug)]
pub struct ReexportedFnEntry {
    pub local_name: String,
    pub canonical_ref: CanonicalRef,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
    pub def_span: Option<Span>,
}

/// Summary of an exported type (summary-based, not AST copy).
#[derive(Clone, Debug)]
pub struct TypeSummary {
    pub key: LocalSymbolKey,
    pub name: String,
    pub type_params: Vec<String>,
    pub type_param_vars: Vec<TypeVarId>,
    pub kind: TypeSummaryKind,
    pub lifts: Option<krypton_parser::ast::Lifts>,
    pub visibility: Visibility,
}

#[derive(Clone, Debug)]
pub enum TypeSummaryKind {
    Opaque,
    Record { fields: Vec<(String, Type)> },
    Sum { variants: Vec<VariantSummary> },
}

#[derive(Clone, Debug)]
pub struct VariantSummary {
    pub key: LocalSymbolKey,
    pub name: String,
    pub fields: Vec<Type>,
}

/// A reexported type entry preserving canonical ownership.
#[derive(Clone, Debug)]
pub struct ReexportedTypeEntry {
    pub local_name: String,
    pub canonical_ref: CanonicalRef,
    pub visibility: Visibility,
}

/// Summary of an exported trait.
#[derive(Clone, Debug)]
pub struct TraitSummary {
    pub key: LocalSymbolKey,
    pub visibility: Visibility,
    pub name: String,
    pub module_path: ModulePath,
    pub type_var: String,
    pub type_var_id: TypeVarId,
    /// All trait type parameter ids in declaration order; `type_var_ids[0] == type_var_id`.
    pub type_var_ids: Vec<TypeVarId>,
    pub type_var_names: Vec<String>,
    pub type_var_arity: usize,
    pub superclasses: Vec<TraitName>,
    pub methods: Vec<TraitMethodSummary>,
}

#[derive(Clone, Debug)]
pub struct TraitMethodSummary {
    pub name: String,
    pub param_types: Vec<(crate::types::ParamMode, Type)>,
    pub return_type: Type,
    pub constraints: Vec<(TraitName, Vec<TypeVarId>)>,
}

/// Summary of a local trait instance.
#[derive(Clone, Debug)]
pub struct InstanceSummary {
    pub key: LocalSymbolKey,
    pub trait_name: TraitName,
    /// Joined display form of the type arguments (e.g., `"Int, String"`).
    pub target_type_name: String,
    /// Type arguments. Length 1 for single-parameter traits.
    pub target_types: Vec<Type>,
    pub type_var_ids: HashMap<String, TypeVarId>,
    pub constraints: Vec<crate::typed_ast::ResolvedConstraint>,
    pub method_summaries: Vec<InstanceMethodSummary>,
    pub is_intrinsic: bool,
}

#[derive(Clone, Debug)]
pub struct InstanceMethodSummary {
    pub name: String,
    pub scheme: TypeScheme,
    pub constraint_pairs: Vec<(TraitName, Vec<TypeVarId>)>,
}

/// Extern type ownership summary.
#[derive(Clone, Debug)]
pub struct ExternTypeSummary {
    pub krypton_name: String,
    pub host_module: String,
    pub target: ExternTarget,
    pub lifts: Option<krypton_parser::ast::Lifts>,
}

// ---------------------------------------------------------------------------
// Direct dependency extraction from parsed AST
// ---------------------------------------------------------------------------

/// Collect direct dependency module paths from the parsed module's import declarations.
pub fn collect_direct_deps(module: &krypton_parser::ast::Module) -> Vec<ModulePath> {
    let mut deps = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for decl in &module.decls {
        if let krypton_parser::ast::Decl::Import { path, .. } = decl {
            if seen.insert(path.clone()) {
                deps.push(ModulePath::new(path.clone()));
            }
        }
    }
    deps
}

// ---------------------------------------------------------------------------
// Interface extraction
// ---------------------------------------------------------------------------

/// Extract a `ModuleInterface` from a fully-assembled `TypedModule`.
///
/// This is Phase 1 extraction — runs alongside the existing path
/// without replacing any consumers.
pub fn extract_interface(typed: &TypedModule, direct_dep_paths: &[String]) -> ModuleInterface {
    let module_path = ModulePath::new(&typed.module_path);

    let direct_deps = direct_dep_paths.iter().map(ModulePath::new).collect();

    // Build sets of constructor names for classifying exported fns
    let mut constructor_names: HashMap<String, String> = HashMap::new(); // ctor_name -> parent_type
    for sd in &typed.struct_decls {
        if sd.qualified_name.module_path == typed.module_path {
            constructor_names.insert(sd.name.clone(), sd.name.clone());
        }
    }
    for sd in &typed.sum_decls {
        if sd.qualified_name.module_path == typed.module_path {
            for v in &sd.variants {
                constructor_names.insert(v.name.clone(), sd.name.clone());
            }
        }
    }

    let exported_fns = extract_exported_fns(&typed.exported_fn_types, &constructor_names);
    let reexported_fns = extract_reexported_fns(typed);
    let exported_types = extract_exported_types(typed);
    let reexported_types = extract_reexported_types(typed);
    let exported_traits = extract_exported_traits(typed);
    let exported_instances = extract_instances(&typed.instance_defs);
    let extern_types = extract_extern_types(&typed.extern_types);

    // Build private_names: all top-level names that exist but aren't exported.
    let private_names = extract_private_names(typed);

    ModuleInterface {
        module_path,
        direct_deps,
        exported_fns,
        reexported_fns,
        exported_types,
        reexported_types,
        exported_traits,
        exported_instances,
        extern_types,
        exported_fn_qualifiers: typed.exported_fn_qualifiers.clone(),
        type_visibility: typed.type_visibility.clone(),
        private_names,
    }
}

fn extract_exported_fns(
    exported: &[ExportedFn],
    constructor_names: &HashMap<String, String>,
) -> Vec<ExportedFnSummary> {
    let exported_symbols = mangle_overload_symbols(exported);
    exported
        .iter()
        .enumerate()
        .map(|(i, ef)| {
            let key = if let Some(parent) = constructor_names.get(&ef.name) {
                LocalSymbolKey::Constructor {
                    parent_type: parent.clone(),
                    name: ef.name.clone(),
                }
            } else {
                LocalSymbolKey::Function(ef.name.clone())
            };
            ExportedFnSummary {
                key,
                name: ef.name.clone(),
                exported_symbol: exported_symbols[i].clone(),
                scheme: ef.scheme.clone(),
                origin: ef.origin.clone(),
                def_span: ef.def_span,
            }
        })
        .collect()
}

/// Assign source-order mangled symbol names to an exported-fn slice.
/// Entries sharing a bare name form an overload group; within a group the
/// earliest (by `def_span` start offset) keeps the bare name and siblings
/// are mangled with a 6-hex-digit FNV-1a hash of their canonical parameter
/// type fingerprint. Delegates to `overload::mangle_group` so that AST-side
/// mangling cannot diverge from this interface-side mangling.
fn mangle_overload_symbols(exported: &[ExportedFn]) -> Vec<String> {
    let mut groups: HashMap<&str, Vec<usize>> = HashMap::new();
    for (i, ef) in exported.iter().enumerate() {
        groups.entry(ef.name.as_str()).or_default().push(i);
    }
    let mut out = vec![String::new(); exported.len()];
    for (name, indices) in groups {
        let params: Vec<Vec<Type>> = indices
            .iter()
            .map(|&i| match &exported[i].scheme.ty {
                Type::Fn(ps, _) => ps.iter().map(|(_, t)| t.clone()).collect(),
                _ => vec![],
            })
            .collect();
        let def_spans: Vec<Option<Span>> =
            indices.iter().map(|&i| exported[i].def_span).collect();
        let mangled = crate::overload::mangle_group(name, &params, &def_spans);
        for (pos, &idx) in indices.iter().enumerate() {
            out[idx] = mangled[pos].clone();
        }
    }
    out
}

/// Mangle exported symbols for a slice of `TypedFnDecl`s using the same
/// source-order hash-based mangler that `mangle_overload_symbols` uses for
/// `ExportedFnSummary`. Call this once at end-of-typechecking to stamp
/// `TypedFnDecl.exported_symbol` so IR/codegen can read the source-of-truth
/// directly. `params_per_decl[i]` is the parameter-type fingerprint for
/// `decls[i]`; the caller is responsible for building it from whatever the
/// local source of truth is (`result_schemes`, instance-method schemes, etc.).
pub fn mangle_typed_fn_decls(
    decls: &[crate::typed_ast::TypedFnDecl],
    params_per_decl: &[Vec<Type>],
) -> Vec<String> {
    assert_eq!(
        decls.len(),
        params_per_decl.len(),
        "ICE: mangle_typed_fn_decls: decls and params_per_decl length mismatch",
    );
    let mut groups: HashMap<&str, Vec<usize>> = HashMap::new();
    for (i, d) in decls.iter().enumerate() {
        groups.entry(d.name.as_str()).or_default().push(i);
    }
    let mut out = vec![String::new(); decls.len()];
    for (name, indices) in groups {
        let params: Vec<Vec<Type>> =
            indices.iter().map(|&i| params_per_decl[i].clone()).collect();
        let def_spans: Vec<Option<Span>> =
            indices.iter().map(|&i| Some(decls[i].def_span)).collect();
        let mangled = crate::overload::mangle_group(name, &params, &def_spans);
        for (pos, &idx) in indices.iter().enumerate() {
            out[idx] = mangled[pos].clone();
        }
    }
    out
}

fn extract_reexported_fns(typed: &TypedModule) -> Vec<ReexportedFnEntry> {
    typed
        .reexported_fn_types
        .iter()
        .map(|ef| {
            let qn = ef.qualified_name.as_ref().unwrap_or_else(|| {
                panic!(
                    "ICE: re-exported fn '{}' missing qualified_name",
                    ef.name
                )
            });
            let (canonical_module, canonical_name) =
                (qn.module_path.clone(), qn.local_name.clone());
            let symbol = typed
                .exported_type_infos
                .values()
                .find_map(|info| {
                    if info.source_module != canonical_module {
                        return None;
                    }
                    match &info.kind {
                        ExportedTypeKind::Record { .. } if info.name == canonical_name => {
                            Some(LocalSymbolKey::Constructor {
                                parent_type: info.name.clone(),
                                name: canonical_name.clone(),
                            })
                        }
                        ExportedTypeKind::Sum { variants } => variants.iter().find_map(|variant| {
                            (variant.name == canonical_name).then(|| LocalSymbolKey::Constructor {
                                parent_type: info.name.clone(),
                                name: canonical_name.clone(),
                            })
                        }),
                        _ => None,
                    }
                })
                // Re-exported symbols that aren't constructors or type names are functions
                .unwrap_or_else(|| LocalSymbolKey::Function(canonical_name.clone()));

            ReexportedFnEntry {
                local_name: ef.name.clone(),
                canonical_ref: CanonicalRef {
                    module: ModulePath::new(&canonical_module),
                    symbol,
                },
                scheme: ef.scheme.clone(),
                origin: ef.origin.clone(),
                def_span: ef.def_span,
            }
        })
        .collect()
}

fn extract_exported_types(typed: &TypedModule) -> Vec<TypeSummary> {
    // Extern type names — these are opaque from the consumer's perspective
    // (you can name the type, but you can't construct it).
    let extern_type_names: HashSet<&str> = typed
        .extern_types
        .iter()
        .map(|et| et.krypton_name.as_str())
        .collect();

    typed
        .exported_type_infos
        .iter()
        .filter_map(|(name, info)| {
            // Unknown visibility defaults to Private (safe: won't be exported)
            let mut vis = typed
                .type_visibility
                .get(name)
                .copied()
                .unwrap_or(Visibility::Private);
            // Extern types need to be in the interface regardless of visibility,
            // because consumers need them to resolve function signatures that
            // reference these types (e.g. `send(target: Ref[m], ...)`).
            // They are always Opaque — you can name them but not construct them.
            if extern_type_names.contains(name.as_str()) {
                vis = Visibility::Opaque;
            } else if vis == Visibility::Private {
                return None;
            }

            let parent_name = name.clone();
            let kind = match &info.kind {
                ExportedTypeKind::Opaque => TypeSummaryKind::Opaque,
                ExportedTypeKind::Record { fields } => TypeSummaryKind::Record {
                    fields: fields.clone(),
                },
                ExportedTypeKind::Sum { variants } => TypeSummaryKind::Sum {
                    variants: variants
                        .iter()
                        .map(|v| VariantSummary {
                            key: LocalSymbolKey::Constructor {
                                parent_type: parent_name.clone(),
                                name: v.name.clone(),
                            },
                            name: v.name.clone(),
                            fields: v.fields.clone(),
                        })
                        .collect(),
                },
            };

            Some(TypeSummary {
                key: LocalSymbolKey::Type(name.clone()),
                name: name.clone(),
                type_params: info.type_params.clone(),
                type_param_vars: info.type_param_vars.clone(),
                kind,
                lifts: info.lifts.clone(),
                visibility: vis,
            })
        })
        .collect()
}

fn extract_reexported_types(typed: &TypedModule) -> Vec<ReexportedTypeEntry> {
    typed
        .reexported_type_names
        .iter()
        .map(|name| {
            let canonical_module = typed
                .type_origin(name)
                .unwrap_or(&typed.module_path)
                .to_string();
            // Re-exported types are explicitly listed, so Pub is the expected visibility
            let vis = typed
                .reexported_type_visibility
                .get(name)
                .copied()
                .unwrap_or(Visibility::Pub);

            ReexportedTypeEntry {
                local_name: name.clone(),
                canonical_ref: CanonicalRef {
                    module: ModulePath::new(&canonical_module),
                    symbol: LocalSymbolKey::Type(name.clone()),
                },
                visibility: vis,
            }
        })
        .collect()
}

fn extract_exported_traits(typed: &TypedModule) -> Vec<TraitSummary> {
    typed
        .exported_trait_defs
        .iter()
        .map(|td| TraitSummary {
            key: LocalSymbolKey::Trait(td.name.clone()),
            visibility: td.visibility,
            name: td.name.clone(),
            module_path: ModulePath::new(&td.module_path),
            type_var: td.type_var.clone(),
            type_var_id: td.type_var_id,
            type_var_ids: td.type_var_ids.clone(),
            type_var_names: td.type_var_names.clone(),
            type_var_arity: td.type_var_arity,
            superclasses: td.superclasses.clone(),
            methods: td
                .methods
                .iter()
                .map(|m| TraitMethodSummary {
                    name: m.name.clone(),
                    param_types: m.param_types.clone(),
                    return_type: m.return_type.clone(),
                    constraints: m.constraints.clone(),
                })
                .collect(),
        })
        .collect()
}

fn extract_instances(instances: &[InstanceDefInfo]) -> Vec<InstanceSummary> {
    instances
        .iter()
        .map(|inst| InstanceSummary {
            key: LocalSymbolKey::Instance {
                trait_name: inst.trait_name.display_name().to_string(),
                target_type: inst.target_type_name.clone(),
            },
            trait_name: inst.trait_name.clone(),
            target_type_name: inst.target_type_name.clone(),
            target_types: inst.target_types.clone(),
            type_var_ids: inst.type_var_ids.clone(),
            constraints: inst.constraints.clone(),
            method_summaries: inst
                .methods
                .iter()
                .map(|m| InstanceMethodSummary {
                    name: m.name.clone(),
                    scheme: m.scheme.clone(),
                    constraint_pairs: m.constraint_pairs.clone(),
                })
                .collect(),
            is_intrinsic: inst.is_intrinsic,
        })
        .collect()
}

fn extract_extern_types(externs: &[ExternTypeInfo]) -> Vec<ExternTypeSummary> {
    externs
        .iter()
        .map(|et| ExternTypeSummary {
            krypton_name: et.krypton_name.clone(),
            host_module: et.host_module.clone(),
            target: et.target.clone(),
            lifts: et.lifts.clone(),
        })
        .collect()
}

fn extract_private_names(typed: &TypedModule) -> HashSet<String> {
    let mut private = HashSet::new();

    // Exported/reexported fn names
    let exported_fn_names: HashSet<&str> = typed
        .exported_fn_types
        .iter()
        .map(|f| f.name.as_str())
        .chain(typed.reexported_fn_types.iter().map(|f| f.name.as_str()))
        .collect();

    // Private functions: any name in fn_types that isn't exported or reexported.
    // This includes locally-defined private fns AND non-pub-imported fns.
    for entry in &typed.fn_types {
        if !exported_fn_names.contains(entry.name.as_str()) {
            private.insert(entry.name.clone());
        }
    }

    // Private types: in type_visibility as Private
    for (name, vis) in &typed.type_visibility {
        if matches!(vis, Visibility::Private) {
            private.insert(name.clone());
        }
    }

    private
}

// ---------------------------------------------------------------------------
// Display for snapshots
// ---------------------------------------------------------------------------

/// Produce a deterministic, human-readable representation of a ModuleInterface.
pub fn display_interface(iface: &ModuleInterface) -> String {
    let mut out = String::new();

    out.push_str(&format!("module {}\n", iface.module_path));

    if !iface.direct_deps.is_empty() {
        out.push_str("\ndeps:\n");
        let mut deps: Vec<_> = iface.direct_deps.iter().map(|d| d.as_str()).collect();
        deps.sort();
        for d in deps {
            out.push_str(&format!("  {d}\n"));
        }
    }

    if !iface.exported_fns.is_empty() {
        out.push_str("\nexported fns:\n");
        let mut fns: Vec<_> = iface.exported_fns.iter().collect();
        fns.sort_by_key(|f| &f.name);
        for f in fns {
            out.push_str(&format!("  {} : {}\n", f.key, f.scheme));
        }
    }

    if !iface.reexported_fns.is_empty() {
        out.push_str("\nreexported fns:\n");
        let mut fns: Vec<_> = iface.reexported_fns.iter().collect();
        fns.sort_by_key(|f| &f.local_name);
        for f in fns {
            out.push_str(&format!(
                "  {} -> {} : {}\n",
                f.local_name, f.canonical_ref, f.scheme
            ));
        }
    }

    if !iface.exported_types.is_empty() {
        out.push_str("\nexported types:\n");
        let mut types: Vec<_> = iface.exported_types.iter().collect();
        types.sort_by_key(|t| &t.name);
        for t in types {
            let vis = match t.visibility {
                Visibility::Pub => "pub",
                Visibility::Opaque => "pub(opaque)",
                Visibility::Private => "private",
            };
            out.push_str(&format!("  {} ({vis})", t.key));
            if !t.type_params.is_empty() {
                out.push_str(&format!("[{}]", t.type_params.join(", ")));
            }
            match &t.kind {
                TypeSummaryKind::Opaque => {
                    out.push_str(" = opaque\n");
                }
                TypeSummaryKind::Record { fields } => {
                    out.push_str(" = {");
                    for (i, (name, ty)) in fields.iter().enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(&format!(" {name}: {ty}"));
                    }
                    out.push_str(" }\n");
                }
                TypeSummaryKind::Sum { variants } => {
                    out.push_str(" = ");
                    for (i, v) in variants.iter().enumerate() {
                        if i > 0 {
                            out.push_str(" | ");
                        }
                        out.push_str(&v.name);
                        if !v.fields.is_empty() {
                            out.push('(');
                            for (j, f) in v.fields.iter().enumerate() {
                                if j > 0 {
                                    out.push_str(", ");
                                }
                                out.push_str(&format!("{f}"));
                            }
                            out.push(')');
                        }
                    }
                    out.push('\n');
                }
            }
        }
    }

    if !iface.reexported_types.is_empty() {
        out.push_str("\nreexported types:\n");
        let mut types: Vec<_> = iface.reexported_types.iter().collect();
        types.sort_by_key(|t| &t.local_name);
        for t in types {
            let vis = match t.visibility {
                Visibility::Pub => "pub",
                Visibility::Opaque => "pub(opaque)",
                Visibility::Private => "private",
            };
            out.push_str(&format!(
                "  {} -> {} ({vis})\n",
                t.local_name, t.canonical_ref
            ));
        }
    }

    if !iface.exported_traits.is_empty() {
        out.push_str("\nexported traits:\n");
        let mut traits: Vec<_> = iface.exported_traits.iter().collect();
        traits.sort_by_key(|t| &t.name);
        for t in traits {
            out.push_str(&format!(
                "  {} [{} : {}]\n",
                t.key, t.type_var, t.type_var_id
            ));
            for m in &t.methods {
                let params = m
                    .param_types
                    .iter()
                    .map(|(mode, p)| match (mode, p) {
                        (crate::types::ParamMode::Borrow, Type::Own(inner)) => {
                            format!("&~{inner}")
                        }
                        (crate::types::ParamMode::ObservationalBorrow, _) => {
                            format!("&{p}")
                        }
                        _ => format!("{p}"),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                out.push_str(&format!(
                    "    {}: ({params}) -> {}\n",
                    m.name, m.return_type
                ));
            }
        }
    }

    if !iface.exported_instances.is_empty() {
        out.push_str("\nexported instances:\n");
        let mut instances: Vec<_> = iface.exported_instances.iter().collect();
        instances.sort_by_key(|i| (&i.trait_name, &i.target_type_name));
        for inst in instances {
            out.push_str(&format!("  {}\n", inst.key));
            for m in &inst.method_summaries {
                out.push_str(&format!("    {}: {}\n", m.name, m.scheme));
            }
        }
    }

    if !iface.extern_types.is_empty() {
        out.push_str("\nextern types:\n");
        let mut etypes: Vec<_> = iface.extern_types.iter().collect();
        etypes.sort_by_key(|e| &e.krypton_name);
        for e in etypes {
            out.push_str(&format!(
                "  {} ({:?} \"{}\")\n",
                e.krypton_name, e.target, e.host_module
            ));
        }
    }

    out
}

// ---------------------------------------------------------------------------
// Conversion helpers: interface summary → typed_ast types
// ---------------------------------------------------------------------------

use crate::typed_ast::{
    ExportedTraitDef, ExportedTraitMethod, ExportedTypeInfo, ExportedVariantInfo, InstanceMethod,
};

/// Convert `TypeSummary` → `ExportedTypeInfo` for type registry registration.
pub fn type_summary_to_export_info(ts: &TypeSummary, source_module: &str) -> ExportedTypeInfo {
    let kind = match &ts.kind {
        TypeSummaryKind::Opaque => ExportedTypeKind::Opaque,
        TypeSummaryKind::Record { fields } => ExportedTypeKind::Record {
            fields: fields.clone(),
        },
        TypeSummaryKind::Sum { variants } => ExportedTypeKind::Sum {
            variants: variants
                .iter()
                .map(|v| ExportedVariantInfo {
                    name: v.name.clone(),
                    fields: v.fields.clone(),
                })
                .collect(),
        },
    };
    ExportedTypeInfo {
        name: ts.name.clone(),
        source_module: source_module.to_string(),
        type_params: ts.type_params.clone(),
        type_param_vars: ts.type_param_vars.clone(),
        kind,
        lifts: ts.lifts.clone(),
    }
}

/// Convert `TraitSummary` → `ExportedTraitDef` for trait registration.
pub fn trait_summary_to_exported_def(ts: &TraitSummary) -> ExportedTraitDef {
    ExportedTraitDef {
        visibility: ts.visibility,
        name: ts.name.clone(),
        module_path: ts.module_path.0.clone(),
        type_var: ts.type_var.clone(),
        type_var_id: ts.type_var_id,
        type_var_ids: ts.type_var_ids.clone(),
        type_var_names: ts.type_var_names.clone(),
        type_var_arity: ts.type_var_arity,
        superclasses: ts.superclasses.clone(),
        methods: ts
            .methods
            .iter()
            .map(|m| ExportedTraitMethod {
                name: m.name.clone(),
                param_types: m.param_types.clone(),
                return_type: m.return_type.clone(),
                constraints: m.constraints.clone(),
            })
            .collect(),
    }
}

/// Convert `InstanceSummary` → `InstanceDefInfo` for instance registration.
/// Note: method bodies and param names are not available in the interface,
/// so they are filled with dummy values (empty body/params). This is fine
/// because imported instances only need the type information, not bodies.
pub fn instance_summary_to_def_info(is: &InstanceSummary) -> InstanceDefInfo {
    use crate::typed_ast::{TypedExpr, TypedExprKind};
    let dummy_body = TypedExpr {
        kind: TypedExprKind::Lit(krypton_parser::ast::Lit::Unit),
        ty: Type::Unit,
        span: (0, 0),
        resolved_ref: None,
        scope_id: None,
    };
    InstanceDefInfo {
        trait_name: is.trait_name.clone(),
        target_type_name: is.target_type_name.clone(),
        target_types: is.target_types.clone(),
        type_var_ids: is.type_var_ids.clone(),
        constraints: is.constraints.clone(),
        methods: is
            .method_summaries
            .iter()
            .map(|m| InstanceMethod {
                name: m.name.clone(),
                params: vec![],
                body: dummy_body.clone(),
                scheme: m.scheme.clone(),
                constraint_pairs: m.constraint_pairs.clone(),
            })
            .collect(),
        is_intrinsic: is.is_intrinsic,
    }
}
