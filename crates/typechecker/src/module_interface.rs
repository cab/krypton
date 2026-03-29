use std::collections::HashMap;
use std::fmt;

use krypton_parser::ast::{ExternTarget, Visibility};

use crate::typed_ast::{
    ExportedFn, ExportedTypeKind, ExternFnInfo, ExternTypeInfo, InstanceDefInfo, ParamQualifier,
    TraitName, TypedModule,
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
    pub extern_fns: Vec<ExternFnSummary>,
    pub extern_types: Vec<ExternTypeSummary>,
    pub exported_fn_qualifiers: HashMap<String, Vec<(ParamQualifier, String)>>,
    pub type_visibility: HashMap<String, Visibility>,
}

/// Summary of an exported function.
#[derive(Clone, Debug)]
pub struct ExportedFnSummary {
    pub key: LocalSymbolKey,
    pub name: String,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
}

/// A reexported function — points back to the canonical defining module.
#[derive(Clone, Debug)]
pub struct ReexportedFnEntry {
    pub local_name: String,
    pub canonical_ref: CanonicalRef,
    pub scheme: TypeScheme,
    pub origin: Option<TraitName>,
}

/// Summary of an exported type (summary-based, not AST copy).
#[derive(Clone, Debug)]
pub struct TypeSummary {
    pub key: LocalSymbolKey,
    pub name: String,
    pub type_params: Vec<String>,
    pub type_param_vars: Vec<TypeVarId>,
    pub kind: TypeSummaryKind,
    pub visibility: Visibility,
}

#[derive(Clone, Debug)]
pub enum TypeSummaryKind {
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
    pub type_var_arity: usize,
    pub superclasses: Vec<TraitName>,
    pub methods: Vec<TraitMethodSummary>,
}

#[derive(Clone, Debug)]
pub struct TraitMethodSummary {
    pub name: String,
    pub param_types: Vec<Type>,
    pub return_type: Type,
    pub constraints: Vec<(TraitName, TypeVarId)>,
}

/// Summary of a local trait instance.
#[derive(Clone, Debug)]
pub struct InstanceSummary {
    pub key: LocalSymbolKey,
    pub trait_name: TraitName,
    pub target_type_name: String,
    pub target_type: Type,
    pub type_var_ids: HashMap<String, TypeVarId>,
    pub constraints: Vec<crate::typed_ast::ResolvedConstraint>,
    pub method_summaries: Vec<InstanceMethodSummary>,
    pub is_intrinsic: bool,
}

#[derive(Clone, Debug)]
pub struct InstanceMethodSummary {
    pub name: String,
    pub scheme: TypeScheme,
    pub constraint_pairs: Vec<(TraitName, TypeVarId)>,
}

/// Extern function ownership summary.
#[derive(Clone, Debug)]
pub struct ExternFnSummary {
    pub name: String,
    pub declaring_module: ModulePath,
    pub host_module_path: String,
    pub target: ExternTarget,
    pub param_types: Vec<Type>,
    pub return_type: Type,
}

/// Extern type ownership summary.
#[derive(Clone, Debug)]
pub struct ExternTypeSummary {
    pub krypton_name: String,
    pub host_module: String,
    pub target: ExternTarget,
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
    let extern_fns = extract_extern_fns(&typed.extern_fns);
    let extern_types = extract_extern_types(&typed.extern_types);

    ModuleInterface {
        module_path,
        direct_deps,
        exported_fns,
        reexported_fns,
        exported_types,
        reexported_types,
        exported_traits,
        exported_instances,
        extern_fns,
        extern_types,
        exported_fn_qualifiers: typed.exported_fn_qualifiers.clone(),
        type_visibility: typed.type_visibility.clone(),
    }
}

fn extract_exported_fns(
    exported: &[ExportedFn],
    constructor_names: &HashMap<String, String>,
) -> Vec<ExportedFnSummary> {
    exported
        .iter()
        .map(|ef| {
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
                scheme: ef.scheme.clone(),
                origin: ef.origin.clone(),
            }
        })
        .collect()
}

fn extract_reexported_fns(typed: &TypedModule) -> Vec<ReexportedFnEntry> {
    typed
        .reexported_fn_types
        .iter()
        .map(|ef| {
            // Look up canonical defining module from fn_types
            let canonical_module = typed
                .fn_types_by_name
                .get(&ef.name)
                .and_then(|&idx| typed.fn_types.get(idx))
                .map(|entry| entry.qualified_name.module_path.clone())
                .unwrap_or_else(|| typed.module_path.clone());

            ReexportedFnEntry {
                local_name: ef.name.clone(),
                canonical_ref: CanonicalRef {
                    module: ModulePath::new(&canonical_module),
                    symbol: LocalSymbolKey::Function(ef.name.clone()),
                },
                scheme: ef.scheme.clone(),
                origin: ef.origin.clone(),
            }
        })
        .collect()
}

fn extract_exported_types(typed: &TypedModule) -> Vec<TypeSummary> {
    typed
        .exported_type_infos
        .iter()
        .filter_map(|(name, info)| {
            let vis = typed
                .type_visibility
                .get(name)
                .copied()
                .unwrap_or(Visibility::Private);
            if vis == Visibility::Private {
                return None;
            }

            let parent_name = name.clone();
            let kind = match &info.kind {
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
            target_type: inst.target_type.clone(),
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

fn extract_extern_fns(externs: &[ExternFnInfo]) -> Vec<ExternFnSummary> {
    externs
        .iter()
        .map(|ef| ExternFnSummary {
            name: ef.name.clone(),
            declaring_module: ModulePath::new(&ef.declaring_module_path),
            host_module_path: ef.module_path.clone(),
            target: ef.target.clone(),
            param_types: ef.param_types.clone(),
            return_type: ef.return_type.clone(),
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
        })
        .collect()
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
                    .map(|p| format!("{p}"))
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

    if !iface.extern_fns.is_empty() {
        out.push_str("\nextern fns:\n");
        let mut efns: Vec<_> = iface.extern_fns.iter().collect();
        efns.sort_by_key(|e| &e.name);
        for e in efns {
            out.push_str(&format!(
                "  {} ({:?} \"{}\") : ({}) -> {}\n",
                e.name,
                e.target,
                e.host_module_path,
                e.param_types
                    .iter()
                    .map(|t| format!("{t}"))
                    .collect::<Vec<_>>()
                    .join(", "),
                e.return_type,
            ));
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
