use std::collections::{HashMap, HashSet};

use krypton_parser::ast::{Decl, ExternTarget, FnDecl, Module, Span, TypeDeclKind, Visibility};

use crate::overload::{fn_param_types, types_overlap};
use crate::trait_registry::TraitRegistry;
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{
    self, ExportedTraitDef, ExternFnInfo, ExternTraitInfo, ExternTypeInfo, InstanceDefInfo,
    StructDecl, SumDecl, TraitDefInfo, TraitName, TypedExpr, TypedFnDecl, TypedModule,
};
use crate::types::{
    BindingSource, Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId,
};
use crate::unify::{SpannedTypeError, TypeError};

use super::checks;
use super::display::build_type_param_map;
use super::extern_decl::{process_extern_methods, ExternBindingInfo, PendingExternTrait};
use super::helpers::{
    constructor_binding_kind_for_decl, constructor_names, free_vars, spanned,
    QualifiedModuleBinding,
};
use super::import_ctx::ImportContext;


/// Result of `infer_function_bodies`: fn decls, schemes, typed bodies,
/// constraint requirements.
pub(crate) type InferFunctionBodiesResult<'a> = (
    Vec<&'a krypton_parser::ast::FnDecl>,
    Vec<Option<TypeScheme>>,
    Vec<Option<TypedExpr>>,
    HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
);

/// Result of `process_traits_and_deriving`: trait registry, exported defs,
/// extern trait infos, derived/imported instance defs, and trait method map.
pub(crate) type TraitsAndDerivingResult = (
    TraitRegistry,
    Vec<ExportedTraitDef>,
    Vec<ExternTraitInfo>,
    Vec<InstanceDefInfo>,
    Vec<InstanceDefInfo>,
    HashMap<String, TraitName>,
);

/// Result of processing a module's local extern declarations.
pub(crate) type LocalExternResult = (
    Vec<ExternFnInfo>,
    Vec<ExternTypeInfo>,
    Vec<ExternBindingInfo>,
    HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
    Vec<PendingExternTrait>,
);


/// State accumulated during the bootstrap phases of module inference
/// (env setup, import processing, extern loading, type registration).
/// Consumed by `assemble_typed_module` at the end.
pub(crate) struct ModuleInferenceState {
    // Core inference state
    pub(super) env: TypeEnv,
    pub(super) subst: Substitution,
    pub(super) gen: TypeVarGen,
    pub(super) registry: TypeRegistry,
    pub(super) let_own_spans: HashSet<Span>,
    pub(super) lambda_own_captures: HashMap<Span, String>,
    // Import accumulation
    pub(super) imports: ImportContext,
    pub(super) imported_trait_defs: Vec<ExportedTraitDef>,
    pub(super) imported_trait_names: HashSet<String>,
    pub(super) trait_aliases: Vec<(String, TraitName)>,
    pub(super) qualified_modules: HashMap<String, QualifiedModuleBinding>,
    // Re-export state
    pub(super) reexported_fn_types: Vec<typed_ast::ExportedFn>,
    pub(super) reexported_type_names: Vec<String>,
    pub(super) reexported_type_visibility: HashMap<String, Visibility>,
    pub(super) reexported_trait_defs: Vec<ExportedTraitDef>,
    // Prelude tracking
    pub(super) prelude_imported_names: HashSet<String>,
}

impl ModuleInferenceState {
    pub(super) fn new(is_core_module: bool) -> Self {
        let mut env = TypeEnv::new();
        let mut gen = TypeVarGen::new();
        let mut registry = TypeRegistry::new();
        registry.register_builtins(&mut gen);

        crate::intrinsics::register_intrinsics(&mut env, &mut gen, is_core_module);

        ModuleInferenceState {
            env,
            subst: Substitution::new(),
            gen,
            registry,
            let_own_spans: HashSet::new(),
            lambda_own_captures: HashMap::new(),
            imports: ImportContext::new(),
            imported_trait_defs: Vec::new(),
            imported_trait_names: HashSet::new(),
            trait_aliases: Vec::new(),
            qualified_modules: HashMap::new(),
            reexported_fn_types: Vec::new(),
            reexported_type_names: Vec::new(),
            reexported_type_visibility: HashMap::new(),
            reexported_trait_defs: Vec::new(),
            prelude_imported_names: HashSet::new(),
        }
    }

    pub(super) fn process_local_externs(
        &mut self,
        module: &Module,
        mod_path: &str,
    ) -> Result<LocalExternResult, SpannedTypeError> {
        let mut extern_fns: Vec<ExternFnInfo> = Vec::new();
        let mut extern_types: Vec<ExternTypeInfo> = Vec::new();
        let mut extern_bindings: Vec<ExternBindingInfo> = Vec::new();
        let mut extern_fn_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> =
            HashMap::new();
        let mut pending_extern_traits: Vec<PendingExternTrait> = Vec::new();

        // Build trait name lookup from imported trait defs
        let mut trait_name_lookup: HashMap<String, TraitName> = HashMap::new();
        for td in &self.imported_trait_defs {
            trait_name_lookup.insert(
                td.name.clone(),
                TraitName::new(td.module_path.clone(), td.name.clone()),
            );
        }

        for decl in &module.decls {
            if let Decl::Extern {
                target,
                module_path,
                alias,
                is_trait,
                type_params,
                lifts,
                methods,
                span,
                ..
            } = decl
            {
                // Extern traits are collected for registration in the trait phase
                if *is_trait {
                    if matches!(target, ExternTarget::Js) {
                        return Err(spanned(
                            TypeError::ExternTraitOnJsTarget {
                                name: alias.clone().unwrap_or_default(),
                            },
                            *span,
                        ));
                    }
                    if let Some(name) = alias {
                        pending_extern_traits.push(PendingExternTrait {
                            name: name.clone(),
                            java_interface: module_path.clone(),
                            type_params: type_params.clone(),
                            methods: methods.clone(),
                            span: *span,
                        });
                    }
                    continue;
                }

                // Register type binding if `as Name[params]` is present
                let mut tp_map: Option<HashMap<String, TypeVarId>> = None;
                let mut tp_arity: Option<HashMap<String, usize>> = None;
                if let Some(name) = alias {
                    // Check if already registered (e.g. Vec is a builtin)
                    let type_param_vars = if let Some(existing) = self.registry.lookup_type(name) {
                        existing.type_param_vars.clone()
                    } else {
                        let vars: Vec<_> = type_params.iter().map(|_| self.gen.fresh()).collect();
                        self.registry
                            .register_type(crate::type_registry::TypeInfo {
                                name: name.clone(),
                                type_params: type_params.clone(),
                                type_param_vars: vars.clone(),
                                kind: crate::type_registry::TypeKind::Record { fields: vec![] },
                                lifts: lifts.clone(),
                                is_prelude: false,
                            })
                            .map_err(|e| spanned(e, *span))?;
                        vars
                    };
                    self.registry.mark_user_visible(name);
                    extern_types.push(ExternTypeInfo {
                        krypton_name: name.clone(),
                        host_module: module_path.clone(),
                        target: target.clone(),
                        lifts: lifts.clone(),
                    });

                    // Build type_param_map for method resolution
                    if !type_params.is_empty() {
                        let (map, arity) =
                            build_type_param_map(type_params, &type_param_vars, name);
                        tp_map = Some(map);
                        tp_arity = Some(arity);
                    }
                }

                {
                    let tp_names = type_params.as_slice();
                    let result = process_extern_methods(
                        module_path,
                        target,
                        methods,
                        &mut self.env,
                        &mut self.gen,
                        &self.registry,
                        &trait_name_lookup,
                        mod_path,
                        *span,
                        tp_map.as_ref(),
                        tp_arity.as_ref(),
                        if tp_map.is_some() {
                            Some(tp_names)
                        } else {
                            None
                        },
                        alias.as_deref(),
                    )?;

                    for (name, reqs) in result.fn_constraints {
                        extern_fn_constraints.insert(name, reqs);
                    }
                    extern_bindings.extend(result.bindings);
                    extern_fns.extend(result.extern_fns);
                }
            }
        }
        Ok((
            extern_fns,
            extern_types,
            extern_bindings,
            extern_fn_constraints,
            pending_extern_traits,
        ))
    }

    pub(super) fn cleanup_prelude_shadows(&mut self, module: &Module) {
        for decl in &module.decls {
            match decl {
                Decl::Extern { methods, .. } => {
                    for m in methods {
                        self.imports.remove_prelude_fn(&m.name);
                    }
                }
                Decl::DefFn(f) => {
                    self.imports.remove_prelude_fn(&f.name);
                }
                _ => {}
            }
        }
    }

    pub(super) fn resolve_fn_param_types_for_overlap(&self, f: &FnDecl) -> Option<Vec<Type>> {
        super::traits_register::resolve_fn_param_types_for_overlap(f, &self.registry)
    }

    pub(super) fn check_duplicate_function_names(&self, module: &Module) -> Result<(), SpannedTypeError> {
        // Collect all extern method names (same name across targets is fine)
        let mut extern_names: HashSet<&str> = HashSet::new();
        for decl in &module.decls {
            if let Decl::Extern { methods, .. } = decl {
                for m in methods {
                    extern_names.insert(&m.name);
                }
            }
        }
        // Group DefFn by name
        let mut groups: HashMap<&str, Vec<&FnDecl>> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefFn(f) = decl {
                if extern_names.contains(f.name.as_str()) {
                    return Err(spanned(
                        TypeError::DuplicateFunction {
                            name: f.name.clone(),
                        },
                        f.span,
                    ));
                }
                groups.entry(&f.name).or_default().push(f);
            }
        }
        // Check each group with >1 definition for valid overloading
        for (name, fns) in &groups {
            if fns.len() <= 1 {
                continue;
            }
            let last_span = fns.last().unwrap().span;
            // All defs must have type annotations on all params
            let param_types: Vec<Vec<Type>> = {
                let mut pts = Vec::new();
                for f in fns {
                    match self.resolve_fn_param_types_for_overlap(f) {
                        Some(tys) => pts.push(tys),
                        None => {
                            return Err(spanned(
                                TypeError::LocalOverloadMissingAnnotation {
                                    name: name.to_string(),
                                },
                                last_span,
                            ));
                        }
                    }
                }
                pts
            };
            // All arities must match
            let arities: Vec<usize> = param_types.iter().map(|p| p.len()).collect();
            if arities.iter().any(|a| *a != arities[0]) {
                return Err(spanned(
                    TypeError::LocalOverloadArityMismatch {
                        name: name.to_string(),
                        arities,
                    },
                    last_span,
                ));
            }
            // Pairwise overlap check
            for i in 0..param_types.len() {
                for j in (i + 1)..param_types.len() {
                    if types_overlap(&param_types[i], &param_types[j]) {
                        return Err(spanned(
                            TypeError::LocalOverloadOverlap {
                                name: name.to_string(),
                            },
                            fns[j].span,
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn check_explicit_import_shadows(&self, module: &Module) -> Result<(), SpannedTypeError> {
        for decl in &module.decls {
            match decl {
                Decl::DefFn(f) => {
                    let non_prelude_imports: Vec<_> = self
                        .imports
                        .get_by_name(&f.name)
                        .filter(|imp| !imp.is_prelude)
                        .collect();
                    if non_prelude_imports.is_empty() {
                        continue;
                    }
                    // Try to resolve local param types for overload checking
                    let local_params = match self.resolve_fn_param_types_for_overlap(f) {
                        Some(params) => params,
                        None => {
                            // Unannotated — keep current error behavior
                            let imp = &non_prelude_imports[0];
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: f.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                f.span,
                            ));
                        }
                    };
                    for imp in &non_prelude_imports {
                        let imp_params = match fn_param_types(&imp.scheme.ty) {
                            Some(params) => params,
                            None => {
                                // Import is not a function — conflict
                                return Err(spanned(
                                    TypeError::DefinitionConflictsWithImport {
                                        def_name: f.name.clone(),
                                        source_module: imp.qualified_name.module_path.clone(),
                                    },
                                    f.span,
                                ));
                            }
                        };
                        if imp_params.len() != local_params.len() {
                            return Err(spanned(
                                TypeError::ImportOverloadArityMismatch {
                                    name: f.name.clone(),
                                    arities: vec![
                                        ("(local)".to_string(), local_params.len()),
                                        (
                                            imp.qualified_name.module_path.clone(),
                                            imp_params.len(),
                                        ),
                                    ],
                                },
                                f.span,
                            ));
                        }
                        if types_overlap(&local_params, &imp_params) {
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: f.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                f.span,
                            ));
                        }
                    }
                }
                Decl::Extern { methods, .. } => {
                    for m in methods {
                        if let Some(imp) = self
                            .imports
                            .get_by_name(&m.name)
                            .find(|imp| !imp.is_prelude)
                        {
                            return Err(spanned(
                                TypeError::DefinitionConflictsWithImport {
                                    def_name: m.name.clone(),
                                    source_module: imp.qualified_name.module_path.clone(),
                                },
                                m.span,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    pub(super) fn preregister_type_names(&mut self, module: &Module) {
        for decl in &module.decls {
            if let Decl::DefType(type_decl) = decl {
                self.registry.register_name(&type_decl.name);
                self.registry.mark_user_visible(&type_decl.name);
            }
        }
    }

    pub(super) fn process_local_type_decls(
        &mut self,
        module: &Module,
        module_path: &str,
    ) -> Result<Vec<(String, TypeScheme)>, SpannedTypeError> {
        let mut constructor_schemes: Vec<(String, TypeScheme)> = Vec::new();
        for decl in &module.decls {
            if let Decl::DefType(type_decl) = decl {
                if let Some(existing) = self.registry.lookup_type(&type_decl.name) {
                    if existing.is_prelude {
                        if let crate::type_registry::TypeKind::Sum { variants } = &existing.kind {
                            for v in variants {
                                self.env.unbind(&v.name);
                            }
                        }
                        self.imports.imported_type_info.remove(&type_decl.name);
                    }
                }

                let constructors =
                    type_registry::process_type_decl(type_decl, &mut self.registry, &mut self.gen)
                        .map_err(|e| spanned(e, type_decl.span))?;

                // E0109: value-position uses of resource-carrying types
                // inside record field / variant payload annotations must be
                // spelled `~T`. Walk per-field TypeExpr spans so the error
                // points at the offending annotation rather than the whole
                // type declaration.
                if let Some(info) = self.registry.lookup_type(&type_decl.name) {
                    match (&type_decl.kind, &info.kind) {
                        (
                            krypton_parser::ast::TypeDeclKind::Record { fields: ast_fields },
                            crate::type_registry::TypeKind::Record { fields: info_fields },
                        ) => {
                            for ((_, ast_ty), (_, resolved_ty)) in
                                ast_fields.iter().zip(info_fields.iter())
                            {
                                crate::ownership::check_no_bare_resource_use(
                                    resolved_ty,
                                    &self.registry,
                                    ast_ty.span(),
                                    crate::type_error::BareResourceContext::RecordField,
                                )?;
                            }
                        }
                        (
                            krypton_parser::ast::TypeDeclKind::Sum { variants: ast_variants },
                            crate::type_registry::TypeKind::Sum { variants: info_variants },
                        ) => {
                            for (ast_v, info_v) in
                                ast_variants.iter().zip(info_variants.iter())
                            {
                                for (ast_ty, resolved_ty) in
                                    ast_v.fields.iter().zip(info_v.fields.iter())
                                {
                                    crate::ownership::check_no_bare_resource_use(
                                        resolved_ty,
                                        &self.registry,
                                        ast_ty.span(),
                                        crate::type_error::BareResourceContext::VariantPayload,
                                    )?;
                                }
                            }
                        }
                        _ => {}
                    }
                }

                for (name, scheme) in constructors {
                    // Value-namespace check: a constructor may not collide with
                    // another local constructor of a *different* type. Prelude
                    // constructors are shadowable and therefore skipped.
                    if let Some(existing) = self.env.lookup_entry(&name) {
                        if let BindingSource::Constructor {
                            type_qualified_name,
                            ..
                        } = &existing.source
                        {
                            if type_qualified_name.local_name != type_decl.name {
                                let existing_is_prelude = self
                                    .registry
                                    .lookup_type(&type_qualified_name.local_name)
                                    .is_some_and(|t| t.is_prelude);
                                if !existing_is_prelude {
                                    return Err(spanned(
                                        TypeError::DuplicateConstructor {
                                            name: name.clone(),
                                            first_type: type_qualified_name.local_name.clone(),
                                            second_type: type_decl.name.clone(),
                                        },
                                        type_decl.span,
                                    ));
                                }
                            }
                        }
                    }
                    self.env.bind_constructor(
                        name.clone(),
                        scheme.clone(),
                        module_path.to_string(),
                        type_decl.name.clone(),
                        name.clone(),
                        constructor_binding_kind_for_decl(type_decl, &name),
                    );
                    constructor_schemes.push((name, scheme));
                }
            }
        }
        Ok(constructor_schemes)
    }

    /// Assemble the final TypedModule from accumulated state and inference-phase outputs.
    ///
    /// Extracted from `infer_module_inner` specifically to reduce that function's
    /// stack frame size — bundling the args into a struct here would risk pushing
    /// the inputs back onto the caller's frame and undoing that optimization, so
    /// the wide signature is intentional.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn assemble_typed_module(
        self,
        module: &Module,
        module_path: String,
        fn_decls: &[&krypton_parser::ast::FnDecl],
        result_schemes: Vec<Option<TypeScheme>>,
        fn_bodies: Vec<Option<TypedExpr>>,
        instance_defs: Vec<InstanceDefInfo>,
        derived_instance_defs: Vec<InstanceDefInfo>,
        _imported_instance_defs: Vec<InstanceDefInfo>,
        fn_constraint_requirements: &mut HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
        _trait_method_map: &HashMap<String, TraitName>,
        trait_registry: &TraitRegistry,
        exported_trait_defs: Vec<ExportedTraitDef>,
        extern_fns: Vec<ExternFnInfo>,
        extern_types: Vec<ExternTypeInfo>,
        extern_traits: Vec<ExternTraitInfo>,
        extern_bindings: Vec<ExternBindingInfo>,
        constructor_schemes: Vec<(String, TypeScheme)>,
        interface_cache: &HashMap<String, crate::module_interface::ModuleInterface>,
    ) -> Result<TypedModule, Vec<SpannedTypeError>> {
        let mut instance_defs = instance_defs;
        instance_defs.extend(derived_instance_defs);

        let mut results: Vec<typed_ast::FnTypeEntry> = self
            .imports
            .imported_fn_types
            .into_iter()
            .map(|f| typed_ast::FnTypeEntry {
                name: f.name,
                scheme: f.scheme,
                origin: f.origin,
                qualified_name: f.qualified_name,
            })
            .collect();
        results.extend(
            constructor_schemes
                .iter()
                .map(|(n, s)| typed_ast::FnTypeEntry {
                    name: n.clone(),
                    scheme: s.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        n.clone(),
                    ),
                }),
        );
        results.extend(
            extern_bindings
                .iter()
                .map(|binding| typed_ast::FnTypeEntry {
                    name: binding.name.clone(),
                    scheme: binding.scheme.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        binding.name.clone(),
                    ),
                }),
        );
        results.extend(
            fn_decls
                .iter()
                .enumerate()
                .map(|(i, d)| typed_ast::FnTypeEntry {
                    name: d.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        d.name.clone(),
                    ),
                }),
        );
        // Add instance method types to the flat list for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(
                    &inst.trait_name.local_name,
                    &inst.target_type_name,
                    &m.name,
                );
                results.push(typed_ast::FnTypeEntry {
                    name: qualified.clone(),
                    scheme: m.scheme.clone(),
                    origin: None,
                    qualified_name: typed_ast::QualifiedName::new(
                        module_path.to_string(),
                        qualified,
                    ),
                });
            }
        }

        // Build exported_fn_types: the public API surface for downstream importers.
        // Includes pub (transparent) constructors, pub local functions, pub extern methods,
        // and instance methods.
        // Does NOT include imported functions.
        let mut exported_fn_types: Vec<typed_ast::ExportedFn> = Vec::new();

        // 1. Constructors for pub (transparent) types only
        for (cname, scheme) in &constructor_schemes {
            let is_pub_open = module.decls.iter().any(|d| {
                if let Decl::DefType(td) = d {
                    matches!(td.visibility, Visibility::Pub)
                        && constructor_names(td).contains(cname)
                } else {
                    false
                }
            });
            if is_pub_open {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: cname.clone(),
                    scheme: scheme.clone(),
                    origin: None,
                    def_span: None,
                    qualified_name: None,
                });
            }
        }

        // 2. Local pub function declarations
        for (i, decl) in fn_decls.iter().enumerate() {
            if matches!(decl.visibility, Visibility::Pub) {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: decl.name.clone(),
                    scheme: result_schemes[i].clone().unwrap(),
                    origin: None,
                    def_span: Some(decl.span),
                    qualified_name: None,
                });
            }
        }

        // 3. Local pub extern methods
        for binding in &extern_bindings {
            if matches!(binding.visibility, Visibility::Pub) {
                exported_fn_types.push(typed_ast::ExportedFn {
                    name: binding.name.clone(),
                    scheme: binding.scheme.clone(),
                    origin: None,
                    def_span: Some(binding.def_span),
                    qualified_name: None,
                });
            }
        }

        let mut functions: Vec<TypedFnDecl> = Vec::new();
        let mut fn_bodies = fn_bodies;
        for (i, decl) in fn_decls.iter().enumerate() {
            let mut body = fn_bodies[i].take().unwrap();
            typed_ast::apply_subst(&mut body, &self.subst);
            functions.push(TypedFnDecl {
                name: decl.name.clone(),
                visibility: decl.visibility,
                params: decl
                    .params
                    .iter()
                    .map(|p| crate::typed_ast::TypedParam {
                        name: p.name.clone(),
                        mode: p.mode,
                    })
                    .collect(),
                body,
                close_self_type: None,
                fn_scope_id: crate::typed_ast::ScopeId(u32::MAX),
            });
        }
        // Build temporary flat list of instance method bodies for internal analysis passes
        for inst in &instance_defs {
            for m in &inst.methods {
                let qualified = typed_ast::mangled_method_name(
                    &inst.trait_name.local_name,
                    &inst.target_type_name,
                    &m.name,
                );
                let close_self_type =
                    if inst.trait_name.local_name == "Disposable" && m.name == "dispose" {
                        Some(inst.target_type_name.clone())
                    } else {
                        None
                    };
                functions.push(TypedFnDecl {
                    name: qualified,
                    visibility: Visibility::Pub,
                    params: m.params.clone(),
                    body: m.body.clone(),
                    close_self_type,
                    fn_scope_id: crate::typed_ast::ScopeId(u32::MAX),
                });
            }
        }

        let fn_schemes: HashMap<String, TypeScheme> = results
            .iter()
            .map(|e| (e.name.clone(), e.scheme.clone()))
            .collect();
        let mut validation_errors: Vec<SpannedTypeError> = Vec::new();
        for func in &functions {
            let current_requirements = fn_schemes
                .get(&func.name)
                .map(|s| s.constraints.as_slice())
                .unwrap_or(&[]);
            // Monomorphic functions have no type variables
            let func_var_names = fn_schemes
                .get(&func.name)
                .map(|s| &s.var_names)
                .cloned()
                .unwrap_or_default();
            if let Err(e) = checks::check_constrained_function_refs(
                &func.body,
                current_requirements,
                &fn_schemes,
                trait_registry,
                &func_var_names,
            ) {
                validation_errors.push(e);
            }
        }

        // fn_schemes already includes imported function schemes with constraints embedded

        // Detect implicit trait constraints from body and merge into fn_constraint_requirements
        for func in &functions {
            let mut fn_type_param_vars: HashSet<TypeVarId> = HashSet::new();
            if let Some(scheme) = fn_schemes.get(&func.name) {
                if let Type::Fn(param_types, ret_ty) = &scheme.ty {
                    for (_, pty) in param_types.iter() {
                        for v in free_vars(pty) {
                            fn_type_param_vars.insert(v);
                        }
                    }
                    for v in free_vars(ret_ty) {
                        fn_type_param_vars.insert(v);
                    }
                }
            }
            let mut constraints = Vec::new();
            checks::detect_trait_constraints(
                &func.body,
                trait_registry,
                &self.subst,
                &fn_type_param_vars,
                &fn_schemes,
                &mut constraints,
            );
            if !constraints.is_empty() {
                constraints.sort();
                constraints.dedup();
                // Merge into fn_constraint_requirements (dedup by trait+var)
                let existing = fn_constraint_requirements
                    .entry(func.name.clone())
                    .or_default();
                for (trait_name, type_vars) in constraints {
                    if !existing
                        .iter()
                        .any(|(t, v)| t == &trait_name && *v == type_vars)
                    {
                        existing.push((trait_name, type_vars));
                    }
                }
            }
        }

        // Fold final constraints into TypeSchemes in fn_types (results) so they
        // propagate to importers via exported_fn_types without a side-channel map.
        for entry in &mut results {
            if let Some(reqs) = fn_constraint_requirements.get(&entry.name) {
                if entry.scheme.constraints.is_empty() && !reqs.is_empty() {
                    entry.scheme.constraints = reqs.clone();
                }
            }
        }
        // Also update exported_fn_types (built earlier from result_schemes)
        for ef in &mut exported_fn_types {
            if let Some(reqs) = fn_constraint_requirements.get(&ef.name) {
                if ef.scheme.constraints.is_empty() && !reqs.is_empty() {
                    ef.scheme.constraints = reqs.clone();
                }
            }
        }

        let mut trait_defs = Vec::new();
        for info in trait_registry.traits().values() {
            let is_imported = self.imported_trait_names.contains(&info.name);
            let method_info: Vec<(String, usize)> = info
                .methods
                .iter()
                .map(|m| (m.name.clone(), m.param_types.len()))
                .collect();
            let method_tc_types: HashMap<String, (Vec<(crate::types::ParamMode, Type)>, Type)> =
                info.methods
                    .iter()
                    .map(|m| {
                        (
                            m.name.clone(),
                            (m.param_types.clone(), m.return_type.clone()),
                        )
                    })
                    .collect();
            let method_constraints: HashMap<String, Vec<(TraitName, Vec<TypeVarId>)>> = info
                .methods
                .iter()
                .filter(|m| !m.constraints.is_empty())
                .map(|m| (m.name.clone(), m.constraints.clone()))
                .collect();
            trait_defs.push(TraitDefInfo {
                name: info.name.clone(),
                trait_id: TraitName::new(info.module_path.clone(), info.name.clone()),
                methods: method_info,
                is_imported,
                type_var_id: info.type_var_id,
                type_var_ids: info.type_var_ids.clone(),
                method_tc_types,
                method_constraints,
            });
        }

        // Convert FnTypeEntry to tuple format for ownership/auto_close APIs
        let results_tuples: Vec<(String, TypeScheme, Option<TraitName>)> = results
            .iter()
            .map(|e| (e.name.clone(), e.scheme.clone(), e.origin.clone()))
            .collect();

        let (ownership_result, ownership_errors) = crate::ownership::check_ownership(
            module,
            &functions,
            &results_tuples,
            &self.registry,
            &self.let_own_spans,
            &self.lambda_own_captures,
            &self.imports.imported_fn_qualifiers,
        );
        let has_ownership_errors = !ownership_errors.is_empty();
        validation_errors.extend(ownership_errors);

        // Filter to exported functions only for cross-module propagation
        let exported_names: HashSet<&str> = exported_fn_types
            .iter()
            .map(|ef| ef.name.as_str())
            .collect();
        let exported_fn_qualifiers: HashMap<_, _> = ownership_result
            .fn_qualifiers
            .into_iter()
            .filter(|(name, _)| exported_names.contains(name.as_str()))
            .collect();

        // Stamp ScopeIds on every typed function body before analysis/lowering.
        // Both auto_close and ir::lower rely on scope identity being stable and
        // unique — ScopeIds replace the fragile span-based lookup.
        crate::scope_ids::stamp_functions(&mut functions);

        // Only run auto_close if ownership checking passed — auto_close depends on
        // complete ownership results and may encounter unexpected types otherwise.
        let auto_close = if !has_ownership_errors {
            let (auto_close, auto_close_errors) = crate::auto_close::compute_auto_close(
                &functions,
                &results_tuples,
                trait_registry,
                &ownership_result.moves,
            );
            validation_errors.extend(auto_close_errors);
            auto_close
        } else {
            crate::typed_ast::AutoCloseInfo::default()
        };

        if !validation_errors.is_empty() {
            validation_errors.sort_by_key(|e| e.span);
            return Err(validation_errors);
        }

        let struct_decls: Vec<_> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Record { fields } => Some(StructDecl {
                        name: td.name.clone(),
                        type_params: td.type_params.clone(),
                        fields: fields.clone(),
                        qualified_name: typed_ast::QualifiedName::new(
                            module_path.to_string(),
                            td.name.clone(),
                        ),
                    }),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let sum_decls: Vec<SumDecl> = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::DefType(td) => match &td.kind {
                    TypeDeclKind::Sum { variants } => Some(SumDecl {
                        name: td.name.clone(),
                        type_params: td.type_params.clone(),
                        variants: variants.clone(),
                        qualified_name: typed_ast::QualifiedName::new(
                            module_path.to_string(),
                            td.name.clone(),
                        ),
                    }),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        let _local_type_names: HashSet<String> = module
            .decls
            .iter()
            .filter_map(|d| {
                if let Decl::DefType(td) = d {
                    Some(td.name.clone())
                } else {
                    None
                }
            })
            .collect();
        let mut type_visibility: HashMap<String, Visibility> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                type_visibility.insert(td.name.clone(), td.visibility);
            }
            if let Decl::Extern {
                alias: Some(name),
                alias_visibility,
                is_trait: false,
                ..
            } = decl
            {
                type_visibility.insert(
                    name.clone(),
                    alias_visibility.unwrap_or(Visibility::Private),
                );
            }
        }

        let mut exported_trait_defs = exported_trait_defs;
        exported_trait_defs.extend(self.reexported_trait_defs);

        // Build exported_type_infos from fully-resolved TypeInfo in the registry.
        // This allows importers to register types without re-resolving from AST.
        let mut exported_type_infos: HashMap<String, typed_ast::ExportedTypeInfo> = HashMap::new();
        for decl in &module.decls {
            if let Decl::DefType(td) = decl {
                if matches!(td.visibility, Visibility::Private) {
                    continue;
                }
                if let Some(type_info) = self.registry.lookup_type(&td.name) {
                    let kind = match &type_info.kind {
                        crate::type_registry::TypeKind::Record { fields } => {
                            typed_ast::ExportedTypeKind::Record {
                                fields: fields.clone(),
                            }
                        }
                        crate::type_registry::TypeKind::Sum { variants } => {
                            typed_ast::ExportedTypeKind::Sum {
                                variants: variants
                                    .iter()
                                    .map(|v| typed_ast::ExportedVariantInfo {
                                        name: v.name.clone(),
                                        fields: v.fields.clone(),
                                    })
                                    .collect(),
                            }
                        }
                    };
                    exported_type_infos.insert(
                        td.name.clone(),
                        typed_ast::ExportedTypeInfo {
                            name: td.name.clone(),
                            source_module: module_path.to_string(),
                            type_params: td.type_params.clone(),
                            type_param_vars: type_info.type_param_vars.clone(),
                            kind,
                            lifts: type_info.lifts.clone(),
                        },
                    );
                }
            }
        }

        // Include extern type aliases in exported_type_infos so they flow
        // through the interface like any other type — consumers register
        // them uniformly via register_type_from_export.
        for decl in &module.decls {
            if let Decl::Extern {
                alias: Some(name),
                is_trait: false,
                ..
            } = decl
            {
                if exported_type_infos.contains_key(name) {
                    continue;
                }
                if let Some(type_info) = self.registry.lookup_type(name) {
                    exported_type_infos.insert(
                        name.clone(),
                        typed_ast::ExportedTypeInfo {
                            name: name.clone(),
                            source_module: module_path.to_string(),
                            type_params: type_info.type_params.clone(),
                            type_param_vars: type_info.type_param_vars.clone(),
                            kind: typed_ast::ExportedTypeKind::Opaque,
                            lifts: type_info.lifts.clone(),
                        },
                    );
                }
            }
        }

        // Include imported types (sum and record) in exported_type_infos so
        // IR lowering can resolve them without AST fallback.
        for (type_name, (source_path, _vis)) in &self.imports.imported_type_info {
            if exported_type_infos.contains_key(type_name) {
                continue;
            }
            if let Some(iface) = interface_cache.get(source_path.as_str()) {
                if let Some(ts) = iface.exported_types.iter().find(|t| t.name == *type_name) {
                    let export =
                        crate::module_interface::type_summary_to_export_info(ts, source_path);
                    exported_type_infos.insert(type_name.clone(), export);
                }
            }
        }

        let fn_types_by_name: HashMap<String, usize> = results
            .iter()
            .enumerate()
            .map(|(i, e)| (e.name.clone(), i))
            .collect();

        Ok(TypedModule {
            module_path,
            fn_types: results,
            fn_types_by_name,
            exported_fn_types,
            functions,
            trait_defs,
            instance_defs,
            extern_fns,
            extern_types,
            extern_traits,
            struct_decls,
            sum_decls,
            type_visibility,
            reexported_fn_types: self.reexported_fn_types,
            reexported_type_names: self.reexported_type_names,
            reexported_type_visibility: self.reexported_type_visibility,
            exported_trait_defs,
            exported_type_infos,
            auto_close,
            exported_fn_qualifiers,
            module_source: None,
        })
    }
}
