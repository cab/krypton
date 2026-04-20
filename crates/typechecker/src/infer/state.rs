use rustc_hash::{FxHashMap, FxHashSet};

use krypton_parser::ast::{Decl, FnDecl, Module, Span, Visibility};

use crate::overload::types_overlap;
use crate::trait_registry::TraitRegistry;
use crate::type_registry::{self, TypeRegistry};
use crate::typed_ast::{
    self, ExportedTraitDef, ExternTraitInfo, InstanceDefInfo, TraitName, TypedExpr,
};
use crate::types::{
    BindingSource, Substitution, Type, TypeEnv, TypeScheme, TypeVarGen, TypeVarId,
};
use crate::unify::{SpannedTypeError, TypeError};

use super::helpers::{constructor_binding_kind_for_decl, spanned, QualifiedModuleBinding};
use super::import_ctx::ImportContext;


/// Result of `infer_function_bodies`: fn decls, schemes, typed bodies,
/// constraint requirements.
pub(crate) type InferFunctionBodiesResult<'a> = (
    Vec<&'a krypton_parser::ast::FnDecl>,
    Vec<Option<TypeScheme>>,
    Vec<Option<TypedExpr>>,
    FxHashMap<String, Vec<(TraitName, Vec<TypeVarId>)>>,
);

/// Result of `process_traits_and_deriving`: trait registry, exported defs,
/// extern trait infos, derived/imported instance defs, and trait method map.
pub(crate) type TraitsAndDerivingResult = (
    TraitRegistry,
    Vec<ExportedTraitDef>,
    Vec<ExternTraitInfo>,
    Vec<InstanceDefInfo>,
    Vec<InstanceDefInfo>,
    FxHashMap<String, TraitName>,
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
    pub(super) let_own_spans: FxHashSet<Span>,
    pub(super) lambda_own_captures: FxHashMap<Span, String>,
    // Import accumulation
    pub(super) imports: ImportContext,
    pub(super) imported_trait_defs: Vec<ExportedTraitDef>,
    pub(super) imported_trait_names: FxHashSet<String>,
    pub(super) trait_aliases: Vec<(String, TraitName)>,
    pub(super) qualified_modules: FxHashMap<String, QualifiedModuleBinding>,
    // Re-export state
    pub(super) reexported_fn_types: Vec<typed_ast::ExportedFn>,
    pub(super) reexported_type_names: Vec<String>,
    pub(super) reexported_type_visibility: FxHashMap<String, Visibility>,
    pub(super) reexported_trait_defs: Vec<ExportedTraitDef>,
    // Prelude tracking
    pub(super) prelude_imported_names: FxHashSet<String>,
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
            let_own_spans: FxHashSet::default(),
            lambda_own_captures: FxHashMap::default(),
            imports: ImportContext::new(),
            imported_trait_defs: Vec::new(),
            imported_trait_names: FxHashSet::default(),
            trait_aliases: Vec::new(),
            qualified_modules: FxHashMap::default(),
            reexported_fn_types: Vec::new(),
            reexported_type_names: Vec::new(),
            reexported_type_visibility: FxHashMap::default(),
            reexported_trait_defs: Vec::new(),
            prelude_imported_names: FxHashSet::default(),
        }
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

    pub(super) fn check_duplicate_function_names(&self, module: &Module) -> Result<(), SpannedTypeError> {
        // Collect all extern method names (same name across targets is fine)
        let mut extern_names: FxHashSet<&str> = FxHashSet::default();
        for decl in &module.decls {
            if let Decl::Extern { methods, .. } = decl {
                for m in methods {
                    extern_names.insert(&m.name);
                }
            }
        }
        // Group DefFn by name
        let mut groups: FxHashMap<&str, Vec<&FnDecl>> = FxHashMap::default();
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
                    match super::traits_register::resolve_fn_param_types_for_overlap(f, &self.registry) {
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

}
