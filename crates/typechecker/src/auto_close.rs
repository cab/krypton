use crate::trait_registry::TraitRegistry;
use crate::typed_ast::{AutoCloseBinding, AutoCloseInfo, TypedExpr, TypedExprKind, TypedFnDecl};
use crate::types::Type;

/// A live resource binding: (name, type_name).
type LiveBinding = (String, String);

fn concrete_type_name(ty: &Type) -> Option<&str> {
    match ty {
        Type::Named(name, _) => Some(name.as_str()),
        Type::Int => Some("Int"),
        Type::Float => Some("Float"),
        Type::Bool => Some("Bool"),
        Type::String => Some("String"),
        _ => None,
    }
}

/// Check if a type is ~T where T implements Resource.
fn is_owned_resource(ty: &Type, registry: &TraitRegistry) -> Option<String> {
    if let Type::Own(inner) = ty {
        if let Some(name) = concrete_type_name(inner) {
            if registry.find_instance("Resource", inner).is_some() {
                return Some(name.to_string());
            }
        }
    }
    None
}

struct AutoCloseAnalyzer<'a> {
    registry: &'a TraitRegistry,
    info: AutoCloseInfo,
}

impl<'a> AutoCloseAnalyzer<'a> {
    fn new(registry: &'a TraitRegistry) -> Self {
        Self {
            registry,
            info: AutoCloseInfo::default(),
        }
    }

    fn analyze_function(&mut self, decl: &TypedFnDecl, fn_param_types: &[Type], close_self_type: Option<&str>) {
        let mut live: Vec<LiveBinding> = Vec::new();

        // Check function params for ~Resource bindings
        for (i, param_name) in decl.params.iter().enumerate() {
            if let Some(param_ty) = fn_param_types.get(i) {
                if let Some(type_name) = is_owned_resource(param_ty, self.registry) {
                    // Skip the "self" parameter of a Resource close impl to avoid
                    // infinite recursion (close calling itself on its own param).
                    // Other ~Resource params/locals are still auto-closed.
                    if close_self_type == Some(type_name.as_str()) {
                        continue;
                    }
                    live.push((param_name.clone(), type_name));
                }
            }
        }

        self.walk_expr(&decl.body, &mut live);

        // Any remaining live bindings need closing at function exit
        if !live.is_empty() {
            let mut exits: Vec<AutoCloseBinding> = live
                .iter()
                .rev()
                .map(|(name, type_name)| AutoCloseBinding {
                    name: name.clone(),
                    type_name: type_name.clone(),
                })
                .collect();
            // Deduplicate: only keep the last binding per name (the live one)
            let mut seen = std::collections::HashSet::new();
            exits.retain(|b| seen.insert(b.name.clone()));
            self.info.fn_exits.insert(decl.name.clone(), exits);
        }
    }

    fn walk_expr(&mut self, expr: &TypedExpr, live: &mut Vec<LiveBinding>) {
        match &expr.kind {
            TypedExprKind::Let { name, value, body } => {
                self.walk_expr(value, live);

                // Shadow check: if name already in live, close the old one
                if let Some(pos) = live.iter().position(|(n, _)| n == name) {
                    let (old_name, old_type_name) = live.remove(pos);
                    self.info.shadow_closes.insert(
                        expr.span,
                        AutoCloseBinding {
                            name: old_name,
                            type_name: old_type_name,
                        },
                    );
                }

                // Check if this let introduces a ~Resource binding
                if let Some(type_name) = is_owned_resource(&value.ty, self.registry) {
                    live.push((name.clone(), type_name));
                }

                if let Some(body) = body {
                    self.walk_expr(body, live);
                }
            }

            TypedExprKind::App { func, args } => {
                self.walk_expr(func, live);
                for arg in args {
                    self.walk_expr(arg, live);
                }
                // Consumption detection: if arg is a Var in live and param is ~T, mark consumed
                for arg in args {
                    if let TypedExprKind::Var(var_name) = &arg.kind {
                        if let Type::Own(_) = &arg.ty {
                            if let Some(pos) = live.iter().position(|(n, _)| n == var_name) {
                                live.remove(pos);
                            }
                        }
                    }
                }
            }

            TypedExprKind::QuestionMark { expr: inner, .. } => {
                self.walk_expr(inner, live);
                // Record snapshot of live bindings for early return
                if !live.is_empty() {
                    let bindings: Vec<AutoCloseBinding> = live
                        .iter()
                        .rev()
                        .map(|(name, type_name)| AutoCloseBinding {
                            name: name.clone(),
                            type_name: type_name.clone(),
                        })
                        .collect();
                    self.info.early_returns.insert(expr.span, bindings);
                }
            }

            TypedExprKind::If { cond, then_, else_ } => {
                self.walk_expr(cond, live);
                let mut then_live = live.clone();
                let mut else_live = live.clone();
                self.walk_expr(then_, &mut then_live);
                self.walk_expr(else_, &mut else_live);
                // Merge: keep only bindings present in both branches
                live.retain(|binding| {
                    then_live.iter().any(|(n, _)| n == &binding.0)
                        && else_live.iter().any(|(n, _)| n == &binding.0)
                });
            }

            TypedExprKind::Match { scrutinee, arms } => {
                self.walk_expr(scrutinee, live);
                if arms.is_empty() {
                    return;
                }
                let mut branch_lives: Vec<Vec<LiveBinding>> = Vec::new();
                for arm in arms {
                    let mut arm_live = live.clone();
                    self.walk_expr(&arm.body, &mut arm_live);
                    branch_lives.push(arm_live);
                }
                // Merge: keep only bindings present in ALL branches
                live.retain(|binding| {
                    branch_lives
                        .iter()
                        .all(|bl| bl.iter().any(|(n, _)| n == &binding.0))
                });
            }

            TypedExprKind::Lambda { body, .. } => {
                // Lambda captures don't consume resources for auto-close purposes;
                // the lambda body has its own scope
                let mut lambda_live = Vec::new();
                self.walk_expr(body, &mut lambda_live);
            }

            TypedExprKind::Do(exprs) => {
                for expr in exprs {
                    self.walk_expr(expr, live);
                }
            }

            TypedExprKind::Var(name) => {
                // A bare variable reference doesn't consume — only consumption
                // through function calls (handled in App) matters
                let _ = name;
            }

            TypedExprKind::BinaryOp { lhs, rhs, .. } => {
                self.walk_expr(lhs, live);
                self.walk_expr(rhs, live);
            }

            TypedExprKind::UnaryOp { operand, .. } => {
                self.walk_expr(operand, live);
            }

            TypedExprKind::FieldAccess { expr, .. } => {
                self.walk_expr(expr, live);
            }

            TypedExprKind::StructLit { fields, .. } => {
                for (_, e) in fields {
                    self.walk_expr(e, live);
                }
            }

            TypedExprKind::StructUpdate { base, fields } => {
                self.walk_expr(base, live);
                for (_, e) in fields {
                    self.walk_expr(e, live);
                }
            }

            TypedExprKind::LetPattern { value, body, .. } => {
                self.walk_expr(value, live);
                if let Some(body) = body {
                    self.walk_expr(body, live);
                }
            }

            TypedExprKind::Recur(args) | TypedExprKind::Tuple(args) | TypedExprKind::VecLit(args) => {
                for arg in args {
                    self.walk_expr(arg, live);
                }
            }

            TypedExprKind::Lit(_) => {}
        }
    }
}

/// If this function is a Resource close impl (e.g., `Resource$Handle$close`),
/// return the target type name (e.g., `"Handle"`). This parameter must not be
/// auto-closed to avoid infinite recursion.
fn resource_close_self_type(fn_name: &str) -> Option<&str> {
    let rest = fn_name.strip_prefix("Resource$")?;
    let type_name = rest.strip_suffix("$close")?;
    if type_name.is_empty() { None } else { Some(type_name) }
}

/// Compute auto-close information for all functions in the module.
pub fn compute_auto_close(
    functions: &[TypedFnDecl],
    fn_types: &[(String, crate::types::TypeScheme)],
    registry: &TraitRegistry,
) -> AutoCloseInfo {
    if registry.lookup_trait("Resource").is_none() {
        return AutoCloseInfo::default();
    }

    let mut analyzer = AutoCloseAnalyzer::new(registry);

    for decl in functions {
        let close_self_type = resource_close_self_type(&decl.name);

        let param_types = fn_types
            .iter()
            .find(|(name, _)| name == &decl.name)
            .and_then(|(_, scheme)| {
                if let Type::Fn(params, _) = &scheme.ty {
                    Some(params.clone())
                } else {
                    None
                }
            })
            .unwrap_or_default();
        analyzer.analyze_function(decl, &param_types, close_self_type);
    }

    analyzer.info
}
