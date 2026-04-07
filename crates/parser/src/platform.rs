use crate::ast::*;

/// Returns true if the declaration should be kept for the given target.
fn matches_target(platform: &Option<Vec<CompileTarget>>, target: CompileTarget) -> bool {
    match platform {
        None => true,
        Some(targets) => targets.contains(&target),
    }
}

/// Get the platform annotation from a declaration.
fn decl_platform(decl: &Decl) -> &Option<Vec<CompileTarget>> {
    match decl {
        Decl::DefFn(f) => &f.platform,
        Decl::DefType(t) => &t.platform,
        Decl::DefTrait { platform, .. } => platform,
        Decl::DefImpl { platform, .. } => platform,
        Decl::Import { platform, .. } => platform,
        Decl::Extern { platform, .. } => platform,
    }
}

/// Filter declarations in a module by platform target.
///
/// Removes declarations whose `@platform` annotation doesn't include `target`.
/// `extern java` / `extern js` without an explicit `@platform` are implicitly
/// platform-specific: `extern java` ≡ `@platform([jvm])`, `extern js` ≡ `@platform([js])`.
pub fn filter_by_platform(module: &mut Module, target: CompileTarget) {
    module.decls.retain(|decl| {
        let platform = decl_platform(decl);
        if platform.is_some() {
            return matches_target(platform, target);
        }
        // Implicit platform from extern target keyword
        if let Decl::Extern {
            target: extern_target,
            ..
        } = decl
        {
            return matches!(
                (extern_target, target),
                (ExternTarget::Java, CompileTarget::Jvm) | (ExternTarget::Js, CompileTarget::Js)
            );
        }
        true
    });
}
