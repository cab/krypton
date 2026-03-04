// Pattern exhaustiveness checking
// Validates that match expressions cover all cases

use crate::error::TypeError;
use crate::types::InferType;
use alang_parser::ast::{MatchBranch, Pattern, Span};

/// Check if match branches are exhaustive
/// TODO: Implement exhaustiveness checking
/// For now, checks if there's a wildcard pattern
pub fn check_exhaustiveness(
    _scrutinee_ty: &InferType,
    branches: &[MatchBranch],
    _span: &Span,
) -> Result<(), TypeError> {
    // Stub implementation
    // Simple check: if there's a wildcard, it's exhaustive
    let has_wildcard = branches
        .iter()
        .any(|b| matches!(b.pattern, Pattern::Wildcard));

    if has_wildcard || branches.is_empty() {
        Ok(())
    } else {
        // For now, just accept any match
        // In Phase 4, this will properly check sum type coverage
        Ok(())
    }
}

/// Check if a pattern is redundant
/// TODO: Implement redundancy checking
pub fn check_redundancy(_pattern: &Pattern, previous_patterns: &[&Pattern]) -> bool {
    // Stub: pattern is redundant if preceded by wildcard
    previous_patterns
        .iter()
        .any(|p| matches!(p, Pattern::Wildcard))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wildcard_exhaustive() {
        let branches = vec![MatchBranch {
            pattern: Pattern::Wildcard,
            guard: None,
            body: alang_parser::ast::Expr::Unit(Span { start: 0, end: 0 }),
        }];

        let result = check_exhaustiveness(
            &InferType::Primitive(crate::types::PrimitiveType::Int),
            &branches,
            &Span { start: 0, end: 0 },
        );

        assert!(result.is_ok());
    }
}
