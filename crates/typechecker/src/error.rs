// Type checking errors with ariadne integration
// Error codes from spec/types.md

use crate::types::InferType;
use alang_parser::ast::Span;
use ariadne::{Color, Label, Report, ReportKind, Source};

/// Type checking error with error code and source location
#[derive(Debug, Clone)]
pub struct TypeError {
    pub code: ErrorCode,
    pub message: String,
    pub primary_span: Span,
    pub labels: Vec<(Span, String)>,
    pub notes: Vec<String>,
}

/// Error codes from spec/types.md
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorCode {
    // Basic type errors (E0001-E0008)
    TypeMismatch,       // E0001
    UnknownType,        // E0002
    UnknownVariable,    // E0003
    NotAFunction,       // E0004
    WrongArity,         // E0005
    NonExhaustiveMatch, // E0006
    RedundantPattern,   // E0007
    InfiniteType,       // E0008

    // Affine type errors (E0101-E0104)
    MovedValueUsed,   // E0101
    MovedValueNotUsed, // E0102
    MoveInOneBranch,  // E0103
    CaptureOfMoved,   // E0104

    // Additional errors
    DuplicateField,
    UnknownField,
    DuplicateVariant,
    NotAStruct,
    NotASumType,
    UnknownVariant,
}

impl ErrorCode {
    pub fn as_str(&self) -> &'static str {
        match self {
            ErrorCode::TypeMismatch => "E0001",
            ErrorCode::UnknownType => "E0002",
            ErrorCode::UnknownVariable => "E0003",
            ErrorCode::NotAFunction => "E0004",
            ErrorCode::WrongArity => "E0005",
            ErrorCode::NonExhaustiveMatch => "E0006",
            ErrorCode::RedundantPattern => "E0007",
            ErrorCode::InfiniteType => "E0008",
            ErrorCode::MovedValueUsed => "E0101",
            ErrorCode::MovedValueNotUsed => "E0102",
            ErrorCode::MoveInOneBranch => "E0103",
            ErrorCode::CaptureOfMoved => "E0104",
            ErrorCode::DuplicateField => "E1001",
            ErrorCode::UnknownField => "E1002",
            ErrorCode::DuplicateVariant => "E1003",
            ErrorCode::NotAStruct => "E1004",
            ErrorCode::NotASumType => "E1005",
            ErrorCode::UnknownVariant => "E1006",
        }
    }
}

impl TypeError {
    /// Type mismatch error: expected one type, found another
    pub fn type_mismatch(expected: &InferType, found: &InferType, span: Span) -> Self {
        TypeError {
            code: ErrorCode::TypeMismatch,
            message: "type mismatch".to_string(),
            primary_span: span.clone(),
            labels: vec![(
                span,
                format!("expected {}, found {}", expected, found),
            )],
            notes: vec![
                format!("expected type: {}", expected),
                format!("   found type: {}", found),
            ],
        }
    }

    /// Unknown variable error
    pub fn unknown_variable(name: &str, span: Span) -> Self {
        TypeError {
            code: ErrorCode::UnknownVariable,
            message: format!("unknown variable `{}`", name),
            primary_span: span.clone(),
            labels: vec![(span, "not found in this scope".to_string())],
            notes: vec![],
        }
    }

    /// Unknown type error
    pub fn unknown_type(name: &str, span: Span) -> Self {
        TypeError {
            code: ErrorCode::UnknownType,
            message: format!("unknown type `{}`", name),
            primary_span: span.clone(),
            labels: vec![(span, "type not defined".to_string())],
            notes: vec![],
        }
    }

    /// Infinite type error (occurs check failure)
    pub fn infinite_type(ty: &InferType, span: Span) -> Self {
        TypeError {
            code: ErrorCode::InfiniteType,
            message: "infinite type detected".to_string(),
            primary_span: span.clone(),
            labels: vec![(
                span,
                format!("type variable occurs in {}", ty),
            )],
            notes: vec!["This would create an infinitely large type".to_string()],
        }
    }

    /// Not a function error
    pub fn not_a_function(ty: &InferType, span: Span) -> Self {
        TypeError {
            code: ErrorCode::NotAFunction,
            message: "expected function".to_string(),
            primary_span: span.clone(),
            labels: vec![(span, format!("this has type {}, not a function", ty))],
            notes: vec![],
        }
    }

    /// Wrong number of arguments error
    pub fn wrong_arity(expected: usize, found: usize, span: Span) -> Self {
        TypeError {
            code: ErrorCode::WrongArity,
            message: "wrong number of arguments".to_string(),
            primary_span: span.clone(),
            labels: vec![(
                span,
                format!("expected {} arguments, found {}", expected, found),
            )],
            notes: vec![],
        }
    }

    /// Unknown field error
    pub fn unknown_field(field: &str, span: Span) -> Self {
        TypeError {
            code: ErrorCode::UnknownField,
            message: format!("unknown field `{}`", field),
            primary_span: span.clone(),
            labels: vec![(span, "field not defined in struct".to_string())],
            notes: vec![],
        }
    }

    /// Not a struct error
    pub fn not_a_struct(name: &str, span: Span) -> Self {
        TypeError {
            code: ErrorCode::NotAStruct,
            message: format!("`{}` is not a struct type", name),
            primary_span: span.clone(),
            labels: vec![(span, "expected struct type".to_string())],
            notes: vec![],
        }
    }

    /// Not a sum type error
    pub fn not_a_sum_type(name: &str, span: Span) -> Self {
        TypeError {
            code: ErrorCode::NotASumType,
            message: format!("`{}` is not a sum type", name),
            primary_span: span.clone(),
            labels: vec![(span, "expected sum type".to_string())],
            notes: vec![],
        }
    }

    /// Unknown variant error
    pub fn unknown_variant(variant: &str, span: Span) -> Self {
        TypeError {
            code: ErrorCode::UnknownVariant,
            message: format!("unknown variant `{}`", variant),
            primary_span: span.clone(),
            labels: vec![(span, "variant not defined in sum type".to_string())],
            notes: vec![],
        }
    }

    /// Moved value used error
    pub fn moved_value_used(name: &str, span: Span) -> Self {
        TypeError {
            code: ErrorCode::MovedValueUsed,
            message: format!("use of moved value `{}`", name),
            primary_span: span.clone(),
            labels: vec![(span, "value used after move".to_string())],
            notes: vec![
                "^move values can only be used once".to_string(),
            ],
        }
    }

    /// Non-exhaustive match error
    pub fn non_exhaustive_match(missing: Vec<String>, span: Span) -> Self {
        TypeError {
            code: ErrorCode::NonExhaustiveMatch,
            message: "non-exhaustive patterns".to_string(),
            primary_span: span.clone(),
            labels: vec![(span, "missing cases".to_string())],
            notes: vec![format!("missing patterns: {}", missing.join(", "))],
        }
    }
}

/// Convert TypeError to ariadne Report and write to output
pub fn report_error(error: &TypeError, filename: &str, source: &str) -> String {
    let mut output = Vec::new();

    let mut report = Report::build(
        ReportKind::Error,
        (filename, error.primary_span.start..error.primary_span.end),
    )
    .with_message(format!("error[{}]: {}", error.code.as_str(), error.message));

    for (span, message) in &error.labels {
        report = report.with_label(
            Label::new((filename, span.start..span.end))
                .with_message(message)
                .with_color(Color::Red),
        );
    }

    for note in &error.notes {
        report = report.with_note(note);
    }

    report
        .finish()
        .write((filename, Source::from(source)), &mut output)
        .unwrap();

    String::from_utf8(output).unwrap()
}

/// Report multiple errors
pub fn report_errors(errors: &[TypeError], filename: &str, source: &str) -> String {
    errors
        .iter()
        .map(|e| report_error(e, filename, source))
        .collect::<Vec<_>>()
        .join("\n")
}
