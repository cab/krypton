// Built-in types and operations
// Provides primitive types and standard library types

use crate::types::PrimitiveType;

/// Get the name of a primitive type
pub fn primitive_type_name(prim: PrimitiveType) -> &'static str {
    match prim {
        PrimitiveType::Int => "Int",
        PrimitiveType::Float => "Float",
        PrimitiveType::String => "String",
        PrimitiveType::Bool => "Bool",
        PrimitiveType::Unit => "Unit",
        PrimitiveType::Never => "Never",
    }
}

/// Check if a name refers to a primitive type
pub fn is_primitive_type(name: &str) -> Option<PrimitiveType> {
    match name {
        "Int" => Some(PrimitiveType::Int),
        "Float" => Some(PrimitiveType::Float),
        "String" => Some(PrimitiveType::String),
        "Bool" => Some(PrimitiveType::Bool),
        "Unit" => Some(PrimitiveType::Unit),
        "Never" => Some(PrimitiveType::Never),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_names() {
        assert_eq!(primitive_type_name(PrimitiveType::Int), "Int");
        assert_eq!(primitive_type_name(PrimitiveType::String), "String");
    }

    #[test]
    fn test_is_primitive() {
        assert_eq!(is_primitive_type("Int"), Some(PrimitiveType::Int));
        assert_eq!(is_primitive_type("Foo"), None);
    }
}
