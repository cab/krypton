use std::collections::HashMap;

use ristretto_classfile::attributes::{Attribute, Instruction};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Field, FieldAccessFlags, FieldType, Method,
    MethodAccessFlags,
};

use super::compiler::{CodegenError, JvmType, VariantField};
use super::{jvm_type_to_base_field_type, jvm_type_to_field_descriptor, JAVA_21};

pub(super) fn generate_struct_class(
    name: &str,
    fields: &[(String, JvmType)],
    class_descriptors: &HashMap<u16, String>,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;

    // Build constructor descriptor
    let mut ctor_desc = String::from("(");
    for (_, jt) in fields {
        let desc = match jt {
            JvmType::StructRef(idx) => class_descriptors[idx].clone(),
            other => jvm_type_to_field_descriptor(*other),
        };
        ctor_desc.push_str(&desc);
    }
    ctor_desc.push_str(")V");
    let init_desc = cp.add_utf8(&ctor_desc)?;

    // Build field refs for putfield/getfield
    let mut field_refs = Vec::new();
    let mut jvm_fields = Vec::new();
    for (fname, jt) in fields {
        let fdesc = match jt {
            JvmType::StructRef(idx) => class_descriptors[idx].clone(),
            other => jvm_type_to_field_descriptor(*other),
        };
        let field_ref = cp.add_field_ref(this_class, fname, &fdesc)?;
        field_refs.push(field_ref);

        let name_idx = cp.add_utf8(fname)?;
        let desc_idx = cp.add_utf8(&fdesc)?;
        let field_type = match jt {
            JvmType::StructRef(_) => {
                // fdesc is "LClassName;" — extract "ClassName"
                FieldType::Object(fdesc[1..fdesc.len() - 1].to_string())
            }
            other => jvm_type_to_base_field_type(*other),
        };
        jvm_fields.push(Field {
            access_flags: FieldAccessFlags::PRIVATE | FieldAccessFlags::FINAL,
            name_index: name_idx,
            descriptor_index: desc_idx,
            field_type,
            attributes: vec![],
        });
    }

    // Constructor code: aload_0, invokespecial Object.<init>, then store each field
    let mut ctor_code = vec![
        Instruction::Aload_0,
        Instruction::Invokespecial(object_init),
    ];

    let mut param_slot: u16 = 1; // slot 0 = this
    for (i, (_, jt)) in fields.iter().enumerate() {
        ctor_code.push(Instruction::Aload_0);
        let load = match jt {
            JvmType::Long => Instruction::Lload(param_slot as u8),
            JvmType::Double => Instruction::Dload(param_slot as u8),
            JvmType::Int => Instruction::Iload(param_slot as u8),
            JvmType::StructRef(_) => Instruction::Aload(param_slot as u8),
        };
        ctor_code.push(load);
        ctor_code.push(Instruction::Putfield(field_refs[i]));
        param_slot += match jt {
            JvmType::Long | JvmType::Double => 2,
            _ => 1,
        };
    }
    ctor_code.push(Instruction::Return);

    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 20,
            max_locals: param_slot,
            code: ctor_code,
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    // Accessor methods
    let mut methods = vec![constructor];
    for (i, (fname, jt)) in fields.iter().enumerate() {
        let ret_desc = match jt {
            JvmType::StructRef(idx) => class_descriptors[idx].clone(),
            other => jvm_type_to_field_descriptor(*other),
        };
        let method_desc = format!("(){ret_desc}");
        let method_name_idx = cp.add_utf8(fname)?;
        let method_desc_idx = cp.add_utf8(&method_desc)?;

        let ret_instr = match jt {
            JvmType::Long => Instruction::Lreturn,
            JvmType::Double => Instruction::Dreturn,
            JvmType::Int => Instruction::Ireturn,
            JvmType::StructRef(_) => Instruction::Areturn,
        };

        methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: method_name_idx,
            descriptor_index: method_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: 4,
                max_locals: 1,
                code: vec![
                    Instruction::Aload_0,
                    Instruction::Getfield(field_refs[i]),
                    ret_instr,
                ],
                exception_table: vec![],
                attributes: vec![],
            }],
        });
    }

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        fields: jvm_fields,
        methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a sealed interface class file for a sum type.
pub(super) fn generate_sealed_interface_class(
    name: &str,
    variant_class_names: &[&str],
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    // Add class refs for each variant (for PermittedSubclasses)
    let mut variant_class_indexes = Vec::new();
    for vname in variant_class_names {
        let idx = cp.add_class(vname)?;
        variant_class_indexes.push(idx);
    }

    let permitted_name = cp.add_utf8("PermittedSubclasses")?;

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC
            | ClassAccessFlags::INTERFACE
            | ClassAccessFlags::ABSTRACT,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        attributes: vec![Attribute::PermittedSubclasses {
            name_index: permitted_name,
            class_indexes: variant_class_indexes,
        }],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a variant class file that implements a sealed interface.
pub(super) fn generate_variant_class(
    variant_name: &str,
    interface_name: &str,
    display_name: &str,
    fields: &[VariantField],
    class_descriptors: &HashMap<u16, String>,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(variant_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(interface_name)?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;

    // Build constructor descriptor — erased fields use Ljava/lang/Object;
    let mut ctor_desc = String::from("(");
    for f in fields {
        if f.is_erased {
            ctor_desc.push_str("Ljava/lang/Object;");
        } else {
            let desc = match f.jvm_type {
                JvmType::StructRef(idx) => class_descriptors
                    .get(&idx)
                    .cloned()
                    .unwrap_or_else(|| jvm_type_to_field_descriptor(f.jvm_type)),
                _ => jvm_type_to_field_descriptor(f.jvm_type),
            };
            ctor_desc.push_str(&desc);
        }
    }
    ctor_desc.push_str(")V");
    let init_desc = cp.add_utf8(&ctor_desc)?;

    // Build fields and field refs
    let mut field_refs = Vec::new();
    let mut jvm_fields = Vec::new();
    for f in fields {
        let fdesc = if f.is_erased {
            "Ljava/lang/Object;".to_string()
        } else {
            match f.jvm_type {
                JvmType::StructRef(idx) => class_descriptors
                    .get(&idx)
                    .cloned()
                    .unwrap_or_else(|| jvm_type_to_field_descriptor(f.jvm_type)),
                _ => jvm_type_to_field_descriptor(f.jvm_type),
            }
        };
        let field_ref = cp.add_field_ref(this_class, &f.name, &fdesc)?;
        field_refs.push(field_ref);

        let name_idx = cp.add_utf8(&f.name)?;
        let desc_idx = cp.add_utf8(&fdesc)?;
        let field_type = if f.is_erased {
            FieldType::Object("java/lang/Object".to_string())
        } else {
            match f.jvm_type {
                JvmType::StructRef(_) => FieldType::Object(fdesc[1..fdesc.len() - 1].to_string()),
                _ => jvm_type_to_base_field_type(f.jvm_type),
            }
        };
        jvm_fields.push(Field {
            access_flags: FieldAccessFlags::PUBLIC | FieldAccessFlags::FINAL,
            name_index: name_idx,
            descriptor_index: desc_idx,
            field_type,
            attributes: vec![],
        });
    }

    // Constructor code
    let mut ctor_code = vec![
        Instruction::Aload_0,
        Instruction::Invokespecial(object_init),
    ];

    let mut param_slot: u16 = 1;
    for (i, f) in fields.iter().enumerate() {
        ctor_code.push(Instruction::Aload_0);
        if f.is_erased {
            ctor_code.push(Instruction::Aload(param_slot as u8));
            param_slot += 1;
        } else {
            let load = match f.jvm_type {
                JvmType::Long => Instruction::Lload(param_slot as u8),
                JvmType::Double => Instruction::Dload(param_slot as u8),
                JvmType::Int => Instruction::Iload(param_slot as u8),
                JvmType::StructRef(_) => Instruction::Aload(param_slot as u8),
            };
            ctor_code.push(load);
            param_slot += match f.jvm_type {
                JvmType::Long | JvmType::Double => 2,
                _ => 1,
            };
        }
        ctor_code.push(Instruction::Putfield(field_refs[i]));
    }
    ctor_code.push(Instruction::Return);

    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 20,
            max_locals: param_slot,
            code: ctor_code,
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let mut methods = vec![constructor];

    // For nullary variants, add INSTANCE singleton field + <clinit>
    let mut singleton_field = None;
    if fields.is_empty() {
        let self_desc = format!("L{variant_name};");
        let instance_name = cp.add_utf8("INSTANCE")?;
        let instance_desc_idx = cp.add_utf8(&self_desc)?;
        let instance_field_ref = cp.add_field_ref(this_class, "INSTANCE", &self_desc)?;
        let self_init = cp.add_method_ref(this_class, "<init>", "()V")?;

        let clinit_name = cp.add_utf8("<clinit>")?;
        let clinit_desc = cp.add_utf8("()V")?;
        let clinit = Method {
            access_flags: MethodAccessFlags::STATIC,
            name_index: clinit_name,
            descriptor_index: clinit_desc,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: 2,
                max_locals: 0,
                code: vec![
                    Instruction::New(this_class),
                    Instruction::Dup,
                    Instruction::Invokespecial(self_init),
                    Instruction::Putstatic(instance_field_ref),
                    Instruction::Return,
                ],
                exception_table: vec![],
                attributes: vec![],
            }],
        };
        methods.push(clinit);

        singleton_field = Some(Field {
            access_flags: FieldAccessFlags::PUBLIC
                | FieldAccessFlags::STATIC
                | FieldAccessFlags::FINAL,
            name_index: instance_name,
            descriptor_index: instance_desc_idx,
            field_type: FieldType::Object(variant_name.to_string()),
            attributes: vec![],
        });
    }

    // toString() method returning the variant name
    let tostring_name = cp.add_utf8("toString")?;
    let tostring_desc = cp.add_utf8("()Ljava/lang/String;")?;
    let variant_str = cp.add_string(display_name)?;
    let ldc = if variant_str <= 255 {
        Instruction::Ldc(variant_str as u8)
    } else {
        Instruction::Ldc_w(variant_str)
    };
    methods.push(Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: tostring_name,
        descriptor_index: tostring_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 1,
            max_locals: 1,
            code: vec![ldc, Instruction::Areturn],
            exception_table: vec![],
            attributes: vec![],
        }],
    });

    if let Some(sf) = singleton_field {
        jvm_fields.push(sf);
    }

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER | ClassAccessFlags::FINAL,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        interfaces: vec![interface_class],
        fields: jvm_fields,
        methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}
