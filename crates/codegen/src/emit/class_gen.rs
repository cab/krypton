use std::collections::HashMap;

use ristretto_classfile::attributes::{Attribute, Instruction};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Field, FieldAccessFlags, FieldType, Method,
    MethodAccessFlags,
};

use super::{JAVA_21, jvm_type_to_field_descriptor, jvm_type_to_base_field_type};
use super::compiler::{JvmType, CodegenError};

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
                FieldType::Object(fdesc[1..fdesc.len()-1].to_string())
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
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(param_slot as u8),
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
            JvmType::Ref | JvmType::StructRef(_) => Instruction::Areturn,
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
    fields: &[(String, JvmType, bool)], // (name, jvm_type, is_erased)
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
    for (_, jt, is_erased) in fields {
        if *is_erased {
            ctor_desc.push_str("Ljava/lang/Object;");
        } else {
            ctor_desc.push_str(&jvm_type_to_field_descriptor(*jt));
        }
    }
    ctor_desc.push_str(")V");
    let init_desc = cp.add_utf8(&ctor_desc)?;

    // Build fields and field refs
    let mut field_refs = Vec::new();
    let mut jvm_fields = Vec::new();
    for (i, (fname, jt, is_erased)) in fields.iter().enumerate() {
        let fdesc = if *is_erased {
            "Ljava/lang/Object;".to_string()
        } else {
            jvm_type_to_field_descriptor(*jt)
        };
        let field_ref = cp.add_field_ref(this_class, fname, &fdesc)?;
        field_refs.push(field_ref);

        let name_idx = cp.add_utf8(fname)?;
        let desc_idx = cp.add_utf8(&fdesc)?;
        let field_type = if *is_erased {
            FieldType::Object("java/lang/Object".to_string())
        } else {
            jvm_type_to_base_field_type(*jt)
        };
        jvm_fields.push(Field {
            access_flags: FieldAccessFlags::PUBLIC | FieldAccessFlags::FINAL,
            name_index: name_idx,
            descriptor_index: desc_idx,
            field_type,
            attributes: vec![],
        });
        let _ = i; // suppress unused
    }

    // Constructor code
    let mut ctor_code = vec![
        Instruction::Aload_0,
        Instruction::Invokespecial(object_init),
    ];

    let mut param_slot: u16 = 1;
    for (i, (_, jt, is_erased)) in fields.iter().enumerate() {
        ctor_code.push(Instruction::Aload_0);
        if *is_erased {
            ctor_code.push(Instruction::Aload(param_slot as u8));
            param_slot += 1;
        } else {
            let load = match jt {
                JvmType::Long => Instruction::Lload(param_slot as u8),
                JvmType::Double => Instruction::Dload(param_slot as u8),
                JvmType::Int => Instruction::Iload(param_slot as u8),
                JvmType::Ref | JvmType::StructRef(_) => Instruction::Aload(param_slot as u8),
            };
            ctor_code.push(load);
            param_slot += match jt {
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

/// Check if a type expression references any of the given type parameters (directly or in App args).

pub(super) fn generate_fun_interface(arity: u8) -> Result<Vec<u8>, CodegenError> {
    let class_name = format!("Fun{arity}");
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(&class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    // Build apply method descriptor: (Object, ..., Object)Object
    let mut apply_desc = String::from("(");
    for _ in 0..arity {
        apply_desc.push_str("Ljava/lang/Object;");
    }
    apply_desc.push_str(")Ljava/lang/Object;");

    let apply_name = cp.add_utf8("apply")?;
    let apply_desc_idx = cp.add_utf8(&apply_desc)?;

    let apply_method = Method {
        access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::ABSTRACT,
        name_index: apply_name,
        descriptor_index: apply_desc_idx,
        attributes: vec![],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC
            | ClassAccessFlags::INTERFACE
            | ClassAccessFlags::ABSTRACT,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        methods: vec![apply_method],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a trait interface class file (e.g., `Eq.class`).
/// All methods take and return Object (type erasure).
pub(super) fn generate_trait_interface_class(
    name: &str,
    methods: &[(String, usize)], // (method_name, param_count)
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(name)?;
    let object_class = cp.add_class("java/lang/Object")?;

    let mut jvm_methods = Vec::new();
    for (method_name, param_count) in methods {
        let mut desc = String::from("(");
        for _ in 0..*param_count {
            desc.push_str("Ljava/lang/Object;");
        }
        desc.push_str(")Ljava/lang/Object;");

        let name_idx = cp.add_utf8(method_name)?;
        let desc_idx = cp.add_utf8(&desc)?;

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::ABSTRACT,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![],
        });
    }

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC
            | ClassAccessFlags::INTERFACE
            | ClassAccessFlags::ABSTRACT,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        methods: jvm_methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate an instance singleton class (e.g., `Eq$Point.class`).
/// Implements the trait interface, delegates to static methods on the main class.
pub(super) fn generate_instance_class(
    class_name: &str,
    trait_interface_name: &str,
    main_class_name: &str,
    methods: &[(String, String, usize, String)], // (iface_method_name, static_method_name, param_count, static_descriptor)
    param_jvm_types: &HashMap<String, Vec<JvmType>>,
    return_jvm_types: &HashMap<String, JvmType>,
    param_class_names: &HashMap<String, Vec<Option<String>>>, // method_name → per-param class names for checkcast
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(trait_interface_name)?;
    let main_class = cp.add_class(main_class_name)?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8("()V")?;

    // INSTANCE field
    let self_desc = format!("L{class_name};");
    let instance_name = cp.add_utf8("INSTANCE")?;
    let instance_desc = cp.add_utf8(&self_desc)?;
    let instance_field_ref = cp.add_field_ref(this_class, "INSTANCE", &self_desc)?;
    let self_init = cp.add_method_ref(this_class, "<init>", "()V")?;

    // Boxing/unboxing refs
    let long_box_class = cp.add_class("java/lang/Long")?;
    let long_valueof = cp.add_method_ref(long_box_class, "valueOf", "(J)Ljava/lang/Long;")?;
    let long_unbox = cp.add_method_ref(long_box_class, "longValue", "()J")?;
    let double_box_class = cp.add_class("java/lang/Double")?;
    let double_valueof = cp.add_method_ref(double_box_class, "valueOf", "(D)Ljava/lang/Double;")?;
    let _double_unbox = cp.add_method_ref(double_box_class, "doubleValue", "()D")?;
    let bool_box_class = cp.add_class("java/lang/Boolean")?;
    let bool_valueof = cp.add_method_ref(bool_box_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
    let _bool_unbox = cp.add_method_ref(bool_box_class, "booleanValue", "()Z")?;

    // Constructor
    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 2,
            max_locals: 1,
            code: vec![
                Instruction::Aload_0,
                Instruction::Invokespecial(object_init),
                Instruction::Return,
            ],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    // <clinit> — static initializer
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

    let mut jvm_methods = vec![constructor, clinit];

    // Bridge methods: implement interface methods delegating to static impls
    for (iface_method_name, static_method_name, param_count, static_desc) in methods {
        // Interface method descriptor: all Object
        let mut iface_desc = String::from("(");
        for _ in 0..*param_count {
            iface_desc.push_str("Ljava/lang/Object;");
        }
        iface_desc.push_str(")Ljava/lang/Object;");

        let concrete_params = param_jvm_types.get(iface_method_name)
            .cloned()
            .unwrap_or_default();
        let concrete_ret = return_jvm_types.get(iface_method_name)
            .copied()
            .unwrap_or(JvmType::Int);

        let static_ref = cp.add_method_ref(main_class, static_method_name, static_desc)?;

        let method_name_idx = cp.add_utf8(iface_method_name)?;
        let method_desc_idx = cp.add_utf8(&iface_desc)?;

        // Build bridge code: unbox params → invokestatic → box result
        let mut bridge_code: Vec<Instruction> = Vec::new();
        let mut slot: u8 = 1; // slot 0 = this

        let class_names_for_method = param_class_names.get(iface_method_name)
            .cloned()
            .unwrap_or_default();

        for (param_idx, pt) in concrete_params.iter().enumerate() {
            bridge_code.push(Instruction::Aload(slot));
            match pt {
                JvmType::Long => {
                    bridge_code.push(Instruction::Checkcast(long_box_class));
                    bridge_code.push(Instruction::Invokevirtual(long_unbox));
                }
                JvmType::Double => {
                    bridge_code.push(Instruction::Checkcast(double_box_class));
                    bridge_code.push(Instruction::Invokevirtual(_double_unbox));
                }
                JvmType::Int => {
                    bridge_code.push(Instruction::Checkcast(bool_box_class));
                    bridge_code.push(Instruction::Invokevirtual(_bool_unbox));
                }
                JvmType::StructRef(_) => {
                    // Checkcast Object → concrete struct type if we know the class name
                    if let Some(Some(cn)) = class_names_for_method.get(param_idx) {
                        let cast_class = cp.add_class(cn)?;
                        bridge_code.push(Instruction::Checkcast(cast_class));
                    }
                }
                _ => {}
            }
            slot += 1;
        }

        bridge_code.push(Instruction::Invokestatic(static_ref));

        // Box the result back to Object
        match concrete_ret {
            JvmType::Long => {
                bridge_code.push(Instruction::Invokestatic(long_valueof));
            }
            JvmType::Double => {
                bridge_code.push(Instruction::Invokestatic(double_valueof));
            }
            JvmType::Int => {
                bridge_code.push(Instruction::Invokestatic(bool_valueof));
            }
            _ => {}
        }
        bridge_code.push(Instruction::Areturn);

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: method_name_idx,
            descriptor_index: method_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: 20,
                max_locals: (1 + *param_count) as u16,
                code: bridge_code,
                exception_table: vec![],
                attributes: vec![],
            }],
        });
    }

    // INSTANCE field declaration
    let field = Field {
        access_flags: FieldAccessFlags::PUBLIC | FieldAccessFlags::STATIC | FieldAccessFlags::FINAL,
        name_index: instance_name,
        descriptor_index: instance_desc,
        field_type: FieldType::Object(class_name.to_string()),
        attributes: vec![],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER | ClassAccessFlags::FINAL,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        interfaces: vec![interface_class],
        fields: vec![field],
        methods: jvm_methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a built-in Show instance class for a primitive type.
pub(super) fn generate_builtin_show_instance_class(
    class_name: &str,
    type_name: &str,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class("Show")?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8("()V")?;

    let self_desc = format!("L{class_name};");
    let instance_name = cp.add_utf8("INSTANCE")?;
    let instance_desc = cp.add_utf8(&self_desc)?;
    let instance_field_ref = cp.add_field_ref(this_class, "INSTANCE", &self_desc)?;
    let self_init = cp.add_method_ref(this_class, "<init>", "()V")?;

    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 2,
            max_locals: 1,
            code: vec![
                Instruction::Aload_0,
                Instruction::Invokespecial(object_init),
                Instruction::Return,
            ],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

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

    let iface_desc = "(Ljava/lang/Object;)Ljava/lang/Object;";
    let show_name = cp.add_utf8("show")?;
    let show_desc_idx = cp.add_utf8(iface_desc)?;
    let string_class = cp.add_class("java/lang/String")?;

    let mut bridge_code = Vec::new();
    match type_name {
        "Int" => {
            let long_class = cp.add_class("java/lang/Long")?;
            let long_unbox = cp.add_method_ref(long_class, "longValue", "()J")?;
            let string_valueof = cp.add_method_ref(string_class, "valueOf", "(J)Ljava/lang/String;")?;
            bridge_code.push(Instruction::Aload(1));
            bridge_code.push(Instruction::Checkcast(long_class));
            bridge_code.push(Instruction::Invokevirtual(long_unbox));
            bridge_code.push(Instruction::Invokestatic(string_valueof));
        }
        "Float" => {
            let double_class = cp.add_class("java/lang/Double")?;
            let double_unbox = cp.add_method_ref(double_class, "doubleValue", "()D")?;
            let string_valueof = cp.add_method_ref(string_class, "valueOf", "(D)Ljava/lang/String;")?;
            bridge_code.push(Instruction::Aload(1));
            bridge_code.push(Instruction::Checkcast(double_class));
            bridge_code.push(Instruction::Invokevirtual(double_unbox));
            bridge_code.push(Instruction::Invokestatic(string_valueof));
        }
        "Bool" => {
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_unbox = cp.add_method_ref(bool_class, "booleanValue", "()Z")?;
            let string_valueof = cp.add_method_ref(string_class, "valueOf", "(Z)Ljava/lang/String;")?;
            bridge_code.push(Instruction::Aload(1));
            bridge_code.push(Instruction::Checkcast(bool_class));
            bridge_code.push(Instruction::Invokevirtual(bool_unbox));
            bridge_code.push(Instruction::Invokestatic(string_valueof));
        }
        "String" => {
            bridge_code.push(Instruction::Aload(1));
            bridge_code.push(Instruction::Checkcast(string_class));
        }
        _ => {}
    }
    bridge_code.push(Instruction::Areturn);

    let show_method = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: show_name,
        descriptor_index: show_desc_idx,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 4,
            max_locals: 2,
            code: bridge_code,
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let field = Field {
        access_flags: FieldAccessFlags::PUBLIC | FieldAccessFlags::STATIC | FieldAccessFlags::FINAL,
        name_index: instance_name,
        descriptor_index: instance_desc,
        field_type: FieldType::Object(class_name.to_string()),
        attributes: vec![],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER | ClassAccessFlags::FINAL,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        interfaces: vec![interface_class],
        fields: vec![field],
        methods: vec![constructor, clinit, show_method],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a built-in trait instance class (Add$Int, Eq$String, etc.).
///
/// Each class implements its trait interface with a bridge method that
/// unboxes arguments, performs the operation, and boxes the result.
pub(super) fn generate_builtin_trait_instance_class(
    class_name: &str,
    trait_name: &str,
    method_name: &str,
    type_name: &str,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(trait_name)?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8("()V")?;

    let self_desc = format!("L{class_name};");
    let instance_name = cp.add_utf8("INSTANCE")?;
    let instance_desc = cp.add_utf8(&self_desc)?;
    let instance_field_ref = cp.add_field_ref(this_class, "INSTANCE", &self_desc)?;
    let self_init = cp.add_method_ref(this_class, "<init>", "()V")?;

    // Constructor
    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 2,
            max_locals: 1,
            code: vec![
                Instruction::Aload_0,
                Instruction::Invokespecial(object_init),
                Instruction::Return,
            ],
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    // Static initializer
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

    // Determine if unary (Neg) or binary
    let is_unary = trait_name == "Neg";
    let iface_desc = if is_unary {
        "(Ljava/lang/Object;)Ljava/lang/Object;"
    } else {
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"
    };

    let method_name_idx = cp.add_utf8(method_name)?;
    let method_desc_idx = cp.add_utf8(iface_desc)?;

    // Build bridge method bytecode
    let (bridge_code, max_stack, max_locals) = build_bridge_bytecode(
        &mut cp, trait_name, type_name, is_unary,
    )?;

    let bridge_method = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: method_name_idx,
        descriptor_index: method_desc_idx,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack,
            max_locals,
            code: bridge_code,
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let field = Field {
        access_flags: FieldAccessFlags::PUBLIC | FieldAccessFlags::STATIC | FieldAccessFlags::FINAL,
        name_index: instance_name,
        descriptor_index: instance_desc,
        field_type: FieldType::Object(class_name.to_string()),
        attributes: vec![],
    };

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER | ClassAccessFlags::FINAL,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        interfaces: vec![interface_class],
        fields: vec![field],
        methods: vec![constructor, clinit, bridge_method],
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Build the bridge method bytecode for a built-in trait instance.
fn build_bridge_bytecode(
    cp: &mut ConstantPool,
    trait_name: &str,
    type_name: &str,
    _is_unary: bool,
) -> Result<(Vec<Instruction>, u16, u16), CodegenError> {
    let mut code = Vec::new();

    match (trait_name, type_name) {
        // Binary arithmetic: Int (Long)
        ("Add", "Int") | ("Sub", "Int") | ("Mul", "Int") | ("Div", "Int") => {
            let long_class = cp.add_class("java/lang/Long")?;
            let long_unbox = cp.add_method_ref(long_class, "longValue", "()J")?;
            let long_box = cp.add_method_ref(long_class, "valueOf", "(J)Ljava/lang/Long;")?;
            // Unbox first arg
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(long_class));
            code.push(Instruction::Invokevirtual(long_unbox));
            // Unbox second arg
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(long_class));
            code.push(Instruction::Invokevirtual(long_unbox));
            // Operation
            let op = match trait_name {
                "Add" => Instruction::Ladd,
                "Sub" => Instruction::Lsub,
                "Mul" => Instruction::Lmul,
                "Div" => Instruction::Ldiv,
                _ => unreachable!(),
            };
            code.push(op);
            // Box result
            code.push(Instruction::Invokestatic(long_box));
            code.push(Instruction::Areturn);
            Ok((code, 4, 3))
        }

        // Binary arithmetic: Float (Double)
        ("Add", "Float") | ("Sub", "Float") | ("Mul", "Float") | ("Div", "Float") => {
            let double_class = cp.add_class("java/lang/Double")?;
            let double_unbox = cp.add_method_ref(double_class, "doubleValue", "()D")?;
            let double_box = cp.add_method_ref(double_class, "valueOf", "(D)Ljava/lang/Double;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(double_class));
            code.push(Instruction::Invokevirtual(double_unbox));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(double_class));
            code.push(Instruction::Invokevirtual(double_unbox));
            let op = match trait_name {
                "Add" => Instruction::Dadd,
                "Sub" => Instruction::Dsub,
                "Mul" => Instruction::Dmul,
                "Div" => Instruction::Ddiv,
                _ => unreachable!(),
            };
            code.push(op);
            code.push(Instruction::Invokestatic(double_box));
            code.push(Instruction::Areturn);
            Ok((code, 4, 3))
        }

        // Unary Neg: Int
        ("Neg", "Int") => {
            let long_class = cp.add_class("java/lang/Long")?;
            let long_unbox = cp.add_method_ref(long_class, "longValue", "()J")?;
            let long_box = cp.add_method_ref(long_class, "valueOf", "(J)Ljava/lang/Long;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(long_class));
            code.push(Instruction::Invokevirtual(long_unbox));
            code.push(Instruction::Lneg);
            code.push(Instruction::Invokestatic(long_box));
            code.push(Instruction::Areturn);
            Ok((code, 2, 2))
        }

        // Unary Neg: Float
        ("Neg", "Float") => {
            let double_class = cp.add_class("java/lang/Double")?;
            let double_unbox = cp.add_method_ref(double_class, "doubleValue", "()D")?;
            let double_box = cp.add_method_ref(double_class, "valueOf", "(D)Ljava/lang/Double;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(double_class));
            code.push(Instruction::Invokevirtual(double_unbox));
            code.push(Instruction::Dneg);
            code.push(Instruction::Invokestatic(double_box));
            code.push(Instruction::Areturn);
            Ok((code, 2, 2))
        }

        // Eq: Int — Lcmp + branch
        ("Eq", "Int") => {
            let long_class = cp.add_class("java/lang/Long")?;
            let long_unbox = cp.add_method_ref(long_class, "longValue", "()J")?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(long_class));
            code.push(Instruction::Invokevirtual(long_unbox));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(long_class));
            code.push(Instruction::Invokevirtual(long_unbox));
            code.push(Instruction::Lcmp);
            // Ifne: branch if TOS != 0 (not equal) → false path
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifne(branch_idx + 3)); // if not equal → false
            code.push(Instruction::Iconst_1);              // true
            code.push(Instruction::Goto(branch_idx + 4));  // skip false
            code.push(Instruction::Iconst_0);              // false
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((code, 4, 3))
        }

        // Eq: Float — Dcmpl + branch
        ("Eq", "Float") => {
            let double_class = cp.add_class("java/lang/Double")?;
            let double_unbox = cp.add_method_ref(double_class, "doubleValue", "()D")?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(double_class));
            code.push(Instruction::Invokevirtual(double_unbox));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(double_class));
            code.push(Instruction::Invokevirtual(double_unbox));
            code.push(Instruction::Dcmpl);
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifne(branch_idx + 3));
            code.push(Instruction::Iconst_1);
            code.push(Instruction::Goto(branch_idx + 4));
            code.push(Instruction::Iconst_0);
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((code, 4, 3))
        }

        // Eq: String — String.equals
        ("Eq", "String") => {
            let string_class = cp.add_class("java/lang/String")?;
            let string_equals = cp.add_method_ref(string_class, "equals", "(Ljava/lang/Object;)Z")?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Invokevirtual(string_equals));
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((code, 2, 3))
        }

        // Eq: Bool — unbox + compare
        ("Eq", "Bool") => {
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_unbox = cp.add_method_ref(bool_class, "booleanValue", "()Z")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(bool_class));
            code.push(Instruction::Invokevirtual(bool_unbox));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(bool_class));
            code.push(Instruction::Invokevirtual(bool_unbox));
            // Isub: if equal, result is 0; Ifeq branches if 0
            code.push(Instruction::Isub);
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifeq(branch_idx + 3)); // equal → true
            code.push(Instruction::Iconst_0);
            code.push(Instruction::Goto(branch_idx + 4));
            code.push(Instruction::Iconst_1);
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((code, 2, 3))
        }

        // Ord: Int — Lcmp + Iflt
        ("Ord", "Int") => {
            let long_class = cp.add_class("java/lang/Long")?;
            let long_unbox = cp.add_method_ref(long_class, "longValue", "()J")?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(long_class));
            code.push(Instruction::Invokevirtual(long_unbox));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(long_class));
            code.push(Instruction::Invokevirtual(long_unbox));
            code.push(Instruction::Lcmp);
            // Iflt: branch if TOS < 0 (first < second) → true
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifge(branch_idx + 3)); // if >= → false
            code.push(Instruction::Iconst_1);
            code.push(Instruction::Goto(branch_idx + 4));
            code.push(Instruction::Iconst_0);
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((code, 4, 3))
        }

        // Ord: Float — Dcmpl + Iflt
        ("Ord", "Float") => {
            let double_class = cp.add_class("java/lang/Double")?;
            let double_unbox = cp.add_method_ref(double_class, "doubleValue", "()D")?;
            let bool_class = cp.add_class("java/lang/Boolean")?;
            let bool_box = cp.add_method_ref(bool_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(double_class));
            code.push(Instruction::Invokevirtual(double_unbox));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(double_class));
            code.push(Instruction::Invokevirtual(double_unbox));
            code.push(Instruction::Dcmpl);
            let branch_idx = code.len() as u16;
            code.push(Instruction::Ifge(branch_idx + 3));
            code.push(Instruction::Iconst_1);
            code.push(Instruction::Goto(branch_idx + 4));
            code.push(Instruction::Iconst_0);
            code.push(Instruction::Invokestatic(bool_box));
            code.push(Instruction::Areturn);
            Ok((code, 4, 3))
        }

        // Add: String — String.concat
        ("Add", "String") => {
            let string_class = cp.add_class("java/lang/String")?;
            let string_concat = cp.add_method_ref(
                string_class, "concat", "(Ljava/lang/String;)Ljava/lang/String;",
            )?;
            code.push(Instruction::Aload(1));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Aload(2));
            code.push(Instruction::Checkcast(string_class));
            code.push(Instruction::Invokevirtual(string_concat));
            code.push(Instruction::Areturn);
            Ok((code, 2, 3))
        }

        _ => Err(CodegenError::UnsupportedExpr(format!(
            "Unknown built-in trait instance: {trait_name}${type_name}"
        ))),
    }
}

/// Generate a parameterized instance class with constructor taking subdictionaries.
pub(super) fn generate_parameterized_instance_class(
    class_name: &str,
    trait_interface_name: &str,
    main_class_name: &str,
    methods: &[(String, String, usize, String)],
    param_jvm_types: &HashMap<String, Vec<JvmType>>,
    return_jvm_types: &HashMap<String, JvmType>,
    param_class_names: &HashMap<String, Vec<Option<String>>>,
    subdict_count: usize,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(trait_interface_name)?;
    let main_class = cp.add_class(main_class_name)?;
    let code_utf8 = cp.add_utf8("Code")?;
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;

    let long_box_class = cp.add_class("java/lang/Long")?;
    let long_valueof = cp.add_method_ref(long_box_class, "valueOf", "(J)Ljava/lang/Long;")?;
    let long_unbox = cp.add_method_ref(long_box_class, "longValue", "()J")?;
    let double_box_class = cp.add_class("java/lang/Double")?;
    let double_valueof = cp.add_method_ref(double_box_class, "valueOf", "(D)Ljava/lang/Double;")?;
    let double_unbox = cp.add_method_ref(double_box_class, "doubleValue", "()D")?;
    let bool_box_class = cp.add_class("java/lang/Boolean")?;
    let bool_valueof = cp.add_method_ref(bool_box_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
    let bool_unbox = cp.add_method_ref(bool_box_class, "booleanValue", "()Z")?;

    // Subdict fields
    let mut subdict_field_refs = Vec::new();
    let mut field_list = Vec::new();
    for i in 0..subdict_count {
        let field_name = format!("dict{}", i);
        let field_name_idx = cp.add_utf8(&field_name)?;
        let field_desc_idx = cp.add_utf8("Ljava/lang/Object;")?;
        let obj_desc = "Ljava/lang/Object;".to_string();
        let field_ref = cp.add_field_ref(this_class, &field_name, &obj_desc)?;
        subdict_field_refs.push(field_ref);
        field_list.push(Field {
            access_flags: FieldAccessFlags::PRIVATE | FieldAccessFlags::FINAL,
            name_index: field_name_idx,
            descriptor_index: field_desc_idx,
            field_type: FieldType::Object("java/lang/Object".to_string()),
            attributes: vec![],
        });
    }

    // Constructor
    let mut init_desc_str = String::from("(");
    for _ in 0..subdict_count {
        init_desc_str.push_str("Ljava/lang/Object;");
    }
    init_desc_str.push_str(")V");
    let init_name = cp.add_utf8("<init>")?;
    let init_desc = cp.add_utf8(&init_desc_str)?;

    let mut init_code = vec![
        Instruction::Aload_0,
        Instruction::Invokespecial(object_init),
    ];
    for i in 0..subdict_count {
        init_code.push(Instruction::Aload_0);
        init_code.push(Instruction::Aload((i + 1) as u8));
        init_code.push(Instruction::Putfield(subdict_field_refs[i]));
    }
    init_code.push(Instruction::Return);

    let constructor = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: init_name,
        descriptor_index: init_desc,
        attributes: vec![Attribute::Code {
            name_index: code_utf8,
            max_stack: 3,
            max_locals: (1 + subdict_count) as u16,
            code: init_code,
            exception_table: vec![],
            attributes: vec![],
        }],
    };

    let mut jvm_methods = vec![constructor];

    for (iface_method_name, static_method_name, param_count, static_desc) in methods {
        let mut iface_desc = String::from("(");
        for _ in 0..*param_count {
            iface_desc.push_str("Ljava/lang/Object;");
        }
        iface_desc.push_str(")Ljava/lang/Object;");

        let concrete_params = param_jvm_types.get(iface_method_name).cloned().unwrap_or_default();
        let concrete_ret = return_jvm_types.get(iface_method_name).copied().unwrap_or(JvmType::Int);

        let static_ref = cp.add_method_ref(main_class, static_method_name, static_desc)?;
        let method_name_idx = cp.add_utf8(iface_method_name)?;
        let method_desc_idx = cp.add_utf8(&iface_desc)?;

        let mut bridge_code: Vec<Instruction> = Vec::new();

        // Load subdicts from fields first (these become the dict params for the static method)
        for i in 0..subdict_count {
            bridge_code.push(Instruction::Aload_0);
            bridge_code.push(Instruction::Getfield(subdict_field_refs[i]));
        }

        // Load and unbox user params
        let mut slot: u8 = 1;
        let class_names_for_method = param_class_names.get(iface_method_name).cloned().unwrap_or_default();
        for (param_idx, pt) in concrete_params.iter().enumerate() {
            bridge_code.push(Instruction::Aload(slot));
            match pt {
                JvmType::Long => {
                    bridge_code.push(Instruction::Checkcast(long_box_class));
                    bridge_code.push(Instruction::Invokevirtual(long_unbox));
                }
                JvmType::Double => {
                    bridge_code.push(Instruction::Checkcast(double_box_class));
                    bridge_code.push(Instruction::Invokevirtual(double_unbox));
                }
                JvmType::Int => {
                    bridge_code.push(Instruction::Checkcast(bool_box_class));
                    bridge_code.push(Instruction::Invokevirtual(bool_unbox));
                }
                JvmType::StructRef(_) => {
                    if let Some(Some(cn)) = class_names_for_method.get(param_idx) {
                        let cast_class = cp.add_class(cn)?;
                        bridge_code.push(Instruction::Checkcast(cast_class));
                    }
                }
                _ => {}
            }
            slot += 1;
        }

        bridge_code.push(Instruction::Invokestatic(static_ref));

        match concrete_ret {
            JvmType::Long => bridge_code.push(Instruction::Invokestatic(long_valueof)),
            JvmType::Double => bridge_code.push(Instruction::Invokestatic(double_valueof)),
            JvmType::Int => bridge_code.push(Instruction::Invokestatic(bool_valueof)),
            _ => {}
        }
        bridge_code.push(Instruction::Areturn);

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: method_name_idx,
            descriptor_index: method_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: 20,
                max_locals: (1 + *param_count) as u16,
                code: bridge_code,
                exception_table: vec![],
                attributes: vec![],
            }],
        });
    }

    let class_file = ClassFile {
        version: JAVA_21,
        access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER | ClassAccessFlags::FINAL,
        constant_pool: cp,
        this_class,
        super_class: object_class,
        interfaces: vec![interface_class],
        fields: field_list,
        methods: jvm_methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}
