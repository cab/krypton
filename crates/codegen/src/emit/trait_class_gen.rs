use std::collections::HashMap;

use ristretto_classfile::attributes::{Attribute, Instruction};
use ristretto_classfile::{
    ClassAccessFlags, ClassFile, ConstantPool, Field, FieldAccessFlags, FieldType, Method,
    MethodAccessFlags,
};

use super::compiler::{CodegenError, JvmType};
use super::intrinsics::IntrinsicEntry;
use super::JAVA_21;

/// Pre-resolved type information for a single method in an extern trait bridge class.
pub(super) struct BridgeMethodInfo {
    pub name: String,
    /// Java param descriptors, e.g. `["J", "Ljava/lang/String;"]`
    pub java_param_descs: Vec<String>,
    /// Java return descriptor, e.g. `"V"`, `"J"`, `"Ljava/lang/Object;"`
    pub java_return_desc: String,
    /// True when the Krypton return type is Unit (Java void).
    pub is_void_return: bool,
    /// Total Krypton param count including self (for `invokeinterface` on the trait dict).
    pub krypton_param_count: usize,
}

/// Generate a trait interface class file (e.g., `Eq.class`).
/// All methods take and return Object (type erasure).
/// Single-method traits also extend FunN so dict singletons can be used as lambdas.
pub(super) fn generate_trait_interface_class(
    name: &str,
    methods: &[(String, usize)], // (method_name, param_count)
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let code_utf8 = cp.add_utf8("Code")?;

    // For single-method traits, extend FunN so instances are usable as lambdas
    let mut interfaces = Vec::new();
    if methods.len() == 1 {
        let param_count = methods[0].1;
        let fun_class_name = format!("krypton/runtime/Fun{param_count}");
        let fun_class = cp.add_class(&fun_class_name)?;
        interfaces.push(fun_class);
    }

    let mut iface_method_refs = Vec::new();
    let mut jvm_methods = Vec::new();
    for (method_name, param_count) in methods {
        let mut desc = String::from("(");
        for _ in 0..*param_count {
            desc.push_str("Ljava/lang/Object;");
        }
        desc.push_str(")Ljava/lang/Object;");

        let name_idx = cp.add_utf8(method_name)?;
        let desc_idx = cp.add_utf8(&desc)?;

        let method_ref = cp.add_interface_method_ref(this_class, method_name, &desc)?;
        iface_method_refs.push((method_ref, *param_count));

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::ABSTRACT,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![],
        });
    }

    // For single-method traits, generate a default `apply` bridge method
    if methods.len() == 1 {
        let (method_ref, param_count) = iface_method_refs[0];
        let mut apply_desc = String::from("(");
        for _ in 0..param_count {
            apply_desc.push_str("Ljava/lang/Object;");
        }
        apply_desc.push_str(")Ljava/lang/Object;");

        let apply_name = cp.add_utf8("apply")?;
        let apply_desc_idx = cp.add_utf8(&apply_desc)?;

        // Bridge bytecode: aload_0 (this), aload_1..N (args), invokeinterface trait.method, areturn
        let mut bridge_code = vec![Instruction::Aload_0];
        for i in 1..=(param_count as u8) {
            bridge_code.push(Instruction::Aload(i));
        }
        bridge_code.push(Instruction::Invokeinterface(
            method_ref,
            (param_count + 1) as u8,
        ));
        bridge_code.push(Instruction::Areturn);

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: apply_name,
            descriptor_index: apply_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: (param_count + 1) as u16,
                max_locals: (param_count + 1) as u16,
                code: bridge_code,
                exception_table: vec![],
                attributes: vec![],
            }],
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
        interfaces,
        methods: jvm_methods,
        ..Default::default()
    };

    let mut buffer = Vec::new();
    class_file.to_bytes(&mut buffer)?;
    Ok(buffer)
}

/// Generate a bridge class for an extern trait that adapts a Krypton (value, dict) pair
/// into a Java interface implementation.
///
/// The bridge class has two `Object` fields (`value` and `dict`), a constructor that
/// stores them, and bridge methods that delegate to the Krypton trait dict interface.
///
/// Example for `Runnable`:
/// ```java
/// public class module/Runnable$$Bridge implements java/lang/Runnable {
///     Object value;
///     Object dict;
///     <init>(Object, Object)V { super(); this.value = arg0; this.dict = arg1; }
///     void run() {
///         this.dict.run(this.value);  // via invokeinterface on Krypton trait
///     }
/// }
/// ```
pub(super) fn generate_extern_trait_bridge_class(
    bridge_class_name: &str,
    java_interface: &str,
    krypton_trait_interface: &str,
    methods: &[BridgeMethodInfo],
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(bridge_class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let java_iface_class = cp.add_class(java_interface)?;
    let krypton_iface_class = cp.add_class(krypton_trait_interface)?;
    let code_utf8 = cp.add_utf8("Code")?;

    // Fields: value and dict, both Object
    let object_desc = "Ljava/lang/Object;";
    let value_field_name = cp.add_utf8("value")?;
    let value_field_desc = cp.add_utf8(object_desc)?;
    let dict_field_name = cp.add_utf8("dict")?;
    let dict_field_desc = cp.add_utf8(object_desc)?;

    let value_field_ref = cp.add_field_ref(this_class, "value", object_desc)?;
    let dict_field_ref = cp.add_field_ref(this_class, "dict", object_desc)?;

    // Object.<init>()V
    let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;

    let fields = vec![
        Field {
            access_flags: FieldAccessFlags::PRIVATE,
            name_index: value_field_name,
            descriptor_index: value_field_desc,
            field_type: FieldType::Object("java/lang/Object".to_string()),
            attributes: vec![],
        },
        Field {
            access_flags: FieldAccessFlags::PRIVATE,
            name_index: dict_field_name,
            descriptor_index: dict_field_desc,
            field_type: FieldType::Object("java/lang/Object".to_string()),
            attributes: vec![],
        },
    ];

    let mut jvm_methods = Vec::new();

    // Constructor: <init>(Object value, Object dict)V
    {
        let init_name = cp.add_utf8("<init>")?;
        let init_desc = cp.add_utf8("(Ljava/lang/Object;Ljava/lang/Object;)V")?;

        let code = vec![
            Instruction::Aload_0,                    // this
            Instruction::Invokespecial(object_init), // super()
            Instruction::Aload_0,                    // this
            Instruction::Aload_1,                    // value
            Instruction::Putfield(value_field_ref),  // this.value = value
            Instruction::Aload_0,                    // this
            Instruction::Aload_2,                    // dict
            Instruction::Putfield(dict_field_ref),   // this.dict = dict
            Instruction::Return,
        ];

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: init_name,
            descriptor_index: init_desc,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack: 2,
                max_locals: 3, // this + value + dict
                code,
                exception_table: vec![],
                attributes: vec![],
            }],
        });
    }

    // Boxing/unboxing constant pool entries (added lazily)
    let long_box_class = cp.add_class("java/lang/Long")?;
    let long_valueof = cp.add_method_ref(long_box_class, "valueOf", "(J)Ljava/lang/Long;")?;
    let long_unbox = cp.add_method_ref(long_box_class, "longValue", "()J")?;
    let double_box_class = cp.add_class("java/lang/Double")?;
    let double_valueof = cp.add_method_ref(double_box_class, "valueOf", "(D)Ljava/lang/Double;")?;
    let double_unbox = cp.add_method_ref(double_box_class, "doubleValue", "()D")?;
    let bool_box_class = cp.add_class("java/lang/Boolean")?;
    let bool_valueof = cp.add_method_ref(bool_box_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;
    let bool_unbox = cp.add_method_ref(bool_box_class, "booleanValue", "()Z")?;

    // Bridge methods: each Java interface method delegates to the Krypton trait dict
    for info in methods {
        // Build Java method descriptor from resolved types
        let mut java_desc = String::from("(");
        for pd in &info.java_param_descs {
            java_desc.push_str(pd);
        }
        java_desc.push(')');
        java_desc.push_str(&info.java_return_desc);

        // Krypton trait interface method descriptor: all Object (type-erased)
        let mut krypton_desc = String::from("(");
        for _ in 0..info.krypton_param_count {
            krypton_desc.push_str("Ljava/lang/Object;");
        }
        krypton_desc.push_str(")Ljava/lang/Object;");

        let krypton_method_ref =
            cp.add_interface_method_ref(krypton_iface_class, &info.name, &krypton_desc)?;

        let method_name_idx = cp.add_utf8(&info.name)?;
        let method_desc_idx = cp.add_utf8(&java_desc)?;

        // Bytecode:
        //   aload_0; getfield dict; checkcast KryptonTraitInterface
        //   aload_0; getfield value   // self param for Krypton method
        //   [load + box each Java param]
        //   invokeinterface KryptonTrait.method(Object, ...)Object
        //   [unbox/convert result for Java return type]
        let mut code = vec![
            Instruction::Aload_0,
            Instruction::Getfield(dict_field_ref),
            Instruction::Checkcast(krypton_iface_class),
            Instruction::Aload_0,
            Instruction::Getfield(value_field_ref),
        ];

        // Load and box Java method params for the Krypton (all-Object) interface.
        // Primitives must be boxed; reference types widen to Object naturally.
        let mut slot: u16 = 1; // slot 0 = this
        for pd in &info.java_param_descs {
            match pd.as_str() {
                "J" => {
                    code.push(Instruction::Lload(slot as u8));
                    code.push(Instruction::Invokestatic(long_valueof));
                    slot += 2;
                }
                "D" => {
                    code.push(Instruction::Dload(slot as u8));
                    code.push(Instruction::Invokestatic(double_valueof));
                    slot += 2;
                }
                "Z" => {
                    code.push(Instruction::Iload(slot as u8));
                    code.push(Instruction::Invokestatic(bool_valueof));
                    slot += 1;
                }
                _ => {
                    // Reference type — loads as Object directly
                    code.push(Instruction::Aload(slot as u8));
                    slot += 1;
                }
            }
        }

        code.push(Instruction::Invokeinterface(
            krypton_method_ref,
            info.krypton_param_count as u8 + 1, // +1 for the dict reference (interface receiver)
        ));

        // Convert the Object result from the Krypton invokeinterface to the Java return type
        if info.is_void_return {
            code.push(Instruction::Pop);
            code.push(Instruction::Return);
        } else {
            match info.java_return_desc.as_str() {
                "J" => {
                    code.push(Instruction::Checkcast(long_box_class));
                    code.push(Instruction::Invokevirtual(long_unbox));
                    code.push(Instruction::Lreturn);
                }
                "D" => {
                    code.push(Instruction::Checkcast(double_box_class));
                    code.push(Instruction::Invokevirtual(double_unbox));
                    code.push(Instruction::Dreturn);
                }
                "Z" => {
                    code.push(Instruction::Checkcast(bool_box_class));
                    code.push(Instruction::Invokevirtual(bool_unbox));
                    code.push(Instruction::Ireturn);
                }
                desc => {
                    // Reference type — checkcast to the concrete class
                    let class_name = &desc[1..desc.len() - 1]; // strip L...; wrapper
                    let cast_class = cp.add_class(class_name)?;
                    code.push(Instruction::Checkcast(cast_class));
                    code.push(Instruction::Areturn);
                }
            }
        }

        let max_stack = 2 + info.krypton_param_count as u16; // dict + value + params
        let max_locals = slot; // this + java method param slots

        jvm_methods.push(Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: method_name_idx,
            descriptor_index: method_desc_idx,
            attributes: vec![Attribute::Code {
                name_index: code_utf8,
                max_stack,
                max_locals,
                code,
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
        interfaces: vec![java_iface_class],
        fields,
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

        let concrete_params = param_jvm_types
            .get(iface_method_name)
            .expect("ICE: bridge method missing param_jvm_types");
        let concrete_ret = return_jvm_types
            .get(iface_method_name)
            .copied()
            .expect("ICE: bridge method missing return_jvm_type");

        let static_ref = cp.add_method_ref(main_class, static_method_name, static_desc)?;

        let method_name_idx = cp.add_utf8(iface_method_name)?;
        let method_desc_idx = cp.add_utf8(&iface_desc)?;

        // Build bridge code: unbox params → invokestatic → box result
        let mut bridge_code: Vec<Instruction> = Vec::new();
        let mut slot: u8 = 1; // slot 0 = this

        let class_names_for_method = param_class_names
            .get(iface_method_name)
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
                    if let Some(Some(cn)) = class_names_for_method.get(param_idx) {
                        let cast_class = cp.add_class(cn)?;
                        bridge_code.push(Instruction::Checkcast(cast_class));
                    }
                }
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
            JvmType::StructRef(_) => { /* reference types: no boxing needed before Areturn */ }
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
    trait_interface_name: &str,
    entry: &IntrinsicEntry,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(trait_interface_name)?;
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

    let (bridge_code, max_stack, max_locals, _frames) =
        super::intrinsics::build_bridge_bytecode(&mut cp, this_class, object_class, entry)?;

    let show_method = Method {
        access_flags: MethodAccessFlags::PUBLIC,
        name_index: show_name,
        descriptor_index: show_desc_idx,
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
    trait_interface_name: &str,
    entry: &IntrinsicEntry,
) -> Result<Vec<u8>, CodegenError> {
    let mut cp = ConstantPool::default();

    let this_class = cp.add_class(class_name)?;
    let object_class = cp.add_class("java/lang/Object")?;
    let interface_class = cp.add_class(trait_interface_name)?;
    let code_utf8 = cp.add_utf8("Code")?;
    let smt_name = cp.add_utf8("StackMapTable")?;
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
    let is_unary = entry.is_unary();
    let iface_desc = if is_unary {
        "(Ljava/lang/Object;)Ljava/lang/Object;"
    } else {
        "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"
    };

    let method_name_idx = cp.add_utf8(entry.method_name)?;
    let method_desc_idx = cp.add_utf8(iface_desc)?;

    // Build bridge method bytecode via intrinsics registry
    let (bridge_code, max_stack, max_locals, bridge_frames) =
        super::intrinsics::build_bridge_bytecode(&mut cp, this_class, object_class, entry)?;
    let bridge_attributes = if bridge_frames.is_empty() {
        vec![]
    } else {
        vec![Attribute::StackMapTable {
            name_index: smt_name,
            frames: bridge_frames,
        }]
    };

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
            attributes: bridge_attributes,
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

/// JVM class name triple required to emit a parameterized instance class.
pub(super) struct TraitClassNames<'a> {
    pub class: &'a str,
    pub trait_interface: &'a str,
    pub main: &'a str,
}

/// Per-method JVM signature info needed to bridge each trait method.
pub(super) struct TraitMethodSignatures<'a> {
    pub methods: &'a [(String, String, usize, String)],
    pub param_jvm_types: &'a HashMap<String, Vec<JvmType>>,
    pub return_jvm_types: &'a HashMap<String, JvmType>,
    pub param_class_names: &'a HashMap<String, Vec<Option<String>>>,
}

/// Generate a parameterized instance class with constructor taking subdictionaries.
pub(super) fn generate_parameterized_instance_class(
    names: TraitClassNames<'_>,
    sigs: TraitMethodSignatures<'_>,
    subdict_count: usize,
) -> Result<Vec<u8>, CodegenError> {
    let TraitClassNames {
        class: class_name,
        trait_interface: trait_interface_name,
        main: main_class_name,
    } = names;
    let TraitMethodSignatures {
        methods,
        param_jvm_types,
        return_jvm_types,
        param_class_names,
    } = sigs;
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
    for (i, &field_ref) in subdict_field_refs.iter().enumerate().take(subdict_count) {
        init_code.push(Instruction::Aload_0);
        init_code.push(Instruction::Aload((i + 1) as u8));
        init_code.push(Instruction::Putfield(field_ref));
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

        let concrete_params = param_jvm_types
            .get(iface_method_name)
            .expect("ICE: bridge method missing param_jvm_types");
        let concrete_ret = return_jvm_types
            .get(iface_method_name)
            .copied()
            .expect("ICE: bridge method missing return_jvm_type");

        let static_ref = cp.add_method_ref(main_class, static_method_name, static_desc)?;
        let method_name_idx = cp.add_utf8(iface_method_name)?;
        let method_desc_idx = cp.add_utf8(&iface_desc)?;

        let mut bridge_code: Vec<Instruction> = Vec::new();

        // Load subdicts from fields first (these become the dict params for the static method)
        for &field_ref in subdict_field_refs.iter().take(subdict_count) {
            bridge_code.push(Instruction::Aload_0);
            bridge_code.push(Instruction::Getfield(field_ref));
        }

        // Load and unbox user params
        let mut slot: u8 = 1;
        let class_names_for_method = param_class_names
            .get(iface_method_name)
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
            }
            slot += 1;
        }

        bridge_code.push(Instruction::Invokestatic(static_ref));

        match concrete_ret {
            JvmType::Long => bridge_code.push(Instruction::Invokestatic(long_valueof)),
            JvmType::Double => bridge_code.push(Instruction::Invokestatic(double_valueof)),
            JvmType::Int => bridge_code.push(Instruction::Invokestatic(bool_valueof)),
            JvmType::StructRef(_) => { /* reference types: no boxing needed before Areturn */ }
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
