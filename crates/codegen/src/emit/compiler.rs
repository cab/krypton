//! Core compiler types, expression dispatch, and function compilation.

use std::collections::HashMap;

use krypton_ir::{bind_type_vars, SimpleExprKind, TraitName, Type, TypeVarId};
use krypton_parser::ast::Span;
use ristretto_classfile::attributes::{Attribute, Instruction, VerificationType};
use ristretto_classfile::{ClassAccessFlags, ClassFile, ConstantPool, Method, MethodAccessFlags};

use super::builder::{BytecodeBuilder, CpoolRefs};
use super::lambda::LambdaState;
use super::{jvm_type_to_field_descriptor, type_to_jvm_basic, JAVA_21};

/// Tracks the JVM type of a value on the operand stack.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum JvmType {
    Long,
    Double,
    Int,
    StructRef(u16), // cpool class index for struct type
}

impl JvmType {
    pub fn is_reference(&self) -> bool {
        matches!(self, JvmType::StructRef(_))
    }
}

/// Error type for codegen failures.
#[derive(Debug)]
pub struct CodegenError {
    pub kind: CodegenErrorKind,
    /// Originating module's (filename, source text), if different from the main file.
    pub error_source: Option<(String, String)>,
}

#[derive(Debug)]
pub enum CodegenErrorKind {
    ClassFile(ristretto_classfile::Error),
    NoMainFunction,
    UnsupportedExpr(String, Option<Span>),
    UndefinedVariable(String, Option<Span>),
    TypeError(String, Option<Span>),
    RecurNotInTailPosition(Option<Span>),
}

impl CodegenError {
    pub fn error_code(&self) -> &'static str {
        self.kind.error_code()
    }

    pub fn span(&self) -> Option<Span> {
        self.kind.span()
    }

    /// Attach originating module source info for diagnostic rendering.
    pub fn with_source(mut self, filename: String, source: String) -> Self {
        self.error_source = Some((filename, source));
        self
    }
}

impl CodegenErrorKind {
    pub fn error_code(&self) -> &'static str {
        match self {
            CodegenErrorKind::ClassFile(_) => "C0001",
            CodegenErrorKind::NoMainFunction => "C0002",
            CodegenErrorKind::UnsupportedExpr(..) => "C0003",
            CodegenErrorKind::UndefinedVariable(..) => "C0004",
            CodegenErrorKind::TypeError(..) => "C0005",
            CodegenErrorKind::RecurNotInTailPosition(_) => "C0006",
        }
    }

    pub fn span(&self) -> Option<Span> {
        match self {
            CodegenErrorKind::ClassFile(_) | CodegenErrorKind::NoMainFunction => None,
            CodegenErrorKind::UnsupportedExpr(_, s)
            | CodegenErrorKind::UndefinedVariable(_, s)
            | CodegenErrorKind::TypeError(_, s) => *s,
            CodegenErrorKind::RecurNotInTailPosition(s) => *s,
        }
    }
}

// Convenience constructors to minimize churn at call sites.
#[allow(non_snake_case)]
impl CodegenError {
    pub fn ClassFile(e: ristretto_classfile::Error) -> Self {
        CodegenErrorKind::ClassFile(e).into()
    }
    pub fn NoMainFunction() -> Self {
        CodegenErrorKind::NoMainFunction.into()
    }
    pub fn UnsupportedExpr(msg: String, span: Option<Span>) -> Self {
        CodegenErrorKind::UnsupportedExpr(msg, span).into()
    }
    pub fn UndefinedVariable(msg: String, span: Option<Span>) -> Self {
        CodegenErrorKind::UndefinedVariable(msg, span).into()
    }
    pub fn TypeError(msg: String, span: Option<Span>) -> Self {
        CodegenErrorKind::TypeError(msg, span).into()
    }
    pub fn RecurNotInTailPosition(span: Option<Span>) -> Self {
        CodegenErrorKind::RecurNotInTailPosition(span).into()
    }
}

impl From<CodegenErrorKind> for CodegenError {
    fn from(kind: CodegenErrorKind) -> Self {
        CodegenError {
            kind,
            error_source: None,
        }
    }
}

impl From<ristretto_classfile::Error> for CodegenError {
    fn from(e: ristretto_classfile::Error) -> Self {
        CodegenErrorKind::ClassFile(e).into()
    }
}

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

impl std::fmt::Display for CodegenErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CodegenErrorKind::ClassFile(e) => write!(f, "class file error: {e}"),
            CodegenErrorKind::NoMainFunction => write!(f, "no main function found"),
            CodegenErrorKind::UnsupportedExpr(s, _) => write!(f, "unsupported expression: {s}"),
            CodegenErrorKind::UndefinedVariable(s, _) => write!(f, "undefined variable: {s}"),
            CodegenErrorKind::TypeError(s, _) => write!(f, "type error: {s}"),
            CodegenErrorKind::RecurNotInTailPosition(_) => {
                write!(f, "recur must be in tail position")
            }
        }
    }
}

/// Info about a compiled user-defined function, used for invokestatic calls.
#[derive(Clone)]
pub(super) struct FunctionInfo {
    pub(super) method_ref: u16,
    pub(super) param_types: Vec<JvmType>,
    pub(super) return_type: JvmType,
    pub(super) is_void: bool,
}

/// Info about a struct type for codegen.
#[derive(Debug)]
pub(super) struct StructInfo {
    pub(super) class_index: u16,
    pub(super) class_name: String,
    pub(super) fields: Vec<(String, JvmType)>,
    pub(super) constructor_ref: u16,
    pub(super) accessor_refs: HashMap<String, u16>,
}

/// A single field in a sum-type variant.
#[derive(Clone)]
pub(super) struct VariantField {
    pub(super) name: String,
    pub(super) jvm_type: JvmType,
    pub(super) is_erased: bool,
}

/// Info about a single variant of a sum type.
pub(super) struct VariantInfo {
    pub(super) class_index: u16,
    pub(super) fields: Vec<VariantField>,
    pub(super) constructor_ref: u16,
    pub(super) field_refs: Vec<u16>, // field ref indices in main cpool
}

/// Info about a sum type (sealed interface).
pub(super) struct SumTypeInfo {
    pub(super) interface_class_index: u16,
    pub(super) variants: HashMap<String, VariantInfo>,
}

/// Info about a tuple type (backed by krypton/runtime/TupleN).
pub(super) struct TupleInfo {
    pub(super) class_index: u16,
    pub(super) constructor_ref: u16,
    pub(super) field_refs: Vec<u16>,
}

/// Type registry for codegen (structs, sum types, tuples, functions).
pub(super) struct CodegenTypeInfo {
    pub(super) struct_info: HashMap<String, StructInfo>,
    pub(super) class_descriptors: HashMap<u16, String>,
    pub(super) sum_type_info: HashMap<String, SumTypeInfo>,
    pub(super) variant_to_sum: HashMap<String, String>,
    pub(super) tuple_info: HashMap<usize, TupleInfo>,
    pub(super) functions: HashMap<String, Vec<FunctionInfo>>,
    pub(super) fn_tc_types: HashMap<String, (Vec<Type>, Type)>,
    /// Cross-module sum type references: bare_name → class_index.
    /// These only carry the class index (no variant info) since the defining
    /// module emits the actual bytecode.
    pub(super) extern_sum_class_indices: HashMap<String, u16>,
}

impl CodegenTypeInfo {
    /// Get the first (or only) function info for a name.
    pub(super) fn get_function(&self, name: &str) -> Option<&FunctionInfo> {
        self.functions.get(name).and_then(|v| v.first())
    }

    pub(super) fn jvm_type_descriptor(&self, ty: JvmType) -> String {
        match ty {
            JvmType::StructRef(idx) => self.class_descriptors[&idx].clone(),
            other => jvm_type_to_field_descriptor(other),
        }
    }

    pub(super) fn build_descriptor(&self, params: &[JvmType], ret: JvmType) -> String {
        let mut desc = String::from("(");
        for p in params {
            desc.push_str(&self.jvm_type_descriptor(*p));
        }
        desc.push(')');
        desc.push_str(&self.jvm_type_descriptor(ret));
        desc
    }
}

/// Info about a trait for dispatch.
pub(super) struct TraitDispatchInfo {
    pub(super) interface_class: u16, // class index of the trait interface in main cpool
    pub(super) method_refs: HashMap<String, u16>, // method_name → interface method_ref
}

/// Info about a trait instance singleton.
pub(super) struct InstanceSingletonInfo {
    pub(super) instance_field_ref: u16, // field_ref for INSTANCE field (for getstatic)
}

/// Info for constructing a bridge class at call sites.
pub(super) struct ExternTraitBridgeInfo {
    pub(super) bridge_class: u16,      // class index for the bridge class
    pub(super) bridge_init: u16,       // method_ref for <init>(Object, Object)V
}

/// Trait dispatch state for codegen.
pub(super) struct TraitState {
    pub(super) trait_dispatch: HashMap<TraitName, TraitDispatchInfo>,
    pub(super) instance_singletons: HashMap<(TraitName, Type), InstanceSingletonInfo>,
    pub(super) impl_dict_requirements: HashMap<String, Vec<DictRequirement>>,
    pub(super) dict_locals: HashMap<(TraitName, TypeVarId), u16>,
    pub(super) parameterized_instances: HashMap<TraitName, Vec<ParameterizedInstanceInfo>>,
    pub(super) extern_trait_bridges: HashMap<TraitName, ExternTraitBridgeInfo>,
}

impl TraitState {
    /// Look up a dict local by trait name and type variable ID.
    pub(super) fn get_dict_local(&self, trait_name: &TraitName, var_id: TypeVarId) -> Option<u16> {
        self.dict_locals.get(&(trait_name.clone(), var_id)).copied()
    }

    /// Look up a dict local by trait name only (for single-constraint lookups like trait_dict).
    /// Returns the first match if multiple exist.
    pub(super) fn get_dict_local_by_trait(&self, trait_name: &TraitName) -> Option<u16> {
        self.dict_locals
            .iter()
            .find(|((tn, _), _)| tn == trait_name)
            .map(|(_, &slot)| slot)
    }

}

#[derive(Clone)]
pub(super) struct DictRequirement {
    pub(super) trait_name: TraitName,
    pub(super) type_var: TypeVarId,
}

impl DictRequirement {
    pub(super) fn trait_name(&self) -> &TraitName {
        &self.trait_name
    }

    pub(super) fn type_var_id(&self) -> TypeVarId {
        self.type_var
    }
}

#[derive(Clone)]
pub(super) struct ParameterizedInstanceInfo {
    pub(super) class_name: String,
    pub(super) target_type: Type,
    pub(super) requirements: Vec<DictRequirement>,
}

/// Info about the Vec backing class (KryptonArray).
#[derive(Clone)]
pub(super) struct VecInfo {
    pub(super) init_ref: u16,
    pub(super) set_ref: u16,
    pub(super) freeze_ref: u16,
}

/// Info about a join point (local continuation) for IR compilation.
pub(super) struct JoinPointInfo {
    pub(super) target_offset: u16,
    pub(super) param_slots: Vec<(u16, JvmType)>,
    pub(super) frame_locals: Vec<VerificationType>,
    pub(super) forward_jumps: Vec<usize>,
}

pub(super) struct Compiler<'link> {
    pub(super) link_view: &'link krypton_typechecker::link_context::ModuleLinkView<'link>,
    pub(super) cp: ConstantPool,
    pub(super) this_class: u16,
    pub(super) builder: BytecodeBuilder,
    pub(super) lambda: LambdaState,
    pub(super) types: CodegenTypeInfo,
    pub(super) traits: TraitState,
    pub(super) vec_info: Option<VecInfo>,
    // IR compilation state
    pub(super) var_locals: HashMap<krypton_ir::VarId, (u16, JvmType)>,
    /// Slots pre-allocated for resource variables (null-initialized at function entry
    /// so the JVM verifier sees valid types at every PC in the exception table range).
    /// Consumed by Let binding compilation — checked before allocating a new slot.
    pre_allocated_slots: HashMap<krypton_ir::VarId, u16>,
    pub(super) var_types: HashMap<krypton_ir::VarId, Type>,
    pub(super) join_points: HashMap<krypton_ir::VarId, JoinPointInfo>,
    pub(super) fn_names: HashMap<krypton_ir::FnId, String>,
    /// sum_type_name → (tag → variant_name) for IR Switch compilation.
    pub(super) variant_tags: HashMap<String, HashMap<u32, String>>,
    /// sum_type_name → type_params for resolving generic types in switch bindings.
    pub(super) sum_type_params: HashMap<String, Vec<krypton_ir::TypeVarId>>,
    /// variant_name → field types (from IR SumTypeDef) for resolving generic bindings.
    pub(super) variant_field_types: HashMap<String, Vec<Type>>,
    pub(super) raw_extern_functions: HashMap<String, FunctionInfo>,
    pub(super) raw_extern_classes: HashMap<String, u16>,
}

impl<'link> Compiler<'link> {
    pub(super) fn is_abstract_type_ctor(ty: &Type) -> bool {
        match ty {
            Type::Var(_) => true,
            Type::Own(inner) => Self::is_abstract_type_ctor(inner),
            Type::App(ctor, _) => Self::is_abstract_type_ctor(ctor),
            Type::Dict { .. } | Type::FnHole => false,
            _ => false,
        }
    }

    pub(super) fn new(class_name: &str, link_view: &'link krypton_typechecker::link_context::ModuleLinkView<'link>) -> Result<Self, CodegenError> {
        let mut cp = ConstantPool::default();

        let this_class = cp.add_class(class_name)?;
        let object_class = cp.add_class("java/lang/Object")?;
        let code_utf8 = cp.add_utf8("Code")?;
        let object_init = cp.add_method_ref(object_class, "<init>", "()V")?;
        let init_name = cp.add_utf8("<init>")?;
        let init_desc = cp.add_utf8("()V")?;

        // StackMapTable support
        let smt_name = cp.add_utf8("StackMapTable")?;
        let string_class = cp.add_class("java/lang/String")?;
        let string_arr_class = cp.add_class("[Ljava/lang/String;")?;

        // Boxing support: Long.valueOf, Double.valueOf, Boolean.valueOf
        let long_box_class = cp.add_class("java/lang/Long")?;
        let long_box_valueof =
            cp.add_method_ref(long_box_class, "valueOf", "(J)Ljava/lang/Long;")?;
        let double_box_class = cp.add_class("java/lang/Double")?;
        let double_box_valueof =
            cp.add_method_ref(double_box_class, "valueOf", "(D)Ljava/lang/Double;")?;
        let bool_box_class = cp.add_class("java/lang/Boolean")?;
        let bool_box_valueof =
            cp.add_method_ref(bool_box_class, "valueOf", "(Z)Ljava/lang/Boolean;")?;

        // Unboxing support
        let long_unbox = cp.add_method_ref(long_box_class, "longValue", "()J")?;
        let double_unbox = cp.add_method_ref(double_box_class, "doubleValue", "()D")?;
        let bool_unbox = cp.add_method_ref(bool_box_class, "booleanValue", "()Z")?;

        // String operations
        let string_concat = cp.add_method_ref(
            string_class,
            "concat",
            "(Ljava/lang/String;)Ljava/lang/String;",
        )?;
        let string_equals = cp.add_method_ref(string_class, "equals", "(Ljava/lang/Object;)Z")?;

        // Intrinsic support
        let runtime_exception_class = cp.add_class("java/lang/RuntimeException")?;
        let runtime_exception_init =
            cp.add_method_ref(runtime_exception_class, "<init>", "(Ljava/lang/String;)V")?;
        // Conversion method refs for IR compilation
        let long_to_string =
            cp.add_method_ref(long_box_class, "toString", "(J)Ljava/lang/String;")?;
        let double_to_string =
            cp.add_method_ref(double_box_class, "toString", "(D)Ljava/lang/String;")?;
        let bool_to_string =
            cp.add_method_ref(bool_box_class, "toString", "(Z)Ljava/lang/String;")?;
        // Finally handler support (resource auto-close on panic)
        let throwable_class = cp.add_class("java/lang/Throwable")?;
        let system_class = cp.add_class("java/lang/System")?;
        let printstream_class = cp.add_class("java/io/PrintStream")?;
        let system_err_field = cp.add_field_ref(system_class, "err", "Ljava/io/PrintStream;")?;
        let printstream_println =
            cp.add_method_ref(printstream_class, "println", "(Ljava/lang/String;)V")?;
        let refs = CpoolRefs {
            code_utf8,
            object_init,
            init_name,
            init_desc,
            smt_name,
            string_class,
            long_box_valueof,
            double_box_valueof,
            bool_box_valueof,
            long_box_class,
            long_unbox,
            double_box_class,
            double_unbox,
            bool_box_class,
            bool_unbox,
            object_class,
            string_concat,
            string_equals,
            string_arr_class,
            runtime_exception_class,
            runtime_exception_init,
            long_to_string,
            double_to_string,
            bool_to_string,
            throwable_class,
            system_err_field,
            printstream_println,
        };
        let mut builder = BytecodeBuilder::new(refs);
        builder.next_local = 1; // slot 0 = String[] args for main
        builder.frame.local_types = vec![VerificationType::Object {
            cpool_index: builder.refs.string_arr_class,
        }];

        let compiler = Compiler {
            link_view,
            cp,
            this_class,
            builder,
            lambda: LambdaState {
                lambda_counter: 0,
                lambda_methods: Vec::new(),
                bootstrap_methods: Vec::new(),
                metafactory_handle: None,
                fun_classes: HashMap::new(),
                fun_apply_refs: HashMap::new(),
            },
            types: CodegenTypeInfo {
                struct_info: HashMap::new(),
                class_descriptors: {
                    let mut cd = HashMap::new();
                    cd.insert(string_class, "Ljava/lang/String;".to_string());
                    cd.insert(long_box_class, "Ljava/lang/Long;".to_string());
                    cd.insert(double_box_class, "Ljava/lang/Double;".to_string());
                    cd.insert(bool_box_class, "Ljava/lang/Boolean;".to_string());
                    cd
                },
                sum_type_info: HashMap::new(),
                variant_to_sum: HashMap::new(),
                tuple_info: HashMap::new(),
                extern_sum_class_indices: HashMap::new(),
                functions: HashMap::new(),
                fn_tc_types: HashMap::new(),
            },
            traits: TraitState {
                trait_dispatch: HashMap::new(),
                instance_singletons: HashMap::new(),
                impl_dict_requirements: HashMap::new(),
                dict_locals: HashMap::new(),
                parameterized_instances: HashMap::new(),
                extern_trait_bridges: HashMap::new(),
            },
            vec_info: None,
            var_locals: HashMap::new(),
            pre_allocated_slots: HashMap::new(),
            var_types: HashMap::new(),
            join_points: HashMap::new(),
            fn_names: HashMap::new(),
            variant_tags: HashMap::new(),
            sum_type_params: HashMap::new(),
            variant_field_types: HashMap::new(),
            raw_extern_functions: HashMap::new(),
            raw_extern_classes: HashMap::new(),
        };

        Ok(compiler)
    }

    /// Map a typechecker Type to a JvmType, using struct_info/sum_type_info for Named types.
    ///
    /// This resolves ALL Krypton types including sum types and tuples. For raw
    /// extern descriptors (which must match Java's actual signatures), use
    /// `extern_type_to_jvm` instead — it falls back to Object for Krypton-only
    /// named types that Java doesn't know about.
    pub(super) fn type_to_jvm(&self, ty: &Type) -> Result<JvmType, CodegenError> {
        match ty {
            Type::Named(name, _) => {
                if name == "Dict" {
                    return Ok(JvmType::StructRef(self.builder.refs.object_class));
                }
                if let Some(info) = self.types.struct_info.get(name) {
                    Ok(JvmType::StructRef(info.class_index))
                } else if let Some(info) = self.types.sum_type_info.get(name) {
                    Ok(JvmType::StructRef(info.interface_class_index))
                } else if let Some(&class_index) = self.types.extern_sum_class_indices.get(name) {
                    Ok(JvmType::StructRef(class_index))
                } else {
                    Err(CodegenError::TypeError(
                        format!("ICE: unknown named type `{name}` — not registered as struct, sum type, or extern"),
                        None,
                    ))
                }
            }
            Type::Var(_) => Ok(JvmType::StructRef(self.builder.refs.object_class)),
            Type::Fn(params, _) => {
                let arity = params.len() as u8;
                if let Some(&class_idx) = self.lambda.fun_classes.get(&arity) {
                    Ok(JvmType::StructRef(class_idx))
                } else {
                    Ok(JvmType::StructRef(self.builder.refs.object_class))
                }
            }
            Type::Tuple(elems) => {
                let arity = elems.len();
                if let Some(info) = self.types.tuple_info.get(&arity) {
                    Ok(JvmType::StructRef(info.class_index))
                } else {
                    Err(CodegenError::TypeError(
                        format!("unknown tuple arity: {arity}"),
                        None,
                    ))
                }
            }
            Type::String => Ok(JvmType::StructRef(self.builder.refs.string_class)),
            Type::Own(inner) => self.type_to_jvm(inner),
            Type::App(ctor, _) if Self::is_abstract_type_ctor(ctor) => {
                Ok(JvmType::StructRef(self.builder.refs.object_class))
            }
            Type::App(_, _) => Err(CodegenError::TypeError(
                format!(
                    "unexpected unreduced concrete type application during codegen erasure: {ty}"
                ),
                None,
            )),
            Type::Dict { .. } | Type::FnHole => {
                Ok(JvmType::StructRef(self.builder.refs.object_class))
            }
            other => type_to_jvm_basic(other),
        }
    }

    /// Look up variant metadata: class_index, constructor_ref, interface_class_index, fields.
    pub(super) fn variant_construct_info(
        &self,
        variant_name: &str,
    ) -> Result<(u16, u16, u16, Vec<VariantField>), CodegenError> {
        let sum_name = self
            .types
            .variant_to_sum
            .get(variant_name)
            .ok_or_else(|| {
                CodegenError::TypeError(format!("unknown variant: {variant_name}"), None)
            })?
            .clone();
        let sum_info = &self.types.sum_type_info[&sum_name];
        let vi = &sum_info.variants[variant_name];
        Ok((
            vi.class_index,
            vi.constructor_ref,
            sum_info.interface_class_index,
            vi.fields.clone(),
        ))
    }

    /// After field args are on the stack: pop frame entries, emit Invokespecial, push result type.
    pub(super) fn emit_variant_invokespecial(
        &mut self,
        constructor_ref: u16,
        fields: &[VariantField],
        result_class: u16,
    ) -> JvmType {
        for f in fields.iter().rev() {
            if f.is_erased {
                self.builder.frame.pop_type();
            } else {
                self.builder.pop_jvm_type(f.jvm_type);
            }
        }
        self.builder.frame.pop_type(); // new
        self.builder.frame.pop_type(); // dup
        self.builder
            .emit(Instruction::Invokespecial(constructor_ref));
        let result_type = JvmType::StructRef(result_class);
        self.builder.push_jvm_type(result_type);
        result_type
    }

    pub(super) fn nullable_inner_type<'a>(
        &self,
        ty: &'a Type,
    ) -> Result<&'a Type, CodegenError> {
        match ty {
            Type::Named(name, args) if name == "Option" && args.len() == 1 => Ok(&args[0]),
            other => Err(CodegenError::TypeError(
                format!("nullable extern must return Option[T], found {other}"),
                None,
            )),
        }
    }

    pub(super) fn nullable_host_return_jvm(
        &self,
        ty: &Type,
    ) -> Result<JvmType, CodegenError> {
        self.nullable_host_jvm_for_inner(self.nullable_inner_type(ty)?)
    }

    pub(super) fn throws_inner_type<'a>(
        &self,
        ty: &'a Type,
    ) -> Result<&'a Type, CodegenError> {
        match ty {
            Type::Named(name, args) if name == "Result" && args.len() == 2 => Ok(&args[1]),
            other => Err(CodegenError::TypeError(
                format!("@throws extern must return Result[String, T], found {other}"),
                None,
            )),
        }
    }

    pub(super) fn result_variant_construct_info(
        &self,
        result_type: &Type,
        variant_name: &str,
    ) -> Result<(u16, u16, u16, Vec<VariantField>), CodegenError> {
        let sum_name = match result_type {
            Type::Named(name, _) => name,
            other => {
                return Err(CodegenError::TypeError(
                    format!("expected Result sum type, found {other}"),
                    None,
                ))
            }
        };
        let sum_info = self.types.sum_type_info.get(sum_name).ok_or_else(|| {
            CodegenError::TypeError(format!("unknown Result sum type: {sum_name}"), None)
        })?;
        let variant = sum_info.variants.get(variant_name).ok_or_else(|| {
            CodegenError::TypeError(
                format!("missing Result variant {variant_name} for {sum_name}"),
                None,
            )
        })?;
        Ok((
            variant.class_index,
            variant.constructor_ref,
            sum_info.interface_class_index,
            variant.fields.clone(),
        ))
    }

    fn nullable_host_jvm_for_inner(&self, inner: &Type) -> Result<JvmType, CodegenError> {
        Ok(match inner {
            Type::Int => JvmType::StructRef(self.builder.refs.long_box_class),
            Type::Float => JvmType::StructRef(self.builder.refs.double_box_class),
            Type::Bool => JvmType::StructRef(self.builder.refs.bool_box_class),
            Type::String => JvmType::StructRef(self.builder.refs.string_class),
            Type::Own(inner) => return self.nullable_host_jvm_for_inner(inner),
            Type::Named(_, _) => match self.type_to_jvm(inner)? {
                JvmType::StructRef(idx) => JvmType::StructRef(idx),
                primitive => {
                    return Err(CodegenError::TypeError(
                        format!("unsupported nullable host return type: {primitive:?}"),
                        None,
                    ))
                }
            },
            other => match self.type_to_jvm(other)? {
                JvmType::StructRef(idx) => JvmType::StructRef(idx),
                primitive => {
                    return Err(CodegenError::TypeError(
                        format!("unsupported nullable host return type: {primitive:?}"),
                        None,
                    ))
                }
            },
        })
    }

    pub(super) fn option_variant_construct_info(
        &self,
        option_type: &Type,
        variant_name: &str,
    ) -> Result<(u16, u16, u16, Vec<VariantField>), CodegenError> {
        let sum_name = match option_type {
            Type::Named(name, _) => name,
            other => {
                return Err(CodegenError::TypeError(
                    format!("expected Option sum type, found {other}"),
                    None,
                ))
            }
        };
        let sum_info = self.types.sum_type_info.get(sum_name).ok_or_else(|| {
            CodegenError::TypeError(format!("unknown Option sum type: {sum_name}"), None)
        })?;
        let variant = sum_info.variants.get(variant_name).ok_or_else(|| {
            CodegenError::TypeError(
                format!("missing Option variant {variant_name} for {sum_name}"),
                None,
            )
        })?;
        Ok((
            variant.class_index,
            variant.constructor_ref,
            sum_info.interface_class_index,
            variant.fields.clone(),
        ))
    }

    pub(super) fn variant_singleton_field_ref(
        &mut self,
        class_index: u16,
    ) -> Result<u16, CodegenError> {
        let desc = self
            .types
            .class_descriptors
            .get(&class_index)
            .cloned()
            .ok_or_else(|| {
                CodegenError::TypeError(
                    format!("missing class descriptor for singleton variant {}", class_index),
                    None,
                )
            })?;
        Ok(self.cp.add_field_ref(class_index, "INSTANCE", &desc)?)
    }

    /// Emit coercion bytecode to convert `actual` type on the stack to `target` type.
    pub(super) fn emit_type_coercion(&mut self, actual: JvmType, target: JvmType) {
        let obj = self.builder.refs.object_class;
        if matches!(target, JvmType::StructRef(idx) if idx == obj)
            && !matches!(actual, JvmType::StructRef(_))
        {
            self.builder.box_if_needed(actual);
        } else if !matches!(target, JvmType::StructRef(_))
            && matches!(actual, JvmType::StructRef(idx) if idx == obj)
        {
            self.builder.unbox_if_needed(target);
        } else if matches!(actual, JvmType::StructRef(idx) if idx == obj)
            && matches!(target, JvmType::StructRef(idx) if idx != obj)
        {
            let cast_class = match target {
                JvmType::StructRef(idx) => idx,
                _ => unreachable!(),
            };
            self.builder.emit(Instruction::Checkcast(cast_class));
            self.builder.frame.pop_type();
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: cast_class,
            });
        }
    }

    /// Reset per-method compilation state.
    pub(super) fn reset_method_state(&mut self) {
        self.builder.reset();
        self.traits.dict_locals.clear();
        self.var_locals.clear();
        self.pre_allocated_slots.clear();
        self.var_types.clear();
        self.join_points.clear();
    }

    pub(super) fn emit_int_const(&mut self, n: i32) -> Result<(), CodegenError> {
        match n {
            0 => self.builder.emit(Instruction::Iconst_0),
            1 => self.builder.emit(Instruction::Iconst_1),
            2 => self.builder.emit(Instruction::Iconst_2),
            3 => self.builder.emit(Instruction::Iconst_3),
            4 => self.builder.emit(Instruction::Iconst_4),
            5 => self.builder.emit(Instruction::Iconst_5),
            _ => {
                let idx = self.cp.add_integer(n)?;
                if idx <= 255 {
                    self.builder.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.builder.emit(Instruction::Ldc_w(idx));
                }
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // IR-driven expression compilation (Steps 2-6)
    // -----------------------------------------------------------------------

    /// Compile an IR Atom (variable reference or literal).
    pub(super) fn compile_ir_atom(
        &mut self,
        atom: &krypton_ir::Atom,
    ) -> Result<JvmType, CodegenError> {
        match atom {
            krypton_ir::Atom::Var(id) => {
                let &(slot, jvm_ty) = self.var_locals.get(id).ok_or_else(|| {
                    CodegenError::UndefinedVariable(
                        format!("ICE: no local for VarId({})", id.0),
                        None,
                    )
                })?;
                self.builder.emit_load(slot, jvm_ty);
                Ok(jvm_ty)
            }
            krypton_ir::Atom::Lit(lit) => self.compile_ir_literal(lit),
        }
    }

    /// Compile an IR Literal.
    pub(super) fn compile_ir_literal(
        &mut self,
        lit: &krypton_ir::Literal,
    ) -> Result<JvmType, CodegenError> {
        match lit {
            krypton_ir::Literal::Int(n) => {
                match *n {
                    0 => self.builder.emit(Instruction::Lconst_0),
                    1 => self.builder.emit(Instruction::Lconst_1),
                    _ => {
                        let idx = self.cp.add_long(*n)?;
                        self.builder.emit(Instruction::Ldc2_w(idx));
                    }
                }
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            krypton_ir::Literal::Float(f) => {
                let idx = self.cp.add_double(*f)?;
                self.builder.emit(Instruction::Ldc2_w(idx));
                self.builder.frame.push_double_type();
                Ok(JvmType::Double)
            }
            krypton_ir::Literal::Bool(b) => {
                self.builder.emit(if *b {
                    Instruction::Iconst_1
                } else {
                    Instruction::Iconst_0
                });
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            krypton_ir::Literal::String(s) => {
                let idx = self.cp.add_string(s)?;
                if idx <= 255 {
                    self.builder.emit(Instruction::Ldc(idx as u8));
                } else {
                    self.builder.emit(Instruction::Ldc_w(idx));
                }
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.string_class,
                });
                Ok(JvmType::StructRef(self.builder.refs.string_class))
            }
            krypton_ir::Literal::Unit => {
                self.builder.emit(Instruction::Iconst_0);
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
        }
    }

    /// Compile an IR PrimOp.
    pub(super) fn compile_ir_primop(
        &mut self,
        op: krypton_ir::PrimOp,
        args: &[krypton_ir::Atom],
    ) -> Result<JvmType, CodegenError> {
        use krypton_ir::PrimOp;
        match op {
            // Integer arithmetic
            PrimOp::AddInt => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Ladd);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            PrimOp::SubInt => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Lsub);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            PrimOp::MulInt => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Lmul);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            PrimOp::DivInt => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Ldiv);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            PrimOp::ModInt => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Lrem);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            PrimOp::NegInt => {
                self.compile_ir_atom(&args[0])?;
                self.builder.emit(Instruction::Lneg);
                Ok(JvmType::Long)
            }
            // Float arithmetic
            PrimOp::AddFloat => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Dadd);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_double_type();
                Ok(JvmType::Double)
            }
            PrimOp::SubFloat => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Dsub);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_double_type();
                Ok(JvmType::Double)
            }
            PrimOp::MulFloat => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Dmul);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_double_type();
                Ok(JvmType::Double)
            }
            PrimOp::DivFloat => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Ddiv);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_double_type();
                Ok(JvmType::Double)
            }
            PrimOp::NegFloat => {
                self.compile_ir_atom(&args[0])?;
                self.builder.emit(Instruction::Dneg);
                Ok(JvmType::Double)
            }
            // Integer comparison (handles both JVM long and int operands)
            PrimOp::EqInt
            | PrimOp::NeqInt
            | PrimOp::LtInt
            | PrimOp::LeInt
            | PrimOp::GtInt
            | PrimOp::GeInt => {
                let lhs_ty = self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;

                // JVM int operands (Bool) use If_icmpXX directly;
                // JVM long operands use Lcmp + IfXX.
                let branch_placeholder = if lhs_ty == JvmType::Int {
                    self.builder.frame.pop_type_n(2); // two ints
                    self.builder.emit_placeholder(match op {
                        PrimOp::EqInt => Instruction::If_icmpne(0),
                        PrimOp::NeqInt => Instruction::If_icmpeq(0),
                        PrimOp::LtInt => Instruction::If_icmpge(0),
                        PrimOp::LeInt => Instruction::If_icmpgt(0),
                        PrimOp::GtInt => Instruction::If_icmple(0),
                        PrimOp::GeInt => Instruction::If_icmplt(0),
                        _ => unreachable!(),
                    })
                } else {
                    self.builder.emit(Instruction::Lcmp);
                    self.builder.frame.pop_type_n(4);
                    self.builder.frame.push_type(VerificationType::Integer);
                    let p = self.builder.emit_placeholder(match op {
                        PrimOp::EqInt => Instruction::Ifne(0),
                        PrimOp::NeqInt => Instruction::Ifeq(0),
                        PrimOp::LtInt => Instruction::Ifge(0),
                        PrimOp::LeInt => Instruction::Ifgt(0),
                        PrimOp::GtInt => Instruction::Ifle(0),
                        PrimOp::GeInt => Instruction::Iflt(0),
                        _ => unreachable!(),
                    });
                    self.builder.frame.pop_type(); // Ifxx consumes the int from Lcmp
                    p
                };

                let stack_at_false = self.builder.frame.stack_types.clone();
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                let goto_placeholder = self.builder.emit_placeholder(Instruction::Goto(0));
                let false_target = self.builder.current_offset();
                self.builder.frame.stack_types = stack_at_false;
                self.builder.frame.record_frame(false_target);
                self.builder.emit(Instruction::Iconst_0);
                self.builder.frame.push_type(VerificationType::Integer);
                let end_target = self.builder.current_offset();
                self.builder.frame.record_frame(end_target);

                if lhs_ty == JvmType::Int {
                    self.builder.patch(
                        branch_placeholder,
                        match op {
                            PrimOp::EqInt => Instruction::If_icmpne(false_target),
                            PrimOp::NeqInt => Instruction::If_icmpeq(false_target),
                            PrimOp::LtInt => Instruction::If_icmpge(false_target),
                            PrimOp::LeInt => Instruction::If_icmpgt(false_target),
                            PrimOp::GtInt => Instruction::If_icmple(false_target),
                            PrimOp::GeInt => Instruction::If_icmplt(false_target),
                            _ => unreachable!(),
                        },
                    );
                } else {
                    self.builder.patch(
                        branch_placeholder,
                        match op {
                            PrimOp::EqInt => Instruction::Ifne(false_target),
                            PrimOp::NeqInt => Instruction::Ifeq(false_target),
                            PrimOp::LtInt => Instruction::Ifge(false_target),
                            PrimOp::LeInt => Instruction::Ifgt(false_target),
                            PrimOp::GtInt => Instruction::Ifle(false_target),
                            PrimOp::GeInt => Instruction::Iflt(false_target),
                            _ => unreachable!(),
                        },
                    );
                }
                self.builder
                    .patch(goto_placeholder, Instruction::Goto(end_target));
                Ok(JvmType::Int)
            }
            // Float comparison
            PrimOp::EqFloat
            | PrimOp::NeqFloat
            | PrimOp::LtFloat
            | PrimOp::LeFloat
            | PrimOp::GtFloat
            | PrimOp::GeFloat => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                let cmp_instr = match op {
                    PrimOp::LtFloat | PrimOp::LeFloat => Instruction::Dcmpl,
                    _ => Instruction::Dcmpl,
                };
                self.builder.emit(cmp_instr);
                self.builder.frame.pop_type_n(4);
                self.builder.frame.push_type(VerificationType::Integer);
                let branch_placeholder = self.builder.emit_placeholder(match op {
                    PrimOp::EqFloat => Instruction::Ifne(0),
                    PrimOp::NeqFloat => Instruction::Ifeq(0),
                    PrimOp::LtFloat => Instruction::Ifge(0),
                    PrimOp::LeFloat => Instruction::Ifgt(0),
                    PrimOp::GtFloat => Instruction::Ifle(0),
                    PrimOp::GeFloat => Instruction::Iflt(0),
                    _ => unreachable!(),
                });
                self.builder.frame.pop_type(); // Ifxx consumes the int
                let stack_at_false = self.builder.frame.stack_types.clone();
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                let goto_placeholder = self.builder.emit_placeholder(Instruction::Goto(0));
                let false_target = self.builder.current_offset();
                self.builder.frame.stack_types = stack_at_false;
                self.builder.frame.record_frame(false_target);
                self.builder.emit(Instruction::Iconst_0);
                self.builder.frame.push_type(VerificationType::Integer);
                let end_target = self.builder.current_offset();
                self.builder.frame.record_frame(end_target);
                self.builder.patch(
                    branch_placeholder,
                    match op {
                        PrimOp::EqFloat => Instruction::Ifne(false_target),
                        PrimOp::NeqFloat => Instruction::Ifeq(false_target),
                        PrimOp::LtFloat => Instruction::Ifge(false_target),
                        PrimOp::LeFloat => Instruction::Ifgt(false_target),
                        PrimOp::GtFloat => Instruction::Ifle(false_target),
                        PrimOp::GeFloat => Instruction::Iflt(false_target),
                        _ => unreachable!(),
                    },
                );
                self.builder
                    .patch(goto_placeholder, Instruction::Goto(end_target));
                Ok(JvmType::Int)
            }
            // Boolean
            PrimOp::And => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Iand);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            PrimOp::Or => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder.emit(Instruction::Ior);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            PrimOp::Not => {
                self.compile_ir_atom(&args[0])?;
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Ixor);
                self.builder.frame.pop_type();
                Ok(JvmType::Int)
            }
            // String
            PrimOp::ConcatString => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder
                    .emit(Instruction::Invokevirtual(self.builder.refs.string_concat));
                self.builder.frame.pop_type();
                Ok(JvmType::StructRef(self.builder.refs.string_class))
            }
            PrimOp::EqString => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder
                    .emit(Instruction::Invokevirtual(self.builder.refs.string_equals));
                self.builder.frame.pop_type();
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            PrimOp::NeqString => {
                self.compile_ir_atom(&args[0])?;
                self.compile_ir_atom(&args[1])?;
                self.builder
                    .emit(Instruction::Invokevirtual(self.builder.refs.string_equals));
                self.builder.frame.pop_type();
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Iconst_1);
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Ixor);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Integer);
                Ok(JvmType::Int)
            }
            // Conversions
            PrimOp::IntToFloat => {
                self.compile_ir_atom(&args[0])?;
                self.builder.emit(Instruction::L2d);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_double_type();
                Ok(JvmType::Double)
            }
            PrimOp::FloatToInt => {
                self.compile_ir_atom(&args[0])?;
                self.builder.emit(Instruction::D2l);
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_long_type();
                Ok(JvmType::Long)
            }
            PrimOp::IntToString => {
                self.compile_ir_atom(&args[0])?;
                self.builder
                    .emit(Instruction::Invokestatic(self.builder.refs.long_to_string));
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.string_class,
                });
                Ok(JvmType::StructRef(self.builder.refs.string_class))
            }
            PrimOp::FloatToString => {
                self.compile_ir_atom(&args[0])?;
                self.builder.emit(Instruction::Invokestatic(
                    self.builder.refs.double_to_string,
                ));
                self.builder.frame.pop_type_n(2);
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.string_class,
                });
                Ok(JvmType::StructRef(self.builder.refs.string_class))
            }
            PrimOp::BoolToString => {
                self.compile_ir_atom(&args[0])?;
                self.builder
                    .emit(Instruction::Invokestatic(self.builder.refs.bool_to_string));
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.string_class,
                });
                Ok(JvmType::StructRef(self.builder.refs.string_class))
            }
        }
    }

    /// Compile an IR SimpleExpr.
    pub(super) fn compile_ir_simple_expr(
        &mut self,
        value: &krypton_ir::SimpleExpr,
        bind_ty: &Type,
        _ir_module: &krypton_ir::Module,
    ) -> Result<JvmType, CodegenError> {
        match &value.kind {
            SimpleExprKind::Atom(atom) => self.compile_ir_atom(atom),

            SimpleExprKind::PrimOp { op, args } => self.compile_ir_primop(*op, args),

            SimpleExprKind::Call { func, args } => {
                let name = self
                    .fn_names
                    .get(func)
                    .ok_or_else(|| {
                        CodegenError::UndefinedVariable(
                            format!("ICE: no name for FnId({})", func.0),
                            None,
                        )
                    })?
                    .clone();

                // Intrinsics
                if name == "panic" {
                    let re_class = self.builder.refs.runtime_exception_class;
                    let re_init = self.builder.refs.runtime_exception_init;
                    self.builder.emit_new_dup(re_class);
                    self.compile_ir_atom(&args[0])?;
                    self.builder.emit(Instruction::Invokespecial(re_init));
                    self.builder.frame.pop_type();
                    self.builder.frame.pop_type();
                    self.builder.frame.pop_type();
                    self.builder.emit(Instruction::Athrow);
                    // Record a frame for dead code after athrow so the verifier
                    // can process any subsequent dead instructions (e.g. Switch goto).
                    self.builder.frame.stack_types.clear();
                    let jvm_ret = self.type_to_jvm(bind_ty)?;
                    self.builder.push_jvm_type(jvm_ret);
                    let after_athrow = self.builder.code.len() as u16;
                    self.builder.frame.record_frame(after_athrow);
                    return Ok(jvm_ret);
                }
                // Struct constructor
                if let Some(si) = self.types.struct_info.get(&name) {
                    let class_index = si.class_index;
                    let constructor_ref = si.constructor_ref;
                    let fields = si.fields.clone();
                    let result_type = JvmType::StructRef(class_index);
                    self.builder.emit_new_dup(class_index);
                    for arg in args {
                        self.compile_ir_atom(arg)?;
                    }
                    for (_, ft) in &fields {
                        self.builder.pop_jvm_type(*ft);
                    }
                    self.builder.frame.pop_type();
                    self.builder.frame.pop_type();
                    self.builder
                        .emit(Instruction::Invokespecial(constructor_ref));
                    self.builder.push_jvm_type(result_type);
                    return Ok(result_type);
                }

                // Variant constructor
                if self.types.variant_to_sum.contains_key(&name) {
                    let (class_idx, ctor_ref, iface_idx, fields) =
                        self.variant_construct_info(&name)?;
                    self.builder.emit_new_dup(class_idx);
                    for (i, arg) in args.iter().enumerate() {
                        let arg_type = self.compile_ir_atom(arg)?;
                        if fields[i].is_erased {
                            self.builder.box_if_needed(arg_type);
                        }
                    }
                    let result_type = self.emit_variant_invokespecial(ctor_ref, &fields, iface_idx);
                    return Ok(result_type);
                }

                // Static call (user-defined function)
                // The IR already includes dict args at the front of the args list,
                // so we just compile all args in order — no need for emit_dict_argument_for_type.
                let info = self
                    .types
                    .get_function(&name)
                    .ok_or_else(|| CodegenError::UndefinedVariable(name.clone(), None))?;
                let param_types = info.param_types.clone();
                let return_type = info.return_type;
                let is_void = info.is_void;
                let method_ref = info.method_ref;

                for (i, arg) in args.iter().enumerate() {
                    let arg_type = self.compile_ir_atom(arg)?;
                    let expected = param_types[i];
                    if let JvmType::StructRef(idx) = expected {
                        if idx == self.builder.refs.object_class
                            && !matches!(arg_type, JvmType::StructRef(_))
                        {
                            self.builder.box_if_needed(arg_type);
                        } else if idx != self.builder.refs.object_class {
                            if let JvmType::StructRef(arg_idx) = arg_type {
                                if arg_idx == self.builder.refs.object_class && arg_idx != idx {
                                    self.builder.emit(Instruction::Checkcast(idx));
                                    self.builder.frame.pop_type();
                                    self.builder
                                        .frame
                                        .push_type(VerificationType::Object { cpool_index: idx });
                                }
                            }
                        }
                    }
                }

                for pt in param_types.iter().rev() {
                    self.builder.pop_jvm_type(*pt);
                }
                self.builder.emit(Instruction::Invokestatic(method_ref));
                if is_void {
                    self.builder.emit(Instruction::Iconst_0);
                    self.builder.frame.push_type(VerificationType::Integer);
                    Ok(JvmType::Int)
                } else {
                    self.builder.push_jvm_type(return_type);
                    Ok(return_type)
                }
            }

            SimpleExprKind::TraitCall {
                trait_name,
                method_name,
                args,
            } => {
                if let Some(dispatch) = self.traits.trait_dispatch.get(trait_name) {
                    let iface_method_ref = dispatch.method_refs[method_name];
                    let iface_class = dispatch.interface_class;

                    // args[0] is the dict, args[1..] are user args
                    // Compile dict arg — cast to the trait interface
                    let dict_jvm = self.compile_ir_atom(&args[0])?;
                    if let JvmType::StructRef(idx) = dict_jvm {
                        if idx != iface_class {
                            self.builder.emit(Instruction::Checkcast(iface_class));
                            self.builder.frame.pop_type();
                            self.builder.frame.push_type(VerificationType::Object {
                                cpool_index: iface_class,
                            });
                        }
                    }

                    // Compile user args (skip dict at args[0])
                    let user_args = &args[1..];
                    for arg in user_args {
                        let arg_type = self.compile_ir_atom(arg)?;
                        self.builder.box_if_needed(arg_type);
                    }
                    // invokeinterface: receiver + user_args
                    self.builder.emit(Instruction::Invokeinterface(
                        iface_method_ref,
                        (user_args.len() + 1) as u8,
                    ));
                    for _ in user_args {
                        self.builder.frame.pop_type();
                    }
                    self.builder.frame.pop_type(); // receiver (dict)
                    let expected_ret = self.type_to_jvm(bind_ty)?;
                    self.coerce_interface_return(expected_ret);
                    Ok(expected_ret)
                } else {
                    Err(CodegenError::UnsupportedExpr(
                        format!("no dispatch info for trait {trait_name}.{method_name}"),
                        None,
                    ))
                }
            }

            SimpleExprKind::CallClosure { closure, args } => {
                // Determine arity from closure type
                let closure_ty = match closure {
                    krypton_ir::Atom::Var(var_id) => {
                        self.var_types.get(var_id).cloned().ok_or_else(|| {
                            CodegenError::TypeError(
                                format!("CallClosure: var {:?} has no type", var_id),
                                None,
                            )
                        })?
                    }
                    _ => {
                        return Err(CodegenError::TypeError(
                            "CallClosure: closure must be a Var atom".to_string(),
                            None,
                        ))
                    }
                };
                let fn_type = match &closure_ty {
                    Type::Own(inner) => inner.as_ref().clone(),
                    other => other.clone(),
                };
                let (arity, ret_ty) = match &fn_type {
                    Type::Fn(params, ret) => (params.len() as u8, ret.as_ref().clone()),
                    _ => {
                        return Err(CodegenError::TypeError(
                            format!("closure call on non-function type: {fn_type:?}"),
                            None,
                        ))
                    }
                };
                let ret_jvm = self.type_to_jvm(&ret_ty)?;

                self.lambda.ensure_fun_interface(
                    arity,
                    &mut self.cp,
                    &mut self.types.class_descriptors,
                )?;
                let fun_class = self.lambda.fun_classes[&arity];
                let apply_ref = self.lambda.fun_apply_refs[&arity];

                let callee_jvm = self.compile_ir_atom(closure)?;
                if let JvmType::StructRef(idx) = callee_jvm {
                    if idx != fun_class {
                        self.builder.emit(Instruction::Checkcast(fun_class));
                        self.builder.frame.pop_type();
                        self.builder.frame.push_type(VerificationType::Object {
                            cpool_index: fun_class,
                        });
                    }
                }

                for arg in args {
                    let arg_type = self.compile_ir_atom(arg)?;
                    self.builder.box_if_needed(arg_type);
                }

                self.builder
                    .emit(Instruction::Invokeinterface(apply_ref, arity + 1));
                for _ in 0..arity {
                    self.builder.frame.pop_type();
                }
                self.builder.pop_jvm_type(JvmType::StructRef(fun_class));

                self.coerce_interface_return(ret_jvm);
                Ok(ret_jvm)
            }

            SimpleExprKind::MakeClosure { func, captures } => {
                let func_name = self
                    .fn_names
                    .get(func)
                    .ok_or_else(|| {
                        CodegenError::UndefinedVariable(
                            format!("ICE: no name for FnId({})", func.0),
                            None,
                        )
                    })?
                    .clone();

                // Get the closure type from bind_ty
                let fn_type = match bind_ty {
                    Type::Own(inner) => inner.as_ref().clone(),
                    other => other.clone(),
                };
                let (param_types_tc, ret_ty) = match &fn_type {
                    Type::Fn(params, ret) => (params.clone(), ret.as_ref().clone()),
                    _ => {
                        return Err(CodegenError::TypeError(
                            format!("MakeClosure bind type is not Fn: {fn_type:?}"),
                            None,
                        ))
                    }
                };
                let param_jvm_types: Vec<JvmType> = param_types_tc
                    .iter()
                    .map(|t| self.type_to_jvm(t))
                    .collect::<Result<_, _>>()?;
                let ret_jvm = self.type_to_jvm(&ret_ty)?;
                let arity = param_jvm_types.len() as u8;

                self.lambda.ensure_fun_interface(
                    arity,
                    &mut self.cp,
                    &mut self.types.class_descriptors,
                )?;
                let fun_class_idx = self.lambda.fun_classes[&arity];

                // Dict captures are now handled in the IR (lower_constrained_fn_as_value),
                // so captures already includes any needed dict atoms.
                let capture_count = captures.len();

                // Build bridge method
                let bridge_name = format!("lambda${}", self.lambda.lambda_counter);
                self.lambda.lambda_counter += 1;
                let mut bridge_desc = String::from("(");
                for _ in 0..capture_count {
                    bridge_desc.push_str("Ljava/lang/Object;");
                }
                for _ in &param_jvm_types {
                    bridge_desc.push_str("Ljava/lang/Object;");
                }
                bridge_desc.push_str(")Ljava/lang/Object;");

                let saved_dict_locals = self.traits.dict_locals.clone();
                let scope = self.push_method_scope();

                // Set up bridge locals: captures (including dict captures) + params
                self.builder.next_local = (capture_count + param_jvm_types.len()) as u16;
                for _ in 0..capture_count {
                    self.builder
                        .frame
                        .local_types
                        .push(VerificationType::Object {
                            cpool_index: self.builder.refs.object_class,
                        });
                }
                for _ in &param_jvm_types {
                    self.builder
                        .frame
                        .local_types
                        .push(VerificationType::Object {
                            cpool_index: self.builder.refs.object_class,
                        });
                }

                // Check if the target function exists
                if let Some(info) = self.types.get_function(&func_name) {
                    let target_param_types = info.param_types.clone();
                    let target_return_type = info.return_type;
                    let target_is_void = info.is_void;
                    let target_method_ref = info.method_ref;

                    // Load capture args with proper unboxing to match target param types
                    let mut bridge_slot = 0u16;
                    for &capture_target_type in target_param_types.iter().take(capture_count) {
                        self.load_bridge_arg(bridge_slot, capture_target_type);
                        bridge_slot += 1;
                    }

                    // Load and unbox/cast user params
                    for (i, actual_type) in param_jvm_types.iter().copied().enumerate() {
                        self.load_bridge_arg(bridge_slot, actual_type);
                        let expected_type = target_param_types[capture_count + i];
                        if let JvmType::StructRef(idx) = expected_type {
                            if idx == self.builder.refs.object_class
                                && !matches!(actual_type, JvmType::StructRef(_))
                            {
                                self.builder.box_if_needed(actual_type);
                            }
                        }
                        bridge_slot += 1;
                    }

                    self.builder
                        .emit(Instruction::Invokestatic(target_method_ref));
                    for actual_type in target_param_types.iter().rev().copied() {
                        self.builder.pop_jvm_type(actual_type);
                    }
                    if target_is_void {
                        self.builder.emit(Instruction::Iconst_0);
                        self.builder.frame.push_type(VerificationType::Integer);
                    } else {
                        self.builder.push_jvm_type(target_return_type);
                        match ret_jvm {
                            JvmType::Long | JvmType::Double | JvmType::Int if matches!(target_return_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class) =>
                            {
                                self.builder.unbox_if_needed(ret_jvm);
                            }
                            JvmType::StructRef(idx)
                                if idx != self.builder.refs.object_class
                                    && matches!(target_return_type, JvmType::StructRef(ret_idx) if ret_idx == self.builder.refs.object_class) =>
                            {
                                self.builder.emit(Instruction::Checkcast(idx));
                                self.builder.frame.pop_type();
                                self.builder
                                    .frame
                                    .push_type(VerificationType::Object { cpool_index: idx });
                            }
                            _ => {}
                        }
                    }
                } else if let Some(si) = self.types.struct_info.get(&func_name) {
                    let class_index = si.class_index;
                    let constructor_ref = si.constructor_ref;
                    let field_types: Vec<JvmType> = si.fields.iter().map(|(_, ty)| *ty).collect();
                    self.builder.emit_new_dup(class_index);
                    for (i, actual_type) in field_types.iter().copied().enumerate() {
                        self.load_bridge_arg((capture_count + i) as u16, actual_type);
                    }
                    self.builder
                        .emit(Instruction::Invokespecial(constructor_ref));
                    for actual_type in field_types.iter().rev().copied() {
                        self.builder.pop_jvm_type(actual_type);
                    }
                    self.builder.frame.pop_type();
                    self.builder.frame.pop_type();
                    self.builder.push_jvm_type(JvmType::StructRef(class_index));
                } else if self.types.variant_to_sum.contains_key(&func_name) {
                    let (class_idx, ctor_ref, iface_idx, fields) =
                        self.variant_construct_info(&func_name)?;
                    self.builder.emit_new_dup(class_idx);
                    for (i, (f, actual_type)) in fields
                        .iter()
                        .zip(param_jvm_types.iter().copied())
                        .enumerate()
                    {
                        self.load_bridge_arg((capture_count + i) as u16, actual_type);
                        if f.is_erased {
                            self.builder.box_if_needed(actual_type);
                        }
                    }
                    self.emit_variant_invokespecial(ctor_ref, &fields, iface_idx);
                } else {
                    return Err(CodegenError::UndefinedVariable(func_name, None));
                }

                let bridge_result = self.builder.box_if_needed(ret_jvm);
                debug_assert!(matches!(bridge_result, JvmType::StructRef(_)));
                self.builder.emit(Instruction::Areturn);

                let bridge_name_idx = self.cp.add_utf8(&bridge_name)?;
                let bridge_desc_idx = self.cp.add_utf8(&bridge_desc)?;
                self.lambda.lambda_methods.push(Method {
                    access_flags: MethodAccessFlags::PRIVATE
                        | MethodAccessFlags::STATIC
                        | MethodAccessFlags::SYNTHETIC,
                    name_index: bridge_name_idx,
                    descriptor_index: bridge_desc_idx,
                    attributes: vec![self.builder.finish_method()],
                });

                self.pop_method_scope(scope);
                self.traits.dict_locals = saved_dict_locals;

                // Push captures onto stack
                for capture in captures {
                    let cap_type = self.compile_ir_atom(capture)?;
                    self.builder.box_if_needed(cap_type);
                }

                self.emit_fun_reference_indy(
                    arity,
                    &bridge_name,
                    &bridge_desc,
                    fun_class_idx,
                    capture_count,
                )
            }

            SimpleExprKind::Construct { type_ref, fields } => {
                let type_name = type_ref.symbol.local_name();
                let si = self.types.struct_info.get(&type_name).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown struct: {type_name}"), None)
                })?;
                let class_index = si.class_index;
                let constructor_ref = si.constructor_ref;
                let field_types: Vec<JvmType> = si.fields.iter().map(|(_, t)| *t).collect();
                let result_type = JvmType::StructRef(class_index);
                self.builder.emit_new_dup(class_index);
                for (i, atom) in fields.iter().enumerate() {
                    let arg_type = self.compile_ir_atom(atom)?;
                    if field_types[i].is_reference() && !arg_type.is_reference() {
                        self.builder.box_if_needed(arg_type);
                    }
                }
                for ft in field_types.iter().rev() {
                    self.builder.pop_jvm_type(*ft);
                }
                self.builder.frame.pop_type();
                self.builder.frame.pop_type();
                self.builder
                    .emit(Instruction::Invokespecial(constructor_ref));
                self.builder.push_jvm_type(result_type);
                Ok(result_type)
            }

            SimpleExprKind::ConstructVariant {
                type_ref: _,
                variant,
                tag: _,
                fields,
            } => {
                let (class_idx, ctor_ref, iface_idx, variant_fields) =
                    self.variant_construct_info(variant)?;
                self.builder.emit_new_dup(class_idx);
                for (i, atom) in fields.iter().enumerate() {
                    let arg_type = self.compile_ir_atom(atom)?;
                    if variant_fields[i].is_erased {
                        self.builder.box_if_needed(arg_type);
                    }
                }
                Ok(self.emit_variant_invokespecial(ctor_ref, &variant_fields, iface_idx))
            }

            SimpleExprKind::Project { value, field_index } => {
                let val_type = self.compile_ir_atom(value)?;
                // Look up struct name from var_types
                let struct_name = match value {
                    krypton_ir::Atom::Var(var_id) => match self.var_types.get(var_id) {
                        Some(Type::Named(name, _)) => name.clone(),
                        Some(Type::Own(inner)) => match inner.as_ref() {
                            Type::Named(name, _) => name.clone(),
                            _ => {
                                return Err(CodegenError::TypeError(
                                    "Project on non-struct type".to_string(),
                                    None,
                                ))
                            }
                        },
                        _ => {
                            return Err(CodegenError::TypeError(
                                "Project on non-struct type".to_string(),
                                None,
                            ))
                        }
                    },
                    _ => {
                        return Err(CodegenError::TypeError(
                            "Project on literal".to_string(),
                            None,
                        ))
                    }
                };
                let si = self.types.struct_info.get(&struct_name).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown struct: {struct_name}"), None)
                })?;
                let (field_name, field_jvm_type) = &si.fields[*field_index];
                let accessor_ref = si.accessor_refs[field_name];
                let field_jvm_type = *field_jvm_type;

                self.builder.pop_jvm_type(val_type);
                self.builder.emit(Instruction::Invokevirtual(accessor_ref));
                self.builder.push_jvm_type(field_jvm_type);

                // Coerce Object→bind_ty if needed
                let expected = self.type_to_jvm(bind_ty)?;
                if matches!(field_jvm_type, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
                    && !matches!(expected, JvmType::StructRef(idx) if idx == self.builder.refs.object_class)
                {
                    self.builder.unbox_if_needed(expected);
                    return Ok(expected);
                }
                Ok(field_jvm_type)
            }

            SimpleExprKind::Tag { .. } => {
                panic!("ICE: Tag should never be emitted by lowering");
            }

            SimpleExprKind::MakeTuple { elements } => {
                let arity = elements.len();
                let info = self.types.tuple_info.get(&arity).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown tuple arity: {arity}"), None)
                })?;
                let class_index = info.class_index;
                let constructor_ref = info.constructor_ref;
                self.builder.emit_new_dup(class_index);
                for atom in elements {
                    let elem_type = self.compile_ir_atom(atom)?;
                    self.builder.box_if_needed(elem_type);
                }
                for _ in 0..arity {
                    self.builder.frame.pop_type();
                }
                self.builder.frame.pop_type();
                self.builder.frame.pop_type();
                self.builder
                    .emit(Instruction::Invokespecial(constructor_ref));
                let result_type = JvmType::StructRef(class_index);
                self.builder.push_jvm_type(result_type);
                Ok(result_type)
            }

            SimpleExprKind::TupleProject { value, index } => {
                self.compile_ir_atom(value)?;
                // Determine arity from var_types
                let arity = match value {
                    krypton_ir::Atom::Var(var_id) => match self.var_types.get(var_id) {
                        Some(Type::Tuple(elems)) => elems.len(),
                        _ => {
                            return Err(CodegenError::TypeError(
                                "TupleProject on non-tuple type".to_string(),
                                None,
                            ))
                        }
                    },
                    _ => {
                        return Err(CodegenError::TypeError(
                            "TupleProject on literal".to_string(),
                            None,
                        ))
                    }
                };
                let info = self.types.tuple_info.get(&arity).ok_or_else(|| {
                    CodegenError::TypeError(format!("unknown tuple arity: {arity}"), None)
                })?;
                let field_ref = info.field_refs[*index];
                let tuple_class = info.class_index;

                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: tuple_class,
                });
                self.builder.emit(Instruction::Invokevirtual(field_ref));
                self.builder.frame.pop_type();
                self.builder.frame.push_type(VerificationType::Object {
                    cpool_index: self.builder.refs.object_class,
                });

                // Coerce from Object to expected type
                let expected = self.type_to_jvm(bind_ty)?;
                match expected {
                    JvmType::StructRef(idx) if idx != self.builder.refs.object_class => {
                        self.builder.emit(Instruction::Checkcast(idx));
                        self.builder.frame.pop_type();
                        self.builder
                            .frame
                            .push_type(VerificationType::Object { cpool_index: idx });
                    }
                    JvmType::Long | JvmType::Double | JvmType::Int => {
                        self.builder.unbox_if_needed(expected);
                    }
                    _ => {}
                }
                Ok(expected)
            }

            SimpleExprKind::GetDict { instance_ref: _, trait_name, ty } => {
                let pushed_class = self
                    .traits
                    .trait_dispatch
                    .get(trait_name)
                    .map(|d| d.interface_class)
                    .unwrap_or(self.builder.refs.object_class);
                self.emit_dict_argument_for_type(trait_name, ty, pushed_class)?;
                Ok(JvmType::StructRef(pushed_class))
            }

            SimpleExprKind::MakeDict {
                instance_ref: _,
                trait_name,
                ty,
                sub_dicts,
            } => {
                let pushed_class = self
                    .traits
                    .trait_dispatch
                    .get(trait_name)
                    .map(|d| d.interface_class)
                    .unwrap_or(self.builder.refs.object_class);

                if let Some(instance_info) = self
                    .traits
                    .parameterized_instances
                    .get(trait_name)
                    .and_then(|instances| {
                        instances.iter().find(|inst| {
                            let mut bindings = HashMap::new();
                            bind_type_vars(&inst.target_type, ty, &mut bindings)
                        })
                    })
                    .cloned()
                {
                    let inst_class = self.cp.add_class(&instance_info.class_name)?;
                    self.types
                        .class_descriptors
                        .insert(inst_class, format!("L{};", instance_info.class_name));
                    let mut init_desc = String::from("(");
                    for _ in &instance_info.requirements {
                        init_desc.push_str("Ljava/lang/Object;");
                    }
                    init_desc.push_str(")V");
                    let init_ref = self.cp.add_method_ref(inst_class, "<init>", &init_desc)?;
                    self.builder.emit(Instruction::New(inst_class));
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: inst_class,
                    });
                    self.builder.emit(Instruction::Dup);
                    self.builder.frame.push_type(VerificationType::Object {
                        cpool_index: inst_class,
                    });
                    for sub_dict in sub_dicts {
                        self.compile_ir_atom(sub_dict)?;
                    }
                    self.builder.emit(Instruction::Invokespecial(init_ref));
                    for _ in sub_dicts {
                        self.builder.frame.pop_type();
                    }
                    self.builder.frame.pop_type();
                    Ok(JvmType::StructRef(pushed_class))
                } else {
                    // Two-phase dict resolution: try parameterized instance first, then
                    // fall back to emit_dict_argument_for_type for structural matching
                    self.emit_dict_argument_for_type(trait_name, ty, pushed_class)?;
                    Ok(JvmType::StructRef(pushed_class))
                }
            }

            SimpleExprKind::MakeVec {
                element_type: _,
                elements,
            } => {
                let vec_class = self
                    .types
                    .struct_info
                    .get("Vec")
                    .ok_or_else(|| {
                        CodegenError::TypeError(
                            "ICE: Vec not in struct_info".to_string(),
                            None,
                        )
                    })?
                    .class_index;
                let info = self
                    .vec_info
                    .as_ref()
                    .ok_or_else(|| {
                        CodegenError::TypeError("Vec info not registered".to_string(), None)
                    })?
                    .clone();
                let arr_vtype = VerificationType::Object {
                    cpool_index: vec_class,
                };

                let new_offset = self.builder.current_offset();
                self.builder.emit(Instruction::New(vec_class));
                self.builder
                    .frame
                    .push_type(VerificationType::Uninitialized { offset: new_offset });
                self.builder.emit(Instruction::Dup);
                self.builder
                    .frame
                    .push_type(VerificationType::Uninitialized { offset: new_offset });
                self.emit_int_const(elements.len() as i32)?;
                self.builder.frame.push_type(VerificationType::Integer);
                self.builder.emit(Instruction::Invokespecial(info.init_ref));
                self.builder.frame.pop_type();
                self.builder.frame.pop_type();
                self.builder.frame.pop_type();
                self.builder.frame.push_type(arr_vtype.clone());

                for (i, elem) in elements.iter().enumerate() {
                    self.builder.emit(Instruction::Dup);
                    self.builder.frame.push_type(arr_vtype.clone());
                    self.emit_int_const(i as i32)?;
                    self.builder.frame.push_type(VerificationType::Integer);
                    let elem_type = self.compile_ir_atom(elem)?;
                    self.builder.box_if_needed(elem_type);
                    self.builder.emit(Instruction::Invokevirtual(info.set_ref));
                    self.builder.frame.pop_type();
                    self.builder.frame.pop_type();
                    self.builder.frame.pop_type();
                }

                self.builder.emit(Instruction::Dup);
                self.builder.frame.push_type(arr_vtype);
                self.builder
                    .emit(Instruction::Invokevirtual(info.freeze_ref));
                self.builder.frame.pop_type();

                Ok(JvmType::StructRef(vec_class))
            }

        }
    }

    /// Compile an IR Expr (ExprKind).
    pub(super) fn compile_ir_expr(
        &mut self,
        expr: &krypton_ir::Expr,
        ir_module: &krypton_ir::Module,
    ) -> Result<JvmType, CodegenError> {
        match &expr.kind {
            krypton_ir::ExprKind::Atom(atom) => self.compile_ir_atom(atom),

            krypton_ir::ExprKind::Let {
                bind,
                ty,
                value,
                body,
            } => {
                let jvm_ty = self.type_to_jvm(ty)?;
                let val_type = self.compile_ir_simple_expr(value, ty, ir_module)?;

                // Coerce if needed (actual=val_type → target=jvm_ty)
                self.emit_type_coercion(val_type, jvm_ty);

                // Use pre-allocated slot if one exists (resource vars null-initialized
                // at function entry for JVM verifier compatibility in finally handlers).
                // The slot mapping is kept (not removed) so the function-wide finally
                // handler can still find block-scoped resources whose `var_locals`
                // entries were rolled back by branch restoration.
                let slot = if let Some(&existing_slot) = self.pre_allocated_slots.get(bind) {
                    self.builder.emit_store(existing_slot, jvm_ty);
                    existing_slot
                } else {
                    let slot = self.builder.alloc_anonymous_local(jvm_ty);
                    self.builder.emit_store(slot, jvm_ty);
                    slot
                };
                self.var_locals.insert(*bind, (slot, jvm_ty));
                self.var_types.insert(*bind, ty.clone());

                // If the value is function-typed, register in local_fn_info for higher-order calls
                let fn_type = match ty {
                    Type::Own(inner) => inner.as_ref(),
                    other => other,
                };
                if let Type::Fn(inner_params, inner_ret) = fn_type {
                    let inner_param_jvm: Vec<JvmType> = inner_params
                        .iter()
                        .map(|t| self.type_to_jvm(t))
                        .collect::<Result<_, _>>()?;
                    let inner_ret_jvm = self.type_to_jvm(inner_ret)?;
                    let arity = inner_params.len() as u8;
                    self.lambda.ensure_fun_interface(
                        arity,
                        &mut self.cp,
                        &mut self.types.class_descriptors,
                    )?;
                    // Use a synthetic name for the local_fn_info
                    let var_name = format!("__ir_var_{}", bind.0);
                    self.builder.locals.insert(var_name.clone(), (slot, jvm_ty));
                    self.builder
                        .local_fn_info
                        .insert(var_name, (inner_param_jvm, inner_ret_jvm));
                }

                self.compile_ir_expr(body, ir_module)
            }

            krypton_ir::ExprKind::LetRec { bindings, body } => {
                // First pass: allocate locals for all bindings
                for (var_id, ty, _fn_id, _captures) in bindings {
                    let jvm_ty = self.type_to_jvm(ty)?;
                    let slot = self.builder.alloc_anonymous_local(jvm_ty);
                    self.var_locals.insert(*var_id, (slot, jvm_ty));
                    self.var_types.insert(*var_id, ty.clone());
                }
                // Second pass: compile MakeClosure for each and store
                for (var_id, ty, fn_id, captures) in bindings {
                    let make_closure = krypton_ir::SimpleExpr::new(
                        (0, 0),
                        SimpleExprKind::MakeClosure {
                            func: *fn_id,
                            captures: captures.clone(),
                        },
                    );
                    let val_type = self.compile_ir_simple_expr(&make_closure, ty, ir_module)?;
                    let &(slot, jvm_ty) = self.var_locals.get(var_id).unwrap();
                    // Coerce if needed
                    if jvm_ty != val_type
                        && matches!(jvm_ty, JvmType::StructRef(_))
                        && !val_type.is_reference()
                    {
                        self.builder.box_if_needed(val_type);
                    }
                    self.builder.emit_store(slot, jvm_ty);
                }
                self.compile_ir_expr(body, ir_module)
            }

            krypton_ir::ExprKind::LetJoin {
                name,
                params,
                join_body,
                body,
                is_recur,
            } => {
                if *is_recur {
                    // Recur loop: allocate param slots, compile body first (initial jump),
                    // then set recur target and compile join_body.
                    let mut param_slots = Vec::new();
                    for (var_id, ty) in params {
                        let jvm_ty = self.type_to_jvm(ty)?;
                        let slot = self.builder.alloc_anonymous_local(jvm_ty);
                        param_slots.push((slot, jvm_ty));
                        self.var_types.insert(*var_id, ty.clone());
                    }

                    // Register join point with forward reference (body's Jump will be patched)
                    self.join_points.insert(
                        *name,
                        JoinPointInfo {
                            target_offset: 0,
                            param_slots: param_slots.clone(),
                            frame_locals: self.builder.frame.local_types.clone(),
                            forward_jumps: Vec::new(),
                        },
                    );

                    // Compile body (contains initial `jump loop(args)` — forward ref)
                    let _body_type = self.compile_ir_expr(body, ir_module)?;

                    // Set recur target here (where join_body starts).
                    // No Nop — recur_target overwrites the Jump handler's dead-code frame.
                    let recur_target = self.builder.code.len() as u16;
                    self.builder.recur_target = recur_target;
                    self.builder.fn_params = param_slots.clone();
                    self.builder.recur_frame_locals = self.builder.frame.local_types.clone();

                    // Update join point with actual target (for back-edge jumps from join_body)
                    if let Some(jp) = self.join_points.get_mut(name) {
                        jp.target_offset = recur_target;
                        jp.frame_locals = self.builder.recur_frame_locals.clone();
                        for &jump_idx in &jp.forward_jumps.clone() {
                            self.builder
                                .patch(jump_idx, Instruction::Goto(recur_target));
                        }
                    }

                    // Add params to var_locals (visible in join_body)
                    for (i, (var_id, _ty)) in params.iter().enumerate() {
                        let (slot, jvm_ty) = param_slots[i];
                        self.var_locals.insert(*var_id, (slot, jvm_ty));
                    }

                    // Record frame at join_body start (clear stale stack from body's Jump)
                    self.builder.frame.stack_types.clear();
                    self.builder.frame.record_frame(recur_target);

                    // Compile join_body (jumps are back-edges with target_offset != 0)
                    self.compile_ir_expr(join_body, ir_module)
                } else {
                    // Forward join point
                    let mut param_slots = Vec::new();
                    // Save local_types BEFORE pushing Top placeholders
                    let pre_top_local_types = self.builder.frame.local_types.clone();

                    for (var_id, ty) in params {
                        let jvm_ty = self.type_to_jvm(ty)?;
                        let slot = self.builder.next_local;
                        let slot_size: u16 = match jvm_ty {
                            JvmType::Long | JvmType::Double => 2,
                            _ => 1,
                        };
                        // Keep Top pushes to maintain local_types/next_local sync
                        for _ in 0..slot_size {
                            self.builder.frame.local_types.push(VerificationType::Top);
                        }
                        self.builder.next_local += slot_size;
                        param_slots.push((slot, jvm_ty));
                        self.var_types.insert(*var_id, ty.clone());
                    }

                    let saved_locals = self.builder.locals.clone();
                    let saved_local_types = self.builder.frame.local_types.clone();
                    let saved_next_local = self.builder.next_local;

                    // Build join frame with actual param types (not Top)
                    let mut join_frame_locals = pre_top_local_types;
                    for &(_slot, jvm_ty) in &param_slots {
                        let vtypes = self.builder.jvm_type_to_vtypes(jvm_ty);
                        join_frame_locals.extend(vtypes);
                    }

                    self.join_points.insert(
                        *name,
                        JoinPointInfo {
                            target_offset: 0,
                            param_slots: param_slots.clone(),
                            frame_locals: join_frame_locals.clone(),
                            forward_jumps: Vec::new(),
                        },
                    );

                    // Compile body (which contains Jump to this join point)
                    let body_type = self.compile_ir_expr(body, ir_module)?;

                    // Skip over join_body
                    let skip_goto = self.builder.emit_placeholder(Instruction::Goto(0));

                    // Join body starts here
                    let join_start = self.builder.current_offset();
                    // Update the join point target
                    if let Some(jp) = self.join_points.get_mut(name) {
                        jp.target_offset = join_start;
                    }

                    // Restore frame state for join_body
                    self.builder.max_locals_hwm =
                        self.builder.max_locals_hwm.max(self.builder.next_local);
                    self.builder.frame.stack_types.clear();
                    self.builder.frame.local_types = join_frame_locals.clone();
                    self.builder.next_local = saved_next_local;
                    self.builder.locals = saved_locals.clone();

                    // Add params to var_locals (visible in join_body)
                    for (i, (var_id, _ty)) in params.iter().enumerate() {
                        let (slot, jvm_ty) = param_slots[i];
                        self.var_locals.insert(*var_id, (slot, jvm_ty));
                    }
                    self.builder.frame.record_frame(join_start);

                    let join_type = self.compile_ir_expr(join_body, ir_module)?;

                    let after = self.builder.current_offset();

                    // Patch skip goto
                    self.builder.patch(skip_goto, Instruction::Goto(after));

                    // Patch forward jumps
                    if let Some(jp) = self.join_points.get(name) {
                        for &jump_idx in &jp.forward_jumps {
                            self.builder.patch(jump_idx, Instruction::Goto(join_start));
                        }
                    }

                    // Record merge frame — use saved state (Top in param positions)
                    // Both paths (skip_goto with Top, join_body with actual types) are valid
                    // since everything is assignable to Top.
                    self.builder.max_locals_hwm =
                        self.builder.max_locals_hwm.max(self.builder.next_local);
                    self.builder.frame.stack_types.clear();
                    self.builder.frame.local_types = saved_local_types;
                    self.builder.next_local = saved_next_local;
                    self.builder.locals = saved_locals;
                    let result_type = body_type;
                    self.builder.push_jvm_type(result_type);
                    self.builder.frame.record_frame(after);

                    let _ = join_type;
                    Ok(result_type)
                }
            }

            krypton_ir::ExprKind::AutoClose {
                resource,
                dict,
                type_name,
                null_slot,
                body,
            } => self.compile_auto_close(*resource, dict, type_name, *null_slot, body, ir_module),

            krypton_ir::ExprKind::Jump { target, args } => {
                let jp = self.join_points.get(target).ok_or_else(|| {
                    CodegenError::UndefinedVariable(
                        format!("ICE: no join point for VarId({})", target.0),
                        None,
                    )
                })?;
                let param_slots = jp.param_slots.clone();
                let target_offset = jp.target_offset;
                let frame_locals = jp.frame_locals.clone();

                // Compile args and store into param slots, converting types if needed
                for (i, arg) in args.iter().enumerate() {
                    let arg_type = self.compile_ir_atom(arg)?;
                    let (slot, jvm_ty) = param_slots[i];
                    if arg_type != jvm_ty {
                        if matches!(jvm_ty, JvmType::StructRef(_))
                            && !matches!(arg_type, JvmType::StructRef(_))
                        {
                            // Primitive → Object: box
                            self.builder.box_if_needed(arg_type);
                        } else if !matches!(jvm_ty, JvmType::StructRef(_))
                            && matches!(arg_type, JvmType::StructRef(_))
                        {
                            // Object → primitive: unbox
                            self.builder.unbox_if_needed(jvm_ty);
                        }
                    }
                    self.builder.emit_store(slot, jvm_ty);
                }

                if target_offset == 0 {
                    // Forward reference: emit placeholder and record for patching
                    let goto_idx = self.builder.emit_placeholder(Instruction::Goto(0));
                    if let Some(jp) = self.join_points.get_mut(target) {
                        jp.forward_jumps.push(goto_idx);
                    }
                } else {
                    // Back-edge (recur): record frame and goto
                    let initial_locals = super::builder::compact_types(&frame_locals);
                    self.builder
                        .frame
                        .frames
                        .insert(target_offset, (initial_locals, vec![]));
                    self.builder.emit(Instruction::Goto(target_offset));
                }

                // Clear stack for dead code after goto, but keep local_types intact
                // so that enclosing Switch merge frames see the full locals.
                self.builder.frame.stack_types.clear();

                // Push phantom return type so the dead-code frame's stack matches
                // the merge target's expected stack.
                let return_type = self.builder.fn_return_type
                    .expect("ICE: fn_return_type must be set before body compilation");
                self.builder.push_jvm_type(return_type);
                let after_goto = self.builder.code.len() as u16;
                self.builder.frame.record_frame(after_goto);
                Ok(return_type)
            }

            krypton_ir::ExprKind::BoolSwitch {
                scrutinee,
                true_body,
                false_body,
            } => {
                let scrutinee_type = self.compile_ir_atom(scrutinee)?;
                let scrutinee_slot = self.builder.alloc_anonymous_local(scrutinee_type);
                self.builder.emit_store(scrutinee_slot, scrutinee_type);

                let stack_at_match = self.builder.frame.stack_types.clone();
                let saved_locals = self.builder.locals.clone();
                let saved_local_types = self.builder.frame.local_types.clone();
                let saved_next_local = self.builder.next_local;
                let saved_var_locals = self.var_locals.clone();
                let saved_var_types = self.var_types.clone();

                // Emit: if scrutinee == 0 goto false_branch
                self.builder.emit_load(scrutinee_slot, scrutinee_type);
                let false_patch = self.builder.emit_placeholder(Instruction::Ifeq(0));
                self.builder.frame.pop_type();

                // True branch
                let true_type = self.compile_ir_expr(true_body, ir_module)?;
                let target_type = self.builder.fn_return_type.unwrap_or(true_type);
                self.emit_type_coercion(true_type, target_type);
                let goto_patch = self.builder.emit_placeholder(Instruction::Goto(0));

                // False branch — restore state
                let mut max_next_local = self.builder.next_local;
                self.builder.frame.stack_types = stack_at_match.clone();
                self.builder.locals = saved_locals.clone();
                self.builder.frame.local_types = saved_local_types.clone();
                self.builder.next_local = saved_next_local;
                self.var_locals = saved_var_locals.clone();
                self.var_types = saved_var_types.clone();

                let false_start = self.builder.current_offset();
                self.builder
                    .patch(false_patch, Instruction::Ifeq(false_start));
                self.builder.frame.record_frame(false_start);

                let false_type = self.compile_ir_expr(false_body, ir_module)?;
                self.emit_type_coercion(false_type, target_type);

                if self.builder.next_local > max_next_local {
                    max_next_local = self.builder.next_local;
                }

                // Merge point
                let after_match = self.builder.current_offset();
                self.builder
                    .patch(goto_patch, Instruction::Goto(after_match));
                self.builder.frame.local_types = saved_local_types;
                self.builder.frame.stack_types = stack_at_match;
                self.builder.locals = saved_locals;
                self.builder.next_local = saved_next_local;
                self.var_locals = saved_var_locals;
                self.var_types = saved_var_types;
                self.builder.push_jvm_type(target_type);
                self.builder.frame.record_frame(after_match);

                if max_next_local > self.builder.max_locals_hwm {
                    self.builder.max_locals_hwm = max_next_local;
                }

                Ok(target_type)
            }

            krypton_ir::ExprKind::Switch {
                scrutinee,
                branches,
                default,
            } => {
                let scrutinee_type = self.compile_ir_atom(scrutinee)?;
                let scrutinee_slot = self.builder.alloc_anonymous_local(scrutinee_type);
                self.builder.emit_store(scrutinee_slot, scrutinee_type);

                let stack_at_match = self.builder.frame.stack_types.clone();
                let saved_locals = self.builder.locals.clone();
                let saved_local_types = self.builder.frame.local_types.clone();
                let saved_next_local = self.builder.next_local;
                let saved_var_locals = self.var_locals.clone();
                let saved_var_types = self.var_types.clone();

                let mut goto_patches: Vec<usize> = Vec::new();
                let mut result_type = None;
                let mut max_next_local = saved_next_local;

                let total_branches = branches.len() + if default.is_some() { 1 } else { 0 };
                let all_tags: Vec<u32> = branches.iter().map(|b| b.tag).collect();

                for (i, branch) in branches.iter().enumerate() {
                    let is_last = i == total_branches - 1 && default.is_none();

                    if self.builder.next_local > max_next_local {
                        max_next_local = self.builder.next_local;
                    }

                    // Restore state for each branch
                    self.builder.frame.stack_types = stack_at_match.clone();
                    self.builder.locals = saved_locals.clone();
                    self.builder.frame.local_types = saved_local_types.clone();
                    self.builder.next_local = saved_next_local;
                    self.var_locals = saved_var_locals.clone();
                    self.var_types = saved_var_types.clone();

                    if i > 0 {
                        let branch_start = self.builder.current_offset();
                        self.builder.frame.record_frame(branch_start);
                    }

                    // Instanceof check (skip for last branch — it's the fallthrough)
                    let next_arm_patch = if !is_last {
                        let variant_name = self.find_variant_by_tag(
                            scrutinee,
                            &saved_var_types,
                            branch.tag,
                            &all_tags,
                        )?;
                        let sum_name = self
                            .types
                            .variant_to_sum
                            .get(&variant_name)
                            .ok_or_else(|| {
                                CodegenError::TypeError(
                                    format!("unknown variant: {variant_name}"),
                                    None,
                                )
                            })?
                            .clone();
                        let sum_info = &self.types.sum_type_info[&sum_name];
                        let vi = &sum_info.variants[&variant_name];
                        let variant_class_index = vi.class_index;

                        self.builder.emit_load(scrutinee_slot, scrutinee_type);
                        self.builder
                            .emit(Instruction::Instanceof(variant_class_index));
                        self.builder.pop_jvm_type(scrutinee_type);
                        self.builder.frame.push_type(VerificationType::Integer);
                        let idx = self.builder.emit_placeholder(Instruction::Ifeq(0));
                        self.builder.frame.pop_type();
                        Some(idx)
                    } else {
                        None
                    };

                    // Bind branch variables
                    if !branch.bindings.is_empty() {
                        let variant_name = self.find_variant_by_tag(
                            scrutinee,
                            &saved_var_types,
                            branch.tag,
                            &all_tags,
                        )?;
                        let sum_name = self.types.variant_to_sum[&variant_name].clone();
                        let resolved_field_types = self.resolve_variant_field_types(
                            scrutinee,
                            &saved_var_types,
                            &sum_name,
                            &variant_name,
                        );
                        let sum_info = &self.types.sum_type_info[&sum_name];
                        let vi = &sum_info.variants[&variant_name];
                        let variant_class_index = vi.class_index;
                        let field_refs = vi.field_refs.clone();
                        let fields = vi.fields.clone();

                        self.builder.emit_load(scrutinee_slot, scrutinee_type);
                        self.builder
                            .emit(Instruction::Checkcast(variant_class_index));
                        self.builder.pop_jvm_type(scrutinee_type);
                        self.builder.frame.push_type(VerificationType::Object {
                            cpool_index: variant_class_index,
                        });
                        let cast_slot = self
                            .builder
                            .alloc_anonymous_local(JvmType::StructRef(variant_class_index));
                        self.builder
                            .emit_store(cast_slot, JvmType::StructRef(variant_class_index));

                        for (j, (var_id, var_ty)) in branch.bindings.iter().enumerate() {
                            let f = &fields[j];
                            let field_ref = field_refs[j];
                            let resolved_ty_for_field = resolved_field_types
                                .as_ref()
                                .and_then(|rft| rft.get(j).cloned());
                            let actual_type = if f.is_erased {
                                // Use the resolved concrete type when available so
                                // primitives (Long/Double/Int) get unboxed correctly.
                                let concrete_ty =
                                    resolved_ty_for_field.as_ref().unwrap_or(var_ty);
                                self.type_to_jvm(concrete_ty)
                                    .unwrap_or(JvmType::StructRef(self.builder.refs.object_class))
                            } else {
                                f.jvm_type
                            };

                            self.builder
                                .emit_load(cast_slot, JvmType::StructRef(variant_class_index));
                            self.builder.emit(Instruction::Getfield(field_ref));
                            self.builder.frame.pop_type();
                            if f.is_erased {
                                self.builder.frame.push_type(VerificationType::Object {
                                    cpool_index: self.builder.refs.object_class,
                                });
                                match actual_type {
                                    JvmType::StructRef(class_idx)
                                        if class_idx != self.builder.refs.object_class =>
                                    {
                                        self.builder.emit(Instruction::Checkcast(class_idx));
                                        self.builder.frame.pop_type();
                                        self.builder.frame.push_type(VerificationType::Object {
                                            cpool_index: class_idx,
                                        });
                                    }
                                    JvmType::Long | JvmType::Double | JvmType::Int => {
                                        self.builder.unbox_if_needed(actual_type);
                                    }
                                    _ => {}
                                }
                            } else {
                                self.builder.push_jvm_type(f.jvm_type);
                            }

                            let var_slot = self.builder.alloc_anonymous_local(actual_type);
                            self.builder.emit_store(var_slot, actual_type);
                            self.var_locals.insert(*var_id, (var_slot, actual_type));
                            let resolved_ty = resolved_field_types
                                .as_ref()
                                .and_then(|rft| rft.get(j).cloned())
                                .unwrap_or_else(|| var_ty.clone());
                            self.var_types.insert(*var_id, resolved_ty);
                        }
                    }

                    let arm_type = self.compile_ir_expr(&branch.body, ir_module)?;

                    // Normalize result type
                    let target_type = self.builder.fn_return_type.unwrap_or(arm_type);
                    if result_type.is_none() {
                        result_type = Some(target_type);
                    }
                    self.emit_type_coercion(arm_type, target_type);

                    if !is_last || default.is_some() {
                        let goto_idx = self.builder.emit_placeholder(Instruction::Goto(0));
                        goto_patches.push(goto_idx);
                    }

                    if let Some(patch_idx) = next_arm_patch {
                        let target = self.builder.current_offset();
                        self.builder.patch(patch_idx, Instruction::Ifeq(target));
                    }
                }

                // Default branch
                if let Some(default_body) = default {
                    if self.builder.next_local > max_next_local {
                        max_next_local = self.builder.next_local;
                    }
                    self.builder.frame.stack_types = stack_at_match.clone();
                    self.builder.locals = saved_locals.clone();
                    self.builder.frame.local_types = saved_local_types.clone();
                    self.builder.next_local = saved_next_local;
                    self.var_locals = saved_var_locals.clone();
                    self.var_types = saved_var_types.clone();

                    let default_start = self.builder.current_offset();
                    self.builder.frame.record_frame(default_start);

                    let arm_type = self.compile_ir_expr(default_body, ir_module)?;
                    let target_type = self.builder.fn_return_type.unwrap_or(arm_type);
                    if result_type.is_none() {
                        result_type = Some(target_type);
                    }
                    self.emit_type_coercion(arm_type, target_type);
                }

                if self.builder.next_local > max_next_local {
                    max_next_local = self.builder.next_local;
                }

                let after_match = self.builder.current_offset();
                self.builder.frame.local_types = saved_local_types;
                self.builder.frame.stack_types = stack_at_match;
                self.builder.locals = saved_locals;
                self.builder.next_local = saved_next_local;
                self.var_locals = saved_var_locals;
                self.var_types = saved_var_types;
                if let Some(rt) = result_type {
                    self.builder.push_jvm_type(rt);
                }
                self.builder.frame.record_frame(after_match);

                for goto_idx in goto_patches {
                    self.builder.patch(goto_idx, Instruction::Goto(after_match));
                }

                if max_next_local > self.builder.max_locals_hwm {
                    self.builder.max_locals_hwm = max_next_local;
                }

                Ok(result_type.ok_or_else(|| {
                    CodegenError::TypeError(
                        "switch expression produced no result type".to_string(),
                        None,
                    )
                })?)
            }
        }
    }

    /// Substitute type variables in a type using a mapping from TypeVarId to concrete Type.
    fn substitute_type_vars(ty: &Type, subst: &HashMap<krypton_ir::TypeVarId, Type>) -> Type {
        match ty {
            Type::Var(v) => subst.get(v).cloned().unwrap_or_else(|| ty.clone()),
            Type::Named(name, args) => Type::Named(
                name.clone(),
                args.iter()
                    .map(|a| Self::substitute_type_vars(a, subst))
                    .collect(),
            ),
            Type::Own(inner) => Type::Own(Box::new(Self::substitute_type_vars(inner, subst))),
            Type::App(ctor, args) => Type::App(
                Box::new(Self::substitute_type_vars(ctor, subst)),
                args.iter()
                    .map(|a| Self::substitute_type_vars(a, subst))
                    .collect(),
            ),
            Type::Fn(params, ret) => Type::Fn(
                params
                    .iter()
                    .map(|p| Self::substitute_type_vars(p, subst))
                    .collect(),
                Box::new(Self::substitute_type_vars(ret, subst)),
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| Self::substitute_type_vars(e, subst))
                    .collect(),
            ),
            _ => ty.clone(),
        }
    }

    /// Resolve concrete field types for a variant binding using the scrutinee's type.
    /// Returns a vec of concrete types for each field, or None if resolution isn't possible.
    fn resolve_variant_field_types(
        &self,
        scrutinee: &krypton_ir::Atom,
        var_types: &HashMap<krypton_ir::VarId, Type>,
        sum_name: &str,
        variant_name: &str,
    ) -> Option<Vec<Type>> {
        // Get the sum type's type params and the variant's generic field types
        let type_params = self.sum_type_params.get(sum_name)?;
        let field_types = self.variant_field_types.get(variant_name)?;

        // Get the scrutinee's concrete type arguments
        let type_args = if let krypton_ir::Atom::Var(var_id) = scrutinee {
            match var_types.get(var_id) {
                Some(Type::Named(_, args)) => Some(args),
                Some(Type::Own(inner)) => match inner.as_ref() {
                    Type::Named(_, args) => Some(args),
                    _ => None,
                },
                _ => None,
            }
        } else {
            None
        }?;

        if type_params.len() != type_args.len() {
            return None;
        }

        // Build substitution: type_param -> concrete type
        let subst: HashMap<krypton_ir::TypeVarId, Type> = type_params
            .iter()
            .zip(type_args.iter())
            .map(|(p, a)| (*p, a.clone()))
            .collect();

        // Apply substitution to each field type
        Some(
            field_types
                .iter()
                .map(|ft| Self::substitute_type_vars(ft, &subst))
                .collect(),
        )
    }

    /// Find variant name by tag from scrutinee type info.
    fn find_variant_by_tag(
        &self,
        scrutinee: &krypton_ir::Atom,
        var_types: &HashMap<krypton_ir::VarId, Type>,
        tag: u32,
        all_tags: &[u32],
    ) -> Result<String, CodegenError> {
        let sum_name = match scrutinee {
            krypton_ir::Atom::Var(var_id) => match var_types.get(var_id) {
                Some(Type::Named(name, _)) => name.clone(),
                Some(Type::Own(inner)) => match inner.as_ref() {
                    Type::Named(name, _) => name.clone(),
                    _ => {
                        return Err(CodegenError::TypeError(
                            "Switch scrutinee is not a named type".to_string(),
                            None,
                        ))
                    }
                },
                _ => {
                    // Intentional: when var_types lacks type info, infer sum type from
                    // branch tags. Errors on 0 or 2+ candidates.
                    let candidates: Vec<&String> = self
                        .variant_tags
                        .iter()
                        .filter(|(_, tags)| all_tags.iter().all(|t| tags.contains_key(t)))
                        .map(|(name, _)| name)
                        .collect();
                    if candidates.len() == 1 {
                        candidates[0].clone()
                    } else {
                        return Err(CodegenError::TypeError(
                            format!("ICE: Switch scrutinee var {:?} has no type in var_types ({} tag-match candidates)", var_id, candidates.len()), None));
                    }
                }
            },
            _ => {
                return Err(CodegenError::TypeError(
                    "Switch on literal scrutinee".to_string(),
                    None,
                ))
            }
        };

        self.variant_tags
            .get(&sum_name)
            .and_then(|tags| tags.get(&tag))
            .cloned()
            .ok_or_else(|| {
                CodegenError::TypeError(
                    format!("cannot find variant with tag {tag} for type {sum_name}"),
                    None,
                )
            })
    }

    /// Compile an IR FnDef into a JVM Method.
    pub(super) fn compile_ir_function(
        &mut self,
        fn_def: &krypton_ir::FnDef,
        ir_module: &krypton_ir::Module,
    ) -> Result<Method, CodegenError> {
        self.reset_method_state();

        let info = self
            .types
            .get_function(&fn_def.name)
            .ok_or_else(|| CodegenError::UndefinedVariable(fn_def.name.clone(), None))?;
        let param_types = info.param_types.clone();
        let return_type = info.return_type;

        let tc_types = self.types.fn_tc_types.get(&fn_def.name).cloned();

        // Functions without trait constraints need no dict params
        let dict_requirements = self
            .traits
            .impl_dict_requirements
            .get(&fn_def.name)
            .cloned()
            .unwrap_or_default();
        let num_dict_params = dict_requirements.len();
        let mut fn_params = Vec::new();

        // Allocate dict params
        for (di, requirement) in dict_requirements.iter().enumerate() {
            let slot = self.builder.next_local;
            let jvm_ty = JvmType::StructRef(self.builder.refs.object_class);
            self.traits.dict_locals.insert(
                (requirement.trait_name().clone(), requirement.type_var_id()),
                slot,
            );
            fn_params.push((slot, jvm_ty));
            // Also register in var_locals for the IR param (dict params are at the front)
            if di < fn_def.params.len() {
                let (var_id, param_ty) = &fn_def.params[di];
                self.var_locals.insert(*var_id, (slot, jvm_ty));
                self.var_types.insert(*var_id, param_ty.clone());
            }
            self.builder.next_local += 1;
            self.builder
                .frame
                .local_types
                .push(VerificationType::Object {
                    cpool_index: self.builder.refs.object_class,
                });
        }

        // Allocate user params
        for (i, &jvm_ty) in param_types[num_dict_params..].iter().enumerate() {
            let param_idx = num_dict_params + i;
            let (var_id, param_ty) = &fn_def.params[param_idx];
            let slot = self.builder.next_local;
            let slot_size: u16 = match jvm_ty {
                JvmType::Long | JvmType::Double => 2,
                _ => 1,
            };
            self.builder.next_local += slot_size;
            let vtypes = self.builder.jvm_type_to_vtypes(jvm_ty);
            self.builder.frame.local_types.extend(vtypes);
            fn_params.push((slot, jvm_ty));
            self.var_locals.insert(*var_id, (slot, jvm_ty));
            self.var_types.insert(*var_id, param_ty.clone());

            // If this param is function-typed, register in local_fn_info
            if let Some((ref tc_param_types, _)) = tc_types {
                let tc_idx = i;
                if tc_idx < tc_param_types.len() {
                    let tc_param_type = match &tc_param_types[tc_idx] {
                        Type::Own(inner) => inner.as_ref(),
                        other => other,
                    };
                    if let Type::Fn(inner_params, inner_ret) = tc_param_type {
                        let inner_param_jvm: Vec<JvmType> = inner_params
                            .iter()
                            .map(|t| self.type_to_jvm(t))
                            .collect::<Result<_, _>>()?;
                        let inner_ret_jvm = self.type_to_jvm(inner_ret)?;
                        let arity = inner_params.len() as u8;
                        self.lambda.ensure_fun_interface(
                            arity,
                            &mut self.cp,
                            &mut self.types.class_descriptors,
                        )?;
                        let var_name = format!("__ir_var_{}", var_id.0);
                        self.builder.locals.insert(var_name.clone(), (slot, jvm_ty));
                        self.builder
                            .local_fn_info
                            .insert(var_name, (inner_param_jvm, inner_ret_jvm));
                    }
                }
            }
        }

        self.builder.fn_params = fn_params;
        self.builder.fn_return_type = Some(return_type);

        // Pre-allocate and null-initialize resource locals for finally handler.
        // This ensures the JVM verifier sees valid Object types in these slots
        // at every PC in the exception table's protected range. Same pattern as
        // javac's try-with-resources: `Resource r = null; try { r = ...; } finally { ... }`
        if let Some(finally_closes) = ir_module.fn_exit_closes.get(&fn_def.name) {
            for fc in finally_closes {
                let slot = self
                    .builder
                    .alloc_anonymous_local(JvmType::StructRef(self.builder.refs.object_class));
                self.builder.emit(Instruction::Aconst_null);
                self.builder.frame.push_type(VerificationType::Null);
                self.builder.emit(Instruction::Astore(slot as u8));
                self.builder.frame.pop_type();
                self.pre_allocated_slots.insert(fc.resource_var, slot);
            }
        }

        self.builder.emit(Instruction::Nop);
        let body_start = self.builder.current_offset();
        self.builder.recur_target = body_start;
        self.builder.recur_frame_locals = self.builder.frame.local_types.clone();

        // Save handler-safe locals (only params + null-initialized resource slots)
        let handler_locals = self.builder.frame.local_types.clone();

        let body_type = self.compile_ir_expr(&fn_def.body, ir_module)?;

        // Return type coercion
        self.emit_type_coercion(body_type, return_type);

        let ret_instr = match return_type {
            JvmType::Long => Instruction::Lreturn,
            JvmType::Double => Instruction::Dreturn,
            JvmType::Int => Instruction::Ireturn,
            JvmType::StructRef(_) => Instruction::Areturn,
        };
        self.builder.emit(ret_instr);

        // Emit finally handler for resource auto-close on panic
        if let Some(finally_closes) = ir_module.fn_exit_closes.get(&fn_def.name) {
            if !finally_closes.is_empty() {
                self.emit_finally_handler(finally_closes, body_start, &handler_locals)?;
            }
        }

        let descriptor = self.types.build_descriptor(&param_types, return_type);
        let jvm_name = if fn_def.name == "main" {
            "krypton_main"
        } else {
            &fn_def.name
        };
        let name_idx = self.cp.add_utf8(jvm_name)?;
        let desc_idx = self.cp.add_utf8(&descriptor)?;

        Ok(Method {
            access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
            name_index: name_idx,
            descriptor_index: desc_idx,
            attributes: vec![self.builder.finish_method()],
        })
    }

    /// Compile an `ExprKind::AutoClose` node: evaluate `close(dict, resource)`
    /// via the Resource trait, optionally null the resource slot so the
    /// function-wide finally handler skips it, then compile `body`.
    fn compile_auto_close(
        &mut self,
        resource: krypton_ir::VarId,
        dict: &krypton_ir::Atom,
        type_name: &str,
        null_slot: bool,
        body: &krypton_ir::Expr,
        ir_module: &krypton_ir::Module,
    ) -> Result<JvmType, CodegenError> {
        // Resolve the resource's slot. block-scoped resources may have had
        // their var_locals entry rolled back by branch restoration; fall
        // back to pre_allocated_slots which persists for the whole fn.
        let resource_slot = self
            .var_locals
            .get(&resource)
            .copied()
            .map(|(slot, _)| slot)
            .or_else(|| self.pre_allocated_slots.get(&resource).copied())
            .ok_or_else(|| {
                CodegenError::UndefinedVariable(
                    format!("AutoClose: resource var {:?} has no slot", resource),
                    None,
                )
            })?;

        // Resolve the Resource trait dispatch table.
        let resource_trait = krypton_ir::TraitName::core_resource();
        let dispatch = self
            .traits
            .trait_dispatch
            .get(&resource_trait)
            .ok_or_else(|| {
                CodegenError::UnsupportedExpr(
                    "no dispatch info for Resource trait in AutoClose".to_string(),
                    None,
                )
            })?;
        let close_method_ref = dispatch.method_refs["close"];
        let _ = type_name; // type_name is carried for debug/pretty only

        // Load dict atom
        let _ = self.compile_ir_atom(dict)?;

        // Load and box the resource value
        self.builder.emit(Instruction::Aload(resource_slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });

        // invokeinterface close(dict, resource) — 2 args, returns Object (Unit)
        self.builder
            .emit(Instruction::Invokeinterface(close_method_ref, 2));
        self.builder.frame.pop_type(); // resource
        self.builder.frame.pop_type(); // dict
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.object_class,
        });
        self.builder.emit(Instruction::Pop);
        self.builder.frame.pop_type();

        // Optionally null the slot so the fn-wide finally handler skips it.
        if null_slot {
            self.builder.emit(Instruction::Aconst_null);
            self.builder.frame.push_type(VerificationType::Null);
            self.builder.emit(Instruction::Astore(resource_slot as u8));
            self.builder.frame.pop_type();
        }

        // Continue with the body of the AutoClose (the actual return path).
        self.compile_ir_expr(body, ir_module)
    }

    /// Emit a finally handler that calls close() on resources when an exception occurs.
    /// Follows the Java try-with-resources pattern: close each resource in LIFO order,
    /// suppress any exception thrown by close() itself, then re-throw the original.
    fn emit_finally_handler(
        &mut self,
        finally_closes: &[krypton_ir::FinallyClose],
        body_start: u16,
        handler_locals: &[VerificationType],
    ) -> Result<(), CodegenError> {
        let handler_start = self.builder.current_offset();

        // Set up StackMapTable frame at handler entry: stack = [Throwable],
        // locals = only params + pre-initialized resource slots (valid at all PCs in protected range)
        self.builder.frame.stack_types.clear();
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.throwable_class,
        });
        self.builder.frame.local_types = handler_locals.to_vec();
        self.builder.record_frame();

        // Store the caught exception in a local
        let exc_slot = self.builder.next_local;
        self.builder.next_local += 1;
        self.builder.max_locals_hwm = self.builder.max_locals_hwm.max(self.builder.next_local);
        self.builder.emit(Instruction::Astore(exc_slot as u8));
        self.builder.frame.pop_type();
        // Extend handler locals to include exc_slot
        let mut active_locals = handler_locals.to_vec();
        // Pad with Top up to exc_slot
        while active_locals.len() < exc_slot as usize {
            active_locals.push(VerificationType::Top);
        }
        active_locals.push(VerificationType::Object {
            cpool_index: self.builder.refs.throwable_class,
        });
        self.builder.frame.local_types = active_locals.clone();

        let resource_trait = krypton_ir::TraitName::core_resource();
        let dispatch = self
            .traits
            .trait_dispatch
            .get(&resource_trait)
            .ok_or_else(|| {
                CodegenError::UnsupportedExpr(
                    "no dispatch info for Resource trait in finally handler".to_string(),
                    None,
                )
            })?;
        let close_method_ref = dispatch.method_refs["close"];
        let iface_class = dispatch.interface_class;

        // Close each resource in LIFO order (reverse of declaration order)
        for fc in finally_closes.iter().rev() {
            // var_locals may have been rolled back for block-scoped resources
            // declared inside branches; fall back to pre_allocated_slots which
            // is populated once at function entry and never restored.
            let resource_slot = self
                .var_locals
                .get(&fc.resource_var)
                .copied()
                .map(|(slot, _)| slot)
                .or_else(|| self.pre_allocated_slots.get(&fc.resource_var).copied())
                .ok_or_else(|| {
                    CodegenError::UndefinedVariable(
                        format!(
                            "finally handler: resource var {:?} not found",
                            fc.resource_var
                        ),
                        None,
                    )
                })?;

            // Skip close if resource is null (exception before initialization)
            self.builder.emit(Instruction::Aload(resource_slot as u8));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
            let null_check_placeholder = self.builder.emit_placeholder(Instruction::Ifnull(0));
            self.builder.frame.pop_type();

            // Inner try: protect close() call so double-panic is suppressed
            let inner_try_start = self.builder.current_offset();

            // Load dict for Resource[type_name]
            let resource_type = krypton_ir::Type::Named(fc.type_name.clone(), vec![]);
            self.emit_dict_argument_for_type(&resource_trait, &resource_type, iface_class)?;

            // Load and box the resource value
            self.builder.emit(Instruction::Aload(resource_slot as u8));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });

            // invokeinterface close(dict, resource) — 2 args
            self.builder
                .emit(Instruction::Invokeinterface(close_method_ref, 2));
            self.builder.frame.pop_type(); // resource
            self.builder.frame.pop_type(); // dict
                                           // close returns Object (boxed Unit) — pop it
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
            self.builder.emit(Instruction::Pop);
            self.builder.frame.pop_type();

            let inner_try_end = self.builder.current_offset();

            // goto after_inner (skip the inner catch handler)
            let goto_placeholder = self.builder.emit_placeholder(Instruction::Goto(0));

            // Inner catch handler: suppress exception from close(), log warning
            let inner_handler = self.builder.current_offset();
            // Frame: stack = [Throwable], locals = active_locals
            self.builder.frame.stack_types.clear();
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.throwable_class,
            });
            self.builder.frame.local_types = active_locals.clone();
            self.builder.record_frame();

            // Pop the suppressed exception
            self.builder.emit(Instruction::Pop);
            self.builder.frame.pop_type();

            // Log warning: System.err.println("warning: resource close failed during panic")
            self.builder
                .emit(Instruction::Getstatic(self.builder.refs.system_err_field));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.object_class,
            });
            let warning_msg = self
                .cp
                .add_string("warning: resource close failed during panic")?;
            self.builder.emit(Instruction::Ldc_w(warning_msg));
            self.builder.frame.push_type(VerificationType::Object {
                cpool_index: self.builder.refs.string_class,
            });
            self.builder.emit(Instruction::Invokevirtual(
                self.builder.refs.printstream_println,
            ));
            self.builder.frame.pop_type(); // string arg
            self.builder.frame.pop_type(); // printstream receiver

            // after_inner: patch the goto and null check
            let after_inner = self.builder.current_offset();
            self.builder
                .patch(goto_placeholder, Instruction::Goto(after_inner));
            self.builder
                .patch(null_check_placeholder, Instruction::Ifnull(after_inner));

            // Record frame at after_inner (merge point of goto, null check, and inner catch)
            self.builder.frame.stack_types.clear();
            self.builder.frame.local_types = active_locals.clone();
            self.builder.record_frame();

            // Inner exception table entry: suppress close() failure
            self.builder
                .add_exception_entry(inner_try_start..inner_try_end, inner_handler, 0);
        }

        // Re-throw the original exception
        self.builder.emit(Instruction::Aload(exc_slot as u8));
        self.builder.frame.push_type(VerificationType::Object {
            cpool_index: self.builder.refs.throwable_class,
        });
        self.builder.emit(Instruction::Athrow);

        // Outer exception table entry: covers body through return
        self.builder
            .add_exception_entry(body_start..handler_start, handler_start, 0);

        Ok(())
    }

    pub(super) fn build_class(
        mut self,
        extra_methods: Vec<Method>,
        is_main: bool,
    ) -> Result<Vec<u8>, CodegenError> {
        let this_class = self.this_class;
        let object_class = self.builder.refs.object_class;
        let constructor = Method {
            access_flags: MethodAccessFlags::PUBLIC,
            name_index: self.builder.refs.init_name,
            descriptor_index: self.builder.refs.init_desc,
            attributes: vec![Attribute::Code {
                name_index: self.builder.refs.code_utf8,
                max_stack: 1,
                max_locals: 1,
                code: vec![
                    Instruction::Aload_0,
                    Instruction::Invokespecial(self.builder.refs.object_init),
                    Instruction::Return,
                ],
                exception_table: vec![],
                attributes: vec![],
            }],
        };

        let mut methods = vec![constructor];
        methods.extend(extra_methods);
        // Add lambda methods
        methods.extend(std::mem::take(&mut self.lambda.lambda_methods));

        if is_main {
            let main_name = self.cp.add_utf8("main")?;
            let main_desc = self.cp.add_utf8("([Ljava/lang/String;)V")?;

            let main_method = Method {
                access_flags: MethodAccessFlags::PUBLIC | MethodAccessFlags::STATIC,
                name_index: main_name,
                descriptor_index: main_desc,
                attributes: vec![self.builder.finish_method()],
            };
            methods.push(main_method);
        }

        // Build class attributes (BootstrapMethods if any)
        let mut class_attributes = Vec::new();
        if !self.lambda.bootstrap_methods.is_empty() {
            let bsm_name = self.cp.add_utf8("BootstrapMethods")?;
            class_attributes.push(Attribute::BootstrapMethods {
                name_index: bsm_name,
                methods: std::mem::take(&mut self.lambda.bootstrap_methods),
            });
        }

        let class_file = ClassFile {
            version: JAVA_21,
            access_flags: ClassAccessFlags::PUBLIC | ClassAccessFlags::SUPER,
            constant_pool: self.cp,
            this_class,
            super_class: object_class,
            methods,
            attributes: class_attributes,
            ..Default::default()
        };

        let mut buffer = Vec::new();
        class_file.to_bytes(&mut buffer)?;
        Ok(buffer)
    }
}
