use super::*;
use crate::kernel::AlgebraicValueType;

/// A struct element is nominal even though it has no scalar Click value type.
/// Keep it in substitution until a surrounding pointer supplies its representation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum TypeArgument {
    Value(ClickType),
    Struct(String),
}

impl TypeArgument {
    pub(super) fn value(&self) -> Option<&ClickType> {
        match self {
            Self::Value(value) => Some(value),
            Self::Struct(_) => None,
        }
    }
    fn describe(&self) -> String {
        match self {
            Self::Value(value) => validation::describe_click_type(value),
            Self::Struct(name) => format!("struct {name}"),
        }
    }
}

impl From<ClickType> for TypeArgument {
    fn from(value: ClickType) -> Self {
        Self::Value(value)
    }
}

pub(super) type TypeSubstitution = BTreeMap<String, TypeArgument>;

fn bind_type_argument(
    name: &str,
    actual: TypeArgument,
    substitution: &mut TypeSubstitution,
) -> Result<(), String> {
    if let Some(previous) = substitution.get(name) {
        if previous != &actual {
            return Err(format!(
                "type parameter `{name}` is both {} and {}",
                previous.describe(),
                actual.describe()
            ));
        }
    } else {
        substitution.insert(name.to_owned(), actual);
    }
    Ok(())
}

pub(super) fn validate_type_parameter_list(
    kind: &str,
    name: &str,
    parameters: &[String],
) -> Result<(), ClickError> {
    let mut seen = BTreeSet::new();
    for parameter in parameters {
        if parser::is_c_type_keyword(parameter) {
            return Err(ClickError::new(format!(
                "{kind} `{name}` type parameter `{parameter}` conflicts with a built-in type"
            )));
        }
        if !seen.insert(parameter) {
            return Err(ClickError::new(format!(
                "{kind} `{name}` repeats type parameter `{parameter}`"
            )));
        }
    }
    Ok(())
}

pub(super) fn infer_type_substitution(
    kind: &str,
    name: &str,
    type_parameters: &[String],
    parameter_types: impl IntoIterator<Item = ClickType>,
    argument_types: impl IntoIterator<Item = Option<ClickType>>,
) -> Result<TypeSubstitution, String> {
    let allowed = type_parameters.iter().map(String::as_str).collect();
    let mut substitution = BTreeMap::new();
    for (parameter, argument) in parameter_types.into_iter().zip(argument_types) {
        // An `Integer` parameter names no type parameter, so it decides
        // none, and its argument is checked as an `Integer` where the call
        // is: an unsuffixed literal there is read as one, not as `int32`.
        if parameter == ClickType::Integer {
            continue;
        }
        if let Some(argument) = argument {
            unify_click_type(&parameter, &argument, &allowed, &mut substitution).map_err(
                |message| format!("cannot infer type arguments for {kind} `{name}`: {message}"),
            )?;
        }
    }
    let missing = type_parameters
        .iter()
        .filter(|parameter| !substitution.contains_key(*parameter))
        .cloned()
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return Err(format!(
            "cannot infer type argument{} {} for {kind} `{name}`",
            if missing.len() == 1 { "" } else { "s" },
            missing.join(", ")
        ));
    }
    Ok(substitution)
}

pub(super) fn unify_click_type(
    pattern: &ClickType,
    actual: &ClickType,
    allowed: &BTreeSet<&str>,
    substitution: &mut TypeSubstitution,
) -> Result<(), String> {
    // A C value of a primitive type's instance, a Rust `Vec<u32>`, is that
    // instance's Surface value.
    let primitive;
    let actual = match primitive_instance_value_type(actual) {
        Some(value_type) => {
            primitive = value_type;
            &primitive
        }
        None => actual,
    };
    match pattern {
        ClickType::Proposition => {
            if actual == &ClickType::Proposition {
                Ok(())
            } else {
                Err("expected Prop argument".into())
            }
        }
        ClickType::Resource if actual == &ClickType::Resource => Ok(()),
        ClickType::Resource => Err("expected Resource argument".into()),
        ClickType::Function { parameters, result } => {
            let ClickType::Function {
                parameters: actual_parameters,
                result: actual_result,
            } = actual
            else {
                return Err("expected a specification function type".into());
            };
            if parameters.len() != actual_parameters.len() {
                return Err("specification function arity mismatch".into());
            }
            for (pattern, actual) in parameters.iter().zip(actual_parameters) {
                unify_click_type(pattern, actual, allowed, substitution)?;
            }
            unify_click_type(result, actual_result, allowed, substitution)
        }
        ClickType::Parameter(name) if allowed.contains(name.as_str()) => {
            bind_type_argument(name, actual.clone().into(), substitution)
        }
        ClickType::Parameter(name) => Err(format!("unknown type parameter `{name}`")),
        ClickType::CObjectPointer { .. } if pattern == actual => Ok(()),
        ClickType::CObjectPointer { .. } => Err(format!(
            "expected {}, got {}",
            validation::describe_click_type(pattern),
            validation::describe_click_type(actual)
        )),
        ClickType::Program(InterfaceType::ParameterPointer(name))
            if allowed.contains(name.name()) =>
        {
            let pointee = actual
                .interface_type()
                .and_then(|ty| ty.pointee_type())
                .ok_or_else(|| {
                    format!(
                        "expected a typed pointer argument, got {}",
                        validation::describe_click_type(actual)
                    )
                })?;
            let element = match actual {
                ClickType::CObjectPointer { struct_name, .. } if pointee.is_pointer() => {
                    ClickType::CObjectPointer {
                        interface_type: pointee,
                        struct_name: struct_name.clone(),
                    }
                }
                ClickType::CObjectPointer { struct_name, .. } => {
                    return bind_type_argument(
                        name.name(),
                        TypeArgument::Struct(struct_name.clone()),
                        substitution,
                    );
                }
                _ => ClickType::Program(pointee),
            };
            unify_click_type(
                &ClickType::Parameter(name.name().to_owned()),
                &element,
                allowed,
                substitution,
            )
        }
        ClickType::Program(expected) => match actual {
            ClickType::Program(actual)
                if validation::click_types_compatible(*actual, *expected) =>
            {
                Ok(())
            }
            _ => Err(format!(
                "expected {}, got {}",
                validation::describe_click_type(pattern),
                validation::describe_click_type(actual)
            )),
        },
        ClickType::Integer => match actual {
            ClickType::Integer => Ok(()),
            _ => Err(format!(
                "expected {}, got {}",
                validation::describe_click_type(pattern),
                validation::describe_click_type(actual)
            )),
        },
        ClickType::Algebraic(expected) => {
            let ClickType::Algebraic(actual) = actual else {
                return Err(format!(
                    "expected {}, got {}",
                    validation::describe_click_type(pattern),
                    validation::describe_click_type(actual)
                ));
            };
            // A constructor that leaves out its type arguments, where
            // nothing around it fixed them, reaches here as the bare name.
            if !actual.rigid
                && expected.name == actual.name
                && actual.arguments.is_empty()
                && !expected.arguments.is_empty()
            {
                return Err(format!(
                    "a `{}` constructor leaves out its type arguments and nothing around it fixes them; write them, as in `{}<...>::...`",
                    actual.name, actual.name
                ));
            }
            if expected.rigid != actual.rigid
                || expected.name != actual.name
                || expected.arguments.len() != actual.arguments.len()
            {
                return Err(format!(
                    "expected {}, got {}",
                    validation::describe_click_type(pattern),
                    validation::describe_click_type(&ClickType::Algebraic(actual.clone()))
                ));
            }
            for (expected, actual) in expected.arguments.iter().zip(&actual.arguments) {
                unify_click_type(expected, actual, allowed, substitution)?;
            }
            Ok(())
        }
    }
}

pub(super) fn instantiate_click_type(
    click_type: &ClickType,
    substitution: &TypeSubstitution,
) -> Result<ClickType, String> {
    match click_type {
        ClickType::Proposition => Ok(ClickType::Proposition),
        ClickType::Resource => Ok(ClickType::Resource),
        ClickType::Function { parameters, result } => Ok(ClickType::Function {
            parameters: parameters
                .iter()
                .map(|ty| instantiate_click_type(ty, substitution))
                .collect::<Result<_, _>>()?,
            result: Box::new(instantiate_click_type(result, substitution)?),
        }),
        ClickType::Parameter(name) => substitution
            .get(name)
            .ok_or_else(|| format!("unresolved type parameter `{name}`"))
            .and_then(|argument| {
                argument.value().cloned().ok_or_else(|| {
                    format!(
                        "struct type `{}` requires a pointer; struct values are not supported",
                        argument.describe()
                    )
                })
            }),
        ClickType::Program(InterfaceType::ParameterPointer(name))
            if substitution.contains_key(name.name()) =>
        {
            let element = substitution
                .get(name.name())
                .ok_or_else(|| format!("unresolved pointer element type `{}`", name.name()))?;
            let element = match element {
                TypeArgument::Struct(struct_name) => {
                    return Ok(ClickType::CObjectPointer {
                        interface_type: InterfaceType::Int32Pointer,
                        struct_name: struct_name.clone(),
                    });
                }
                // The enclosing declaration's own type parameter: `T*`
                // stays a pointer to it, as a generic declaration that
                // calls another at its own `T` writes.
                TypeArgument::Value(ClickType::Parameter(parameter)) => {
                    return Ok(ClickType::Program(InterfaceType::ParameterPointer(
                        crate::kernel::TypeParameterName::intern(parameter),
                    )));
                }
                TypeArgument::Value(element) => element,
            };
            let pointer = element
                .interface_type()
                .and_then(|ty| ty.pointer_type())
                .ok_or_else(|| {
                    format!(
                        "pointer element type `{}` must have a C representation",
                        validation::describe_click_type(element)
                    )
                })?;
            Ok(match element {
                ClickType::CObjectPointer { struct_name, .. } => ClickType::CObjectPointer {
                    interface_type: pointer,
                    struct_name: struct_name.clone(),
                },
                _ => ClickType::Program(pointer),
            })
        }
        ClickType::Program(_) | ClickType::CObjectPointer { .. } => Ok(click_type.clone()),
        ClickType::Integer => Ok(ClickType::Integer),
        ClickType::Algebraic(application) => Ok(ClickType::Algebraic(instantiate_algebraic_type(
            application,
            substitution,
        )?)),
    }
}

pub(super) fn instantiate_algebraic_type(
    application: &AlgebraicTypeApplication,
    substitution: &TypeSubstitution,
) -> Result<AlgebraicTypeApplication, String> {
    Ok(AlgebraicTypeApplication {
        rigid: application.rigid,
        name: application.name.clone(),
        arguments: application
            .arguments
            .iter()
            .map(|argument| instantiate_click_type(argument, substitution))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

/// The instances of Click library primitive types the kernel has been
/// given, by their kernel name: each is a rigid kernel type, and this is how
/// its kernel name reads back as the Surface application `Vec<uint32>`.
/// Each name is a function of its parts alone, so one table serves the
/// whole process.
static PRIMITIVE_INSTANCES: std::sync::LazyLock<
    std::sync::RwLock<BTreeMap<String, (String, Vec<AlgebraicValueType>)>>,
> = std::sync::LazyLock::new(Default::default);

/// The kernel type of an instance of a Click library primitive type,
/// `Vec<uint32>`: a rigid type named by `primitive_kernel_type_name`,
/// recorded so the name reads back as its Surface application.
pub(crate) fn primitive_instance_type(
    name: &str,
    arguments: &[AlgebraicValueType],
) -> crate::kernel::AlgebraicType {
    let kernel_name = primitive_kernel_type_name(name, arguments);
    let known = PRIMITIVE_INSTANCES
        .read()
        .expect("primitive instance table")
        .contains_key(&kernel_name);
    if !known {
        PRIMITIVE_INSTANCES
            .write()
            .expect("primitive instance table")
            .insert(kernel_name.clone(), (name.to_string(), arguments.to_vec()));
        crate::kernel::TypeParameterName::declare_library_instance(&kernel_name);
    }
    crate::kernel::AlgebraicType::parameter(kernel_name)
}

/// The kernel's name for an instance of a Click library primitive type,
/// `Vec<uint32>`. The kernel reads each instance as a rigid type of its own:
/// it has no constructors to case on and no structure to induct over, and
/// two instances are one type exactly when their arguments are equal.
fn primitive_kernel_type_name(name: &str, arguments: &[AlgebraicValueType]) -> String {
    fn argument_name(argument: &AlgebraicValueType) -> String {
        match argument {
            AlgebraicValueType::Algebraic { name, arguments } if !arguments.is_empty() => {
                primitive_kernel_type_name(name, arguments)
            }
            AlgebraicValueType::Algebraic { name, .. } => name.clone(),
            AlgebraicValueType::Parameter(name) => format!("[rigid {name}]"),
            AlgebraicValueType::Integer => "Integer".to_string(),
            AlgebraicValueType::Program(interface_type) => validation::describe_click_type(
                &ClickType::Program(interface_type_from_program_type(*interface_type)),
            ),
            AlgebraicValueType::ObjectPointer(interface_type, class) => {
                format!("{interface_type:?} [{class:?}]")
            }
        }
    }
    format!(
        "{name}<{}>",
        arguments
            .iter()
            .map(argument_name)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// The primitive type and arguments the kernel type `kernel_name` is an
/// instance of, `("Vec", [uint32])`.
pub(crate) fn primitive_instance_of(
    kernel_name: &str,
) -> Option<(String, Vec<AlgebraicValueType>)> {
    PRIMITIVE_INSTANCES
        .read()
        .expect("primitive instance table")
        .get(kernel_name)
        .cloned()
}

/// The Surface type of a value whose type names an instance of a
/// primitive type: a C value of the kernel's rigid `Vec<uint32>`, or the
/// rigid type itself, is `Vec<uint32>`.
pub(super) fn primitive_instance_value_type(click_type: &ClickType) -> Option<ClickType> {
    let kernel_name = match click_type {
        ClickType::Program(InterfaceType::Parameter(name)) => name.name(),
        ClickType::Algebraic(application) if application.rigid => application.name.as_str(),
        _ => return None,
    };
    primitive_instance_of(kernel_name)?;
    Some(click_type_from_algebraic_value_type(
        &AlgebraicValueType::Parameter(kernel_name.to_string()),
    ))
}

/// Whether the kernel type `kernel_name` is the instance of a Click library
/// primitive type that `expected` writes.
pub(super) fn is_primitive_instance(
    kernel_name: &str,
    expected: &AlgebraicTypeApplication,
) -> bool {
    !expected.rigid
        && click_type_from_algebraic_value_type(&AlgebraicValueType::Parameter(
            kernel_name.to_string(),
        )) == ClickType::Algebraic(expected.clone())
}

pub(super) fn click_type_from_algebraic_value_type(value_type: &AlgebraicValueType) -> ClickType {
    let primitive = match value_type {
        AlgebraicValueType::Parameter(name) => PRIMITIVE_INSTANCES
            .read()
            .expect("primitive instance table")
            .get(name)
            .cloned(),
        _ => None,
    };
    if let Some((name, arguments)) = primitive {
        return ClickType::Algebraic(AlgebraicTypeApplication {
            rigid: false,
            name,
            arguments: arguments
                .iter()
                .map(click_type_from_algebraic_value_type)
                .collect(),
        });
    }
    match value_type {
        AlgebraicValueType::Parameter(name) => ClickType::Algebraic(AlgebraicTypeApplication {
            rigid: true,
            name: name.clone(),
            arguments: Vec::new(),
        }),
        AlgebraicValueType::Program(interface_type) => {
            ClickType::Program(interface_type_from_program_type(*interface_type))
        }
        AlgebraicValueType::ObjectPointer(interface_type, class) => {
            ClickType::from_object_pointer_class(
                interface_type_from_program_type(*interface_type),
                class,
            )
        }
        AlgebraicValueType::Integer => ClickType::Integer,
        AlgebraicValueType::Algebraic { name, arguments } => {
            ClickType::Algebraic(AlgebraicTypeApplication {
                rigid: false,
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(click_type_from_algebraic_value_type)
                    .collect(),
            })
        }
    }
}

pub(crate) fn interface_type_from_program_type(interface_type: ProgramType) -> InterfaceType {
    match interface_type {
        ProgramType::Parameter(name) => InterfaceType::Parameter(name),
        ProgramType::ParameterPointer(name) => InterfaceType::ParameterPointer(name),
        ProgramType::Void => InterfaceType::Void,
        ProgramType::Bool => InterfaceType::Bool,
        ProgramType::VoidPointer => InterfaceType::VoidPointer,
        ProgramType::VoidPointerPointer => InterfaceType::VoidPointerPointer,
        ProgramType::Pointer => InterfaceType::Pointer,
        ProgramType::Int8 => InterfaceType::Int8,
        ProgramType::Int16 => InterfaceType::Int16,
        ProgramType::Int32 => InterfaceType::Int32,
        ProgramType::UInt8 => InterfaceType::UInt8,
        ProgramType::UInt16 => InterfaceType::UInt16,
        ProgramType::UInt32 => InterfaceType::UInt32,
        ProgramType::Int64 => InterfaceType::Int64(LongRank::Long),
        ProgramType::UInt64 => InterfaceType::UInt64(LongRank::Long),
        ProgramType::Int128 => InterfaceType::Int128,
        ProgramType::UInt128 => InterfaceType::UInt128,
        ProgramType::Float32 => InterfaceType::Float32,
        ProgramType::Float64 => InterfaceType::Float64,
        ProgramType::Int8Pointer => InterfaceType::Int8Pointer,
        ProgramType::Int16Pointer => InterfaceType::Int16Pointer,
        ProgramType::UInt16Pointer => InterfaceType::UInt16Pointer,
        ProgramType::Int32Pointer => InterfaceType::Int32Pointer,
        ProgramType::UInt8Pointer => InterfaceType::UInt8Pointer,
        ProgramType::UInt32Pointer => InterfaceType::UInt32Pointer,
        ProgramType::Int64Pointer => InterfaceType::Int64Pointer(LongRank::Long),
        ProgramType::Int128Pointer => InterfaceType::Int128Pointer,
        ProgramType::UInt64Pointer => InterfaceType::UInt64Pointer(LongRank::Long),
        ProgramType::UInt128Pointer => InterfaceType::UInt128Pointer,
        ProgramType::Float32Pointer => InterfaceType::Float32Pointer,
        ProgramType::Float64Pointer => InterfaceType::Float64Pointer,
        ProgramType::Int8PointerPointer => InterfaceType::Int8PointerPointer,
        ProgramType::Int16PointerPointer => InterfaceType::Int16PointerPointer,
        ProgramType::UInt16PointerPointer => InterfaceType::UInt16PointerPointer,
        ProgramType::Int32PointerPointer => InterfaceType::Int32PointerPointer,
        ProgramType::UInt8PointerPointer => InterfaceType::UInt8PointerPointer,
        ProgramType::UInt32PointerPointer => InterfaceType::UInt32PointerPointer,
        ProgramType::Int64PointerPointer => InterfaceType::Int64PointerPointer(LongRank::Long),
        ProgramType::Int128PointerPointer => InterfaceType::Int128PointerPointer,
        ProgramType::UInt64PointerPointer => InterfaceType::UInt64PointerPointer(LongRank::Long),
        ProgramType::UInt128PointerPointer => InterfaceType::UInt128PointerPointer,
        ProgramType::Float32PointerPointer => InterfaceType::Float32PointerPointer,
        ProgramType::Float64PointerPointer => InterfaceType::Float64PointerPointer,
        ProgramType::FunctionPointer(signature) => InterfaceType::FunctionPointer(signature),
        ProgramType::Int8Array(length) => InterfaceType::Int8Array(length),
        ProgramType::Int16Array(length) => InterfaceType::Int16Array(length),
        ProgramType::UInt16Array(length) => InterfaceType::UInt16Array(length),
        ProgramType::Int32Array(length) => InterfaceType::Int32Array(length),
        ProgramType::UInt8Array(length) => InterfaceType::UInt8Array(length),
        ProgramType::UInt32Array(length) => InterfaceType::UInt32Array(length),
        ProgramType::Int64Array(length) => InterfaceType::Int64Array(LongRank::Long, length),
        ProgramType::Int128Array(length) => InterfaceType::Int128Array(length),
        ProgramType::UInt64Array(length) => InterfaceType::UInt64Array(LongRank::Long, length),
        ProgramType::UInt128Array(length) => InterfaceType::UInt128Array(length),
        ProgramType::Float32Array(length) => InterfaceType::Float32Array(length),
        ProgramType::Float64Array(length) => InterfaceType::Float64Array(length),
        ProgramType::PointerArray(element, length) => {
            InterfaceType::PointerArray(element, LongRank::Long, length)
        }
    }
}

pub(super) fn instance_name(
    name: &str,
    type_parameters: &[String],
    substitution: &TypeSubstitution,
) -> Result<String, String> {
    fn type_identity(ty: &ClickType) -> String {
        match ty {
            ClickType::Algebraic(application) if application.rigid => {
                format!("[rigid {}]", application.name)
            }
            ClickType::Algebraic(application) if !application.arguments.is_empty() => format!(
                "{}<{}>",
                application.name,
                application
                    .arguments
                    .iter()
                    .map(type_identity)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            _ => validation::describe_click_type(ty),
        }
    }
    if type_parameters.is_empty() {
        return Ok(name.to_string());
    }
    let arguments = type_parameters
        .iter()
        .map(|parameter| {
            substitution
                .get(parameter)
                .map(|argument| match argument {
                    TypeArgument::Value(value) => type_identity(value),
                    TypeArgument::Struct(_) => argument.describe(),
                })
                .ok_or_else(|| format!("unresolved type parameter `{parameter}`"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!("{name}::<{}>", arguments.join(", ")))
}

pub(super) fn instantiate_function(
    definition: &ClickFunctionDefinition,
    substitution: &TypeSubstitution,
) -> Result<ClickFunctionDefinition, String> {
    let return_type = instantiate_click_type(definition.return_type(), substitution)?;
    let return_object_class = return_type
        .pointer_object_class()
        .or_else(|| definition.return_object_class().cloned());
    Ok(ClickFunctionDefinition {
        name: instance_name(
            definition.name(),
            definition.type_parameters(),
            substitution,
        )?,
        type_parameters: Vec::new(),
        parameters: definition
            .parameters()
            .iter()
            .map(|parameter| instantiate_parameter(parameter, substitution))
            .collect::<Result<Vec<_>, _>>()?,
        return_type,
        return_object_class,
        decreases: definition
            .decreases()
            .map(|expression| instantiate_expression(expression, substitution))
            .transpose()?,
        body: definition
            .body()
            .map(|body| instantiate_expression(body, substitution))
            .transpose()?,
    })
}

pub(super) fn instantiate_function_for_surface_call_with_variables(
    definition: &ClickFunctionDefinition,
    arguments: &[ContractExpression],
    variables: &BTreeMap<String, ClickType>,
) -> Result<ClickFunctionDefinition, String> {
    if definition.type_parameters().is_empty() {
        return Ok(definition.clone());
    }
    let argument_types = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| match parameter.click_type() {
            ClickType::Resource | ClickType::Program(InterfaceType::ParameterPointer(_)) => {
                syntactic_expression_type(argument, variables)
            }
            ClickType::Program(_) | ClickType::CObjectPointer { .. } => {
                Some(parameter.click_type().clone())
            }
            ClickType::Algebraic(_)
            | ClickType::Parameter(_)
            | ClickType::Proposition
            | ClickType::Function { .. }
            | ClickType::Integer => syntactic_expression_type(argument, variables),
        })
        .collect::<Vec<_>>();
    let substitution = infer_type_substitution(
        "function",
        definition.name(),
        definition.type_parameters(),
        definition
            .parameters()
            .iter()
            .map(|parameter| parameter.click_type().clone()),
        argument_types,
    )?;
    instantiate_function(definition, &substitution)
}

/// An explicit cast fixes the argument's logical C type. Its destination
/// spelling is not evidence that the original object has that class; the
/// existing kernel argument/constructor check still consumes the value.
pub(super) fn explicit_cast_click_type(expression: &ContractExpression) -> Option<ClickType> {
    let (ContractExpression::ProgramExpression(lowered)
    | ContractExpression::CUnary { lowered, .. }) = expression
    else {
        return None;
    };
    let ProgramExpression::Cast {
        target_type,
        pointee_struct,
        ..
    } = lowered
    else {
        return None;
    };
    let interface_type = interface_type_from_program_type(*target_type);
    Some(match pointee_struct {
        Some(struct_name) if interface_type.is_pointer() => ClickType::CObjectPointer {
            interface_type,
            struct_name: struct_name.clone(),
        },
        _ => ClickType::Program(interface_type),
    })
}

pub(super) fn click_type_from_program_value(value: &ProgramValue) -> ClickType {
    let interface_type = interface_type_from_program_type(value.program_type());
    if let ProgramValue::Pointer(pointer) = value
        && let Some(class) = pointer.object_class()
    {
        return ClickType::from_object_pointer_class(interface_type, &class);
    }
    ClickType::Program(interface_type)
}

pub(super) fn default_numeral_click_type(expression: &ContractExpression) -> Option<ClickType> {
    let ProgramExpression::Value(value) = contract_expression_as_program_expression(expression)?
    else {
        return None;
    };
    Some(click_type_from_program_value(&value))
}

pub(super) fn syntactic_expression_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, ClickType>,
) -> Option<ClickType> {
    if let Some(cast_type) = explicit_cast_click_type(expression) {
        return Some(cast_type);
    }
    match expression {
        ContractExpression::IntegerContext(_) => Some(ClickType::Integer),

        ContractExpression::Lambda {
            parameters, result, ..
        } => Some(lambdas::signature(parameters, result)),
        ContractExpression::Apply { function, .. } => {
            match syntactic_expression_type(function, variables)? {
                ClickType::Function { result, .. } => Some(*result),
                _ => None,
            }
        }

        ContractExpression::Resource(_) => Some(ClickType::Resource),
        ContractExpression::IntegerLiteral(_) | ContractExpression::Negate(_) => {
            default_numeral_click_type(expression)
        }
        ContractExpression::AlgebraicVariable { algebraic_type, .. }
        | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
            Some(ClickType::Algebraic(algebraic_type.clone()))
        }
        ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
            Some(click_type_from_program_value(value))
        }
        ContractExpression::Binding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => variables.get(name).cloned(),
        ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::SliceLength(_),
        )) => Some(ClickType::Program(InterfaceType::UInt64(LongRank::Long))),
        ContractExpression::Old(inner)
        | ContractExpression::Exact(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => syntactic_expression_type(inner, variables),
        ContractExpression::Let { body, .. } => syntactic_expression_type(body, variables),
        _ => None,
    }
}

pub(super) fn concrete_variable_types(
    values: &ProgramValueBindings,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
) -> BTreeMap<String, ClickType> {
    values
        .iter()
        .map(|(name, value)| (name.clone(), click_type_from_program_value(value)))
        .chain(algebraic_values.iter().map(|(name, value)| {
            (
                name.clone(),
                click_type_from_algebraic_value_type(&value.algebraic_type.value_type()),
            )
        }))
        .collect()
}

pub(super) fn instantiate_predicate(
    definition: &PredicateDefinition,
    substitution: &TypeSubstitution,
) -> Result<PredicateDefinition, String> {
    Ok(PredicateDefinition {
        name: instance_name(
            definition.name(),
            definition.type_parameters(),
            substitution,
        )?,
        type_parameters: Vec::new(),
        parameters: definition
            .parameters()
            .iter()
            .map(|parameter| instantiate_parameter(parameter, substitution))
            .collect::<Result<Vec<_>, _>>()?,
        body: instantiate_proposition(definition.body(), substitution)?,
    })
}

pub(super) fn instantiate_predicate_for_surface_call(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
    variables: &BTreeMap<String, ClickType>,
) -> Result<PredicateDefinition, String> {
    if definition.type_parameters().is_empty() {
        return Ok(definition.clone());
    }
    let argument_types = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| match parameter.click_type() {
            ClickType::Resource | ClickType::Program(InterfaceType::ParameterPointer(_)) => {
                syntactic_expression_type(argument, variables)
            }
            ClickType::Program(_) | ClickType::CObjectPointer { .. } => {
                Some(parameter.click_type().clone())
            }
            ClickType::Algebraic(_)
            | ClickType::Parameter(_)
            | ClickType::Proposition
            | ClickType::Function { .. }
            | ClickType::Integer => syntactic_expression_type(argument, variables),
        })
        .collect::<Vec<_>>();
    let substitution = infer_type_substitution(
        "predicate",
        definition.name(),
        definition.type_parameters(),
        definition
            .parameters()
            .iter()
            .map(|parameter| parameter.click_type().clone()),
        argument_types,
    )?;
    instantiate_predicate(definition, &substitution)
}

pub(super) fn instantiate_theorem(
    definition: &TheoremDefinition,
    substitution: &TypeSubstitution,
) -> Result<TheoremDefinition, String> {
    instantiate_theorem_with_proof(definition, substitution, true)
}

/// Instantiate a checked declaration for application without visiting its proof.
pub(super) fn instantiate_theorem_statement(
    definition: &TheoremDefinition,
    substitution: &TypeSubstitution,
) -> Result<TheoremDefinition, String> {
    if definition.type_parameters().is_empty() {
        return Ok(TheoremDefinition {
            axiom: definition.axiom,
            generic_pointer_parameters: definition.generic_pointer_parameters.clone(),
            body: parser::DeclarationBody::default(),
            name: definition.name.clone(),
            type_parameters: Vec::new(),
            parameters: definition.parameters.clone(),
            executes: definition.executes.clone(),
            requires: definition.requires.clone(),
            ensures: definition
                .ensures
                .iter()
                .map(|ensure| EnsureClause {
                    proof_bindings: ensure.proof_bindings.clone(),
                    name: ensure.name.clone(),
                    ensure: ensure.ensure.clone(),
                    proof: SourceProof::Default,
                    borrowed: ensure.borrowed,
                    view_source: ensure.view_source,
                    condition: ensure.condition.clone(),
                })
                .collect(),
            ensure_claim_ids: definition.ensure_claim_ids.clone(),
        });
    }
    instantiate_theorem_with_proof(definition, substitution, false)
}

fn instantiate_theorem_with_proof(
    definition: &TheoremDefinition,
    substitution: &TypeSubstitution,
    include_proof: bool,
) -> Result<TheoremDefinition, String> {
    let parameters = definition
        .parameters()
        .iter()
        .map(|parameter| instantiate_parameter(parameter, substitution))
        .collect::<Result<Vec<_>, _>>()?;
    let algebraic_parameters = parameters
        .iter()
        .enumerate()
        .filter_map(|(binder_index, parameter)| {
            let ClickType::Algebraic(algebraic_type) = parameter.click_type() else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ContractExpression::AlgebraicVariable {
                    name: parameter.name().into(),
                    algebraic_type: algebraic_type.clone(),
                    binder_index,
                },
            ))
        })
        .collect::<BTreeMap<_, _>>();
    Ok(TheoremDefinition {
        axiom: definition.axiom,
        generic_pointer_parameters: definition.generic_pointer_parameters.clone(),
        body: if include_proof {
            definition.parsed_body().clone()
        } else {
            parser::DeclarationBody::default()
        },
        executes: definition.executes.clone(),
        name: instance_name(
            definition.name(),
            definition.type_parameters(),
            substitution,
        )?,
        type_parameters: Vec::new(),
        parameters,
        requires: definition
            .requires()
            .iter()
            .map(|requirement| {
                instantiate_requirement(requirement, substitution, &algebraic_parameters)
            })
            .collect::<Result<Vec<_>, _>>()?,
        ensures: definition
            .ensures()
            .iter()
            .map(|ensure| {
                instantiate_ensure_clause(
                    ensure,
                    substitution,
                    &algebraic_parameters,
                    include_proof,
                )
            })
            .collect::<Result<Vec<_>, _>>()?,
        ensure_claim_ids: definition.ensure_claim_ids.clone(),
    })
}

fn instantiate_requirement(
    requirement: &Requirement,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<Requirement, String> {
    Ok(match requirement {
        Requirement::Proposition(proposition) => {
            Requirement::Proposition(substitute_click_proposition(
                &instantiate_proposition(proposition, substitution)?,
                algebraic_parameters,
            )?)
        }
        requirement => requirement.clone(),
    })
}

fn instantiate_ensure_clause(
    ensure: &EnsureClause,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
    include_proof: bool,
) -> Result<EnsureClause, String> {
    let ensure_value = match ensure.ensure() {
        Ensure::Proposition(proposition) => Ensure::Proposition(substitute_click_proposition(
            &instantiate_proposition(proposition, substitution)?,
            algebraic_parameters,
        )?),
        resource @ Ensure::Resource(_) => resource.clone(),
    };
    Ok(EnsureClause {
        proof_bindings: ensure
            .proof_bindings
            .iter()
            .map(|(name, click_type, value)| {
                Ok((
                    name.clone(),
                    click_type
                        .as_ref()
                        .map(|click_type| instantiate_click_type(click_type, substitution))
                        .transpose()?,
                    substitute_contract_expression(
                        &instantiate_expression(value, substitution)?,
                        algebraic_parameters,
                    )?,
                ))
            })
            .collect::<Result<_, String>>()?,
        name: ensure.name.clone(),
        ensure: ensure_value,
        proof: if include_proof {
            instantiate_source_proof(ensure.proof(), substitution, algebraic_parameters)?
        } else {
            SourceProof::Default
        },
        borrowed: ensure.borrowed,
        view_source: ensure.view_source,
        condition: ensure
            .condition()
            .map(|condition| {
                substitute_click_proposition(
                    &instantiate_proposition(condition, substitution)?,
                    algebraic_parameters,
                )
            })
            .transpose()?,
    })
}

fn instantiate_source_proof(
    proof: &SourceProof,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<SourceProof, String> {
    Ok(match proof {
        SourceProof::Default => SourceProof::Default,
        SourceProof::Tactic(tactic) => SourceProof::Tactic(*tactic),
        SourceProof::Script(tactics) => SourceProof::Script(
            tactics
                .iter()
                .map(|tactic| instantiate_proof_tactic(tactic, substitution, algebraic_parameters))
                .collect::<Result<Vec<_>, _>>()?,
        ),
    })
}

fn instantiate_theorem_application(
    application: &TheoremApplication,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<TheoremApplication, String> {
    Ok(TheoremApplication {
        name: application.name.clone(),
        arguments: application
            .arguments
            .iter()
            .map(|argument| {
                substitute_contract_expression(
                    &instantiate_expression(argument, substitution)?,
                    algebraic_parameters,
                )
            })
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn instantiate_function_application(
    application: &ClickFunctionApplication,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<ClickFunctionApplication, String> {
    Ok(ClickFunctionApplication {
        name: application.name.clone(),
        arguments: application
            .arguments
            .iter()
            .map(|argument| {
                substitute_contract_expression(
                    &instantiate_expression(argument, substitution)?,
                    algebraic_parameters,
                )
            })
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn instantiate_proof_tactics(
    tactics: &[ProofTactic],
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<Vec<ProofTactic>, String> {
    tactics
        .iter()
        .map(|tactic| instantiate_proof_tactic(tactic, substitution, algebraic_parameters))
        .collect()
}

fn instantiate_proof_tactic(
    tactic: &ProofTactic,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<ProofTactic, String> {
    crate::instrumentation::record_deterministic_work(1);
    let expression = |value: &ContractExpression| {
        substitute_contract_expression(
            &instantiate_expression(value, substitution)?,
            algebraic_parameters,
        )
    };
    let proposition = |value: &ClickProposition| {
        substitute_click_proposition(
            &instantiate_proposition(value, substitution)?,
            algebraic_parameters,
        )
    };
    Ok(match tactic {
        ProofTactic::Match(proof_match) => ProofTactic::Match(std::sync::Arc::new(ProofMatch {
            scrutinee: expression(&proof_match.scrutinee)?,
            ensuring: proof_match.ensuring.clone(),
            arms: proof_match
                .arms
                .iter()
                .map(|arm| {
                    let mut scoped_parameters = algebraic_parameters.clone();
                    for binding in &arm.bindings {
                        scoped_parameters.remove(binding);
                    }
                    Ok(ProofInductionArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        tactics: instantiate_proof_tactics(
                            &arm.tactics,
                            substitution,
                            &scoped_parameters,
                        )?,
                    })
                })
                .collect::<Result<_, String>>()?,
        })),
        ProofTactic::UnfoldFunction(application) => ProofTactic::UnfoldFunction(
            instantiate_function_application(application, substitution, algebraic_parameters)?,
        ),
        ProofTactic::ApplyInduction {
            hypothesis,
            arguments,
        } => ProofTactic::ApplyInduction {
            hypothesis: hypothesis.clone(),
            arguments: arguments
                .iter()
                .map(&expression)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::ApplyTheorem(application) => ProofTactic::ApplyTheorem(
            instantiate_theorem_application(application, substitution, algebraic_parameters)?,
        ),
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => ProofTactic::ApplyTheoremUsing {
            application: instantiate_theorem_application(
                application,
                substitution,
                algebraic_parameters,
            )?,
            premises: premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::IntroBlock { binder, body } => ProofTactic::IntroBlock {
            binder: binder.clone(),
            body: instantiate_proof_tactics(body, substitution, algebraic_parameters)?,
        },
        ProofTactic::Have(have) => ProofTactic::Have(ProofHave {
            proposition: proposition(&have.proposition)?,
            proof: instantiate_source_proof(&have.proof, substitution, algebraic_parameters)?,
        }),
        ProofTactic::If(proof_if) => ProofTactic::If(ProofIf {
            condition: proposition(&proof_if.condition)?,
            ensuring: proof_if.ensuring.clone(),
            then_tactics: instantiate_proof_tactics(
                &proof_if.then_tactics,
                substitution,
                algebraic_parameters,
            )?,
            else_tactics: instantiate_proof_tactics(
                &proof_if.else_tactics,
                substitution,
                algebraic_parameters,
            )?,
        }),
        ProofTactic::CloseInvariantsBy(body) => ProofTactic::CloseInvariantsBy(
            instantiate_proof_tactics(body, substitution, algebraic_parameters)?,
        ),
        ProofTactic::StepProved { step, proof } => ProofTactic::StepProved {
            step: Box::new(instantiate_proof_tactic(
                step,
                substitution,
                algebraic_parameters,
            )?),
            proof: match proof {
                StepProof::By(body) => StepProof::By(instantiate_proof_tactics(
                    body,
                    substitution,
                    algebraic_parameters,
                )?),
                StepProof::Requires(entries) => StepProof::Requires(
                    entries
                        .iter()
                        .map(|entry| {
                            Ok(StepRequirement {
                                label: entry.label.clone(),
                                have: ProofHave {
                                    proposition: proposition(&entry.have.proposition)?,
                                    proof: instantiate_source_proof(
                                        &entry.have.proof,
                                        substitution,
                                        algebraic_parameters,
                                    )?,
                                },
                            })
                        })
                        .collect::<Result<_, String>>()?,
                ),
            },
        },
        ProofTactic::All(all) => ProofTactic::All(ProofAll {
            arms: all
                .arms
                .iter()
                .map(|arm| {
                    Ok(ProofAllArm {
                        proposition: proposition(&arm.proposition)?,
                        tactics: instantiate_proof_tactics(
                            &arm.tactics,
                            substitution,
                            algebraic_parameters,
                        )?,
                    })
                })
                .collect::<Result<_, String>>()?,
        }),
        ProofTactic::Both(both) => ProofTactic::Both(ProofBoth {
            left_tactics: instantiate_proof_tactics(
                &both.left_tactics,
                substitution,
                algebraic_parameters,
            )?,
            right_tactics: instantiate_proof_tactics(
                &both.right_tactics,
                substitution,
                algebraic_parameters,
            )?,
        }),
        ProofTactic::Cases(cases) => ProofTactic::Cases(cases.try_map(
            |assumption| proposition(assumption),
            |tactics| instantiate_proof_tactics(tactics, substitution, algebraic_parameters),
        )?),
        ProofTactic::ApplyFact(fact) => ProofTactic::ApplyFact(proposition(fact)?),
        ProofTactic::ApplyFactUsing { fact, premises } => ProofTactic::ApplyFactUsing {
            fact: proposition(fact)?,
            premises: premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::ArithmeticUsing(premises) => ProofTactic::ArithmeticUsing(
            premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ProofTactic::CompatibilityNormalize(premises) => ProofTactic::CompatibilityNormalize(
            premises
                .as_ref()
                .map(|premises| {
                    premises
                        .iter()
                        .map(proposition)
                        .collect::<Result<Vec<_>, _>>()
                })
                .transpose()?,
        ),
        ProofTactic::NormalizeUsing(premises) => ProofTactic::NormalizeUsing(
            premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ProofTactic::Contradiction(value) => ProofTactic::Contradiction(proposition(value)?),
        ProofTactic::Rewrite(value) => ProofTactic::Rewrite(proposition(value)?),
        ProofTactic::Transport { source, target } => ProofTactic::Transport {
            source: proposition(source)?,
            target: proposition(target)?,
        },
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => ProofTactic::TransportUsing {
            source: proposition(source)?,
            target: proposition(target)?,
            premises: premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::Instantiate {
            quantified,
            arguments,
        } => ProofTactic::Instantiate {
            quantified: proposition(quantified)?,
            arguments: arguments.iter().map(expression).collect::<Result<_, _>>()?,
        },
        ProofTactic::SolveUsing(using) => ProofTactic::SolveUsing(ProofSolveUsing {
            premises: using
                .premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        tactic => tactic.clone(),
    })
}

fn instantiate_parameter(
    parameter: &FunctionParameter,
    substitution: &TypeSubstitution,
) -> Result<FunctionParameter, String> {
    let click_type = instantiate_click_type(parameter.click_type(), substitution)?;
    let struct_name = match &click_type {
        ClickType::CObjectPointer { struct_name, .. } => Some(struct_name.clone()),
        _ => parameter.struct_name.clone(),
    };
    Ok(FunctionParameter {
        slice_length: parameter.slice_length.clone(),
        click_type,
        name: parameter.name.clone(),
        struct_name,
        function_pointer_signature: parameter.function_pointer_signature.clone(),
        constant: parameter.constant,
        pointee_constant: parameter.pointee_constant,
        reference: false,
    })
}

fn instantiate_expression(
    expression: &ContractExpression,
    substitution: &TypeSubstitution,
) -> Result<ContractExpression, String> {
    let recurse =
        |expression: &ContractExpression| instantiate_expression(expression, substitution);
    Ok(match expression {
        ContractExpression::Proposition(proposition) => ContractExpression::Proposition(Box::new(
            instantiate_proposition(proposition, substitution)?,
        )),

        ContractExpression::Lambda {
            parameters,
            result,
            body,
        } => ContractExpression::Lambda {
            parameters: parameters
                .iter()
                .map(|(name, ty)| Ok((name.clone(), instantiate_click_type(ty, substitution)?)))
                .collect::<Result<_, String>>()?,
            result: instantiate_click_type(result, substitution)?,
            body: Box::new(recurse(body)?),
        },
        ContractExpression::Apply {
            function,
            arguments,
        } => ContractExpression::Apply {
            function: Box::new(recurse(function)?),
            arguments: arguments.iter().map(recurse).collect::<Result<_, _>>()?,
        },

        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => ContractExpression::AlgebraicConstructor {
            algebraic_type: instantiate_algebraic_type(algebraic_type, substitution)?,
            variant: variant.clone(),
            arguments: arguments
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ContractExpression::AlgebraicVariable {
            name,
            algebraic_type,
            binder_index,
        } => ContractExpression::AlgebraicVariable {
            name: name.clone(),
            algebraic_type: instantiate_algebraic_type(algebraic_type, substitution)?,
            binder_index: *binder_index,
        },
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            ContractExpression::AlgebraicMatch {
                scrutinee: Box::new(recurse(scrutinee)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(AlgebraicMatchArm {
                            type_name: arm.type_name.clone(),
                            variant: arm.variant.clone(),
                            bindings: arm.bindings.clone(),
                            body: recurse(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            }
        }
        ContractExpression::SequenceLiteral(elements) => ContractExpression::SequenceLiteral(
            elements.iter().map(recurse).collect::<Result<_, _>>()?,
        ),
        ContractExpression::SequenceConcat(left, right) => {
            ContractExpression::SequenceConcat(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Old(inner) => ContractExpression::Old(Box::new(recurse(inner)?)),
        ContractExpression::Exact(inner) => ContractExpression::Exact(Box::new(recurse(inner)?)),
        ContractExpression::At {
            selector,
            expression,
        } => ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(recurse(expression)?),
        },
        ContractExpression::Add(left, right) => {
            ContractExpression::Add(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Subtract(left, right) => {
            ContractExpression::Subtract(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Multiply(left, right) => {
            ContractExpression::Multiply(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Divide(left, right) => {
            ContractExpression::Divide(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Remainder(left, right) => {
            ContractExpression::Remainder(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::ShiftLeft(left, right) => {
            ContractExpression::ShiftLeft(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::RustShiftLeft(left, right) => {
            ContractExpression::RustShiftLeft(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::ShiftRight(left, right) => {
            ContractExpression::ShiftRight(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::RustShiftRight(left, right) => {
            ContractExpression::RustShiftRight(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseAnd(left, right) => {
            ContractExpression::BitwiseAnd(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseOr(left, right) => {
            ContractExpression::BitwiseOr(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseXor(left, right) => {
            ContractExpression::BitwiseXor(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Index(left, right) => {
            ContractExpression::Index(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseNot(inner) => {
            ContractExpression::BitwiseNot(Box::new(recurse(inner)?))
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => ContractExpression::If {
            condition: Box::new(instantiate_proposition(condition, substitution)?),
            then_branch: Box::new(recurse(then_branch)?),
            else_branch: Box::new(recurse(else_branch)?),
        },
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => ContractExpression::RangeFold {
            start: Box::new(recurse(start)?),
            end: Box::new(recurse(end)?),
            initial: Box::new(recurse(initial)?),
            accumulator: accumulator.clone(),
            item: item.clone(),
            body: Box::new(recurse(body)?),
        },
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => ContractExpression::Let {
            name: name.clone(),
            click_type: click_type
                .as_ref()
                .map(|click_type| instantiate_click_type(click_type, substitution))
                .transpose()?,
            value: Box::new(recurse(value)?),
            body: Box::new(recurse(body)?),
        },
        ContractExpression::Call { name, arguments } => ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        },
        expression => expression.clone(),
    })
}

fn instantiate_proposition(
    proposition: &ClickProposition,
    substitution: &TypeSubstitution,
) -> Result<ClickProposition, String> {
    let expression =
        |expression: &ContractExpression| instantiate_expression(expression, substitution);
    let recurse =
        |proposition: &ClickProposition| instantiate_proposition(proposition, substitution);
    Ok(match proposition {
        ClickProposition::Value(value) => ClickProposition::Value(expression(value)?),

        ClickProposition::Comparison {
            operator,
            left,
            right,
        } => ClickProposition::Comparison {
            operator: *operator,
            left: expression(left)?,
            right: expression(right)?,
        },
        ClickProposition::FloatClassification {
            classification,
            expression: value,
        } => ClickProposition::FloatClassification {
            classification: *classification,
            expression: expression(value)?,
        },
        ClickProposition::Defined { expression: value } => ClickProposition::Defined {
            expression: expression(value)?,
        },
        ClickProposition::IsA { class, pointer } => ClickProposition::IsA {
            class: class.clone(),
            pointer: expression(pointer)?,
        },
        ClickProposition::At {
            selector,
            proposition,
        } => ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(recurse(proposition)?),
        },
        ClickProposition::And(left, right) => {
            ClickProposition::And(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ClickProposition::Or(left, right) => {
            ClickProposition::Or(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ClickProposition::Not(body) => ClickProposition::Not(Box::new(recurse(body)?)),
        ClickProposition::Implies(left, right) => {
            ClickProposition::Implies(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ClickProposition::ForAll {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => ClickProposition::ForAll {
            click_type: instantiate_click_type(interface_type, substitution)?,
            name: name.clone(),
            written_name: written_name.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::Exists {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => ClickProposition::Exists {
            click_type: instantiate_click_type(interface_type, substitution)?,
            name: name.clone(),
            written_name: written_name.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item,
            body,
        } => ClickProposition::RangeAll {
            start: expression(start)?,
            end: expression(end)?,
            item: item.clone(),
            written_item: written_item.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item,
            body,
        } => ClickProposition::RangeAny {
            start: expression(start)?,
            end: expression(end)?,
            item: item.clone(),
            written_item: written_item.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::PredicateCall { name, arguments } => ClickProposition::PredicateCall {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(expression)
                .collect::<Result<Vec<_>, _>>()?,
        },
        proposition => proposition.clone(),
    })
}

#[cfg(test)]
mod theorem_statement_tests {
    use super::*;

    #[test]
    fn application_instantiates_clauses_but_omits_proof_and_proof_locations() {
        let file = crate::surface::parse("theorem identity<T>(x: T) { requires x == x; ensures x == x by { have x == x by close(); close(); } }").unwrap();
        let definition = &file.theorem_definitions()[0];
        let substitution =
            BTreeMap::from([("T".into(), ClickType::Program(InterfaceType::Int32).into())]);
        let declaration = instantiate_theorem(definition, &substitution).unwrap();
        let statement = instantiate_theorem_statement(definition, &substitution).unwrap();
        assert_eq!(declaration.parameters(), statement.parameters());
        assert_eq!(declaration.requires(), statement.requires());
        assert_eq!(
            declaration.ensures()[0].ensure(),
            statement.ensures()[0].ensure()
        );
        assert!(matches!(
            declaration.ensures()[0].proof(),
            SourceProof::Script(_)
        ));
        assert!(matches!(
            statement.ensures()[0].proof(),
            SourceProof::Default
        ));
        assert!(statement.parsed_body().proof_clauses.is_empty());
        assert!(statement.parsed_body().implicit_proofs.is_empty());
    }
}
