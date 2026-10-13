//! Direct lowering from the pinned C++ semantic artifact to kernel execution.
//!
//! This adapter consumes Clang's already-typed nodes. It does not print C++ as
//! C, invoke the C parser, or infer types from source spellings. The first
//! slice represents `int&` and `const int&` as address-valued kernel parameters;
//! every C++ lvalue-to-rvalue conversion becomes a typed load through that
//! address and assignment writes the referent without reseating the reference.
//! Mutable `int*` parameters remain distinct from references in the semantic
//! artifact, while both reuse the kernel's checked address and memory rules.
//! Function-body scalar locals use the kernel's ordinary declaration,
//! assignment, and call-result statements.

use super::lifetime::{LifetimePlan, LifetimeState};
use super::names::ResolvedNames;
use super::scalar::{self, Scalar, ScalarKind};
use std::collections::BTreeMap;

use super::{
    CppBinaryOperator, CppCallArgument, CppCleanup, CppCondition, CppConstant,
    CppExceptionBehavior, CppExpression, CppFieldReference, CppFunction, CppFunctionKind,
    CppInitializer, CppPlace, CppPlaceReference, CppStatement, CppType, PreparedCppImport,
};
use crate::kernel::{
    CAggregateLayout, CExpression, CFunction, CStatement, CType, LoadSourceId, LoadSourceOwnerId,
    c_add, c_allocate_aggregate_destination, c_and, c_assign, c_call, c_call_assign, c_cast,
    c_checked_object_address, c_copy_aggregate, c_declare, c_declare_aggregate,
    c_declare_initialized, c_declare_with_all_qualifiers, c_divide, c_end_automatic_lifetimes,
    c_equal, c_function, c_greater_equal, c_greater_than, c_if, c_less_equal, c_less_than,
    c_multiply, c_not_equal, c_parameter, c_pointer_offset_bytes, c_remainder, c_return, c_seq,
    c_skip, c_subtract, c_try_catch_int32, c_try_catch_int32_with_cleanup, c_typed_load,
    c_typed_load_with_source, c_typed_store, c_variable, int32,
};

/// One kernel function together with the immutable semantic artifact that
/// produced it. Keeping the source artifact attached retains Clang declaration
/// identities and spans even though they are not part of kernel equality.
#[derive(Clone, Debug)]
pub struct LoweredCppFunction {
    source: PreparedCppImport,
    names: ResolvedNames,
    function: CFunction,
    reachable_functions: Vec<CFunction>,
    execution: std::sync::Arc<crate::languages::PreparedExecution>,
}

impl LoweredCppFunction {
    /// Proof-facing name for a resolved Clang declaration identity.
    pub fn contract_name(&self, declaration_id: &str) -> Option<&str> {
        self.names.get(declaration_id)
    }

    pub(crate) fn prepared_execution(&self) -> std::sync::Arc<crate::languages::PreparedExecution> {
        self.execution.clone()
    }
    pub fn contract_functions(&self) -> &[crate::languages::c::syntax::C0Function] {
        &self.execution.functions
    }

    pub fn record_layouts(&self) -> &BTreeMap<String, crate::languages::c::syntax::C0StructLayout> {
        &self.execution.layouts
    }

    pub fn source(&self) -> &PreparedCppImport {
        &self.source
    }

    pub fn source_function(&self) -> &CppFunction {
        &self.source.export().function
    }

    pub fn kernel_function(&self) -> &CFunction {
        &self.function
    }

    pub fn reachable_kernel_functions(&self) -> &[CFunction] {
        &self.reachable_functions
    }
}

/// Normalize the pinned C++ artifact into checked execution and its prepared
/// contract-facing metadata.
pub fn lower_import(import: &PreparedCppImport) -> Result<LoweredCppFunction, String> {
    let names = ResolvedNames::new(
        std::iter::once(&import.export().function)
            .chain(&import.export().reachable_functions)
            .map(|function| (function.declaration_id.as_str(), function.name.as_str())),
    )?;
    // Build immutable inventories once; every function borrows the same indexes.
    let records = super::schema::RecordIndex::new(
        import
            .export()
            .records
            .iter()
            .map(|record| {
                crate::instrumentation::record_deterministic_work(1);
                (record.declaration_id.clone(), record)
            })
            .collect::<BTreeMap<_, _>>(),
    );
    let constants = import
        .export()
        .constants
        .iter()
        .map(|constant| {
            crate::instrumentation::record_deterministic_work(1);
            (constant.declaration_id.as_str(), constant)
        })
        .collect::<BTreeMap<_, _>>();
    let layouts = super::interface::prepare_layouts(import)?;
    // One checked kernel definition per native record for the imported graph.
    // Member selectors and interface requirements share immutable indexes.
    let kernel_layouts = layouts
        .iter()
        .map(|(name, layout)| {
            (
                name.clone(),
                std::sync::Arc::new(layout.to_kernel_aggregate_layout()),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let function = lower_function(
        import,
        &import.export().function,
        &names,
        &records,
        &constants,
        &layouts,
        &kernel_layouts,
    )?;
    let reachable_functions = import
        .export()
        .reachable_functions
        .iter()
        .map(|source| {
            lower_function(
                import,
                source,
                &names,
                &records,
                &constants,
                &layouts,
                &kernel_layouts,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let library_contracts = super::standard_library::contracts(import, &names)?;
    let execution = std::sync::Arc::new(super::interface::prepare(
        import,
        &function,
        &reachable_functions,
        layouts,
        library_contracts,
    )?);
    Ok(LoweredCppFunction {
        execution,
        names,
        source: import.clone(),
        function,
        reachable_functions,
    })
}

fn lower_function(
    import: &PreparedCppImport,
    source: &CppFunction,
    names: &ResolvedNames,
    records: &super::schema::RecordIndex<'_>,
    constants: &BTreeMap<&str, &CppConstant>,
    layouts: &BTreeMap<String, crate::languages::c::syntax::C0StructLayout>,
    kernel_layouts: &BTreeMap<String, std::sync::Arc<CAggregateLayout>>,
) -> Result<CFunction, String> {
    let mut declared_places = Vec::new();
    collect_declared_places(&source.body, &mut declared_places);
    let places = source
        .parameters
        .iter()
        .chain(declared_places)
        .map(|parameter| (parameter.declaration_id.as_str(), parameter))
        .collect::<BTreeMap<_, _>>();
    let reference_parameters = source
        .parameters
        .iter()
        .enumerate()
        .filter(|(index, parameter)| is_reference_parameter(*index, parameter))
        .map(|(_, parameter)| parameter.declaration_id.as_str())
        // A local of reference type is carried the same way: the pointer is
        // named for the address it holds, and the local's own name is the
        // referent a proof reads.
        .chain(
            places
                .values()
                .filter(|place| is_reference_local(place))
                .map(|place| place.declaration_id.as_str()),
        )
        .collect::<std::collections::BTreeSet<_>>();
    let parameters = source
        .parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            if is_receiver(index, parameter) {
                let mut receiver = parameter.clone();
                receiver.name = RECEIVER_NAME.to_string();
                return lower_parameter(&receiver, layouts);
            }
            if !is_reference_parameter(index, parameter) {
                return lower_parameter(parameter, layouts);
            }
            let mut carrier = parameter.clone();
            carrier.name = reference_carrier_name(&parameter.name);
            lower_parameter(&carrier, layouts)
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut context = LoweringContext {
        receiver: source
            .parameters
            .first()
            .filter(|parameter| is_receiver(0, parameter))
            .map(|parameter| parameter.declaration_id.as_str()),
        reference_parameters,
        source_unit: import.logical_source(),
        function_name: names.require(&source.declaration_id)?,
        names,
        source_names: places.values().map(|place| place.name.as_str()).collect(),
        next_call_capture: 0,
        full_expression_records: Vec::new(),
        places,
        records,
        constants,
        kernel_layouts,
        next_load_occurrence: 0,
        return_capture_name: return_capture_name(source),
        nested_capture_name: fresh_internal_name(source, "__click_cpp_nested_value"),
        unwind_exception_name: fresh_internal_name(source, "__click_cpp_unwind_exception"),
        unwind_cleanups: matches!(
            import.export().exception_behavior,
            CppExceptionBehavior::ScalarInt32
        ),
    };
    let lifetimes = LifetimePlan::new(&source.body, |id| context.records.get(id).copied())?;
    let body = context.lower_sequence_with_lifetimes(
        &source.body,
        &lifetimes,
        &mut LifetimeState::default(),
        0,
    )?;
    if !context.full_expression_records.is_empty() {
        return Err(
            "C++ record argument temporaries escaped their full-expression lowering".into(),
        );
    }
    let return_type = match &source.function_kind {
        CppFunctionKind::Constructor { .. } | CppFunctionKind::Destructor { .. } => CType::Void,
        _ if source.return_type == CppType::Void => CType::Void,
        _ if matches!(source.return_type, CppType::Record { .. }) => CType::Int32Pointer,
        _ => cpp_return_scalar_type(&source.return_type)?,
    };
    let return_constant = matches!(&source.return_type, CppType::LvalueReference { pointee } if is_const_int32(pointee));
    let mut function = c_function(
        return_type,
        names.require(&source.declaration_id)?.to_owned(),
        parameters,
        body,
    )
    .with_typed_access_policy(crate::kernel::CTypedAccessPolicy::NativeObjectOnly)
    .with_return_pointee_constant(return_constant)
    .with_scalar_object_inputs(
        source
            .parameters
            .iter()
            .enumerate()
            .filter_map(|(parameter_index, parameter)| {
                let CppType::LvalueReference { pointee } = &parameter.value_type else {
                    return None;
                };
                let element_type = if is_mutable_int32(pointee) || is_const_int32(pointee) {
                    CType::Int32
                } else if is_const_int64(pointee) {
                    CType::Int64
                } else {
                    // Record references need their own nominal object boundary.
                    return None;
                };
                Some(crate::kernel::CScalarObjectInput {
                    parameter_index,
                    element_type,
                })
            })
            .collect(),
    );
    function = function.with_aggregate_object_inputs(
        source
            .parameters
            .iter()
            .enumerate()
            .filter_map(|(parameter_index, parameter)| {
                let CppType::LvalueReference { pointee } = &parameter.value_type else {
                    return None;
                };
                let CppType::Record { name, .. } = pointee.as_ref() else {
                    return None;
                };
                Some(context.record_layout_arc(name).map(|layout| {
                    crate::kernel::CAggregateObjectInput {
                        parameter_index,
                        layout,
                    }
                }))
            })
            .collect::<Result<Vec<_>, String>>()?,
    );
    if let CppFunctionKind::Constructor { record_name, .. } = &source.function_kind {
        function = function.with_construction_parameter(0, context.record_layout(record_name)?);
    }
    if let CppType::Record { name, .. } = &source.return_type {
        function = if super::construction::is_construction_return(source) {
            function.with_construction_return(context.record_layout(name)?)
        } else {
            function.with_return_aggregate_layout(context.record_layout(name)?)
        };
    }
    super::library_models::implementation(import, source, function, kernel_layouts)
}

pub(super) use crate::languages::c::syntax::reference_carrier_name;

/// The name a sidecar gives a member function's receiver: the pointer
/// `this`, as in C++.
pub(super) const RECEIVER_NAME: &str = "this";

/// Whether a parameter is a member function's receiver. The exporter
/// delivers it first, as a reference named `self`.
pub(super) fn is_receiver(index: usize, parameter: &CppPlace) -> bool {
    index == 0 && parameter.name == "self"
}

/// Whether a declared local is a reference, which a proof names by its
/// referent as it names a reference parameter.
pub(super) fn is_reference_local(local: &CppPlace) -> bool {
    matches!(local.value_type, CppType::LvalueReference { .. })
}

/// Whether a parameter is a reference the sidecar names by its referent. A
/// receiver also arrives as a reference; it is the pointer `this`.
pub(super) fn is_reference_parameter(index: usize, parameter: &CppPlace) -> bool {
    matches!(parameter.value_type, CppType::LvalueReference { .. })
        && !is_receiver(index, parameter)
}

fn lower_parameter(
    parameter: &CppPlace,
    layouts: &BTreeMap<String, crate::languages::c::syntax::C0StructLayout>,
) -> Result<crate::kernel::CParameter, String> {
    match &parameter.value_type {
        CppType::Record {
            name,
            is_const: false,
            ..
        } => {
            let layout = layouts
                .get(name)
                .ok_or("C++ record parameter has no checked layout")?;
            Ok(crate::kernel::c_parameter_with_aggregate_layout(
                parameter.name.clone(),
                CType::UInt8Pointer,
                layout.to_kernel_aggregate_layout(),
            ))
        }
        CppType::Integer { .. } | CppType::Enumeration { .. } => Ok(c_parameter(
            parameter.name.clone(),
            cpp_scalar_kernel_type(&parameter.value_type)?,
        )),
        CppType::Boolean {
            bits: 8,
            is_const: false,
        } => Ok(c_parameter(parameter.name.clone(), CType::Bool)),
        CppType::LvalueReference { pointee }
            if is_mutable_int32(pointee) || is_const_int32(pointee) =>
        {
            Ok(c_parameter(parameter.name.clone(), CType::Int32Pointer)
                .with_pointee_constant(is_const_int32(pointee)))
        }
        CppType::LvalueReference { pointee } if is_const_int64(pointee) => Ok(c_parameter(
            parameter.name.clone(),
            CType::Int64Pointer,
        )
        .with_pointee_constant(true)),
        CppType::LvalueReference { pointee }
            if matches!(pointee.as_ref(), CppType::Record { .. }) =>
        {
            Ok(
                c_parameter(parameter.name.clone(), CType::Int32Pointer).with_pointee_constant(
                    matches!(pointee.as_ref(), CppType::Record { is_const: true, .. }),
                ),
            )
        }
        CppType::Pointer { pointee } if Scalar::pointer_element(pointee, false).is_some() => {
            Ok(c_parameter(
                parameter.name.clone(),
                Scalar::pointer_element(pointee, false)
                    .unwrap()
                    .kind
                    .pointer_kernel_type()
                    .unwrap(),
            )
            .with_native_pointer_input(true))
        }
        _ => Err(format!(
            "C++ parameter `{}` is outside native scalar/reference/pointer and trivial record-value lowering",
            parameter.name
        )),
    }
}

// An empty evaluation prefix does not introduce a synthetic execution step.
fn evaluate_then(prefix: CStatement, continuation: CStatement) -> CStatement {
    if matches!(prefix, CStatement::Skip) {
        continuation
    } else {
        c_seq(prefix, continuation)
    }
}

/// A source scalar evaluation, independent of its initializer/return context.
/// Artifact wrappers retain their source role; every call uses this normalizer.
enum ScalarInput<'a> {
    Value(&'a CppExpression),
    Call {
        callee: &'a super::CppFunctionReference,
        arguments: &'a [CppCallArgument],
        value_type: &'a CppType,
        conversions: &'a [super::CppScalarConversion],
    },
}

struct ScalarEvaluation {
    prefix: CStatement,
    value: CExpression,
    value_type: CType,
    may_throw: bool,
}

struct LoweringContext<'a> {
    /// Declarations of the reference parameters, whose carrying pointers are
    /// named by [`reference_carrier_name`].
    reference_parameters: std::collections::BTreeSet<&'a str>,
    /// The declaration of the receiver, which is named [`RECEIVER_NAME`].
    receiver: Option<&'a str>,
    source_unit: &'a str,
    function_name: &'a str,
    names: &'a ResolvedNames,
    places: BTreeMap<&'a str, &'a CppPlace>,
    records: &'a super::schema::RecordIndex<'a>,
    constants: &'a BTreeMap<&'a str, &'a CppConstant>,
    kernel_layouts: &'a BTreeMap<String, std::sync::Arc<CAggregateLayout>>,
    next_load_occurrence: u32,
    return_capture_name: String,
    nested_capture_name: String,
    source_names: std::collections::BTreeSet<&'a str>,
    next_call_capture: u64,
    full_expression_records: Vec<String>,
    unwind_exception_name: String,
    unwind_cleanups: bool,
}

impl LoweringContext<'_> {
    fn lower_statement(&mut self, statement: &CppStatement) -> Result<CStatement, String> {
        let mark = self.full_expression_records.len();
        let lowered = self.lower_statement_inner(statement)?;
        if self.full_expression_records.len() == mark {
            return Ok(lowered);
        }
        self.full_expression_records.truncate(mark);
        if let CppStatement::Declare { local, .. } = statement {
            let name = if is_reference_local(local) {
                reference_carrier_name(&local.name)
            } else {
                local.name.clone()
            };
            return self.scope_declaration_expression(lowered, name);
        }
        Ok(CStatement::Scope {
            body: Box::new(lowered),
        })
    }

    fn lower_statement_inner(&mut self, statement: &CppStatement) -> Result<CStatement, String> {
        match statement {
            CppStatement::TrivialCopy { target, source, .. } => {
                let root = self.place(target)?;
                let (CppType::Record { name, .. }, _) = self
                    .records
                    .resolve_path(&root.value_type, &target.projections)?
                else {
                    return Err("C++ trivial copy requires a record target".into());
                };
                Ok(c_copy_aggregate(
                    self.lower_place(target)?,
                    self.lower_place(source)?,
                    self.record_layout(name)?,
                ))
            }
            CppStatement::Declare {
                local, initializer, ..
            } => match (&local.value_type, initializer) {
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                    CppInitializer::Uninitialized,
                ) => Ok(c_declare(
                    local.name.clone(),
                    cpp_scalar_kernel_type(&local.value_type)?,
                )),
                (CppType::LvalueReference { pointee }, CppInitializer::Value { value }) => {
                    let address = self.lower_expression(value)?;
                    let carrier = reference_carrier_name(&local.name);
                    Ok(c_seq(
                        c_declare_with_all_qualifiers(
                            carrier.clone(),
                            CType::Int32Pointer,
                            false,
                            false,
                            false,
                            is_const_int32(pointee),
                        ),
                        c_assign(carrier, address),
                    ))
                }
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. } | CppType::Pointer { .. },
                    CppInitializer::Value { value },
                ) => {
                    let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                    Ok(evaluate_then(
                        evaluation.prefix,
                        c_declare_initialized(
                            local.name.clone(),
                            evaluation.value_type,
                            evaluation.value,
                            false,
                            false,
                            Scalar::of(&local.value_type).is_some_and(|scalar| scalar.is_const),
                            false,
                        ),
                    ))
                }
                (
                    CppType::Integer { .. }
                    | CppType::Enumeration { .. }
                    | CppType::Pointer { .. }
                    | CppType::LvalueReference { .. },
                    CppInitializer::Call {
                        callee,
                        arguments,
                        conversions,
                        ..
                    },
                ) => {
                    let raw_type = conversions
                        .first()
                        .map_or(&local.value_type, |cast| &cast.source_type);
                    let raw_value_type = scalar::scalar_value_type(raw_type);
                    let raw_type = &raw_value_type;
                    // A reference bound to a call's result is carried by a
                    // pointer named for the address it holds.
                    let name = if is_reference_local(local) {
                        reference_carrier_name(&local.name)
                    } else {
                        local.name.clone()
                    };
                    let evaluation = self.normalize_scalar_into(
                        ScalarInput::Call {
                            callee,
                            arguments,
                            value_type: raw_type,
                            conversions,
                        },
                        (conversions.is_empty()
                            && !Scalar::of(&local.value_type)
                                .is_some_and(|scalar| scalar.is_const))
                        .then_some(name.as_str()),
                    )?;
                    let constant =
                        Scalar::of(&local.value_type).is_some_and(|scalar| scalar.is_const);
                    if conversions.is_empty() && !constant {
                        return Ok(evaluation.prefix);
                    }
                    Ok(evaluate_then(
                        evaluation.prefix,
                        c_declare_initialized(
                            name,
                            cpp_return_scalar_type(&scalar::scalar_value_type(&local.value_type))?,
                            evaluation.value,
                            false,
                            false,
                            constant,
                            false,
                        ),
                    ))
                }
                (
                    CppType::Record { name, .. },
                    CppInitializer::ConstructionCall {
                        callee, arguments, ..
                    },
                ) => {
                    let layout = self.record_layout(name)?;
                    let (prefix, actual) = self.normalize_arguments(arguments)?;
                    Ok(evaluate_then(
                        prefix,
                        c_seq(
                            c_allocate_aggregate_destination(local.name.clone(), layout),
                            c_call_assign(
                                local.name.clone(),
                                self.names.require(&callee.declaration_id)?.to_owned(),
                                actual,
                            ),
                        ),
                    ))
                }
                (
                    CppType::Record {
                        declaration_id,
                        name,
                        ..
                    },
                    CppInitializer::Aggregate { fields, .. },
                ) => {
                    let record = self.records.get(declaration_id.as_str()).ok_or_else(|| {
                        format!("C++ lowering found unknown record declaration `{declaration_id}`")
                    })?;
                    if record.name != *name || fields.len() != record.fields.len() {
                        return Err(format!(
                            "C++ aggregate initializer for `{name}` disagrees with its record"
                        ));
                    }
                    let layout = self.record_layout(&record.name)?;
                    let members = record
                        .fields
                        .iter()
                        .map(|field| {
                            Ok((
                                field.declaration_id.clone(),
                                field.name.clone(),
                                cpp_scalar_kernel_type(&field.value_type)?,
                            ))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    let mut result = c_declare_aggregate(local.name.clone(), layout);
                    for (initializer, (declaration_id, member_name, value_type)) in
                        fields.iter().zip(members)
                    {
                        if initializer.field.declaration_id != declaration_id {
                            return Err(format!(
                                "C++ aggregate initializer for `{name}` is out of declaration order"
                            ));
                        }
                        let pointer = CExpression::MemberAddress {
                            object: Box::new(c_variable(local.name.clone())),
                            selection: std::sync::Arc::new(
                                crate::kernel::CAggregateMemberSelection {
                                    layout: self.record_layout_arc(name)?,
                                    path: vec![member_name].into(),
                                    value_type,
                                },
                            ),
                        };
                        let value = self.lower_expression(&initializer.value)?;
                        result = c_seq(result, c_typed_store(pointer, value, value_type));
                    }
                    Ok(result)
                }
                (
                    CppType::Record {
                        declaration_id,
                        name,
                        ..
                    },
                    CppInitializer::Constructor {
                        callee, arguments, ..
                    },
                ) => {
                    let record = self.records.get(declaration_id.as_str()).ok_or_else(|| {
                        format!("C++ lowering found unknown record declaration `{declaration_id}`")
                    })?;
                    if record.name != *name {
                        return Err(format!(
                            "C++ constructor initializer for `{name}` disagrees with its record"
                        ));
                    }
                    let layout = self.record_layout(&record.name)?;
                    let mut lowered_arguments =
                        vec![c_cast(c_variable(local.name.clone()), CType::Int32Pointer)];
                    lowered_arguments.extend(self.lower_call_arguments(arguments)?);
                    Ok(c_seq(
                        c_allocate_aggregate_destination(local.name.clone(), layout),
                        c_call(
                            self.names.require(&callee.declaration_id)?.to_owned(),
                            lowered_arguments,
                        ),
                    ))
                }
                _ => Err(format!(
                    "C++ local `{}` has an initializer outside direct lowering",
                    local.name
                )),
            },
            CppStatement::Assign { target, value, .. } => {
                let target_is_local = matches!(
                    self.place(target)?.value_type,
                    CppType::Integer { .. } | CppType::Enumeration { .. } | CppType::Pointer { .. }
                );
                let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                let assignment = if target_is_local {
                    c_assign(target.name.clone(), evaluation.value)
                } else {
                    c_typed_store(self.lower_place(target)?, evaluation.value, CType::Int32)
                };
                Ok(evaluate_then(evaluation.prefix, assignment))
            }
            CppStatement::Store { pointer, value, .. } => Ok(c_typed_store(
                self.lower_expression(pointer)?,
                self.lower_expression(value)?,
                cpp_scalar_kernel_type(value.value_type())?,
            )),
            CppStatement::MemberConstruct {
                object,
                field,
                callee,
                arguments,
                ..
            } => {
                let place = self.place(object)?;
                let (value_type, _) = self.records.resolve_path(
                    &place.value_type,
                    object
                        .projections
                        .iter()
                        .map(super::schema::CppProjection::as_ref)
                        .chain(std::iter::once(super::schema::ProjectionRef::Field(field))),
                )?;
                let mut path: Vec<_> = object
                    .projections
                    .iter()
                    .map(|projection| match projection.as_ref() {
                        super::schema::ProjectionRef::Field(field) => field.name.clone(),
                        super::schema::ProjectionRef::Base(_) => "base".into(),
                    })
                    .collect();
                path.push(field.name.clone());
                let destination = self.lower_member_address(
                    place,
                    c_variable(self.variable_name(object)),
                    path,
                    value_type,
                )?;
                let mut lowered = vec![destination];
                lowered.extend(self.lower_call_arguments(arguments)?);
                Ok(c_call(
                    self.names.require(&callee.declaration_id)?.to_owned(),
                    lowered,
                ))
            }
            CppStatement::MemberStore {
                object,
                field,
                value,
                ..
            } => {
                let (pointer, value_type) = self.lower_member_pointer(object, field)?;
                let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                Ok(evaluate_then(
                    evaluation.prefix,
                    c_typed_store(pointer, evaluation.value, value_type),
                ))
            }
            CppStatement::Unreachable { span } => Ok(crate::kernel::c_labeled_assert(
                c_cast(CExpression::Value(int32(0)), CType::Bool),
                format!(
                    "C++ __builtin_unreachable at {}:{}:{}",
                    span.file, span.start_line, span.start_column
                ),
            )),
            CppStatement::Assume { condition, span } => Ok(crate::kernel::c_labeled_assert(
                self.lower_expression(condition)?,
                format!(
                    "C++ __builtin_assume at {}:{}:{}",
                    span.file, span.start_line, span.start_column
                ),
            )),
            CppStatement::LibraryAssert {
                condition,
                contract,
                span,
                ..
            } => Ok(crate::kernel::c_labeled_assert(
                self.lower_expression(condition)?,
                format!(
                    "C++ assumed library contract `{}` [{} sha256:{}]{} at {}:{}:{}",
                    contract.function,
                    contract.header,
                    contract.sha256,
                    contract
                        .literal_constructor
                        .as_ref()
                        .map(|pin| format!(
                            "; literal constructor `{}` [{} sha256:{}]",
                            pin.function, pin.header, pin.sha256
                        ))
                        .unwrap_or_default(),
                    span.file,
                    span.start_line,
                    span.start_column
                ),
            )),
            CppStatement::AssignConstructionCall { .. }
            | CppStatement::ReturnConstruct { .. }
            | CppStatement::ReturnAggregateCall { .. }
            | CppStatement::ReturnRecord { .. }
            | CppStatement::Return { .. }
            | CppStatement::ReturnCall { .. }
            | CppStatement::Throw { .. }
            | CppStatement::TryCatchInt32 { .. }
            | CppStatement::Scope { .. }
            | CppStatement::If { .. } => {
                Err("C++ control flow requires lifetime-aware lowering".into())
            }
            CppStatement::Call {
                callee, arguments, ..
            } => {
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                Ok(evaluate_then(
                    prefix,
                    c_call(
                        self.names.require(&callee.declaration_id)?.to_owned(),
                        arguments,
                    ),
                ))
            }
        }
    }

    fn finish_record_expression(&mut self, body: CStatement) -> CStatement {
        if self.full_expression_records.is_empty() {
            body
        } else {
            self.full_expression_records.clear();
            CStatement::Scope {
                body: Box::new(body),
            }
        }
    }

    fn scope_declaration_expression(
        &mut self,
        body: CStatement,
        name: String,
    ) -> Result<CStatement, String> {
        fn detach(
            statement: CStatement,
            name: &str,
            capture: &str,
            declarations: &mut Vec<CStatement>,
        ) -> CStatement {
            match statement {
                CStatement::Seq(first, second) => c_seq(
                    detach(
                        std::sync::Arc::unwrap_or_clone(first),
                        name,
                        capture,
                        declarations,
                    ),
                    detach(
                        std::sync::Arc::unwrap_or_clone(second),
                        name,
                        capture,
                        declarations,
                    ),
                ),
                CStatement::Declare {
                    name: ref declared, ..
                } if declared == name => {
                    let mut declaration = statement.clone();
                    let CStatement::Declare {
                        initializer,
                        c_type,
                        ..
                    } = &mut declaration
                    else {
                        unreachable!()
                    };
                    if let Some(value) = initializer.take() {
                        *initializer = Some(c_variable(capture));
                        declarations.push(c_declare(capture, *c_type));
                        declarations.push(declaration);
                        c_assign(capture, value)
                    } else {
                        declarations.insert(0, declaration);
                        c_skip()
                    }
                }
                CStatement::DeclareAggregate {
                    name: ref declared, ..
                } if declared == name => {
                    declarations.insert(0, statement);
                    c_skip()
                }
                statement => statement,
            }
        }
        let capture = self.fresh_call_capture()?;
        let mut declarations = Vec::new();
        let body = detach(body, &name, &capture, &mut declarations);
        let mut before = c_skip();
        let mut after = c_skip();
        for declaration in declarations {
            if matches!(
                &declaration,
                CStatement::Declare {
                    initializer: Some(_),
                    ..
                }
            ) {
                after = evaluate_then(after, declaration);
            } else {
                before = evaluate_then(before, declaration);
            }
        }
        Ok(evaluate_then(
            before,
            evaluate_then(
                CStatement::Scope {
                    body: Box::new(body),
                },
                after,
            ),
        ))
    }

    /// Capture the result before destruction. A throwing return call takes the
    /// same cleanup chain on its exceptional edge and never produces a return.
    fn lower_captured_return(
        &mut self,
        mut evaluation: CStatement,
        value_type: CType,
        cleanups: &[&CppCleanup],
        unwind_cleanups: &[&CppCleanup],
        can_throw: bool,
    ) -> Result<CStatement, String> {
        let capture = self.return_capture_name.clone();
        if can_throw && self.unwind_cleanups && !unwind_cleanups.is_empty() {
            let binding = self.unwind_exception_name.clone();
            let mut handler = c_skip();
            for cleanup in unwind_cleanups {
                handler = c_seq(handler, self.lower_cleanup(cleanup)?);
            }
            handler = c_seq(handler, CStatement::Throw(c_variable(binding.clone())));
            evaluation = c_try_catch_int32_with_cleanup(evaluation, binding, handler, true);
        }
        let mut result = c_seq(c_declare(capture.clone(), value_type), evaluation);
        for cleanup in cleanups {
            result = c_seq(result, self.lower_cleanup(cleanup)?);
        }
        Ok(c_seq(result, c_return(c_variable(capture))))
    }

    /// Each sequence starts with the objects live on entry. Construction adds
    /// an object only after its initializer; lexical exits restore a cursor.
    fn lower_sequence_with_lifetimes<'p>(
        &mut self,
        statements: &[CppStatement],
        plan: &'p LifetimePlan,
        state: &mut LifetimeState<'p>,
        unwind_base: usize,
    ) -> Result<CStatement, String> {
        let mut lowered = None;
        for statement in statements {
            let current =
                self.lower_statement_with_lifetimes(statement, plan, state, unwind_base)?;
            lowered = Some(match lowered {
                Some(previous) => c_seq(previous, current),
                None => current,
            });
            plan.constructed(statement, state);
        }
        Ok(lowered.unwrap_or_else(c_skip))
    }

    fn lower_statement_with_lifetimes<'p>(
        &mut self,
        statement: &CppStatement,
        plan: &'p LifetimePlan,
        state: &mut LifetimeState<'p>,
        unwind_base: usize,
    ) -> Result<CStatement, String> {
        match statement {
            CppStatement::AssignConstructionCall {
                target,
                callee,
                arguments,
                ..
            } => {
                let Some(CppType::Record { name, .. }) =
                    plan.full_expression_temporary_type(statement)
                else {
                    return Err(
                        "C++ construction assignment is missing its RHS lifetime event".into(),
                    );
                };
                let layout = self.record_layout(name)?;
                let (prefix, actual) = self.normalize_arguments(arguments)?;
                let temporary = self.fresh_aggregate_capture()?;
                // The RHS is a separate object: the live LHS may be read by
                // the factory and cannot serve as unwritten construction storage.
                let operation = evaluate_then(
                    prefix,
                    c_seq(
                        c_allocate_aggregate_destination(temporary.clone(), layout.clone()),
                        c_seq(
                            c_call_assign(
                                temporary.clone(),
                                self.names.require(&callee.declaration_id)?.to_owned(),
                                actual,
                            ),
                            c_seq(
                                c_copy_aggregate(
                                    self.lower_place(target)?,
                                    c_variable(temporary.clone()),
                                    layout,
                                ),
                                c_end_automatic_lifetimes(vec![temporary]),
                            ),
                        ),
                    ),
                );
                Ok(self.finish_record_expression(operation))
            }
            CppStatement::ReturnConstruct {
                callee, arguments, ..
            } => {
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                let mut actual = vec![c_cast(
                    c_variable(crate::kernel::C_CONTRACT_RESULT_NAME),
                    CType::Int32Pointer,
                )];
                actual.extend(arguments);
                let operation = evaluate_then(
                    prefix,
                    c_seq(
                        c_call(
                            self.names.require(&callee.declaration_id)?.to_owned(),
                            actual,
                        ),
                        c_return(c_variable(crate::kernel::C_CONTRACT_RESULT_NAME)),
                    ),
                );
                Ok(self.finish_record_expression(operation))
            }
            CppStatement::ReturnAggregateCall {
                callee, arguments, ..
            } => {
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                let operation = evaluate_then(
                    prefix,
                    c_seq(
                        c_call_assign(
                            crate::kernel::C_CONTRACT_RESULT_NAME,
                            self.names.require(&callee.declaration_id)?.to_owned(),
                            arguments,
                        ),
                        c_return(c_variable(crate::kernel::C_CONTRACT_RESULT_NAME)),
                    ),
                );
                Ok(self.finish_record_expression(operation))
            }
            CppStatement::ReturnRecord {
                source, value_type, ..
            } => {
                let CppType::Record { name, .. } = value_type else {
                    return Err("C++ record return has no nominal record type".into());
                };
                let layout = self.record_layout(name)?;
                let capture = self.return_capture_name.clone();
                let mut result = c_seq(
                    c_declare_aggregate(capture.clone(), layout.clone()),
                    c_copy_aggregate(
                        c_variable(capture.clone()),
                        self.lower_place(source)?,
                        layout,
                    ),
                );
                for cleanup in state.exit(0) {
                    result = c_seq(result, self.lower_cleanup(cleanup)?);
                }
                Ok(c_seq(result, c_return(c_variable(capture))))
            }
            CppStatement::Return { value, .. } => {
                let evaluation = self.normalize_scalar(ScalarInput::Value(value))?;
                self.lower_scalar_return(evaluation, &state.exit(0).collect::<Vec<_>>(), &[])
            }
            CppStatement::ReturnCall {
                callee,
                arguments,
                value_type,
                conversions,
                ..
            } => {
                let evaluation = self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type: conversions
                        .first()
                        .map_or(value_type, |cast| &cast.source_type),
                    conversions,
                })?;
                self.lower_scalar_return(
                    evaluation,
                    &state.exit(0).collect::<Vec<_>>(),
                    &state.exit(unwind_base).collect::<Vec<_>>(),
                )
            }
            CppStatement::Throw { value, .. } => {
                let throw = CStatement::Throw(self.lower_expression(value)?);
                self.lower_throwing_statement(throw, state.exit(unwind_base))
            }
            CppStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let mut evaluation = self.normalize_scalar(match condition {
                    CppCondition::Expression(value) => ScalarInput::Value(value),
                    CppCondition::Call { call } => ScalarInput::Call {
                        callee: &call.callee,
                        arguments: &call.arguments,
                        value_type: &call.value_type,
                        conversions: &[],
                    },
                })?;
                if !self.full_expression_records.is_empty() {
                    let capture = self.fresh_call_capture()?;
                    let body = evaluate_then(
                        evaluation.prefix,
                        c_assign(capture.clone(), c_cast(evaluation.value, CType::Bool)),
                    );
                    evaluation.prefix = c_seq(
                        c_declare(capture.clone(), CType::Bool),
                        self.finish_record_expression(body),
                    );
                    evaluation.value = c_variable(capture);
                    evaluation.value_type = CType::Bool;
                }
                let prefix = if evaluation.may_throw {
                    self.lower_throwing_statement(evaluation.prefix, state.exit(unwind_base))?
                } else {
                    evaluation.prefix
                };
                let mark = state.mark();
                let then_branch =
                    self.lower_sequence_with_lifetimes(then_branch, plan, state, unwind_base)?;
                state.restore(mark);
                let else_branch =
                    self.lower_sequence_with_lifetimes(else_branch, plan, state, unwind_base)?;
                state.restore(mark);
                Ok(evaluate_then(
                    prefix,
                    c_if(evaluation.value, then_branch, else_branch),
                ))
            }
            CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => {
                let mark = state.mark();
                let try_body = self.lower_sequence_with_lifetimes(try_body, plan, state, mark)?;
                state.restore(mark);
                let handler =
                    self.lower_sequence_with_lifetimes(handler, plan, state, unwind_base)?;
                state.restore(mark);
                Ok(c_try_catch_int32(try_body, binding.name.clone(), handler))
            }
            CppStatement::Scope { body, .. } => {
                let mark = state.mark();
                let mut result =
                    self.lower_sequence_with_lifetimes(body, plan, state, unwind_base)?;
                for cleanup in state.exit(mark) {
                    result = c_seq(result, self.lower_cleanup(cleanup)?);
                }
                state.restore(mark);
                Ok(result)
            }
            CppStatement::Declare {
                initializer: CppInitializer::Call { .. },
                ..
            }
            | CppStatement::Call { .. } => {
                let operation = self.lower_statement(statement)?;
                self.lower_throwing_statement(operation, state.exit(unwind_base))
            }
            _ => self.lower_statement(statement),
        }
    }

    fn lower_throwing_statement<'p>(
        &mut self,
        statement: CStatement,
        mut cleanups: impl Iterator<Item = &'p CppCleanup>,
    ) -> Result<CStatement, String> {
        let Some(first) = cleanups.next() else {
            return Ok(statement);
        };
        let binding = self.unwind_exception_name.clone();
        let mut handler = c_seq(c_skip(), self.lower_cleanup(first)?);
        for cleanup in cleanups {
            handler = c_seq(handler, self.lower_cleanup(cleanup)?);
        }
        handler = c_seq(handler, CStatement::Throw(c_variable(binding.clone())));
        Ok(c_try_catch_int32_with_cleanup(
            statement, binding, handler, true,
        ))
    }

    /// Normalize evaluation into explicit statements followed by a pure value.
    /// The validated C++ ordering policy is shared by every scalar call context.
    fn normalize_scalar(&mut self, input: ScalarInput<'_>) -> Result<ScalarEvaluation, String> {
        self.normalize_scalar_into(input, None)
    }

    /// Use an existing source destination when the caller needs no temporary.
    fn normalize_scalar_into(
        &mut self,
        input: ScalarInput<'_>,
        destination: Option<&str>,
    ) -> Result<ScalarEvaluation, String> {
        match input {
            ScalarInput::Value(value) if expression_contains_observer(value) => {
                self.normalize_expression(value)
            }
            ScalarInput::Value(value) => Ok(ScalarEvaluation {
                prefix: c_skip(),
                value: self.lower_expression(value)?,
                value_type: cpp_return_scalar_type(value.value_type())?,
                may_throw: false,
            }),
            ScalarInput::Call {
                callee,
                arguments,
                value_type,
                conversions,
            } => {
                let (prefix, arguments) = self.normalize_arguments(arguments)?;
                // A converted result always has a callee-typed temporary.
                let capture = match destination.filter(|_| conversions.is_empty()) {
                    Some(name) => name.to_owned(),
                    None => self.fresh_call_capture()?,
                };
                let capture_type = cpp_return_scalar_type(value_type)?;
                let mut value = c_variable(capture.clone());
                let mut result_type = capture_type;
                for conversion in conversions {
                    if matches!(conversion.value_type, CppType::Pointer { .. }) {
                        result_type = cpp_return_scalar_type(&conversion.value_type)?;
                        if conversion.cast_kind == super::CppScalarCastKind::BytePointerCast {
                            value = c_cast(value, result_type);
                        }
                        continue;
                    }
                    let source = Scalar::mutable_kind(&conversion.source_type)
                        .ok_or("unsupported C++ call conversion operand")?;
                    let target = Scalar::mutable_kind(&conversion.value_type)
                        .ok_or("unsupported C++ call conversion result")?;
                    if source != target {
                        value = scalar::convert(value, source, target);
                    }
                    result_type = target.kernel_type();
                }
                Ok(ScalarEvaluation {
                    prefix: evaluate_then(
                        prefix,
                        c_seq(
                            c_declare_with_all_qualifiers(
                                capture.clone(),
                                capture_type,
                                false,
                                false,
                                false,
                                matches!(value_type, CppType::LvalueReference { pointee } if is_const_int32(pointee)),
                            ),
                            c_call_assign(
                                capture.clone(),
                                self.names.require(&callee.declaration_id)?.to_owned(),
                                arguments,
                            ),
                        ),
                    ),
                    value,
                    value_type: result_type,
                    may_throw: true,
                })
            }
        }
    }

    fn normalize_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<(CStatement, Vec<CExpression>), String> {
        let mut evaluation = c_skip();
        let has_nested = arguments
            .iter()
            .any(|argument| matches!(argument, CppCallArgument::Call { .. }));
        // Check and snapshot field reads before a nested call can throw. Scalar
        // isolation keeps their values invariant in every argument order.
        let mut snapshots = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let snapshot = if let CppCallArgument::Value { value } = argument {
                if has_nested && super::schema::field_scalar_argument(value) {
                    let capture = self.fresh_call_capture()?;
                    let expression = self.lower_expression(value)?;
                    evaluation = evaluate_then(
                        evaluation,
                        c_seq(
                            c_declare(capture.clone(), cpp_return_scalar_type(value.value_type())?),
                            c_assign(capture.clone(), expression),
                        ),
                    );
                    Some(c_variable(capture))
                } else {
                    None
                }
            } else {
                None
            };
            snapshots.push(snapshot);
        }
        let mut lowered = Vec::with_capacity(arguments.len());
        for (argument, snapshot) in arguments.iter().zip(snapshots) {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(snapshot) = snapshot {
                lowered.push(snapshot);
            } else if matches!(
                argument,
                CppCallArgument::RecordConstruct { .. }
                    | CppCallArgument::Call {
                        value_type: CppType::Record { .. },
                        ..
                    }
            ) {
                let (callee, arguments, value_type, constructing) = match argument {
                    CppCallArgument::RecordConstruct {
                        callee,
                        arguments,
                        value_type,
                        ..
                    } => (callee, arguments, value_type, true),
                    CppCallArgument::Call {
                        callee,
                        arguments,
                        value_type,
                        ..
                    } => (callee, arguments, value_type, false),
                    _ => unreachable!(),
                };
                let CppType::Record { name, .. } = value_type else {
                    return Err("C++ record argument temporary has no record layout".into());
                };
                let layout = self.record_layout(name)?;
                let temporary = self.fresh_aggregate_capture()?;
                let (inner_prefix, mut actual) = self.normalize_arguments(arguments)?;
                let call = if constructing {
                    actual.insert(
                        0,
                        c_cast(c_variable(temporary.clone()), CType::Int32Pointer),
                    );
                    c_call(
                        self.names.require(&callee.declaration_id)?.to_owned(),
                        actual,
                    )
                } else {
                    c_call_assign(
                        temporary.clone(),
                        self.names.require(&callee.declaration_id)?.to_owned(),
                        actual,
                    )
                };
                evaluation = evaluate_then(
                    evaluation,
                    evaluate_then(
                        inner_prefix,
                        c_seq(
                            c_allocate_aggregate_destination(temporary.clone(), layout),
                            call,
                        ),
                    ),
                );
                self.full_expression_records.push(temporary.clone());
                lowered.push(c_cast(c_variable(temporary), CType::UInt8Pointer));
            } else if let CppCallArgument::Call {
                callee,
                arguments,
                value_type,
                ..
            } = argument
            {
                let inner = self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type,
                    conversions: &[],
                })?;
                evaluation = evaluate_then(evaluation, inner.prefix);
                lowered.push(inner.value);
            } else if let CppCallArgument::Value { value } = argument
                && !has_nested
                && expression_contains_observer(value)
            {
                let inner = self.normalize_scalar(ScalarInput::Value(value))?;
                evaluation = evaluate_then(evaluation, inner.prefix);
                lowered.push(inner.value);
            } else {
                // Remaining siblings are stable and total across the call.
                lowered.push(self.lower_call_argument(argument)?);
            }
        }
        Ok((evaluation, lowered))
    }

    fn lower_scalar_return(
        &mut self,
        evaluation: ScalarEvaluation,
        cleanups: &[&CppCleanup],
        unwind_cleanups: &[&CppCleanup],
    ) -> Result<CStatement, String> {
        let temporary_records = !self.full_expression_records.is_empty();
        self.full_expression_records.clear();
        if cleanups.is_empty() {
            let body = evaluate_then(evaluation.prefix, c_return(evaluation.value));
            return Ok(if temporary_records {
                CStatement::Scope {
                    body: Box::new(body),
                }
            } else {
                body
            });
        }
        let capture = self.return_capture_name.clone();
        let evaluation_body = evaluate_then(evaluation.prefix, c_assign(capture, evaluation.value));
        let evaluation_body = if temporary_records {
            CStatement::Scope {
                body: Box::new(evaluation_body),
            }
        } else {
            evaluation_body
        };
        self.lower_captured_return(
            evaluation_body,
            evaluation.value_type,
            cleanups,
            unwind_cleanups,
            evaluation.may_throw,
        )
    }

    fn normalize_expression(
        &mut self,
        expression: &CppExpression,
    ) -> Result<ScalarEvaluation, String> {
        let value_type = if let CppType::Pointer { pointee } = expression.value_type() {
            Scalar::pointer_element(pointee, true)
                .and_then(|scalar| scalar.kind.pointer_kernel_type())
                .ok_or("unsupported native pointer expression")?
        } else {
            cpp_return_scalar_type(expression.value_type())?
        };
        let (prefix, value, may_throw) = match expression {
            CppExpression::ObserverCall {
                callee,
                arguments,
                value_type,
                ..
            } => {
                if self.unwind_cleanups {
                    return Err("C++ expression observers currently require the normal-only exception profile".into());
                }
                return self.normalize_scalar(ScalarInput::Call {
                    callee,
                    arguments,
                    value_type,
                    conversions: &[],
                });
            }
            CppExpression::LogicalNot { value, .. } => {
                let input = self.normalize_expression(value)?;
                (
                    input.prefix,
                    c_cast(crate::kernel::c_not(input.value), CType::Bool),
                    input.may_throw,
                )
            }
            CppExpression::BytePointerCast { value, .. } => {
                let input = self.normalize_expression(value)?;
                (
                    input.prefix,
                    c_cast(input.value, CType::UInt8Pointer),
                    input.may_throw,
                )
            }
            CppExpression::IntegralCast {
                value, value_type, ..
            }
            | CppExpression::EnumCast {
                value, value_type, ..
            } => {
                let input = self.normalize_expression(value)?;
                let source = Scalar::mutable_kind(value.value_type())
                    .ok_or("unsupported observer cast operand")?;
                let target =
                    Scalar::mutable_kind(value_type).ok_or("unsupported observer cast result")?;
                (
                    input.prefix,
                    scalar::convert(input.value, source, target),
                    input.may_throw,
                )
            }
            CppExpression::ReferenceBinding { address, .. } => {
                let input = self.normalize_expression(address)?;
                let value = if matches!(address.as_ref(), CppExpression::AddressOf { .. }) {
                    input.value
                } else {
                    c_checked_object_address(c_typed_load(input.value, CType::Int32))
                };
                (input.prefix, value, input.may_throw)
            }
            CppExpression::Dereference { pointer, .. } => {
                let input = self.normalize_expression(pointer)?;
                let value = self.lower_typed_load(input.value, CType::Int32)?;
                (input.prefix, value, input.may_throw)
            }
            CppExpression::Binary {
                operator,
                left,
                right,
                value_type,
                ..
            } => {
                let lhs = self.normalize_expression(left)?;
                let rhs = self.normalize_expression(right)?;
                if *operator == CppBinaryOperator::LogicalAnd {
                    let capture = self.fresh_call_capture()?;
                    let prefix = evaluate_then(
                        lhs.prefix,
                        c_seq(
                            c_declare(capture.clone(), CType::Bool),
                            c_if(
                                lhs.value,
                                evaluate_then(rhs.prefix, c_assign(capture.clone(), rhs.value)),
                                c_assign(
                                    capture.clone(),
                                    c_cast(CExpression::Value(int32(0)), CType::Bool),
                                ),
                            ),
                        ),
                    );
                    return Ok(ScalarEvaluation {
                        prefix,
                        value: c_variable(capture),
                        value_type: CType::Bool,
                        may_throw: lhs.may_throw || rhs.may_throw,
                    });
                }
                let value = lower_binary_value(*operator, lhs.value, rhs.value, value_type);
                (
                    evaluate_then(lhs.prefix, rhs.prefix),
                    value,
                    lhs.may_throw || rhs.may_throw,
                )
            }
            _ => (c_skip(), self.lower_expression(expression)?, false),
        };
        Ok(ScalarEvaluation {
            prefix,
            value,
            value_type,
            may_throw,
        })
    }

    fn fresh_call_capture(&mut self) -> Result<String, String> {
        self.fresh_capture(self.nested_capture_name.clone())
    }

    fn fresh_aggregate_capture(&mut self) -> Result<String, String> {
        // Materialized objects have addressable storage. Keep their names
        // separate from scalar call captures: addressability is summarized
        // across functions by name, so an aggregate temporary in one function
        // must not obscure a scalar capture's nonescaping storage in another.
        self.fresh_capture(format!("{}_aggregate", self.nested_capture_name))
    }

    fn fresh_capture(&mut self, prefix: String) -> Result<String, String> {
        let mut capture = format!("{prefix}_{}", self.next_call_capture);
        self.next_call_capture = self
            .next_call_capture
            .checked_add(1)
            .ok_or("C++ nested call capture counter overflow")?;
        loop {
            crate::instrumentation::record_deterministic_work(1);
            if !self.source_names.contains(capture.as_str()) {
                break;
            }
            capture.push('_');
        }
        Ok(capture)
    }

    fn lower_call_arguments(
        &mut self,
        arguments: &[CppCallArgument],
    ) -> Result<Vec<CExpression>, String> {
        arguments
            .iter()
            .map(|argument| self.lower_call_argument(argument))
            .collect()
    }

    fn lower_cleanup(&self, cleanup: &CppCleanup) -> Result<CStatement, String> {
        let CppCleanup::Destructor { object, callee, .. } = cleanup;
        Ok(c_call(
            self.names.require(&callee.declaration_id)?.to_owned(),
            vec![c_cast(self.lower_place(object)?, CType::Int32Pointer)],
        ))
    }

    fn lower_call_argument(&mut self, argument: &CppCallArgument) -> Result<CExpression, String> {
        match argument {
            CppCallArgument::RecordCopy { place, .. } => {
                Ok(c_cast(self.lower_place(place)?, CType::UInt8Pointer))
            }
            CppCallArgument::Value { value } => self.lower_expression(value),
            CppCallArgument::Reference { place } => {
                let address = self.lower_place(place)?;
                let root = self.place(place)?;
                if !matches!(root.value_type, CppType::Record { .. }) {
                    return Ok(address);
                }
                // Automatic aggregates use byte-addressed storage. Calls
                // need the reference's pointee representation, as constructor
                // and destructor receivers already do.
                let (value_type, _) = self
                    .records
                    .resolve_path(&root.value_type, &place.projections)?;
                let pointer_type = match value_type {
                    CppType::Record { .. } | CppType::Integer { bits: 32, .. } => {
                        CType::Int32Pointer
                    }
                    CppType::Integer { bits: 64, .. } => CType::Int64Pointer,
                    _ => {
                        return Err(
                            "C++ reference place has no supported pointer representation".into(),
                        );
                    }
                };
                Ok(c_cast(address, pointer_type))
            }
            CppCallArgument::Call { .. } | CppCallArgument::RecordConstruct { .. } => {
                Err("nested C++ call bypassed scalar evaluation normalization".into())
            }
        }
    }

    fn lower_expression(&mut self, expression: &CppExpression) -> Result<CExpression, String> {
        match expression {
            CppExpression::RuntimeConstantEvaluation { .. } => {
                Ok(c_cast(CExpression::Value(int32(0)), CType::Bool))
            }
            CppExpression::LogicalNot { value, .. } => Ok(c_cast(
                crate::kernel::c_not(self.lower_expression(value)?),
                CType::Bool,
            )),

            CppExpression::ObserverCall { .. } => Err(
                "C++ expression observers are supported in normalized scalar values only".into(),
            ),
            CppExpression::NullPointer { value_type, .. } => Ok(c_cast(
                CExpression::Value(int32(0)),
                cpp_scalar_kernel_type(value_type)?,
            )),
            CppExpression::IntegerLiteral {
                value, value_type, ..
            }
            | CppExpression::CompilerConstant {
                value, value_type, ..
            } => Scalar::mutable_kind(value_type)
                .and_then(|kind| kind.parse_literal(value))
                .map(|literal| literal.kernel_expression())
                .ok_or_else(|| format!("unsupported C++ integer constant `{value}`")),
            CppExpression::ConstantReference {
                constant,
                value_type,
                ..
            } => {
                let resolved = self
                    .constants
                    .get(constant.declaration_id.as_str())
                    .ok_or_else(|| {
                        format!(
                            "C++ lowering found unknown constant declaration `{}`",
                            constant.declaration_id
                        )
                    })?;
                if resolved.name != constant.name {
                    return Err(format!(
                        "C++ constant declaration `{}` changed name during lowering",
                        constant.declaration_id
                    ));
                }
                Scalar::mutable_kind(value_type)
                    .and_then(|kind| kind.parse_literal(&resolved.evaluated_value))
                    .map(|literal| literal.kernel_expression())
                    .ok_or_else(|| {
                        format!(
                            "C++ constant `{}` has unsupported evaluated value `{}`",
                            resolved.name, resolved.evaluated_value
                        )
                    })
            }
            CppExpression::Load {
                place, value_type, ..
            } => match (&self.place(place)?.value_type, value_type) {
                (
                    CppType::Boolean {
                        bits: 8,
                        is_const: false,
                    },
                    CppType::Boolean {
                        bits: 8,
                        is_const: false,
                    },
                ) => Ok(c_variable(self.variable_name(place))),
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                ) if cpp_scalar_kernel_type(&scalar::scalar_value_type(
                    &self.place(place)?.value_type,
                ))? == cpp_scalar_kernel_type(value_type)? =>
                {
                    Ok(c_variable(self.variable_name(place)))
                }
                (
                    CppType::Pointer { pointee },
                    CppType::Pointer {
                        pointee: value_pointee,
                    },
                ) if Scalar::pointer_element(pointee, false).is_some()
                    && scalar::same_scalar_type(pointee, value_pointee) =>
                {
                    Ok(c_variable(self.variable_name(place)))
                }
                (CppType::LvalueReference { pointee }, value_type)
                    if (is_mutable_int32(pointee) || is_const_int32(pointee))
                        && is_mutable_int32(value_type) =>
                {
                    let pointer = self.lower_place(place)?;
                    let occurrence = self.next_load_occurrence;
                    self.next_load_occurrence = self
                        .next_load_occurrence
                        .checked_add(1)
                        .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
                    Ok(c_typed_load_with_source(
                        pointer,
                        CType::Int32,
                        Some(LoadSourceId {
                            owner: LoadSourceOwnerId {
                                source_unit: self.source_unit.into(),
                                function: self.function_name.into(),
                            },
                            occurrence,
                        }),
                    ))
                }
                (CppType::LvalueReference { pointee }, value_type)
                    if is_const_int64(pointee) && is_mutable_int64(value_type) =>
                {
                    let pointer = self.lower_place(place)?;
                    self.lower_typed_load(pointer, CType::Int64)
                }
                _ => Err("C++ load is outside direct bool/reference lowering".into()),
            },
            CppExpression::AddressOf {
                place, value_type, ..
            } if !place.projections.is_empty() => {
                // Address formation checks storage, not a read of the field value.
                let CppType::Pointer { pointee } = value_type else {
                    unreachable!("validated field address")
                };
                Ok(c_checked_object_address(c_typed_load(
                    self.lower_place(place)?,
                    Scalar::pointer_element(pointee, true)
                        .unwrap()
                        .kind
                        .kernel_type(),
                )))
            }
            CppExpression::AddressOf {
                place, value_type, ..
            } => match (&self.place(place)?.value_type, value_type) {
                (CppType::LvalueReference { pointee }, CppType::Pointer { pointee: result })
                    if (is_mutable_int32(pointee) || is_const_int32(pointee))
                        && scalar::same_scalar_type(pointee, result) =>
                {
                    Ok(c_variable(self.variable_name(place)))
                }
                (
                    CppType::Integer { .. } | CppType::Enumeration { .. },
                    CppType::Pointer { pointee },
                ) if Scalar::pointer_element(pointee, true).is_some() => Ok(
                    CExpression::AddressOf(Box::new(c_variable(self.variable_name(place)))),
                ),
                _ => Err("C++ address-of is outside integer reference lowering".into()),
            },
            CppExpression::ReferenceBinding { address, .. } => {
                let pointer = self.lower_expression(address)?;
                if matches!(address.as_ref(), CppExpression::AddressOf { .. }) {
                    // An existing reference parameter already denotes its referent.
                    Ok(pointer)
                } else {
                    Ok(c_checked_object_address(c_typed_load(
                        pointer,
                        CType::Int32,
                    )))
                }
            }
            CppExpression::Dereference {
                pointer,
                value_type,
                ..
            } if is_native_object_pointer(pointer.value_type()) => {
                let address = self.lower_expression(pointer)?;
                self.lower_typed_load(address, cpp_scalar_kernel_type(value_type)?)
            }
            CppExpression::Dereference { .. } => {
                Err("C++ dereference is outside mutable `int*` lowering".into())
            }
            CppExpression::MemberLoad {
                object,
                field,
                value_type,
                ..
            } => {
                let (pointer, field_type) = self.lower_member_pointer(object, field)?;
                if cpp_scalar_kernel_type(value_type)? != field_type {
                    return Err(format!(
                        "C++ member `{}` load type disagrees with its record field",
                        field.name
                    ));
                }
                self.lower_typed_load(pointer, field_type)
            }
            CppExpression::BytePointerCast { value, .. } => {
                Ok(c_cast(self.lower_expression(value)?, CType::UInt8Pointer))
            }
            CppExpression::IntegralCast {
                value, value_type, ..
            }
            | CppExpression::EnumCast {
                value, value_type, ..
            } => {
                let source = Scalar::mutable_kind(value.value_type())
                    .ok_or_else(|| "unsupported C++ integral cast operand".to_string())?;
                let target = Scalar::mutable_kind(value_type)
                    .ok_or_else(|| "unsupported C++ integral cast result".to_string())?;
                Ok(scalar::convert(
                    self.lower_expression(value)?,
                    source,
                    target,
                ))
            }
            CppExpression::Binary {
                operator,
                left,
                right,
                value_type,
                ..
            } => {
                let left = self.lower_expression(left)?;
                let right = self.lower_expression(right)?;
                Ok(lower_binary_value(*operator, left, right, value_type))
            }
        }
    }

    fn record_layout_arc(&self, name: &str) -> Result<std::sync::Arc<CAggregateLayout>, String> {
        self.kernel_layouts
            .get(name)
            .cloned()
            .ok_or_else(|| format!("C++ lowering found no checked layout for `{name}`"))
    }

    fn record_layout(&self, name: &str) -> Result<CAggregateLayout, String> {
        self.record_layout_arc(name)
            .map(|layout| layout.as_ref().clone())
    }

    fn lower_place(&self, place: &CppPlaceReference) -> Result<CExpression, String> {
        let root = self.place(place)?;
        let (value_type, offset) = self
            .records
            .resolve_path(&root.value_type, &place.projections)?;
        if !place.projections.is_empty() {
            let path = place
                .projections
                .iter()
                .map(|projection| match projection.as_ref() {
                    super::schema::ProjectionRef::Field(field) => field.name.clone(),
                    super::schema::ProjectionRef::Base(_) => "base".into(),
                })
                .collect();
            return self.lower_member_address(
                root,
                c_variable(self.variable_name(place)),
                path,
                value_type,
            );
        }
        Ok(c_pointer_offset_bytes(
            c_variable(self.variable_name(place)),
            offset,
        ))
    }

    fn lower_member_address(
        &self,
        root: &CppPlace,
        object: CExpression,
        path: Vec<String>,
        value_type: &CppType,
    ) -> Result<CExpression, String> {
        let root_type = match &root.value_type {
            CppType::LvalueReference { pointee } => pointee.as_ref(),
            value => value,
        };
        let CppType::Record { name, .. } = root_type else {
            return Err("member address requires a record root".into());
        };
        let value_type = match value_type {
            CppType::Record { name, .. } => {
                CType::UInt8Array(self.record_layout(name)?.size_bytes())
            }
            value => cpp_scalar_kernel_type(value)?,
        };
        Ok(CExpression::MemberAddress {
            object: Box::new(object),
            selection: std::sync::Arc::new(crate::kernel::CAggregateMemberSelection {
                layout: self.record_layout_arc(name)?,
                path: path.into(),
                value_type,
            }),
        })
    }

    fn lower_typed_load(
        &mut self,
        pointer: CExpression,
        value_type: CType,
    ) -> Result<CExpression, String> {
        let occurrence = self.next_load_occurrence;
        self.next_load_occurrence = self
            .next_load_occurrence
            .checked_add(1)
            .ok_or_else(|| "C++ load occurrence capacity exceeded".to_string())?;
        Ok(c_typed_load_with_source(
            pointer,
            value_type,
            Some(LoadSourceId {
                owner: LoadSourceOwnerId {
                    source_unit: self.source_unit.into(),
                    function: self.function_name.into(),
                },
                occurrence,
            }),
        ))
    }

    fn lower_member_pointer(
        &self,
        object: &CppPlaceReference,
        field: &CppFieldReference,
    ) -> Result<(CExpression, CType), String> {
        let place = self.place(object)?;
        let (value_type, offset) = self.records.resolve_path(
            &place.value_type,
            object
                .projections
                .iter()
                .map(super::schema::CppProjection::as_ref)
                .chain(std::iter::once(super::schema::ProjectionRef::Field(field))),
        )?;
        let mut path: Vec<_> = object
            .projections
            .iter()
            .map(|projection| match projection.as_ref() {
                super::schema::ProjectionRef::Field(field) => field.name.clone(),
                super::schema::ProjectionRef::Base(_) => "base".into(),
            })
            .collect();
        path.push(field.name.clone());
        let _ = offset; // Resolution authenticated the supplied declaration path.
        Ok((
            self.lower_member_address(
                place,
                c_variable(self.variable_name(object)),
                path,
                value_type,
            )?,
            cpp_scalar_kernel_type(value_type)?,
        ))
    }

    /// The kernel variable a place reference reads: the place's own name,
    /// or the carrier of a reference parameter.
    fn variable_name(&self, place: &CppPlaceReference) -> String {
        if self.receiver == Some(place.declaration_id.as_str()) {
            RECEIVER_NAME.to_string()
        } else if self
            .reference_parameters
            .contains(place.declaration_id.as_str())
        {
            reference_carrier_name(&place.name)
        } else {
            place.name.clone()
        }
    }

    fn place(&self, place: &CppPlaceReference) -> Result<&CppPlace, String> {
        let Some(parameter) = self.places.get(place.declaration_id.as_str()) else {
            return Err(format!(
                "C++ lowering found unknown declaration `{}`",
                place.declaration_id
            ));
        };
        if parameter.name != place.name {
            return Err(format!(
                "C++ declaration `{}` is named `{}`, not `{}`",
                place.declaration_id, parameter.name, place.name
            ));
        }
        Ok(parameter)
    }
}
fn return_capture_name(function: &CppFunction) -> String {
    fresh_internal_name(function, "__click_cpp_return_value")
}

fn fresh_internal_name(function: &CppFunction, base: &str) -> String {
    let mut declared_places = Vec::new();
    collect_declared_places(&function.body, &mut declared_places);
    let names = function
        .parameters
        .iter()
        .chain(declared_places)
        .map(|place| place.name.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    if !names.contains(base) {
        return base.to_string();
    }
    for suffix in 1u64.. {
        let candidate = format!("{base}_{suffix}");
        if !names.contains(candidate.as_str()) {
            return candidate;
        }
    }
    unreachable!("an unbounded suffix space contains an unused internal name")
}

fn collect_declared_places<'a>(statements: &'a [CppStatement], places: &mut Vec<&'a CppPlace>) {
    for statement in statements {
        match statement {
            CppStatement::Declare { local, .. } => places.push(local),
            CppStatement::Scope { body, .. } => collect_declared_places(body, places),
            CppStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                ..
            } => {
                collect_declared_places(try_body, places);
                places.push(binding);
                collect_declared_places(handler, places);
            }
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_declared_places(then_branch, places);
                collect_declared_places(else_branch, places);
            }
            _ => {}
        }
    }
}

fn expression_contains_observer(expression: &CppExpression) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match expression {
        CppExpression::ObserverCall { .. } => true,
        CppExpression::LogicalNot { value, .. }
        | CppExpression::IntegralCast { value, .. }
        | CppExpression::EnumCast { value, .. }
        | CppExpression::BytePointerCast { value, .. }
        | CppExpression::ReferenceBinding { address: value, .. }
        | CppExpression::Dereference { pointer: value, .. } => expression_contains_observer(value),
        CppExpression::Binary { left, right, .. } => {
            expression_contains_observer(left) || expression_contains_observer(right)
        }
        _ => false,
    }
}

fn lower_binary_value(
    operator: CppBinaryOperator,
    left: CExpression,
    right: CExpression,
    value_type: &CppType,
) -> CExpression {
    let expression = match operator {
        CppBinaryOperator::Add => c_add(left, right),
        CppBinaryOperator::Subtract => c_subtract(left, right),
        CppBinaryOperator::Multiply => c_multiply(left, right),
        CppBinaryOperator::Divide => c_divide(left, right),
        CppBinaryOperator::Remainder => c_remainder(left, right),
        CppBinaryOperator::Equal => c_equal(left, right),
        CppBinaryOperator::NotEqual => c_not_equal(left, right),
        CppBinaryOperator::LessThan => c_less_than(left, right),
        CppBinaryOperator::GreaterThan => c_greater_than(left, right),
        CppBinaryOperator::LessEqual => c_less_equal(left, right),
        CppBinaryOperator::GreaterEqual => c_greater_equal(left, right),
        CppBinaryOperator::LogicalAnd => c_and(left, right),
    };
    if is_mutable_bool(value_type) {
        c_cast(expression, CType::Bool)
    } else {
        expression
    }
}

fn cpp_return_scalar_type(value_type: &CppType) -> Result<CType, String> {
    if let CppType::Pointer { pointee } = value_type {
        return Scalar::pointer_element(pointee, false)
            .and_then(|scalar| scalar.kind.pointer_kernel_type())
            .ok_or_else(|| "unsupported native C++ pointer result".into());
    }
    if matches!(value_type, CppType::LvalueReference { pointee } if is_mutable_int32(pointee) || is_const_int32(pointee))
    {
        return Ok(CType::Int32Pointer);
    }
    Scalar::mutable_kind(value_type)
        .map(ScalarKind::kernel_type)
        .ok_or_else(|| "unsupported C++ scalar kernel type".into())
}

fn cpp_scalar_kernel_type(value_type: &CppType) -> Result<CType, String> {
    if let Some(kind) = Scalar::mutable_kind(value_type).filter(|kind| kind.is_integer()) {
        Ok(kind.kernel_type())
    } else if is_native_object_pointer(value_type) {
        cpp_return_scalar_type(value_type)
    } else {
        Err("unsupported C++ scalar kernel type".into())
    }
}

fn is_mutable_int32(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Int32, false)
}
fn is_mutable_bool(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Bool, false)
}
fn is_mutable_int64(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Int64, false)
}
fn is_const_int32(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Int32, true)
}
fn is_const_int64(value_type: &CppType) -> bool {
    Scalar::is(value_type, ScalarKind::Int64, true)
}

fn is_native_object_pointer(value_type: &CppType) -> bool {
    matches!(value_type, CppType::Pointer { pointee } if Scalar::pointer_element(pointee, false).is_some())
}
