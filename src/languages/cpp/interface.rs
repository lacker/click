//! Contract-facing metadata prepared by the C++ frontend alongside execution.
use super::scalar::{Scalar, ScalarKind};
use super::{CppStatement, CppType, PreparedCppImport};
use crate::kernel::ProgramFunction;
use crate::languages::PreparedExecution;
use crate::languages::c::target::LongRank;
use crate::languages::interface::InterfaceType;
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn prepare(
    import: &PreparedCppImport,
    selected: &[ProgramFunction],
    reachable: &[ProgramFunction],
    layouts: BTreeMap<String, crate::languages::interface::RecordLayout>,
    library_contracts: String,
    cpp_binding_conversions: BTreeSet<crate::kernel::CppObjectConversion>,
    dispatches: &BTreeSet<String>,
    receiver_calls: &BTreeMap<String, Vec<crate::languages::interface::CppReceiverCall>>,
    overload_paths: BTreeMap<String, String>,
) -> Result<PreparedExecution, String> {
    let shared_layouts = std::sync::Arc::new(layouts.clone());
    let shared_paths = std::sync::Arc::new(overload_paths.clone());
    let functions = prepare_functions(import, selected, reachable, &layouts)?
        .into_iter()
        .map(|mut function| {
            crate::instrumentation::record_deterministic_work(1);
            function.prepared_record_layouts = shared_layouts.clone();
            function.cpp_overload_paths = Some(shared_paths.clone());
            if dispatches.contains(function.name()) {
                function = function.with_cpp_virtual_call();
            }
            match receiver_calls.get(function.name()) {
                Some(calls) => function.with_receiver_calls(calls.clone()),
                None => function,
            }
        })
        .collect::<Vec<_>>();
    // A diagnostic prints each record by its C++ path.
    for record in &import.export().records {
        super::names::register_record_display(&record.name, &record.path.join("::"));
    }
    let record_spellings = import
        .export()
        .records
        .iter()
        .flat_map(|record| {
            // A head's qualifier writes the record's own segment,
            // `Stored<long long>::Read`; a type writes its path,
            // `std::span<int>`.
            [record.path.last().cloned(), Some(record.path.join("::"))]
                .into_iter()
                .flatten()
                .filter(|spelling| record.is_layout_free() || spelling != &record.name)
                .map(|spelling| (spelling, record.name.clone()))
        })
        .collect();
    Ok(PreparedExecution {
        functions,
        layouts,
        library_contracts,
        library_models: BTreeSet::new(),
        record_spellings,
        overload_paths,
        rust_binding_conversions: Default::default(),
        cpp_binding_conversions,
    })
}

/// Materialize checked nominal layouts once for execution and proof metadata.
pub(super) fn prepare_layouts(
    import: &PreparedCppImport,
) -> Result<BTreeMap<String, crate::languages::interface::RecordLayout>, String> {
    let mut layouts = BTreeMap::new();
    let records = import
        .export()
        .records
        .iter()
        .map(|record| (record.declaration_id.clone(), record))
        .collect();
    let mut leaf_counts = BTreeMap::new();
    let mut total_leaves = 0usize;
    for record in super::schema::record_layout_order(&records)? {
        if record.is_layout_free() {
            continue;
        }
        let mut leaves: usize = record.base.as_ref().map_or(0, |base| {
            let CppType::Record { name, .. } = &base.value_type else {
                unreachable!("validated nominal base")
            };
            leaf_counts[name.as_str()]
        });
        for field in &record.fields {
            crate::instrumentation::record_deterministic_work(1);
            leaves = leaves.saturating_add(match &field.value_type {
                CppType::Record { name, .. } => leaf_counts[name.as_str()],
                _ => 1,
            });
        }
        total_leaves = total_leaves.saturating_add(leaves);
        super::budget::limit(
            "materialized record layout leaves",
            total_leaves,
            super::budget::MAX_RECORD_LAYOUT_LEAVES,
        )?;
        leaf_counts.insert(record.name.as_str(), leaves);
        let mut constant_pointees = Vec::new();
        let mut fields = record
            .fields
            .iter()
            .map(|field| {
                crate::instrumentation::record_deterministic_work(1);
                let mut struct_name = None;
                let value_type = match &field.value_type {
                    value
                        if Scalar::mutable_kind(value).is_some_and(|kind| {
                            matches!(
                                kind,
                                ScalarKind::UInt8
                                    | ScalarKind::Int32
                                    | ScalarKind::UInt32
                                    | ScalarKind::Int64
                                    | ScalarKind::UInt64
                            )
                        }) =>
                    {
                        Scalar::mutable_kind(value).unwrap().proof_type()
                    }
                    CppType::Pointer { .. }
                        if let Some((_, name)) =
                            super::scalar::record_pointee(&field.value_type) =>
                    {
                        struct_name = Some(name.to_owned());
                        InterfaceType::Int32Pointer
                    }
                    CppType::Pointer { pointee }
                        if Scalar::pointer_element(pointee, true).is_some() =>
                    {
                        let element = Scalar::pointer_element(pointee, true).unwrap();
                        if element.is_const {
                            constant_pointees.push(field.name.clone());
                        }
                        element.kind.pointer_proof_type().unwrap()
                    }
                    CppType::Record {
                        name,
                        is_const: false,
                        ..
                    } => {
                        struct_name = Some(name.clone());
                        InterfaceType::Int32 // C's nominal embedded-record placeholder.
                    }
                    CppType::Parameter {
                        name,
                        is_const: false,
                    } => InterfaceType::Parameter(crate::kernel::TypeParameterName::intern(name)),
                    CppType::Array { element, length } => {
                        match Scalar::pointer_element(element, false).map(|scalar| scalar.kind) {
                            Some(ScalarKind::Int32) => InterfaceType::Int32Array(*length),
                            Some(ScalarKind::UInt32) => InterfaceType::UInt32Array(*length),
                            Some(ScalarKind::UInt8) => InterfaceType::UInt8Array(*length),
                            _ => {
                                return Err(format!(
                                    "C++ record field `{}.{}` has an unsupported array element",
                                    record.name, field.name
                                ));
                            }
                        }
                    }
                    _ => {
                        return Err(format!(
                            "C++ record field `{}.{}` is outside the supported proof interface",
                            record.name, field.name
                        ));
                    }
                };
                Ok((
                    field.name.clone(),
                    value_type,
                    struct_name,
                    field.offset_bytes,
                    field.size_bytes,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        if let Some(base) = &record.base {
            crate::instrumentation::record_deterministic_work(1);
            let CppType::Record { name, .. } = &base.value_type else {
                unreachable!("validated nominal base")
            };
            fields.insert(
                0,
                (
                    "base".into(),
                    InterfaceType::Int32,
                    Some(name.clone()),
                    base.offset_bytes,
                    base.size_bytes,
                ),
            );
        }
        // A class template instance that holds a value of an abstract type
        // argument has that value's size, `sizeof(T)`: its size and field
        // offsets are terms, as a Rust generic struct's are
        // (`docs/internals/kernel.md#symbolic-layouts`). The exporter's
        // word-sized placeholder layout is not used.
        // Fields keep declaration order, so the ones before the first field
        // an abstract type sizes or aligns keep their byte offsets (a base
        // subobject and the vtable pointer among them); only that field and
        // the ones after it are at terms.
        let first_dependent = fields.iter().position(|(_, value_type, struct_name, ..)| {
            matches!(value_type, InterfaceType::Parameter(parameter) if parameter.has_abstract_size())
                || struct_name.as_ref().is_some_and(|name| {
                    *value_type != InterfaceType::Int32Pointer
                        && layouts
                            .get(name)
                            .is_some_and(|layout: &crate::languages::interface::RecordLayout| {
                                layout.symbolic_layout().is_some()
                            })
                })
        });
        let mut layout = if let Some(first_dependent) = first_dependent {
            let mut prefix = fields;
            let suffix = prefix.split_off(first_dependent);
            if let Some((name, ..)) = suffix.iter().find(|(_, value_type, struct_name, ..)| {
                struct_name.is_some() && *value_type != InterfaceType::Int32Pointer
            }) {
                return Err(format!(
                    "C++ record `{}` embeds `{name}` after a value of an abstract type, which is outside the supported slice",
                    record.name
                ));
            }
            crate::languages::interface::RecordLayout::symbolic_with_prefix(
                &record.name,
                prefix,
                suffix
                    .into_iter()
                    .map(|(name, value_type, struct_name, _, _)| (name, value_type, struct_name))
                    .collect(),
                // A polymorphic class with no base starts with its own
                // vtable pointer, which no field names.
                if record.polymorphic && record.base.is_none() {
                    8
                } else {
                    0
                },
                record.size_bytes,
                record.alignment_bytes,
                &layouts,
            )
        } else {
            crate::languages::interface::RecordLayout::from_explicit_fields_with_structs(
                fields,
                record.size_bytes,
                record.alignment_bytes,
                &layouts,
            )
        }
        .map_err(|error| format!("invalid C++ record layout for `{}`: {error}", record.name))?;
        for name in &constant_pointees {
            layout.mark_pointee_constant(name)?;
        }
        if layouts.insert(record.name.clone(), layout).is_some() {
            return Err(format!("duplicate C++ record name `{}`", record.name));
        }
    }
    Ok(layouts)
}

fn prepare_functions(
    import: &PreparedCppImport,
    selected: &[ProgramFunction],
    reachable: &[ProgramFunction],
    layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> Result<Vec<crate::languages::interface::ImportedFunction>, String> {
    let observers = super::schema::observer_callees(import);
    // An override's interface is the virtual method it overrides, which a
    // call through that method assumes of it.
    let names = import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .zip(selected.iter().chain(reachable))
        .map(|(source, kernel)| (source.declaration_id.as_str(), kernel.name()))
        .collect::<BTreeMap<_, _>>();
    import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .zip(selected.iter().chain(reachable))
        .map(|(source, kernel)| {
            crate::instrumentation::record_deterministic_work(1);
            let mut locals = BTreeMap::new();
            let mut references = BTreeSet::new();
            let mut record_references = BTreeMap::new();
            let mut objects = BTreeSet::new();
            let mut ambiguous = BTreeSet::new();
            // The declared type of each local bound by its spelling, and the
            // spellings two scopes declare at different types.
            let mut spelled_local_types = BTreeMap::new();
            let mut ambiguous_spellings = BTreeSet::new();
            let mut opaque_exception_constructor = None;
            let mut pending = vec![source.body.as_slice()];
            while let Some(body) = pending.pop() {
                for statement in body {
                    crate::instrumentation::record_deterministic_work(1);
                    match statement {
                        CppStatement::Declare { local, .. } => {
                            // A name declared both as a reference and as
                            // an object, in two scopes, is read as written.
                            if matches!(local.value_type, CppType::LvalueReference { .. }) {
                                references.insert(local.name.clone());
                                if let Some((_, name, _)) =
                                    super::scalar::record_referent(&local.value_type)
                                {
                                    let carrier =
                                        crate::kernel::BindingName::reference_carrier(local.name.as_str());
                                    if record_references
                                        .get(&carrier)
                                        .is_some_and(|known| known != name)
                                    {
                                        ambiguous.insert(local.name.clone());
                                    }
                                    record_references.insert(carrier, name.to_owned());
                                }
                            } else {
                                objects.insert(local.name.clone());
                                if let Some(ty) =
                                    super::lowering::spelled_local_type(local, layouts)
                                    && spelled_local_types
                                        .insert(local.name.clone(), ty)
                                        .is_some_and(|known| known != ty)
                                {
                                    ambiguous_spellings.insert(local.name.clone());
                                }
                            }
                            if let CppType::Record { name, .. } = &local.value_type {
                                if locals.get(&local.name).is_some_and(|known| known != name) {
                                    ambiguous.insert(local.name.clone());
                                }
                                locals.insert(local.name.clone(), name.clone());
                            }
                        }
                        CppStatement::ThrowIosFailure { .. } => {
                            opaque_exception_constructor = Some(super::schema::IOS_FAILURE_CONSTRUCTOR);
                        }
                        CppStatement::Scope { body, .. } | CppStatement::While { body, .. } => {
                            pending.push(body)
                        }
                        CppStatement::If {
                            then_branch,
                            else_branch,
                            ..
                        } => {
                            pending.push(then_branch);
                            pending.push(else_branch);
                        }
                        CppStatement::TryCatchInt32 {
                            try_body, handler, ..
                        } => {
                            pending.push(try_body);
                            pending.push(handler);
                        }
                        _ => {}
                    }
                }
            }
            for name in &ambiguous_spellings {
                spelled_local_types.remove(name);
            }
            for name in ambiguous {
                locals.remove(&name);
                let carrier: crate::kernel::BindingName =
                    crate::kernel::BindingName::reference_carrier(name.as_str());
                if record_references.contains_key(&carrier) {
                    return Err(format!("C++ record-reference local `{name}` has ambiguous record layouts across scopes"));
                }
            }
            for name in &objects {
                let carrier: crate::kernel::BindingName =
                    crate::kernel::BindingName::reference_carrier(name.as_str());
                if record_references.contains_key(&carrier) {
                    return Err(format!("C++ record-reference local `{name}` shares its name with an object in another scope"));
                }
            }
            let interface = source
                .virtual_method
                .iter()
                .flat_map(|method| &method.overrides)
                .map(|overridden| names[overridden.declaration_id.as_str()].to_string())
                .next();
            // A generic class template's method at other type arguments is
            // an instance of its method at abstract ones.
            let generic = source
                .generic_instance
                .as_ref()
                .map(|generic| {
                    names
                        .get(generic.declaration_id.as_str())
                        .map(|name| name.to_string())
                        .ok_or_else(|| {
                            format!(
                                "C++ generic instance `{}` names no exported method",
                                source.name
                            )
                        })
                })
                .transpose()?
                // A standard function the Click library states is an
                // instance of the library's template method.
                .or_else(|| {
                    source
                        .axiom
                        .as_ref()
                        .and_then(super::standard_library::library_generic)
                });
            let mut imported = function_interface(source, kernel, layouts)?;
            if imported.prelowered_kernel_function().is_some() {
                imported.opaque_exception_constructor = opaque_exception_constructor;
            }
            if source.axiom.is_some() {
                imported = imported.with_positional_parameters();
            }
            Ok(imported
                .with_generic_instance(generic)
                .with_trait_interface(interface)
                .with_read_only_contract(observers.contains(&source.declaration_id))
                .with_local_struct_values(
                    locals
                        .into_iter()
                        .map(|(name, ty)| (name.into(), ty))
                        .collect(),
                )
                .with_local_struct_pointers(record_references)
                .with_spelled_local_types(spelled_local_types)
                .with_local_references(
                    references
                        .difference(&objects)
                        .cloned()
                        .map(Into::into)
                        .collect(),
                ))
        })
        .collect::<Result<Vec<_>, String>>()
}

/// Builds the proof-facing signature for the supported C++ profile from Clang's
/// typed declaration. The body deliberately remains absent here: executable
/// semantics come from `lower_import`, never from reconstructing C++ as C.
fn function_interface(
    source: &super::CppFunction,
    lowered: &crate::kernel::ProgramFunction,
    layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> Result<crate::languages::interface::ImportedFunction, String> {
    let return_reference = matches!(source.return_type, CppType::LvalueReference { .. });
    let return_element = super::scalar::reference_element(&source.return_type);
    let return_constant = super::scalar::returns_constant_element(&source.return_type);
    let return_type = if source.return_type == CppType::Void {
        InterfaceType::Void
    } else if let Some(element) = return_element {
        element
            .kind
            .pointer_proof_type()
            .ok_or("unsupported native reference return interface")?
    } else if matches!(source.return_type, CppType::Record { .. })
        || return_reference
        || super::scalar::record_pointee(&source.return_type).is_some()
    {
        InterfaceType::Int32Pointer
    } else if super::scalar::void_pointer(&source.return_type).is_some() {
        InterfaceType::VoidPointer
    } else if let CppType::Pointer { pointee } = &source.return_type {
        Scalar::pointer_element(pointee, true)
            .and_then(|scalar| scalar.kind.pointer_proof_type())
            .ok_or("unsupported native pointer return interface")?
    } else {
        Scalar::mutable_kind(&source.return_type)
            .map(ScalarKind::proof_type)
            .ok_or_else(|| {
                format!(
                    "C++ declaration `{}` has an unsupported return type",
                    source.declaration_id
                )
            })?
    };
    let parameters = source
        .parameters
        .iter()
        .zip(lowered.parameters())
        .map(|(parameter, lowered_parameter)| {
            crate::instrumentation::record_deterministic_work(1);
            let carried_name = lowered_parameter.binding_name();
            let is_reference = carried_name.reference_referent().is_some();
            if let Some(kind) = Scalar::mutable_kind(&parameter.value_type) {
                return Ok(crate::languages::interface::ImportedParameter::from_binding(kind.proof_type(), carried_name.clone(), None));
            }
            match &parameter.value_type {
            CppType::Record { name, is_const: false, .. } => {
                let layout = layouts.get(name).ok_or("C++ record parameter has no checked layout")?;
                Ok(crate::languages::interface::ImportedParameter::from_binding(InterfaceType::UInt8Pointer, carried_name.clone(), None)
                    .with_struct_value(name.clone(), layout.clone()))
            }
            reference @ CppType::LvalueReference { .. }
                if super::scalar::reference_element(reference).is_some() =>
            {
                let element = super::scalar::reference_element(reference).unwrap();
                Ok(crate::languages::interface::ImportedParameter::from_binding(
                    element
                        .kind
                        .pointer_proof_type()
                        .ok_or("unsupported native reference parameter interface")?,
                    carried_name.clone(),
                    None,
                )
                .with_pointee_constant(element.is_const)
                .with_reference(is_reference))
            }
            CppType::LvalueReference { pointee }
                if Scalar::is(pointee, ScalarKind::Int64, true) =>
            {
                Ok(crate::languages::interface::ImportedParameter::from_binding(
                    InterfaceType::Int64Pointer(LongRank::Long),
                    carried_name.clone(),
                    None,
                )
                .with_pointee_constant(true)
                .with_reference(is_reference))
            }
            CppType::LvalueReference { pointee } => {
                let CppType::Record { name, is_const, .. } = pointee.as_ref() else {
                    return Err(format!(
                        "C++ declaration `{}` parameter `{}` has an unsupported reference pointee",
                        source.declaration_id, parameter.name
                    ));
                };
                let carrier_type = if layouts.contains_key(name) {
                    InterfaceType::Int32Pointer
                } else {
                    InterfaceType::VoidPointer
                };
                let carrier = crate::languages::interface::ImportedParameter::from_binding(
                    carrier_type,
                    carried_name.clone(),
                    Some(name.clone()),
                );
                // The record's layout is what lets a diagnostic name a field
                // of the referent, `c.first`, where it would print a cell.
                let carrier = match layouts.get(name) {
                    Some(layout) => symbolic_reference_bounds(
                        carrier.with_pointee_struct_layout(name.clone(), layout.clone()),
                        layout,
                    ),
                    None => carrier,
                };
                Ok(carrier
                    .with_pointee_constant(*is_const)
                    .with_reference(is_reference))
            }
            pointer @ CppType::Pointer { .. } if super::scalar::record_pointee(pointer).is_some() => {
                let (_, name) = super::scalar::record_pointee(pointer).unwrap();
                let carrier_type = if layouts.contains_key(name) {
                    InterfaceType::Int32Pointer
                } else {
                    InterfaceType::VoidPointer
                };
                let carrier = crate::languages::interface::ImportedParameter::from_binding(
                    carrier_type,
                    carried_name.clone(),
                    Some(name.to_owned()),
                );
                Ok(match layouts.get(name) {
                    Some(layout) => symbolic_reference_bounds(
                        carrier.with_pointee_struct_layout(name.to_owned(), layout.clone()),
                        layout,
                    ),
                    None => carrier,
                })
            }
            CppType::FunctionPointer { .. } => Ok(crate::languages::interface::ImportedParameter::function_pointer(
                carried_name.clone(),
                function_pointer_signature(&parameter.value_type)?,
            )),
            pointer if let Some(is_const) = super::scalar::void_pointer(pointer) =>
            {
                Ok(crate::languages::interface::ImportedParameter::from_binding(
                    InterfaceType::VoidPointer, carried_name.clone(), None,
                ).with_pointee_constant(is_const))
            }
            CppType::Pointer { pointee } if Scalar::pointer_element(pointee, true).is_some() =>
            {
                Ok(crate::languages::interface::ImportedParameter::from_binding(
                    Scalar::pointer_element(pointee, true).unwrap().kind.pointer_proof_type().unwrap(),
                    carried_name.clone(),
                    None,
                ).with_pointee_constant(super::scalar::returns_constant_element(&parameter.value_type)))
            }
            _ => Err(format!(
                "C++ declaration `{}` parameter `{}` is outside the supported bool/reference/pointer/record interface",
                source.declaration_id, parameter.name
            )),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut interface = crate::languages::interface::ImportedFunction::external(
        return_type,
        lowered.name().to_owned(),
        parameters,
    )
    .with_return_reference(return_reference)
    .with_return_pointee_constant(return_constant);
    let parameter_count = source.parameters.len() - usize::from(source.receiver().is_some());
    let explicit = parameter_count
        .checked_sub(source.closure_captures)
        .ok_or("C++ closure has more captures than parameters")?;
    let types = source.parameter_type_spellings.as_deref();
    if types.is_some_and(|types| types.len() != explicit) {
        return Err(format!(
            "C++ declaration `{}` has inconsistent parameter spellings",
            source.name
        ));
    }
    // Frozen captures can supply a complete zero-parameter signature without
    // this metadata. Other overloads need a capture with exact native types.
    if let Some(types) = types.or_else(|| (explicit == 0).then_some(&[])) {
        let path = super::names::cpp_display_name(lowered.name())
            .unwrap_or_else(|| lowered.name().to_owned());
        let qualification = if matches!(
            source.function_kind,
            super::CppFunctionKind::Method { is_const: true, .. }
        ) {
            " const"
        } else {
            ""
        };
        interface.cpp_source_signature =
            Some(format!("{path}({}){qualification}", types.join(", ")).into());
    }
    // An axiom keeps no body: its calls are checked against a contract.
    // A pure virtual method is only its interface.
    // A generic method's instance is verified as that method, once.
    if !source.is_interface_only() && !source.is_pure_virtual() && source.generic_instance.is_none()
    {
        interface = interface.with_prelowered_kernel_function(lowered.clone());
    }
    // A lambda's leading parameters are its captures, which a sidecar head
    // does not write; its contract reads them by name.
    interface = interface.with_closure_captures(source.closure_captures);
    if let Some((_, name, _)) = super::scalar::record_referent(&source.return_type)
        && (return_reference || super::scalar::record_pointee(&source.return_type).is_some())
    {
        let layout = layouts
            .get(name)
            .ok_or("C++ record pointer return has no checked layout")?;
        interface = interface.with_struct_pointer_return(name.to_owned(), layout.clone());
    }
    if let CppType::Record { name, .. } = &source.return_type {
        let layout = layouts
            .get(name)
            .ok_or("C++ record return has no checked layout")?;
        interface = interface
            .with_struct_return(name.clone(), layout.clone())
            .with_aggregate_return_mode(lowered.contract_interface().aggregate_return_mode());
    }
    Ok(interface.with_nonthrowing_contract(source.has_nonthrowing_interface()))
}

/// The signature of a function-pointer type in proof types, as a C
/// function-pointer declarator in a sidecar head spells it.
pub(super) fn function_pointer_signature(
    value_type: &CppType,
) -> Result<crate::languages::interface::CallbackInterface, String> {
    let CppType::FunctionPointer {
        return_type,
        parameters,
        ..
    } = value_type
    else {
        return Err("C++ function-pointer signature requires a function-pointer type".into());
    };
    let proof_type = |value_type: &CppType| match value_type {
        CppType::Void => Some(InterfaceType::Void),
        CppType::Pointer { pointee } => Scalar::pointer_element(pointee, true)
            .and_then(|element| element.kind.pointer_proof_type()),
        _ => Scalar::mutable_kind(value_type).map(ScalarKind::proof_type),
    };
    let unsupported = || "C++ function-pointer type is outside the proof interface".to_string();
    let return_constant = super::scalar::returns_constant_element(return_type);
    let return_type = proof_type(return_type).ok_or_else(unsupported)?;
    let parameters = parameters
        .iter()
        .map(|parameter| {
            crate::instrumentation::record_deterministic_work(1);
            proof_type(parameter)
                .filter(|interface_type| *interface_type != InterfaceType::Void)
                .map(|interface_type| {
                    crate::languages::interface::CallbackParameter::new(
                        interface_type,
                        None,
                        super::scalar::returns_constant_element(parameter),
                    )
                })
                .ok_or_else(unsupported)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(crate::languages::interface::CallbackInterface::new(
        return_type,
        None,
        parameters,
        return_constant,
    ))
}

/// A reference or pointer to a symbolic record designates its whole object,
/// `sizeof` bytes, as a Rust reference to one does.
fn symbolic_reference_bounds(
    parameter: crate::languages::interface::ImportedParameter,
    layout: &crate::languages::interface::RecordLayout,
) -> crate::languages::interface::ImportedParameter {
    match layout.size() {
        size @ crate::kernel::LayoutSize::Of(_) => parameter.with_fixed_reference_bounds(size),
        crate::kernel::LayoutSize::Bytes(_) => parameter,
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/languages/cpp/interface/tests.rs");
}
