//! Exact pinned-library implementation models. Their checked bodies prove
//! model behavior; equivalence to the imported library remains an assumption.
use super::{CppFunction, CppFunctionKind, CppType, PreparedCppImport};
use crate::kernel::*;
use std::collections::BTreeMap;
use std::sync::Arc;

const SPAN_HEADER: &str = "sysroot/usr/include/c++/12/span";
const SPAN_SHA256: &str = "f1e67ea2c1e2e0faef697f37d995abb59eeb7fb0c0cf13a586fe2799ed9196bd";
const INT_RECORD: &str = "c:@N@std@S@span>#I#Vl18446744073709551615";
const WORD_RECORD: &str = "c:@N@std@S@span>#i#Vl18446744073709551615";
const BYTE_RECORD: &str = "c:@N@std@S@span>#$@N@std@E@byte#Vl18446744073709551615";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Model {
    WordConstructor,
    WritableBytes,
    ByteData,
    IntBack,
    IntFirst,
}

/// Declaration candidate only. This admits no execution or equivalence claim:
/// selection below additionally checks the locked header and concrete layout.
pub(super) fn candidate(source: &CppFunction) -> Option<Model> {
    let axiom = source.axiom.as_ref()?;
    match (
        axiom.qualified_name.as_str(),
        axiom.signature.as_str(),
        source.declaration_id.as_str(),
    ) {
        (
            "std::span<unsigned int>::span",
            "void (unsigned int *, unsigned long) noexcept",
            "c:@N@std@S@span>#i#Vl18446744073709551615@F@span<#*i>#S0_#l#",
        ) => Some(Model::WordConstructor),
        (
            "std::as_writable_bytes",
            "class std::span<enum std::byte> (class std::span<unsigned int>) noexcept",
            "c:@N@std@F@as_writable_bytes<#i#Vl18446744073709551615>#$@N@std@S@span>#i#Vl18446744073709551615#",
        ) => Some(Model::WritableBytes),
        (
            "std::span<std::byte>::data",
            "enum std::byte *(void) const noexcept",
            "c:@N@std@S@span>#$@N@std@E@byte#Vl18446744073709551615@F@data#1",
        ) => Some(Model::ByteData),
        (
            "std::span<int>::back",
            "int &(void) const noexcept",
            "c:@N@std@S@span>#I#Vl18446744073709551615@F@back#1",
        ) => Some(Model::IntBack),
        (
            "std::span<int>::first",
            "class std::span<int> (unsigned long) const noexcept",
            "c:@N@std@S@span>#I#Vl18446744073709551615@F@first#l#1",
        ) => Some(Model::IntFirst),
        _ => None,
    }
}

fn record_id(ty: &CppType) -> Option<&str> {
    match ty {
        CppType::Record { declaration_id, .. } => Some(declaration_id),
        CppType::LvalueReference { pointee } => record_id(pointee),
        _ => None,
    }
}
fn record_name(ty: &CppType) -> Option<&str> {
    match ty {
        CppType::Record { name, .. } => Some(name),
        CppType::LvalueReference { pointee } => record_name(pointee),
        _ => None,
    }
}

fn layout_matches(import: &PreparedCppImport, id: &str, pointer_type: CType) -> bool {
    let Some(record) = import
        .export()
        .records
        .iter()
        .find(|record| record.declaration_id == id)
    else {
        return false;
    };
    if record.span.file != SPAN_HEADER
        || record.size_bytes != 16
        || record.alignment_bytes != 8
        || record.base.is_some()
        || record.fields.len() != 2
    {
        return false;
    }
    let ptr = &record.fields[0];
    let extent = &record.fields[1];
    if ptr.declaration_id != format!("{id}@FI@_M_ptr")
        || extent.declaration_id != format!("{id}@FI@_M_extent")
        || ptr.name != "_M_ptr"
        || ptr.offset_bytes != 0
        || ptr.size_bytes != 8
        || extent.name != "_M_extent"
        || extent.offset_bytes != 8
        || extent.size_bytes != 8
    {
        return false;
    }
    let CppType::Pointer { pointee } = &ptr.value_type else {
        return false;
    };
    if id == BYTE_RECORD
        && !matches!(pointee.as_ref(), CppType::Enumeration { declaration_id, is_const: false, .. } if declaration_id == "c:@N@std@E@byte")
    {
        return false;
    }
    if id == WORD_RECORD
        && !super::scalar::Scalar::is(pointee, super::scalar::ScalarKind::UInt32, false)
    {
        return false;
    }
    if id == INT_RECORD
        && !super::scalar::Scalar::is(pointee, super::scalar::ScalarKind::Int32, false)
    {
        return false;
    }
    let Some(element) = super::scalar::Scalar::pointer_element(pointee, false) else {
        return false;
    };
    if element.kind.pointer_kernel_type() != Some(pointer_type) {
        return false;
    }
    let Some(extent_id) = record_id(&extent.value_type) else {
        return false;
    };
    let Some(inner) = import
        .export()
        .records
        .iter()
        .find(|record| record.declaration_id == extent_id)
    else {
        return false;
    };
    inner.declaration_id == "c:@N@std@N@__detail@S@__extent_storage>#Vl18446744073709551615"
        && inner.span.file == SPAN_HEADER
        && inner.base.is_none()
        && inner.size_bytes == 8
        && inner.alignment_bytes == 8
        && inner.fields.len() == 1
        && inner.fields[0].declaration_id == format!("{extent_id}@FI@_M_extent_value")
        && inner.fields[0].name == "_M_extent_value"
        && inner.fields[0].offset_bytes == 0
        && inner.fields[0].size_bytes == 8
        && super::scalar::Scalar::mutable_kind(&inner.fields[0].value_type)
            == Some(super::scalar::ScalarKind::UInt64)
}

// Receiver shape is part of the pinned ABI, not merely a record-valued
// parameter. Lowering names this exact implicit object `this`.
fn receiver_matches(source: &CppFunction, expected_record: &str, constant: bool) -> bool {
    let Some(receiver) = source.parameters.first() else {
        return false;
    };
    let CppType::LvalueReference { pointee } = &receiver.value_type else {
        return false;
    };
    let CppType::Record {
        declaration_id,
        name,
        is_const,
    } = pointee.as_ref()
    else {
        return false;
    };
    if receiver.name != "self"
        || receiver.declaration_id != format!("{}@this", source.declaration_id)
        || declaration_id != expected_record
        || *is_const != constant
    {
        return false;
    }
    match &source.function_kind {
        CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        } if !constant => record_declaration_id == declaration_id && record_name == name,
        CppFunctionKind::Method {
            record_declaration_id,
            record_name,
            is_const,
        } => {
            record_declaration_id == declaration_id && record_name == name && *is_const == constant
        }
        _ => false,
    }
}

pub(super) fn selected(import: &PreparedCppImport, source: &CppFunction) -> Option<Model> {
    let kind = candidate(source)?;
    if source.axiom.as_ref()?.declaration_header.as_deref() != Some(SPAN_HEADER) {
        return None;
    }
    if import
        .export()
        .profile
        .validate_byte_representation_guarantee()
        .is_err()
        || import.dependency_digest(SPAN_HEADER) != Some(SPAN_SHA256)
        || !source.declared_noexcept
    {
        return None;
    }
    let types_match = match kind {
        Model::IntBack => {
            source.parameters.len() == 1
                && receiver_matches(source, INT_RECORD, true)
                && matches!(&source.return_type, CppType::LvalueReference { pointee }
                    if super::scalar::Scalar::is(pointee, super::scalar::ScalarKind::Int32, false))
        }
        Model::IntFirst => {
            source.parameters.len() == 2
                && receiver_matches(source, INT_RECORD, true)
                && matches!(&source.return_type, CppType::Record { declaration_id, is_const: false, .. } if declaration_id == INT_RECORD)
                && super::scalar::Scalar::is(
                    &source.parameters[1].value_type,
                    super::scalar::ScalarKind::UInt64,
                    false,
                )
        }
        Model::WordConstructor => {
            source.parameters.len() == 3
                && receiver_matches(source, WORD_RECORD, false)
                && matches!(source.function_kind, CppFunctionKind::Constructor { .. })
                && source.return_type == CppType::Void
                && matches!(&source.parameters[1].value_type, CppType::Pointer { pointee }
                    if super::scalar::Scalar::is(pointee, super::scalar::ScalarKind::UInt32, false))
                && super::scalar::Scalar::is(
                    &source.parameters[2].value_type,
                    super::scalar::ScalarKind::UInt64,
                    false,
                )
        }
        Model::WritableBytes => {
            source.parameters.len() == 1
                && matches!(source.function_kind, CppFunctionKind::Free)
                && record_id(&source.parameters[0].value_type) == Some(WORD_RECORD)
                && record_id(&source.return_type) == Some(BYTE_RECORD)
                && matches!(
                    source.parameters[0].value_type,
                    CppType::Record {
                        is_const: false,
                        ..
                    }
                )
                && matches!(
                    source.return_type,
                    CppType::Record {
                        is_const: false,
                        ..
                    }
                )
        }
        Model::ByteData => {
            source.parameters.len() == 1
                && receiver_matches(source, BYTE_RECORD, true)
                && matches!(&source.return_type, CppType::Pointer { pointee } if matches!(pointee.as_ref(), CppType::Enumeration { declaration_id, is_const: false, .. } if declaration_id == "c:@N@std@E@byte"))
        }
    };
    let layout_match = if matches!(kind, Model::IntBack | Model::IntFirst) {
        layout_matches(import, INT_RECORD, CType::Int32Pointer)
    } else {
        layout_matches(import, WORD_RECORD, CType::UInt32Pointer)
            && (kind == Model::WordConstructor
                || layout_matches(import, BYTE_RECORD, CType::UInt8Pointer))
    };
    (types_match && layout_match).then_some(kind)
}

pub(super) fn assumptions(import: &PreparedCppImport) -> Vec<String> {
    std::iter::once(&import.export().function).chain(&import.export().reachable_functions).filter_map(|source| selected(import, source).map(|kind| {
        format!("assumed source-to-model equivalence for {} [{}; span SHA256 {}]; model implementation requires independent checked certification", source.axiom.as_ref().unwrap().qualified_name, if matches!(kind, Model::IntBack | Model::IntFirst) { "Clang 19.1.7 LP64 native typed-prefix profile" } else { super::schema::DECLARED_UINT32_BYTE_GUARANTEE }, SPAN_SHA256)
    })).collect()
}

fn member(
    layout: Arc<CAggregateLayout>,
    owner: CExpression,
    path: &[&str],
    ty: CType,
) -> CExpression {
    CExpression::MemberAddress {
        object: Box::new(owner),
        selection: Arc::new(CAggregateMemberSelection {
            layout,
            path: path.iter().map(|name| name.to_string()).collect(),
            value_type: ty,
        }),
    }
}

pub(super) fn implementation(
    import: &PreparedCppImport,
    source: &CppFunction,
    mut function: CFunction,
    layouts: &BTreeMap<String, Arc<CAggregateLayout>>,
) -> Result<CFunction, String> {
    let Some(kind) = selected(import, source) else {
        return Ok(function);
    };
    let argument_record =
        record_name(&source.parameters[0].value_type).ok_or("model input record missing")?;
    let input_layout = layouts
        .get(argument_record)
        .ok_or("model input layout missing")?
        .clone();
    let owner = c_variable(if kind == Model::WritableBytes {
        &source.parameters[0].name
    } else {
        "this"
    });
    let pointer_type = match kind {
        Model::ByteData => CType::UInt8Pointer,
        Model::IntBack | Model::IntFirst => CType::Int32Pointer,
        _ => CType::UInt32Pointer,
    };
    let pointer = member(
        input_layout.clone(),
        owner.clone(),
        &["_M_ptr"],
        pointer_type,
    );
    let count = member(
        input_layout,
        owner,
        &["_M_extent", "_M_extent_value"],
        CType::UInt64,
    );
    let body = match kind {
        Model::IntBack => c_return(c_checked_object_address(c_typed_load(
            c_add(
                c_typed_load(pointer, CType::Int32Pointer),
                c_subtract(c_typed_load(count, CType::UInt64), c_uint64_literal(1)),
            ),
            CType::Int32,
        ))),
        Model::IntFirst => {
            let destination = c_variable(C_CONTRACT_RESULT_NAME);
            let result_layout = layouts
                .get(record_name(&source.return_type).ok_or("model result missing")?)
                .ok_or("model result layout missing")?
                .clone();
            let output_pointer = member(
                result_layout.clone(),
                destination.clone(),
                &["_M_ptr"],
                CType::Int32Pointer,
            );
            let output_count = member(
                result_layout,
                destination.clone(),
                &["_M_extent", "_M_extent_value"],
                CType::UInt64,
            );
            c_seq(
                c_typed_store(
                    output_pointer,
                    c_typed_load(pointer, CType::Int32Pointer),
                    CType::Int32Pointer,
                ),
                c_seq(
                    c_typed_store(
                        output_count,
                        c_variable(&source.parameters[1].name),
                        CType::UInt64,
                    ),
                    c_return(destination),
                ),
            )
        }
        Model::WordConstructor => {
            function = function.with_native_span_inputs(vec![CNativeSpanInput {
                parameter_index: 1,
                length_parameter_index: 2,
                element_type: CType::UInt32,
            }]);
            c_seq(
                c_typed_store(
                    pointer,
                    c_variable(&source.parameters[1].name),
                    CType::UInt32Pointer,
                ),
                c_seq(
                    c_typed_store(count, c_variable(&source.parameters[2].name), CType::UInt64),
                    c_return(c_void_value()),
                ),
            )
        }
        Model::ByteData => c_return(c_typed_load(pointer, CType::UInt8Pointer)),
        Model::WritableBytes => {
            let input_pointer = c_typed_load(pointer, CType::UInt32Pointer);
            let input_count = c_typed_load(count, CType::UInt64);
            function = function.with_native_span_expression_inputs(vec![CNativeSpanRequirement {
                carrier: input_pointer.clone(),
                count: input_count.clone(),
                element_type: CType::UInt32,
                access_policy: CTypedAccessPolicy::NativeObjectOnly,
            }]);
            let result_layout = layouts
                .get(record_name(&source.return_type).ok_or("model result missing")?)
                .ok_or("model result layout missing")?
                .clone();
            let destination = c_variable(C_CONTRACT_RESULT_NAME);
            let output_pointer = member(
                result_layout.clone(),
                destination.clone(),
                &["_M_ptr"],
                CType::UInt8Pointer,
            );
            let output_count = member(
                result_layout,
                destination.clone(),
                &["_M_extent", "_M_extent_value"],
                CType::UInt64,
            );
            c_seq(
                c_typed_store(
                    output_pointer,
                    c_cast(input_pointer, CType::UInt8Pointer),
                    CType::UInt8Pointer,
                ),
                c_seq(
                    c_typed_store(
                        output_count,
                        c_multiply(input_count, c_uint64_literal(4)),
                        CType::UInt64,
                    ),
                    c_return(destination),
                ),
            )
        }
    };
    Ok(function.with_body(body))
}

pub(super) fn contract(
    import: &PreparedCppImport,
    source: &CppFunction,
    name: &str,
) -> Option<String> {
    let kind = selected(import, source)?;
    let record = record_name(&source.parameters[0].value_type)?;
    Some(match kind {
        Model::IntBack => format!(
            "int32& {name}(const struct {record}* this) {{\n views std_span_data(this);\n views std_span_size(this);\n requires 1u64 <= std_span_size(this);\n requires valid_place(std_span_data(this)[0..std_span_size(this)]);\n ensures &result == std_span_data(this) + (std_span_size(this) - 1u64);\n}} by {{ execute(); simp(); }}\n"
        ),
        Model::IntFirst => {
            let count = &source.parameters[1].name;
            format!(
                "struct {record} {name}(const struct {record}* this, uint64 {count}) {{\n views std_span_data(this);\n views std_span_size(this);\n requires {count} <= std_span_size(this);\n requires valid_place(std_span_data(this)[0..{count}]);\n ensures std_span_data(result) == std_span_data(this);\n ensures std_span_size(result) == {count};\n}} by {{ execute(); simp(); }}\n"
            )
        }
        Model::WordConstructor => {
            let pointer = &source.parameters[1].name;
            let count = &source.parameters[2].name;
            format!(
                "void {name}(struct {record}* this, uint32* {pointer}, uint64 {count}) {{\n owns std_span_data(this);\n owns std_span_size(this);\n requires {count} == 1u64;\n ensures std_span_data(this) == {pointer};\n ensures std_span_size(this) == {count};\n}} by {{ execute(); simp(); }}\n"
            )
        }
        Model::WritableBytes => {
            let parameter = &source.parameters[0].name;
            let result = record_name(&source.return_type)?;
            format!(
                "struct {result} {name}(struct {record} {parameter}) {{\n requires std_span_size({parameter}) == 1u64;\n ensures std_span_data(result) == old((uint8*)std_span_data({parameter}));\n ensures std_span_size(result) == old(std_span_size({parameter})) * 4u64;\n}} by {{ execute(); simp(); }}\n"
            )
        }
        Model::ByteData => format!(
            "uint8* {name}(const struct {record}* this) {{\n views std_span_data(this);\n ensures result == std_span_data(this);\n}} by {{ execute(); simp(); }}\n"
        ),
    })
}
