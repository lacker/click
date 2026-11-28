use super::schema::{
    Expression as E, Function, MirCallee, MirLocalId, Record, RustExport, Statement as S, Type,
};
#[cfg(test)]
mod array_reference_tests;
mod arrays;
mod chunks;
mod enumerate;
#[cfg(test)]
mod move_regressions;
mod moves;
#[cfg(test)]
mod owned_parameter_regressions;
mod ranges;
#[cfg(test)]
mod record_pointer_fields_tests;
#[cfg(test)]
mod return_call_tests;
mod shared_arrays;
use crate::kernel::*;
use crate::languages::c::syntax::LongRank;
use crate::languages::interface::{
    CallbackInterface, CallbackParameter, ImportedFunction, ImportedParameter, InterfaceType,
    RecordLayout,
};
use std::collections::{BTreeMap, BTreeSet};

// Rust reference lowering changes the access type without introducing C's
// authored character/void cast escape. Preserve the complete pointer domain.
fn reference_view(
    expression: ProgramExpression,
    target_type: ProgramType,
    pointee_volatile: bool,
    pointee_constant: bool,
) -> ProgramExpression {
    ProgramExpression::Cast {
        expression: Box::new(expression),
        target_type,
        integer_mode: IntegerCastMode::PointerCoercion,
        pointee_struct: None,
        pointee_struct_size: None,
        pointee_volatile,
        pointee_constant,
        explicit_qualification: false,
    }
}

/// The kernel type of a Rust `&[u8]` or `&mut [u8]`.
pub(super) const BYTE_SLICE: ProgramType =
    ProgramType::SlicePointer(crate::kernel::SliceElement::UInt8);

/// The slice whose data pointer is `pointer`, viewed at `thin_type`, and
/// whose element count is `length`: one wide value built from its parts
/// (`design/rust-slice-values.md`, step 3b).
fn slice_value(
    pointer: ProgramExpression,
    thin_type: ProgramType,
    length: ProgramExpression,
    constant: bool,
) -> ProgramExpression {
    ProgramExpression::SliceFromRawParts {
        data: Box::new(reference_view(pointer, thin_type, false, constant)),
        count: Box::new(length),
    }
}

/// The data pointer and element count of the slice `slice` holds:
/// `slice.as_ptr()` and `slice.len()`, read in place.
fn slice_components(slice: ProgramExpression) -> (ProgramExpression, ProgramExpression) {
    (
        ProgramExpression::SliceData(Box::new(slice.clone())),
        ProgramExpression::SliceLength(Box::new(slice)),
    )
}

pub(crate) type LoweredRust = (Vec<ImportedFunction>, BTreeMap<String, RecordLayout>);

thread_local! {
    /// The kernel types of the crate enums being lowered, by name. One
    /// lowering runs on one thread and sets them for its duration
    /// ([`EnumTypes::enter`]), so a type is found from its name alone.
    static ENUM_TYPES: std::cell::RefCell<BTreeMap<String, TypeParameterName>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// The crate's enums for the duration of one lowering.
struct EnumTypes;

impl EnumTypes {
    fn enter(export: &RustExport) -> Result<Self, String> {
        // Each enum is known as soon as it is declared, and the guard clears
        // them all if a later one is refused.
        ENUM_TYPES.with(|known| known.borrow_mut().clear());
        let guard = Self;
        // Crate enums first: a library enum instance may hold one,
        // `Result<u32, ParseError>`.
        let (crate_enums, instances): (Vec<_>, Vec<_>) = export
            .enums
            .iter()
            .partition(|declared| declared.generic.is_none());
        for declared in crate_enums.into_iter().chain(instances) {
            // A library enum instance's payload of a crate enum is that enum
            // itself, `Result<u32, ParseError>`'s error a `ParseError`, whose
            // variants the instance's schemas carry.
            let mut nested = BTreeMap::new();
            let mut payload_type = |t: &Type| -> Result<Option<AlgebraicValueType>, String> {
                let Type::Enum { name } = t else {
                    return Ok(None);
                };
                if declared.generic.is_none() {
                    return Ok(None);
                }
                let enum_type = EnumTypes::get(name)?.algebraic_type();
                let value_type = enum_type.value_type();
                nested.insert(value_type.clone(), enum_type.variants.clone());
                Ok(Some(value_type))
            };
            let variants: std::sync::Arc<[AlgebraicVariantType]> = declared
                .variants
                .iter()
                .map(|variant| {
                    Ok(AlgebraicVariantType {
                        name: variant.name.clone(),
                        fields: variant
                            .fields
                            .iter()
                            .map(|field| {
                                if let Some(nested) = payload_type(field)? {
                                    return Ok(nested);
                                }
                                // The library's `Option` of a shared slice,
                                // which a chunk iterator's `next()` returns,
                                // holds that slice, one wide pointer
                                // (`design/rust-slice-values.md`).
                                if declared.generic.as_deref() == Some("Option")
                                    && let Some(slice) = shared_slice_type(field)?
                                {
                                    return Ok(AlgebraicValueType::Program(slice));
                                }
                                let interface_type = scalar_type(field)?;
                                // The library's `Option` of a shared
                                // reference, which a slice iterator's
                                // `next()` returns, holds that reference.
                                let reference_payload = declared.generic.as_deref()
                                    == Some("Option")
                                    && matches!(field, Type::Reference { mutable: false, .. });
                                if interface_type == InterfaceType::Void
                                    || (interface_type.is_pointer() && !reference_payload)
                                {
                                    return Err(
                                        "Rust enum fields must be integers or booleans".to_string()
                                    );
                                }
                                Ok(AlgebraicValueType::Program(interface_type.to_kernel_type()))
                            })
                            .collect::<Result<_, String>>()?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?
                .into();
            // An instance of a library enum is that `spec enum` at its
            // arguments: `Option<u32>` is `Option` at `u32`.
            let spec_name = declared.generic.as_ref().unwrap_or(&declared.name);
            let arguments = declared
                .arguments
                .iter()
                .map(|argument| {
                    if let Some(nested) = payload_type(argument)? {
                        return Ok(nested);
                    }
                    if let Some(slice) = shared_slice_type(argument)? {
                        return Ok(AlgebraicValueType::Program(slice));
                    }
                    Ok(AlgebraicValueType::Program(
                        scalar_type(argument)?.to_kernel_type(),
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let nominal = AlgebraicValueType::Algebraic {
                name: spec_name.clone(),
                arguments: arguments.clone(),
            };
            nested.insert(nominal, variants.clone());
            let algebraic_type = AlgebraicType {
                rigid: false,
                name: spec_name.clone(),
                arguments,
                variants: variants.clone(),
                schemas: std::sync::Arc::new(AlgebraicSchemas::new(nested)),
            };
            let duplicate = ENUM_TYPES.with(|known| {
                known
                    .borrow_mut()
                    .insert(
                        declared.name.clone(),
                        TypeParameterName::of(&algebraic_type),
                    )
                    .is_some()
            });
            if duplicate {
                return Err("duplicate Rust enum".into());
            }
        }
        Ok(guard)
    }

    fn get(name: &str) -> Result<TypeParameterName, String> {
        ENUM_TYPES
            .with(|known| known.borrow().get(name).copied())
            .ok_or_else(|| format!("unknown Rust enum `{name}`"))
    }
}

impl Drop for EnumTypes {
    fn drop(&mut self) {
        ENUM_TYPES.with(|known| known.borrow_mut().clear());
    }
}

/// The C type of field `index` of variant `variant` of enum `name`, when
/// that field is itself an enum: `Result<u32, ParseError>`'s `Err` field.
fn nested_enum_field_type(
    name: &str,
    variant: &str,
    index: usize,
) -> Result<Option<InterfaceType>, String> {
    let enum_type = EnumTypes::get(name)?.algebraic_type();
    let Some(AlgebraicValueType::Algebraic { name: field, .. }) = enum_type
        .variants
        .iter()
        .find(|declared| declared.name == variant)
        .and_then(|declared| declared.fields.get(index))
    else {
        return Ok(None);
    };
    Ok(Some(InterfaceType::Parameter(EnumTypes::get(field)?)))
}

fn enum_construct(
    name: &str,
    variant: &str,
    fields: impl IntoIterator<Item = Result<ProgramExpression, String>>,
) -> Result<ProgramExpression, String> {
    let enum_type = EnumTypes::get(name)?;
    let declared = enum_type
        .algebraic_type()
        .variants
        .iter()
        .find(|declared| declared.name == variant)
        .map(|declared| declared.fields.clone())
        .ok_or_else(|| format!("unknown variant `{variant}` of a Rust enum"))?;
    // A field is converted to its declared type as an assignment is.
    let fields = fields
        .into_iter()
        .zip(&declared)
        .map(|(field, declared)| {
            let value = field?;
            Ok(match declared {
                AlgebraicValueType::Program(interface_type) => {
                    crate::kernel::program_expression::cast(value, *interface_type)
                }
                _ => value,
            })
        })
        .collect::<Result<_, String>>()?;
    Ok(ProgramExpression::EnumConstruct {
        enum_type,
        variant: variant.into(),
        fields,
    })
}

/// Lower the Rust panic checks for already prepared binary operands.
fn binary_checks(
    mut prefix: ProgramStatement,
    operator: &str,
    left_type: &Type,
    right_type: &Type,
    left_operand: &ProgramExpression,
    right_operand: &ProgramExpression,
) -> Result<ProgramStatement, String> {
    if matches!(left_type, Type::Usize | Type::U64) {
        let l = left_operand.clone();
        let r = right_operand.clone();
        let max = crate::kernel::program_expression::uint64_literal(u64::MAX);
        // Stay unsigned at the full target width. Widening to
        // signed i64 would lose half of the usize value range.
        let obligation = match operator {
            "add" => Some(crate::kernel::program_expression::less_equal(
                l,
                crate::kernel::program_expression::subtract(max, r),
            )),
            "sub" => Some(crate::kernel::program_expression::greater_equal(l, r)),
            "mul" => Some(crate::kernel::program_expression::or(
                crate::kernel::program_expression::equal(
                    r.clone(),
                    crate::kernel::program_expression::uint64_literal(0),
                ),
                crate::kernel::program_expression::less_equal(
                    l,
                    crate::kernel::program_expression::divide(max, r),
                ),
            )),
            "shl" | "shr" => Some(crate::kernel::program_expression::less_than(
                crate::kernel::program_expression::cast(r, ProgramType::UInt64),
                crate::kernel::program_expression::uint64_literal(64),
            )),
            _ => None,
        };
        if let Some(obligation) = obligation {
            prefix = program_seq(
                prefix,
                program_labeled_assert(obligation, format!("Rust {operator} panic check")),
            );
        }
    }
    // A signed shift panics in Rust unless its count is below
    // the operand's width. C checks only the promoted word's
    // width, which for `i8` and `i16` is 32, so the check is
    // explicit; a negative count is a large unsigned one.
    if left_type.is_signed_integer() && matches!(operator, "shl" | "shr") {
        let width = left_type
            .integer_bits()
            .ok_or("Rust signed shift operand has no width")?;
        let count = right_operand.clone();
        let obligation = if right_type.integer_bits() == Some(64) {
            crate::kernel::program_expression::less_than(
                crate::kernel::program_expression::cast(count, ProgramType::UInt64),
                crate::kernel::program_expression::uint64_literal(width.into()),
            )
        } else {
            crate::kernel::program_expression::less_than(
                crate::kernel::program_expression::cast(count, ProgramType::UInt32),
                crate::kernel::program_expression::uint32_literal(width),
            )
        };
        prefix = program_seq(
            prefix,
            program_labeled_assert(obligation, format!("Rust {operator} panic check")),
        );
    }
    // Narrow signed arithmetic is computed in `int`, where it
    // cannot overflow; Rust panics unless the result fits.
    if matches!(left_type, Type::I8 | Type::I16) && matches!(operator, "add" | "sub" | "mul") {
        let l = crate::kernel::program_expression::cast(left_operand.clone(), ProgramType::Int32);
        let r = crate::kernel::program_expression::cast(right_operand.clone(), ProgramType::Int32);
        let (minimum, maximum) = match left_type {
            Type::I8 => (i8::MIN as i64, i8::MAX as i64),
            _ => (i16::MIN as i64, i16::MAX as i64),
        };
        let wide = |value: ProgramExpression| {
            crate::kernel::program_expression::cast(value, ProgramType::Int64)
        };
        let value = match operator {
            "add" => crate::kernel::program_expression::add(wide(l), wide(r)),
            "sub" => crate::kernel::program_expression::subtract(wide(l), wide(r)),
            _ => crate::kernel::program_expression::multiply(wide(l), wide(r)),
        };
        prefix = program_seq(
            prefix,
            program_labeled_assert(
                crate::kernel::program_expression::and(
                    crate::kernel::program_expression::greater_equal(
                        value.clone(),
                        crate::kernel::program_expression::int64_literal(minimum),
                    ),
                    crate::kernel::program_expression::less_equal(
                        value,
                        crate::kernel::program_expression::int64_literal(maximum),
                    ),
                ),
                format!("Rust {operator} panic check"),
            ),
        );
    }
    if matches!(left_type, Type::U8 | Type::U16 | Type::U32) {
        let l = crate::kernel::program_expression::cast(left_operand.clone(), ProgramType::UInt32);
        let r = crate::kernel::program_expression::cast(right_operand.clone(), ProgramType::UInt32);
        let width = match left_type {
            Type::U8 => 8,
            Type::U16 => 16,
            _ => 32,
        };
        let maximum = match left_type {
            Type::U8 => 255,
            Type::U16 => 65535,
            _ => u32::MAX,
        };
        let max = crate::kernel::program_expression::uint32_literal(maximum);
        // Stay unsigned, as `usize` does: `max - r` cannot wrap,
        // and a guard such as `l < n` then bounds `l` directly.
        let obligation = match operator {
            "add" => Some(crate::kernel::program_expression::less_equal(
                l,
                crate::kernel::program_expression::subtract(max.clone(), r),
            )),
            "sub" => Some(crate::kernel::program_expression::greater_equal(l, r)),
            "mul" => Some(crate::kernel::program_expression::or(
                crate::kernel::program_expression::equal(
                    r.clone(),
                    crate::kernel::program_expression::uint32_literal(0),
                ),
                crate::kernel::program_expression::less_equal(
                    l,
                    crate::kernel::program_expression::divide(max, r),
                ),
            )),
            "shl" | "shr" => Some(if right_type.integer_bits() == Some(64) {
                crate::kernel::program_expression::less_than(
                    crate::kernel::program_expression::cast(
                        right_operand.clone(),
                        ProgramType::UInt64,
                    ),
                    crate::kernel::program_expression::uint64_literal(width),
                )
            } else {
                crate::kernel::program_expression::less_than(
                    r,
                    crate::kernel::program_expression::uint32_literal(width as u32),
                )
            }),
            _ => None,
        };
        if let Some(obligation) = obligation {
            prefix = program_seq(
                prefix,
                program_labeled_assert(obligation, format!("Rust {operator} panic check")),
            );
        }
    }
    Ok(prefix)
}

fn binary_value(
    operator: &str,
    left_type: &Type,
    right_type: &Type,
    mut l: ProgramExpression,
    r: ProgramExpression,
) -> Result<ProgramExpression, String> {
    // A Rust comparison of two 8- or 16-bit values is native
    // at their type (`design/machine-integers.md`, Decisions
    // 2026-11-01): its operands keep their width, and the `bool`
    // value below reads the comparison at it.
    let narrow = matches!(left_type, Type::U8 | Type::U16 | Type::I8 | Type::I16);
    let narrow_comparison = narrow && matches!(operator, "eq" | "ne" | "lt" | "le" | "gt" | "ge");
    // Rust `+ - * & | ^ <<` on 8- or 16-bit values are the
    // operators of that type (decision G4): native nodes over the
    // operands as written. A checked operator's overflow panic is
    // its own assertion (`prepared_expr`). A native shift's count
    // is a 32-bit word; a count of another width keeps the
    // promoted shift.
    let narrow_signed_division =
        matches!(left_type, Type::I8 | Type::I16) && matches!(operator, "div" | "rem");
    let narrow_operator = narrow_signed_division
        || narrow
            && (matches!(
                operator,
                "add" | "sub" | "mul" | "bit_and" | "bit_or" | "bit_xor"
            ) || (operator == "shl" && right_type.integer_bits() == Some(32)));
    // Keep the RHS at its source width. The shared shift evaluator
    // checks signed/nonnegative and full-width upper bounds before
    // forming its word-sized shift term. Narrowing here would lose
    // the exact relation to Rust's already checked count.
    if narrow_signed_division || (narrow && !narrow_comparison && !narrow_operator) {
        // Signed division/remainder and the remaining promoted narrow
        // operators use a 32-bit operation and a cast back (decision G4).
        crate::kernel::machine_integer::format_audit::record(
            crate::kernel::machine_integer::format_audit::WordIdentity::PromotedNarrowArithmetic,
            std::panic::Location::caller(),
        );
    }
    if narrow_comparison || narrow_operator {
    } else if matches!(left_type, Type::U8 | Type::U16) {
        // Narrow unsigned remainder fits in signed int, matching
        // the promotion used by its contract expression. Other
        // operations keep unsigned words (notably u16 multiply).
        l = crate::kernel::program_expression::cast(
            l,
            if operator == "rem" {
                ProgramType::Int32
            } else {
                ProgramType::UInt32
            },
        );
    } else if left_type.is_signed_integer() && operator == "shl" {
        // A signed left shift wraps in Rust and may be undefined
        // in C: shift the bits as an unsigned word of at least
        // the operand's width, then reinterpret them at the
        // operand's width below.
        l = crate::kernel::program_expression::cast(
            l,
            if left_type.integer_bits() == Some(64) {
                ProgramType::UInt64
            } else {
                ProgramType::UInt32
            },
        );
    } else if matches!(left_type, Type::I8 | Type::I16) {
        l = crate::kernel::program_expression::cast(l, ProgramType::Int32);
    }
    let result = match operator {
        "add" => crate::kernel::program_expression::add(l, r),
        "sub" => crate::kernel::program_expression::subtract(l, r),
        "mul" => crate::kernel::program_expression::multiply(l, r),
        "div" => crate::kernel::program_expression::divide(l, r),
        "rem" => crate::kernel::program_expression::remainder(l, r),
        "shl" => crate::kernel::program_expression::shift_left(l, r),
        "shr" => crate::kernel::program_expression::shift_right(l, r),
        "bit_and" => crate::kernel::program_expression::bitwise_and(l, r),
        "bit_or" => crate::kernel::program_expression::bitwise_or(l, r),
        "bit_xor" => crate::kernel::program_expression::bitwise_xor(l, r),
        "eq" => crate::kernel::program_expression::equal(l, r),
        "ne" => crate::kernel::program_expression::not_equal(l, r),
        "lt" => crate::kernel::program_expression::less_than(l, r),
        "le" => crate::kernel::program_expression::less_equal(l, r),
        "gt" => crate::kernel::program_expression::greater_than(l, r),
        "ge" => crate::kernel::program_expression::greater_equal(l, r),
        "and" => crate::kernel::program_expression::and(l, r),
        "or" => crate::kernel::program_expression::or(l, r),
        _ => return Err("unsupported Rust operator in artifact".into()),
    };
    if matches!(
        operator,
        "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or"
    ) {
        // A Rust comparison or connective is a `bool` value: the
        // condition itself, with no path split (Stage 5, D5).
        Ok(crate::kernel::program_expression::bool_value(result))
    } else if narrow_operator {
        Ok(crate::kernel::program_expression::narrow_arithmetic(
            result,
            scalar_type(left_type)?.to_kernel_type(),
        ))
    } else if narrow && matches!(operator, "div" | "rem") {
        // This path is the existing unsigned result conversion.
        Ok(crate::kernel::program_expression::cast(
            result,
            scalar_type(left_type)?.to_kernel_type(),
        ))
    } else {
        Ok(rust_scalar_cast(
            result,
            scalar_type(left_type)?.to_kernel_type(),
        ))
    }
}

/// Read an operand before its last use.
fn observe_operand(mut value: ProgramExpression) -> ProgramExpression {
    if let ProgramExpression::StepResult { ends, .. } = &mut value {
        *ends = false;
    }
    value
}

fn typed_value_step(
    steps: Vec<u32>,
    expression: ProgramExpression,
    value_type: ProgramType,
    pointee_constant: bool,
) -> ProgramStatement {
    ProgramStatement::StepValue {
        aggregate_layout: None,
        steps,
        expression,
        value_type: Some(value_type),
        pointee_constant,
    }
}

/// Whether `value` is a local or a literal, possibly converted: a read with
/// no work of its own that names itself.
fn direct_operand(value: &ProgramExpression) -> bool {
    match value {
        ProgramExpression::Variable(_) | ProgramExpression::Value(_) => true,
        ProgramExpression::Cast { expression, .. } => direct_operand(expression),
        _ => false,
    }
}

/// Whether `value` is a local's address or a reference a local holds.
fn borrowed_local(value: &ProgramExpression) -> bool {
    match value {
        ProgramExpression::Variable(_) => true,
        ProgramExpression::AddressOf(target) => {
            matches!(target.as_ref(), ProgramExpression::Variable(_))
        }
        ProgramExpression::Cast { expression, .. } => borrowed_local(expression),
        _ => false,
    }
}

/// Whether running `statement` changes nothing: it is empty.
fn no_effect(statement: &ProgramStatement) -> bool {
    match statement {
        ProgramStatement::Skip => true,
        ProgramStatement::Seq(statements) => statements.iter().all(|s| no_effect(s)),
        _ => false,
    }
}

/// The slice local `slice` reads: the local itself, or a shared borrow of it,
/// `&bytes`, which has the same pointer and length.
pub(super) fn shared_slice_local(slice: &E) -> Option<&MirLocalId> {
    match slice {
        E::Local { name } => Some(name),
        E::Borrow {
            place,
            value_type: Type::ByteSlice { mutable: false },
        } => match place.as_ref() {
            E::Local { name } => Some(name),
            _ => None,
        },
        _ => None,
    }
}

/// The slice type of a shared slice `&[T]` of a scalar `T`, a wide pointer
/// (`design/rust-slice-values.md`); `None` for any other type.
fn shared_slice_type(t: &Type) -> Result<Option<ProgramType>, String> {
    let slice = match t {
        Type::ByteSlice { mutable: false } | Type::ScalarSlice { mutable: false, .. } => t,
        Type::Reference {
            mutable: false,
            pointee,
        } if matches!(
            pointee.as_ref(),
            Type::ByteSlice { .. } | Type::ScalarSlice { .. }
        ) =>
        {
            pointee.as_ref()
        }
        _ => return Ok(None),
    };
    let element = match slice {
        Type::ScalarSlice { element, .. } => scalar_type(element)?,
        _ => InterfaceType::UInt8,
    };
    let thin = element
        .pointer_type()
        .ok_or("a slice's element must be a scalar")?;
    Ok(
        crate::kernel::SliceElement::of_thin_pointer_type(thin.to_kernel_type())
            .map(ProgramType::SlicePointer),
    )
}

/// The kernel element of a Rust slice of `element`, a scalar.
fn slice_element(element: &Type) -> Result<crate::kernel::SliceElement, String> {
    scalar_type(element)?
        .pointer_type()
        .and_then(|thin| crate::kernel::SliceElement::of_thin_pointer_type(thin.to_kernel_type()))
        .ok_or_else(|| "a slice's element must be a scalar".into())
}

/// The kernel type of a Rust value: a slice's wide pointer type, or a
/// scalar's type.
fn value_program_type(t: &Type) -> Result<ProgramType, String> {
    match slice_program_type(t)? {
        Some(slice) => Ok(slice),
        None => Ok(scalar_type(t)?.to_kernel_type()),
    }
}

/// The slice type of a slice-typed Rust local or parameter: `&[T]` and
/// `&mut [T]` of a scalar `T`, one wide pointer
/// (`design/rust-slice-values.md`, step 3b).
fn slice_program_type(t: &Type) -> Result<Option<ProgramType>, String> {
    Ok(match t {
        Type::ByteSlice { .. } => Some(ProgramType::SlicePointer(
            crate::kernel::SliceElement::UInt8,
        )),
        Type::StrSlice => Some(ProgramType::SlicePointer(crate::kernel::SliceElement::Str)),
        Type::ScalarSlice { element, .. } => {
            Some(ProgramType::SlicePointer(slice_element(element)?))
        }
        _ => None,
    })
}

fn scalar_type(t: &Type) -> Result<InterfaceType, String> {
    match t {
        Type::Enum { name } => Ok(InterfaceType::Parameter(EnumTypes::get(name)?)),
        Type::I8 => Ok(InterfaceType::Int8),
        Type::I16 => Ok(InterfaceType::Int16),
        Type::I32 => Ok(InterfaceType::Int32),
        Type::I64 | Type::Isize => Ok(InterfaceType::Int64(LongRank::Long)),
        Type::U8 => Ok(InterfaceType::UInt8),
        Type::U16 => Ok(InterfaceType::UInt16),
        Type::U32 => Ok(InterfaceType::UInt32),
        Type::U64 | Type::Usize => Ok(InterfaceType::UInt64(LongRank::Long)),
        Type::Bool => Ok(InterfaceType::Bool),
        Type::Unit => Ok(InterfaceType::Void),
        Type::Parameter { name } => Ok(InterfaceType::Parameter(
            crate::kernel::TypeParameterName::intern(name),
        )),
        Type::Vec { element } => Ok(InterfaceType::Parameter(vec_type(element)?)),
        // A box of a crate struct is its address, as a struct reference is.
        Type::Box { .. } | Type::OptionBox { .. } => Ok(InterfaceType::Int32Pointer),
        Type::Reference { pointee, .. } => match pointee.as_ref() {
            // A reference to a value of unknown type is opaque as a struct
            // reference is: nothing is read through it without its fields.
            Type::I32 | Type::Record { .. } | Type::TraitObject => Ok(InterfaceType::Int32Pointer),
            Type::U8 => Ok(InterfaceType::UInt8Pointer),
            Type::U16 => Ok(InterfaceType::UInt16Pointer),
            Type::U32 => Ok(InterfaceType::UInt32Pointer),
            Type::I8 => Ok(InterfaceType::Int8Pointer),
            Type::I16 => Ok(InterfaceType::Int16Pointer),
            Type::I64 | Type::Isize => Ok(InterfaceType::Int64Pointer(LongRank::Long)),
            Type::U64 | Type::Usize => Ok(InterfaceType::UInt64Pointer(LongRank::Long)),
            Type::Parameter { name } => Ok(InterfaceType::ParameterPointer(
                crate::kernel::TypeParameterName::intern(name),
            )),
            // An enum value is a spec value, as a type parameter's is.
            Type::Enum { name } => Ok(InterfaceType::ParameterPointer(EnumTypes::get(name)?)),
            Type::Vec { element } => Ok(InterfaceType::ParameterPointer(vec_type(element)?)),
            Type::Array { element, .. } => match element.as_ref() {
                Type::I32 => Ok(InterfaceType::Int32Pointer),
                Type::U8 => Ok(InterfaceType::UInt8Pointer),
                Type::U32 => Ok(InterfaceType::UInt32Pointer),
                _ => Err("fixed arrays require i32, u8 or u32 elements".into()),
            },
            _ => Err("Rust reference pointee outside scalar/reference lowering".into()),
        },
        Type::Array { .. } => Err("Rust array values require whole-array lowering".into()),
        Type::FnPointer { .. } => Ok(fn_pointer_signature(t)?.pointer_type()),
        _ => Err("Rust value type outside direct scalar/reference lowering".into()),
    }
}
/// The type of a `Vec<element>` value: the library's primitive `Vec` at
/// `element`, which the kernel reads as a rigid type of its own.
fn vec_type(element: &Type) -> Result<crate::kernel::TypeParameterName, String> {
    let element = scalar_type(element)?.to_kernel_type();
    Ok(crate::kernel::TypeParameterName::of(
        &crate::surface::primitive_instance_type("Vec", &[AlgebraicValueType::Program(element)]),
    ))
}
/// A function-pointer type's signature, as a sidecar's `fn(i32) -> i32`
/// parameter type spells it.
fn fn_pointer_signature(t: &Type) -> Result<CallbackInterface, String> {
    let Type::FnPointer { parameters, result } = t else {
        return Err("Rust function-pointer signature requires a function-pointer type".into());
    };
    let parameters = parameters
        .iter()
        .map(|parameter| {
            let interface_type = scalar_type(parameter)?;
            if interface_type == InterfaceType::Void || interface_type.is_pointer() {
                return Err("Rust function-pointer parameters must be scalars".to_string());
            }
            Ok(CallbackParameter::new(interface_type, None, false))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let result = scalar_type(result)?;
    if result.is_pointer() {
        return Err("Rust function-pointer results must be scalars or unit".into());
    }
    Ok(CallbackInterface::new(result, None, parameters, false))
}
// Embedded arrays retain one ABI field and their concrete length. Never
// flatten a field into one layout entry per element.
fn record_field_type(t: &Type) -> Result<InterfaceType, String> {
    let Type::Array { element, length } = t else {
        return scalar_type(t);
    };
    let element = scalar_type(element)?.to_kernel_type();
    let length = arrays::array_length(element, *length)?;
    Ok(match element {
        ProgramType::Int32 => InterfaceType::Int32Array(length),
        ProgramType::UInt8 => InterfaceType::UInt8Array(length),
        ProgramType::UInt32 => InterfaceType::UInt32Array(length),
        _ => unreachable!(),
    })
}
fn array_field_parts(t: ProgramType) -> Option<(ProgramType, u32)> {
    match t {
        ProgramType::Int32Array(n) => Some((ProgramType::Int32, n)),
        ProgramType::UInt8Array(n) => Some((ProgramType::UInt8, n)),
        ProgramType::UInt32Array(n) => Some((ProgramType::UInt32, n)),
        _ => None,
    }
}
// Rust integer `as` uses the same explicit modulo policy as C++20.
/// The Rust integer type a slice or array element of C type `element` is.
fn indexed_element_type(element: ProgramType) -> Option<Type> {
    Some(match element {
        ProgramType::UInt8 => Type::U8,
        ProgramType::UInt16 => Type::U16,
        ProgramType::UInt32 => Type::U32,
        ProgramType::UInt64 => Type::U64,
        ProgramType::Int8 => Type::I8,
        ProgramType::Int16 => Type::I16,
        ProgramType::Int32 => Type::I32,
        ProgramType::Int64 => Type::I64,
        _ => return None,
    })
}
/// A branch's or loop's condition: a `bool` value written as a condition is
/// the comparison it tests, which the branch splits on (Stage 5, D5).
fn branch_condition(condition: ProgramExpression) -> ProgramExpression {
    match condition {
        ProgramExpression::Cast {
            expression,
            integer_mode: IntegerCastMode::BoolValue,
            ..
        } => *expression,
        condition => condition,
    }
}

fn rust_scalar_cast(value: ProgramExpression, target: ProgramType) -> ProgramExpression {
    if crate::kernel::MachineIntegerType::from_program_type(target).is_some() {
        crate::kernel::program_expression::integer_cast_modulo(value, target)
    } else if target.is_pointer() {
        reference_view(value, target, false, false)
    } else {
        crate::kernel::program_expression::cast(value, target)
    }
}
/// Rust `!value` on an integer of type `target`: at 8 or 16 bits the native
/// complement of that type (decision G4), otherwise the complement of the
/// value's word converted modularly to `target`.
fn rust_bitwise_not(value: ProgramExpression, target: ProgramType) -> ProgramExpression {
    if matches!(
        target,
        ProgramType::Int8 | ProgramType::UInt8 | ProgramType::Int16 | ProgramType::UInt16
    ) {
        crate::kernel::program_expression::narrow_arithmetic(
            crate::kernel::program_expression::bitwise_not(value),
            target,
        )
    } else {
        rust_scalar_cast(
            crate::kernel::program_expression::bitwise_not(value),
            target,
        )
    }
}
fn integer_from(
    value: ProgramExpression,
    source: &Type,
    target: &Type,
) -> Result<ProgramExpression, String> {
    if !source.converts_losslessly_to(target) {
        return Err("integer From requires a supported lossless conversion".into());
    }
    Ok(crate::kernel::program_expression::cast(
        value,
        scalar_type(target)?.to_kernel_type(),
    ))
}
pub(crate) fn lower(export: &RustExport) -> Result<LoweredRust, String> {
    lower_with_identity(export, None)
}
pub(crate) fn lower_with_identity(
    export: &RustExport,
    identity: Option<&str>,
) -> Result<LoweredRust, String> {
    // Enum fields are scalars, so their types need no other enum's.
    let _enums = EnumTypes::enter(export)?;
    let mut layouts = BTreeMap::new();
    let mut fields = BTreeMap::new();
    for record in &export.records {
        let mut layout_fields = record
            .fields
            .iter()
            .map(|f| {
                Ok((
                    f.name.clone(),
                    record_field_type(&f.value_type)?,
                    match &f.value_type {
                        Type::Reference { pointee, .. }
                        | Type::Box { pointee }
                        | Type::OptionBox { pointee } => match pointee.as_ref() {
                            Type::Record { name } => Some(name.clone()),
                            _ => None,
                        },
                        _ => None,
                    },
                    f.offset,
                    record_field_type(&f.value_type)?
                        .to_kernel_type()
                        .byte_width(),
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let layout = if record.symbolic {
            // An abstract instance's offsets are terms, in declaration order.
            RecordLayout::symbolic(
                &record.name,
                layout_fields
                    .into_iter()
                    .map(|(name, field_type, pointee, _, _)| (name, field_type, pointee))
                    .collect(),
                record.alignment,
            )?
        } else {
            // Rust may reorder fields; declaration order still selects
            // constructor operands, while layout validation consumes
            // physical offset order.
            layout_fields.sort_by_key(|f| f.3);
            // Pointer fields keep their nominal pointee for chained field
            // reads. They do not embed its layout, so recursive records
            // need no traversal.
            RecordLayout::from_explicit_fields_with_structs(
                layout_fields,
                record.size,
                record.alignment,
                &BTreeMap::new(),
            )?
        };
        // A box field, or an option of one, holds its type resource.
        let mut layout = layout;
        for f in &record.fields {
            let (optional, pointee) = match &f.value_type {
                Type::Box { pointee } => (false, pointee),
                Type::OptionBox { pointee } => (true, pointee),
                _ => continue,
            };
            if let Type::Record { name } = pointee.as_ref() {
                layout = layout.with_boxed_field(
                    &f.name,
                    crate::languages::interface::BoxedField {
                        optional,
                        record: name.clone(),
                    },
                );
            }
        }
        for f in &record.fields {
            if fields
                .insert(
                    (record.name.as_str(), f.name.as_str()),
                    (
                        layout.field(&f.name).ok_or("unknown Rust field")?.offset(),
                        record_field_type(&f.value_type)?.to_kernel_type(),
                    ),
                )
                .is_some()
            {
                return Err("duplicate Rust field".into());
            }
        }
        if layouts.insert(record.name.clone(), layout).is_some() {
            return Err("duplicate Rust record".into());
        }
    }
    let record_index = export
        .records
        .iter()
        .map(|r| (r.name.as_str(), r))
        .collect::<BTreeMap<_, _>>();
    let destructors = export
        .records
        .iter()
        .filter(|record| matches!(record.destructor, Some(super::schema::Destructor::Implicit)))
        .map(|record| {
            let target = super::names::RustDestructor {
                record: record.name.clone(),
            };
            (target.contract_name(), target)
        })
        .collect::<BTreeMap<_, _>>();
    let function_index = export
        .functions
        .iter()
        .map(|f| (f.name.as_str(), f))
        .collect::<BTreeMap<_, _>>();
    let mut names = BTreeSet::new();
    let mut functions = Vec::new();
    for f in &export.functions {
        if !names.insert(f.name.clone()) {
            return Err("duplicate Rust function name".into());
        }
        let mut function = lower_function(
            export,
            identity,
            f,
            &fields,
            &layouts,
            &record_index,
            &function_index,
        )
        .map_err(|error| located(&export.logical_source, f, error))?;
        function.rust_destructor = destructors.get(&f.name).cloned();
        functions.push(function);
    }
    Ok((functions, layouts))
}
/// `error`, refusing to lower `f`, with the function's source location
/// unless it already names one.
fn located(source: &str, f: &Function, error: String) -> String {
    if error.starts_with(&format!("{source}:")) {
        return error;
    }
    let name = super::names::display_rust_names(&f.name);
    format!("{source}:{} in {name}: {error}", f.span.line)
}

fn lower_function(
    export: &RustExport,
    identity: Option<&str>,
    f: &Function,
    fields: &BTreeMap<(&str, &str), (crate::kernel::LayoutOffset, ProgramType)>,
    layouts: &BTreeMap<String, RecordLayout>,
    records: &BTreeMap<&str, &Record>,
    functions: &BTreeMap<&str, &Function>,
) -> Result<ImportedFunction, String> {
    if !(f.return_type.is_scalar()
        || matches!(
            f.return_type,
            Type::Unit
                | Type::Record { .. }
                | Type::Enum { .. }
                | Type::Parameter { .. }
                | Type::Vec { .. }
                | Type::Box { .. }
                | Type::OptionBox { .. }
                | Type::ByteSlice { .. }
                | Type::ScalarSlice { .. }
                | Type::StrSlice
        ))
    {
        return Err("Rust reference/aggregate returns are not supported".into());
    }
    let return_layout = match &f.return_type {
        Type::Record { name } => Some((
            name,
            layouts.get(name).ok_or("missing return record layout")?,
        )),
        _ => None,
    };
    // A slice result is one wide value, as a slice parameter is
    // (`design/rust-slice-values.md`, step 3c).
    let return_type = if return_layout.is_some() {
        InterfaceType::UInt8Pointer
    } else if let Some(ProgramType::SlicePointer(slice)) = slice_program_type(&f.return_type)? {
        InterfaceType::Slice(slice)
    } else {
        scalar_type(&f.return_type)?
    };
    // Instances retain the names of their generic contract. Other bodyless
    // declarations can take their parameter names from the sidecar head.
    let instance_of = if f.external {
        f.instance_of
            .clone()
            .or_else(|| super::standard_library::library_generic(f))
    } else {
        None
    };
    let owner = LocalFunctionId::new(Some(export.logical_source.clone()), f.name.clone());
    let mut parameters = Vec::new();
    let mut kernel_parameters = Vec::new();
    let mut locals = BTreeSet::new();
    let mut slices = BTreeMap::new();
    let mut shared_scalar_slices = BTreeMap::new();
    let mut arrays = BTreeMap::new();
    let mut references = BTreeMap::new();
    for (position, p) in f.parameters.iter().enumerate() {
        let spelling = || p.name.source_name().ok_or("unnamed Rust parameter");
        let binding = match &p.name {
            MirLocalId::Source(name) => BindingName::from(name.clone()),
            MirLocalId::PositionalParameter { position: slot }
                if f.external && instance_of.is_none() && *slot == position =>
            {
                let ordinal = u32::try_from(position).map_err(|_| "too many Rust parameters")?;
                BindingName::from(LocalBindingId::new(owner.clone(), true, ordinal, None))
            }
            _ => return Err("unnamed Rust parameter".into()),
        };
        crate::instrumentation::record_deterministic_work(1);
        if matches!(p.value_type, Type::Array { .. }) {
            return Err("by-value Rust arrays as parameters are not supported".into());
        }
        if !locals.insert(p.name.clone()) {
            return Err("duplicate Rust parameter".into());
        }
        if let Type::Record { name } = &p.value_type {
            // A generic function's instance takes the record as the
            // generic function, whose MIR is checked, does; a library
            // function takes it as its contract says.
            if f.mir.is_none() && f.instance_of.is_none() && f.core_method.is_none() {
                return Err("owned record parameters require compiler MIR".into());
            }
            let layout = layouts.get(name).ok_or("missing parameter record layout")?;
            let parameter =
                ImportedParameter::from_binding(InterfaceType::UInt8Pointer, binding, None)
                    .with_struct_value(name.clone(), layout.clone());
            kernel_parameters.push(parameter.to_kernel_parameter());
            parameters.push(parameter);
            continue;
        }
        // A slice parameter is one wide pointer, its data pointer and
        // element count (`design/rust-slice-values.md`, step 3b).
        if let Type::ByteSlice { .. } | Type::ScalarSlice { .. } | Type::StrSlice = &p.value_type {
            let mutable = matches!(
                p.value_type,
                Type::ByteSlice { mutable: true } | Type::ScalarSlice { mutable: true, .. }
            );
            if let Type::ScalarSlice { element, .. } = &p.value_type {
                if !element.is_integer() {
                    return Err("scalar slice parameters require integer elements".into());
                }
                shared_scalar_slices.insert(p.name.clone(), scalar_type(element)?.to_kernel_type());
            } else {
                // A string slice's body reads it as its bytes.
                slices.insert(p.name.clone(), !mutable);
            }
            let Some(ProgramType::SlicePointer(slice)) = slice_program_type(&p.value_type)? else {
                unreachable!("a slice parameter has a slice type")
            };
            parameters.push(
                ImportedParameter::from_binding(InterfaceType::Slice(slice), binding.clone(), None)
                    .with_pointee_constant(!mutable),
            );
            kernel_parameters.push(
                program_parameter(binding, ProgramType::SlicePointer(slice))
                    .with_pointee_constant(!mutable),
            );
            continue;
        }
        if let Type::Reference { mutable, .. } = &p.value_type {
            references.insert(p.name.clone(), !mutable);
        }
        if let Type::FnPointer { .. } = &p.value_type {
            let signature = fn_pointer_signature(&p.value_type)?;
            kernel_parameters.push(program_parameter(
                binding,
                signature.pointer_type().to_kernel_type(),
            ));
            parameters.push(ImportedParameter::function_pointer(
                spelling()?.to_owned(),
                signature,
            ));
            continue;
        }
        let interface_type = scalar_type(&p.value_type)?;
        if let Type::Reference { mutable, pointee } = &p.value_type
            && let Type::Array { element, length } = pointee.as_ref()
        {
            let element = scalar_type(element)?.to_kernel_type();
            if *length > i32::MAX as u64 / u64::from(element.byte_width()) {
                return Err("fixed array storage exceeds the signed-word memory model".into());
            }
            arrays.insert(p.name.clone(), (*length, element, !mutable));
        }
        if interface_type == InterfaceType::Void {
            return Err("unit parameters outside Rust slice".into());
        }
        let (tag, constant) = match &p.value_type {
            Type::Reference { mutable, pointee } => (
                match pointee.as_ref() {
                    Type::Record { name } => Some(name.clone()),
                    _ => None,
                },
                !mutable,
            ),
            // A box is the address of the struct it owns.
            Type::Box { pointee } | Type::OptionBox { pointee } => (
                match pointee.as_ref() {
                    Type::Record { name } => Some(name.clone()),
                    _ => None,
                },
                false,
            ),
            _ => (None, false),
        };
        let mut parameter =
            ImportedParameter::from_binding(interface_type, binding.clone(), tag.clone())
                .with_pointee_constant(constant);
        // The record's layout is what seeds a whole-record `owns *x` at its
        // fields' widths, so a 64-bit field reads as one cell.
        let mut kernel_parameter = program_parameter(binding, interface_type.to_kernel_type())
            .with_pointee_constant(constant);
        if let Some(layout) = tag.as_ref().and_then(|name| layouts.get(name)) {
            parameter = parameter.with_pointee_struct_layout(tag.clone().unwrap(), layout.clone());
            // A reference or box to a symbolic struct designates its whole
            // object, `sizeof(S)` bytes, inside which each field lies.
            if matches!(p.value_type, Type::Reference { .. } | Type::Box { .. })
                && let size @ crate::kernel::LayoutSize::Of(_) = layout.size()
            {
                parameter = parameter.with_fixed_reference_bounds(size);
                kernel_parameter = kernel_parameter.with_fixed_reference_bounds(size);
            }
        }
        if let Some((length, element, _)) = arrays.get(&p.name) {
            let bytes = u32::try_from(*length * u64::from(element.byte_width()))
                .expect("validated fixed array length");
            parameter = parameter.with_fixed_reference_bounds(bytes);
            kernel_parameter = kernel_parameter.with_fixed_reference_bounds(bytes);
        }
        parameters.push(parameter);
        kernel_parameters.push(kernel_parameter);
    }
    // A declaration in an `extern` block has no body to execute: its calls
    // are checked against the sidecar's `extern fn` contract.
    if f.external {
        if f.mir.is_some() || !f.body.is_empty() {
            return Err("Rust extern function must not carry a body".into());
        }
        let generic = instance_of.is_some();
        let mut declaration = ImportedFunction::external(return_type, f.name.clone(), parameters)
            .with_generic_instance(instance_of);
        if let Some((name, layout)) = return_layout {
            declaration = declaration.with_struct_return(name.clone(), layout.clone());
        }
        // A generic function's instance names its parameters as the generic
        // function does.
        return Ok(if generic {
            declaration
        } else {
            declaration.with_positional_parameters()
        });
    }
    // Reserve the compiler's explicit MIR call IDs before allocating any
    // additional results for calls and operand evaluation.
    let next_result_step = f
        .mir
        .iter()
        .flat_map(|mir| &mir.blocks)
        .filter_map(|block| match &block.terminator {
            super::schema::MirTerminator::Call { result, .. } => *result,
            _ => None,
        })
        .max()
        .map(|last| last.checked_add(1).ok_or("too many calls in one function"))
        .transpose()?
        .unwrap_or(0);
    // A source name bound more than once is one declaration per binding,
    // spelled as the source spells it; MIR's local order is the
    // declaration order, so a proof's `word` is the innermost live one.
    let bindings = f
        .mir
        .iter()
        .flat_map(|mir| {
            mir.locals
                .iter()
                .enumerate()
                .filter_map(|(ordinal, local)| {
                    let id = if local.name == mir.return_place {
                        let id = LocalBindingId::return_place(owner.clone());
                        if let Ok(Some(slice)) = slice_program_type(&local.value_type) {
                            id.initialize_program_type(slice);
                        } else if let Ok(value_type) = scalar_type(&local.value_type) {
                            id.initialize_program_type(value_type.to_kernel_type());
                        }
                        id
                    } else if let Some(&ordinal) = mir.compound_literals.get(&local.name) {
                        let id = LocalBindingId::compound_literal(owner.clone(), ordinal);
                        match &local.value_type {
                            Type::Array { element, length } => {
                                let length = u32::try_from(*length).ok()?;
                                let array_type = match element.as_ref() {
                                    Type::I32 => ProgramType::Int32Array(length),
                                    Type::U8 => ProgramType::UInt8Array(length),
                                    Type::U32 => ProgramType::UInt32Array(length),
                                    _ => return None,
                                };
                                id.initialize_program_type(array_type);
                                id.initialize_array_shape(&[length]);
                            }
                            Type::Record { name } => id.initialize_struct_name(name),
                            _ => return None,
                        }
                        id
                    } else if let Some(&ordinal) = mir.borrowed_scalars.get(&local.name) {
                        LocalBindingId::temporary(owner.clone(), ordinal)
                    } else if matches!(local.name, MirLocalId::SliceComponent { .. }) {
                        let ordinal = u32::try_from(ordinal).ok()?;
                        LocalBindingId::slice_component(owner.clone(), ordinal)
                    } else {
                        let spelling = mir.spellings.get(&local.name).cloned();
                        // A compiler flag can be assigned and tested in
                        // different MIR blocks without a source name.
                        let compiler_flag = matches!(local.name, MirLocalId::Compiler(_))
                            && matches!(local.value_type, Type::Bool);
                        if spelling.is_none() && !compiler_flag {
                            return None;
                        }
                        let ordinal = u32::try_from(ordinal).ok()?;
                        LocalBindingId::new(owner.clone(), false, ordinal, spelling)
                    };
                    Some((local.name.clone(), BindingName::from(id)))
                })
        })
        .collect();
    let mut cx = Context {
        bindings,
        scalar_operands: BTreeMap::new(),
        declaration_sites: Vec::new(),
        shared_array_iterators: BTreeMap::new(),
        ranges: BTreeMap::new(),
        enumerate_fields: BTreeMap::new(),
        shared_array_options: BTreeMap::new(),
        shared_scalar_slices,
        mir_chunk_iterators: BTreeMap::new(),
        chunk_options: BTreeMap::new(),
        local_arrays: BTreeSet::new(),
        owned_locals: BTreeSet::new(),
        addressable_locals: BTreeSet::new(),
        memory_values: BTreeMap::new(),
        slices,
        arrays,
        references,
        source: &export.logical_source,
        function: &f.name,
        fields,
        next_load: 0,
        import_identity: identity.map(std::sync::Arc::from),
        mir_point: None,
        mir_nodes: BTreeMap::new(),
        next_result_step: std::cell::Cell::new(next_result_step),
        step_pointee_layouts: std::cell::RefCell::new(BTreeMap::new()),
        loop_iterators: Vec::new(),
        locals,
        return_type,
        layouts,
        records,
        functions,
    };
    let (body, source_sites) = match &f.mir {
        Some(mir) if f.body.is_empty() => {
            let lowered = moves::lower(&mut cx, f, mir, &owner)?;
            let regions = lowered
                .binding_calls
                .into_iter()
                .collect::<BTreeMap<_, _>>();
            let mut object_bindings = Vec::new();
            for binding in &mir.object_bindings {
                let Some(&call) = regions.get(&binding.call) else {
                    continue;
                };
                let region = |block| {
                    regions
                        .get(&block)
                        .copied()
                        .ok_or("Rust object binding lost its call region")
                };
                let super::schema::MirTerminator::Call {
                    function: MirCallee::Binding { binding: contract },
                    ..
                } = &mir.blocks[binding.acquire].terminator
                else {
                    return Err("Rust object binding lost its acquisition".into());
                };
                object_bindings.push(crate::languages::interface::ObjectBindingRegions {
                    argument: binding.argument,
                    binding: contract.clone(),
                    call,
                    acquire: region(binding.acquire)?,
                    release: region(binding.release)?,
                });
            }
            (lowered.statement, Some((lowered.sites, object_bindings)))
        }
        Some(_) => return Err("Rust function must select exactly one body representation".into()),
        None => (cx.body(&f.body)?, None),
    };
    let loop_iterators = std::mem::take(&mut cx.loop_iterators);
    let step_pointee_layouts = cx.step_pointee_layouts.take();
    let mut kernel = program_function(
        return_type.to_kernel_type(),
        &f.name,
        kernel_parameters,
        body,
    );
    if let Some((_, layout)) = return_layout {
        kernel = kernel.with_return_aggregate_layout(layout.to_kernel_aggregate_layout());
    }
    let local_records = f
        .mir
        .as_ref()
        .map(|mir| {
            mir.locals
                .iter()
                .filter_map(|local| match &local.value_type {
                    Type::Record { name } => Some(
                        cx.binding(&local.name)
                            .map(|binding| (binding, name.clone())),
                    ),
                    _ => None,
                })
                .collect::<Result<_, _>>()
        })
        .transpose()?
        .unwrap_or_default();
    let mut lowered = ImportedFunction::external(return_type, f.name.clone(), parameters)
        .with_local_struct_values(local_records)
        .with_step_pointee_layouts(step_pointee_layouts)
        .with_prelowered_kernel_function(kernel)
        .with_closure_captures(f.captures)
        .with_trait_interface(f.implements.clone())
        .with_loop_iterators(loop_iterators)
        .with_spelled_local_types(spelled_local_types(f));
    // Only MIR lowering supplies a map from kernel regions to source sites.
    // A structured body must not claim to supply an empty map for its regions.
    if let Some((regions, object_bindings)) = source_sites {
        lowered = lowered.with_source_sites(crate::languages::interface::SourceSites {
            paths: f.sites.clone(),
            regions,
            object_bindings,
            declarations: std::mem::take(&mut cx.declaration_sites),
        });
    }
    if let Some((name, layout)) = return_layout {
        lowered = lowered.with_struct_return(name.clone(), layout.clone());
    }
    Ok(lowered)
}
/// The declared type of each local the lowering binds by its spelling
/// alone: a source name bound once, which is no repeated name's and no
/// parameter's: a slice's wide pointer type, or a scalar's type. A local of
/// another type has none.
fn spelled_local_types(f: &super::schema::Function) -> BTreeMap<String, ProgramType> {
    let Some(mir) = &f.mir else {
        return BTreeMap::new();
    };
    mir.locals
        .iter()
        .filter(|local| !mir.spellings.contains_key(&local.name) && local.name != mir.return_place)
        .filter_map(|local| {
            let MirLocalId::Source(name) = &local.name else {
                return None;
            };
            Some((name.clone(), value_program_type(&local.value_type).ok()?))
        })
        .collect()
}

struct Context<'a> {
    /// The binding of each local whose source name is bound more than
    /// once, by its MIR key; every other local is bound by its name.
    bindings: BTreeMap<MirLocalId, BindingName>,
    /// Expression values retained until their last read.
    scalar_operands:
        BTreeMap<MirLocalId, (u32, crate::languages::rust::borrow_frontiers::MirPoint)>,
    /// Where each of those is declared: its binding and source statement
    /// (`Function::sites`), so `statement(i).local(word)` names it.
    declaration_sites: Vec<(BindingName, u32)>,
    shared_array_iterators: BTreeMap<MirLocalId, shared_arrays::SliceIteratorStorage>,
    /// The range locals, with their element type.
    ranges: BTreeMap<MirLocalId, ranges::RangeStorage>,
    /// The count of each enumerated slice iterator and the index of each yielded Option.
    enumerate_fields: BTreeMap<MirLocalId, BindingName>,
    shared_array_options: BTreeMap<MirLocalId, shared_arrays::SliceIteratorOptionStorage>,
    /// The scalar slice locals and parameters other than byte slices, with
    /// their element type.
    shared_scalar_slices: BTreeMap<MirLocalId, ProgramType>,
    mir_chunk_iterators: BTreeMap<MirLocalId, crate::languages::interface::ChunkIteratorFields>,
    chunk_options: BTreeMap<MirLocalId, chunks::ChunkOptionFields>,
    local_arrays: BTreeSet<MirLocalId>,
    owned_locals: BTreeSet<MirLocalId>,
    /// Integer and `bool` locals, which a borrow takes the address of.
    addressable_locals: BTreeSet<MirLocalId>,
    /// The enum and type-parameter locals the body borrows, with the C type
    /// of their value. Such a value otherwise lives in its local's binding;
    /// these live in their object's memory, so a write through the borrow
    /// is the value later reads see.
    memory_values: BTreeMap<MirLocalId, ProgramType>,
    /// The byte slice locals and parameters, and whether each is shared.
    slices: BTreeMap<MirLocalId, bool>,
    arrays: BTreeMap<MirLocalId, (u64, ProgramType, bool)>,
    references: BTreeMap<MirLocalId, bool>,
    source: &'a str,
    function: &'a str,
    fields: &'a BTreeMap<(&'a str, &'a str), (crate::kernel::LayoutOffset, ProgramType)>,
    next_load: u32,
    import_identity: Option<std::sync::Arc<str>>,
    mir_point: Option<super::borrow_frontiers::MirPoint>,
    mir_nodes: BTreeMap<usize, usize>,
    next_result_step: std::cell::Cell<u32>,
    /// The record each staged reference operand points at, by its step.
    step_pointee_layouts: std::cell::RefCell<BTreeMap<u32, crate::kernel::AggregateLayout>>,
    /// The iterator each loop advances, by loop index in preorder.
    loop_iterators: Vec<Option<crate::languages::interface::RustLoopIterator>>,
    locals: BTreeSet<MirLocalId>,
    return_type: InterfaceType,
    layouts: &'a BTreeMap<String, RecordLayout>,
    records: &'a BTreeMap<&'a str, &'a Record>,
    functions: &'a BTreeMap<&'a str, &'a Function>,
}
impl Context<'_> {
    /// The kernel binding of the local `name`.
    fn binding(&self, name: &MirLocalId) -> Result<BindingName, String> {
        self.bindings
            .get(name)
            .cloned()
            .or_else(|| name.source_name().map(BindingName::from))
            .ok_or_else(|| {
                "unsupported Rust construct: compiler local has no storage binding".into()
            })
    }

    fn result_step(&self) -> u32 {
        let id = self.next_result_step.get();
        self.next_result_step.set(
            id.checked_add(1)
                .expect("too many result steps in one function"),
        );
        crate::instrumentation::record_deterministic_work(1);
        id
    }

    fn call_value(
        &self,
        function: impl Into<String>,
        arguments: Vec<ProgramExpression>,
    ) -> (ProgramStatement, ProgramExpression) {
        crate::kernel::program_call_value(self.result_step(), function, arguments)
    }

    fn call_then_assign(
        &self,
        target: &MirLocalId,
        function: impl Into<String>,
        arguments: Vec<ProgramExpression>,
    ) -> Result<ProgramStatement, String> {
        let (call, value) = self.call_value(function, arguments);
        Ok(program_seq(
            call,
            program_assign(self.binding(target)?, value),
        ))
    }

    fn load_with_source(
        &mut self,
        pointer: ProgramExpression,
        value_type: ProgramType,
        reference_access: Option<ReferenceAccessSourceId>,
    ) -> Result<ProgramExpression, String> {
        let occurrence = self.next_load;
        self.next_load = self
            .next_load
            .checked_add(1)
            .ok_or("Rust load identity exhausted")?;
        Ok(crate::kernel::program_expression::typed_load_with_source(
            pointer,
            value_type,
            Some(LoadSourceId {
                owner: LoadSourceOwnerId {
                    source_unit: self.source.into(),
                    function: self.function.into(),
                },
                occurrence,
                reference_access: reference_access.map(std::sync::Arc::new),
            }),
        ))
    }

    fn reference_source(
        &self,
        expr: &E,
        kind: ReferenceAccessKind,
    ) -> Option<ReferenceAccessSourceId> {
        let point = self.mir_point?;
        let import_identity = self.import_identity.clone()?;
        let E::Deref { reference, .. } = expr else {
            return None;
        };
        let E::Local { name } = reference.as_ref() else {
            return None;
        };
        let node = *self.mir_nodes.get(&(expr as *const E as usize))?;
        Some(ReferenceAccessSourceId {
            import_identity,
            function: self.function.into(),
            block: point.block,
            statement: point.statement,
            node,
            reference_local: name.source_name()?.into(),
            kind,
        })
    }
    fn source_store(
        &self,
        target: &E,
        pointer: ProgramExpression,
        value: ProgramExpression,
        value_type: ProgramType,
    ) -> ProgramStatement {
        let mut statement = program_typed_store(pointer, value, value_type);
        if let ProgramStatement::TypedStore { source, .. } = &mut statement
            && let Some(id) = self.reference_source(target, ReferenceAccessKind::Write)
        {
            *source = StatementStoreSource::new(id);
        }
        statement
    }
    /// Declares the slice local `place`, one wide value of type
    /// `slice_type`.
    pub(super) fn declare_slice(
        &self,
        place: &MirLocalId,
        slice_type: ProgramType,
        constant: bool,
    ) -> Result<ProgramStatement, String> {
        Ok(program_declare_with_all_qualifiers(
            self.binding(place)?,
            slice_type,
            false,
            false,
            false,
            constant,
        ))
    }

    fn body(&mut self, body: &[S]) -> Result<ProgramStatement, String> {
        let mut result = program_skip();
        for s in body {
            result = program_seq(result, self.statement(s)?);
        }
        Ok(result)
    }
    fn statement(&mut self, s: &S) -> Result<ProgramStatement, String> {
        match s {
            S::SliceSplit {
                slice,
                midpoint,
                left,
                right,
            } => self.slice_split(slice, midpoint, left, right),
            S::Declare { place, initializer } => {
                if let Type::Reference { mutable, .. } = &place.value_type {
                    self.references.insert(place.name.clone(), !mutable);
                }
                if !self.locals.insert(place.name.clone()) {
                    return Err("duplicate Rust local identity".into());
                }
                if let Type::Array { element, length } = &place.value_type {
                    return self.declare_array(&place.name, element, *length, initializer);
                }
                if let Type::ByteSlice { mutable } = &place.value_type {
                    let (pointer, length) = self.slice_parts(initializer)?;
                    self.slices.insert(place.name.clone(), !mutable);
                    return Ok(program_seq(
                        self.declare_slice(&place.name, BYTE_SLICE, !mutable)?,
                        program_assign(
                            self.binding(&place.name)?,
                            slice_value(pointer, ProgramType::UInt8Pointer, length, !mutable),
                        ),
                    ));
                }
                if let Type::Reference { mutable, pointee } = &place.value_type
                    && let Type::Array { element, length } = pointee.as_ref()
                {
                    let (pointer, source_length, source_element) =
                        self.indexed_parts(initializer)?;
                    if source_length != crate::kernel::program_expression::uint64_literal(*length)
                        || source_element != scalar_type(element)?.to_kernel_type()
                    {
                        return Err("fixed array local disagrees with initializer".into());
                    }
                    let t = scalar_type(&place.value_type)?.to_kernel_type();
                    self.arrays
                        .insert(place.name.clone(), (*length, source_element, !mutable));
                    return Ok(program_seq(
                        program_declare_with_all_qualifiers(
                            self.binding(&place.name)?,
                            t,
                            false,
                            false,
                            false,
                            !mutable,
                        ),
                        program_assign(
                            self.binding(&place.name)?,
                            reference_view(pointer, t, false, !mutable),
                        ),
                    ));
                }
                let t = scalar_type(&place.value_type)?;
                if t == InterfaceType::Void {
                    return Err("unit locals outside Rust slice".into());
                }
                let constant = matches!(place.value_type, Type::Reference { mutable: false, .. });
                let declaration = program_declare_with_all_qualifiers(
                    self.binding(&place.name)?,
                    t.to_kernel_type(),
                    false,
                    false,
                    false,
                    constant,
                );
                let assign = self.assign(&place.name, initializer)?;
                Ok(program_seq(declaration, assign))
            }
            S::Assign {
                target: E::Local { name },
                value,
            } => self.assign(name, value),
            S::Assign { target, value } => {
                if let E::Deref {
                    value_type: Type::Array { element, length },
                    ..
                } = target
                {
                    let (checks, pointer) = self.prepared_address(target)?;
                    return Ok(program_seq(
                        checks,
                        self.assign_array(
                            pointer,
                            scalar_type(element)?.to_kernel_type(),
                            *length,
                            value,
                        )?,
                    ));
                }
                let (mut checks, mut value) = self.prepared_expr(value)?;
                if matches!(target, E::Index { .. }) {
                    // Rust evaluates the RHS before the destination index,
                    // which may call a function that changes the RHS storage.
                    let value_type = indexed_element_type(self.place_type(target)?)
                        .ok_or("unsupported Rust indexed assignment type")?;
                    let (capture, result) = self.capture_operand(value, &value_type)?;
                    checks = program_seq(checks, capture);
                    value = result;
                }
                let (target_checks, address) = self.prepared_address(target)?;
                Ok(program_seq(
                    program_seq(checks, target_checks),
                    program_typed_store(address, value, self.place_type(target)?),
                ))
            }
            S::While { condition, body } => {
                fn simple_guard(expression: &E) -> bool {
                    match expression {
                        E::Integer { .. }
                        | E::UnsignedInteger { .. }
                        | E::SignedInteger { .. }
                        | E::UsizeInteger { .. }
                        | E::Boolean { .. }
                        | E::Local { .. }
                        | E::SliceLength { .. } => true,
                        E::Not { value } | E::Cast { value, .. } | E::IntegerFrom { value, .. } => {
                            simple_guard(value)
                        }
                        E::Binary {
                            operator,
                            left,
                            right,
                            ..
                        } => {
                            matches!(
                                operator.as_str(),
                                "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and" | "or"
                            ) && simple_guard(left)
                                && simple_guard(right)
                        }
                        _ => false,
                    }
                }
                if !simple_guard(condition) {
                    return Err("Rust while conditions currently require scalar comparisons without calls, indexing or arithmetic".into());
                }
                Ok(program_while(
                    branch_condition(self.expr(condition)?),
                    Vec::new(),
                    self.body(body)?,
                ))
            }
            S::If {
                condition,
                then_body,
                else_body,
            } => {
                let (checks, condition) = self.prepared_expr(condition)?;
                Ok(program_seq(
                    checks,
                    program_if(
                        branch_condition(condition),
                        self.body(then_body)?,
                        self.body(else_body)?,
                    ),
                ))
            }
            S::Return {
                value:
                    Some(E::Call {
                        function,
                        arguments,
                    }),
            } => {
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                let (call, value) = self.call_value(function, arguments);
                Ok(program_seq(
                    checks,
                    program_seq(call, program_return(value)),
                ))
            }
            S::Return { value: Some(value) } => {
                let (checks, value) = self.prepared_expr(value)?;
                Ok(program_seq(checks, program_return(value)))
            }
            S::Return { value: None } if self.return_type == InterfaceType::Void => {
                Ok(program_return(program_void_value()))
            }
            S::Return { value: None } => Err("missing Rust return value".into()),
            S::Call {
                function,
                arguments,
            } => {
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(program_seq(checks, program_call(function, arguments)))
            }
        }
    }
    fn slice_split(
        &mut self,
        slice: &E,
        midpoint: &E,
        left: &super::schema::Place,
        right: &super::schema::Place,
    ) -> Result<ProgramStatement, String> {
        self.slice_split_slots(slice, midpoint, left, right, true)
    }
    fn slice_split_slots(
        &mut self,
        slice: &E,
        midpoint: &E,
        left: &super::schema::Place,
        right: &super::schema::Place,
        declare: bool,
    ) -> Result<ProgramStatement, String> {
        if left.name == right.name {
            return Err("split_at results require distinct slice slots".into());
        }
        let shared_reborrow = matches!(slice, E::Borrow { .. })
            && shared_slice_local(slice).is_some_and(|name| self.slices.contains_key(name));
        if !self.shared_byte_slice(slice) && !shared_reborrow {
            return Err("split_at requires a shared byte-slice local".into());
        }
        let (pointer, length) = self.slice_parts(slice)?;
        // Evaluate the receiver before the argument and capture both metadata
        // components. The midpoint may call code; it is evaluated only once.
        let (pointer_capture, saved_pointer) = self.capture_operand(
            pointer,
            &Type::Reference {
                mutable: false,
                pointee: Box::new(Type::U8),
            },
        )?;
        let (length_capture, saved_length) = self.capture_operand(length, &Type::Usize)?;
        let (midpoint_prefix, midpoint_value) = self.prepared_expr(midpoint)?;
        let (midpoint_capture, saved_midpoint) =
            self.capture_operand(midpoint_value, &Type::Usize)?;
        let mut result = program_seq(
            pointer_capture,
            program_seq(
                length_capture,
                program_seq(midpoint_prefix, midpoint_capture),
            ),
        );
        result = program_seq(
            result,
            program_labeled_assert(
                crate::kernel::program_expression::less_equal(
                    observe_operand(saved_midpoint.clone()),
                    observe_operand(saved_length.clone()),
                ),
                "Rust split_at panic check",
            ),
        );
        for (place, pointer, length) in [
            (
                left,
                observe_operand(saved_pointer.clone()),
                observe_operand(saved_midpoint.clone()),
            ),
            (
                right,
                // The right half starts at the midpoint in its own type, as
                // the contract's `bytes[mid]` does.
                crate::kernel::program_expression::add(
                    saved_pointer,
                    observe_operand(saved_midpoint.clone()),
                ),
                crate::kernel::program_expression::subtract(saved_length, saved_midpoint),
            ),
        ] {
            if place.value_type != (Type::ByteSlice { mutable: false }) {
                return Err("split_at results must be shared byte slices".into());
            }
            if declare {
                if !self.locals.insert(place.name.clone()) {
                    return Err("duplicate split_at local identity".into());
                }
                self.slices.insert(place.name.clone(), true);
                result = program_seq(result, self.declare_slice(&place.name, BYTE_SLICE, true)?);
            } else if self.slices.get(&place.name) != Some(&true) {
                return Err("split_at requires declared shared slice results".into());
            }
            result = program_seq(
                result,
                program_assign(
                    self.binding(&place.name)?,
                    slice_value(pointer, ProgramType::UInt8Pointer, length, true),
                ),
            );
        }
        Ok(result)
    }
    fn assign(&mut self, name: &MirLocalId, e: &E) -> Result<ProgramStatement, String> {
        if !self.locals.contains(name) {
            return Err(format!("unknown Rust local `{name}`"));
        }
        if let Some(&value_type) = self.memory_values.get(name) {
            let (prefix, value) = self.prepared_expr(e)?;
            let address = self.address(&E::Local { name: name.clone() })?;
            return Ok(program_seq(
                prefix,
                program_typed_store(address, value, value_type),
            ));
        }
        // A slice a call returns is one wide value, assigned as it is, and
        // so is its reborrow; a body reads a returned `&str` as its bytes.
        let e = match e {
            E::Borrow { place, value_type }
                if matches!(place.as_ref(), E::CallResult { .. })
                    && slice_program_type(value_type)?.is_some() =>
            {
                place.as_ref()
            }
            e => e,
        };
        if let E::CallResult { function, .. } = e
            && (self.slices.contains_key(name) || self.shared_scalar_slices.contains_key(name))
        {
            let value = self.expr(e)?;
            let string = matches!(function, MirCallee::Direct(callee)
                if self.functions.get(callee.as_str()).map(|f| &f.return_type)
                    == Some(&Type::StrSlice));
            return Ok(program_assign(
                self.binding(name)?,
                if string {
                    crate::kernel::program_expression::cast(value, BYTE_SLICE)
                } else {
                    value
                },
            ));
        }
        if let Some(expected) = self.shared_scalar_slices.get(name).copied() {
            let (pointer, source_length, element) = self.indexed_parts(e)?;
            if element != expected {
                return Err("shared scalar slice assignment element mismatch".into());
            }
            return Ok(program_assign(
                self.binding(name)?,
                ProgramExpression::SliceFromRawParts {
                    data: Box::new(pointer),
                    count: Box::new(source_length),
                },
            ));
        }
        if self.local_arrays.contains(name) {
            let (length, element, _) = self.arrays[name];
            return self.assign_array(self.array_pointer(name)?, element, length, e);
        }
        if let Some(constant) = self.slices.get(name).copied() {
            let checks = self.chunk_slice_checks(e)?;
            let (pointer, length) = self.slice_parts(e)?;
            return Ok(program_seq(
                checks,
                program_assign(
                    self.binding(name)?,
                    slice_value(pointer, ProgramType::UInt8Pointer, length, constant),
                ),
            ));
        }
        if let Some((length, element, constant)) = self.arrays.get(name).copied() {
            let (pointer, source_length, source_element) = self.indexed_parts(e)?;
            if source_length != crate::kernel::program_expression::uint64_literal(length)
                || source_element != element
            {
                return Err("fixed array assignment disagrees with destination".into());
            }
            let pointer_type = match element {
                ProgramType::Int32 => ProgramType::Int32Pointer,
                ProgramType::UInt8 => ProgramType::UInt8Pointer,
                ProgramType::UInt32 => ProgramType::UInt32Pointer,
                _ => return Err("unsupported fixed array element".into()),
            };
            return Ok(program_assign(
                self.binding(name)?,
                reference_view(pointer, pointer_type, false, constant),
            ));
        }
        match e {
            E::Call {
                function,
                arguments,
            } => {
                let (checks, arguments) = self.prepared_arguments(function, arguments)?;
                Ok(program_seq(
                    checks,
                    self.call_then_assign(name, function, arguments)?,
                ))
            }
            _ => {
                let (checks, value) = self.prepared_expr(e)?;
                let mut assignment = program_assign(self.binding(name)?, value);
                if let (
                    Some(import_identity),
                    Some(point),
                    E::Borrow {
                        place,
                        value_type:
                            Type::Reference {
                                mutable: true,
                                pointee,
                            },
                    },
                ) = (&self.import_identity, self.mir_point, e)
                    && matches!(
                        pointee.as_ref(),
                        Type::I32 | Type::U8 | Type::U16 | Type::U32
                    )
                    && let E::Deref { reference, .. } = place.as_ref()
                    && let E::Local { name: parent } = reference.as_ref()
                    && let (Some(parent), Some(child)) = (parent.source_name(), name.source_name())
                    && let ProgramStatement::Assign { source, .. } = &mut assignment
                {
                    *source = StatementAssignSource::new(ReferenceBorrowSourceId {
                        import_identity: import_identity.clone(),
                        function: self.function.into(),
                        block: point.block,
                        statement: point.statement,
                        parent: parent.into(),
                        child: child.into(),
                    });
                }
                Ok(program_seq(checks, assignment))
            }
        }
    }
    fn prepared_arguments(
        &mut self,
        function: &str,
        args: &[E],
    ) -> Result<(ProgramStatement, Vec<ProgramExpression>), String> {
        let types = self
            .functions
            .get(function)
            .ok_or("missing Rust call definition")?
            .parameters
            .iter()
            .map(|p| p.value_type.clone())
            .collect::<Vec<_>>();
        self.typed_arguments(types, args)
    }

    /// Arguments checked against the parameter types they are passed for.
    fn typed_arguments(
        &mut self,
        types: Vec<Type>,
        args: &[E],
    ) -> Result<(ProgramStatement, Vec<ProgramExpression>), String> {
        if types.len() != args.len() {
            return Err("Rust call argument count disagrees with callee".into());
        }
        // Each argument's own work, and the values it passes, or the scalar
        // value it still has to pass once every argument's work is known.
        let mut pieces: Vec<(
            ProgramStatement,
            Vec<ProgramExpression>,
            Option<(ProgramExpression, Type)>,
        )> = Vec::new();
        for (argument, value_type) in args.iter().zip(types) {
            let mut checks = program_skip();
            let mut values = Vec::new();
            if matches!(value_type, Type::Record { .. }) {
                let value = match argument {
                    E::Local { name } if self.owned_locals.contains(name) => {
                        crate::kernel::program_expression::variable(self.binding(name)?)
                    }
                    E::CallResult { keeps: false, .. } => self.expr(argument)?,
                    _ => return Err("owned call operand has no supported value".into()),
                };
                values.push(value);
                pieces.push((checks, values, None));
                continue;
            }
            // A slice argument is one wide value, built from the data
            // pointer and count the argument reads, each captured where its
            // own work ends (`design/rust-slice-values.md`, step 3b).
            if let E::CallResult { .. } = argument
                && slice_program_type(&value_type)?.is_some()
            {
                let (checks, value) = self.slice_operand(argument, &value_type)?;
                pieces.push((checks, vec![value], None));
                continue;
            }
            if let Type::ByteSlice { .. } | Type::StrSlice = value_type {
                let mutable = value_type == (Type::ByteSlice { mutable: true });
                let (pointer, length) = self.slice_parts(argument)?;
                let (capture_pointer, pointer) = self.capture_operand(
                    pointer,
                    &Type::Reference {
                        mutable,
                        pointee: Box::new(Type::U8),
                    },
                )?;
                let (capture_length, length) = self.capture_operand(length, &Type::Usize)?;
                checks = program_seq(checks, program_seq(capture_pointer, capture_length));
                let slice = ProgramExpression::SliceFromRawParts {
                    data: Box::new(pointer),
                    count: Box::new(length),
                };
                // A string slice is its bytes at the type `str`.
                values.push(if value_type == Type::StrSlice {
                    crate::kernel::program_expression::cast(
                        slice,
                        ProgramType::SlicePointer(crate::kernel::SliceElement::Str),
                    )
                } else {
                    slice
                });
                pieces.push((checks, values, None));
                continue;
            }
            if let Type::ScalarSlice { element, mutable } = &value_type {
                let (pointer, length, actual) = self.indexed_parts(argument)?;
                if actual != scalar_type(element)?.to_kernel_type() {
                    return Err("Rust scalar slice call element mismatch".into());
                }
                let (capture_pointer, pointer) = self.capture_operand(
                    pointer,
                    &Type::Reference {
                        mutable: *mutable,
                        pointee: element.clone(),
                    },
                )?;
                let (capture_length, length) = self.capture_operand(length, &Type::Usize)?;
                checks = program_seq(checks, program_seq(capture_pointer, capture_length));
                values.push(ProgramExpression::SliceFromRawParts {
                    data: Box::new(pointer),
                    count: Box::new(length),
                });
                pieces.push((checks, values, None));
                continue;
            }
            let (prefix, value) = self.prepared_expr(argument)?;
            pieces.push((prefix, values, Some((value, value_type))));
        }
        // The call reads its arguments after all of their work, so a local or
        // a literal is passed as itself only when no later work could change
        // it; any other value is captured where its own work ends.
        let mut stable_after = vec![true; pieces.len() + 1];
        for index in (0..pieces.len()).rev() {
            stable_after[index] = stable_after[index + 1] && no_effect(&pieces[index].0);
        }
        let mut checks = program_skip();
        let mut values = Vec::new();
        for (index, (prefix, passed, scalar)) in pieces.into_iter().enumerate() {
            let stable = stable_after[index];
            checks = program_seq(checks, prefix);
            values.extend(passed);
            if let Some((value, value_type)) = scalar {
                let reference = matches!(value_type, Type::Reference { .. });
                let (capture, value) =
                    if !reference && matches!(value, ProgramExpression::StepResult { .. }) {
                        (program_skip(), value)
                    } else if stable && !reference && direct_operand(&value) {
                        let interface_type = scalar_type(&value_type)?.to_kernel_type();
                        (
                            program_skip(),
                            crate::kernel::program_expression::cast(value, interface_type),
                        )
                    } else if stable && reference && borrowed_local(&value) {
                        // A borrow of a local, or a reference a local holds, is
                        // read once, by the call, so its view is formed there.
                        let interface_type = scalar_type(&value_type)?.to_kernel_type();
                        let constant = matches!(value_type, Type::Reference { mutable: false, .. });
                        (
                            program_skip(),
                            reference_view(value, interface_type, false, constant),
                        )
                    } else {
                        self.capture_operand(value, &value_type)?
                    };
                checks = program_seq(checks, capture);
                values.push(value);
            }
        }
        Ok((checks, values))
    }

    /// Stage an operand if a later expression could change it or reading it
    /// involves work. A guard observes the result and its final use ends it.
    fn read_operand(
        &self,
        value: ProgramExpression,
        value_type: &Type,
        stable: bool,
    ) -> Result<(ProgramStatement, ProgramExpression, ProgramExpression), String> {
        if !matches!(value_type, Type::Reference { .. })
            && matches!(value, ProgramExpression::StepResult { .. })
        {
            return Ok((program_skip(), observe_operand(value.clone()), value));
        }
        if stable && !matches!(value_type, Type::Reference { .. }) && direct_operand(&value) {
            let interface_type = scalar_type(value_type)?.to_kernel_type();
            let guard = crate::kernel::program_expression::cast(value.clone(), interface_type);
            return Ok((program_skip(), guard, value));
        }
        let (capture, result) = self.capture_operand(value, value_type)?;
        Ok((capture, observe_operand(result.clone()), result))
    }

    fn capture_operand(
        &self,
        value: ProgramExpression,
        value_type: &Type,
    ) -> Result<(ProgramStatement, ProgramExpression), String> {
        let step = self.result_step();
        let interface_type = scalar_type(value_type)?.to_kernel_type();
        let constant = matches!(value_type, Type::Reference { mutable: false, .. });
        if let Type::Reference { pointee, .. } = value_type
            && let Type::Record { name } = pointee.as_ref()
            && let Some(layout) = self.layouts.get(name)
        {
            self.step_pointee_layouts
                .borrow_mut()
                .insert(step, layout.to_kernel_aggregate_layout());
        }
        let expression = if matches!(value_type, Type::Reference { .. }) {
            reference_view(value, interface_type, false, constant)
        } else {
            crate::kernel::program_expression::cast(value, interface_type)
        };
        Ok((
            typed_value_step(vec![step], expression, interface_type, constant),
            ProgramExpression::StepResult {
                step,
                origin: crate::kernel::StepOrigin::Value("Rust operand"),
                ends: true,
            },
        ))
    }

    fn prepared_closure(
        &mut self,
        function: &str,
        site: &crate::kernel::ClosureSite,
        captures: &[E],
        value_type: &Type,
    ) -> Result<(ProgramStatement, ProgramExpression), String> {
        let closure = self
            .functions
            .get(function)
            .ok_or("Rust closure instance of an unknown closure")?;
        let Type::FnPointer { parameters, result } = value_type else {
            return Err("Rust closure instance requires a callable type".into());
        };
        if closure.captures != captures.len()
            || closure.return_type != **result
            || closure.parameters.len() != closure.captures + parameters.len()
            || closure.parameters[closure.captures..]
                .iter()
                .zip(parameters)
                .any(|(parameter, expected)| parameter.value_type != *expected)
        {
            return Err(format!(
                "Rust closure instance of `{function}` does not have the closure's type"
            ));
        }
        let mut checks = program_skip();
        let mut values = Vec::new();
        for capture in captures {
            let (capture_checks, value) = self.prepared_expr(capture)?;
            checks = program_seq(checks, capture_checks);
            values.push(value);
        }
        let (call, result) = crate::kernel::program_create_closure(
            self.result_step(),
            function.to_owned(),
            values,
            Some(site.clone()),
        );
        Ok((program_seq(checks, call), result))
    }

    // Read operands once, in source order. Generated asserts are checked
    // execution obligations. The operator uses the same retained operands.
    fn prepared_expr(&mut self, e: &E) -> Result<(ProgramStatement, ProgramExpression), String> {
        match e {
            E::EnumerateOptionIndex { option } => self.enumerate_option_index(option),
            E::SharedArrayOptionElement { option } => {
                use crate::kernel::program_expression::{equal, int32_literal, variable};
                let option = self.shared_array_option(option)?;
                Ok((
                    program_assert(equal(variable(&option.tag), int32_literal(1))),
                    variable(&option.pointer),
                ))
            }
            E::ClosureInstance {
                function,
                site,
                captures,
                value_type,
            } => self.prepared_closure(function, site, captures, value_type),
            E::Call {
                function,
                arguments,
            } => {
                let return_type = self
                    .functions
                    .get(function.as_str())
                    .ok_or("missing Rust call definition")?
                    .return_type
                    .clone();
                let (prefix, arguments) = self.prepared_arguments(function, arguments)?;
                let (mut call, result) = self.call_value(function, arguments);
                let value_type = value_program_type(&return_type)?;
                let ProgramStatement::CallResult {
                    result_type,
                    result_pointee_constant,
                    ..
                } = &mut call
                else {
                    unreachable!("a value-producing call");
                };
                *result_type = Some(value_type);
                *result_pointee_constant =
                    matches!(return_type, Type::Reference { mutable: false, .. });
                Ok((program_seq(prefix, call), result))
            }
            E::Index { .. } => {
                let (checks, pointer) = self.prepared_address(e)?;
                let occurrence = self.next_load;
                self.next_load = self
                    .next_load
                    .checked_add(1)
                    .ok_or("Rust load identity exhausted")?;
                Ok((
                    checks,
                    crate::kernel::program_expression::typed_load_with_source(
                        pointer,
                        self.place_type(e)?,
                        Some(LoadSourceId {
                            owner: LoadSourceOwnerId {
                                source_unit: self.source.into(),
                                function: self.function.into(),
                            },
                            occurrence,
                            reference_access: None,
                        }),
                    ),
                ))
            }
            E::Borrow { place, value_type } if matches!(place.as_ref(), E::Index { .. }) => {
                let (checks, pointer) = self.prepared_address(place)?;
                Ok((
                    checks,
                    reference_view(
                        pointer,
                        scalar_type(value_type)?.to_kernel_type(),
                        false,
                        false,
                    ),
                ))
            }
            E::Binary {
                operator,
                left_type,
                right_type,
                left,
                right,
            } => {
                let (left_prefix, left_value) = self.prepared_expr(left)?;
                if operator == "and" || operator == "or" {
                    if *left_type != Type::Bool || *right_type != Type::Bool {
                        return Err("Rust logical operators require bool operands".into());
                    }
                    let step = self.result_step();
                    let (right_prefix, right_value) = self.prepared_expr(right)?;
                    let right = program_seq(
                        right_prefix,
                        typed_value_step(vec![step], right_value, ProgramType::Bool, false),
                    );
                    let skipped_value = ProgramExpression::Value(crate::kernel::bool_value(
                        u32::from(operator == "or"),
                    ));
                    let skipped =
                        typed_value_step(vec![step], skipped_value, ProgramType::Bool, false);
                    let (kind, yes, no) = if operator == "and" {
                        (OperatorKind::And, right, skipped)
                    } else {
                        (OperatorKind::Or, skipped, right)
                    };
                    return Ok((
                        program_seq(
                            left_prefix,
                            program_if(branch_condition(left_value), yes, no),
                        ),
                        ProgramExpression::StepResult {
                            step,
                            origin: StepOrigin::Operator(kind),
                            ends: true,
                        },
                    ));
                }
                let (right_prefix, right_value) = self.prepared_expr(right)?;
                // The left operand is read before the right one's own work,
                // so it is used where it is read only when that work has no
                // effect that could change it.
                let (left_capture, left_operand, left_read) = self.read_operand(
                    left_value,
                    left_type,
                    no_effect(&left_prefix) && no_effect(&right_prefix),
                )?;
                let (right_capture, right_operand, right_read) =
                    self.read_operand(right_value, right_type, no_effect(&right_prefix))?;
                let prefix = program_seq(
                    program_seq(left_prefix, left_capture),
                    program_seq(right_prefix, right_capture),
                );
                // Append checks to the existing sequence so a check-free
                // expression does not acquire a new execution region.
                let prefix = binary_checks(
                    prefix,
                    operator,
                    left_type,
                    right_type,
                    &left_operand,
                    &right_operand,
                )?;
                Ok((
                    prefix,
                    binary_value(operator, left_type, right_type, left_read, right_read)?,
                ))
            }
            E::Not { value }
            | E::BitwiseNot { value, .. }
            | E::Cast { value, .. }
            | E::IntegerFrom { value, .. } => {
                let (prefix, value) = self.prepared_expr(value)?;
                let value = match e {
                    E::Not { .. } => crate::kernel::program_expression::bool_value(
                        crate::kernel::program_expression::not(value),
                    ),
                    E::BitwiseNot { value_type, .. } => {
                        rust_bitwise_not(value, scalar_type(value_type)?.to_kernel_type())
                    }
                    E::Cast { value_type, .. } => {
                        rust_scalar_cast(value, scalar_type(value_type)?.to_kernel_type())
                    }
                    E::IntegerFrom {
                        source_type,
                        value_type,
                        ..
                    } => integer_from(value, source_type, value_type)?,
                    _ => unreachable!(),
                };
                Ok((prefix, value))
            }
            _ => Ok((program_skip(), self.expr(e)?)),
        }
    }
    /// Whether `slice` is a shared byte slice whose parts never change while
    /// it is read: a shared slice local, a shared borrow of one, or a shared
    /// slice of an array.
    pub(super) fn shared_byte_slice(&self, slice: &E) -> bool {
        match slice {
            E::ArrayToSlice { mutable: false, .. } => true,
            slice => shared_slice_local(slice)
                .is_some_and(|name| self.slices.get(name).is_some_and(|constant| *constant)),
        }
    }

    fn slice_parts(&mut self, e: &E) -> Result<(ProgramExpression, ProgramExpression), String> {
        if let E::ChunkOptionSlice { option } = e {
            use crate::kernel::program_expression::variable;
            let fields = self.chunk_option(option)?;
            return Ok((variable(&fields.pointer), variable(&fields.length)));
        }
        if let E::Borrow {
            place,
            value_type: Type::ByteSlice { mutable },
        } = e
        {
            let E::Local { name } = place.as_ref() else {
                return Err("slice reborrow requires a slice local".into());
            };
            if *mutable && self.slices.get(name).is_none_or(|constant| *constant) {
                return Err("mutable slice reborrow requires a mutable source".into());
            }
            return self.slice_parts(place);
        }
        if let E::ChunkRemainder { iterator } = e {
            use crate::kernel::program_expression::variable;
            let fields = self.chunk_iterator(iterator)?;
            return Ok((
                variable(fields.remainder.clone()),
                variable(fields.remainder_length.clone()),
            ));
        }
        if let E::ArrayToSlice { array, mutable } = e {
            let (pointer, length, element) = self.indexed_parts(array)?;
            if element != ProgramType::UInt8 {
                return Err("array coercion requires u8 elements".into());
            }
            let constant = self.array_source_is_constant(array)?;
            if *mutable && constant {
                return Err("mutable array coercion requires a mutable source".into());
            }
            return Ok((pointer, length));
        }
        let E::Local { name } = e else {
            return Err("slice values must be local slice references".into());
        };
        if !self.slices.contains_key(name) {
            return Err("unknown Rust slice reference".into());
        }
        Ok(slice_components(
            crate::kernel::program_expression::variable(self.binding(name)?),
        ))
    }
    /// The one wide value the slice expression `e` gives at the slice type
    /// `value_type`, with the checks reading it owes: a call's slice result
    /// as the call returned it, any other slice built from the data pointer
    /// and count it reads (`design/rust-slice-values.md`, step 3c). A body
    /// reads a `&str` as its bytes, so a string slice is cast to `str`.
    pub(super) fn slice_operand(
        &mut self,
        e: &E,
        value_type: &Type,
    ) -> Result<(ProgramStatement, ProgramExpression), String> {
        let slice_type =
            slice_program_type(value_type)?.ok_or("a slice operand has a slice type")?;
        let (checks, value) = match (e, value_type) {
            (E::CallResult { .. }, _) => (program_skip(), self.expr(e)?),
            (_, Type::ScalarSlice { element, .. }) => {
                let (pointer, length, actual) = self.indexed_parts(e)?;
                if actual != scalar_type(element)?.to_kernel_type() {
                    return Err("Rust scalar slice element mismatch".into());
                }
                (
                    program_skip(),
                    ProgramExpression::SliceFromRawParts {
                        data: Box::new(pointer),
                        count: Box::new(length),
                    },
                )
            }
            _ => {
                let checks = self.chunk_slice_checks(e)?;
                let constant = value_type != &(Type::ByteSlice { mutable: true });
                let (pointer, length) = self.slice_parts(e)?;
                (
                    checks,
                    slice_value(pointer, ProgramType::UInt8Pointer, length, constant),
                )
            }
        };
        Ok((
            checks,
            if *value_type == Type::StrSlice {
                crate::kernel::program_expression::cast(value, slice_type)
            } else {
                value
            },
        ))
    }
    fn array_source_is_constant(&self, e: &E) -> Result<bool, String> {
        match e {
            E::Local { name } => self
                .arrays
                .get(name)
                .map(|a| a.2)
                .ok_or("unknown array source".into()),
            E::Deref { reference, .. } => self.array_source_is_constant(reference),
            E::Field { base, .. } => match base.as_ref() {
                E::Local { name } if self.owned_locals.contains(name) => Ok(false),
                E::Deref { reference, .. } => match reference.as_ref() {
                    E::Local { name } => self
                        .references
                        .get(name)
                        .copied()
                        .ok_or("unknown record reference".into()),
                    _ => Err("array field requires a record reference local".into()),
                },
                _ => Err("array field requires a borrowed record".into()),
            },
            E::Borrow {
                value_type: Type::Reference { mutable, .. },
                ..
            } => Ok(!mutable),
            _ => Err("array coercion requires a fixed array place".into()),
        }
    }
    fn indexed_parts(
        &mut self,
        e: &E,
    ) -> Result<(ProgramExpression, ProgramExpression, ProgramType), String> {
        match e {
            E::Borrow { place, value_type } => {
                if matches!(value_type, Type::Reference { mutable: true, .. })
                    && self.array_source_is_constant(place)?
                {
                    return Err(
                        "mutable array field borrow requires a mutable record reference".into(),
                    );
                }
                self.indexed_parts(place)
            }
            E::Deref { reference, .. } => self.indexed_parts(reference),
            E::Local { name } if self.shared_scalar_slices.contains_key(name) => {
                let element = self.shared_scalar_slices[name];
                let (pointer, length) = slice_components(
                    crate::kernel::program_expression::variable(self.binding(name)?),
                );
                Ok((pointer, length, element))
            }
            E::ArrayToSlice {
                array,
                mutable: false,
            } => self.indexed_parts(array),
            E::Local { name } if self.arrays.contains_key(name) => {
                let (length, element, _) = self.arrays[name];
                Ok((
                    self.array_pointer(name)?,
                    crate::kernel::program_expression::uint64_literal(length),
                    element,
                ))
            }
            E::Field { record, field, .. } => {
                let (_, ty) = *self
                    .fields
                    .get(&(record.as_str(), field.as_str()))
                    .ok_or("unknown Rust array field")?;
                let (element, length) =
                    array_field_parts(ty).ok_or("indexed Rust field is not a scalar array")?;
                let constant = self.array_source_is_constant(e)?;
                let pointer_type = match element {
                    ProgramType::Int32 => ProgramType::Int32Pointer,
                    ProgramType::UInt8 => ProgramType::UInt8Pointer,
                    ProgramType::UInt32 => ProgramType::UInt32Pointer,
                    _ => unreachable!(),
                };
                let pointer = self.address(e)?;
                Ok((
                    reference_view(pointer, pointer_type, false, constant),
                    crate::kernel::program_expression::uint64_literal(u64::from(length)),
                    element,
                ))
            }
            _ => {
                let (pointer, length) = self.slice_parts(e)?;
                Ok((pointer, length, ProgramType::UInt8))
            }
        }
    }
    fn array_pointer(&self, name: &MirLocalId) -> Result<ProgramExpression, String> {
        let (_, element, constant) = self.arrays.get(name).ok_or("unknown fixed array")?;
        let pointer_type = match element {
            ProgramType::UInt8 => ProgramType::UInt8Pointer,
            ProgramType::UInt32 => ProgramType::UInt32Pointer,
            ProgramType::Int32 => ProgramType::Int32Pointer,
            _ => return Err("unsupported fixed array element".into()),
        };
        Ok(reference_view(
            crate::kernel::program_expression::variable(self.binding(name)?),
            pointer_type,
            false,
            *constant,
        ))
    }
    fn prepared_address(&mut self, e: &E) -> Result<(ProgramStatement, ProgramExpression), String> {
        if let E::Index { slice, index } = e {
            let (pointer, length, _) = self.indexed_parts(slice)?;
            let (checks, value) = self.prepared_expr(index)?;
            let (capture, index) = self.capture_operand(value, &Type::Usize)?;
            // The index keeps its own type, as the contract's place does.
            let offset = index.clone();
            return Ok((
                program_seq(
                    checks,
                    program_seq(
                        capture,
                        program_labeled_assert(
                            crate::kernel::program_expression::less_than(
                                observe_operand(index.clone()),
                                length,
                            ),
                            if matches!(slice.as_ref(), E::Local { name }
                                if self.slices.contains_key(name)
                                    || self.shared_scalar_slices.contains_key(name))
                            {
                                "Rust slice index panic check"
                            } else {
                                "Rust array index panic check"
                            },
                        ),
                    ),
                ),
                crate::kernel::program_expression::add(pointer, offset),
            ));
        }
        Ok((program_skip(), self.address(e)?))
    }
    /// The offset of `record`'s `field` in its layout: a number, or for a
    /// symbolic layout its `offsetof` term. The export's own `offset` is
    /// read only through the layout.
    pub(super) fn field_offset(
        &self,
        record: &str,
        field: &str,
    ) -> Result<crate::kernel::LayoutOffset, String> {
        self.fields
            .get(&(record, field))
            .map(|(offset, _)| *offset)
            .ok_or_else(|| "unknown Rust field".into())
    }
    fn address(&mut self, e: &E) -> Result<ProgramExpression, String> {
        match e {
            E::Local { name } if self.local_arrays.contains(name) => self.array_pointer(name),
            E::Deref { reference, .. } => self.expr(reference),
            E::Field {
                base,
                record,
                field,
            } => {
                let (offset, _) = *self
                    .fields
                    .get(&(record.as_str(), field.as_str()))
                    .ok_or("unknown Rust field")?;
                // Field bases are either record references or local stack objects.
                let pointer = match base.as_ref() {
                    E::Deref { reference, .. } => self.expr(reference)?,
                    _ => self.expr(base)?,
                };
                Ok(crate::kernel::program_expression::pointer_offset_bytes(
                    pointer, offset,
                ))
            }
            E::Local { name } if self.owned_locals.contains(name) => {
                Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(self.binding(name)?),
                    ProgramType::Int32Pointer,
                ))
            }
            E::Local { name } if self.addressable_locals.contains(name) => {
                Ok(ProgramExpression::AddressOf(Box::new(
                    crate::kernel::program_expression::variable(self.binding(name)?),
                )))
            }
            E::Local { name } if self.memory_values.contains_key(name) => {
                let ProgramType::Parameter(value_type) = self.memory_values[name] else {
                    return Err(
                        "a memory-backed Rust local holds an enum or type-parameter value".into(),
                    );
                };
                Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::variable(self.binding(name)?),
                    ProgramType::ParameterPointer(value_type),
                ))
            }
            _ => Err("only reference-backed Rust places can be borrowed or stored".into()),
        }
    }
    fn place_type(&mut self, e: &E) -> Result<ProgramType, String> {
        match e {
            E::Index { slice, .. } => Ok(self.indexed_parts(slice)?.2),
            E::Field { record, field, .. } => self
                .fields
                .get(&(record.as_str(), field.as_str()))
                .map(|(_, t)| *t)
                .ok_or("unknown Rust field type".into()),
            E::Deref { value_type, .. } => Ok(scalar_type(value_type)?.to_kernel_type()),
            _ => Err("unsupported Rust memory place type".into()),
        }
    }
    /// `e` as a branch's or loop's condition ([`branch_condition`]).
    fn condition(&mut self, e: &E) -> Result<ProgramExpression, String> {
        self.expr(e).map(branch_condition)
    }

    fn expr(&mut self, e: &E) -> Result<ProgramExpression, String> {
        match e {
            E::CallResult {
                call,
                function,
                keeps,
            } => Ok(ProgramExpression::StepResult {
                step: *call,
                origin: crate::kernel::StepOrigin::Call(
                    function
                        .source_name()
                        .ok_or("unsupported Rust construct: unnamed function pointer result")?
                        .to_owned(),
                ),
                ends: !*keeps,
            }),
            E::SharedArrayHasNext { iterator } => self.shared_array_has_next(iterator),
            E::RangeHasNext { iterator } => self.range_has_next(iterator),
            E::SharedArrayOptionTag { option } => Ok(crate::kernel::program_expression::variable(
                &self.shared_array_option(option)?.tag,
            )),
            E::SharedArrayOptionElement { .. } => {
                Err("shared Option payload requires checked preparation".into())
            }
            E::EnumerateOptionIndex { .. } => {
                Err("enumerated Option index requires checked preparation".into())
            }
            E::ChunkHasNext { iterator } => self.chunk_has_next(iterator),
            E::ChunkOptionTag { option } => Ok(crate::kernel::program_expression::variable(
                &self.chunk_option(option)?.tag,
            )),
            E::VariantIs { value, variant } => Ok(ProgramExpression::EnumIs {
                value: Box::new(self.expr(value)?),
                variant: variant.clone(),
            }),
            E::ChunkOptionSlice { .. } | E::ChunkRemainder { .. } | E::ArrayToSlice { .. } => {
                Err("Rust slices require pointer-plus-length preparation".into())
            }
            E::Array { .. } | E::Repeat { .. } => {
                Err("array values require whole-array assignment".into())
            }
            E::Integer { value } => Ok(crate::kernel::program_expression::int32_literal(
                *value as u32,
            )),
            E::UsizeInteger { value } => {
                Ok(crate::kernel::program_expression::uint64_literal(*value))
            }
            E::EnumConstruct {
                name,
                variant,
                fields,
            } => enum_construct(name, variant, fields.iter().map(|field| self.expr(field))),
            E::EnumField {
                base,
                variant,
                index,
                ..
            } => Ok(ProgramExpression::EnumField {
                value: Box::new(self.expr(base)?),
                variant: variant.clone(),
                index: *index,
            }),
            E::SliceLength { slice } => Ok(self.indexed_parts(slice)?.1),
            E::Index { .. } => Err("indexed Rust places require checked preparation".into()),
            E::UnsignedInteger { value, value_type } => match value_type {
                Type::U8 => Ok(crate::kernel::program_expression::uint8_literal(
                    u8::try_from(*value).map_err(|_| "Rust u8 literal out of range")?,
                )),
                Type::U16 => Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::int32_literal(
                        u16::try_from(*value).map_err(|_| "Rust u16 literal out of range")? as u32,
                    ),
                    ProgramType::UInt16,
                )),
                Type::U32 => Ok(crate::kernel::program_expression::uint32_literal(
                    u32::try_from(*value).map_err(|_| "Rust u32 literal out of range")?,
                )),
                Type::U64 | Type::Usize => {
                    Ok(crate::kernel::program_expression::uint64_literal(*value))
                }
                _ => Err("unsigned literal needs an unsigned Rust type".into()),
            },
            E::SignedInteger { value, value_type } => match value_type {
                Type::I8 => Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::int32_literal(
                        i8::try_from(*value).map_err(|_| "Rust i8 literal out of range")? as i32
                            as u32,
                    ),
                    ProgramType::Int8,
                )),
                Type::I16 => Ok(crate::kernel::program_expression::cast(
                    crate::kernel::program_expression::int32_literal(
                        i16::try_from(*value).map_err(|_| "Rust i16 literal out of range")? as i32
                            as u32,
                    ),
                    ProgramType::Int16,
                )),
                Type::I32 => Ok(crate::kernel::program_expression::int32_literal(
                    i32::try_from(*value).map_err(|_| "Rust i32 literal out of range")? as u32,
                )),
                Type::I64 | Type::Isize => {
                    Ok(crate::kernel::program_expression::int64_literal(*value))
                }
                _ => Err("signed literal needs a signed Rust type".into()),
            },
            E::Boolean { value } => Ok(crate::kernel::program_expression::int32_literal(
                u32::from(*value),
            )),
            E::NoneBox => Ok(crate::kernel::program_expression::cast(
                crate::kernel::program_expression::int32_literal(0),
                ProgramType::Int32Pointer,
            )),
            E::IntegerFrom {
                value,
                source_type,
                value_type,
            } => {
                let value = self.expr(value)?;
                integer_from(value, source_type, value_type)
            }
            E::Local { name } if self.scalar_operands.contains_key(name) => {
                let (step, last_use) = self.scalar_operands[name];
                Ok(ProgramExpression::StepResult {
                    step,
                    origin: crate::kernel::StepOrigin::Value("Rust operand"),
                    ends: self.mir_point == Some(last_use),
                })
            }
            E::Local { name } if self.memory_values.contains_key(name) => {
                let value_type = self.memory_values[name];
                Ok(crate::kernel::program_expression::typed_load(
                    self.address(e)?,
                    value_type,
                ))
            }
            E::Local { name } => {
                if !self.locals.contains(name) {
                    return Err(format!("unknown Rust local `{name}`"));
                }
                Ok(crate::kernel::program_expression::variable(
                    self.binding(name)?,
                ))
            }
            E::Not { value } => Ok(crate::kernel::program_expression::bool_value(
                crate::kernel::program_expression::not(self.expr(value)?),
            )),
            E::Borrow { place, value_type } => {
                if let E::Field { record, field, .. } = place.as_ref()
                    && self
                        .fields
                        .get(&(record.as_str(), field.as_str()))
                        .is_some_and(|(_, ty)| array_field_parts(*ty).is_some())
                    && matches!(value_type, Type::Reference { mutable: true, .. })
                    && self.array_source_is_constant(place)?
                {
                    return Err(
                        "mutable array field borrow requires a mutable record reference".into(),
                    );
                }
                Ok(reference_view(
                    self.address(place)?,
                    scalar_type(value_type)?.to_kernel_type(),
                    false,
                    false,
                ))
            }
            E::Cast { value, value_type } => Ok(rust_scalar_cast(
                self.expr(value)?,
                scalar_type(value_type)?.to_kernel_type(),
            )),
            E::BitwiseNot { value, value_type } => Ok(rust_bitwise_not(
                self.expr(value)?,
                scalar_type(value_type)?.to_kernel_type(),
            )),
            E::Deref { .. } | E::Field { .. } => {
                if array_field_parts(self.place_type(e)?).is_some() {
                    return Err("array fields must be borrowed or indexed; owned field copies are unsupported".into());
                }
                let pointer = self.address(e)?;
                let value_type = self.place_type(e)?;
                let access = self.reference_source(e, ReferenceAccessKind::Read);
                self.load_with_source(pointer, value_type, access)
            }
            E::Binary {
                operator,
                left_type,
                right_type,
                left,
                right,
            } => {
                let left = self.expr(left)?;
                let right = self.expr(right)?;
                binary_value(operator, left_type, right_type, left, right)
            }
            E::Call { .. } => Err("nested Rust calls outside statement lowering".into()),
            E::ClosureInstance { .. } => {
                Err("Rust closure instance requires prepared evaluation".into())
            }
            E::FunctionAddress {
                function,
                value_type,
            } => {
                let target = self
                    .functions
                    .get(function.as_str())
                    .ok_or("Rust function pointer to an unknown function")?;
                let Type::FnPointer { parameters, result } = value_type else {
                    return Err("Rust function address requires a function-pointer type".into());
                };
                if target.return_type != **result
                    || target.parameters.len() != parameters.len()
                    || target
                        .parameters
                        .iter()
                        .zip(parameters)
                        .any(|(parameter, expected)| parameter.value_type != *expected)
                {
                    return Err(format!(
                        "Rust function address `{function}` does not have its function's type"
                    ));
                }
                Ok(crate::kernel::program_expression::function_address(
                    function,
                ))
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/languages/rust/lowering/tests.rs");
}
