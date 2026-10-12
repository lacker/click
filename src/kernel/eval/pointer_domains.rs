//! Object-domain obligations for executable pointer operations.
//!
//! These queries grant neither ownership nor initialized bytes. An absent
//! legacy descriptor is reported separately from a checked domain; a present
//! descriptor cannot fall back to address-only permission or block bounds.

use super::*;
use num_traits::ToPrimitive;
use std::sync::Arc;

/// Exact observation of the admitted fixed-width native range counts. A
/// numeral's magnitude does not change the cost of observing its native
/// format; general mathematical/128-bit conversion keeps its existing work.
pub(in crate::kernel) fn native_count_observation(
    kind: MachineIntegerType,
    value: Bitvector32Term,
) -> Option<IntegerTerm> {
    if matches!(
        kind,
        MachineIntegerType::Int32
            | MachineIntegerType::UInt32
            | MachineIntegerType::Int64
            | MachineIntegerType::UInt64
    ) && let Some(constant) = kind.constant_from_term(&value)
    {
        return Some(IntegerTerm::Constant(constant.to_integer()));
    }
    IntegerTerm::from_machine(kind, value)
}

/// Prefixes may use the existing wide resource geometry. Their byte extent
/// must fit a signed native pointer displacement; declarations themselves
/// retain their separately checked, compact u32 layout sizes.
pub(in crate::kernel) fn native_prefix_element_limit(stride: u32) -> i64 {
    assert_ne!(stride, 0);
    i64::MAX / i64::from(stride)
}

// Concrete native positions and declaration extents fit a fixed-width
// integer. Use actual checked native operations for these selected operands;
// symbolic or larger mathematical integers retain arbitrary-precision work.
fn native_operands(left: &IntegerTerm, right: &IntegerTerm) -> Option<(i64, i64)> {
    crate::instrumentation::record_deterministic_work(2);
    Some((left.as_const()?.to_i64()?, right.as_const()?.to_i64()?))
}

fn domain_add(left: IntegerTerm, right: IntegerTerm) -> IntegerTerm {
    if let Some(value) =
        native_operands(&left, &right).and_then(|(left, right)| left.checked_add(right))
    {
        IntegerTerm::constant_i64(value)
    } else {
        IntegerTerm::add(left, right)
    }
}

fn domain_subtract(left: IntegerTerm, right: IntegerTerm) -> IntegerTerm {
    if let Some(value) =
        native_operands(&left, &right).and_then(|(left, right)| left.checked_sub(right))
    {
        IntegerTerm::constant_i64(value)
    } else if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
        IntegerTerm::constant(left - right)
    } else {
        IntegerTerm::subtract(left, right)
    }
}

fn domain_multiply(left: IntegerTerm, right: IntegerTerm) -> IntegerTerm {
    if let Some(value) =
        native_operands(&left, &right).and_then(|(left, right)| left.checked_mul(right))
    {
        IntegerTerm::constant_i64(value)
    } else {
        IntegerTerm::multiply(left, right)
    }
}

pub(in crate::kernel) fn domain_less_equal(left: IntegerTerm, right: IntegerTerm) -> ConditionTerm {
    if let Some((left, right)) = native_operands(&left, &right) {
        ConditionTerm::Constant(left <= right)
    } else {
        machine_observation_order(&left, &right, false)
            .or_else(|| machine_constant_order(&left, &right, false))
            .or_else(|| machine_offset_order(&left, &right, false))
            .unwrap_or_else(|| ConditionTerm::integer_less_equal(left, right))
    }
}

pub(in crate::kernel) fn domain_less_than(left: IntegerTerm, right: IntegerTerm) -> ConditionTerm {
    if let Some((left, right)) = native_operands(&left, &right) {
        ConditionTerm::Constant(left < right)
    } else {
        machine_observation_order(&left, &right, true)
            .or_else(|| machine_constant_order(&left, &right, true))
            .or_else(|| machine_offset_order(&left, &right, true))
            .unwrap_or_else(|| ConditionTerm::integer_less_than(left, right))
    }
}

// Two complete observations in the same native format have exactly the
// ordering of their mathematical values. Comparisons across formats retain
// the mathematical query.
fn machine_observation_order(
    left: &IntegerTerm,
    right: &IntegerTerm,
    strict: bool,
) -> Option<ConditionTerm> {
    let (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) = (left, right) else {
        return None;
    };
    if left.ty() != right.ty() {
        return None;
    }
    crate::instrumentation::record_deterministic_work(2);
    let (left_value, right_value) = (left.value().clone(), right.value().clone());
    Some(match (left.ty(), strict) {
        (MachineIntegerType::Int32, false) => {
            ConditionTerm::signed_less_equal(left_value, right_value)
        }
        (MachineIntegerType::Int32, true) => {
            ConditionTerm::signed_less_than(left_value, right_value)
        }
        (MachineIntegerType::UInt32, false) => {
            ConditionTerm::unsigned_less_equal(left_value, right_value)
        }
        (MachineIntegerType::UInt32, true) => {
            ConditionTerm::unsigned_less_than(left_value, right_value)
        }
        (MachineIntegerType::Int64, false) => {
            ConditionTerm::int64_signed_less_equal(left_value, right_value)
        }
        (MachineIntegerType::Int64, true) => {
            ConditionTerm::int64_signed_less_than(left_value, right_value)
        }
        (MachineIntegerType::UInt64, false) => {
            ConditionTerm::uint64_less_equal(left_value, right_value)
        }
        (MachineIntegerType::UInt64, true) => {
            ConditionTerm::uint64_less_than(left_value, right_value)
        }
        _ => return None,
    })
}

/// Compare an exact observed native value with a mathematical constant in
/// that value's format. This is the native/Integer order equivalence, never
/// an integer-to-machine cast: bounds outside the format become intrinsic
/// truths/refusals, and unsupported expressions retain mathematical guards.
fn machine_constant_order(
    left: &IntegerTerm,
    right: &IntegerTerm,
    strict: bool,
) -> Option<ConditionTerm> {
    let (machine, constant, constant_left) = match (left, right) {
        (IntegerTerm::Machine(machine), IntegerTerm::Constant(constant)) => {
            (machine, constant.to_i128()?, false)
        }
        (IntegerTerm::Constant(constant), IntegerTerm::Machine(machine)) => {
            (machine, constant.to_i128()?, true)
        }
        _ => return None,
    };
    crate::instrumentation::record_deterministic_work(2);
    let (minimum, maximum) = match machine.ty() {
        MachineIntegerType::Int32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
        MachineIntegerType::UInt32 => (0, i128::from(u32::MAX)),
        MachineIntegerType::Int64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
        MachineIntegerType::UInt64 => (0, i128::from(u64::MAX)),
        _ => return None,
    };
    let intrinsic = if constant_left {
        if constant < minimum || (!strict && constant == minimum) {
            Some(true)
        } else if constant > maximum || (strict && constant == maximum) {
            Some(false)
        } else {
            None
        }
    } else if constant > maximum || (!strict && constant == maximum) {
        Some(true)
    } else if constant < minimum || (strict && constant == minimum) {
        Some(false)
    } else {
        None
    };
    if let Some(value) = intrinsic {
        return Some(ConditionTerm::Constant(value));
    }
    let constant = match machine.ty() {
        MachineIntegerType::Int32 => Bitvector32Term::Constant(constant as i32 as u32),
        MachineIntegerType::UInt32 => Bitvector32Term::Constant(constant as u32),
        MachineIntegerType::Int64 => Bitvector32Term::Int64Constant(constant as i64),
        MachineIntegerType::UInt64 => Bitvector32Term::UInt64Constant(constant as u64),
        _ => unreachable!("selected order-bridge format"),
    };
    let (left, right) = if constant_left {
        (constant, machine.value().clone())
    } else {
        (machine.value().clone(), constant)
    };
    Some(match (machine.ty(), strict) {
        (MachineIntegerType::Int32, false) => ConditionTerm::signed_less_equal(left, right),
        (MachineIntegerType::Int32, true) => ConditionTerm::signed_less_than(left, right),
        (MachineIntegerType::UInt32, false) => ConditionTerm::unsigned_less_equal(left, right),
        (MachineIntegerType::UInt32, true) => ConditionTerm::unsigned_less_than(left, right),
        (MachineIntegerType::Int64, false) => ConditionTerm::int64_signed_less_equal(left, right),
        (MachineIntegerType::Int64, true) => ConditionTerm::int64_signed_less_than(left, right),
        (MachineIntegerType::UInt64, false) => ConditionTerm::uint64_less_equal(left, right),
        (MachineIntegerType::UInt64, true) => ConditionTerm::uint64_less_than(left, right),
        _ => unreachable!("selected order-bridge format"),
    })
}

/// Observe one native value before applying its mathematical constant offset.
/// These root-local forms never move addition inside a wrapping machine term.
fn machine_offset_parts(term: &IntegerTerm) -> Option<(&SharedMachineIntegerTerm, i128)> {
    match term {
        IntegerTerm::Machine(machine) => Some((machine, 0)),
        IntegerTerm::Add(left, right) => match (left.as_ref(), right.as_ref()) {
            (IntegerTerm::Machine(machine), IntegerTerm::Constant(offset))
            | (IntegerTerm::Constant(offset), IntegerTerm::Machine(machine)) => {
                Some((machine, offset.to_i128()?))
            }
            _ => None,
        },
        IntegerTerm::Subtract(left, right) => match (left.as_ref(), right.as_ref()) {
            (IntegerTerm::Machine(machine), IntegerTerm::Constant(offset)) => {
                Some((machine, offset.to_i128()?.checked_neg()?))
            }
            _ => None,
        },
        _ => None,
    }
}

fn machine_offset_order(
    left: &IntegerTerm,
    right: &IntegerTerm,
    strict: bool,
) -> Option<ConditionTerm> {
    if let (Some((left, left_offset)), Some((right, right_offset))) =
        (machine_offset_parts(left), machine_offset_parts(right))
    {
        if left.ty() != right.ty() {
            return None;
        }
        // Over integers, x+1<=y iff x<y, and x<y+1 iff x<=y.
        // Canceling equal offsets is also exact, including at native extrema.
        let native_strict = match (strict, left_offset.checked_sub(right_offset)?) {
            (strict, 0) => strict,
            (false, 1) => true,
            (true, -1) => false,
            _ => return None,
        };
        return machine_observation_order(
            &IntegerTerm::Machine(left.clone()),
            &IntegerTerm::Machine(right.clone()),
            native_strict,
        );
    }
    let (machine, offset, constant, constant_left) = match (left, right) {
        (IntegerTerm::Constant(constant), other) => {
            let (machine, offset) = machine_offset_parts(other)?;
            (machine, offset, constant, true)
        }
        (other, IntegerTerm::Constant(constant)) => {
            let (machine, offset) = machine_offset_parts(other)?;
            (machine, offset, constant, false)
        }
        _ => return None,
    };
    let constant = IntegerTerm::constant(constant.to_i128()?.checked_sub(offset)?.into());
    let observed = IntegerTerm::Machine(machine.clone());
    if constant_left {
        machine_constant_order(&constant, &observed, strict)
    } else {
        machine_constant_order(&observed, &constant, strict)
    }
}

pub(in crate::kernel) fn domain_equal(left: IntegerTerm, right: IntegerTerm) -> ConditionTerm {
    if let Some((left, right)) = native_operands(&left, &right) {
        ConditionTerm::Constant(left == right)
    } else {
        ConditionTerm::integer_equal(left, right)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum PointerDomainCheck {
    Legacy,
    Checked(Vec<ConditionTerm>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum PointerDomainView {
    Typed,
    /// The caller must select this only where its language permits character
    /// access to the selected object's representation. Casting alone does
    /// not select this policy or change the retained object descriptor.
    ObjectRepresentationBytes,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum PointerDomainRefusal {
    UnresolvedDesignation,
    UnauthenticatedDomain,
    UnsupportedDisplacement,
    IncompatibleType,
    IncompatibleStride,
    IncompatibleDomain,
    InvalidAccessWidth,
}

struct AuthenticatedDomain {
    base: Pointer,
    element_type: CType,
    stride: u32,
    count: SharedIntegerTerm,
    /// A witnessed native prefix never identifies the complete array end.
    prefix: bool,
    source_slice: bool,
    authentication_guards: Vec<ConditionTerm>,
    paired_base: Option<CPointerValue>,
}

fn resolved_carrier<'a>(
    state: &CState,
    pointer: &'a CPointerValue,
    assumptions: &PureFactContext,
) -> Result<std::borrow::Cow<'a, CPointerValue>, PointerDomainRefusal> {
    if matches!(pointer.designation(), Some(PointerDesignation::Loaded(_))) {
        let resolved =
            crate::kernel::memory_provenance::resolve_loaded_pointer_carrier(pointer, assumptions)
                .or_else(|| {
                    // Keep the producer's spelling when its exact read pair
                    // already names a retained input. Changing only the raw
                    // spelling here would leave the prefix's retained base
                    // in a different address coordinate system.
                    (state.memory().native_input_span(pointer).is_some()
                        || state.memory().allocated_scalar_extent(pointer).is_some()
                        || state.memory().native_record_prefix(pointer).is_some())
                    .then(|| pointer.clone())
                })
                .or_else(|| {
                    let canonical =
                        crate::kernel::memory_provenance::canonical_loaded_pointer_carrier(
                            pointer,
                            assumptions,
                        )?;
                    state
                        .memory()
                        .checked_native_record_pointer(&canonical)
                        .or_else(|| {
                            (state.memory().native_input_span(&canonical).is_some()
                                || state.memory().allocated_scalar_extent(&canonical).is_some()
                                || state.memory().native_record_prefix(&canonical).is_some())
                            .then_some(canonical)
                        })
                })
                .or_else(|| state.memory().checked_native_record_pointer(pointer));
        let Some(resolved) = resolved else {
            return if state.memory().native_input_span(pointer).is_some()
                || state.memory().allocated_scalar_extent(pointer).is_some()
                || state.memory().native_record_prefix(pointer).is_some()
            {
                Ok(std::borrow::Cow::Borrowed(pointer))
            } else {
                Err(PointerDomainRefusal::UnresolvedDesignation)
            };
        };
        let resolved = if matches!(
            resolved.designation(),
            Some(PointerDesignation::Unresolved(_))
        ) {
            state
                .memory()
                .checked_native_record_pointer(&resolved)
                .unwrap_or(resolved)
        } else {
            resolved
        };
        Ok(std::borrow::Cow::Owned(resolved))
    } else if matches!(
        pointer.designation(),
        Some(PointerDesignation::Unresolved(_))
    ) {
        if state.memory().native_record_prefix(pointer).is_some() {
            return Ok(std::borrow::Cow::Borrowed(pointer));
        }
        Ok(state
            .memory()
            .checked_native_record_pointer(pointer)
            .map(std::borrow::Cow::Owned)
            .unwrap_or(std::borrow::Cow::Borrowed(pointer)))
    } else {
        Ok(std::borrow::Cow::Borrowed(pointer))
    }
}

fn authenticated_domain(
    state: &CState,
    pointer: &CPointerValue,
    assumptions: &PureFactContext,
) -> Result<Option<AuthenticatedDomain>, PointerDomainRefusal> {
    let Some(designation) = pointer.designation() else {
        return if state.typed_access_policy() == CTypedAccessPolicy::NativeObjectOnly {
            Err(PointerDomainRefusal::UnresolvedDesignation)
        } else {
            Ok(None)
        };
    };
    if let PointerDesignation::InputSelected {
        base,
        element_type,
        stride,
        count,
        ..
    } = designation
    {
        let guards = state
            .memory()
            .authenticated_input_selection(pointer, assumptions)
            .ok_or(PointerDomainRefusal::UnauthenticatedDomain)?;
        if *stride == 0 {
            return Err(PointerDomainRefusal::UnauthenticatedDomain);
        }
        return Ok(Some(AuthenticatedDomain {
            base: base.clone(),
            element_type: *element_type,
            stride: *stride,
            count: count.clone(),
            // A native input's selected child does not implicitly admit
            // representation traversal through a differently typed cast.
            prefix: true,
                source_slice: false,
            authentication_guards: guards,
            paired_base: None,
        }));
    }
    let PointerDesignation::Object {
        base,
        element_type,
        stride,
        count,
        ..
    } = designation
    else {
        if let Some((origin, element_type, bytes)) = state.memory().allocated_scalar_extent(pointer)
        {
            if state.typed_access_policy() == CTypedAccessPolicy::NativeObjectOnly {
                return Err(PointerDomainRefusal::UnauthenticatedDomain);
            }
            let stride = element_type.byte_width();
            // Only complete, aligned scalar elements belong to this bounded
            // C access profile. A trailing byte suffix is not another element.
            let count = IntegerTerm::truncating_quotient(
                bytes.as_ref().clone(),
                IntegerTerm::constant_i64(i64::from(stride)),
            );
            return Ok(Some(AuthenticatedDomain {
                base: origin.pointer().clone(),
                element_type,
                stride,
                count: count.into(),
                prefix: true,
                source_slice: false,
                authentication_guards: Vec::new(),
                paired_base: Some(origin),
            }));
        }
        if let Some((origin, layout, count)) = state.memory().native_record_prefix(pointer) {
            let stride = layout.size_bytes();
            if stride == 0 {
                return Err(PointerDomainRefusal::UnauthenticatedDomain);
            }
            return Ok(Some(AuthenticatedDomain {
                base: origin.pointer().clone(),
                element_type: CType::UInt8Array(stride),
                stride,
                count,
                prefix: true,
                source_slice: false,
                authentication_guards: Vec::new(),
                paired_base: Some(origin),
            }));
        }
        if let Some((origin, element_type, count)) = state.memory().native_input_span(pointer) {
            if state.typed_access_policy() == CTypedAccessPolicy::NativeObjectOnly
                && state.memory().native_input_span_policy(pointer)
                    == Some(CTypedAccessPolicy::CAllocatedAccessAllowed)
            {
                return Err(PointerDomainRefusal::UnauthenticatedDomain);
            }
            let stride = element_type.byte_width();
            if stride == 0 {
                return Err(PointerDomainRefusal::UnauthenticatedDomain);
            }
            return Ok(Some(AuthenticatedDomain {
                base: origin.pointer().clone(),
                element_type,
                stride,
                count,
                prefix: true,
                source_slice: state.memory().native_input_is_slice(pointer),
                authentication_guards: Vec::new(),
                paired_base: Some(origin),
            }));
        }
        // Loaded values need a complete stored-carrier certificate, including
        // the address used to calculate position. A resolved descriptor alone
        // or an address equality is insufficient.
        return Err(PointerDomainRefusal::UnresolvedDesignation);
    };
    if *stride == 0 || !state.memory().authenticated_pointer_domain_at_base(pointer) {
        return Err(PointerDomainRefusal::UnauthenticatedDomain);
    }
    Ok(Some(AuthenticatedDomain {
        base: base.clone(),
        element_type: *element_type,
        stride: *stride,
        count: count.clone(),
        prefix: false,
        source_slice: false,
        authentication_guards: Vec::new(),
        paired_base: None,
    }))
}

fn machine_integer(term: &Bitvector32Term, kind: MachineIntegerType) -> IntegerTerm {
    let constant = match kind {
        MachineIntegerType::Int32 => term
            .as_const()
            .map(|value| IntegerTerm::constant_i64(i64::from(value as i32))),
        MachineIntegerType::Int64 => term.int64_as_const().map(IntegerTerm::constant_i64),
        MachineIntegerType::UInt64 => term
            .uint64_as_const()
            .map(|value| IntegerTerm::constant(value.into())),
        _ => None,
    };
    constant.unwrap_or_else(|| {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(kind, term.clone()))
    })
}

/// Interpret address scaling after machine observation, rather than moving
/// scaling or addition inside a modular machine term. The work follows only
/// the selected offset tree and uses no resource, alias or memory-history scan.
fn exact_offset_units(offset: &PointerOffsetTerm, unit: u32) -> Option<IntegerTerm> {
    enum Work<'a> {
        Visit(&'a PointerOffsetTerm),
        Add,
    }
    let unit = i64::from(unit);
    let mut pending = vec![Work::Visit(offset)];
    let mut values = Vec::new();
    while let Some(work) = pending.pop() {
        match work {
            Work::Visit(offset) => {
                crate::instrumentation::record_deterministic_work(1);
                match offset {
                    PointerOffsetTerm::Constant(bytes) if bytes % unit == 0 => {
                        values.push(IntegerTerm::constant_i64(bytes / unit));
                    }
                    PointerOffsetTerm::Add(left, right) => {
                        pending.push(Work::Add);
                        pending.push(Work::Visit(right));
                        pending.push(Work::Visit(left));
                    }
                    PointerOffsetTerm::Int32Scaled { value, byte_width }
                        if byte_width % unit == 0 =>
                    {
                        values.push(domain_multiply(
                            machine_integer(value, MachineIntegerType::Int32),
                            IntegerTerm::constant_i64(byte_width / unit),
                        ));
                    }
                    PointerOffsetTerm::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } if byte_width % unit == 0 => {
                        values.push(domain_multiply(
                            machine_integer(
                                value,
                                if *unsigned {
                                    MachineIntegerType::UInt64
                                } else {
                                    MachineIntegerType::Int64
                                },
                            ),
                            IntegerTerm::constant_i64(byte_width / unit),
                        ));
                    }
                    _ => return None,
                }
            }
            Work::Add => {
                let right = values.pop()?;
                let left = values.pop()?;
                values.push(domain_add(left, right));
            }
        }
    }
    values.pop()
}

/// Cancel only identical additive byte terms before requiring element-unit
/// divisibility. In particular, an opaque address need not itself be divisible
/// by the element width when its retained displacement is exact.
fn cancelled_offset_units(
    pointer: &PointerOffsetTerm,
    base: &PointerOffsetTerm,
    unit: u32,
) -> Option<IntegerTerm> {
    let mut pending = vec![(pointer, 1i64), (base, -1i64)];
    let mut atoms = std::collections::BTreeMap::<&PointerOffsetTerm, i64>::new();
    let mut bytes = num_bigint::BigInt::from(0);
    while let Some((offset, sign)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                pending.push((left, sign));
                pending.push((right, sign));
            }
            PointerOffsetTerm::Constant(value) => bytes += num_bigint::BigInt::from(*value) * sign,
            atom => {
                let coefficient = atoms.entry(atom).or_default();
                *coefficient = coefficient.checked_add(sign)?;
            }
        }
    }
    let unit_integer = num_bigint::BigInt::from(unit);
    if &bytes % &unit_integer != num_bigint::BigInt::from(0) {
        return None;
    }
    let mut displacement = IntegerTerm::constant(bytes / unit_integer);
    for (atom, coefficient) in atoms {
        if coefficient == 0 {
            continue;
        }
        // Observe the complete machine value before multiplying its external
        // byte scale. Never rewrite a modular addition or multiply inside it.
        let observed = exact_offset_units(atom, unit)?;
        displacement = domain_add(
            displacement,
            domain_multiply(observed, IntegerTerm::constant_i64(coefficient)),
        );
    }
    Some(displacement)
}

fn exact_displacement(pointer: &Pointer, base: &Pointer, unit: u32) -> Option<IntegerTerm> {
    if unit == 0 || pointer.block != base.block {
        return None;
    }
    if pointer.offset == base.offset {
        return Some(IntegerTerm::constant_i64(0));
    }
    // Cancel a direct retained base before observing offsets. A symbolic raw
    // address is usable as a base without assigning a numeric value to it.
    if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
        if left.as_ref() == &base.offset {
            return exact_offset_units(right, unit);
        }
        if right.as_ref() == &base.offset {
            return exact_offset_units(left, unit);
        }
    }
    // A reconstructed member root may have nested +offset/-offset even when
    // the retained base is one native scaled term. Cancel identical byte
    // summands before observing absolute offsets, which could otherwise leave
    // an unevaluated Machine-Machine difference despite exact divisibility.
    if (matches!(&pointer.offset, PointerOffsetTerm::Add(_, _))
        || matches!(&base.offset, PointerOffsetTerm::Add(_, _)))
        && let Some(displacement) = cancelled_offset_units(&pointer.offset, &base.offset, unit)
    {
        return Some(displacement);
    }
    match (
        exact_offset_units(&pointer.offset, unit),
        exact_offset_units(&base.offset, unit),
    ) {
        (Some(pointer), Some(base)) => Some(domain_subtract(pointer, base)),
        _ => cancelled_offset_units(&pointer.offset, &base.offset, unit),
    }
}

fn append_guard(guards: &mut Vec<ConditionTerm>, condition: ConditionTerm) {
    if condition != ConditionTerm::Constant(true) && !guards.contains(&condition) {
        guards.push(condition);
    }
}

pub(in crate::kernel) fn domain_displacement(
    pointer: &Pointer,
    base: &Pointer,
    unit: u32,
    assumptions: &PureFactContext,
) -> Option<IntegerTerm> {
    if unit == 0 {
        return None;
    }
    exact_displacement(pointer, base, unit)
        .or_else(|| {
            // This changes only the address spelling of an already authenticated
            // carrier. It never selects a domain from an equal address.
            let aligned = assumptions.equality_graph.pointer_at_base(pointer, base)?;
            exact_displacement(&aligned, base, unit)
        })
        .or_else(|| {
            let PointerOffsetTerm::Add(left, right) = &pointer.offset else {
                return None;
            };
            // A captured interior address can align to base+i rather than base.
            // Preserve the selected outer displacement without rewriting a machine
            // operation inside it. Only these two explicit additive placements are
            // queried; this neither searches aliases nor recovers a designation.
            for (prefix, rest) in [(left, right), (right, left)] {
                let Some(rest) = exact_offset_units(rest, unit) else {
                    continue;
                };
                let prefix = Pointer {
                    block: pointer.block.clone(),
                    offset: prefix.as_ref().clone(),
                };
                let Some(aligned) = assumptions.equality_graph.pointer_at_base(&prefix, base)
                else {
                    continue;
                };
                if let Some(position) = exact_displacement(&aligned, base, unit) {
                    return Some(domain_add(position, rest));
                }
            }
            None
        })
}

#[derive(Clone, Copy)]
enum DomainQuery {
    Formation,
    Executable,
    Span,
}

fn position_guards(
    pointer: &Pointer,
    domain: &AuthenticatedDomain,
    view: PointerDomainView,
    query: DomainQuery,
    guards: &mut Vec<ConditionTerm>,
    assumptions: &PureFactContext,
) -> Result<(IntegerTerm, IntegerTerm, u32), PointerDomainRefusal> {
    for guard in &domain.authentication_guards {
        append_guard(guards, guard.clone());
    }
    if domain.prefix
        && view == PointerDomainView::ObjectRepresentationBytes
        && domain.element_type != CType::UInt8
    {
        return Err(PointerDomainRefusal::IncompatibleType);
    }
    let (stride, count) = match view {
        PointerDomainView::Typed => (domain.stride, domain.count.as_ref().clone()),
        PointerDomainView::ObjectRepresentationBytes => (
            1,
            domain_multiply(
                domain.count.as_ref().clone(),
                IntegerTerm::constant_i64(i64::from(domain.stride)),
            ),
        ),
    };
    if domain.prefix {
        append_guard(
            guards,
            match query {
                DomainQuery::Formation if domain.source_slice =>
                    domain_less_equal(IntegerTerm::constant_i64(0), count.clone()),
                DomainQuery::Executable | DomainQuery::Formation => {
                    domain_less_than(IntegerTerm::constant_i64(0), count.clone())
                }
                DomainQuery::Span => domain_less_equal(IntegerTerm::constant_i64(0), count.clone()),
            },
        );
        // Match wide held ranges: the byte extent fits isize::MAX, so every
        // selected native displacement is exact without modular multiplication.
        // The source slice signature itself certifies its bounded extent.
        // Resource prefixes retain their separate numeric proof obligation.
        if !domain.source_slice {
        append_guard(
            guards,
            domain_less_equal(
                domain.count.as_ref().clone(),
                IntegerTerm::constant_i64(native_prefix_element_limit(domain.stride)),
            ),
        );
        }
    }
    // An opaque read may have either the original scaled-load spelling or
    // its typed read application. Only the identical full read pair permits
    // both spellings to use a common byte coordinate system.
    let paired = domain.paired_base.as_ref().and_then(|base| {
        let Some(PointerDesignation::Loaded(origin)) = base.designation() else {
            return None;
        };
        let actual = base.clone().with_pointer(pointer.clone());
        let actual_offset =
            crate::kernel::memory_provenance::paired_pointer_load_displacement(&actual, origin)?;
        let base_offset =
            crate::kernel::memory_provenance::paired_pointer_load_displacement(base, origin)?;
        let block = PointerBlock::LoadedPointer(origin.id());
        Some((
            Pointer {
                block: block.clone(),
                offset: actual_offset,
            },
            Pointer {
                block,
                offset: base_offset,
            },
        ))
    });
    let (pointer, base) = paired
        .as_ref()
        .map_or((pointer, &domain.base), |(pointer, base)| (pointer, base));
    let position = if let Some(position) = domain_displacement(pointer, base, stride, assumptions) {
        position
    } else {
        let bytes = domain_displacement(pointer, base, 1, assumptions)
            .ok_or(PointerDomainRefusal::UnsupportedDisplacement)?;
        let stride = IntegerTerm::constant_i64(i64::from(stride));
        append_guard(
            guards,
            domain_equal(
                IntegerTerm::truncating_remainder(bytes.clone(), stride.clone()),
                IntegerTerm::constant_i64(0),
            ),
        );
        IntegerTerm::truncating_quotient(bytes, stride)
    };
    append_guard(
        guards,
        domain_less_equal(IntegerTerm::constant_i64(0), position.clone()),
    );
    Ok((position, count, stride))
}

/// A native record index carries its authenticated source layout separately
/// from the byte address encoding. Numeric byte arithmetic cannot select it.
pub(in crate::kernel) fn checked_record_pointer_formation(
    state: &CState,
    origin: &CPointerValue,
    result: &Pointer,
    layout: &Arc<CAggregateLayout>,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    let pointer = resolved_carrier(state, origin, assumptions)?;
    if pointer.designation().is_none() {
        return if state.typed_access_policy() == CTypedAccessPolicy::NativeObjectOnly {
            Err(PointerDomainRefusal::UnresolvedDesignation)
        } else {
            Ok(PointerDomainCheck::Legacy)
        };
    }
    let mut guards = Vec::new();
    if let Some((_, actual, _)) = state.memory().native_record_prefix(&pointer) {
        if !actual.selects_layout_path(&[], layout) {
            return Err(PointerDomainRefusal::IncompatibleDomain);
        }
    } else {
        let base = match pointer.designation() {
            Some(
                PointerDesignation::Object { base, .. }
                | PointerDesignation::InputSelected { base, .. },
            ) => base.clone(),
            _ => pointer.pointer().clone(),
        };
        let at_base = pointer.as_ref().clone().with_pointer(base);
        if matches!(
            at_base.designation(),
            Some(PointerDesignation::Object { .. })
        ) {
            if !state.memory().has_aggregate_object_domain(&at_base, layout) {
                return Err(PointerDomainRefusal::IncompatibleDomain);
            }
        } else {
            let selection = CAggregateMemberSelection {
                layout: layout.clone(),
                path: Arc::from([]),
                value_type: CType::UInt8Array(layout.size_bytes()),
            };
            let (_, authentication) = state
                .memory()
                .guarded_native_record_selection(&at_base, &selection, assumptions)
                .ok_or(PointerDomainRefusal::UnauthenticatedDomain)?;
            guards.extend(authentication);
        }
    }
    match checked_pointer_formation(
        state,
        origin,
        result,
        layout.size_bytes(),
        PointerDomainView::Typed,
        assumptions,
    )? {
        PointerDomainCheck::Checked(formation) => {
            for guard in formation {
                append_guard(&mut guards, guard);
            }
            Ok(PointerDomainCheck::Checked(guards))
        }
        PointerDomainCheck::Legacy => Err(PointerDomainRefusal::UnauthenticatedDomain),
    }
}

pub(in crate::kernel) fn checked_pointer_formation(
    state: &CState,
    origin: &CPointerValue,
    result: &Pointer,
    step_width: u32,
    view: PointerDomainView,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    let resolved_origin = resolved_carrier(state, origin, assumptions)?;
    let Some(domain) = authenticated_domain(state, &resolved_origin, assumptions)? else {
        return Ok(PointerDomainCheck::Legacy);
    };
    if step_width
        != match view {
            PointerDomainView::Typed => domain.stride,
            PointerDomainView::ObjectRepresentationBytes => 1,
        }
    {
        return Err(PointerDomainRefusal::IncompatibleStride);
    }
    let mut guards = Vec::new();
    let result_carrier;
    let resolved_result;
    let result = if matches!(origin.designation(), Some(PointerDesignation::Loaded(_))) {
        result_carrier = origin.clone().with_pointer(result.clone());
        resolved_result = resolved_carrier(state, &result_carrier, assumptions)?;
        resolved_result.pointer()
    } else {
        result
    };
    for pointer in [resolved_origin.pointer(), result] {
        let (position, count, _) = position_guards(
            pointer,
            &domain,
            view,
            DomainQuery::Formation,
            &mut guards,
            assumptions,
        )?;
        append_guard(&mut guards, domain_less_equal(position, count));
    }
    Ok(PointerDomainCheck::Checked(guards))
}

pub(in crate::kernel) fn checked_pointer_access(
    state: &CState,
    pointer: &CPointerValue,
    access_type: CType,
    bytes: u32,
    view: PointerDomainView,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    let pointer = resolved_carrier(state, pointer, assumptions)?;
    let Some(domain) = authenticated_domain(state, &pointer, assumptions)? else {
        return Ok(PointerDomainCheck::Legacy);
    };
    match view {
        PointerDomainView::Typed if access_type != domain.element_type => {
            return Err(PointerDomainRefusal::IncompatibleType);
        }
        PointerDomainView::ObjectRepresentationBytes
            if !matches!(access_type, CType::Int8 | CType::UInt8) =>
        {
            return Err(PointerDomainRefusal::IncompatibleType);
        }
        _ => {}
    }
    if bytes == 0 || bytes != access_type.byte_width() {
        return Err(PointerDomainRefusal::InvalidAccessWidth);
    }
    let mut guards = Vec::new();
    let (position, count, stride) = position_guards(
        pointer.pointer(),
        &domain,
        view,
        DomainQuery::Executable,
        &mut guards,
        assumptions,
    )?;
    if bytes == stride {
        // With positive stride, one complete element fits exactly when its
        // mathematical position is strictly below the element count.
        append_guard(&mut guards, domain_less_than(position, count));
        return Ok(PointerDomainCheck::Checked(guards));
    }
    let start = domain_multiply(position, IntegerTerm::constant_i64(i64::from(stride)));
    let end = domain_add(start, IntegerTerm::constant_i64(i64::from(bytes)));
    let extent = domain_multiply(count, IntegerTerm::constant_i64(i64::from(stride)));
    append_guard(&mut guards, domain_less_equal(end, extent));
    Ok(PointerDomainCheck::Checked(guards))
}

/// Subtraction needs the same selected array or one-element scalar domain,
/// rather than merely the same enclosing allocation. Native ordering of
/// different declared record members is a separate language operation.
pub(in crate::kernel) fn checked_pointer_difference(
    state: &CState,
    left: &CPointerValue,
    right: &CPointerValue,
    step_width: u32,
    view: PointerDomainView,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    let left = resolved_carrier(state, left, assumptions)?;
    let right = resolved_carrier(state, right, assumptions)?;
    match (left.designation(), right.designation()) {
        (None, None) => {
            return if state.typed_access_policy() == CTypedAccessPolicy::NativeObjectOnly {
                Err(PointerDomainRefusal::UnresolvedDesignation)
            } else {
                Ok(PointerDomainCheck::Legacy)
            };
        }
        (Some(_), Some(_)) if left.same_designation(&right) => {}
        _ => return Err(PointerDomainRefusal::IncompatibleDomain),
    }
    authenticated_domain(state, &right, assumptions)?;
    checked_pointer_formation(state, &left, right.pointer(), step_width, view, assumptions)
}

/// Internal byte displacement checks formation inside the same retained
/// domain. This is not permission to read the object's byte representation.
pub(in crate::kernel) fn checked_pointer_byte_formation(
    state: &CState,
    origin: &CPointerValue,
    result: &Pointer,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    checked_pointer_formation(
        state,
        origin,
        result,
        1,
        PointerDomainView::ObjectRepresentationBytes,
        assumptions,
    )
}

/// The caller explicitly selects its language's admitted member-order rule.
/// Distinct members must be complete, nonoverlapping siblings at their actual
/// bases; a one-past pointer retains its original selected domain.
pub(in crate::kernel) fn checked_pointer_ordering(
    state: &CState,
    left: &CPointerValue,
    right: &CPointerValue,
    step_width: u32,
    view: PointerDomainView,
    allow_record_members: bool,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    let left = resolved_carrier(state, left, assumptions)?;
    let right = resolved_carrier(state, right, assumptions)?;
    if left.same_designation(&right) {
        return checked_pointer_difference(state, &left, &right, step_width, view, assumptions);
    }
    if !allow_record_members {
        return Err(PointerDomainRefusal::IncompatibleDomain);
    }
    let (
        Some(PointerDesignation::Object {
            root: left_root,
            path: left_path,
            ..
        }),
        Some(PointerDesignation::Object {
            root: right_root,
            path: right_path,
            ..
        }),
    ) = (left.designation(), right.designation())
    else {
        return Err(PointerDomainRefusal::IncompatibleDomain);
    };
    let Some((PointerDomainSelection::Member(left_member), left_parent)) = left_path.split_last()
    else {
        return Err(PointerDomainRefusal::IncompatibleDomain);
    };
    let Some((PointerDomainSelection::Member(right_member), right_parent)) =
        right_path.split_last()
    else {
        return Err(PointerDomainRefusal::IncompatibleDomain);
    };
    if left_root != right_root || left_parent != right_parent || left_member == right_member {
        return Err(PointerDomainRefusal::IncompatibleDomain);
    }
    let left_domain = authenticated_domain(state, &left, assumptions)?
        .ok_or(PointerDomainRefusal::IncompatibleDomain)?;
    let right_domain = authenticated_domain(state, &right, assumptions)?
        .ok_or(PointerDomainRefusal::IncompatibleDomain)?;
    let unit = IntegerTerm::constant_i64(1);
    if left_domain.count.as_ref() != &unit || right_domain.count.as_ref() != &unit {
        return Err(PointerDomainRefusal::IncompatibleDomain);
    }
    let expected_stride = |domain: &AuthenticatedDomain| match view {
        PointerDomainView::Typed => domain.stride,
        PointerDomainView::ObjectRepresentationBytes => 1,
    };
    if step_width != expected_stride(&left_domain) || step_width != expected_stride(&right_domain) {
        return Err(PointerDomainRefusal::IncompatibleStride);
    }
    // Authentication follows each selected layout path. The remaining shape
    // check uses its constant declared coordinates, not address inequality.
    let left_start = exact_displacement(&left_domain.base, left_root, 1)
        .and_then(|offset| offset.as_const().cloned())
        .ok_or(PointerDomainRefusal::UnsupportedDisplacement)?;
    let right_start = exact_displacement(&right_domain.base, right_root, 1)
        .and_then(|offset| offset.as_const().cloned())
        .ok_or(PointerDomainRefusal::UnsupportedDisplacement)?;
    let left_end = &left_start + i64::from(left_domain.stride);
    let right_end = &right_start + i64::from(right_domain.stride);
    if left_start < 0.into()
        || right_start < 0.into()
        || !(left_end <= right_start || right_end <= left_start)
    {
        return Err(PointerDomainRefusal::IncompatibleDomain);
    }
    let mut guards = Vec::new();
    for (pointer, domain) in [(&left, &left_domain), (&right, &right_domain)] {
        let (position, _, _) = position_guards(
            pointer.pointer(),
            domain,
            view,
            DomainQuery::Executable,
            &mut guards,
            assumptions,
        )?;
        append_guard(
            &mut guards,
            domain_equal(position, IntegerTerm::constant_i64(0)),
        );
    }
    Ok(PointerDomainCheck::Checked(guards))
}

/// A typed interface span is relative to the carried pointer's position.
/// Permission splitting cannot change the selected domain or its extent.
/// The closed bound admits an empty span at one-past without admitting an
/// element read there.
pub(in crate::kernel) fn checked_pointer_span(
    state: &CState,
    pointer: &CPointerValue,
    start: IntegerTerm,
    end: IntegerTerm,
    element_width: u32,
    view: PointerDomainView,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    checked_pointer_span_with_type(
        state,
        pointer,
        start,
        end,
        element_width,
        view,
        None,
        assumptions,
    )
}

/// A typed input promise can be empty even when the referent has another
/// type. A nonempty promise retains the authenticated element type.
pub(in crate::kernel) fn checked_typed_pointer_span(
    state: &CState,
    pointer: &CPointerValue,
    start: IntegerTerm,
    end: IntegerTerm,
    element_type: CType,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    let resolved = resolved_carrier(state, pointer, assumptions)?;
    if state.memory().allocated_scalar_extent(&resolved).is_some()
        || state.memory().native_input_span_policy(&resolved)
            == Some(CTypedAccessPolicy::CAllocatedAccessAllowed)
    {
        return Err(PointerDomainRefusal::UnauthenticatedDomain);
    }
    checked_c_typed_pointer_span(state, pointer, start, end, element_type, assumptions)
}

/// A C typed-place contract also admits the separately authenticated bounded
/// allocation profile. This never installs a native object witness.
pub(in crate::kernel) fn checked_c_typed_pointer_span(
    state: &CState,
    pointer: &CPointerValue,
    start: IntegerTerm,
    end: IntegerTerm,
    element_type: CType,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    checked_pointer_span_with_type(
        state,
        pointer,
        start,
        end,
        element_type.byte_width(),
        PointerDomainView::Typed,
        Some(element_type),
        assumptions,
    )
}

#[allow(clippy::too_many_arguments)]
fn checked_pointer_span_with_type(
    state: &CState,
    pointer: &CPointerValue,
    start: IntegerTerm,
    end: IntegerTerm,
    element_width: u32,
    view: PointerDomainView,
    requested_type: Option<CType>,
    assumptions: &PureFactContext,
) -> Result<PointerDomainCheck, PointerDomainRefusal> {
    let pointer = resolved_carrier(state, pointer, assumptions)?;
    let Some(domain) = authenticated_domain(state, &pointer, assumptions)? else {
        return Ok(PointerDomainCheck::Legacy);
    };
    let expected_stride = match view {
        PointerDomainView::Typed => domain.stride,
        PointerDomainView::ObjectRepresentationBytes => 1,
    };
    if element_width != expected_stride {
        return Err(PointerDomainRefusal::IncompatibleStride);
    }
    let mut guards = Vec::new();
    if requested_type.is_some_and(|requested| requested != domain.element_type) {
        // The ordinary start <= end guard below supplies the other half of
        // emptiness. Keep native count observations in their exact format.
        append_guard(&mut guards, domain_less_equal(end.clone(), start.clone()));
    }
    let (position, count, _) = position_guards(
        pointer.pointer(),
        &domain,
        view,
        DomainQuery::Span,
        &mut guards,
        assumptions,
    )?;
    append_guard(
        &mut guards,
        domain_less_equal(IntegerTerm::constant_i64(0), start.clone()),
    );
    append_guard(&mut guards, domain_less_equal(start, end.clone()));
    append_guard(
        &mut guards,
        domain_less_equal(domain_add(position, end), count),
    );
    Ok(PointerDomainCheck::Checked(guards))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allocated_scalar_domain_is_c_only_bounded_and_does_not_initialize() {
        let _session = crate::kernel::VerificationSession::enter();
        let identity = Variable(989_790);
        let pending = Pointer::symbolic(identity);
        let memory = CMemory::new()
            .with_pending_allocated_scalar(pending.clone(), 5.into(), false, CType::Int32, identity)
            .unwrap();
        let (memory, _, base) = memory
            .resolve_pending_heap_allocation(&pending, true)
            .unwrap();
        let pointer = CPointerValue::new(base.clone(), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let state = CState::new().with_memory(memory);
        let context = PureFactContext::new();
        let check = |result: Result<PointerDomainCheck, PointerDomainRefusal>| {
            matches!(result, Ok(PointerDomainCheck::Checked(guards))
                if guards.iter().all(|guard| context.decide(guard) == Some(true)))
        };
        assert!(check(checked_c_typed_pointer_span(
            &state,
            &pointer,
            0.into(),
            1.into(),
            CType::Int32,
            &context
        )));
        assert!(!check(checked_c_typed_pointer_span(
            &state,
            &pointer,
            0.into(),
            2.into(),
            CType::Int32,
            &context
        )));
        assert!(!check(checked_typed_pointer_span(
            &state,
            &pointer,
            0.into(),
            1.into(),
            CType::Int32,
            &context
        )));
        assert!(check(checked_pointer_access(
            &state,
            &pointer,
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(!check(checked_pointer_access(
            &state,
            &pointer.clone().with_type(CType::UInt32Pointer),
            CType::UInt32,
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(!check(checked_pointer_access(
            &state,
            &pointer.clone().with_pointer(base.offset_by_bytes(1)),
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(
            !state
                .memory()
                .has_initialized_bytes_under(&base, 4, &context)
        );
        assert!(state.resources().facts().is_empty());
        let native_state = state
            .clone()
            .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
        assert!(!check(checked_pointer_access(
            &native_state,
            &pointer,
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &context
        )));
        assert!(!check(checked_pointer_formation(
            &native_state,
            &pointer,
            &base.offset_by_bytes(4),
            4,
            PointerDomainView::Typed,
            &context
        )));
        for forged in [
            CPointerValue::new(base.clone(), CType::Int32Pointer),
            pointer
                .clone()
                .with_designation(PointerDesignation::Unresolved(Variable(989_791))),
        ] {
            assert!(!check(checked_c_typed_pointer_span(
                &state,
                &forged,
                0.into(),
                1.into(),
                CType::Int32,
                &context
            )));
        }
    }

    #[test]
    fn native_execution_rejects_c_only_prefix_even_with_the_same_address_and_type() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = CState::new().with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
        let legacy = CPointerValue::new(Pointer::symbolic(Variable(989_794)), CType::Int32Pointer);
        assert!(
            checked_pointer_access(
                &native,
                &legacy,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &PureFactContext::new()
            )
            .is_err()
        );
        assert!(
            checked_pointer_difference(
                &native,
                &legacy,
                &legacy,
                4,
                PointerDomainView::Typed,
                &PureFactContext::new()
            )
            .is_err()
        );
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(989_795)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(989_796)));
        for policy in [
            CTypedAccessPolicy::CAllocatedAccessAllowed,
            CTypedAccessPolicy::NativeObjectOnly,
        ] {
            let memory = CMemory::new()
                .with_typed_input_span(
                    pointer.clone(),
                    CType::Int32,
                    IntegerTerm::constant_i64(1).into(),
                    policy,
                )
                .unwrap();
            let state = CState::new()
                .with_memory(memory)
                .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
            let result = checked_pointer_access(
                &state,
                &pointer,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &PureFactContext::new(),
            );
            assert_eq!(
                matches!(result, Ok(PointerDomainCheck::Checked(guards))
                if guards.is_empty()),
                policy == CTypedAccessPolicy::NativeObjectOnly
            );
        }
    }

    #[test]
    fn native_prefix_counts_use_wide_extent_guards_without_wrapping() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(989_480)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(989_480)));
        let index = Bitvector32Term::Variable(Variable(989_481));
        let count = Bitvector32Term::Variable(Variable(989_482));
        let limit = native_prefix_element_limit(4) as u64;
        let observed = native_count_observation(MachineIntegerType::UInt64, count.clone()).unwrap();
        let state = CState::new().with_memory(
            CMemory::new()
                .with_native_input_span(pointer.clone(), CType::Int32, observed.into())
                .unwrap(),
        );
        let selected = pointer.clone().with_pointer(Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::scale_int64(index.clone(), 4, true),
        });
        let bounded = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_than(index.clone(), count.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    count.clone(),
                    Bitvector32Term::UInt64Constant(limit),
                ),
                true,
            );
        for check in [
            checked_pointer_formation(
                &state,
                &pointer,
                selected.pointer(),
                4,
                PointerDomainView::Typed,
                &bounded,
            ),
            checked_pointer_access(
                &state,
                &selected,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &bounded,
            ),
        ] {
            let guards = conditions(check);
            assert!(
                guards
                    .iter()
                    .all(|guard| bounded.decide(guard) == Some(true)),
                "{guards:?}"
            );
        }
        let unbounded = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_than(index.clone(), count.clone()),
            true,
        );
        let guards = conditions(checked_pointer_access(
            &state,
            &selected,
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &unbounded,
        ));
        assert!(
            guards
                .iter()
                .any(|guard| unbounded.decide(guard) != Some(true))
        );
        let at_end = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_than(Bitvector32Term::UInt64Constant(0), count.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    count.clone(),
                    Bitvector32Term::UInt64Constant(limit),
                ),
                true,
            );
        let endpoint = pointer.clone().with_pointer(Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::scale_int64(count.clone(), 4, true),
        });
        let formation = conditions(checked_pointer_formation(
            &state,
            &pointer,
            endpoint.pointer(),
            4,
            PointerDomainView::Typed,
            &at_end,
        ));
        assert!(
            formation
                .iter()
                .all(|guard| at_end.decide(guard) == Some(true))
        );
        let guards = conditions(checked_pointer_access(
            &state,
            &endpoint,
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &at_end,
        ));
        assert!(
            guards
                .iter()
                .any(|guard| at_end.decide(guard) == Some(false))
        );
        // A separately spelled endpoint remains unusable even when the
        // selected order solver does not normalize its equality to count.
        let equal_endpoint =
            at_end.assume_condition(ConditionTerm::uint64_equal(index, count), true);
        let guards = conditions(checked_pointer_access(
            &state,
            &selected,
            CType::Int32,
            4,
            PointerDomainView::Typed,
            &equal_endpoint,
        ));
        assert!(
            guards
                .iter()
                .any(|guard| equal_endpoint.decide(guard) != Some(true))
        );
        for (count, admitted) in [
            (u64::from(u32::MAX), true),
            (limit, true),
            (limit + 1, false),
            (u64::MAX, false),
        ] {
            let memory = CMemory::new().with_native_input_span(
                pointer.clone(),
                CType::Int32,
                native_count_observation(
                    MachineIntegerType::UInt64,
                    Bitvector32Term::UInt64Constant(count),
                )
                .unwrap()
                .into(),
            );
            assert_eq!(memory.is_ok(), admitted);
            if let Ok(memory) = memory {
                assert!(memory.blocks.is_empty());
                assert_eq!(memory.cells.representation_len(), 0);
                assert!(memory.heap.initialized.as_map().is_empty());
            }
        }
    }

    #[test]
    fn native_count_observation_has_fixed_cost_and_preserves_signedness() {
        for kind in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let samples = [8, 1000, 1_000_000, 1_000_000_000].map(|value| {
                let term = match kind {
                    MachineIntegerType::Int32 | MachineIntegerType::UInt32 => {
                        Bitvector32Term::Constant(value as u32)
                    }
                    MachineIntegerType::Int64 => Bitvector32Term::Int64Constant(value),
                    MachineIntegerType::UInt64 => Bitvector32Term::UInt64Constant(value as u64),
                    _ => unreachable!(),
                };
                let expected = IntegerTerm::from_machine(kind, term.clone());
                let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                    native_count_observation(kind, term)
                });
                assert_eq!(actual, expected);
                work
            });
            assert!(
                samples.windows(2).all(|pair| pair[0] == pair[1]),
                "{kind:?}: {samples:?}"
            );
        }
        for (kind, term) in [
            (
                MachineIntegerType::Int32,
                Bitvector32Term::Constant(i32::MIN as u32),
            ),
            (
                MachineIntegerType::UInt32,
                Bitvector32Term::Constant(u32::MAX),
            ),
            (
                MachineIntegerType::Int64,
                Bitvector32Term::Int64Constant(i64::MIN),
            ),
            (
                MachineIntegerType::UInt64,
                Bitvector32Term::UInt64Constant(u64::MAX),
            ),
        ] {
            assert_eq!(
                native_count_observation(kind, term.clone()),
                IntegerTerm::from_machine(kind, term)
            );
        }
        assert!(
            native_count_observation(
                MachineIntegerType::UInt64,
                Bitvector32Term::Int64Constant(-1)
            )
            .is_none()
        );
    }

    #[test]
    fn selected_interior_alias_displacement_keeps_exact_outer_offset_and_carrier() {
        let _session = crate::kernel::VerificationSession::enter();
        let origin = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(998_560)), 4),
        };
        let interior = origin.offset_by_bytes(4);
        let captured = Pointer::symbolic(Variable(998_561));
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(captured.clone(), interior),
            true,
        );
        let result = captured.offset_by_bytes(4);
        assert_eq!(
            domain_displacement(&result, &origin, 4, &context),
            Some(IntegerTerm::constant_i64(2))
        );
        assert!(domain_displacement(&result, &origin, 4, &PureFactContext::new()).is_none());
        assert!(domain_displacement(&result, &origin, 0, &context).is_none());
        let identity = Variable(998_560);
        let carrier = CPointerValue::new(origin, CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let state = CState::new().with_memory(
            CMemory::new()
                .with_native_input_span(
                    carrier.clone(),
                    CType::Int32,
                    IntegerTerm::constant_i64(3).into(),
                )
                .unwrap(),
        );
        let selected = carrier.clone().with_pointer(captured);
        let check = checked_pointer_formation(
            &state,
            &selected,
            &result,
            4,
            PointerDomainView::Typed,
            &context,
        )
        .unwrap();
        assert!(matches!(check, PointerDomainCheck::Checked(guards)
            if guards.iter().all(|guard| context.decide(guard) == Some(true))));
        assert!(selected.same_designation(&carrier));
        let wrong_key = selected
            .clone()
            .with_designation(PointerDesignation::Unresolved(Variable(998_563)));
        assert!(
            checked_pointer_formation(
                &state,
                &wrong_key,
                &result,
                4,
                PointerDomainView::Typed,
                &context
            )
            .is_err(),
            "address alignment cannot recover a missing native carrier witness"
        );
    }

    #[test]
    fn native_prefix_positions_use_same_format_observed_order_without_wrapping() {
        let _session = crate::kernel::VerificationSession::enter();
        let index = Bitvector32Term::Variable(Variable(989_470));
        let capacity = Bitvector32Term::Variable(Variable(989_471));
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let observe = |value: Bitvector32Term| {
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(ty, value))
            };
            let native_less: fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm = match ty {
                MachineIntegerType::Int32 => ConditionTerm::signed_less_than,
                MachineIntegerType::UInt32 => ConditionTerm::unsigned_less_than,
                MachineIntegerType::Int64 => ConditionTerm::int64_signed_less_than,
                MachineIntegerType::UInt64 => ConditionTerm::uint64_less_than,
                _ => unreachable!(),
            };
            let upper = domain_less_equal(observe(index.clone()), observe(capacity.clone()));
            assert_eq!(PureFactContext::new().decide(&upper), None);
            let positive = PureFactContext::new()
                .assume_condition(native_less(index.clone(), capacity.clone()), true);
            assert_eq!(positive.decide(&upper), Some(true));
            let negative = PureFactContext::new()
                .assume_condition(native_less(capacity.clone(), index.clone()), true);
            assert_eq!(negative.decide(&upper), Some(false));
            let successor = domain_less_equal(
                domain_add(observe(index.clone()), IntegerTerm::constant_i64(1)),
                observe(capacity.clone()),
            );
            assert_eq!(successor, native_less(index.clone(), capacity.clone()));
            assert_eq!(positive.decide(&successor), Some(true));
            assert_eq!(negative.decide(&successor), Some(false));
            assert!(matches!(
                domain_less_equal(
                    domain_add(observe(index.clone()), IntegerTerm::constant_i64(2)),
                    observe(capacity.clone()),
                ),
                ConditionTerm::IntegerLessEqual(_, _)
            ));
        }
        let signed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            index.clone(),
        ));
        let unsigned = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            capacity.clone(),
        ));
        assert!(matches!(
            domain_less_than(signed, unsigned),
            ConditionTerm::IntegerLessThan(_, _)
        ));
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(989_472)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(989_472)));
        let count = IntegerTerm::from_machine(MachineIntegerType::Int32, capacity.clone()).unwrap();
        let state = CState::new().with_memory(
            CMemory::new()
                .with_native_input_span(pointer.clone(), CType::Int32, count.into())
                .unwrap(),
        );
        let bounded = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_than(0.into(), capacity.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(capacity.clone(), (u32::MAX / 4).into()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(0.into(), index.clone()),
                true,
            );
        let positive = bounded.clone().assume_condition(
            ConditionTerm::signed_less_than(index.clone(), capacity.clone()),
            true,
        );
        let selected = pointer.clone().with_pointer(Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
        });
        for check in [
            checked_pointer_formation(
                &state,
                &pointer,
                selected.pointer(),
                4,
                PointerDomainView::Typed,
                &positive,
            ),
            checked_pointer_access(
                &state,
                &selected,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &positive,
            ),
        ] {
            assert!(
                conditions(check)
                    .iter()
                    .all(|guard| positive.decide(guard) == Some(true))
            );
        }
        let outside =
            bounded.assume_condition(ConditionTerm::signed_less_than(index, capacity), false);
        assert!(
            conditions(checked_pointer_access(
                &state,
                &selected,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &outside,
            ))
            .iter()
            .any(|guard| outside.decide(guard) == Some(false))
        );
    }

    #[test]
    fn native_loaded_prefix_keeps_its_exact_legacy_producer_coordinates() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(16),
        };
        let memory = CMemory::new();
        super::super::symbolic_load_value(&memory, &cell, CType::Int32Pointer).unwrap();
        let Bitvector32Term::Variable(variable) = super::super::canonical_form_of_load(
            intern_c_memory_ref(&memory),
            cell,
            LoadKind::Bits32,
        ) else {
            panic!("exact pointer read");
        };
        let Some(Bitvector32Term::MemoryLoad(snapshot, cell, LoadKind::Bits32)) =
            crate::kernel::registered_load_term_for_variable(&variable)
        else {
            panic!("immutable read definition");
        };
        assert_eq!(
            crate::kernel::registered_load_bytes_for_variable(&variable),
            Some(8)
        );
        let pointer = CPointerValue::new(
            Pointer::loaded(cell.block.clone(), Bitvector32Term::Variable(variable), 4),
            CType::Int32Pointer,
        )
        .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            snapshot, *cell,
        )));
        let state = CState::new().with_memory(
            memory
                .with_native_input_span(
                    pointer.clone(),
                    CType::Int32,
                    IntegerTerm::constant_i64(2).into(),
                )
                .unwrap(),
        );
        let context = PureFactContext::new();
        assert_eq!(
            resolved_carrier(&state, &pointer, &context)
                .unwrap()
                .pointer(),
            pointer.pointer()
        );
        let next = pointer.clone().with_pointer(pointer.offset_by_bytes(4));
        assert!(
            conditions(checked_pointer_formation(
                &state,
                &pointer,
                next.pointer(),
                4,
                PointerDomainView::Typed,
                &context,
            ))
            .is_empty()
        );
        assert!(
            conditions(checked_pointer_access(
                &state,
                &next,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context,
            ))
            .is_empty()
        );
        let Some(PointerDesignation::Loaded(origin)) = pointer.designation() else {
            unreachable!()
        };
        let application_base = Pointer::loaded_value(origin.memory(), origin.address());
        let application = pointer
            .clone()
            .with_pointer(application_base.offset_by_bytes(4));
        assert!(
            conditions(checked_pointer_access(
                &state,
                &application,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context,
            ))
            .is_empty()
        );
        assert!(
            conditions(checked_pointer_formation(
                &state,
                &pointer,
                application.pointer(),
                4,
                PointerDomainView::Typed,
                &context,
            ))
            .is_empty()
        );
        // A prefix begins at its admitted position, which need not be the
        // unshifted opaque read. Keep that offset in both read spellings.
        let shifted_state = CState::new().with_memory(
            CMemory::new()
                .with_native_input_span(
                    next.clone(),
                    CType::Int32,
                    IntegerTerm::constant_i64(2).into(),
                )
                .unwrap(),
        );
        assert!(
            conditions(checked_pointer_access(
                &shifted_state,
                &application,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context,
            ))
            .is_empty()
        );
        let before = pointer.clone().with_pointer(application_base);
        assert!(
            conditions(checked_pointer_access(
                &shifted_state,
                &before,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context,
            ))
            .contains(&ConditionTerm::Constant(false))
        );
        let outside = pointer.clone().with_pointer(pointer.offset_by_bytes(8));
        assert!(
            conditions(checked_pointer_access(
                &state,
                &outside,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context,
            ))
            .contains(&ConditionTerm::Constant(false))
        );
        let forged = pointer
            .clone()
            .with_pointer(Pointer::symbolic(Variable(989_461)));
        let alias = context.clone().assume_condition(
            ConditionTerm::pointer_equal(forged.pointer().clone(), pointer.pointer().clone()),
            true,
        );
        assert_eq!(
            checked_pointer_access(
                &state,
                &forged,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &alias,
            ),
            Err(PointerDomainRefusal::UnresolvedDesignation)
        );
    }

    #[test]
    fn native_record_offsets_select_only_authenticated_prefix_elements() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            8,
            4,
            vec![
                CAggregateField::new("first", 0, CType::Int32),
                CAggregateField::new("second", 4, CType::Int32),
            ],
        ));
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(989_420)), CType::UInt8Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(989_420)));
        let state = CState::new().with_memory(
            CMemory::new()
                .with_native_record_prefix(
                    pointer.clone(),
                    layout.clone(),
                    IntegerTerm::constant_i64(2).into(),
                )
                .unwrap(),
        );
        let offset =
            |index, subtract, layout: Arc<CAggregateLayout>| CExpression::RecordPointerOffset {
                pointer: Box::new(CExpression::Value(CValue::Pointer(pointer.clone()))),
                index: Box::new(index),
                layout,
                subtract,
            };
        let evaluate = |expression: &CExpression, context: &PureFactContext| {
            let mut budget = ExecutionBudget::beside_live_state();
            evaluate_c_expression_paths(&state, expression, context, &mut budget).unwrap()
        };
        let at_one = offset(c_int32_literal(1), false, layout.clone());
        let field = CExpression::MemberAddress {
            object: Box::new(at_one),
            selection: Arc::new(CAggregateMemberSelection {
                layout: layout.clone(),
                path: Arc::from(["second".to_string()]),
                value_type: CType::Int32,
            }),
        };
        let paths = evaluate(&field, &PureFactContext::new());
        let [
            CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Pointer(selected)),
                ..
            },
        ] = paths.as_slice()
        else {
            panic!("selected second record field: {paths:?}");
        };
        assert_eq!(selected.pointer(), &pointer.pointer().offset_by_bytes(12));
        assert!(
            matches!(selected.designation(), Some(PointerDesignation::InputSelected { path, .. })
            if matches!(path.as_ref(), [PointerDomainSelection::Element(index), PointerDomainSelection::Member(name)]
                if index.as_ref() == &IntegerTerm::constant_i64(1) && name == "second"))
        );
        let wrong_layout = Arc::new(CAggregateLayout::new(
            8,
            4,
            vec![
                CAggregateField::new("different", 0, CType::Int32),
                CAggregateField::new("second", 4, CType::Int32),
            ],
        ));
        for expression in [
            offset(c_int32_literal(1), false, wrong_layout),
            offset(c_int32_literal(i32::MIN as u32), true, layout.clone()),
            offset(
                CExpression::Value(CValue::UInt32(Bitvector32Term::Constant(u32::MAX))),
                false,
                layout.clone(),
            ),
            c_pointer_offset_bytes(CExpression::Value(CValue::Pointer(pointer.clone())), 8),
            CExpression::MemberAddress {
                object: Box::new(offset(c_int32_literal(2), false, layout.clone())),
                selection: Arc::new(CAggregateMemberSelection {
                    layout: layout.clone(),
                    path: Arc::from(["first".to_string()]),
                    value_type: CType::Int32,
                }),
            },
        ] {
            assert!(
                evaluate(&expression, &PureFactContext::new())
                    .iter()
                    .all(|path| matches!(path.outcome, CExpressionOutcome::UndefinedBehavior(_))),
                "{expression:?}"
            );
        }
        // Address observation retains the unwrapped mathematical subtraction
        // while issuing no element or native-access evidence.
        let minimum = offset(c_int32_literal(i32::MIN as u32), true, layout);
        let paths = evaluate(
            &minimum,
            &PureFactContext::new().observe_pointer_addresses(),
        );
        let [
            CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Pointer(observed)),
                ..
            },
        ] = paths.as_slice()
        else {
            panic!("observed offset");
        };
        assert_eq!(
            observed.pointer(),
            &Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::add(
                    pointer.offset.clone(),
                    PointerOffsetTerm::Constant(17_179_869_184)
                ),
            }
        );
        assert!(observed.same_designation(&pointer));
    }

    #[test]
    fn symbolic_native_prefix_checks_allow_zero_without_executable_access() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(989_410)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(989_410)));
        let variable = Bitvector32Term::Variable(Variable(989_411));
        let count = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            variable.clone(),
        ));
        let state = CState::new().with_memory(
            CMemory::new()
                .with_native_input_span(pointer.clone(), CType::Int32, count.clone().into())
                .unwrap(),
        );
        let context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), variable.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    variable.clone(),
                    Bitvector32Term::Constant(u32::MAX / 4),
                ),
                true,
            );
        let guards = conditions(checked_pointer_span(
            &state,
            &pointer,
            IntegerTerm::constant_i64(0),
            count,
            4,
            PointerDomainView::Typed,
            &context,
        ));
        assert!(
            guards
                .iter()
                .all(|guard| context.decide(guard) == Some(true)),
            "{guards:?}"
        );
        let zero = context.assume_condition(
            ConditionTerm::equal(variable, Bitvector32Term::Constant(0)),
            true,
        );
        for guards in [
            conditions(checked_pointer_access(
                &state,
                &pointer,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &zero,
            )),
            conditions(checked_pointer_formation(
                &state,
                &pointer,
                pointer.pointer(),
                4,
                PointerDomainView::Typed,
                &zero,
            )),
        ] {
            assert!(
                guards.iter().any(|guard| zero.decide(guard) == Some(false)),
                "{guards:?}"
            );
        }
    }

    fn scalar_state() -> (CState, CPointerValue) {
        let address = CMemory::local_pointer("domain-query-scalar");
        let memory =
            CMemory::new().with_declared_scalar_block(address.block.clone(), 4, CType::Int32);
        let pointer = memory
            .declared_scalar_pointer(&address, CType::Int32)
            .unwrap();
        let mut state = CState::default();
        state.set_memory(memory);
        (state, pointer)
    }

    fn conditions(check: Result<PointerDomainCheck, PointerDomainRefusal>) -> Vec<ConditionTerm> {
        let PointerDomainCheck::Checked(guards) = check.unwrap() else {
            panic!("a declared object must use checked domain obligations")
        };
        guards
    }

    #[test]
    fn displacement_cancels_an_opaque_byte_prefix_before_unit_division() {
        let opaque = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(988_991))),
            byte_width: 4,
        };
        let pointer = |bytes| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(opaque.clone()),
                Box::new(PointerOffsetTerm::Constant(bytes)),
            ),
        };
        assert_eq!(
            exact_displacement(&pointer(16), &pointer(8), 8),
            Some(IntegerTerm::constant_i64(1))
        );
        assert_eq!(
            exact_displacement(&pointer(8), &pointer(16), 8),
            Some(IntegerTerm::constant_i64(-1))
        );
        assert_eq!(exact_displacement(&pointer(17), &pointer(8), 8), None);
        assert_eq!(
            exact_displacement(&pointer(i64::MAX), &pointer(i64::MIN), 1),
            Some(IntegerTerm::constant(
                num_bigint::BigInt::from(i64::MAX) - num_bigint::BigInt::from(i64::MIN)
            ))
        );
        let unmatched = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: opaque,
        };
        assert_eq!(
            exact_displacement(
                &unmatched,
                &Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(0)
                },
                8
            ),
            None
        );
    }

    #[test]
    fn symbolic_native_array_positions_use_exact_typed_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = CMemory::local_pointer("symbolic-position-array");
        let memory = CMemory::new()
            .with_declared_array_block(address.block.clone(), CType::Int32, 4)
            .unwrap();
        let object = memory
            .declared_array_pointer(&address, CType::Int32, 4)
            .unwrap();
        let state = CState::new().with_memory(memory);
        let variable = Bitvector32Term::Variable(Variable(988_220));
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let (nonnegative, below, equal, negative_values) = match ty {
                MachineIntegerType::Int32 => (
                    ConditionTerm::signed_less_equal(0u32.into(), variable.clone()),
                    ConditionTerm::signed_less_than(variable.clone(), 4u32.into()),
                    ConditionTerm::equal as fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm,
                    vec![
                        Bitvector32Term::Constant(u32::MAX),
                        Bitvector32Term::Constant(i32::MAX as u32),
                    ],
                ),
                MachineIntegerType::Int64 => (
                    ConditionTerm::int64_signed_less_equal(
                        Bitvector32Term::Int64Constant(0),
                        variable.clone(),
                    ),
                    ConditionTerm::int64_signed_less_than(
                        variable.clone(),
                        Bitvector32Term::Int64Constant(4),
                    ),
                    ConditionTerm::int64_equal
                        as fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm,
                    vec![
                        Bitvector32Term::Int64Constant(-1),
                        Bitvector32Term::Int64Constant(i64::MAX),
                    ],
                ),
                MachineIntegerType::UInt64 => (
                    ConditionTerm::Constant(true),
                    ConditionTerm::uint64_less_than(
                        variable.clone(),
                        Bitvector32Term::UInt64Constant(4),
                    ),
                    ConditionTerm::uint64_equal
                        as fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm,
                    vec![
                        Bitvector32Term::UInt64Constant(u64::MAX),
                        Bitvector32Term::UInt64Constant(1u64 << 32),
                    ],
                ),
                _ => unreachable!(),
            };
            let selected = object
                .clone()
                .with_pointer(object.pointer().offset_by_typed_elements(
                    variable.clone(),
                    4,
                    ty == MachineIntegerType::UInt64,
                    ty != MachineIntegerType::Int32,
                ));
            let assumptions = PureFactContext::new()
                .assume_condition(nonnegative, true)
                .assume_condition(below, true);
            for guards in [
                conditions(checked_pointer_formation(
                    &state,
                    &object,
                    selected.pointer(),
                    4,
                    PointerDomainView::Typed,
                    &assumptions,
                )),
                conditions(checked_pointer_access(
                    &state,
                    &selected,
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &assumptions,
                )),
            ] {
                assert!(
                    guards
                        .iter()
                        .all(|guard| assumptions.decide(guard) == Some(true)),
                    "{ty:?}: {guards:?}"
                );
            }
            for value in negative_values {
                let assumptions =
                    PureFactContext::new().assume_condition(equal(variable.clone(), value), true);
                let guards = conditions(checked_pointer_formation(
                    &state,
                    &object,
                    selected.pointer(),
                    4,
                    PointerDomainView::Typed,
                    &assumptions,
                ));
                assert!(
                    guards
                        .iter()
                        .any(|guard| assumptions.decide(guard) == Some(false)),
                    "{ty:?}: {guards:?}"
                );
            }
        }
    }

    #[test]
    fn native_domain_order_bridge_preserves_format_extremes_without_wrapping() {
        for (ty, minimum, maximum) in [
            (
                MachineIntegerType::Int32,
                i128::from(i32::MIN),
                i128::from(i32::MAX),
            ),
            (MachineIntegerType::UInt32, 0, i128::from(u32::MAX)),
            (
                MachineIntegerType::Int64,
                i128::from(i64::MIN),
                i128::from(i64::MAX),
            ),
            (MachineIntegerType::UInt64, 0, i128::from(u64::MAX)),
        ] {
            for value in [minimum, minimum + 1, maximum - 1, maximum] {
                let bits = match ty {
                    MachineIntegerType::Int32 => Bitvector32Term::Constant(value as i32 as u32),
                    MachineIntegerType::UInt32 => Bitvector32Term::Constant(value as u32),
                    MachineIntegerType::Int64 => Bitvector32Term::Int64Constant(value as i64),
                    MachineIntegerType::UInt64 => Bitvector32Term::UInt64Constant(value as u64),
                    _ => unreachable!(),
                };
                let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(ty, bits));
                for bound in [
                    minimum - 1,
                    minimum,
                    minimum + 1,
                    maximum - 1,
                    maximum,
                    maximum + 1,
                ] {
                    let bound_term = IntegerTerm::constant(num_bigint::BigInt::from(bound));
                    for strict in [false, true] {
                        assert_eq!(
                            machine_constant_order(&observed, &bound_term, strict),
                            Some(ConditionTerm::Constant(if strict {
                                value < bound
                            } else {
                                value <= bound
                            }))
                        );
                        assert_eq!(
                            machine_constant_order(&bound_term, &observed, strict),
                            Some(ConditionTerm::Constant(if strict {
                                bound < value
                            } else {
                                bound <= value
                            }))
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn native_successor_order_guards_use_mathematical_offsets_without_wrap() {
        let _session = crate::kernel::VerificationSession::enter();
        for (ty, minimum, maximum) in [
            (
                MachineIntegerType::Int32,
                i128::from(i32::MIN),
                i128::from(i32::MAX),
            ),
            (MachineIntegerType::UInt32, 0, i128::from(u32::MAX)),
            (
                MachineIntegerType::Int64,
                i128::from(i64::MIN),
                i128::from(i64::MAX),
            ),
            (MachineIntegerType::UInt64, 0, i128::from(u64::MAX)),
        ] {
            let observe = |value: i128| {
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    ty,
                    match ty {
                        MachineIntegerType::Int32 => Bitvector32Term::Constant(value as i32 as u32),
                        MachineIntegerType::UInt32 => Bitvector32Term::Constant(value as u32),
                        MachineIntegerType::Int64 => Bitvector32Term::Int64Constant(value as i64),
                        MachineIntegerType::UInt64 => Bitvector32Term::UInt64Constant(value as u64),
                        _ => unreachable!(),
                    },
                ))
            };
            for value in [minimum, 0, maximum] {
                for offset in [-1, 1] {
                    let shifted = domain_add(observe(value), IntegerTerm::constant_i64(offset));
                    let mathematical = value + i128::from(offset);
                    for bound in [minimum - 1, minimum, 0, maximum, maximum + 1] {
                        let bound_term = IntegerTerm::constant(bound.into());
                        for (condition, expected) in [
                            (
                                domain_less_equal(shifted.clone(), bound_term.clone()),
                                mathematical <= bound,
                            ),
                            (
                                domain_less_than(shifted.clone(), bound_term.clone()),
                                mathematical < bound,
                            ),
                            (
                                domain_less_equal(bound_term.clone(), shifted.clone()),
                                bound <= mathematical,
                            ),
                            (
                                domain_less_than(bound_term, shifted.clone()),
                                bound < mathematical,
                            ),
                        ] {
                            assert_eq!(
                                PureFactContext::new().decide(&condition),
                                Some(expected),
                                "{ty:?} value={value} offset={offset} bound={bound}: {condition:?}"
                            );
                        }
                    }
                    if offset == 1 {
                        let guard = domain_less_equal(shifted, observe(maximum));
                        assert_eq!(PureFactContext::new().decide(&guard), Some(value < maximum));
                    }
                }
            }
        }
        let x = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(Variable(998_570)),
        ));
        let y = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(Variable(998_571)),
        ));
        let context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(
                    Bitvector32Term::Variable(Variable(998_570)),
                    Bitvector32Term::Constant(0),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(Variable(998_570)),
                    Bitvector32Term::Variable(Variable(998_571)),
                ),
                true,
            );
        let successor = domain_add(x.clone(), IntegerTerm::constant_i64(1));
        for guard in [
            domain_less_equal(IntegerTerm::constant_i64(0), successor.clone()),
            domain_less_equal(successor.clone(), y.clone()),
        ] {
            assert_eq!(context.decide(&guard), Some(true), "{guard:?}");
        }
        let mixed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            Bitvector32Term::Variable(Variable(998_571)),
        ));
        assert!(matches!(
            domain_less_equal(successor, mixed),
            ConditionTerm::IntegerLessEqual(..)
        ));
        assert!(matches!(
            domain_less_equal(domain_add(x, y), IntegerTerm::constant_i64(0)),
            ConditionTerm::IntegerLessEqual(..)
        ));
    }

    fn paired_read(memory: &CMemory, cell: &Pointer) -> CPointerValue {
        let snapshot = intern_c_memory_ref(memory);
        CPointerValue::new(Pointer::loaded_value(&snapshot, cell), CType::Int32Pointer)
            .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
                snapshot,
                cell.clone(),
            )))
    }

    #[test]
    fn loaded_domain_checks_recover_only_complete_paired_carriers() {
        let _session = crate::kernel::VerificationSession::enter();
        let (mut state, object) = scalar_state();
        let cell = CMemory::local_pointer("domain-pointer-slot");
        let stored = state
            .memory()
            .clone()
            .with_block(cell.block.clone(), 32)
            .store(cell.clone(), CValue::Pointer(object.clone()));
        let framed = stored.clone().store(
            cell.offset_by_bytes(16),
            CValue::Int32(Bitvector32Term::Constant(7)),
        );
        state.set_memory(framed.clone());
        let context = PureFactContext::new();
        let read = paired_read(&framed, &cell)
            .with_pointee_constant(true)
            .with_pointee_volatile(true);
        let resolved =
            crate::kernel::memory_provenance::resolve_loaded_pointer_carrier(&read, &context)
                .unwrap();
        assert_eq!(resolved.pointer(), object.pointer());
        assert!(resolved.same_designation(&object));
        assert!(resolved.pointee_constant() && resolved.pointee_volatile());
        assert!(
            conditions(checked_pointer_access(
                &state,
                &read,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ))
            .is_empty()
        );
        let one_past = read.clone().with_pointer(read.offset_by_bytes(4));
        assert!(
            conditions(checked_pointer_formation(
                &state,
                &read,
                one_past.pointer(),
                4,
                PointerDomainView::Typed,
                &context
            ))
            .is_empty()
        );
        assert!(
            conditions(checked_pointer_access(
                &state,
                &one_past,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ))
            .contains(&ConditionTerm::Constant(false))
        );
        assert!(
            conditions(checked_pointer_difference(
                &state,
                &read,
                &one_past,
                4,
                PointerDomainView::Typed,
                &context
            ))
            .is_empty()
        );
        let copied = framed
            .clone()
            .store(cell.offset_by_bytes(8), CValue::Pointer(read.clone()));
        state.set_memory(copied.clone());
        assert!(
            conditions(checked_pointer_access(
                &state,
                &paired_read(&copied, &cell.offset_by_bytes(8)),
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ))
            .is_empty()
        );
        let forged = read.clone().with_pointer(object.pointer().clone());
        assert_eq!(
            checked_pointer_access(
                &state,
                &forged,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ),
            Err(PointerDomainRefusal::UnresolvedDesignation)
        );
        let mismatched = read
            .clone()
            .with_pointer(paired_read(&stored, &cell).into_pointer());
        assert_eq!(
            checked_pointer_access(
                &state,
                &mismatched,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ),
            Err(PointerDomainRefusal::UnresolvedDesignation)
        );
        for value in [
            CValue::UInt8(Bitvector32Term::Constant(0)),
            CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
        ] {
            let altered = framed.clone().store(cell.clone(), value);
            state.set_memory(altered.clone());
            assert_eq!(
                checked_pointer_access(
                    &state,
                    &paired_read(&altered, &cell),
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &context
                ),
                Err(PointerDomainRefusal::UnresolvedDesignation)
            );
        }
        let unknown = framed.with_storage_memory_havoc(
            Variable(987_900),
            &[CMemoryRange::new(cell.clone(), 0u32.into(), 8u32.into())],
            &context,
        );
        state.set_memory(unknown.clone());
        assert_eq!(
            checked_pointer_access(
                &state,
                &paired_read(&unknown, &cell),
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ),
            Err(PointerDomainRefusal::UnresolvedDesignation)
        );
    }

    #[test]
    fn loaded_domain_checks_require_exact_registered_width_and_origin() {
        let _session = crate::kernel::VerificationSession::enter();
        let (mut state, object) = scalar_state();
        let cell = CMemory::local_pointer("domain-registered-slot");
        let memory = state
            .memory()
            .clone()
            .with_block(cell.block.clone(), 24)
            .store(cell.clone(), CValue::Pointer(object.clone()))
            .store(cell.offset_by_bytes(8), CValue::Pointer(object));
        state.set_memory(memory.clone());
        let snapshot = intern_c_memory_ref(&memory);
        let variable = load_variable_for_exact_cell(&snapshot, &cell, LoadKind::Bits32, 8);
        let origin = PointerLoadIdentity::new(snapshot.clone(), cell.clone());
        let context = PureFactContext::new();
        let symbolic = CPointerValue::new(Pointer::symbolic(variable), CType::Int32Pointer)
            .with_designation(PointerDesignation::Loaded(origin.clone()));
        let legacy = symbolic.clone().with_pointer(Pointer::loaded(
            cell.block.clone(),
            Bitvector32Term::Variable(variable),
            4,
        ));
        for value in [&symbolic, &legacy] {
            assert!(
                conditions(checked_pointer_access(
                    &state,
                    value,
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &context
                ))
                .is_empty()
            );
        }
        let bad_scale = legacy.clone().with_pointer(Pointer::loaded(
            cell.block.clone(),
            Bitvector32Term::Variable(variable),
            8,
        ));
        let duplicate = legacy.clone().with_pointer(Pointer {
            block: cell.block.clone(),
            offset: PointerOffsetTerm::Add(
                Box::new(legacy.pointer().offset.clone()),
                Box::new(legacy.pointer().offset.clone()),
            ),
        });
        let narrow =
            load_variable_for_exact_cell(&snapshot, &cell.offset_by_bytes(8), LoadKind::Bits32, 4);
        let narrow = CPointerValue::new(Pointer::symbolic(narrow), CType::Int32Pointer)
            .with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
                snapshot,
                cell.offset_by_bytes(8),
            )));
        for value in [bad_scale, duplicate, narrow] {
            assert_eq!(
                checked_pointer_access(
                    &state,
                    &value,
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &context
                ),
                Err(PointerDomainRefusal::UnresolvedDesignation)
            );
        }
    }

    #[test]
    fn domain_address_alignment_never_changes_selected_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, object) = scalar_state();
        let raw = Pointer::symbolic(Variable(987_901));
        let alias = object.clone().with_pointer(raw.clone());
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(raw.clone(), object.pointer().clone()),
            true,
        );
        assert!(
            conditions(checked_pointer_access(
                &state,
                &alias,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ))
            .is_empty()
        );
        let one_past = object.clone().with_pointer(raw.clone());
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(raw, object.offset_by_bytes(4)),
            true,
        );
        assert!(
            conditions(checked_pointer_access(
                &state,
                &one_past,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &context
            ))
            .contains(&ConditionTerm::Constant(false))
        );
        assert!(
            conditions(checked_pointer_formation(
                &state,
                &object,
                one_past.pointer(),
                4,
                PointerDomainView::Typed,
                &context
            ))
            .is_empty()
        );
    }

    #[test]
    fn checked_member_ordering_requires_actual_sibling_bases() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = std::sync::Arc::new(CAggregateLayout::new(
            8,
            4,
            vec![
                CAggregateField::new("first", 0, CType::Int32),
                CAggregateField::new("second", 4, CType::Int32),
            ],
        ));
        let root = CMemory::local_pointer("domain-query-record");
        let memory = CMemory::new().with_declared_aggregate_block(root.block.clone(), &layout);
        let object = memory.declared_aggregate_pointer(&root, &layout).unwrap();
        let select = |name: &str| {
            memory
                .checked_member_pointer(
                    &object,
                    &CAggregateMemberSelection {
                        layout: layout.clone(),
                        path: vec![name.into()].into(),
                        value_type: CType::Int32,
                    },
                )
                .unwrap()
        };
        let first = select("first");
        let second = select("second");
        let mut state = CState::default();
        state.set_memory(memory);
        let context = PureFactContext::new();
        for (left, right) in [(&first, &second), (&second, &first)] {
            assert!(
                conditions(checked_pointer_ordering(
                    &state,
                    left,
                    right,
                    4,
                    PointerDomainView::Typed,
                    true,
                    &context
                ))
                .is_empty()
            );
            assert_eq!(
                checked_pointer_ordering(
                    &state,
                    left,
                    right,
                    4,
                    PointerDomainView::Typed,
                    false,
                    &context
                ),
                Err(PointerDomainRefusal::IncompatibleDomain)
            );
            assert_eq!(
                checked_pointer_difference(
                    &state,
                    left,
                    right,
                    4,
                    PointerDomainView::Typed,
                    &context
                ),
                Err(PointerDomainRefusal::IncompatibleDomain)
            );
        }
        let one_past = first.clone().with_pointer(first.offset_by_bytes(4));
        assert_eq!(one_past.pointer(), second.pointer());
        assert!(
            conditions(checked_pointer_ordering(
                &state,
                &one_past,
                &second,
                4,
                PointerDomainView::Typed,
                true,
                &context
            ))
            .contains(&ConditionTerm::Constant(false))
        );
        assert!(
            conditions(checked_pointer_byte_formation(
                &state,
                &first,
                &first.offset_by_bytes(1),
                &context
            ))
            .is_empty()
        );
        assert!(
            conditions(checked_pointer_byte_formation(
                &state,
                &first,
                &first.offset_by_bytes(5),
                &context
            ))
            .contains(&ConditionTerm::Constant(false))
        );
    }

    #[test]
    fn loaded_domain_queries_ignore_unrelated_memory() {
        let mut samples = Vec::new();
        for unrelated in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let (mut state, object) = scalar_state();
            let cell = CMemory::local_pointer("domain-query-read-cell");
            let mut memory = state.memory().clone().with_block(cell.block.clone(), 8);
            for id in 0..unrelated {
                memory = memory.with_block(format!("unrelated-loaded-domain-{id}"), 4);
            }
            let memory = memory.store(cell.clone(), CValue::Pointer(object));
            let read = paired_read(&memory, &cell);
            state.set_memory(memory);
            let (check, work) = crate::instrumentation::measure_deterministic_work(|| {
                checked_pointer_access(
                    &state,
                    &read,
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &PureFactContext::new(),
                )
            });
            assert!(conditions(check).is_empty());
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "selected loaded domain work grew with unrelated memory: {samples:?}"
        );
    }

    #[test]
    fn loaded_carrier_resolution_scales_with_selected_copy_chain() {
        let mut samples = Vec::new();
        for copies in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let (state, object) = scalar_state();
            let cell = CMemory::local_pointer("domain-copy-chain-cell");
            let mut memory = state
                .memory()
                .clone()
                .with_block(cell.block.clone(), 8)
                .store(cell.clone(), CValue::Pointer(object.clone()));
            for index in 0..copies {
                let read = paired_read(&memory, &cell);
                let address = Pointer {
                    block: read.pointer().block.clone(),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: Box::new(Bitvector32Term::Variable(Variable(988_000 + index))),
                        byte_width: 4,
                    },
                };
                memory = memory.store(cell.clone(), CValue::Pointer(read.with_pointer(address)));
            }
            let read = paired_read(&memory, &cell);
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::memory_provenance::resolve_loaded_pointer_carrier(
                    &read,
                    &PureFactContext::new(),
                )
            });
            let resolved = resolved.unwrap();
            assert!(resolved.same_designation(&object));
            let mut selected = vec![&resolved.pointer().offset];
            let mut terms = 0;
            while let Some(offset) = selected.pop() {
                match offset {
                    PointerOffsetTerm::Add(left, right) => {
                        selected.push(left);
                        selected.push(right);
                    }
                    PointerOffsetTerm::Int32Scaled { .. } => terms += 1,
                    _ => panic!("the selected copy chain must retain exact observed displacements"),
                }
            }
            assert_eq!(terms, copies);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 5),
            "selected copy-chain work grew faster than its fourfold increase: {samples:?}"
        );
    }

    #[test]
    fn scalar_domain_checks_both_formation_positions_and_full_access() {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, pointer) = scalar_state();
        let assumptions = PureFactContext::new();
        let one_past = pointer.clone().with_pointer(pointer.offset_by_bytes(4));
        let outside = pointer.clone().with_pointer(pointer.offset_by_bytes(8));
        for (origin, result) in [
            (&pointer, one_past.pointer()),
            (&one_past, pointer.pointer()),
        ] {
            assert!(
                conditions(checked_pointer_formation(
                    &state,
                    origin,
                    result,
                    4,
                    PointerDomainView::Typed,
                    &assumptions,
                ))
                .is_empty()
            );
        }
        for (origin, result) in [(&pointer, outside.pointer()), (&outside, pointer.pointer())] {
            assert!(
                conditions(checked_pointer_formation(
                    &state,
                    origin,
                    result,
                    4,
                    PointerDomainView::Typed,
                    &assumptions,
                ))
                .contains(&ConditionTerm::Constant(false))
            );
        }
        assert!(
            conditions(checked_pointer_access(
                &state,
                &pointer,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ))
            .is_empty()
        );
        assert!(
            conditions(checked_pointer_access(
                &state,
                &one_past,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ))
            .contains(&ConditionTerm::Constant(false))
        );
        assert_eq!(
            checked_pointer_access(
                &state,
                &pointer,
                CType::Int64,
                8,
                PointerDomainView::Typed,
                &assumptions,
            ),
            Err(PointerDomainRefusal::IncompatibleType)
        );
        assert_eq!(
            checked_pointer_access(
                &state,
                &pointer,
                CType::Int32,
                8,
                PointerDomainView::Typed,
                &assumptions,
            ),
            Err(PointerDomainRefusal::InvalidAccessWidth)
        );
        let misaligned = pointer.clone().with_pointer(pointer.offset_by_bytes(1));
        assert!(
            conditions(checked_pointer_access(
                &state,
                &misaligned,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ))
            .contains(&ConditionTerm::Constant(false))
        );
        assert_eq!(
            checked_pointer_access(
                &state,
                &pointer,
                CType::UInt8,
                1,
                PointerDomainView::Typed,
                &assumptions,
            ),
            Err(PointerDomainRefusal::IncompatibleType)
        );
        let last_byte = pointer.clone().with_pointer(pointer.offset_by_bytes(3));
        assert!(
            conditions(checked_pointer_access(
                &state,
                &last_byte,
                CType::UInt8,
                1,
                PointerDomainView::ObjectRepresentationBytes,
                &assumptions,
            ))
            .is_empty()
        );
        assert!(
            conditions(checked_pointer_access(
                &state,
                &one_past,
                CType::UInt8,
                1,
                PointerDomainView::ObjectRepresentationBytes,
                &assumptions,
            ))
            .contains(&ConditionTerm::Constant(false))
        );
    }

    #[test]
    fn domain_checks_distinguish_legacy_unresolved_and_forged_descriptors() {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, pointer) = scalar_state();
        let assumptions = PureFactContext::new();
        let legacy = CPointerValue::new(pointer.pointer().clone(), pointer.c_type());
        assert_eq!(
            checked_pointer_access(
                &state,
                &legacy,
                CType::Int32,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ),
            Ok(PointerDomainCheck::Legacy)
        );
        let unresolved = legacy
            .clone()
            .with_designation(PointerDesignation::Unresolved(Variable(9_899_010)));
        let loaded = legacy.with_designation(PointerDesignation::Loaded(PointerLoadIdentity::new(
            intern_c_memory(state.memory().clone()),
            CMemory::local_pointer("unknown-pointer-cell"),
        )));
        for unknown in [unresolved, loaded] {
            assert_eq!(
                checked_pointer_access(
                    &state,
                    &unknown,
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &assumptions,
                ),
                Err(PointerDomainRefusal::UnresolvedDesignation)
            );
        }
        let descriptor = |root, base, stride, count| PointerDesignation::Object {
            root,
            base,
            path: std::sync::Arc::from([]),
            element_type: CType::Int32,
            stride,
            count: IntegerTerm::constant_i64(count).into(),
        };
        for forged in [
            descriptor(pointer.pointer().clone(), pointer.pointer().clone(), 4, 2),
            descriptor(pointer.pointer().clone(), pointer.pointer().clone(), 8, 1),
            descriptor(pointer.pointer().clone(), pointer.offset_by_bytes(4), 4, 1),
            descriptor(
                CMemory::local_pointer("wrong-root"),
                pointer.pointer().clone(),
                4,
                1,
            ),
        ] {
            let forged = pointer.clone().with_designation(forged);
            assert_eq!(
                checked_pointer_access(
                    &state,
                    &forged,
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &assumptions,
                ),
                Err(PointerDomainRefusal::UnauthenticatedDomain)
            );
        }
    }

    #[test]
    fn domain_positions_observe_scaling_outside_modular_machine_sums() {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, pointer) = scalar_state();
        let assumptions = PureFactContext::new();
        let minimum = Bitvector32Term::Constant(i32::MIN as u32);
        let wrapped =
            pointer.offset_by_elements(Bitvector32Term::add(minimum.clone(), minimum.clone()), 4);
        let exact = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(minimum.clone()),
                    byte_width: 4,
                }),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(minimum),
                    byte_width: 4,
                }),
            ),
        };
        assert!(
            conditions(checked_pointer_formation(
                &state,
                &pointer,
                &wrapped,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ))
            .is_empty()
        );
        assert!(
            conditions(checked_pointer_formation(
                &state,
                &pointer,
                &exact,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ))
            .contains(&ConditionTerm::Constant(false))
        );
    }

    #[test]
    fn pointer_difference_requires_matching_complete_domains() {
        let _session = crate::kernel::VerificationSession::enter();
        let (mut state, pointer) = scalar_state();
        let assumptions = PureFactContext::new();
        let one_past = pointer.clone().with_pointer(pointer.offset_by_bytes(4));
        assert!(
            conditions(checked_pointer_difference(
                &state,
                &pointer,
                &one_past,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ))
            .is_empty()
        );
        let legacy = CPointerValue::new(pointer.pointer().clone(), pointer.c_type());
        assert_eq!(
            checked_pointer_difference(
                &state,
                &pointer,
                &legacy,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ),
            Err(PointerDomainRefusal::IncompatibleDomain)
        );
        let other_address = CMemory::local_pointer("different-scalar");
        let memory = state.memory().clone().with_declared_scalar_block(
            other_address.block.clone(),
            4,
            CType::Int32,
        );
        let other = memory
            .declared_scalar_pointer(&other_address, CType::Int32)
            .unwrap();
        state.set_memory(memory);
        assert_eq!(
            checked_pointer_difference(
                &state,
                &pointer,
                &other,
                4,
                PointerDomainView::Typed,
                &assumptions,
            ),
            Err(PointerDomainRefusal::IncompatibleDomain)
        );
    }

    #[test]
    fn checked_scalar_spans_allow_empty_one_past_but_never_extend_the_domain() {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, pointer) = scalar_state();
        let assumptions = PureFactContext::new();
        let span = |pointer: &CPointerValue, start, end| {
            conditions(checked_pointer_span(
                &state,
                pointer,
                IntegerTerm::constant_i64(start),
                IntegerTerm::constant_i64(end),
                4,
                PointerDomainView::Typed,
                &assumptions,
            ))
        };
        assert!(span(&pointer, 0, 1).is_empty());
        let one_past = pointer.clone().with_pointer(pointer.offset_by_bytes(4));
        assert!(span(&one_past, 0, 0).is_empty());
        assert!(span(&one_past, 0, 1).contains(&ConditionTerm::Constant(false)));
        assert!(span(&pointer, 0, 2).contains(&ConditionTerm::Constant(false)));
        assert!(span(&pointer, 1, 0).contains(&ConditionTerm::Constant(false)));
        assert!(span(&pointer, -1, 0).contains(&ConditionTerm::Constant(false)));
        let outside = pointer.clone().with_pointer(pointer.offset_by_bytes(8));
        assert!(span(&outside, 0, 0).contains(&ConditionTerm::Constant(false)));
    }

    #[test]
    fn native_constant_domain_queries_have_fixed_work_across_array_extents() {
        let mut samples = Vec::new();
        for count in [8, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let address = CMemory::local_pointer("native-domain-array");
            let memory = CMemory::new()
                .with_declared_array_block(address.block.clone(), CType::Int32, count)
                .unwrap();
            let pointer = memory
                .declared_array_pointer(&address, CType::Int32, count)
                .unwrap();
            let last = pointer
                .clone()
                .with_pointer(address.offset_by_bytes((count - 1) * 4));
            let one_past = pointer
                .clone()
                .with_pointer(address.offset_by_bytes(count * 4));
            let mut state = CState::default();
            state.set_memory(memory);
            let assumptions = PureFactContext::new();
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    conditions(checked_pointer_formation(
                        &state,
                        &pointer,
                        last.pointer(),
                        4,
                        PointerDomainView::Typed,
                        &assumptions,
                    ))
                    .is_empty()
                );
                assert!(
                    conditions(checked_pointer_access(
                        &state,
                        &last,
                        CType::Int32,
                        4,
                        PointerDomainView::Typed,
                        &assumptions,
                    ))
                    .is_empty()
                );
                assert!(
                    conditions(checked_pointer_access(
                        &state,
                        &one_past,
                        CType::Int32,
                        4,
                        PointerDomainView::Typed,
                        &assumptions,
                    ))
                    .contains(&ConditionTerm::Constant(false))
                );
            });
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }

    #[test]
    fn native_domain_arithmetic_retains_exact_overflow_and_large_integer_work() {
        assert_eq!(
            domain_add(
                IntegerTerm::constant_i64(i64::MAX),
                IntegerTerm::constant_i64(1)
            )
            .as_const(),
            Some(&(num_bigint::BigInt::from(i64::MAX) + 1)),
        );
        assert_eq!(
            domain_subtract(
                IntegerTerm::constant_i64(i64::MIN),
                IntegerTerm::constant_i64(1)
            )
            .as_const(),
            Some(&(num_bigint::BigInt::from(i64::MIN) - 1)),
        );
        let mut samples = Vec::new();
        for bits in [128, 256, 512] {
            let magnitude = num_bigint::BigInt::from(1) << (bits as usize);
            let left = IntegerTerm::constant(magnitude.clone());
            let right = IntegerTerm::constant(magnitude.clone());
            let (product, work) =
                crate::instrumentation::measure_deterministic_work(|| domain_multiply(left, right));
            assert_eq!(product.as_const(), Some(&(&magnitude * &magnitude)));
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] < pair[1]),
            "{samples:?}"
        );
    }

    #[test]
    fn checked_scalar_domain_queries_ignore_unrelated_memory() {
        let mut samples = Vec::new();
        for unrelated in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let (mut state, pointer) = scalar_state();
            let mut memory = state.memory().clone();
            for id in 0..unrelated {
                memory = memory.with_block(format!("unrelated-domain-{id}"), 4);
            }
            state.set_memory(memory);
            let (check, work) = crate::instrumentation::measure_deterministic_work(|| {
                checked_pointer_access(
                    &state,
                    &pointer,
                    CType::Int32,
                    4,
                    PointerDomainView::Typed,
                    &PureFactContext::new(),
                )
            });
            assert!(conditions(check).is_empty());
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "selected domain work grew with unrelated memory: {samples:?}"
        );
    }
}
