use super::*;
use crate::kernel::{CComparisonOperator, CFloatBinaryOperator, CFloatCondition};
use std::fmt::Write;

const MAX_DIAGNOSTIC_ITEMS: usize = 12;
const DEBUG_VALUE_BYTE_LIMIT: usize = 2 * 1024;
const TRUNCATION_SUFFIX: &str =
    "\n… <diagnostic truncated; set CLICK_FULL_DIAGNOSTICS=1 for full internal state>";

pub(super) fn bound_error_message(message: String) -> String {
    bound_error_message_for_mode(message, std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some())
}

pub(super) fn bound_error_message_for_mode(message: String, full_internal_state: bool) -> String {
    if full_internal_state || message.len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT {
        return message;
    }
    truncate_utf8_with_suffix(&message, DEFAULT_DIAGNOSTIC_BYTE_LIMIT, TRUNCATION_SUFFIX)
}

fn truncate_utf8_with_suffix(message: &str, limit: usize, suffix: &str) -> String {
    if message.len() <= limit {
        return message.to_string();
    }
    let content_limit = limit.saturating_sub(suffix.len());
    let mut boundary = content_limit.min(message.len());
    while !message.is_char_boundary(boundary) {
        boundary -= 1;
    }
    let mut bounded = String::with_capacity(boundary + suffix.len());
    bounded.push_str(&message[..boundary]);
    bounded.push_str(suffix);
    bounded
}

struct BoundedDebugWriter {
    output: String,
    content_limit: usize,
}

impl Write for BoundedDebugWriter {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        let remaining = self.content_limit.saturating_sub(self.output.len());
        if value.len() <= remaining {
            self.output.push_str(value);
            return Ok(());
        }
        let mut boundary = remaining.min(value.len());
        while !value.is_char_boundary(boundary) {
            boundary -= 1;
        }
        self.output.push_str(&value[..boundary]);
        Err(fmt::Error)
    }
}

pub(super) fn bounded_debug(value: &impl fmt::Debug) -> String {
    bounded_debug_for_mode(value, std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some())
}

pub(super) fn bounded_debug_for_mode(value: &impl fmt::Debug, full_internal_state: bool) -> String {
    if full_internal_state {
        return format!("{value:?}");
    }
    let content_limit = DEBUG_VALUE_BYTE_LIMIT.saturating_sub(TRUNCATION_SUFFIX.len());
    let mut writer = BoundedDebugWriter {
        output: String::with_capacity(DEBUG_VALUE_BYTE_LIMIT),
        content_limit,
    };
    if write!(&mut writer, "{value:?}").is_err() {
        writer.output.push_str(TRUNCATION_SUFFIX);
    }
    writer.output
}

fn describe_bounded_list<T>(items: &[T], mut describe: impl FnMut(&T) -> String) -> String {
    if items.is_empty() {
        return "[]".to_string();
    }
    let item_limit = diagnostic_item_limit();
    let mut entries = items
        .iter()
        .take(item_limit)
        .map(&mut describe)
        .collect::<Vec<_>>();
    if items.len() > item_limit {
        entries.push(format!("… {} more omitted", items.len() - item_limit));
    }
    format!("[{}]", entries.join(", "))
}

fn diagnostic_item_limit() -> usize {
    if std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some() {
        usize::MAX
    } else {
        MAX_DIAGNOSTIC_ITEMS
    }
}

fn describe_context_pure_and_execution_facts(
    pure_facts: &[Proposition],
    execution_pure_facts: &[ExecutionPureFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let total = pure_facts.len() + execution_pure_facts.len();
    if total == 0 {
        return "[]".to_string();
    }
    let item_limit = diagnostic_item_limit();
    let mut entries = pure_facts
        .iter()
        .chain(
            execution_pure_facts
                .iter()
                .map(ExecutionPureFact::proposition),
        )
        .take(item_limit)
        .map(|fact| describe_pure_fact(fact, parameters, arguments))
        .collect::<Vec<_>>();
    if total > item_limit {
        entries.push(format!("… {} more omitted", total - item_limit));
    }
    format!("[{}]", entries.join(", "))
}

pub(super) fn describe_pure_facts(pure_facts: &[Proposition]) -> String {
    if pure_facts.is_empty() {
        return "[]".to_string();
    }

    describe_bounded_list(pure_facts, |fact| describe_pure_fact(fact, &[], &[]))
}

pub(super) fn describe_unexpressed_pure_facts(
    facts: &[(Proposition, ClickError)],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    describe_bounded_list(facts, |(fact, error)| {
        format!(
            "{}: {}",
            describe_pure_fact(fact, parameters, arguments),
            error.message()
        )
    })
}

pub(super) fn describe_pure_fact(
    fact: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match fact {
        Proposition::CMemoryLoadable { base, bytes, .. } => format!(
            "loadable(base={}, bytes={})",
            describe_pointer(base, parameters, arguments),
            describe_bitvector_with_context(bytes, parameters, arguments)
        ),
        Proposition::CResourceSeparate { left, right } => format!(
            "separate({}, {})",
            describe_c_resource(left, parameters, arguments),
            describe_c_resource(right, parameters, arguments)
        ),
        Proposition::CResourceContains { parent, child } => format!(
            "contains({}, {})",
            describe_c_resource(parent, parameters, arguments),
            describe_c_resource(child, parameters, arguments)
        ),
        Proposition::CMemoryMutatesOnly { pointers, .. } => format!(
            "memory mutates only at {}",
            describe_bounded_list(pointers, |pointer| {
                describe_pointer(pointer, parameters, arguments)
            })
        ),
        Proposition::CMemoryEffectSummary { mutable_ranges, .. } => format!(
            "memory effect ranges {}",
            describe_bounded_list(mutable_ranges, |range| {
                describe_memory_range(range, parameters, arguments)
            })
        ),
        Proposition::CHeapAllocationFreed {
            allocation_base,
            bytes,
            ..
        } => format!(
            "freed heap allocation {} ({} bytes)",
            describe_pointer(allocation_base, parameters, arguments),
            describe_bitvector_with_context(bytes, parameters, arguments)
        ),
        Proposition::ForAll { sort, .. } => {
            format!("universal proposition over {sort:?}")
        }
        Proposition::Exists { sort, .. } => {
            format!("existential proposition over {sort:?}")
        }
        Proposition::ConditionIs(condition, value) => {
            let kind = match condition {
                ConditionTerm::Bitvector32SignedLessThan(_, _) => "signed less-than",
                ConditionTerm::Bitvector32SignedLessEqual(_, _) => "signed less-or-equal",
                ConditionTerm::Bitvector32SignedGreaterThan(_, _) => "signed greater-than",
                ConditionTerm::Bitvector32SignedGreaterEqual(_, _) => "signed greater-or-equal",
                ConditionTerm::Bitvector32Equal(_, _) => "int32 equality",
                ConditionTerm::Bitvector32SignedAddOverflows(_, _) => "addition overflow",
                ConditionTerm::Bitvector32SignedSubtractOverflows(_, _) => "subtraction overflow",
                ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _) => {
                    "multiplication overflow"
                }
                ConditionTerm::Bitvector32SignedDivideOverflows(_, _) => "division overflow",
                ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _) => "left-shift overflow",
                ConditionTerm::Bitvector64SignedLessThan(_, _) => "int64 signed less-than",
                ConditionTerm::Bitvector64SignedLessEqual(_, _) => "int64 signed less-or-equal",
                ConditionTerm::Bitvector64SignedGreaterThan(_, _) => "int64 signed greater-than",
                ConditionTerm::Bitvector64SignedGreaterEqual(_, _) => {
                    "int64 signed greater-or-equal"
                }
                ConditionTerm::Bitvector64UnsignedLessThan(_, _) => "uint64 less-than",
                ConditionTerm::Bitvector64UnsignedLessEqual(_, _) => "uint64 less-or-equal",
                ConditionTerm::Bitvector64UnsignedGreaterThan(_, _) => "uint64 greater-than",
                ConditionTerm::Bitvector64UnsignedGreaterEqual(_, _) => "uint64 greater-or-equal",
                ConditionTerm::Bitvector64Equal(_, _) => "64-bit equality",
                ConditionTerm::Bitvector64SignedAddOverflows(_, _) => "int64 addition overflow",
                ConditionTerm::Bitvector64SignedSubtractOverflows(_, _) => {
                    "int64 subtraction overflow"
                }
                ConditionTerm::Bitvector64SignedMultiplyOverflows(_, _) => {
                    "int64 multiplication overflow"
                }
                ConditionTerm::Bitvector64SignedDivideOverflows(_, _) => "int64 division overflow",
                ConditionTerm::Bitvector64SignedShiftLeftOverflows(_, _) => {
                    "int64 left-shift overflow"
                }
                ConditionTerm::Float32(CFloatCondition::Comparison { .. }) => "float32 comparison",
                ConditionTerm::Float32(CFloatCondition::Classification { .. }) => {
                    "float32 classification"
                }
                ConditionTerm::Float64(CFloatCondition::Comparison { .. }) => "float64 comparison",
                ConditionTerm::Float64(CFloatCondition::Classification { .. }) => {
                    "float64 classification"
                }
                ConditionTerm::PointerOffsetEqual(_, _) => "pointer-offset equality",
                ConditionTerm::PointerEqual(_, _) => "pointer equality",
                ConditionTerm::Constant(_) => "constant condition",
                ConditionTerm::Variable(_) => "condition variable",
            };
            format!("{kind} is {value}")
        }
        _ => bounded_debug(fact),
    }
}

pub(super) fn describe_execution_pure_facts(facts: &[ExecutionPureFact]) -> String {
    if facts.is_empty() {
        return "[]".to_string();
    }

    describe_bounded_list(facts, |fact| {
        describe_pure_fact(fact.proposition(), &[], &[])
    })
}

pub(super) fn describe_available_facts(
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    format!(
        "available pure facts: {}\n  available resource facts: {}",
        describe_context_pure_and_execution_facts(
            pure_facts,
            execution_pure_facts,
            parameters,
            arguments
        ),
        describe_resource_facts(resource_facts, parameters, arguments)
    )
}

pub(super) fn describe_missing_pure_fact(
    required: &Proposition,
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    format!(
        "missing pure fact: {}\n  {}",
        describe_pure_fact(required, parameters, arguments),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameters,
            arguments,
            execution_pure_facts
        )
    )
}

pub(super) fn describe_missing_resource_fact(
    required: &CResourceFact,
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    format!(
        "missing resource fact `{}`\n  {}",
        describe_resource_fact(required, parameters, arguments),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameters,
            arguments,
            execution_pure_facts
        )
    )
}

pub(super) fn describe_proof_context(
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    format!(
        "proof context:\n  pure facts: {}\n  resource facts: {}",
        describe_context_pure_and_execution_facts(
            pure_facts,
            execution_pure_facts,
            parameters,
            arguments
        ),
        describe_resource_facts(resource_facts, parameters, arguments)
    )
}

pub(super) fn describe_missing_proof_obligations(
    obligations: &[ProofObligation],
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    let item_limit = diagnostic_item_limit();
    let mut required = obligations
        .iter()
        .take(item_limit)
        .map(|obligation| match obligation.context() {
            Some(context) => format!(
                "{context}: {}",
                describe_pure_fact(obligation.proposition(), parameters, arguments)
            ),
            None => describe_pure_fact(obligation.proposition(), parameters, arguments),
        })
        .collect::<Vec<_>>();
    if obligations.len() > item_limit {
        required.push(format!("… {} more omitted", obligations.len() - item_limit));
    }

    let label = if required.len() == 1 {
        "missing pure fact"
    } else {
        "missing pure facts"
    };
    format!(
        "{label}: [{}]\n  {}",
        required.join(", "),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameters,
            arguments,
            execution_pure_facts
        )
    )
}

pub(super) fn describe_function_outcome(
    outcome: &CFunctionOutcome,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match outcome {
        CFunctionOutcome::Return { value, .. } => {
            format!(
                "returned {}",
                describe_c_value(value, parameters, arguments)
            )
        }
        CFunctionOutcome::VerificationDiverges => "has no verified return frontier".to_string(),
        CFunctionOutcome::UndefinedBehavior(kind) => match kind {
            crate::kernel::CUndefinedBehavior::SignedOverflow => {
                "undefined behavior: signed overflow".to_string()
            }
            crate::kernel::CUndefinedBehavior::PointerArithmetic => {
                "undefined behavior: pointer arithmetic left the pointed-to object".to_string()
            }
            crate::kernel::CUndefinedBehavior::DivisionByZero => {
                "undefined behavior: division by zero".to_string()
            }
            crate::kernel::CUndefinedBehavior::InvalidShift => {
                "undefined behavior: invalid shift".to_string()
            }
            crate::kernel::CUndefinedBehavior::InvalidMemory => {
                "undefined behavior: invalid memory access".to_string()
            }
            crate::kernel::CUndefinedBehavior::UninitializedRead => {
                "undefined behavior: read of uninitialized storage".to_string()
            }
        },
        CFunctionOutcome::RuntimeError(error) => {
            format!(
                "runtime error: {}",
                describe_runtime_error(error, parameters, arguments)
            )
        }
    }
}

pub(super) fn describe_runtime_error(
    error: &crate::kernel::CRuntimeError,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match error {
        crate::kernel::CRuntimeError::UnboundVariable(name) => {
            format!("unbound variable `{name}`")
        }
        crate::kernel::CRuntimeError::UnknownFunction(name) => {
            format!("unknown function `{name}`")
        }
        crate::kernel::CRuntimeError::TypeMismatch => "type mismatch".to_string(),
        crate::kernel::CRuntimeError::PointerConversion(message) => message.clone(),
        crate::kernel::CRuntimeError::IndeterminatePointeeType => {
            "pointer operation has no known pointee type".to_string()
        }
        crate::kernel::CRuntimeError::WrongArity { expected, actual } => {
            format!("wrong argument count: expected {expected}, got {actual}")
        }
        crate::kernel::CRuntimeError::MissingReturn => "missing return".to_string(),
        crate::kernel::CRuntimeError::MissingResource { resource } => format!(
            "missing resource fact `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::MissingVerifiedFunctionRule(name) => format!(
            "cannot execute call to `{name}` opaquely: its contract has not been verified yet"
        ),
        crate::kernel::CRuntimeError::UnsupportedOpaqueFunctionContract(name) => format!(
            "cannot execute call to `{name}` opaquely: its contract refers to an internal program point that is unavailable at the call site"
        ),
        crate::kernel::CRuntimeError::FunctionContract(message) => {
            format!("function contract could not be applied: {message}")
        }
        crate::kernel::CRuntimeError::InvalidFree(reason) => match reason {
            crate::kernel::CInvalidFree::InteriorPointer => {
                "cannot free an interior pointer; free requires the allocation base".to_string()
            }
            crate::kernel::CInvalidFree::NonHeapPointer => {
                "cannot free a pointer that is not a live heap allocation".to_string()
            }
            crate::kernel::CInvalidFree::DoubleFree => {
                "cannot free an allocation whose lifetime has already ended".to_string()
            }
        },
        crate::kernel::CRuntimeError::UnresolvedAllocationOutcome => {
            "malloc result was neither refined by a null check nor returned".to_string()
        }
        crate::kernel::CRuntimeError::LiveAllocationLeak { allocation } => format!(
            "live allocation obligation was neither returned nor freed: `{}`",
            describe_resource_fact(allocation, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::StaleResourceAfterFree { resource } => format!(
            "resource would remain usable after its allocation is freed: `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::DuplicateResource { resource } => format!(
            "duplicate resource fact `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::OverlappingOwnedMemoryResources { left, right } => format!(
            "overlapping owned memory resource facts `owns {}` and `owns {}`",
            describe_memory_range(left, parameters, arguments),
            describe_memory_range(right, parameters, arguments)
        ),
    }
}

pub(super) fn describe_resource_facts(
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if resource_facts.is_empty() {
        return "[]".to_string();
    }
    describe_bounded_list(resource_facts, |resource| {
        describe_resource_fact(resource, parameters, arguments)
    })
}

pub(super) fn describe_resource_fact(
    resource: &CResourceFact,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(range) = resource.memory_view_range() {
        return format!(
            "views {}",
            describe_memory_range(range, parameters, arguments)
        );
    }
    if let Some(range) = resource.memory_own_range() {
        return format!(
            "owns {}",
            describe_memory_range(range, parameters, arguments)
        );
    }
    match resource {
        CResourceFact::Own(
            CResource::Composite {
                name,
                arguments: resource_arguments,
            }
            | CResource::Token {
                name,
                arguments: resource_arguments,
            },
            quantity,
        ) => {
            let resource =
                format_declared_resource(name, resource_arguments, parameters, arguments);
            if quantity.as_const() == Some(1) {
                format!("owns {resource}")
            } else {
                format!(
                    "owns {resource} (quantity {})",
                    describe_bitvector_with_context(quantity, parameters, arguments)
                )
            }
        }
        CResourceFact::View(
            CResource::Composite {
                name,
                arguments: resource_arguments,
            }
            | CResource::Token {
                name,
                arguments: resource_arguments,
            },
        ) => format!(
            "views {}",
            format_declared_resource(name, resource_arguments, parameters, arguments)
        ),
        CResourceFact::Own(CResource::Memory(_), _) | CResourceFact::View(CResource::Memory(_)) => {
            unreachable!("memory resources handled above")
        }
    }
}

fn describe_c_resource(
    resource: &CResource,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match resource {
        CResource::Memory(range) => {
            format!(
                "memory({})",
                describe_memory_range(range, parameters, arguments)
            )
        }
        CResource::Composite {
            name,
            arguments: resource_arguments,
        }
        | CResource::Token {
            name,
            arguments: resource_arguments,
        } => format_declared_resource(name, resource_arguments, parameters, arguments),
    }
}

fn describe_resource_subject(resource: &ResourceSubject) -> String {
    match resource {
        ResourceSubject::Memory(segment) => {
            format!("memory({})", describe_contract_segment(segment))
        }
        ResourceSubject::Declared {
            name, arguments, ..
        } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn format_declared_resource(
    name: &str,
    resource_arguments: &[CValue],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    format!(
        "{name}({})",
        resource_arguments
            .iter()
            .map(|argument| describe_c_value(argument, parameters, arguments))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub(super) fn describe_memory_range(
    range: &CMemoryRange,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(description) = describe_parameter_relative_range(range, parameters, arguments) {
        return description;
    }
    format!(
        "{}[{}..{}]",
        describe_pointer(range.base(), parameters, arguments),
        describe_bitvector(range.start()),
        describe_bitvector(range.end())
    )
}

pub(super) fn describe_parameter_relative_range(
    range: &CMemoryRange,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(base_index) = diagnostic_pointer_element_index_from_base(
            range.base(),
            base,
            diagnostic_parameter_element_width(parameter),
        ) else {
            continue;
        };
        let start = bitvector32_add(base_index.clone(), range.start().clone());
        let end = bitvector32_add(base_index, range.end().clone());
        return Some(format!(
            "{}[{}..{}]",
            parameter.name(),
            describe_bitvector(&start),
            describe_bitvector(&end)
        ));
    }
    None
}

pub(super) fn describe_pointer(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        if let Some(index) = diagnostic_pointer_element_index_from_base(
            pointer,
            base,
            diagnostic_parameter_element_width(parameter),
        ) {
            if index == Bitvector32Term::Constant(0) {
                return parameter.name().to_string();
            }
            return format!("{}[{}]", parameter.name(), describe_bitvector(&index));
        }
    }
    format!(
        "{}@{}",
        pointer.block,
        describe_pointer_offset(&pointer.offset)
    )
}

pub(super) fn diagnostic_parameter_element_width(parameter: &syntax::C0Parameter) -> i64 {
    match parameter.c_type() {
        C0Type::Void => 0,
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => 1,
        C0Type::Int16 | C0Type::UInt16 | C0Type::Int16Array(_) | C0Type::UInt16Array(_) => 2,
        C0Type::Int32
        | C0Type::UInt8
        | C0Type::UInt32
        | C0Type::Int32Pointer
        | C0Type::UInt32Pointer
        | C0Type::Int32Array(_)
        | C0Type::UInt32Array(_) => 4,
        C0Type::Int64 | C0Type::UInt64 | C0Type::Int64Array(_) | C0Type::UInt64Array(_) => 8,
        C0Type::Float32 | C0Type::Float32Array(_) => 4,
        C0Type::Float64 | C0Type::Float64Array(_) => 8,
        C0Type::Int16Pointer
        | C0Type::UInt16Pointer
        | C0Type::Int64Pointer
        | C0Type::UInt64Pointer
        | C0Type::Int16PointerPointer
        | C0Type::UInt16PointerPointer
        | C0Type::Int32PointerPointer
        | C0Type::UInt8PointerPointer
        | C0Type::UInt32PointerPointer
        | C0Type::Int64PointerPointer
        | C0Type::UInt64PointerPointer
        | C0Type::Float32Pointer
        | C0Type::Float64Pointer
        | C0Type::Float32PointerPointer
        | C0Type::Float64PointerPointer => 8,
        C0Type::FunctionPointer(_) => 8,
    }
}

pub(super) fn diagnostic_pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    byte_width: i64,
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width),
                diagnostic_element_index_from_pointer_offset(&base.offset, byte_width),
            ) {
                Some(bitvector32_subtract(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

pub(super) fn diagnostic_element_index_from_pointer_offset(
    offset: &PointerOffsetTerm,
    byte_width: i64,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % byte_width == 0 => {
            let index = offset / byte_width;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: actual_width,
        } if *actual_width == byte_width => Some(value.as_ref().clone()),
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            diagnostic_element_index_from_pointer_offset(left, byte_width)?,
            diagnostic_element_index_from_pointer_offset(right, byte_width)?,
        )),
        _ => None,
    }
}

pub(super) fn describe_c_value(
    value: &CValue,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match value {
        CValue::Void => "void".to_string(),
        CValue::Int16(value) => {
            format!(
                "{}i16",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::Int32(value) => describe_bitvector_with_context(value, parameters, arguments),
        CValue::UInt8(value) => {
            format!(
                "{}u8",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::UInt32(value) => {
            format!(
                "{}u32",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::UInt16(value) => {
            format!(
                "{}u16",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::Int64(value) => format!(
            "{}i64",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        CValue::UInt64(value) => format!(
            "{}u64",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        CValue::Float32(value) => format!(
            "{}f32",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        CValue::Float64(value) => format!(
            "{}f64",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        CValue::Pointer(pointer) => describe_pointer(pointer, parameters, arguments),
    }
}

pub(super) fn describe_contract_segment(segment: &ContractSegment) -> String {
    let base = describe_c_expression(&segment.base);
    let current = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => {
            let rendered_base = describe_contract_expression(base);
            format!(
                "{rendered_base}[{}..{}]",
                describe_contract_expression(start),
                describe_contract_expression(end)
            )
        }
        ContractSegmentSurface::Field { name, .. } => format!("{base}->{name}"),
        ContractSegmentSurface::Object(_) => format!("object({base})"),
    };
    match segment.state {
        ContractSegmentState::Current => current,
        ContractSegmentState::Old => format!("old({current})"),
    }
}

pub(super) fn describe_evaluated_segments(segments: &[EvaluatedContractSegment]) -> String {
    if segments.is_empty() {
        return "[]".to_string();
    }
    let entries = segments
        .iter()
        .map(|segment| {
            format!(
                "{} => {}[{}..{}]",
                describe_contract_segment(&segment.source),
                describe_pointer(&segment.base, &[], &[]),
                describe_bitvector(&segment.start),
                describe_bitvector(&segment.end)
            )
        })
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

pub(super) fn describe_contract_segments(segments: &[EvaluatedContractSegment]) -> String {
    if segments.is_empty() {
        return "[]".to_string();
    }
    let entries = segments
        .iter()
        .map(|segment| describe_contract_segment(&segment.source))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

pub(super) fn describe_c_expression(expression: &CExpression) -> String {
    match expression {
        CExpression::Value(value) => describe_c_value(value, &[], &[]),
        CExpression::Variable(name) => name.clone(),
        CExpression::FunctionAddress(name) => format!("&{name}"),
        CExpression::Cast {
            expression,
            target_type,
        } => format!("({target_type:?}){}", describe_c_expression(expression)),
        CExpression::FloatNegate(expression) => format!("-{}", describe_c_expression(expression)),
        CExpression::FloatClassification {
            expression,
            classification,
        } => format!(
            "is{classification:?}({})",
            describe_c_expression(expression)
        ),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => format!(
            "{} ? {} : {}",
            describe_c_expression(condition),
            describe_c_expression(then_branch),
            describe_c_expression(else_branch)
        ),
        CExpression::AddressOf(target) => format!("&{}", describe_c_expression(target)),
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            format!("byte_offset({}, {bytes})", describe_c_expression(pointer))
        }
        CExpression::LessThan(left, right) => describe_binary_c_expression(left, "<", right),
        CExpression::LessEqual(left, right) => describe_binary_c_expression(left, "<=", right),
        CExpression::GreaterThan(left, right) => describe_binary_c_expression(left, ">", right),
        CExpression::GreaterEqual(left, right) => describe_binary_c_expression(left, ">=", right),
        CExpression::Equal(left, right) => describe_binary_c_expression(left, "==", right),
        CExpression::NotEqual(left, right) => describe_binary_c_expression(left, "!=", right),
        CExpression::Not(expression) => format!("!{}", describe_c_expression(expression)),
        CExpression::And(left, right) => describe_binary_c_expression(left, "&&", right),
        CExpression::Or(left, right) => describe_binary_c_expression(left, "||", right),
        CExpression::Add(left, right) => describe_binary_c_expression(left, "+", right),
        CExpression::Subtract(left, right) => describe_binary_c_expression(left, "-", right),
        CExpression::Multiply(left, right) => describe_binary_c_expression(left, "*", right),
        CExpression::Divide(left, right) => describe_binary_c_expression(left, "/", right),
        CExpression::Remainder(left, right) => describe_binary_c_expression(left, "%", right),
        CExpression::ShiftLeft(left, right) => describe_binary_c_expression(left, "<<", right),
        CExpression::ShiftRight(left, right) => describe_binary_c_expression(left, ">>", right),
        CExpression::BitwiseAnd(left, right) => describe_binary_c_expression(left, "&", right),
        CExpression::BitwiseOr(left, right) => describe_binary_c_expression(left, "|", right),
        CExpression::BitwiseXor(left, right) => describe_binary_c_expression(left, "^", right),
        CExpression::BitwiseNot(expression) => format!("~{}", describe_c_expression(expression)),
        CExpression::Load(pointer) => format!("*{}", describe_c_expression(pointer)),
        CExpression::TypedLoad {
            pointer,
            value_type,
        } => {
            let name = match value_type {
                CType::Void => "load_void",
                CType::Int16 => "load_int16",
                CType::Int32 => "load_int32",
                CType::UInt8 => "load_uint8",
                CType::UInt16 => "load_uint16",
                CType::UInt32 => "load_uint32",
                CType::Int64 => "load_int64",
                CType::UInt64 => "load_uint64",
                CType::Float32 => "load_float",
                CType::Float64 => "load_double",
                CType::Int16Pointer => "load_int16_pointer",
                CType::UInt16Pointer => "load_uint16_pointer",
                CType::Int32Pointer => "load_int32_pointer",
                CType::UInt8Pointer => "load_uint8_pointer",
                CType::UInt32Pointer => "load_uint32_pointer",
                CType::Int64Pointer => "load_int64_pointer",
                CType::UInt64Pointer => "load_uint64_pointer",
                CType::Int16PointerPointer => "load_int16_pointer_pointer",
                CType::UInt16PointerPointer => "load_uint16_pointer_pointer",
                CType::Int32PointerPointer => "load_int32_pointer_pointer",
                CType::UInt8PointerPointer => "load_uint8_pointer_pointer",
                CType::UInt32PointerPointer => "load_uint32_pointer_pointer",
                CType::Int64PointerPointer => "load_int64_pointer_pointer",
                CType::UInt64PointerPointer => "load_uint64_pointer_pointer",
                CType::Float32Pointer => "load_float_pointer",
                CType::Float64Pointer => "load_double_pointer",
                CType::Float32PointerPointer => "load_float_pointer_pointer",
                CType::Float64PointerPointer => "load_double_pointer_pointer",
                CType::FunctionPointer(_) => "load_function_pointer",
                CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::Int16Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int64Array(_)
                | CType::UInt64Array(_)
                | CType::Float32Array(_)
                | CType::Float64Array(_) => {
                    return format!("*{}", describe_c_expression(pointer));
                }
            };
            format!("{name}({})", describe_c_expression(pointer))
        }
        CExpression::Index(base, index) => {
            format!(
                "{}[{}]",
                describe_c_expression(base),
                describe_c_expression(index)
            )
        }
    }
}

pub(super) fn describe_binary_c_expression(
    left: &CExpression,
    operator: &str,
    right: &CExpression,
) -> String {
    format!(
        "({} {operator} {})",
        describe_c_expression(left),
        describe_c_expression(right)
    )
}

pub(super) fn describe_contract_expression(expression: &ContractExpression) -> String {
    match expression {
        ContractExpression::CFragment(expression) => describe_c_expression(expression),
        ContractExpression::Field { base, field, .. } => {
            format!("{}->{field}", describe_contract_expression(base))
        }
        ContractExpression::CBinding(name) => format!("c({name})"),
        ContractExpression::ResourceWildcard => "_".to_string(),
        ContractExpression::ResourceCount(resource) => {
            format!("count({})", describe_resource_clause(resource))
        }
        ContractExpression::Old(expression) => {
            format!("old({})", describe_contract_expression(expression))
        }
        ContractExpression::At {
            selector,
            expression,
        } => format!(
            "at({}, {})",
            describe_snapshot_selector(selector),
            describe_contract_expression(expression)
        ),
        ContractExpression::Add(left, right) => {
            describe_binary_contract_expression(left, "+", right)
        }
        ContractExpression::Subtract(left, right) => {
            describe_binary_contract_expression(left, "-", right)
        }
        ContractExpression::Multiply(left, right) => {
            describe_binary_contract_expression(left, "*", right)
        }
        ContractExpression::Divide(left, right) => {
            describe_binary_contract_expression(left, "/", right)
        }
        ContractExpression::Remainder(left, right) => {
            describe_binary_contract_expression(left, "%", right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            describe_binary_contract_expression(left, "<<", right)
        }
        ContractExpression::ShiftRight(left, right) => {
            describe_binary_contract_expression(left, ">>", right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            describe_binary_contract_expression(left, "&", right)
        }
        ContractExpression::BitwiseOr(left, right) => {
            describe_binary_contract_expression(left, "|", right)
        }
        ContractExpression::BitwiseXor(left, right) => {
            describe_binary_contract_expression(left, "^", right)
        }
        ContractExpression::BitwiseNot(expression) => {
            format!("~{}", describe_contract_expression(expression))
        }
        ContractExpression::Index(base, index) => format!(
            "{}[{}]",
            describe_contract_expression(base),
            describe_contract_expression(index)
        ),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => format!(
            "if {} then {} else {}",
            describe_click_proposition(condition),
            describe_contract_expression(then_branch),
            describe_contract_expression(else_branch)
        ),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => format!(
            "fold({}..{}, {}, ({accumulator}, {item}) => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_contract_expression(initial),
            describe_contract_expression(body)
        ),
        ContractExpression::Let {
            name, value, body, ..
        } => format!(
            "(let {name} = {}; {})",
            describe_contract_expression(value),
            describe_contract_expression(body)
        ),
        ContractExpression::Call { name, arguments } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

pub(super) fn describe_binary_contract_expression(
    left: &ContractExpression,
    operator: &str,
    right: &ContractExpression,
) -> String {
    format!(
        "({} {operator} {})",
        describe_contract_expression(left),
        describe_contract_expression(right)
    )
}

pub(super) fn describe_click_proposition(proposition: &ClickProposition) -> String {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => format!(
            "{} {operator} {}",
            describe_contract_expression(left),
            describe_contract_expression(right)
        ),
        ClickProposition::FloatClassification {
            expression,
            classification,
        } => format!(
            "{}({})",
            match classification {
                syntax::C0FloatClassification::Finite => "isfinite",
                syntax::C0FloatClassification::Infinite => "isinf",
                syntax::C0FloatClassification::Zero => "iszero",
                syntax::C0FloatClassification::Subnormal => "issubnormal",
                syntax::C0FloatClassification::Nan => "isnan",
            },
            describe_contract_expression(expression)
        ),
        ClickProposition::Separate { left, right } => format!(
            "separate({}, {})",
            describe_resource_subject(left),
            describe_resource_subject(right)
        ),
        ClickProposition::Contains { parent, child } => format!(
            "contains({}, {})",
            describe_resource_subject(parent),
            describe_resource_subject(child)
        ),
        ClickProposition::Loadable { segment } => {
            format!("loadable({})", describe_contract_segment(segment))
        }
        ClickProposition::Defined { expression } => {
            format!("defined({})", describe_contract_expression(expression))
        }
        ClickProposition::At {
            selector,
            proposition,
        } => format!(
            "at({}, {})",
            describe_snapshot_selector(selector),
            describe_click_proposition(proposition)
        ),
        ClickProposition::And(left, right) => describe_binary_click_proposition(left, "&&", right),
        ClickProposition::Or(left, right) => describe_binary_click_proposition(left, "||", right),
        ClickProposition::Not(proposition) => {
            format!("!{}", describe_click_proposition(proposition))
        }
        ClickProposition::Implies(left, right) => {
            describe_binary_click_proposition(left, "=>", right)
        }
        ClickProposition::ForAll { c_type, name, body } => format!(
            "forall ({name}: {}) {{ {} }}",
            describe_c0_type(*c_type),
            describe_click_proposition(body)
        ),
        ClickProposition::Exists { c_type, name, body } => format!(
            "exists ({name}: {}) {{ {} }}",
            describe_c0_type(*c_type),
            describe_click_proposition(body)
        ),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => format!(
            "({}..{}).all({item} => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_click_proposition(body)
        ),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => format!(
            "({}..{}).any({item} => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_click_proposition(body)
        ),
        ClickProposition::PredicateCall { name, arguments } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

pub(super) fn describe_binary_click_proposition(
    left: &ClickProposition,
    operator: &str,
    right: &ClickProposition,
) -> String {
    format!(
        "({} {operator} {})",
        describe_click_proposition(left),
        describe_click_proposition(right)
    )
}

pub(super) fn describe_snapshot_selector(selector: &SnapshotSelector) -> String {
    match selector {
        SnapshotSelector::ProgramPoint(point) => describe_program_point_ref(point),
        SnapshotSelector::Mark(name) => name.clone(),
    }
}

pub(super) fn describe_program_point_ref(point: &ProgramPointRef) -> String {
    let kind = match point.kind {
        ProgramPointKind::Entry => "entry",
        ProgramPointKind::Exit => "exit",
    };
    format!("{}.{}", describe_code_region_ref(&point.region), kind)
}

pub(super) fn describe_code_region_ref(region: &CodeRegionRef) -> String {
    match region {
        CodeRegionRef::Function => "function".to_string(),
        CodeRegionRef::Loop(index) => format!("loop({index})"),
        CodeRegionRef::Statement(index) => format!("statement({index})"),
        CodeRegionRef::Label(name) => name.clone(),
    }
}

pub(super) fn describe_bitvector(term: &Bitvector32Term) -> String {
    describe_bitvector_with_context(term, &[], &[])
}

pub(super) fn describe_bitvector_with_context(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(name) = describe_parameter_bitvector(term, parameters, arguments) {
        return name;
    }
    match term {
        Bitvector32Term::Constant(value) => format!("{}", *value as i32),
        Bitvector32Term::Int64Constant(value) => format!("{value}i64"),
        Bitvector32Term::UInt64Constant(value) => format!("{value}u64"),
        // A diagnostic prints the load represented by a load variable,
        // never the kernel variable's id.
        Bitvector32Term::Variable(variable)
            if crate::kernel::is_load_variable(variable)
                && crate::kernel::registered_load_for_variable(variable).is_some() =>
        {
            let (_, pointer) = crate::kernel::registered_load_for_variable(variable)
                .expect("checked registered above");
            format!(
                "load({})",
                describe_pointer(&pointer, parameters, arguments)
            )
        }
        Bitvector32Term::Variable(variable) => format!("v{}", variable.0),
        Bitvector32Term::Add(left, right) => {
            describe_binary_bitvector_with_context(left, "+", right, parameters, arguments)
        }
        Bitvector32Term::Subtract(left, right) => {
            describe_binary_bitvector_with_context(left, "-", right, parameters, arguments)
        }
        Bitvector32Term::Multiply(left, right) => {
            describe_binary_bitvector_with_context(left, "*", right, parameters, arguments)
        }
        Bitvector32Term::Divide(left, right) => {
            describe_binary_bitvector_with_context(left, "/", right, parameters, arguments)
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            describe_binary_bitvector_with_context(left, "/", right, parameters, arguments)
        }
        Bitvector32Term::Remainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            describe_binary_bitvector_with_context(left, "<<", right, parameters, arguments)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            describe_binary_bitvector_with_context(left, ">>", right, parameters, arguments)
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            describe_binary_bitvector_with_context(left, ">>", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            describe_binary_bitvector_with_context(left, "&", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            describe_binary_bitvector_with_context(left, "|", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            describe_binary_bitvector_with_context(left, "^", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseNot(value) => {
            format!(
                "~{}",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        Bitvector32Term::Float32Negate(value) | Bitvector32Term::Float64Negate(value) => {
            format!(
                "-{}",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        Bitvector32Term::Float32Binary {
            operator,
            left,
            right,
        }
        | Bitvector32Term::Float64Binary {
            operator,
            left,
            right,
        } => {
            let symbol = match operator {
                CFloatBinaryOperator::Add => "+",
                CFloatBinaryOperator::Subtract => "-",
                CFloatBinaryOperator::Multiply => "*",
                CFloatBinaryOperator::Divide => "/",
            };
            describe_binary_bitvector_with_context(left, symbol, right, parameters, arguments)
        }
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value) => format!(
            "cast64({})",
            describe_bitvector_with_context(value, parameters, arguments)
        ),
        Bitvector32Term::Int64Add(left, right) | Bitvector32Term::UInt64Add(left, right) => {
            describe_binary_bitvector_with_context(left, "+", right, parameters, arguments)
        }
        Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::UInt64Subtract(left, right) => {
            describe_binary_bitvector_with_context(left, "-", right, parameters, arguments)
        }
        Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::UInt64Multiply(left, right) => {
            describe_binary_bitvector_with_context(left, "*", right, parameters, arguments)
        }
        Bitvector32Term::Int64Divide(left, right) | Bitvector32Term::UInt64Divide(left, right) => {
            describe_binary_bitvector_with_context(left, "/", right, parameters, arguments)
        }
        Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::UInt64Remainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right) => {
            describe_binary_bitvector_with_context(left, "<<", right, parameters, arguments)
        }
        Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            describe_binary_bitvector_with_context(left, ">>", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            describe_binary_bitvector_with_context(left, "&", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right) => {
            describe_binary_bitvector_with_context(left, "|", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            describe_binary_bitvector_with_context(left, "^", right, parameters, arguments)
        }
        Bitvector32Term::Int64BitwiseNot(value) | Bitvector32Term::UInt64BitwiseNot(value) => {
            format!(
                "~{}",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => format!(
            "if {} then {} else {}",
            describe_condition(condition),
            describe_bitvector_with_context(then_term, parameters, arguments),
            describe_bitvector_with_context(else_term, parameters, arguments)
        ),
        Bitvector32Term::RangeFold { .. } => bounded_debug(term),
        Bitvector32Term::PureFunctionApplication {
            name,
            arguments: values,
        } => format!(
            "{}({})",
            name,
            values
                .iter()
                .map(|argument| {
                    describe_bitvector_with_context(argument, parameters, arguments)
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Bitvector32Term::MemoryLoad(_, pointer) => {
            format!("load({})", describe_pointer(pointer, parameters, arguments))
        }
        Bitvector32Term::PointerAddress(pointer) => {
            format!(
                "address({})",
                describe_pointer(pointer, parameters, arguments)
            )
        }
    }
}

pub(super) fn describe_parameter_bitvector(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        match argument {
            CExpression::Value(CValue::Int32(value))
                if value == term && parameter.c_type() == C0Type::Int32 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt8(value))
                if value == term && parameter.c_type() == C0Type::UInt8 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::Int16(value))
                if value == term && parameter.c_type() == C0Type::Int16 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt16(value))
                if value == term && parameter.c_type() == C0Type::UInt16 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt32(value))
                if value == term && parameter.c_type() == C0Type::UInt32 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::Int64(value))
                if value == term && parameter.c_type() == C0Type::Int64 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt64(value))
                if value == term && parameter.c_type() == C0Type::UInt64 =>
            {
                return Some(parameter.name().to_string());
            }
            _ => {}
        }
    }
    None
}

pub(super) fn describe_binary_bitvector_with_context(
    left: &Bitvector32Term,
    operator: &str,
    right: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    format!(
        "({} {operator} {})",
        describe_bitvector_with_context(left, parameters, arguments),
        describe_bitvector_with_context(right, parameters, arguments)
    )
}

pub(super) fn describe_pointer_offset(offset: &PointerOffsetTerm) -> String {
    match offset {
        PointerOffsetTerm::Constant(value) => value.to_string(),
        PointerOffsetTerm::Variable(variable) => format!("off{}", variable.0),
        PointerOffsetTerm::Add(left, right) => format!(
            "({} + {})",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            format!("{} * {byte_width}", describe_bitvector(value))
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => {
            let signedness = if *unsigned { "uint64" } else { "int64" };
            format!("{signedness}({}) * {byte_width}", describe_bitvector(value))
        }
    }
}

pub(super) fn describe_condition(condition: &ConditionTerm) -> String {
    match condition {
        ConditionTerm::Constant(value) => value.to_string(),
        ConditionTerm::Variable(variable) => format!("cond{}", variable.0),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            describe_binary_condition(left, "<", right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            describe_binary_condition(left, "<=", right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            describe_binary_condition(left, ">", right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            describe_binary_condition(left, ">=", right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            describe_binary_condition(left, "==", right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            format!(
                "overflow({} + {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            format!(
                "overflow({} - {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            format!(
                "overflow({} * {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            format!(
                "overflow({} / {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            format!(
                "overflow({} << {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
            describe_binary_condition(left, "<", right)
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            describe_binary_condition(left, "<=", right)
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            describe_binary_condition(left, ">", right)
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            describe_binary_condition(left, ">=", right)
        }
        ConditionTerm::Bitvector64Equal(left, right) => {
            describe_binary_condition(left, "==", right)
        }
        ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            format!(
                "overflow({} + {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            format!(
                "overflow({} - {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            format!(
                "overflow({} * {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
            format!(
                "overflow({} / {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            format!(
                "overflow({} << {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Float32(float_condition) => describe_float_condition(float_condition),
        ConditionTerm::Float64(float_condition) => describe_float_condition(float_condition),
        ConditionTerm::PointerOffsetEqual(left, right) => format!(
            "{} == {}",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
        ConditionTerm::PointerEqual(left, right) => {
            format!(
                "{} == {}",
                describe_pointer(left, &[], &[]),
                describe_pointer(right, &[], &[])
            )
        }
    }
}

pub(super) fn describe_binary_condition(
    left: &Bitvector32Term,
    operator: &str,
    right: &Bitvector32Term,
) -> String {
    format!(
        "{} {operator} {}",
        describe_bitvector(left),
        describe_bitvector(right)
    )
}

fn describe_float_condition(condition: &CFloatCondition) -> String {
    match condition {
        CFloatCondition::Comparison {
            operator,
            left,
            right,
        } => {
            let operator = match operator {
                CComparisonOperator::Equal => "==",
                CComparisonOperator::NotEqual => "!=",
                CComparisonOperator::LessThan => "<",
                CComparisonOperator::LessEqual => "<=",
                CComparisonOperator::GreaterThan => ">",
                CComparisonOperator::GreaterEqual => ">=",
            };
            describe_binary_condition(left, operator, right)
        }
        CFloatCondition::Classification {
            classification,
            value,
        } => format!("is{classification:?}({})", describe_bitvector(value)),
    }
}
