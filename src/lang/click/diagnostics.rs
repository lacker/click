use super::*;

pub(super) fn describe_pure_facts(pure_facts: &[Proposition]) -> String {
    if pure_facts.is_empty() {
        return "[]".to_string();
    }

    format!("{pure_facts:?}")
}

pub(super) fn describe_context_pure_facts(
    pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if pure_facts.is_empty() {
        return "[]".to_string();
    }

    let entries = pure_facts
        .iter()
        .map(|fact| describe_pure_fact(fact, parameters, arguments))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
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
        _ => format!("{fact:?}"),
    }
}

pub(super) fn describe_execution_pure_facts(facts: &[ExecutionPureFact]) -> String {
    if facts.is_empty() {
        return "[]".to_string();
    }

    let entries = facts
        .iter()
        .map(|fact| format!("{:?}", fact.proposition()))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

pub(super) fn describe_available_facts(
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    let mut all_pure_facts = pure_facts.to_vec();
    all_pure_facts.extend(
        execution_pure_facts
            .iter()
            .map(|fact| fact.proposition().clone()),
    );
    format!(
        "available pure facts: {}\n  available resource facts: {}",
        describe_context_pure_facts(&all_pure_facts, parameters, arguments),
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
    let mut all_pure_facts = pure_facts.to_vec();
    all_pure_facts.extend(
        execution_pure_facts
            .iter()
            .map(|fact| fact.proposition().clone()),
    );
    format!(
        "proof context:\n  pure facts: {}\n  resource facts: {}",
        describe_context_pure_facts(&all_pure_facts, parameters, arguments),
        describe_resource_facts(resource_facts, parameters, arguments)
    )
}

pub(super) fn describe_obligations(obligations: &[ProofObligation]) -> String {
    if obligations.is_empty() {
        return "[]".to_string();
    }

    let entries = obligations
        .iter()
        .map(|obligation| match obligation.context() {
            Some(context) => format!("{context}: {:?}", obligation.proposition()),
            None => format!("{:?}", obligation.proposition()),
        })
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

pub(super) fn describe_missing_proof_obligations(
    obligations: &[ProofObligation],
    pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    execution_pure_facts: &[ExecutionPureFact],
) -> String {
    let required = obligations
        .iter()
        .map(|obligation| match obligation.context() {
            Some(context) => format!(
                "{context}: {}",
                describe_pure_fact(obligation.proposition(), parameters, arguments)
            ),
            None => describe_pure_fact(obligation.proposition(), parameters, arguments),
        })
        .collect::<Vec<_>>();

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
        CFunctionOutcome::UndefinedBehavior(kind) => match kind {
            crate::kernel::CUndefinedBehavior::SignedOverflow => {
                "undefined behavior: signed overflow".to_string()
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
        crate::kernel::CRuntimeError::WrongArity { expected, actual } => {
            format!("wrong argument count: expected {expected}, got {actual}")
        }
        crate::kernel::CRuntimeError::MissingReturn => "missing return".to_string(),
        crate::kernel::CRuntimeError::MissingResource { resource } => format!(
            "missing resource fact `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::DuplicateResource { resource } => format!(
            "duplicate resource fact `{}`",
            describe_resource_fact(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::OverlappingWriteResources { left, right } => format!(
            "overlapping write resource facts `write({})` and `write({})`",
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
    let entries = resource_facts
        .iter()
        .map(|resource| describe_resource_fact(resource, parameters, arguments))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

pub(super) fn describe_resource_fact(
    resource: &CResourceFact,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(range) = resource.memory_view_range() {
        return format!(
            "read({})",
            describe_memory_range(range, parameters, arguments)
        );
    }
    if let Some(range) = resource.memory_own_range() {
        return format!(
            "write({})",
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
        ) => format_declared_resource(name, resource_arguments, parameters, arguments),
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
            "view {}",
            format_declared_resource(name, resource_arguments, parameters, arguments)
        ),
        CResourceFact::Own(CResource::Memory(_)) | CResourceFact::View(CResource::Memory(_)) => {
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
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => 1,
        C0Type::Int32 | C0Type::UInt8 | C0Type::Int32Pointer | C0Type::Int32Array(_) => 4,
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
        CValue::Int32(value) => describe_bitvector_with_context(value, parameters, arguments),
        CValue::UInt8(value) => {
            format!(
                "{}u8",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::Pointer(pointer) => describe_pointer(pointer, parameters, arguments),
    }
}

pub(super) fn describe_contract_segment(segment: &ContractSegment) -> String {
    let prefix = match segment.state {
        ContractSegmentState::Current => "",
        ContractSegmentState::Old => "old ",
    };
    format!(
        "{}{}[{}..{}]",
        prefix,
        describe_c_expression(&segment.base),
        describe_c_expression(&segment.start),
        describe_c_expression(&segment.end)
    )
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
        CExpression::AddressOf(target) => format!("&{}", describe_c_expression(target)),
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
        CExpression::TypedLoad { pointer, .. } => format!("*{}", describe_c_expression(pointer)),
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
        ContractExpression::Old(expression) => {
            format!("old({})", describe_contract_expression(expression))
        }
        ContractExpression::At {
            selector,
            expression,
        } => format!(
            "at({}, {})",
            describe_visit_selector(selector),
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
            "let {name} = {}; {}",
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
        ClickProposition::And(left, right) => describe_binary_click_proposition(left, "&&", right),
        ClickProposition::Or(left, right) => describe_binary_click_proposition(left, "||", right),
        ClickProposition::Not(proposition) => {
            format!("!{}", describe_click_proposition(proposition))
        }
        ClickProposition::Implies(left, right) => {
            describe_binary_click_proposition(left, "=>", right)
        }
        ClickProposition::ForAll { c_type, name, body } => format!(
            "forall ({c_type:?} {name}) {{ {} }}",
            describe_click_proposition(body)
        ),
        ClickProposition::Exists { c_type, name, body } => format!(
            "exists ({c_type:?} {name}) {{ {} }}",
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

pub(super) fn describe_visit_selector(selector: &VisitSelector) -> String {
    match selector {
        VisitSelector::ProgramPoint(point) => describe_program_point_ref(point),
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
        Bitvector32Term::Remainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            describe_binary_bitvector_with_context(left, "<<", right, parameters, arguments)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
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
        Bitvector32Term::RangeFold { .. } => format!("{term:?}"),
        Bitvector32Term::MemoryLoad(_, pointer) => {
            format!("load({})", describe_pointer(pointer, parameters, arguments))
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
