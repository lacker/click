use super::*;

pub(in crate::kernel) fn bitvector_same_base_nonzero_const_offset(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    if let Some((left_base, left_addend)) = left.add_const_parts() {
        if &left_base == right {
            return left_addend != 0;
        }
        if let Some((right_base, right_addend)) = right.add_const_parts() {
            return left_base == right_base && left_addend != right_addend;
        }
    }

    if let Some((right_base, right_addend)) = right.add_const_parts() {
        return &right_base == left && right_addend != 0;
    }

    false
}

pub(in crate::kernel) fn collect_proposition_bitvector_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        Proposition::Equal(left, right) => {
            collect_term_bitvector_variables(left, variables);
            collect_term_bitvector_variables(right, variables);
        }
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bitvector_variables(condition, variables);
        }
        Proposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_term_bitvector_variables(argument, variables);
            }
        }
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(expression, variables);
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CConditionEvaluates {
            state, condition, ..
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(condition, variables);
        }
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_statement_bitvector_variables(statement, variables);
            collect_c_statement_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_statement_bitvector_variables(statement, variables);
            collect_c_statement_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CFunctionExecutes {
            state,
            arguments,
            function,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CFunctionVerifies {
            state,
            arguments,
            function,
            outcome,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => {
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_specification_bitvector_variables(specification, variables);
        }
        Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => {
            collect_c_function_bitvector_variables(function, variables);
            collect_c_function_specification_bitvector_variables(specification, variables);
        }
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::CMemoryCanStore {
            memory, pointer, ..
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(base, variables);
            collect_bitvector_variables(bytes, variables);
        }
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => {
            collect_pointer_bitvector_variables(left_base, variables);
            collect_bitvector_variables(left_start, variables);
            collect_bitvector_variables(left_end, variables);
            collect_pointer_bitvector_variables(right_base, variables);
            collect_bitvector_variables(right_start, variables);
            collect_bitvector_variables(right_end, variables);
        }
        Proposition::CResourceSeparate { left, right } => {
            collect_c_resource_bitvector_variables(left, variables);
            collect_c_resource_bitvector_variables(right, variables);
        }
        Proposition::CResourceComposition(resources) => {
            collect_resource_context_bitvector_variables(resources, variables);
        }
        Proposition::CResourceContains { parent, child } => {
            collect_c_resource_bitvector_variables(parent, variables);
            collect_c_resource_bitvector_variables(child, variables);
        }
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for pointer in pointers {
                collect_pointer_bitvector_variables(pointer, variables);
            }
        }
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for range in mutable_ranges {
                collect_c_memory_range_bitvector_variables(range, variables);
            }
        }
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            collect_pointer_bitvector_variables(allocation_base, variables);
            collect_bitvector_variables(bytes, variables);
        }
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition,
        } => {
            collect_c_state_bitvector_variables(state, variables);
            collect_c_expression_bitvector_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            collect_c_statement_bitvector_variables(body, variables);
            for proposition in preserved {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            collect_proposition_bitvector_variables(postcondition, variables);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bitvector_variables(left, variables);
            collect_proposition_bitvector_variables(right, variables);
        }
        Proposition::Not(body) => collect_proposition_bitvector_variables(body, variables),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            collect_proposition_bitvector_variables(body, variables);
            variables.remove(var);
        }
    }
}

pub(in crate::kernel) fn collect_term_bitvector_variables(
    term: &Term,
    variables: &mut BTreeSet<Variable>,
) {
    match term {
        Term::Condition(condition) => collect_condition_bitvector_variables(condition, variables),
        Term::Bitvector32(bits) => collect_bitvector_variables(bits, variables),
        Term::PointerOffset(offset) => {
            collect_pointer_offset_bitvector_variables(offset, variables)
        }
        Term::CValue(value) => collect_c_value_bitvector_variables(value, variables),
        Term::Sequence(sequence) => collect_sequence_bitvector_variables(sequence, variables),
        Term::CExpressionOutcome(outcome) => {
            collect_c_expression_outcome_bitvector_variables(outcome, variables);
        }
        Term::CStatementOutcome(outcome) => {
            collect_c_statement_outcome_bitvector_variables(outcome, variables);
        }
        Term::CFunctionOutcome(outcome) => {
            collect_c_function_outcome_bitvector_variables(outcome, variables);
        }
        Term::CMemory(memory) => collect_memory_bitvector_variables(memory, variables),
        Term::CState(state) => collect_c_state_bitvector_variables(state, variables),
    }
}

fn collect_sequence_bitvector_variables(
    sequence: &SequenceTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for value in values.iter() {
                collect_c_value_bitvector_variables(value, variables);
            }
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_bitvector_variables(left, variables);
            collect_sequence_bitvector_variables(right, variables);
        }
    }
}

pub(in crate::kernel) fn collect_c_expression_bitvector_variables(
    expression: &CExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        CExpression::Value(value) => collect_c_value_bitvector_variables(value, variables),
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. } => {
            collect_c_expression_bitvector_variables(expression, variables)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bitvector_variables(condition, variables);
            collect_c_expression_bitvector_variables(then_branch, variables);
            collect_c_expression_bitvector_variables(else_branch, variables);
        }
        CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. } => {
            collect_c_expression_bitvector_variables(expression, variables)
        }
        CExpression::AddressOf(body) | CExpression::Not(body) | CExpression::Load(body) => {
            collect_c_expression_bitvector_variables(body, variables);
        }
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_c_expression_bitvector_variables(left, variables);
            collect_c_expression_bitvector_variables(right, variables);
        }
        CExpression::BitwiseNot(expression) => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
    }
}

pub(in crate::kernel) fn collect_c_statement_bitvector_variables(
    statement: &CStatement,
    variables: &mut BTreeSet<Variable>,
) {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::ContinueWithStep { step } => {
            collect_c_statement_bitvector_variables(step, variables);
        }
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        } => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        CStatement::CallAssign { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
        CStatement::Call { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
        CStatement::HeapAllocate { .. } => {}
        CStatement::HeapFree { pointer } => {
            collect_c_expression_bitvector_variables(pointer, variables);
        }
        CStatement::Seq(first, second) => {
            collect_c_statement_bitvector_variables(first, variables);
            collect_c_statement_bitvector_variables(second, variables);
        }
        CStatement::Store { pointer, value } => {
            collect_c_expression_bitvector_variables(pointer, variables);
            collect_c_expression_bitvector_variables(value, variables);
        }
        CStatement::TypedStore { pointer, value, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
            collect_c_expression_bitvector_variables(value, variables);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            collect_c_expression_bitvector_variables(target, variables);
            collect_c_expression_bitvector_variables(operand, variables);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bitvector_variables(condition, variables);
            collect_c_statement_bitvector_variables(then_branch, variables);
            collect_c_statement_bitvector_variables(else_branch, variables);
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
            ..
        } => {
            collect_c_expression_bitvector_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            for check in invariant_checks {
                collect_spec_proposition_bitvector_variables(check.proposition(), variables);
            }
            for check in effect_checks {
                collect_loop_effect_bitvector_variables(check.effect(), variables);
            }
            collect_c_statement_bitvector_variables(body, variables);
        }
        CStatement::Switch { expression, cases } => {
            collect_c_expression_bitvector_variables(expression, variables);
            for case in cases {
                collect_c_statement_bitvector_variables(&case.body, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_spec_memory_bitvector_variables(
    memory: &SpecMemory,
    variables: &mut BTreeSet<Variable>,
) {
    match memory {
        SpecMemory::Current | SpecMemory::FunctionEntry => {}
        SpecMemory::LoopEntry => {}
        SpecMemory::Fixed(memory) => collect_memory_bitvector_variables(memory, variables),
    }
}

pub(in crate::kernel) fn collect_spec_expression_bitvector_variables(
    expression: &SpecExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        SpecExpression::Value(value) => collect_c_value_bitvector_variables(value, variables),
        SpecExpression::CExpression(expression) => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments {
                if let Some(argument) = argument {
                    collect_spec_expression_bitvector_variables(argument, variables);
                }
            }
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            collect_spec_expression_bitvector_variables(left, variables);
            collect_spec_expression_bitvector_variables(right, variables);
        }
        SpecExpression::BitwiseNot(expression) => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_spec_proposition_bitvector_variables(condition, variables);
            collect_spec_expression_bitvector_variables(then_branch, variables);
            collect_spec_expression_bitvector_variables(else_branch, variables);
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator: _,
            item: _,
            body,
        } => {
            collect_spec_expression_bitvector_variables(start, variables);
            collect_spec_expression_bitvector_variables(end, variables);
            collect_spec_expression_bitvector_variables(initial, variables);
            collect_spec_expression_bitvector_variables(body, variables);
        }
        SpecExpression::Let {
            name: _,
            value,
            body,
        } => {
            collect_spec_expression_bitvector_variables(value, variables);
            collect_spec_expression_bitvector_variables(body, variables);
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_spec_expression_bitvector_variables(argument, variables);
            }
        }
        SpecExpression::LoopEntrySnapshot(expression) => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width: _,
        } => {
            collect_spec_expression_bitvector_variables(pointer, variables);
            collect_spec_expression_bitvector_variables(elements, variables);
        }
        SpecExpression::MemoryLoad {
            memory, pointer, ..
        } => {
            collect_spec_memory_bitvector_variables(memory, variables);
            collect_spec_expression_bitvector_variables(pointer, variables);
        }
    }
}

pub(in crate::kernel) fn collect_spec_proposition_bitvector_variables(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        SpecProposition::SequenceMembership { element, sequence } => {
            collect_spec_expression_bitvector_variables(element, variables);
            collect_spec_sequence_bitvector_variables(sequence, variables);
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            collect_spec_sequence_bitvector_variables(left, variables);
            collect_spec_sequence_bitvector_variables(right, variables);
        }
        SpecProposition::Comparison { left, right, .. } => {
            collect_spec_expression_bitvector_variables(left, variables);
            collect_spec_expression_bitvector_variables(right, variables);
        }
        SpecProposition::FloatClassification { expression, .. } => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            collect_spec_proposition_bitvector_variables(left, variables);
            collect_spec_proposition_bitvector_variables(right, variables);
        }
        SpecProposition::Not(body) => {
            collect_spec_proposition_bitvector_variables(body, variables);
        }
        SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsPointer { variable, body, .. } => {
            collect_spec_proposition_bitvector_variables(body, variables);
            variables.remove(variable);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(expression) => {
                        collect_spec_expression_bitvector_variables(expression, variables);
                    }
                    SpecPredicateArgument::ArrayRef { pointer, .. } => {
                        collect_spec_expression_bitvector_variables(pointer, variables);
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            collect_spec_resource_bitvector_variables(left, variables);
            collect_spec_resource_bitvector_variables(right, variables);
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            collect_spec_memory_bitvector_variables(memory, variables);
            collect_spec_expression_bitvector_variables(base, variables);
            collect_spec_expression_bitvector_variables(start, variables);
            collect_spec_expression_bitvector_variables(end, variables);
        }
        SpecProposition::Defined(expression) => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
    }
}

fn collect_spec_sequence_bitvector_variables(
    sequence: &SpecSequenceExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match sequence {
        SpecSequenceExpression::Literal(elements) => {
            for element in elements {
                collect_spec_expression_bitvector_variables(element, variables);
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            collect_spec_sequence_bitvector_variables(left, variables);
            collect_spec_sequence_bitvector_variables(right, variables);
        }
    }
}

fn collect_spec_resource_bitvector_variables(
    resource: &SpecResource,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            collect_spec_expression_bitvector_variables(base, variables);
            collect_spec_expression_bitvector_variables(start, variables);
            collect_spec_expression_bitvector_variables(end, variables);
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                collect_spec_expression_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_loop_effect_bitvector_variables(
    effect: &CLoopEffect,
    variables: &mut BTreeSet<Variable>,
) {
    match effect {
        CLoopEffect::Immutable => {}
        CLoopEffect::Mutable(segments) => {
            for segment in segments {
                collect_c_expression_bitvector_variables(&segment.base, variables);
                collect_c_expression_bitvector_variables(&segment.start, variables);
                collect_c_expression_bitvector_variables(&segment.end, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_c_expression_outcome_bitvector_variables(
    outcome: &CExpressionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    if let CExpressionOutcome::Value(value) = outcome {
        collect_c_value_bitvector_variables(value, variables);
    }
}

pub(in crate::kernel) fn collect_c_statement_outcome_bitvector_variables(
    outcome: &CStatementOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CStatementOutcome::Normal(state) => collect_c_state_bitvector_variables(state, variables),
        CStatementOutcome::Break(state) | CStatementOutcome::Continue(state) => {
            collect_c_state_bitvector_variables(state, variables)
        }
        CStatementOutcome::Return { value, state } => {
            collect_c_value_bitvector_variables(value, variables);
            collect_c_state_bitvector_variables(state, variables);
        }
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => {}
    }
}

pub(in crate::kernel) fn collect_c_function_outcome_bitvector_variables(
    outcome: &CFunctionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CFunctionOutcome::Return { value, state } => {
            collect_c_value_bitvector_variables(value, variables);
            collect_c_state_bitvector_variables(state, variables);
        }
        CFunctionOutcome::VerificationDiverges
        | CFunctionOutcome::UndefinedBehavior(_)
        | CFunctionOutcome::RuntimeError(_) => {}
    }
}

pub(in crate::kernel) fn collect_c_state_bitvector_variables(
    state: &CState,
    variables: &mut BTreeSet<Variable>,
) {
    for binding in state.locals.bindings.values() {
        match binding {
            CLocalBinding::Object { value, .. } => {
                collect_c_value_bitvector_variables(value, variables)
            }
            CLocalBinding::UninitializedObject { .. } => {}
            CLocalBinding::GlobalObject { .. } => {}
            CLocalBinding::ArrayObject { .. } => {}
            CLocalBinding::AggregateObject { .. } => {}
        }
    }
    collect_memory_bitvector_variables(&state.memory, variables);
    collect_resource_context_bitvector_variables(&state.resources, variables);
    for population in state.counted_populations.iter() {
        for argument in &population.arguments {
            collect_c_value_bitvector_variables(argument, variables);
        }
        collect_c_value_bitvector_variables(&CValue::Int32(population.count.clone()), variables);
    }
}

pub(in crate::kernel) fn collect_resource_context_bitvector_variables(
    resources: &ResourceContext,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in resources.facts() {
        collect_resource_bitvector_variables(resource, variables);
    }
}

pub(in crate::kernel) fn collect_resource_bitvector_variables(
    resource: &CResourceFact,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_resource_bitvector_variables(resource.resource(), variables);
}

pub(in crate::kernel) fn collect_c_resource_bitvector_variables(
    resource: &CResource,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        CResource::Memory(range) => collect_c_memory_range_bitvector_variables(range, variables),
        CResource::Composite { arguments, .. } | CResource::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_value_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_c_function_bitvector_variables(
    function: &CFunction,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in function.resource_requires() {
        collect_resource_spec_bitvector_variables(resource, variables);
    }
    for resource in function.resource_ensures() {
        collect_resource_spec_bitvector_variables(resource, variables);
    }
    for resource in function.resource_constructors() {
        collect_resource_spec_bitvector_variables(resource, variables);
    }
    for proposition in function.contract_requires() {
        collect_spec_proposition_bitvector_variables(proposition, variables);
    }
    for proposition in function.contract_ensures() {
        collect_spec_proposition_bitvector_variables(proposition, variables);
    }
    for segment in function.contract_mutable() {
        collect_c_expression_bitvector_variables(&segment.base, variables);
        collect_c_expression_bitvector_variables(&segment.start, variables);
        collect_c_expression_bitvector_variables(&segment.end, variables);
        if let Some(guard) = segment.guard() {
            collect_spec_proposition_bitvector_variables(guard, variables);
        }
    }
    collect_c_statement_bitvector_variables(function.body(), variables);
}

pub(in crate::kernel) fn collect_resource_spec_bitvector_variables(
    resource: &CResourceSpec,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        CResourceSpec::Quantified { quantity, resource } => {
            collect_c_expression_bitvector_variables(quantity, variables);
            collect_resource_spec_bitvector_variables(resource, variables);
        }
        CResourceSpec::ViewMemory(segment) => {
            collect_c_expression_bitvector_variables(&segment.base, variables);
            collect_c_expression_bitvector_variables(&segment.start, variables);
            collect_c_expression_bitvector_variables(&segment.end, variables);
            if let Some(guard) = segment.guard() {
                collect_spec_proposition_bitvector_variables(guard, variables);
            }
        }
        CResourceSpec::OwnMemory(segment) => {
            collect_c_expression_bitvector_variables(&segment.base, variables);
            collect_c_expression_bitvector_variables(&segment.start, variables);
            collect_c_expression_bitvector_variables(&segment.end, variables);
            if let Some(guard) = segment.guard() {
                collect_spec_proposition_bitvector_variables(guard, variables);
            }
        }
        CResourceSpec::Composite { arguments, .. } | CResourceSpec::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_c_function_specification_bitvector_variables(
    specification: &CFunctionSpecification,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_state_bitvector_variables(specification.state(), variables);
    for argument in specification.arguments() {
        collect_c_expression_bitvector_variables(argument, variables);
    }
    for requirement in specification.requires() {
        collect_proposition_bitvector_variables(requirement, variables);
    }
    collect_c_function_outcome_bitvector_variables(specification.outcome(), variables);
}

pub(in crate::kernel) fn collect_assumption_variables(
    assumptions: &PureFactContext,
    variables: &mut BTreeSet<Variable>,
) {
    for proposition in assumptions.pure_facts() {
        collect_proposition_bitvector_variables(&proposition, variables);
    }
}

pub(in crate::kernel) fn collect_execution_environment_variables(
    environment: &CExecutionEnvironment,
    variables: &mut BTreeSet<Variable>,
) {
    variables.extend(
        execution_environment_variable_index(environment)
            .iter()
            .copied(),
    );
}

pub(in crate::kernel) fn execution_environment_variable_index(
    environment: &CExecutionEnvironment,
) -> std::sync::Arc<BTreeSet<Variable>> {
    environment.variable_index.get_or_init(|| {
        let mut variables = BTreeSet::new();
        collect_execution_environment_variables_uncached(environment, &mut variables);
        variables
    })
}

fn collect_execution_environment_variables_uncached(
    environment: &CExecutionEnvironment,
    variables: &mut BTreeSet<Variable>,
) {
    for function in environment.functions.values() {
        collect_c_function_bitvector_variables(function, variables);
    }
    for rule in environment.verified_function_rules.values() {
        collect_c_function_bitvector_variables(&rule.function, variables);
    }
    for rule in environment.verified_loop_rules.iter() {
        collect_c_state_bitvector_variables(&rule.symbolic_entry_state, variables);
        collect_c_statement_bitvector_variables(&rule.loop_statement, variables);
        collect_assumption_variables(&rule.required_assumptions, variables);
        for path in &rule.paths {
            collect_c_statement_outcome_bitvector_variables(&path.outcome, variables);
            for fact in &path.facts {
                collect_proposition_bitvector_variables(fact.proposition(), variables);
            }
            for obligation in &path.obligations {
                collect_proposition_bitvector_variables(obligation.proposition(), variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_c_memory_range_bitvector_variables(
    range: &CMemoryRange,
    variables: &mut BTreeSet<Variable>,
) {
    collect_pointer_bitvector_variables(&range.base, variables);
    collect_bitvector_variables(&range.start, variables);
    collect_bitvector_variables(&range.end, variables);
}

pub(crate) fn resource_context_has_read(
    resources: &ResourceContext,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    // Resource-backed reads are loadability checks too: a view retained
    // across an opaque effect may name its bounds with load atoms from the
    // pre-effect snapshot, while the expression being loaded names the same
    // cells at the current snapshot. Keep the snapshot-DAG bridge scoped to
    // this resource-backed access query, just as `proves_memory_loadable`
    // does for proposition-backed loadability facts.
    crate::kernel::api::with_extended_dag_bridging(|| {
        resources.permits_memory_read(pointer, byte_width, assumptions)
    })
}

pub(in crate::kernel) fn resource_context_has_structural_read(
    resources: &ResourceContext,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    resources.permits_memory_read_structurally(pointer, byte_width, assumptions)
}

pub(in crate::kernel) fn collect_condition_bitvector_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64Equal(left, right)
        | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_variables(term, variables));
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_bitvector_variables(left, variables);
            collect_pointer_bitvector_variables(right, variables);
        }
    }
}

pub(in crate::kernel) fn collect_bitvector_variables(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
) {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            variables.insert(*variable);
            // A load variable denotes its load, so the variables
            // of that load's address (a bound index, a loop counter) are
            // free in the term: a case split or substitution keyed on the
            // term's variables must see them.
            if crate::kernel::is_load_variable(variable)
                && let Some((memory, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                collect_memory_bitvector_variables(&memory, variables);
                collect_pointer_bitvector_variables(&pointer, variables);
            }
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right)
        | Bitvector32Term::Int64Add(left, right)
        | Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::Int64Divide(left, right)
        | Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64Add(left, right)
        | Bitvector32Term::UInt64Subtract(left, right)
        | Bitvector32Term::UInt64Multiply(left, right)
        | Bitvector32Term::UInt64Divide(left, right)
        | Bitvector32Term::UInt64Remainder(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right)
        | Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value)
        | Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            collect_bitvector_variables(value, variables);
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_variables(condition, variables);
            collect_bitvector_variables(then_term, variables);
            collect_bitvector_variables(else_term, variables);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_variables(start, variables);
            collect_bitvector_variables(end, variables);
            collect_bitvector_variables(initial, variables);
            collect_bitvector_variables(body, variables);
            variables.remove(accumulator);
            variables.remove(item);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_variables(argument, variables);
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_bitvector_variables(pointer, variables);
        }
    }
}

pub(in crate::kernel) fn collect_pointer_offset_bitvector_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_variables(value, variables);
        }
    }
}

pub(in crate::kernel) fn collect_pointer_bitvector_variables(
    pointer: &Pointer,
    variables: &mut BTreeSet<Variable>,
) {
    if let PointerBlock::Symbolic(variable) = pointer.block {
        variables.insert(variable);
    }
    collect_pointer_offset_bitvector_variables(&pointer.offset, variables);
}

pub(in crate::kernel) fn collect_memory_bitvector_variables(
    memory: &CMemory,
    variables: &mut BTreeSet<Variable>,
) {
    for (block, contents) in memory.blocks.iter() {
        if let PointerBlock::Symbolic(variable) = block {
            variables.insert(*variable);
        }
        collect_bitvector_variables(contents.size(), variables);
    }
    for (pointer, value) in memory.cells.iter() {
        collect_pointer_bitvector_variables(pointer, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
}

pub(in crate::kernel) fn collect_c_value_bitvector_variables(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        CValue::Void => {}
        CValue::Int16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => collect_bitvector_variables(bits, variables),
        CValue::Pointer(pointer) => collect_pointer_bitvector_variables(pointer, variables),
    }
}
