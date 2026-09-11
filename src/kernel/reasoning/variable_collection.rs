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
        Term::Integer(integer) => collect_integer_variables(integer, variables),
        Term::PointerOffset(offset) => {
            collect_pointer_offset_bitvector_variables(offset, variables)
        }
        Term::CValue(value) => collect_c_value_bitvector_variables(value, variables),
        Term::Sequence(sequence) => collect_sequence_bitvector_variables(sequence, variables),
        Term::Algebraic(term) => collect_algebraic_term_bitvector_variables(term, variables),
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

fn collect_algebraic_term_bitvector_variables(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_bitvector_variables(field, variables);
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_term_bitvector_variables(scrutinee, variables);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bitvector_variables(binding, variables);
                }
                collect_algebraic_term_bitvector_variables(&arm.body, variables);
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                match argument {
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_term_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Integer(value) => {
                        collect_integer_variables(value, variables)
                    }
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bitvector_variables(memory, variables);
                        collect_c_value_bitvector_variables(pointer, variables);
                    }
                }
            }
        }
    }
}

fn collect_algebraic_value_bitvector_variables(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        AlgebraicValue::C(value) => collect_c_value_bitvector_variables(value, variables),
        AlgebraicValue::Integer(value) => collect_integer_variables(value, variables),
        AlgebraicValue::Algebraic(value) => {
            collect_algebraic_term_bitvector_variables(value, variables)
        }
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
        CStatement::CopyAggregate { target, source, .. } => {
            collect_c_expression_bitvector_variables(target, variables);
            collect_c_expression_bitvector_variables(source, variables);
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
    _memory: &SpecMemory,
    _variables: &mut BTreeSet<Variable>,
) {
    // A specification memory is an execution snapshot. Its blocks and cells
    // are opaque to lexical variable collection; callers still visit the
    // explicit pointer and expression payloads adjacent to this snapshot.
}

pub(in crate::kernel) fn collect_spec_expression_bitvector_variables(
    expression: &SpecExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        SpecExpression::ResourceField { .. } => {}
        SpecExpression::IntegerToMachine { value, .. } => {
            collect_spec_integer_variables(value, variables);
        }
        SpecExpression::Value(value) => collect_c_value_bitvector_variables(value, variables),
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_spec_algebraic_expression_bitvector_variables(scrutinee, variables);
            for arm in arms {
                collect_spec_expression_bitvector_variables(&arm.body, variables);
            }
        }
        SpecExpression::CExpression(expression) => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                collect_spec_expression_bitvector_variables(argument, variables);
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
        SpecExpression::BitwiseNot(expression) | SpecExpression::Cast(expression, _) => {
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
                collect_spec_function_argument_bitvector_variables(argument, variables);
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
        SpecProposition::IntegerComparison { left, right, .. } => {
            collect_spec_integer_variables(left, variables);
            collect_spec_integer_variables(right, variables);
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            collect_spec_algebraic_expression_bitvector_variables(left, variables);
            collect_spec_algebraic_expression_bitvector_variables(right, variables);
        }
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
        | SpecProposition::ForAllInteger { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsInteger { variable, body, .. }
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

pub(crate) fn collect_spec_integer_variables(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            SpecIntegerExpression::ResourceField(_) => {}
            SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
                collect_spec_algebraic_expression_bitvector_variables(scrutinee, variables);
                for arm in arms {
                    collect_spec_integer_variables(&arm.body, variables);
                }
            }
            SpecIntegerExpression::Term(term) => collect_integer_variables(term, variables),
            SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
                for argument in arguments {
                    match argument {
                        SpecPureFunctionArgument::Value(value) => {
                            collect_spec_expression_bitvector_variables(value, variables)
                        }
                        SpecPureFunctionArgument::Integer(value) => {
                            collect_spec_integer_variables(value, variables)
                        }
                        SpecPureFunctionArgument::Algebraic(value) => {
                            collect_spec_algebraic_expression_bitvector_variables(value, variables)
                        }
                        SpecPureFunctionArgument::ArrayRef { pointer, .. } => {
                            collect_spec_expression_bitvector_variables(pointer, variables)
                        }
                    }
                }
            }
            SpecIntegerExpression::FromMachine(value) => {
                collect_spec_expression_bitvector_variables(value, variables)
            }
            SpecIntegerExpression::Negate(inner) => pending.push(inner),
            SpecIntegerExpression::Add(left, right)
            | SpecIntegerExpression::Subtract(left, right)
            | SpecIntegerExpression::Multiply(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            SpecIntegerExpression::RangeFold {
                index,
                initial,
                body,
                ..
            } => {
                match index {
                    SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                        collect_spec_expression_bitvector_variables(start, variables);
                        collect_spec_expression_bitvector_variables(end, variables);
                    }
                    SpecIntegerRangeFoldIndex::Integer { start, end } => {
                        pending.push(start);
                        pending.push(end);
                    }
                }
                pending.push(initial);
                pending.push(body);
            }
        }
    }
}

/// Collect every variable identity reachable from a specification-side
/// Integer expression, including identities introduced by Integer and C
/// range-fold binders.
///
/// [`collect_spec_integer_variables`] is intentionally a free-variable
/// collector: premise indexing must not connect a fact outside a binder to a
/// variable that is local to that binder.  Fresh lowering has the opposite
/// requirement.  A newly allocated binder must be fresh from all identities
/// already present in a captured value, including bound identities and
/// mathematical Integers nested in machine payloads.  Keep that distinction
/// here, next to the term-level collectors, rather than duplicating a partial
/// specification walk in the surface elaborator.
pub(crate) fn collect_spec_integer_bound_variables(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
) {
    collect_spec_integer_variables(expression, variables);
    let mut integer_seen = BTreeSet::new();
    collect_spec_integer_bound_variables_inner(expression, variables, &mut integer_seen);
}

fn collect_spec_integer_bound_variables_inner(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match expression {
        SpecIntegerExpression::ResourceField(projection) => {
            variables.insert(projection.identity);
        }
        SpecIntegerExpression::Term(term) => {
            collect_integer_bound_identities(term, variables, integer_seen);
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_spec_algebraic_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                for variable in arm.binding_variables.iter().flatten() {
                    variables.insert(*variable);
                }
                collect_spec_integer_bound_variables_inner(&arm.body, variables, integer_seen);
            }
        }
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_spec_integer_bound_argument(argument, variables, integer_seen);
            }
        }
        SpecIntegerExpression::FromMachine(expression) => {
            collect_spec_integer_bound_expression(expression, variables, integer_seen);
        }
        SpecIntegerExpression::Negate(value) => {
            collect_spec_integer_bound_variables_inner(value, variables, integer_seen);
        }
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => {
            collect_spec_integer_bound_variables_inner(left, variables, integer_seen);
            collect_spec_integer_bound_variables_inner(right, variables, integer_seen);
        }
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            variables.insert(*accumulator);
            variables.insert(*item);
            match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                    collect_spec_integer_bound_expression(start, variables, integer_seen);
                    collect_spec_integer_bound_expression(end, variables, integer_seen);
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    collect_spec_integer_bound_variables_inner(start, variables, integer_seen);
                    collect_spec_integer_bound_variables_inner(end, variables, integer_seen);
                }
            }
            collect_spec_integer_bound_variables_inner(initial, variables, integer_seen);
            collect_spec_integer_bound_variables_inner(body, variables, integer_seen);
        }
    }
}

fn collect_integer_bound_identities(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::Machine(value) => {
            collect_bitvector_integer_variables(value.value(), variables);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_pure_argument_bound_identities(argument, variables, integer_seen);
            }
        }
        IntegerTerm::Negate(value) => {
            collect_shared_integer_bound_identities(value, variables, integer_seen);
        }
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_shared_integer_bound_identities(left, variables, integer_seen);
            collect_shared_integer_bound_identities(right, variables, integer_seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_term_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_identities(binding, variables, integer_seen);
                }
                collect_shared_integer_bound_identities(&arm.body, variables, integer_seen);
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            variables.insert(*accumulator);
            variables.insert(*item);
            match index {
                IntegerRangeFoldIndex::Int32 { start, end } => {
                    collect_bitvector_integer_variables(start.value(), variables);
                    collect_bitvector_integer_variables(end.value(), variables);
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_bound_identities(start, variables, integer_seen);
                    collect_shared_integer_bound_identities(end, variables, integer_seen);
                }
            }
            collect_shared_integer_bound_identities(initial, variables, integer_seen);
            collect_shared_integer_bound_identities(body, variables, integer_seen);
        }
    }
}

fn collect_shared_integer_bound_identities(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if integer_seen.insert(term.id()) {
        collect_integer_bound_identities(term.as_ref(), variables, integer_seen);
    }
}

fn collect_pure_argument_bound_identities(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match argument {
        PureFunctionArgument::Value(value) => {
            collect_c_value_bound_identities(value, variables, integer_seen);
        }
        PureFunctionArgument::Integer(value) => {
            collect_shared_integer_bound_identities(value, variables, integer_seen);
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_algebraic_term_bound_identities(value, variables, integer_seen);
        }
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_c_value_bound_identities(pointer, variables, integer_seen);
        }
    }
}

fn collect_algebraic_term_bound_identities(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => {
            variables.insert(*variable);
        }
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_bound_identities(field, variables, integer_seen);
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_term_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_identities(binding, variables, integer_seen);
                }
                collect_algebraic_term_bound_identities(&arm.body, variables, integer_seen);
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_pure_argument_bound_identities(argument, variables, integer_seen);
            }
        }
    }
}

fn collect_algebraic_value_bound_identities(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match value {
        AlgebraicValue::C(value) => {
            collect_c_value_bound_identities(value, variables, integer_seen);
        }
        AlgebraicValue::Integer(value) => {
            collect_integer_bound_identities(value, variables, integer_seen);
        }
        AlgebraicValue::Algebraic(value) => {
            collect_algebraic_term_bound_identities(value, variables, integer_seen);
        }
    }
}

fn collect_c_value_bound_identities(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
    _integer_seen: &mut BTreeSet<u64>,
) {
    match value {
        CValue::Void | CValue::Pointer(_) => {}
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::Int32(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => {
            collect_bitvector_integer_variables(bits, variables);
        }
    }
}

fn collect_spec_integer_bound_argument(
    argument: &SpecPureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match argument {
        SpecPureFunctionArgument::Value(value) => {
            collect_spec_integer_bound_expression(value, variables, integer_seen);
        }
        SpecPureFunctionArgument::Integer(value) => {
            collect_spec_integer_bound_variables_inner(value, variables, integer_seen);
        }
        SpecPureFunctionArgument::Algebraic(value) => {
            collect_spec_algebraic_bound_identities(value, variables, integer_seen);
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            collect_spec_memory_bound_identities(memory, variables, integer_seen);
            collect_spec_integer_bound_expression(pointer, variables, integer_seen);
        }
    }
}

fn collect_spec_integer_bound_expression(
    expression: &SpecExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match expression {
        SpecExpression::Value(value) => {
            collect_c_value_bound_identities(value, variables, integer_seen);
        }
        SpecExpression::IntegerToMachine { value, .. } => {
            collect_spec_integer_bound_variables_inner(value, variables, integer_seen);
        }
        SpecExpression::ResourceField { projection, .. } => {
            variables.insert(projection.identity);
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_spec_algebraic_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                collect_spec_integer_bound_expression(&arm.body, variables, integer_seen);
            }
        }
        SpecExpression::CExpression(expression) => {
            collect_c_expression_bound_identities(expression, variables, integer_seen);
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                collect_spec_integer_bound_expression(argument, variables, integer_seen);
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
            collect_spec_integer_bound_expression(left, variables, integer_seen);
            collect_spec_integer_bound_expression(right, variables, integer_seen);
        }
        SpecExpression::BitwiseNot(expression)
        | SpecExpression::Cast(expression, _)
        | SpecExpression::LoopEntrySnapshot(expression) => {
            collect_spec_integer_bound_expression(expression, variables, integer_seen);
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_spec_proposition_bound_identities(condition, variables, integer_seen);
            collect_spec_integer_bound_expression(then_branch, variables, integer_seen);
            collect_spec_integer_bound_expression(else_branch, variables, integer_seen);
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_spec_integer_bound_expression(start, variables, integer_seen);
            collect_spec_integer_bound_expression(end, variables, integer_seen);
            collect_spec_integer_bound_expression(initial, variables, integer_seen);
            collect_spec_integer_bound_expression(body, variables, integer_seen);
        }
        SpecExpression::Let { value, body, .. } => {
            collect_spec_integer_bound_expression(value, variables, integer_seen);
            collect_spec_integer_bound_expression(body, variables, integer_seen);
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_spec_integer_bound_argument(argument, variables, integer_seen);
            }
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            collect_spec_integer_bound_expression(pointer, variables, integer_seen);
            collect_spec_integer_bound_expression(elements, variables, integer_seen);
        }
        SpecExpression::MemoryLoad {
            memory, pointer, ..
        } => {
            collect_spec_memory_bound_identities(memory, variables, integer_seen);
            collect_spec_integer_bound_expression(pointer, variables, integer_seen);
        }
    }
}

fn collect_c_expression_bound_identities(
    expression: &CExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match expression {
        CExpression::Value(value) => {
            collect_c_value_bound_identities(value, variables, integer_seen);
        }
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::BitwiseNot(expression) => {
            collect_c_expression_bound_identities(expression, variables, integer_seen);
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bound_identities(condition, variables, integer_seen);
            collect_c_expression_bound_identities(then_branch, variables, integer_seen);
            collect_c_expression_bound_identities(else_branch, variables, integer_seen);
        }
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_c_expression_bound_identities(pointer, variables, integer_seen);
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
            collect_c_expression_bound_identities(left, variables, integer_seen);
            collect_c_expression_bound_identities(right, variables, integer_seen);
        }
    }
}

fn collect_spec_algebraic_bound_identities(
    expression: &SpecAlgebraicExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(variable) => {
            variables.insert(*variable);
        }
        SpecAlgebraicExpressionNode::Binding(_) | SpecAlgebraicExpressionNode::ResourceField(_) => {
        }
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(value) => {
                        collect_spec_integer_bound_expression(value, variables, integer_seen);
                    }
                    SpecAlgebraicValue::Integer(value) => {
                        collect_spec_integer_bound_variables_inner(value, variables, integer_seen);
                    }
                    SpecAlgebraicValue::Algebraic(value) => {
                        collect_spec_algebraic_bound_identities(value, variables, integer_seen);
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            collect_spec_algebraic_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                collect_spec_algebraic_bound_identities(&arm.body, variables, integer_seen);
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_spec_integer_bound_argument(argument, variables, integer_seen);
            }
        }
    }
}

fn collect_spec_sequence_bound_identities(
    sequence: &SpecSequenceExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match sequence {
        SpecSequenceExpression::Literal(values) => {
            for value in values {
                collect_spec_integer_bound_expression(value, variables, integer_seen);
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            collect_spec_sequence_bound_identities(left, variables, integer_seen);
            collect_spec_sequence_bound_identities(right, variables, integer_seen);
        }
    }
}

fn collect_spec_memory_bound_identities(
    _memory: &SpecMemory,
    _variables: &mut BTreeSet<Variable>,
    _integer_seen: &mut BTreeSet<u64>,
) {
    // A SpecMemory is a captured execution snapshot, not lexical input to
    // the expression.  Its blocks, cells, and union overlays are therefore
    // opaque to freshness collection; callers recurse through explicit
    // pointer and expression payloads adjacent to the snapshot instead.
}

fn collect_spec_resource_bound_identities(
    resource: &SpecResource,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            collect_spec_integer_bound_expression(base, variables, integer_seen);
            collect_spec_integer_bound_expression(start, variables, integer_seen);
            collect_spec_integer_bound_expression(end, variables, integer_seen);
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                collect_spec_integer_bound_expression(argument, variables, integer_seen);
            }
        }
    }
}

fn collect_spec_proposition_bound_identities(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    match proposition {
        SpecProposition::IntegerComparison { left, right, .. } => {
            collect_spec_integer_bound_variables_inner(left, variables, integer_seen);
            collect_spec_integer_bound_variables_inner(right, variables, integer_seen);
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            collect_spec_algebraic_bound_identities(left, variables, integer_seen);
            collect_spec_algebraic_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            collect_spec_integer_bound_expression(element, variables, integer_seen);
            collect_spec_sequence_bound_identities(sequence, variables, integer_seen);
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            collect_spec_sequence_bound_identities(left, variables, integer_seen);
            collect_spec_sequence_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::Comparison { left, right, .. } => {
            collect_spec_integer_bound_expression(left, variables, integer_seen);
            collect_spec_integer_bound_expression(right, variables, integer_seen);
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            collect_spec_integer_bound_expression(expression, variables, integer_seen);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            collect_spec_proposition_bound_identities(left, variables, integer_seen);
            collect_spec_proposition_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::Not(body) => {
            collect_spec_proposition_bound_identities(body, variables, integer_seen);
        }
        SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllInteger { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsInteger { variable, body, .. }
        | SpecProposition::ExistsPointer { variable, body, .. } => {
            variables.insert(*variable);
            collect_spec_proposition_bound_identities(body, variables, integer_seen);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(value) => {
                        collect_spec_integer_bound_expression(value, variables, integer_seen);
                    }
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        collect_spec_memory_bound_identities(memory, variables, integer_seen);
                        collect_spec_integer_bound_expression(pointer, variables, integer_seen);
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            collect_spec_resource_bound_identities(left, variables, integer_seen);
            collect_spec_resource_bound_identities(right, variables, integer_seen);
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            collect_spec_memory_bound_identities(memory, variables, integer_seen);
            collect_spec_integer_bound_expression(base, variables, integer_seen);
            collect_spec_integer_bound_expression(start, variables, integer_seen);
            collect_spec_integer_bound_expression(end, variables, integer_seen);
        }
    }
}

pub(crate) fn collect_spec_algebraic_expression_bitvector_variables(
    expression: &SpecAlgebraicExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(_) => {}
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => {}
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(field) => {
                        collect_spec_expression_bitvector_variables(field, variables)
                    }
                    SpecAlgebraicValue::Integer(value) => {
                        collect_spec_integer_variables(value, variables)
                    }
                    SpecAlgebraicValue::Algebraic(field) => {
                        collect_spec_algebraic_expression_bitvector_variables(field, variables)
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            collect_spec_algebraic_expression_bitvector_variables(scrutinee, variables);
            for arm in arms {
                collect_spec_algebraic_expression_bitvector_variables(&arm.body, variables);
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_spec_function_argument_bitvector_variables(argument, variables);
            }
        }
    }
}

fn collect_spec_function_argument_bitvector_variables(
    argument: &SpecPureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
) {
    match argument {
        SpecPureFunctionArgument::Integer(_) => {}
        SpecPureFunctionArgument::Value(expression) => {
            collect_spec_expression_bitvector_variables(expression, variables)
        }
        SpecPureFunctionArgument::Algebraic(expression) => {
            collect_spec_algebraic_expression_bitvector_variables(expression, variables)
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            collect_spec_memory_bitvector_variables(memory, variables);
            collect_spec_expression_bitvector_variables(pointer, variables);
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
    collect_resource_context_bitvector_variables(&state.instance_field_scope, variables);
    for population in state.counted_populations.iter() {
        for argument in population.arguments.iter() {
            collect_algebraic_value_bitvector_variables(argument, variables);
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
        CResource::Instance(instance) => {
            for value in instance.arguments.iter().chain(instance.fields.iter()) {
                collect_algebraic_value_bitvector_variables(value, variables);
            }
        }
        CResource::Memory(range) => collect_c_memory_range_bitvector_variables(range, variables),
        CResource::Composite { arguments, .. } | CResource::Token { arguments, .. } => {
            for argument in arguments.iter() {
                collect_algebraic_value_bitvector_variables(argument, variables);
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
        CResourceSpec::Instance { resource, .. } => {
            collect_resource_spec_bitvector_variables(resource, variables)
        }
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
        collect_c_function_bound_variables(function, variables);
    }
    for contract in environment.function_contracts.values() {
        collect_c_function_bitvector_variables(&contract.function, variables);
        collect_c_function_bound_variables(&contract.function, variables);
    }
    for rule in environment.verified_function_rules.values() {
        collect_c_function_bitvector_variables(&rule.function, variables);
        collect_c_function_bound_variables(&rule.function, variables);
    }
    for rule in environment.verified_loop_rules.iter() {
        collect_c_state_bitvector_variables(&rule.symbolic_entry_state, variables);
        collect_c_state_bound_variables(&rule.symbolic_entry_state, variables);
        collect_c_statement_bitvector_variables(&rule.loop_statement, variables);
        collect_c_statement_bound_variables(&rule.loop_statement, variables);
        collect_assumption_variables(&rule.required_assumptions, variables);
        for fact in rule.required_assumptions.pure_facts() {
            collect_proposition_bound_variables(&fact, variables);
        }
        for path in &rule.paths {
            collect_c_statement_outcome_bitvector_variables(&path.outcome, variables);
            collect_statement_outcome_bound_variables(&path.outcome, variables);
            for fact in &path.facts {
                collect_proposition_bitvector_variables(fact.proposition(), variables);
                collect_proposition_bound_variables(fact.proposition(), variables);
            }
            for obligation in &path.obligations {
                collect_proposition_bitvector_variables(obligation.proposition(), variables);
                collect_proposition_bound_variables(obligation.proposition(), variables);
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

/// Charge one collector node and report whether the checked fold analysis has
/// already exhausted its deterministic budget.  The instrumentation scope is
/// inactive for legacy callers, so those callers retain their existing work
/// accounting while the checked constructors can stop before descending into
/// another payload.
#[inline]
fn checked_collection_checkpoint() -> bool {
    #[cfg(test)]
    crate::instrumentation::record_checked_collection_attempt();
    crate::instrumentation::record_deterministic_work(1);
    crate::instrumentation::checked_collection_exhausted()
}

pub(in crate::kernel) fn collect_condition_bitvector_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_algebraic_term_bitvector_variables(left, variables);
            collect_algebraic_term_bitvector_variables(right, variables);
        }
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
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            collect_integer_variables(left, variables);
            collect_integer_variables(right, variables);
        }
    }
}

pub(crate) fn collect_integer_variables(term: &IntegerTerm, variables: &mut BTreeSet<Variable>) {
    let mut seen = BTreeSet::new();
    collect_integer_variables_seen(term, variables, &mut seen);
}

/// Collect variables used as mathematical Integer binders, excluding C
/// variables embedded in `IntegerTerm::Machine` nodes.  Integer-to-machine
/// payloads nested inside those C terms remain visible because they carry a
/// mathematical Integer expression of their own.
pub(crate) fn collect_integer_carrier_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = BTreeSet::new();
    collect_integer_carrier_variables_seen(term, variables, &mut seen);
}

fn collect_integer_carrier_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Machine(value) => {
            collect_bitvector_integer_variables_seen(value.value(), variables, seen)
        }
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                if let PureFunctionArgument::Integer(value) = argument {
                    collect_shared_integer_carrier_variables_seen(value, variables, seen);
                }
            }
        }
        IntegerTerm::Negate(value) => {
            collect_shared_integer_carrier_variables_seen(value, variables, seen)
        }
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_shared_integer_carrier_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(right, variables, seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_algebraic_value_integer_variables(binding, variables, seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_shared_integer_carrier_variables_seen(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            if let IntegerRangeFoldIndex::Integer { start, end } = index {
                collect_shared_integer_carrier_variables_seen(start, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_shared_integer_carrier_variables_seen(end, variables, seen);
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(initial, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(body, variables, seen);
            variables.insert(*accumulator);
            if matches!(index, IntegerRangeFoldIndex::Integer { .. }) {
                variables.insert(*item);
            }
        }
    }
}

fn collect_shared_integer_carrier_variables_seen(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    if seen.insert(term.id()) {
        collect_integer_carrier_variables_seen(term.as_ref(), variables, seen);
    }
}

/// Collect mathematical Integer variables nested in a machine term.  Memory
/// snapshots are intentionally opaque here: only the address payload of a
/// load can carry a variable relevant to a lexical substitution, and that
/// payload is a machine term with no Integer carrier.
pub(crate) fn collect_bitvector_integer_variables(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = BTreeSet::new();
    collect_bitvector_integer_variables_seen(term, variables, &mut seen);
}

fn collect_bitvector_integer_variables_seen(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(_, pointer) | Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_integer_variables(pointer, variables, seen)
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_shared_integer_variables_seen(value, variables, seen);
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
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            collect_bitvector_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(right, variables, seen);
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            collect_bitvector_integer_variables_seen(value, variables, seen)
        }
        Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_bitvector_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(right, variables, seen);
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_integer_variables(condition, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(then_term, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(else_term, variables, seen);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_integer_variables_seen(start, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(end, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(initial, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(body, variables, seen);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_integer_variables_seen(argument, variables, seen);
            }
        }
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_pure_argument_integer_variables(argument, variables, seen);
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_algebraic_value_integer_variables(binding, variables, seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_integer_variables_seen(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
    }
}

fn collect_pointer_integer_variables(
    pointer: &Pointer,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    collect_pointer_offset_integer_variables(&pointer.offset, variables, seen);
}

fn collect_pointer_offset_integer_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_integer_variables(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_integer_variables(right, variables, seen);
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_integer_variables_seen(value, variables, seen);
        }
    }
}

fn collect_shared_integer_variables_seen(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    if seen.insert(term.id()) {
        collect_integer_free_variables_seen(term.as_ref(), variables, seen);
    }
}

fn collect_integer_free_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Machine(value) => {
            collect_bitvector_integer_variables_seen(value.value(), variables, seen)
        }
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                match argument {
                    PureFunctionArgument::Integer(value) => {
                        collect_shared_integer_variables_seen(value, variables, seen)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_free_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::ArrayRef { pointer, .. } => {
                        collect_c_value_integer_variables(pointer, variables, seen)
                    }
                }
            }
        }
        IntegerTerm::Negate(value) => collect_shared_integer_variables_seen(value, variables, seen),
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_shared_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(right, variables, seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_free_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                let mut body_variables = BTreeSet::new();
                collect_shared_integer_variables_seen(
                    &arm.body,
                    &mut body_variables,
                    &mut BTreeSet::new(),
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                for binding in &arm.bindings {
                    if let AlgebraicValue::Integer(value) = binding
                        && let IntegerTerm::Variable(variable) = value
                    {
                        body_variables.remove(variable);
                    }
                }
                variables.extend(body_variables);
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            if let IntegerRangeFoldIndex::Integer { start, end } = index {
                collect_shared_integer_variables_seen(start, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_shared_integer_variables_seen(end, variables, seen);
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(initial, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            let mut body_variables = BTreeSet::new();
            collect_shared_integer_variables_seen(body, &mut body_variables, &mut BTreeSet::new());
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            body_variables.remove(accumulator);
            if matches!(index, IntegerRangeFoldIndex::Integer { .. }) {
                body_variables.remove(item);
            }
            variables.extend(body_variables);
        }
    }
}

fn collect_algebraic_free_integer_variables(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                match field {
                    AlgebraicValue::C(value) => {
                        collect_c_value_integer_variables(value, variables, seen)
                    }
                    AlgebraicValue::Integer(value) => {
                        collect_integer_free_variables_seen(value, variables, seen)
                    }
                    AlgebraicValue::Algebraic(value) => {
                        collect_algebraic_free_integer_variables(value, variables, seen)
                    }
                }
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_free_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    match binding {
                        AlgebraicValue::C(value) => {
                            collect_c_value_integer_variables(value, variables, seen)
                        }
                        AlgebraicValue::Integer(value) => {
                            collect_integer_free_variables_seen(value, variables, seen)
                        }
                        AlgebraicValue::Algebraic(value) => {
                            collect_algebraic_free_integer_variables(value, variables, seen)
                        }
                    }
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_algebraic_free_integer_variables(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                match argument {
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::Integer(value) => {
                        collect_shared_integer_variables_seen(value, variables, seen)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_free_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::ArrayRef { pointer, .. } => {
                        collect_c_value_integer_variables(pointer, variables, seen)
                    }
                }
            }
        }
    }
}

/// Collect free mathematical Integer variables, preserving the Integer/C
/// carrier boundary through pure and algebraic arguments.
pub(crate) fn collect_integer_free_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = BTreeSet::new();
    collect_integer_free_variables_seen(term, variables, &mut seen);
}

fn collect_condition_integer_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match condition {
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            collect_shared_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(right, variables, seen);
        }
        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_algebraic_integer_variables(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_algebraic_integer_variables(right, variables, seen);
        }
        _ => {}
    }
}

fn collect_pure_argument_integer_variables(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match argument {
        PureFunctionArgument::Integer(value) => {
            collect_shared_integer_variables_seen(value, variables, seen)
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_algebraic_integer_variables(value, variables, seen)
        }
        PureFunctionArgument::Value(value) => {
            collect_c_value_integer_variables(value, variables, seen)
        }
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_c_value_integer_variables(pointer, variables, seen)
        }
    }
}

fn collect_c_value_integer_variables(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        CValue::Void => {}
        CValue::Bool(value)
        | CValue::Int16(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value)
        | CValue::Int32(value)
        | CValue::UInt32(value)
        | CValue::Int64(value)
        | CValue::UInt64(value)
        | CValue::Float32(value)
        | CValue::Float64(value) => {
            collect_bitvector_integer_variables_seen(value, variables, seen)
        }
        CValue::Pointer(_) => {}
    }
}

fn collect_algebraic_integer_variables(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_algebraic_value_integer_variables(field, variables, seen);
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_algebraic_value_integer_variables(binding, variables, seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_algebraic_integer_variables(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_pure_argument_integer_variables(argument, variables, seen);
            }
        }
    }
}

fn collect_algebraic_value_integer_variables(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        AlgebraicValue::C(value) => collect_c_value_integer_variables(value, variables, seen),
        AlgebraicValue::Integer(value) => {
            collect_integer_carrier_variables_seen(value, variables, seen)
        }
        AlgebraicValue::Algebraic(value) => {
            collect_algebraic_integer_variables(value, variables, seen)
        }
    }
}

fn collect_integer_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    crate::instrumentation::record_deterministic_work(1);
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                match argument {
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Integer(value) => {
                        collect_shared_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_term_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bitvector_variables(memory, variables);
                        collect_c_value_bitvector_variables(pointer, variables);
                    }
                }
            }
        }
        IntegerTerm::Machine(value) => collect_bitvector_variables(value.value(), variables),
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_term_bitvector_variables(scrutinee, variables);
            for arm in arms {
                collect_shared_integer_variables(&arm.body, variables, seen);
            }
        }
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::Negate(value) => collect_shared_integer_variables(value, variables, seen),
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_shared_integer_variables(left, variables, seen);
            collect_shared_integer_variables(right, variables, seen);
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end } => {
                    collect_bitvector_variables(start.value(), variables);
                    collect_bitvector_variables(end.value(), variables);
                }
                crate::kernel::IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_variables(start, variables, seen);
                    collect_shared_integer_variables(end, variables, seen);
                }
            }
            collect_shared_integer_variables(initial, variables, seen);
            let mut body_variables = BTreeSet::new();
            collect_shared_integer_variables(body, &mut body_variables, &mut BTreeSet::new());
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
    }
}

fn collect_shared_integer_variables(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    if !seen.insert(term.id()) {
        return;
    }
    collect_integer_variables_seen(term, variables, seen);
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
        | Bitvector32Term::UInt32From64(value)
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
            let mut body_variables = BTreeSet::new();
            collect_bitvector_variables(body, &mut body_variables);
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_variables(argument, variables);
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. } => {}
        Bitvector32Term::AlgebraicMatch { arms, .. } => {
            for arm in arms {
                collect_bitvector_variables(&arm.body, variables);
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            let mut seen = BTreeSet::new();
            collect_shared_integer_variables(value, variables, &mut seen);
        }
    }
}

/// Collect the C-carrier variables that a bitvector substitution can actually
/// reach.  Memory snapshots are deliberately opaque: a load contributes its
/// pointer (and the variables in that pointer), but never the snapshot's
/// blocks or cells.  This is the capture analysis used by `TermRewrite`; the
/// general-purpose collector above retains its historical snapshot behavior
/// for proof-state analyses that need it.
pub(crate) fn collect_bitvector_capture_variables(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = BTreeSet::new();
    collect_bitvector_capture_variables_seen(term, variables, &mut integer_seen);
}

fn collect_bitvector_capture_variables_seen(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            variables.insert(*variable);
            if crate::kernel::is_load_variable(variable)
                && let Some((_, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                collect_pointer_capture_variables(&pointer, variables, integer_seen);
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
            collect_bitvector_capture_variables_seen(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(right, variables, integer_seen);
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value)
        | Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            collect_bitvector_capture_variables_seen(value, variables, integer_seen)
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_capture_variables(condition, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(then_term, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(else_term, variables, integer_seen);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_capture_variables_seen(start, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(end, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(initial, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            let mut body_variables = BTreeSet::new();
            collect_bitvector_capture_variables_seen(body, &mut body_variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_capture_variables_seen(argument, variables, integer_seen);
            }
        }
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            collect_capture_variables_in_algebraic_term(scrutinee, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_capture_variables_in_algebraic_value(binding, variables, integer_seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_capture_variables_seen(&arm.body, variables, integer_seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        Bitvector32Term::MemoryLoad(_, pointer) | Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_capture_variables(pointer, variables, integer_seen)
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_shared_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
    }
}

fn collect_condition_capture_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match condition {
        ConditionTerm::Constant(_) => {}
        ConditionTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_capture_variables_in_algebraic_term(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_capture_variables_in_algebraic_term(right, variables, integer_seen);
        }
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
            collect_bitvector_capture_variables_seen(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(right, variables, integer_seen);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| {
                if !crate::instrumentation::checked_collection_exhausted() {
                    collect_bitvector_capture_variables_seen(term, variables, integer_seen)
                }
            });
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_capture_variables(right, variables, integer_seen);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_capture_variables(right, variables, integer_seen);
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            collect_shared_integer_bitvector_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(right, variables, integer_seen);
        }
    }
}

fn collect_pointer_offset_capture_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_capture_variables(right, variables, integer_seen);
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_capture_variables_seen(value, variables, integer_seen);
        }
    }
}

fn collect_pointer_capture_variables(
    pointer: &Pointer,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &pointer.block {
        PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
            variables.insert(*variable);
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::Heap(_) => {}
    }
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    collect_pointer_offset_capture_variables(&pointer.offset, variables, integer_seen);
}

fn collect_capture_variables_in_c_value(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        CValue::Void => {}
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::Int32(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => {
            collect_bitvector_capture_variables_seen(bits, variables, integer_seen)
        }
        CValue::Pointer(pointer) => {
            collect_pointer_capture_variables(pointer.pointer(), variables, integer_seen)
        }
    }
}

fn collect_capture_variables_in_pure_argument(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match argument {
        PureFunctionArgument::Value(value) => {
            collect_capture_variables_in_c_value(value, variables, integer_seen)
        }
        PureFunctionArgument::Integer(value) => {
            collect_shared_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_capture_variables_in_algebraic_term(value, variables, integer_seen)
        }
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_capture_variables_in_c_value(pointer, variables, integer_seen)
        }
    }
}

fn collect_capture_variables_in_algebraic_term(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_algebraic_value(field, variables, integer_seen);
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_capture_variables_in_algebraic_term(scrutinee, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_capture_variables_in_algebraic_value(binding, variables, integer_seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_algebraic_term(&arm.body, variables, integer_seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
            }
        }
    }
}

fn collect_capture_variables_in_algebraic_value(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        AlgebraicValue::C(value) => {
            collect_capture_variables_in_c_value(value, variables, integer_seen)
        }
        AlgebraicValue::Integer(value) => {
            collect_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
        AlgebraicValue::Algebraic(value) => {
            collect_capture_variables_in_algebraic_term(value, variables, integer_seen)
        }
    }
}

fn collect_shared_integer_bitvector_capture_variables(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    if integer_seen.insert(term.id()) {
        collect_integer_bitvector_capture_variables(term.as_ref(), variables, integer_seen);
    }
}

fn collect_integer_bitvector_capture_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => {}
        IntegerTerm::Machine(value) => {
            collect_bitvector_capture_variables_seen(value.value(), variables, integer_seen)
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
            }
        }
        IntegerTerm::Negate(value) => {
            collect_shared_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_shared_integer_bitvector_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(right, variables, integer_seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_capture_variables_in_algebraic_term(scrutinee, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_capture_variables_in_algebraic_value(binding, variables, integer_seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_shared_integer_bitvector_capture_variables(
                    &arm.body,
                    variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            item,
            body,
            ..
        } => {
            match index {
                IntegerRangeFoldIndex::Int32 { start, end } => {
                    collect_bitvector_capture_variables_seen(
                        start.value(),
                        variables,
                        integer_seen,
                    );
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_bitvector_capture_variables_seen(end.value(), variables, integer_seen);
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_bitvector_capture_variables(
                        start,
                        variables,
                        integer_seen,
                    );
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_shared_integer_bitvector_capture_variables(
                        end,
                        variables,
                        integer_seen,
                    );
                }
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(initial, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            if matches!(index, IntegerRangeFoldIndex::Int32 { .. }) {
                let mut body_variables = BTreeSet::new();
                collect_shared_integer_bitvector_capture_variables(
                    body,
                    &mut body_variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                body_variables.remove(item);
                variables.extend(body_variables);
            } else {
                collect_shared_integer_bitvector_capture_variables(body, variables, integer_seen);
            }
        }
    }
}

/// Collect C-carrier variables nested in an Integer term without descending
/// into memory snapshots.  Machine conversions and opaque pure arguments are
/// part of the lexical expression and therefore remain visible to capture
/// analysis.
pub(crate) fn collect_integer_capture_bitvector_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = BTreeSet::new();
    collect_integer_bitvector_capture_variables(term, variables, &mut integer_seen);
}

/// The carrier-separated free-variable summary used by capture-avoiding
/// Integer rewrites.  `max` includes both free variables and nested fold
/// binders, so a fresh binder cannot collide with a name that is protected
/// deeper in the same DAG.
#[derive(Clone, Debug, Default)]
pub(crate) struct IntegerScopeSummary {
    pub(crate) max: u64,
}

impl IntegerScopeSummary {
    fn merge(&mut self, other: Self) {
        self.max = self.max.max(other.max);
    }

    fn integer_variable(variable: Variable) -> Self {
        Self { max: variable.0 }
    }

    fn bitvector_variable(variable: Variable) -> Self {
        Self { max: variable.0 }
    }

    fn reserve(&mut self, variable: Variable) {
        self.max = self.max.max(variable.0);
    }
}

/// Collect summaries for an Integer DAG in one shared traversal.  The map is
/// populated for every shared Integer node reached from `term`, so later
/// nested-fold scopes reuse their already-computed suffix summary instead of
/// recursively scanning that suffix again.
pub(crate) fn collect_integer_scope_summaries(
    term: &SharedIntegerTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    collect_integer_scope_summary_shared(term, summaries)
}

fn collect_integer_scope_summary_shared(
    term: &SharedIntegerTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if crate::instrumentation::checked_collection_exhausted() {
        return IntegerScopeSummary::default();
    }
    if let Some(summary) = summaries.get(&term.id()) {
        return summary.clone();
    }
    let summary = collect_integer_scope_summary(term.as_ref(), summaries);
    summaries.insert(term.id(), summary.clone());
    summary
}

fn collect_integer_scope_summary(
    term: &IntegerTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match term {
        IntegerTerm::Constant(_) => IntegerScopeSummary::default(),
        IntegerTerm::Variable(variable) => IntegerScopeSummary::integer_variable(*variable),
        IntegerTerm::Machine(value) => collect_bitvector_scope_summary(value.value(), summaries),
        IntegerTerm::Negate(value) => collect_integer_scope_summary_shared(value, summaries),
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            let mut summary = collect_integer_scope_summary_shared(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(right, summaries));
            summary
        }
        IntegerTerm::PureFunctionApplication(application) => {
            let mut summary = IntegerScopeSummary::default();
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_scope_summary_in_argument(argument, summaries));
            }
            summary
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            let mut summary = collect_algebraic_scope_summary(scrutinee, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_algebraic_value_scope_summary(binding, summaries));
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_integer_scope_summary_shared(&arm.body, summaries));
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
            }
            summary
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut summary = match index {
                IntegerRangeFoldIndex::Int32 { start, end } => {
                    let mut summary = collect_bitvector_scope_summary(start.value(), summaries);
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_bitvector_scope_summary(end.value(), summaries));
                    summary
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    let mut summary = collect_integer_scope_summary_shared(start, summaries);
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_integer_scope_summary_shared(end, summaries));
                    summary
                }
            };
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(initial, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(body, summaries));
            summary.reserve(*accumulator);
            summary.reserve(*item);
            summary
        }
    }
}

fn collect_bitvector_scope_summary(
    term: &Bitvector32Term,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_) => IntegerScopeSummary::default(),
        Bitvector32Term::Variable(variable) => {
            let mut summary = IntegerScopeSummary::bitvector_variable(*variable);
            if crate::kernel::is_load_variable(variable)
                && let Some((_, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                summary.merge(collect_pointer_scope_summary(&pointer, summaries));
            }
            summary
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
            let mut summary = collect_bitvector_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(right, summaries));
            summary
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value)
        | Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            collect_bitvector_scope_summary(value, summaries)
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            let mut summary = collect_condition_scope_summary(condition, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(then_term, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(else_term, summaries));
            summary
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut summary = collect_bitvector_scope_summary(start, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(end, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(initial, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(body, summaries));
            summary.reserve(*accumulator);
            summary.reserve(*item);
            summary
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_bitvector_scope_summary(argument, summaries));
            }
            summary
        }
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_scope_summary_in_argument(argument, summaries));
            }
            summary
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            let mut summary = collect_algebraic_scope_summary(scrutinee, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_algebraic_value_scope_summary(binding, summaries));
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_bitvector_scope_summary(&arm.body, summaries));
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
            }
            summary
        }
        Bitvector32Term::MemoryLoad(_, pointer) | Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_scope_summary(pointer, summaries)
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_integer_scope_summary_shared(value, summaries)
        }
    }
}

fn collect_pointer_scope_summary(
    pointer: &Pointer,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    let mut summary = match &pointer.block {
        PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
            IntegerScopeSummary::bitvector_variable(*variable)
        }
        _ => IntegerScopeSummary::default(),
    };
    summary.merge(collect_pointer_offset_scope_summary(
        &pointer.offset,
        summaries,
    ));
    summary
}

fn collect_pointer_offset_scope_summary(
    offset: &PointerOffsetTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
            IntegerScopeSummary::default()
        }
        PointerOffsetTerm::Add(left, right) => {
            let mut summary = collect_pointer_offset_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_pointer_offset_scope_summary(right, summaries));
            summary
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_scope_summary(value, summaries)
        }
    }
}

fn collect_condition_scope_summary(
    condition: &ConditionTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match condition {
        ConditionTerm::Constant(_) => IntegerScopeSummary::default(),
        ConditionTerm::Variable(variable) => IntegerScopeSummary::bitvector_variable(*variable),
        ConditionTerm::AlgebraicEqual(left, right) => {
            let mut summary = collect_algebraic_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_algebraic_scope_summary(right, summaries));
            summary
        }
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
            let mut summary = collect_bitvector_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(right, summaries));
            summary
        }
        ConditionTerm::Float32(condition) | ConditionTerm::Float64(condition) => {
            let mut summary = IntegerScopeSummary::default();
            condition.for_each_bitvector_term(|term| {
                if !crate::instrumentation::checked_collection_exhausted() {
                    summary.merge(collect_bitvector_scope_summary(term, summaries));
                }
            });
            summary
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            let mut summary = collect_pointer_offset_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_pointer_offset_scope_summary(right, summaries));
            summary
        }
        ConditionTerm::PointerEqual(left, right) => {
            let mut summary = collect_pointer_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_pointer_scope_summary(right, summaries));
            summary
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            let mut summary = collect_integer_scope_summary_shared(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(right, summaries));
            summary
        }
    }
}

fn collect_scope_summary_in_argument(
    argument: &PureFunctionArgument,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match argument {
        PureFunctionArgument::Value(value) => collect_c_value_scope_summary(value, summaries),
        PureFunctionArgument::Integer(value) => {
            collect_integer_scope_summary_shared(value, summaries)
        }
        PureFunctionArgument::Algebraic(value) => collect_algebraic_scope_summary(value, summaries),
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_c_value_scope_summary(pointer, summaries)
        }
    }
}

fn collect_c_value_scope_summary(
    value: &CValue,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match value {
        CValue::Void => IntegerScopeSummary::default(),
        CValue::Bool(term)
        | CValue::Int16(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::Int32(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => collect_bitvector_scope_summary(term, summaries),
        CValue::Pointer(pointer) => collect_pointer_scope_summary(pointer.pointer(), summaries),
    }
}

fn collect_algebraic_scope_summary(
    term: &AlgebraicTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => IntegerScopeSummary::default(),
        AlgebraicTermNode::Constructor { fields, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_algebraic_value_scope_summary(field, summaries));
            }
            summary
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            let mut summary = collect_algebraic_scope_summary(scrutinee, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_algebraic_value_scope_summary(binding, summaries));
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_algebraic_scope_summary(&arm.body, summaries));
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
            }
            summary
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_scope_summary_in_argument(argument, summaries));
            }
            summary
        }
    }
}

fn collect_algebraic_value_scope_summary(
    value: &AlgebraicValue,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match value {
        AlgebraicValue::C(value) => collect_c_value_scope_summary(value, summaries),
        AlgebraicValue::Integer(value) => collect_integer_scope_summary(value, summaries),
        AlgebraicValue::Algebraic(value) => collect_algebraic_scope_summary(value, summaries),
    }
}

/// Collect only fold binder names from an Integer expression, keeping the
/// Integer and C carriers separate.  Capture analysis must remove nested
/// binders, while fresh-name selection must reserve them: otherwise a fresh C
/// item can accidentally reuse the name of a deeper fold in the body.
pub(crate) fn collect_integer_binder_variables(
    term: &IntegerTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = BTreeSet::new();
    collect_integer_binder_variables_seen(
        term,
        integer_variables,
        bitvector_variables,
        &mut integer_seen,
    );
}

fn collect_integer_binder_variables_seen(
    term: &IntegerTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => {}
        IntegerTerm::Machine(value) => collect_bitvector_binder_variables_seen(
            value.value(),
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_pure_argument(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        IntegerTerm::Negate(value) => collect_integer_binder_variables_shared(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_integer_binder_variables_shared(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_binder_variables_in_algebraic_term(
                scrutinee,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_binder_variables_in_algebraic_value(
                        binding,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_integer_binder_variables_shared(
                    &arm.body,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            integer_variables.insert(*accumulator);
            match index {
                IntegerRangeFoldIndex::Int32 { start, end } => {
                    bitvector_variables.insert(*item);
                    collect_bitvector_binder_variables_seen(
                        start.value(),
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_bitvector_binder_variables_seen(
                        end.value(),
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    integer_variables.insert(*item);
                    collect_integer_binder_variables_shared(
                        start,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_integer_binder_variables_shared(
                        end,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                initial,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                body,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
    }
}

fn collect_integer_binder_variables_shared(
    term: &SharedIntegerTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    if integer_seen.insert(term.id()) {
        collect_integer_binder_variables_seen(
            term.as_ref(),
            integer_variables,
            bitvector_variables,
            integer_seen,
        );
    }
}

fn collect_bitvector_binder_variables_seen(
    term: &Bitvector32Term,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _)
        | Bitvector32Term::PointerAddress(_) => {}
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_integer_binder_variables_shared(
                value,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
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
            collect_bitvector_binder_variables_seen(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value)
        | Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            collect_bitvector_binder_variables_seen(
                value,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_binder_variables(
                condition,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                then_term,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                else_term,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            bitvector_variables.insert(*accumulator);
            bitvector_variables.insert(*item);
            collect_bitvector_binder_variables_seen(
                start,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                end,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                initial,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                body,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_binder_variables_seen(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_pure_argument(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            collect_binder_variables_in_algebraic_term(
                scrutinee,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_binder_variables_in_algebraic_value(
                        binding,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_binder_variables_seen(
                    &arm.body,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
    }
}

pub(crate) fn collect_bitvector_binder_variables(
    term: &Bitvector32Term,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = BTreeSet::new();
    collect_bitvector_binder_variables_seen(
        term,
        integer_variables,
        bitvector_variables,
        &mut integer_seen,
    );
}

fn collect_condition_binder_variables(
    condition: &ConditionTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_binder_variables_in_algebraic_term(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_binder_variables_in_algebraic_term(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
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
            collect_bitvector_binder_variables_seen(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| {
                if !crate::instrumentation::checked_collection_exhausted() {
                    collect_bitvector_binder_variables_seen(
                        term,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    )
                }
            });
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_binder_variables(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_binder_variables(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_binder_variables(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_binder_variables(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            collect_integer_binder_variables_shared(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
    }
}

fn collect_pointer_offset_binder_variables(
    offset: &PointerOffsetTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_binder_variables(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_binder_variables(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_binder_variables_seen(
                value,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
    }
}

fn collect_pointer_binder_variables(
    pointer: &Pointer,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    collect_pointer_offset_binder_variables(
        &pointer.offset,
        integer_variables,
        bitvector_variables,
        integer_seen,
    );
}

fn collect_binder_variables_in_c_value(
    value: &CValue,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        CValue::Void => {}
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::Int32(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => collect_bitvector_binder_variables_seen(
            bits,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        CValue::Pointer(pointer) => collect_pointer_binder_variables(
            pointer.pointer(),
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
    }
}

fn collect_binder_variables_in_pure_argument(
    argument: &PureFunctionArgument,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match argument {
        PureFunctionArgument::Value(value) => collect_binder_variables_in_c_value(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        PureFunctionArgument::Integer(value) => collect_integer_binder_variables_shared(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        PureFunctionArgument::Algebraic(value) => collect_binder_variables_in_algebraic_term(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        PureFunctionArgument::ArrayRef { pointer, .. } => collect_binder_variables_in_c_value(
            pointer,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
    }
}

fn collect_binder_variables_in_algebraic_term(
    term: &AlgebraicTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_algebraic_value(
                    field,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_binder_variables_in_algebraic_term(
                scrutinee,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_binder_variables_in_algebraic_value(
                        binding,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_algebraic_term(
                    &arm.body,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_pure_argument(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
    }
}

fn collect_binder_variables_in_algebraic_value(
    value: &AlgebraicValue,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut BTreeSet<u64>,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        AlgebraicValue::C(value) => collect_binder_variables_in_c_value(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        AlgebraicValue::Integer(value) => collect_integer_binder_variables_seen(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        AlgebraicValue::Algebraic(value) => collect_binder_variables_in_algebraic_term(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
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
    match &pointer.block {
        PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
            variables.insert(*variable);
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::Heap(_) => {}
    }
    collect_pointer_offset_bitvector_variables(&pointer.offset, variables);
}

pub(in crate::kernel) fn collect_memory_bitvector_variables(
    memory: &CMemory,
    variables: &mut BTreeSet<Variable>,
) {
    for (block, contents) in memory.blocks.iter() {
        match block {
            PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
                variables.insert(*variable);
            }
            PointerBlock::Concrete(_)
            | PointerBlock::StringLiteral { .. }
            | PointerBlock::Function(_)
            | PointerBlock::ExternalArgument
            | PointerBlock::Heap(_) => {}
        }
        collect_bitvector_variables(contents.size(), variables);
    }
    for (pointer, value) in memory.cells.iter() {
        collect_pointer_bitvector_variables(pointer, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
    for ((pointer, _), value) in memory.union_cells.iter() {
        collect_pointer_bitvector_variables(pointer, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
}

pub(crate) fn collect_c_value_bitvector_variables(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        CValue::Void => {}
        CValue::Bool(bits)
        | CValue::Int16(bits)
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

#[cfg(test)]
mod integer_expression_tests {
    use super::*;

    #[test]
    fn deferred_integer_arithmetic_collects_machine_variables() {
        let variable = Variable(781);
        let expression = SpecIntegerExpression::Negate(Box::new(SpecIntegerExpression::Add(
            Box::new(SpecIntegerExpression::Term(IntegerTerm::Constant(1.into()))),
            Box::new(SpecIntegerExpression::FromMachine(Box::new(
                SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable))),
            ))),
        )));
        let mut variables = BTreeSet::new();
        collect_spec_integer_variables(&expression, &mut variables);
        assert_eq!(variables, BTreeSet::from([variable]));
        variables.clear();
        let field = AlgebraicValue::Integer(
            IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(variable),
            )
            .unwrap(),
        );
        collect_algebraic_value_bitvector_variables(&field, &mut variables);
        assert_eq!(variables, BTreeSet::from([variable]));
    }

    #[test]
    fn integer_binder_collection_shared_dag_has_linear_attempts() {
        let mut attempts_by_depth = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let mut expression = IntegerTerm::Variable(Variable(4_000_000 + depth as u64));
            for _ in 0..depth {
                let child: SharedIntegerTerm = expression.into();
                expression = IntegerTerm::Add(child.clone(), child);
            }

            let mut integer_variables = BTreeSet::new();
            let mut bitvector_variables = BTreeSet::new();
            let attempts = {
                let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
                collect_integer_binder_variables(
                    &expression,
                    &mut integer_variables,
                    &mut bitvector_variables,
                );
                crate::instrumentation::checked_collection_attempts()
            };
            assert!(integer_variables.is_empty());
            assert!(bitvector_variables.is_empty());
            attempts_by_depth.push(attempts);
        }

        for pair in attempts_by_depth.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "shared Integer DAG collector attempts grew superlinearly: {attempts_by_depth:?}"
            );
        }
    }
}
