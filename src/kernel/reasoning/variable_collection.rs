use super::*;

#[derive(Default)]
struct SeenTerms {
    integers: BTreeSet<u64>,
    pointers: BTreeSet<u64>,
}
impl SeenTerms {
    fn insert(&mut self, id: u64) -> bool {
        self.integers.insert(id)
    }
}

thread_local! {
    static CONNECTION_BLOCKS: std::cell::RefCell<Option<BTreeSet<PointerBlock>>> = const { std::cell::RefCell::new(None) };
}

/// Explicit values and addresses a fact names; snapshot contents are not
/// dependencies merely because two propositions carry the same snapshot.
pub(crate) fn collect_atomic_connection_keys(
    proposition: &Proposition,
) -> BTreeSet<AtomicConnectionKey> {
    struct Scope(Option<BTreeSet<PointerBlock>>);
    impl Drop for Scope {
        fn drop(&mut self) {
            CONNECTION_BLOCKS.with(|blocks| *blocks.borrow_mut() = self.0.take());
        }
    }
    let prior = CONNECTION_BLOCKS.with(|blocks| blocks.replace(Some(BTreeSet::new())));
    let _scope = Scope(prior);
    let mut variables = BTreeSet::new();
    collect_proposition_connection_variables(proposition, &mut variables);
    let mut keys = variables
        .into_iter()
        .map(AtomicConnectionKey::Variable)
        .collect::<BTreeSet<_>>();
    CONNECTION_BLOCKS.with(|blocks| {
        keys.extend(
            blocks
                .borrow()
                .as_ref()
                .unwrap()
                .iter()
                .cloned()
                .map(AtomicConnectionKey::Block),
        )
    });
    keys
}

thread_local! {
    static CONNECTION_VARIABLES: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static CONNECTION_LOAD_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn collecting_connection_variables() -> bool {
    CONNECTION_VARIABLES.with(std::cell::Cell::get)
}

/// How far back along a snapshot's derivation
/// [`collect_proposition_frame_variables`] looks for havoc ranges.
const HAVOC_RANGE_HOPS: usize = 64;

thread_local! {
    static COLLECTING_HAVOC_RANGES: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The bitvector variables of `proposition`, with those of the ranges the
/// calls and loops recently behind each snapshot it loads from wrote.
///
/// Like [`collect_proposition_connection_variables`], this is for a planner
/// choosing which facts a derivation may need.
pub(crate) fn collect_proposition_frame_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    struct Scope(bool);
    impl Drop for Scope {
        fn drop(&mut self) {
            COLLECTING_HAVOC_RANGES.with(|flag| flag.set(self.0));
        }
    }
    let _scope = Scope(COLLECTING_HAVOC_RANGES.with(|flag| flag.replace(true)));
    collect_proposition_connection_variables(proposition, variables);
}

/// Every variable through which `proposition` can be related to another
/// fact: its bitvector variables, and also the algebraic-value and
/// pointer-offset variables the bitvector collectors deliberately leave out.
///
/// This is for a planner choosing which facts a derivation may need. It is
/// not a free-variable set for freshness or substitution.
pub(crate) fn collect_proposition_connection_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    struct Scope(bool);
    impl Drop for Scope {
        fn drop(&mut self) {
            CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
        }
    }
    let _scope = Scope(CONNECTION_VARIABLES.with(|flag| flag.replace(true)));
    collect_proposition_bitvector_variables(proposition, variables);
}

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

pub(crate) fn collect_proposition_bitvector_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    let mut depth = 0;
    let mut current = proposition;
    while let Proposition::Implies(_, body) = current {
        depth += 1;
        current = body;
    }
    if depth > 128 {
        let mut pending = vec![proposition];
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right)
                | Proposition::Or(left, right)
                | Proposition::Implies(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                Proposition::Not(body)
                | Proposition::ForAll { body, .. }
                | Proposition::Exists { body, .. } => pending.push(body),
                proposition => collect_proposition_bitvector_variables_one(proposition, variables),
            }
        }
        return;
    }
    collect_proposition_bitvector_variables_one(proposition, variables);
}

fn collect_proposition_bitvector_variables_one(
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
        Proposition::CMemoryInitialized {
            memory,
            base: pointer,
            ..
        }
        | Proposition::CMemoryReadDefined {
            memory, pointer, ..
        }
        | Proposition::CMemoryCanStore {
            memory, pointer, ..
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: _,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(base, variables);
            collect_bitvector_variables(bytes, variables);
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
            writes,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for (pointer, _) in writes {
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
        AlgebraicTermNode::Variable(variable) => {
            if collecting_connection_variables() {
                variables.insert(*variable);
            }
        }
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
        CExpression::MemberAddress { object: body, .. }
        | CExpression::AddressOf(body)
        | CExpression::CheckedObjectAddress(body)
        | CExpression::Not(body)
        | CExpression::Load(body) => {
            collect_c_expression_bitvector_variables(body, variables);
        }
        CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::PointerAligned { pointer, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
        }
        crate::kernel::binary_c_expression!(left, right) => {
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
        | CStatement::EndAutomaticLifetimes { .. }
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare {
            initializer: None, ..
        }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::ForStep { step, .. } => {
            collect_c_statement_bitvector_variables(step, variables);
        }
        CStatement::Declare {
            initializer: Some(expression),
            ..
        }
        | CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Throw(expression)
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
        CStatement::HeapAllocate { bytes, .. } => {
            collect_c_expression_bitvector_variables(bytes, variables);
        }
        CStatement::HeapFree { pointer } => {
            collect_c_expression_bitvector_variables(pointer, variables);
        }
        CStatement::Seq(first, second) => {
            collect_c_statement_bitvector_variables(first, variables);
            collect_c_statement_bitvector_variables(second, variables);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_c_statement_bitvector_variables(try_body, variables);
            collect_c_statement_bitvector_variables(handler, variables);
        }
        CStatement::Store { pointer, value } => {
            collect_c_expression_bitvector_variables(pointer, variables);
            collect_c_expression_bitvector_variables(value, variables);
        }
        CStatement::TypedStore { pointer, value, .. } => {
            collect_c_expression_bitvector_variables(pointer, variables);
            collect_c_expression_bitvector_variables(value, variables);
        }
        CStatement::CopyAggregate { target, source, .. }
        | CStatement::InitializeScalarArray { target, source, .. } => {
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
            ranking_measures,
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
            // A `decreases` component is read at the loop head like an
            // invariant is, and substitution rewrites it like one, so the
            // variables it already names are reserved like an invariant
            // check's. Skipping them would let a fresh execution variable be
            // handed out with a name the measure already uses.
            for measure in ranking_measures {
                collect_c_ranking_component_variables(measure, variables);
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

/// The variables one declared `decreases` component already names.
///
/// A component is read at the states the kernel picks and substitution
/// rewrites it, so its variables are reserved wherever it travels: on a loop
/// head, and on the recursion anchor of the function that declared it.
pub(in crate::kernel) fn collect_c_ranking_component_variables(
    component: &CRankingComponent,
    variables: &mut BTreeSet<Variable>,
) {
    match component {
        CRankingComponent::CExpression(expression) => {
            collect_c_expression_bitvector_variables(expression, variables);
        }
        CRankingComponent::Pure { expression, .. } => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
        CRankingComponent::PureInteger { expression, .. } => {
            collect_spec_integer_variables(expression, variables);
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
        crate::kernel::binary_spec_expression!(left, right) => {
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
        SpecExpression::AggregateFieldValue { pointer, .. } => {
            collect_spec_expression_bitvector_variables(pointer, variables);
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
        SpecProposition::ForAllMachineInteger { variable, body, .. }
        | SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllInteger { variable, body, .. }
        | SpecProposition::ForAllAlgebraic { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsMachineInteger { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsInteger { variable, body, .. }
        | SpecProposition::ExistsAlgebraic { variable, body, .. }
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
        SpecProposition::MemoryInitialized { memory, base, .. } => {
            collect_spec_memory_bitvector_variables(memory, variables);
            collect_spec_expression_bitvector_variables(base, variables);
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
            crate::kernel::binary_spec_integer_expression!(left, right) => {
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
                    SpecIntegerRangeFoldIndex::Int32 { start, end }
                    | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
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
    let mut integer_seen = SeenTerms::default();
    collect_spec_integer_bound_variables_inner(expression, variables, &mut integer_seen);
}

fn collect_spec_integer_bound_variables_inner(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
        crate::kernel::binary_spec_integer_expression!(left, right) => {
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
                SpecIntegerRangeFoldIndex::Int32 { start, end }
                | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
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
    integer_seen: &mut SeenTerms,
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
        crate::kernel::binary_integer_term!(left, right) => {
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
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
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
    integer_seen: &mut SeenTerms,
) {
    if integer_seen.insert(term.id()) {
        collect_integer_bound_identities(term.as_ref(), variables, integer_seen);
    }
}

fn collect_pure_argument_bound_identities(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
    _integer_seen: &mut SeenTerms,
) {
    match value {
        CValue::Void => {}
        CValue::Pointer(pointer) => {
            if let Some(designation) = pointer.designation() {
                for term in designation.integer_terms() {
                    collect_shared_integer_bound_identities(term, variables, _integer_seen);
                }
                for term in designation.pointer_terms() {
                    for bits in term.offset.scaled_values() {
                        collect_bitvector_integer_variables(bits, variables);
                    }
                    if let PointerBlock::PureFunctionApplication(application) = &term.block
                        && _integer_seen.pointers.insert(application.id())
                    {
                        for argument in application.arguments() {
                            collect_pure_argument_bound_identities(
                                argument,
                                variables,
                                _integer_seen,
                            );
                        }
                    }
                }
            }
            if let PointerBlock::PureFunctionApplication(application) = &pointer.block
                && _integer_seen.pointers.insert(application.id())
            {
                for argument in application.arguments() {
                    collect_pure_argument_bound_identities(argument, variables, _integer_seen);
                }
            }
        }
        CValue::Int8(bits) => {
            collect_bitvector_integer_variables(bits, variables);
        }
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::Int32(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Int128(bits)
        | CValue::UInt128(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => {
            collect_bitvector_integer_variables(bits, variables);
        }
    }
}

fn collect_spec_integer_bound_argument(
    argument: &SpecPureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
        crate::kernel::binary_spec_expression!(left, right) => {
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
        SpecExpression::AggregateFieldValue { pointer, .. } => {
            collect_spec_integer_bound_expression(pointer, variables, integer_seen);
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
    integer_seen: &mut SeenTerms,
) {
    match expression {
        CExpression::Value(value) => {
            collect_c_value_bound_identities(value, variables, integer_seen);
        }
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. }
        | CExpression::MemberAddress {
            object: expression, ..
        }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::CheckedObjectAddress(expression)
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
        CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::PointerAligned { pointer, .. } => {
            collect_c_expression_bound_identities(pointer, variables, integer_seen);
        }
        crate::kernel::binary_c_expression!(left, right) => {
            collect_c_expression_bound_identities(left, variables, integer_seen);
            collect_c_expression_bound_identities(right, variables, integer_seen);
        }
    }
}

fn collect_spec_algebraic_bound_identities(
    expression: &SpecAlgebraicExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
    _integer_seen: &mut SeenTerms,
) {
    // A SpecMemory is a captured execution snapshot, not lexical input to
    // the expression.  Its blocks, cells, and union overlays are therefore
    // opaque to freshness collection; callers recurse through explicit
    // pointer and expression payloads adjacent to the snapshot instead.
}

fn collect_spec_resource_bound_identities(
    resource: &SpecResource,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
        SpecProposition::ForAllMachineInteger { variable, body, .. }
        | SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllInteger { variable, body, .. }
        | SpecProposition::ForAllAlgebraic { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsMachineInteger { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsInteger { variable, body, .. }
        | SpecProposition::ExistsAlgebraic { variable, body, .. }
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
        SpecProposition::MemoryInitialized { memory, base, .. } => {
            collect_spec_memory_bound_identities(memory, variables, integer_seen);
            collect_spec_integer_bound_expression(base, variables, integer_seen);
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
        CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Jump { state, .. } => {
            collect_c_state_bitvector_variables(state, variables)
        }
        CStatementOutcome::Return { value, state } | CStatementOutcome::Throw { value, state } => {
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
        CFunctionOutcome::Return { value, state } | CFunctionOutcome::Throw { value, state } => {
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
    if let Some(destination) = &state.aggregate_destination {
        collect_pointer_bitvector_variables(&destination.pointer, variables);
    }
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
        CResource::PopulationAuthority(description) => {
            description.visit_values(|value| {
                collect_algebraic_value_bitvector_variables(value, variables)
            });
        }
        CResource::MutexUse(identity) => {
            if let Some(p) = &identity.protected {
                p.visit_values(|v| collect_algebraic_value_bitvector_variables(v, variables));
            }
            if identity.binding.is_none() {
                collect_pointer_bitvector_variables(&identity.mutex, variables);
            }
        }
        CResource::MutexGuard(identity) | CResource::MutexLive(identity) => {
            if identity.epoch.is_none() {
                let pointer = &identity.mutex;
                collect_pointer_bitvector_variables(pointer, variables);
            }
        }
        CResource::Publication(right) => {
            right
                .payload
                .visit_values(|v| collect_algebraic_value_bitvector_variables(v, variables));
            collect_pointer_bitvector_variables(&right.flag, variables);
            if let Some(value) = &right.observed {
                collect_c_value_bitvector_variables(value, variables);
            }
        }
        CResource::Instance(instance) => {
            for value in instance.arguments.iter().chain(instance.fields.iter()) {
                collect_algebraic_value_bitvector_variables(value, variables);
            }
            crate::kernel::ResourceReference::visit_captured_values(
                instance.resource_arguments(),
                |value| {
                    collect_algebraic_value_bitvector_variables(value, variables);
                },
            );
        }
        CResource::Memory(range) => collect_c_memory_range_bitvector_variables(range, variables),
        CResource::Iterated(iterated) => {
            for pointer in iterated.pointers() {
                collect_pointer_bitvector_variables(pointer, variables);
            }
            for term in iterated.terms() {
                collect_bitvector_variables(term, variables);
            }
        }
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
    collect_c_function_contract_interface_bitvector_variables(
        function.contract_interface(),
        variables,
    );
    collect_c_statement_bitvector_variables(function.body(), variables);
}

/// Collects variables from the body-independent contract interface only.
/// Named callback application uses this collector so unrelated template
/// statements, globals, and storage cannot affect fresh identities or
/// callback behavior.
pub(in crate::kernel) fn collect_c_function_contract_interface_bitvector_variables(
    interface: &CFunctionContractInterface,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in interface
        .proof_parameters()
        .iter()
        .chain(interface.resource_requires())
        .chain(interface.resource_ensures())
        .chain(interface.resource_constructors())
    {
        collect_resource_spec_bitvector_variables(resource, variables);
    }
    for proposition in interface
        .contract_requires()
        .iter()
        .chain(interface.contract_ensures())
        .chain(interface.exceptional_ensures())
    {
        collect_spec_proposition_bitvector_variables(proposition, variables);
    }
    for segment in interface.contract_mutable() {
        collect_c_expression_bitvector_variables(&segment.base, variables);
        collect_c_expression_bitvector_variables(&segment.start, variables);
        collect_c_expression_bitvector_variables(&segment.end, variables);
        if let Some(guard) = segment.guard() {
            collect_spec_proposition_bitvector_variables(guard, variables);
        }
    }
    if let Some(measure) = interface.recursion_measure() {
        collect_c_ranking_component_variables(measure, variables);
    }
}

pub(in crate::kernel) fn collect_resource_spec_bitvector_variables(
    resource: &CResourceSpec,
    variables: &mut BTreeSet<Variable>,
) {
    for place in resource.native_record_places() {
        collect_c_expression_bitvector_variables(&place.carrier, variables);
        if let Some(count) = &place.prefix_count {
            collect_c_expression_bitvector_variables(count, variables);
        }
    }
    for span in resource.native_span_requirements() {
        collect_c_expression_bitvector_variables(&span.carrier, variables);
        collect_c_expression_bitvector_variables(&span.count, variables);
    }
    match resource.term() {
        CResourceTerm::Instance { resource, .. } => {
            collect_resource_term_bitvector_variables(resource, variables)
        }
        CResourceTerm::PopulationAuthority { protected, .. } => {
            collect_resource_spec_bitvector_variables(&protected.resource, variables)
        }
        CResourceTerm::MutexGuard { mutex, .. } | CResourceTerm::MutexLive { mutex, .. } => {
            collect_c_expression_bitvector_variables(mutex, variables)
        }
        CResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_c_expression_bitvector_variables(mutex, variables);
            if let Some(p) = protected {
                collect_resource_spec_bitvector_variables(&p.resource, variables);
            }
        }
        CResourceTerm::Publication { flag, payload, .. } => {
            collect_c_expression_bitvector_variables(flag, variables);
            collect_resource_spec_bitvector_variables(&payload.resource, variables);
        }
        CResourceTerm::Memory(segment) => {
            collect_c_expression_bitvector_variables(&segment.base, variables);
            collect_c_expression_bitvector_variables(&segment.start, variables);
            collect_c_expression_bitvector_variables(&segment.end, variables);
            if let Some(guard) = segment.guard() {
                collect_spec_proposition_bitvector_variables(guard, variables);
            }
        }
        CResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_c_expression_bitvector_variables(expression, variables);
            }
        }
        CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, variables);
            }
        }
    }
    if let CResourceQuantity::Count(quantity) = resource.quantity() {
        collect_c_expression_bitvector_variables(quantity, variables);
    }
}

fn collect_resource_term_bitvector_variables(
    resource: &CResourceTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        CResourceTerm::Instance { resource, .. } => {
            collect_resource_term_bitvector_variables(resource, variables)
        }
        CResourceTerm::PopulationAuthority { protected, .. } => {
            collect_resource_spec_bitvector_variables(&protected.resource, variables)
        }
        CResourceTerm::MutexGuard { mutex, .. } | CResourceTerm::MutexLive { mutex, .. } => {
            collect_c_expression_bitvector_variables(mutex, variables)
        }
        CResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_c_expression_bitvector_variables(mutex, variables);
            if let Some(p) = protected {
                collect_resource_spec_bitvector_variables(&p.resource, variables);
            }
        }
        CResourceTerm::Publication { flag, payload, .. } => {
            collect_c_expression_bitvector_variables(flag, variables);
            collect_resource_spec_bitvector_variables(&payload.resource, variables);
        }
        CResourceTerm::Memory(segment) => {
            collect_c_expression_bitvector_variables(&segment.base, variables);
            collect_c_expression_bitvector_variables(&segment.start, variables);
            collect_c_expression_bitvector_variables(&segment.end, variables);
            if let Some(guard) = segment.guard() {
                collect_spec_proposition_bitvector_variables(guard, variables);
            }
        }
        CResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_c_expression_bitvector_variables(expression, variables);
            }
        }
        CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
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
        collect_c_function_contract_interface_bitvector_variables(contract.interface(), variables);
        collect_c_function_contract_interface_bound_variables(contract.interface(), variables);
    }
    for rule in environment.verified_function_rules.values() {
        collect_c_function_bitvector_variables(&rule.function, variables);
        collect_c_function_bound_variables(&rule.function, variables);
        if let Some(declaration) = &rule.source_declaration {
            collect_c_function_bitvector_variables(declaration, variables);
            collect_c_function_bound_variables(declaration, variables);
        }
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
    // The anchor holds the certified function's measure read at its entry.
    // Its variables are named by later call steps, so a fresh identity must
    // not be handed out on top of one, exactly as for a loop head's measure.
    if let Some(anchor) = environment.recursion_anchor() {
        match anchor.measure() {
            CRankingMeasureValue::Machine(term)
            | CRankingMeasureValue::Unsigned32(term)
            | CRankingMeasureValue::Unsigned64(term)
            | CRankingMeasureValue::Signed64(term) => collect_bitvector_variables(term, variables),
            // An Integer measure's reserved names are the C carriers it reads
            // plus its own Integer binders; both are named by later call steps.
            CRankingMeasureValue::Integer(term) => {
                collect_integer_capture_bitvector_variables(term, variables);
                collect_integer_variables(term, variables);
            }
        }
        collect_c_ranking_component_variables(anchor.component(), variables);
        for obligation in anchor.entry_obligations() {
            collect_proposition_bitvector_variables(obligation.proposition(), variables);
            collect_proposition_bound_variables(obligation.proposition(), variables);
        }
    }
}

pub(in crate::kernel) fn collect_c_memory_range_bitvector_variables(
    range: &CMemoryRange,
    variables: &mut BTreeSet<Variable>,
) {
    collect_pointer_bitvector_variables(&range.base, variables);
    collect_bitvector_variables(range.bound_terms().0, variables);
    collect_bitvector_variables(range.bound_terms().1, variables);
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

thread_local! {
    // Condition-index insertion reads syntax, never snapshot contents. A
    // snapshot-dependent fact is indexed lazily by the ordinary collector.
    static DEFER_CONDITION_SNAPSHOTS: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

struct ConditionSnapshotDeferral(Option<bool>);

impl Drop for ConditionSnapshotDeferral {
    fn drop(&mut self) {
        DEFER_CONDITION_SNAPSHOTS.with(|state| state.set(self.0));
    }
}

fn defer_condition_snapshot() -> bool {
    DEFER_CONDITION_SNAPSHOTS.with(|state| {
        if state.get().is_some() {
            state.set(Some(true));
            true
        } else {
            false
        }
    })
}

/// Collect the ordinary condition variables, stopping at each snapshot.
/// Returns whether a snapshot was encountered. If so, the caller must defer
/// the whole fact to the complete collector to preserve its connections.
pub(in crate::kernel) fn collect_condition_index_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) -> bool {
    let prior = DEFER_CONDITION_SNAPSHOTS.with(|state| state.replace(Some(false)));
    let _scope = ConditionSnapshotDeferral(prior);
    collect_condition_bitvector_variables(condition, variables);
    DEFER_CONDITION_SNAPSHOTS.with(|state| state.get() == Some(true))
}

pub(crate) fn collect_condition_bitvector_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_algebraic_term_bitvector_variables(left, variables);
            collect_algebraic_term_bitvector_variables(right, variables);
        }
        ConditionTerm::Constant(_) => {}
        ConditionTerm::Variable(variable) => {
            if collecting_connection_variables() {
                variables.insert(*variable);
            }
        }
        crate::kernel::binary_bitvector_condition!(left, right) => {
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
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_integer_variables(left, variables);
            collect_integer_variables(right, variables);
        }
    }
}

pub(crate) fn collect_integer_variables(term: &IntegerTerm, variables: &mut BTreeSet<Variable>) {
    let mut seen = SeenTerms::default();
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
    let mut seen = SeenTerms::default();
    collect_integer_carrier_variables_seen(term, variables, &mut seen);
}

fn collect_integer_carrier_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
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
        crate::kernel::binary_integer_term!(left, right) => {
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
    seen: &mut SeenTerms,
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
    let mut seen = SeenTerms::default();
    collect_bitvector_integer_variables_seen(term, variables, &mut seen);
}

fn collect_bitvector_integer_variables_seen(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(_, pointer, _) | Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_integer_variables(pointer, variables, seen)
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_shared_integer_variables_seen(value, variables, seen);
        }
        crate::kernel::binary_machine_term!(left, right) => {
            collect_bitvector_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(right, variables, seen);
        }
        crate::kernel::unary_machine_term!(value) => {
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
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    if let PointerBlock::PureFunctionApplication(application) = &pointer.block
        && seen.pointers.insert(application.id())
    {
        for argument in application.arguments() {
            collect_pure_argument_integer_variables(argument, variables, seen);
        }
    }
    collect_pointer_offset_integer_variables(&pointer.offset, variables, seen);
}

fn collect_pointer_offset_integer_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
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
    seen: &mut SeenTerms,
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
    seen: &mut SeenTerms,
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
        crate::kernel::binary_integer_term!(left, right) => {
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
                    &mut SeenTerms::default(),
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
            collect_shared_integer_variables_seen(
                body,
                &mut body_variables,
                &mut SeenTerms::default(),
            );
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
    seen: &mut SeenTerms,
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
    let mut seen = SeenTerms::default();
    collect_integer_free_variables_seen(term, variables, &mut seen);
}

fn collect_condition_integer_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match condition {
        crate::kernel::integer_comparison_condition!(left, right) => {
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
    seen: &mut SeenTerms,
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
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        CValue::Void => {}
        CValue::Int8(value) => collect_bitvector_integer_variables_seen(value, variables, seen),
        CValue::Bool(value)
        | CValue::Int16(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value)
        | CValue::Int32(value)
        | CValue::UInt32(value)
        | CValue::Int64(value)
        | CValue::UInt64(value)
        | CValue::Int128(value)
        | CValue::UInt128(value)
        | CValue::Float32(value)
        | CValue::Float64(value) => {
            collect_bitvector_integer_variables_seen(value, variables, seen)
        }
        CValue::Pointer(pointer) => {
            collect_pointer_integer_variables(pointer.pointer(), variables, seen);
            if let Some(designation) = pointer.designation() {
                for term in designation.pointer_terms() {
                    collect_pointer_integer_variables(term, variables, seen);
                }
                for term in designation.integer_terms() {
                    collect_shared_integer_variables_seen(term, variables, seen);
                }
            }
        }
    }
}

fn collect_algebraic_integer_variables(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
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
    seen: &mut SeenTerms,
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
    seen: &mut SeenTerms,
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
        crate::kernel::binary_integer_term!(left, right) => {
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
                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end }
                | crate::kernel::IntegerRangeFoldIndex::UInt64 { start, end } => {
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
            collect_shared_integer_variables(body, &mut body_variables, &mut SeenTerms::default());
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
    }
}

fn collect_shared_integer_variables(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if !seen.insert(term.id()) {
        return;
    }
    collect_integer_variables_seen(term, variables, seen);
}

fn collect_stored_load_connection_variables(
    memory: &SharedCMemory,
    pointer: &Pointer,
    variables: &mut BTreeSet<Variable>,
) {
    if collecting_connection_variables() {
        // A written load depends on the value at its exact address,
        // rather than every value stored in the same snapshot.
        struct Depth(usize);
        impl Drop for Depth {
            fn drop(&mut self) {
                CONNECTION_LOAD_DEPTH.with(|depth| depth.set(self.0));
            }
        }
        let depth = CONNECTION_LOAD_DEPTH.with(std::cell::Cell::get);
        if depth < HAVOC_RANGE_HOPS {
            let _scope = Depth(depth);
            CONNECTION_LOAD_DEPTH.with(|current| current.set(depth + 1));
            crate::instrumentation::record_deterministic_work(1);
            if let Some(value) = memory.memory().cells.explicitly_stored_value(pointer) {
                collect_c_value_bitvector_variables(value, variables);
            }
        }
    }
}

pub(crate) fn collect_bitvector_variables(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
) {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => {}
        Bitvector32Term::Variable(variable) => {
            let newly_seen = variables.insert(*variable);
            if collecting_connection_variables() && !newly_seen {
                return;
            }
            // A load variable denotes its load, so the variables
            // of that load's address (a bound index, a loop counter) are
            // free in the term: a case split or substitution keyed on the
            // term's variables must see them.
            if crate::kernel::is_load_variable(variable)
                && let Some((memory, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                collect_shared_memory_bitvector_variables(&memory, variables);
                collect_pointer_bitvector_variables(&pointer, variables);
                collect_stored_load_connection_variables(&memory, &pointer, variables);
                if COLLECTING_HAVOC_RANGES.with(std::cell::Cell::get)
                    && let Some((origin, _)) =
                        crate::kernel::eval::registered_load_origin_for_variable(variable)
                {
                    // The canonical snapshot may be a jumped placeholder.
                    // Frame dependencies belong to the live origin DAG.
                    collect_shared_memory_bitvector_variables(&origin, variables);
                }
            }
        }
        crate::kernel::binary_machine_term!(left, right)
        | Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        crate::kernel::unary_machine_term!(value) => {
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
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            // An application's arguments are not free bitvector variables
            // of the term, but a fact about one of them is related to it.
            if collecting_connection_variables() {
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
                        PureFunctionArgument::ArrayRef { pointer, .. } => {
                            collect_c_value_bitvector_variables(pointer, variables)
                        }
                    }
                }
            }
        }
        Bitvector32Term::AlgebraicMatch {
            scrutinee, arms, ..
        } => {
            if collecting_connection_variables() {
                collect_algebraic_term_bitvector_variables(scrutinee, variables);
            }
            for arm in arms {
                collect_bitvector_variables(&arm.body, variables);
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer, _) => {
            collect_shared_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
            collect_stored_load_connection_variables(memory, pointer, variables);
        }
        Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            let mut seen = SeenTerms::default();
            collect_shared_integer_variables(value, variables, &mut seen);
        }
    }
}

fn collect_bitvector_capture_variables_seen(
    term: &Bitvector32Term,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => {}
        Bitvector32Term::Variable(variable) => {
            variables.insert(*variable);
            if crate::kernel::is_load_variable(variable)
                && let Some((_, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                collect_pointer_capture_variables(&pointer, variables, integer_seen);
            }
        }
        crate::kernel::binary_machine_term!(left, right)
        | Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_bitvector_capture_variables_seen(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(right, variables, integer_seen);
        }
        crate::kernel::unary_machine_term!(value) => {
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
            collect_bitvector_capture_variables_seen(
                body,
                &mut body_variables,
                &mut SeenTerms::default(),
            );
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
        Bitvector32Term::MemoryLoad(_, pointer, _) | Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_capture_variables(pointer, variables, integer_seen)
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_shared_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
    }
}

/// The pointer-block and bitvector variables a proposition captures,
/// including the pointers inside pure-function arguments, which the plain
/// bitvector collection does not descend into. Conditions and their
/// connectives are traversed with the capture walk; any other proposition
/// shape falls back to [`collect_proposition_bitvector_variables`].
pub(in crate::kernel) fn collect_proposition_capture_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = SeenTerms::default();
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            Proposition::ConditionIs(condition, _) => {
                collect_condition_capture_variables(condition, variables, &mut integer_seen);
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Proposition::Not(body) => pending.push(body),
            proposition => collect_proposition_bitvector_variables(proposition, variables),
        }
    }
}

fn collect_condition_capture_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
        crate::kernel::binary_bitvector_condition!(left, right) => {
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
        crate::kernel::integer_comparison_condition!(left, right) => {
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &pointer.block {
        PointerBlock::PureFunctionApplication(application) => {
            if integer_seen.pointers.insert(application.id()) {
                for argument in application.arguments() {
                    collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
                }
            }
        }
        PointerBlock::Symbolic(variable)
        | PointerBlock::FunctionSymbolic(variable)
        | PointerBlock::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        // The identity is opaque here, like a scalar load name. The equality
        // graph separately indexes its defining address exactly once.
        | PointerBlock::LoadedPointer(_)
        | PointerBlock::Heap(_)
        | PointerBlock::Temporary(_) => {}
    }
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    collect_pointer_offset_capture_variables(&pointer.offset, variables, integer_seen);
}

fn collect_capture_variables_in_c_value(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        CValue::Void => {}
        CValue::Int8(bits) => {
            collect_bitvector_capture_variables_seen(bits, variables, integer_seen)
        }
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::Int32(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Int128(bits)
        | CValue::UInt128(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => {
            collect_bitvector_capture_variables_seen(bits, variables, integer_seen)
        }
        CValue::Pointer(pointer) => {
            collect_pointer_capture_variables(pointer.pointer(), variables, integer_seen);
            if let Some(designation) = pointer.designation() {
                if let Some(variable) = designation.unresolved_variable() {
                    variables.insert(variable);
                }
                for term in designation.pointer_terms() {
                    collect_pointer_capture_variables(term, variables, integer_seen);
                }
                for term in designation.integer_terms() {
                    collect_shared_integer_bitvector_capture_variables(
                        term,
                        variables,
                        integer_seen,
                    );
                }
            }
        }
    }
}

fn collect_capture_variables_in_pure_argument(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
        crate::kernel::binary_integer_term!(left, right) => {
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
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
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
            if index.machine_item_type().is_some() {
                let mut body_variables = BTreeSet::new();
                collect_shared_integer_bitvector_capture_variables(
                    body,
                    &mut body_variables,
                    &mut SeenTerms::default(),
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
    let mut integer_seen = SeenTerms::default();
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
        crate::kernel::binary_integer_term!(left, right) => {
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
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
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
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => IntegerScopeSummary::default(),
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
        crate::kernel::binary_machine_term!(left, right)
        | Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            let mut summary = collect_bitvector_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(right, summaries));
            summary
        }
        crate::kernel::unary_machine_term!(value) => {
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
        Bitvector32Term::MemoryLoad(_, pointer, _) | Bitvector32Term::PointerAddress(pointer) => {
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
        PointerBlock::Symbolic(variable)
        | PointerBlock::FunctionSymbolic(variable)
        | PointerBlock::ExternalObject(variable) => {
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
        crate::kernel::binary_bitvector_condition!(left, right) => {
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
        crate::kernel::integer_comparison_condition!(left, right) => {
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
        CValue::Int8(term) => collect_bitvector_scope_summary(term, summaries),
        CValue::Bool(term)
        | CValue::Int16(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::Int32(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Int128(term)
        | CValue::UInt128(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => collect_bitvector_scope_summary(term, summaries),
        CValue::Pointer(pointer) => {
            let mut summary = collect_pointer_scope_summary(pointer.pointer(), summaries);
            if let Some(designation) = pointer.designation() {
                if let Some(variable) = designation.unresolved_variable() {
                    summary.merge(IntegerScopeSummary::bitvector_variable(variable));
                }
                for term in designation.pointer_terms() {
                    summary.merge(collect_pointer_scope_summary(term, summaries));
                }
                for term in designation.integer_terms() {
                    summary.merge(collect_integer_scope_summary_shared(term, summaries));
                }
            }
            summary
        }
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
    let mut integer_seen = SeenTerms::default();
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
    integer_seen: &mut SeenTerms,
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
        crate::kernel::binary_integer_term!(left, right) => {
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
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _, _)
        | Bitvector32Term::PointerAddress(_) => {}
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_integer_binder_variables_shared(
                value,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        crate::kernel::binary_machine_term!(left, right)
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
        crate::kernel::unary_machine_term!(value) => {
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

fn collect_condition_binder_variables(
    condition: &ConditionTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
        crate::kernel::binary_bitvector_condition!(left, right) => {
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
        crate::kernel::integer_comparison_condition!(left, right) => {
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    if let PointerBlock::PureFunctionApplication(application) = &pointer.block
        && integer_seen.pointers.insert(application.id())
    {
        for argument in application.arguments() {
            collect_binder_variables_in_pure_argument(
                argument,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
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
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        CValue::Void => {}
        CValue::Int8(bits) => collect_bitvector_binder_variables_seen(
            bits,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::Int32(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Int128(bits)
        | CValue::UInt128(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => collect_bitvector_binder_variables_seen(
            bits,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        CValue::Pointer(pointer) => {
            collect_pointer_binder_variables(
                pointer.pointer(),
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if let Some(designation) = pointer.designation() {
                for term in designation.pointer_terms() {
                    collect_pointer_binder_variables(
                        term,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                for term in designation.integer_terms() {
                    collect_integer_binder_variables_shared(
                        term,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
            }
        }
    }
}

fn collect_binder_variables_in_pure_argument(
    argument: &PureFunctionArgument,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
    integer_seen: &mut SeenTerms,
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
        PointerOffsetTerm::Constant(_) => {}
        PointerOffsetTerm::Variable(variable) => {
            if collecting_connection_variables() {
                variables.insert(*variable);
            }
        }
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
    CONNECTION_BLOCKS.with(|blocks| {
        // ExternalArgument is the shared address arena of all formal array
        // parameters. Their offset variables identify the actual objects;
        // sharing that arena must not connect otherwise unrelated arrays.
        // Null is another shared constant: unrelated non-null assertions must
        // not connect all their objects through the null pointer.
        if let Some(blocks) = blocks.borrow_mut().as_mut()
            && !matches!(
                pointer.block,
                PointerBlock::ExternalArgument
                    | PointerBlock::Symbolic(_)
                    | PointerBlock::FunctionSymbolic(_)
                    | PointerBlock::ExternalObject(_)
            )
            && !pointer.is_in_null_block()
        {
            blocks.insert(pointer.block.clone());
        }
    });
    match &pointer.block {
        PointerBlock::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_capture_variables_in_pure_argument(
                    argument,
                    variables,
                    &mut SeenTerms::default(),
                );
            }
        }
        PointerBlock::Symbolic(variable)
        | PointerBlock::FunctionSymbolic(variable)
        | PointerBlock::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::LoadedPointer(_)
        | PointerBlock::Heap(_)
        | PointerBlock::Temporary(_) => {}
    }
    collect_pointer_offset_bitvector_variables(&pointer.offset, variables);
}

#[cfg(test)]
thread_local! {
    /// How many concrete and union cells, and how many run slots, variable
    /// collection has visited on this thread: the scaling regressions'
    /// measure of a collection, whose visits are not all charged.
    static CELLS_COLLECTED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `operation`'s result and how many cells and run slots variable
/// collection visited while it ran.
#[cfg(test)]
pub(crate) fn count_cells_collected<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    let before = CELLS_COLLECTED.with(std::cell::Cell::get);
    let result = operation();
    let after = CELLS_COLLECTED.with(std::cell::Cell::get);
    (result, after - before)
}

/// The variables a run's cells mention.
///
/// Each slot mentions its pointer's variables and its value's: the value is
/// the slot's load variable, which also mentions the memory and pointer it
/// names. A load run retains its source snapshot and base address, which
/// contain every ordinary variable a slot's resolved value can depend on.
/// Collect that dependency closure rather than minting a name for every
/// slot. The slots' own load IDs are in the reserved range no fresh binder
/// source allocates from, so excluding unobserved IDs cannot introduce a
/// binder collision. An actual read still collects its addressed value and
/// load origin normally. Including unrelated represented source variables
/// is conservative for freshness and premise connection.
fn collect_cell_run_bitvector_variables(
    run: &crate::kernel::primitives::CellRun,
    variables: &mut BTreeSet<Variable>,
) {
    match run_representative_variables(run) {
        Some(shared) => variables.extend(shared),
        None => {
            for index in run.live_indexes() {
                collect_run_slot_bitvector_variables(run, index, variables);
            }
        }
    }
}

/// The variables of one slot of a run: its pointer's and its value's.
fn collect_run_slot_bitvector_variables(
    run: &crate::kernel::primitives::CellRun,
    index: u32,
    variables: &mut BTreeSet<Variable>,
) {
    #[cfg(test)]
    CELLS_COLLECTED.with(|visited| visited.set(visited.get() + 1));
    collect_pointer_bitvector_variables(&run.slot_pointer(index), variables);
    collect_c_value_bitvector_variables(&run.value(index), variables);
}

/// The variables a run's representative slots mention, when they stand for
/// the whole run (see [`collect_cell_run_bitvector_variables`]); `None` when
/// every slot has to be visited.
fn run_representative_variables(
    run: &crate::kernel::primitives::CellRun,
) -> Option<BTreeSet<Variable>> {
    match run.value_mode() {
        crate::kernel::primitives::RunValueMode::SymbolicStorage => {
            return Some(symbolic_storage_run_shared_variables(run));
        }
        crate::kernel::primitives::RunValueMode::Constant(value) => {
            return Some(constant_run_variables(run, value));
        }
        crate::kernel::primitives::RunValueMode::Copy { source_base } => {
            let mut shared = symbolic_storage_run_shared_variables(run);
            collect_pointer_bitvector_variables(source_base, &mut shared);
            return Some(shared);
        }
        crate::kernel::primitives::RunValueMode::Load => {
            return Some(symbolic_storage_run_shared_variables(run));
        }
    }
}

/// The variables every slot of a symbolic static-storage run mentions
/// besides its own load variable, found without naming any slot.
///
/// Slot `i` holds the entry value of storage the function knows nothing
/// about ([`crate::kernel::eval::symbolic_storage_cell_value`]): its own load
/// of the slot's pointer in the run's source, which holds only the storage's
/// block, spelled as a load variable (or a symbolic pointer named by one).
/// What such a value mentions is that load variable and, through it, the
/// source and the slot's pointer; every slot's pointer is the base plus a
/// constant, so the base's variables and the source's are what every slot
/// shares. They are returned here, and the slots' own load variables are
/// left out, for the reasons [`collect_cell_run_bitvector_variables`] gives
/// for a run's non-representative slots: they are in the reserved load
/// range, so no caller avoiding what a memory mentions can collide with one,
/// and a substitution of one finds its slot by the registry
/// (`run_slot_named_by_load_variable`), not by these variables. Unlike a
/// representative-backed run, a global array's slots often share no variable
/// at all, so a premise search that grows its premises by shared variables
/// does not reach this memory from a fact about one element; such a search
/// only chooses premises, so it can miss a proof but not admit one. Naming each
/// slot to collect its variable instead made every collection over a
/// million-element global array mint a million load identities, exhausting
/// the load registry at function entry, and cost the array's length per
/// collection. A slot's identity is minted when the slot is first read.
fn symbolic_storage_run_shared_variables(
    run: &crate::kernel::primitives::CellRun,
) -> BTreeSet<Variable> {
    crate::instrumentation::record_deterministic_work(1);
    let mut shared = BTreeSet::new();
    collect_pointer_bitvector_variables(run.base(), &mut shared);
    collect_shared_memory_bitvector_variables(run.source(), &mut shared);
    shared
}

/// The variables every slot of a constant run mentions: its base pointer's
/// and its one value's. Each slot's pointer is the base plus a constant and
/// each holds that value, so these are exactly the variables of every slot,
/// found without visiting one.
fn constant_run_variables(
    run: &crate::kernel::primitives::CellRun,
    value: &CValue,
) -> BTreeSet<Variable> {
    crate::instrumentation::record_deterministic_work(1);
    let mut shared = BTreeSet::new();
    collect_pointer_bitvector_variables(run.base(), &mut shared);
    collect_c_value_bitvector_variables(value, &mut shared);
    shared
}

/// How many of a snapshot's entries (blocks, concrete cells, runs, union
/// cells) mention each variable. Persistent, so a snapshot's counts share
/// every unchanged node with its derivation base's.
type VariableCounts = crate::persistent::PersistentMap<Variable, u32>;

thread_local! {
    /// The variables each interned snapshot mentions, by arena identity, for
    /// the whole verification session, as counts per entry.
    ///
    /// A snapshot's cells hold loads of earlier snapshots, directly or
    /// through load variables, so the snapshots a collection reaches are a
    /// DAG, and a later snapshot holds every cell of the history before it.
    /// Walking each reached snapshot whole per collection made a collection
    /// cost the whole memory, and walking the DAG as a tree cost every path
    /// to each snapshot. Here a snapshot's counts are its derivation base's
    /// adjusted by the entries the two differ on, which the persistent maps'
    /// diffs visit without the shared rest, so a store or an allocation costs
    /// what it changed, and each snapshot is counted once per session.
    ///
    /// The answer is a function of the snapshot's content and of the load
    /// registry, which never renames or drops a load variable within a
    /// session, and arena identities are never reused, so remembered counts
    /// cannot go stale. [`clear_shared_memory_variables`] empties the table
    /// at every outermost [`crate::kernel::VerificationSession`] entry, which
    /// also clears the registry and starts a fresh arena.
    static SHARED_MEMORY_VARIABLES: std::cell::RefCell<
        std::collections::HashMap<(u32, u32), VariableCounts>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    // Pointer-read projections share heap metadata even when their selected
    // cells differ. Retain the root, so an address cannot be reused for a hit.
    static HEAP_VARIABLES: std::cell::RefCell<Option<(std::sync::Arc<crate::kernel::primitives::CHeapMemory>, VariableCounts)>> = const { std::cell::RefCell::new(None) };
}

/// Forgets every snapshot's remembered variables; see
/// [`SHARED_MEMORY_VARIABLES`].
pub(in crate::kernel) fn clear_shared_memory_variables() {
    super::substitution::clear_shared_memory_bound_variables();
    SHARED_MEMORY_VARIABLES.with(|table| table.borrow_mut().clear());
    HEAP_VARIABLES.with(|table| *table.borrow_mut() = None);
}

fn remembered_memory_variables(memory: &SharedCMemory) -> Option<VariableCounts> {
    SHARED_MEMORY_VARIABLES.with(|table| table.borrow().get(&memory.arena_id()).cloned())
}

/// [`collect_memory_bitvector_variables`] of an interned snapshot, counted
/// once per verification session from its derivation base's counts. Counting
/// charges one unit per entry and per derivation step it visits; a snapshot
/// already counted is an indexed lookup plus the variables it hands back.
pub(in crate::kernel) fn collect_shared_memory_bitvector_variables(
    memory: &SharedCMemory,
    variables: &mut BTreeSet<Variable>,
) {
    if COLLECTING_HAVOC_RANGES.with(std::cell::Cell::get) {
        // The ranges a call or loop wrote to reach this snapshot: a fact
        // about one of their bounds is what frames a load across the edge.
        let mut current = memory.clone();
        for _ in 0..HAVOC_RANGE_HOPS {
            let Some(derivation) = current.derivation() else {
                break;
            };
            crate::instrumentation::record_deterministic_work(1);
            match derivation.as_ref() {
                CMemoryDerivation::Store { pointer, .. } => {
                    collect_pointer_bitvector_variables(pointer, variables);
                }
                CMemoryDerivation::CallHavoc { mutable_ranges, .. } => {
                    for range in mutable_ranges {
                        collect_c_memory_range_bitvector_variables(range, variables);
                    }
                }
                CMemoryDerivation::LoopHavoc {
                    mutable_ranges: Some(mutable_ranges),
                    ..
                } => {
                    for range in mutable_ranges {
                        collect_c_memory_range_bitvector_variables(range, variables);
                    }
                }
                _ => {}
            }
            current = derivation.base().clone();
        }
    }
    if collecting_connection_variables() || defer_condition_snapshot() {
        return;
    }

    variables.extend(
        shared_memory_variable_counts(memory, WholeCount::Charged)
            .keys()
            .copied(),
    );
}

/// Whether counting a snapshot of the chain whole is charged; see
/// [`collect_memory_bitvector_variables`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum WholeCount {
    Charged,
    Uncharged,
}

fn shared_memory_variable_counts(memory: &SharedCMemory, whole: WholeCount) -> VariableCounts {
    if let Some(counts) = remembered_memory_variables(memory) {
        return counts;
    }
    // The uncounted derivation ancestors, nearest first, up to one already
    // counted or with no recorded base. The walk is cut at the snapshot's own
    // size: past that, counting the snapshot whole costs less than counting
    // its history.
    let limit = memory_entry_count(memory.memory());
    let mut chain = vec![memory.clone()];
    let mut counted_base = None;
    while chain.len() <= limit {
        let Some(derivation) = chain
            .last()
            .expect("the chain starts nonempty")
            .derivation()
        else {
            break;
        };
        let base = derivation.base().clone();
        crate::instrumentation::record_deterministic_work(1);
        if let Some(counts) = remembered_memory_variables(&base) {
            counted_base = Some((base, counts));
            break;
        }
        chain.push(base);
    }
    if counted_base.is_none() && chain.len() > limit {
        // Too long a history: count this snapshot alone, whole.
        chain.truncate(1);
    }
    // Oldest first: each snapshot is counted from the one before it.
    let mut previous = counted_base;
    for snapshot in chain.into_iter().rev() {
        let counts = match &previous {
            Some((base, counts)) => {
                counts_from_base(counts.clone(), base.memory(), snapshot.memory())
            }
            None => counts_whole(snapshot.memory(), whole),
        };
        SHARED_MEMORY_VARIABLES.with(|table| {
            table
                .borrow_mut()
                .insert(snapshot.arena_id(), counts.clone());
        });
        previous = Some((snapshot, counts));
    }
    previous.expect("the chain counts at least the snapshot").1
}

fn memory_entry_count(memory: &CMemory) -> usize {
    memory.blocks.len()
        + memory.cells.representation_len()
        + memory.union_cells.len()
        + memory.heap.uninitialized_objects.len()
        + memory.heap.object_input_domains.len()
        + memory.heap.scalar_input_domains.len()
        + memory.heap.native_record_inputs.len()
        + memory.heap.initialized.as_map().len()
        + memory.heap.pending_reallocations.len()
}

fn add_counts(counts: &mut VariableCounts, mentioned: BTreeSet<Variable>, sign: i64) {
    for variable in mentioned {
        let held = i64::from(counts.get(&variable).copied().unwrap_or(0));
        let count = held + sign;
        debug_assert!(
            count >= 0,
            "an entry's variables are counted before removal"
        );
        if count <= 0 {
            counts.remove(&variable);
        } else {
            counts.insert(
                variable,
                u32::try_from(count).expect("entry counts fit in u32"),
            );
        }
    }
}

fn block_variables(block: &PointerBlock, contents: &CBlock) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    match block {
        PointerBlock::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_capture_variables_in_pure_argument(
                    argument,
                    &mut variables,
                    &mut SeenTerms::default(),
                );
            }
        }
        PointerBlock::Symbolic(variable)
        | PointerBlock::FunctionSymbolic(variable)
        | PointerBlock::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::LoadedPointer(_)
        | PointerBlock::Heap(_)
        | PointerBlock::Temporary(_) => {}
    }
    // A memory-havoc marker spells the identity it was minted with in its
    // block name instead of carrying it in a term, so a scan of the
    // state's terms alone does not see it. Reserving it here is what lets
    // every caller that must avoid what a state already mentions -- a
    // branch join's abstraction, a loop head's stream, a constructor
    // witness -- see it without harvesting block names by hand.
    for prefix in ["havoc:", "call-havoc:"] {
        if let Some(index) = block
            .strip_prefix(prefix)
            .and_then(|index| index.parse::<u64>().ok())
        {
            variables.insert(Variable(index));
        }
    }
    collect_bitvector_variables(contents.size(), &mut variables);
    variables
}

fn object_address_variables(pointer: &Pointer) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_pointer_bitvector_variables(pointer, &mut variables);
    variables
}

fn native_record_input_variables(row: &CNativeRecordInput) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_c_value_bitvector_variables(&CValue::Pointer(row.origin.clone()), &mut variables);
    if let CNativeInputKind::TypedPrefix { count, .. }
    | CNativeInputKind::RecordPrefix { count, .. }
    | CNativeInputKind::AllocatedScalar { bytes: count, .. } = &row.kind
    {
        collect_integer_variables(count.as_ref(), &mut variables);
    }
    variables
}

fn cell_variables(pointer: &Pointer, value: &CValue) -> BTreeSet<Variable> {
    #[cfg(test)]
    CELLS_COLLECTED.with(|visited| visited.set(visited.get() + 1));
    let mut variables = BTreeSet::new();
    collect_pointer_bitvector_variables(pointer, &mut variables);
    collect_c_value_bitvector_variables(value, &mut variables);
    variables
}

fn collect_pending_reallocation_variables(
    base: &Pointer,
    pending: &CPendingReallocation,
    variables: &mut BTreeSet<Variable>,
) {
    crate::instrumentation::record_deterministic_work(pending.copied_cells.len());
    collect_pointer_bitvector_variables(base, variables);
    collect_c_value_bitvector_variables(&CValue::Pointer(pending.old_pointer.clone()), variables);
    collect_bitvector_variables(&pending.old_bytes, variables);
    if let Some(prefix) = &pending.zeroed_prefix {
        collect_bitvector_variables(prefix, variables);
    }
    for (offset, value) in &pending.copied_cells {
        collect_pointer_offset_bitvector_variables(offset, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
}

fn pending_reallocation_variables(
    base: &Pointer,
    pending: &CPendingReallocation,
) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_pending_reallocation_variables(base, pending, &mut variables);
    variables
}

/// Counts a run's variables in or out: as one entry when its
/// representatives stand for it, and otherwise as one entry per live slot.
/// Either way the variables counted are exactly the run's
/// ([`collect_cell_run_bitvector_variables`]); per slot, a store into the run
/// changes the counts by the slots it changes rather than by the whole run.
fn add_run_counts(
    counts: &mut VariableCounts,
    run: &crate::kernel::primitives::CellRun,
    sign: i64,
) {
    match run_representative_variables(run) {
        Some(shared) => add_counts(counts, shared, sign),
        None => {
            for index in run.live_indexes() {
                crate::instrumentation::record_deterministic_work(1);
                add_counts(counts, run_slot_variables(run, index), sign);
            }
        }
    }
}

fn run_slot_variables(run: &crate::kernel::primitives::CellRun, index: u32) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_run_slot_bitvector_variables(run, index, &mut variables);
    variables
}

#[cfg(test)]
mod compressed_run_dependency_tests {
    use super::*;

    #[test]
    fn load_run_dependency_closure_keeps_source_values_without_naming_slots() {
        let mut samples = Vec::new();
        for count in [8, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let base_variable = Variable(9_381_010);
            let source_variable = Variable(9_381_011);
            let value_variable = Variable(9_381_012);
            let source = CMemory::new().store(
                Pointer::symbolic(source_variable),
                CValue::UInt32(Bitvector32Term::Variable(value_variable)),
            );
            let run = crate::kernel::primitives::CellRun::new(
                Pointer::symbolic(base_variable),
                4,
                CType::UInt32,
                count,
                crate::kernel::intern_c_memory(source),
                crate::kernel::primitives::IndexIntervals::default(),
            );
            let ((variables, visits), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    count_cells_collected(|| {
                        let mut variables = BTreeSet::new();
                        collect_cell_run_bitvector_variables(&run, &mut variables);
                        variables
                    })
                });
            for variable in [base_variable, source_variable, value_variable] {
                assert!(variables.contains(&variable));
            }
            assert!(
                visits <= 1,
                "collection must visit only the represented source cell: {visits}"
            );
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }
}

/// A run held on both sides of a diff with other holes, counted per slot on
/// both: only the slots whose liveness differs change the counts. `false`
/// when either side is counted as one entry, and the caller counts the two
/// sides whole.
fn adjust_run_counts_by_changed_slots(
    counts: &mut VariableCounts,
    before: &crate::kernel::primitives::CellRun,
    after: &crate::kernel::primitives::CellRun,
) -> bool {
    if !before.same_slots_as(after)
        || run_representative_variables(before).is_some()
        || run_representative_variables(after).is_some()
    {
        return false;
    }
    let changed = before.holes().symmetric_difference(after.holes());
    crate::instrumentation::record_deterministic_work(changed.interval_count());
    for index in changed.indexes() {
        crate::instrumentation::record_deterministic_work(1);
        // The two runs have the same slots holding the same values, so a
        // slot's variables are the same on both sides.
        let sign = if after.holes().contains(index) { -1 } else { 1 };
        add_counts(counts, run_slot_variables(before, index), sign);
    }
    true
}

/// Apply each changed heap entry exactly once, both to a retained heap cache
/// and to a memory derivation's full counts. Persistent diffs skip shared maps.
fn adjust_heap_variable_counts(
    counts: &mut VariableCounts,
    base: &crate::kernel::primitives::CHeapMemory,
    heap: &crate::kernel::primitives::CHeapMemory,
) {
    if std::ptr::eq(base, heap) {
        return;
    }
    for (before, after) in [
        (&base.uninitialized_objects, &heap.uninitialized_objects),
        (base.initialized.as_map(), heap.initialized.as_map()),
    ] {
        for change in before.diff(after) {
            crate::instrumentation::record_deterministic_work(1);
            let pointer = change.key();
            if before.contains_key(pointer) {
                add_counts(counts, object_address_variables(pointer), -1);
            }
            if after.contains_key(pointer) {
                add_counts(counts, object_address_variables(pointer), 1);
            }
        }
    }
    for change in base.object_input_domains.diff(&heap.object_input_domains) {
        crate::instrumentation::record_deterministic_work(1);
        let pointer = change.key();
        if base.object_input_domains.contains_key(pointer) {
            add_counts(counts, object_address_variables(pointer), -1);
        }
        if heap.object_input_domains.contains_key(pointer) {
            add_counts(counts, object_address_variables(pointer), 1);
        }
    }
    for change in base.scalar_input_domains.diff(&heap.scalar_input_domains) {
        crate::instrumentation::record_deterministic_work(1);
        let pointer = change.key();
        if base.scalar_input_domains.contains_key(pointer) {
            add_counts(counts, object_address_variables(pointer), -1);
        }
        if heap.scalar_input_domains.contains_key(pointer) {
            add_counts(counts, object_address_variables(pointer), 1);
        }
    }
    for change in base.native_record_inputs.diff(&heap.native_record_inputs) {
        crate::instrumentation::record_deterministic_work(1);
        let identity = change.key();
        if let Some(row) = base.native_record_inputs.get(identity) {
            add_counts(counts, native_record_input_variables(row), -1);
        }
        if let Some(row) = heap.native_record_inputs.get(identity) {
            add_counts(counts, native_record_input_variables(row), 1);
        }
    }
    for change in base.pending_reallocations.diff(&heap.pending_reallocations) {
        crate::instrumentation::record_deterministic_work(1);
        let pointer = change.key();
        if let Some(pending) = base.pending_reallocations.get(pointer) {
            add_counts(counts, pending_reallocation_variables(pointer, pending), -1);
        }
        if let Some(pending) = heap.pending_reallocations.get(pointer) {
            add_counts(counts, pending_reallocation_variables(pointer, pending), 1);
        }
    }
}

/// A heap's counts from all semantic variable-bearing entries, retained by
/// Arc identity independently of a read projection's selected cells.
fn heap_variable_counts(
    heap: &std::sync::Arc<crate::kernel::primitives::CHeapMemory>,
    whole: WholeCount,
) -> VariableCounts {
    let previous = HEAP_VARIABLES.with(|table| table.borrow().clone());
    let counts = if let Some((base, mut counts)) = previous {
        if std::sync::Arc::ptr_eq(&base, heap) {
            return counts;
        }
        adjust_heap_variable_counts(&mut counts, &base, heap);
        counts
    } else {
        if whole == WholeCount::Charged {
            crate::instrumentation::record_deterministic_work(
                heap.uninitialized_objects.len()
                    + heap.initialized.as_map().len()
                    + heap.object_input_domains.len()
                    + heap.scalar_input_domains.len()
                    + heap.native_record_inputs.len()
                    + heap.pending_reallocations.len(),
            );
        }
        let mut counts = VariableCounts::default();
        for pointer in heap
            .uninitialized_objects
            .keys()
            .chain(heap.initialized.as_map().keys())
            .chain(heap.object_input_domains.keys())
            .chain(heap.scalar_input_domains.keys())
        {
            add_counts(&mut counts, object_address_variables(pointer), 1);
        }
        for row in heap.native_record_inputs.values() {
            add_counts(&mut counts, native_record_input_variables(row), 1);
        }
        for (base, pending) in heap.pending_reallocations.iter() {
            add_counts(
                &mut counts,
                pending_reallocation_variables(base, pending),
                1,
            );
        }
        counts
    };
    HEAP_VARIABLES.with(|table| *table.borrow_mut() = Some((heap.clone(), counts.clone())));
    counts
}

fn counts_whole(memory: &CMemory, whole: WholeCount) -> VariableCounts {
    if whole == WholeCount::Charged {
        crate::instrumentation::record_deterministic_work(
            memory.blocks.len() + memory.cells.representation_len() + memory.union_cells.len(),
        );
    }
    // Start from the retained heap counts, rather than enumerating their
    // variables to combine them with each selected read projection.
    let mut counts = heap_variable_counts(&memory.heap, whole);
    for (block, contents) in memory.blocks.iter() {
        add_counts(&mut counts, block_variables(block, contents), 1);
    }
    for (pointer, value) in memory.cells.concrete().iter() {
        add_counts(&mut counts, cell_variables(pointer, value), 1);
    }
    for run in memory.cells.runs() {
        add_run_counts(&mut counts, run, 1);
    }
    for ((pointer, _), value) in memory.union_cells.iter() {
        add_counts(&mut counts, cell_variables(pointer, value), 1);
    }
    counts
}

/// `memory`'s counts from `base`'s: each entry the two differ on leaves with
/// its old variables and arrives with its new ones. The diffs charge one unit
/// per difference.
fn counts_from_base(
    mut counts: VariableCounts,
    base: &CMemory,
    memory: &CMemory,
) -> VariableCounts {
    for change in base.blocks.diff(&memory.blocks) {
        let block = change.key();
        if let Some(contents) = base.blocks.get(block) {
            add_counts(&mut counts, block_variables(block, contents), -1);
        }
        if let Some(contents) = memory.blocks.get(block) {
            add_counts(&mut counts, block_variables(block, contents), 1);
        }
    }
    adjust_heap_variable_counts(&mut counts, &base.heap, &memory.heap);
    for change in base.cells.concrete().diff(memory.cells.concrete()) {
        let pointer = change.key();
        if let Some(value) = base.cells.concrete().get(pointer) {
            add_counts(&mut counts, cell_variables(pointer, value), -1);
        }
        if let Some(value) = memory.cells.concrete().get(pointer) {
            add_counts(&mut counts, cell_variables(pointer, value), 1);
        }
    }
    for (before, after) in base.cells.run_diff(&memory.cells) {
        if let (Some(before), Some(after)) = (before, after)
            && adjust_run_counts_by_changed_slots(&mut counts, before, after)
        {
            continue;
        }
        if let Some(run) = before {
            add_run_counts(&mut counts, run, -1);
        }
        if let Some(run) = after {
            add_run_counts(&mut counts, run, 1);
        }
    }
    for change in base.union_cells.diff(&memory.union_cells) {
        let key = change.key();
        if let Some(value) = base.union_cells.get(key) {
            add_counts(&mut counts, cell_variables(&key.0, value), -1);
        }
        if let Some(value) = memory.union_cells.get(key) {
            add_counts(&mut counts, cell_variables(&key.0, value), 1);
        }
    }
    counts
}

/// An interned snapshot a cell's load reaches is walked through
/// [`collect_shared_memory_bitvector_variables`], once per session.
pub(in crate::kernel) fn collect_memory_bitvector_variables(
    memory: &CMemory,
    variables: &mut BTreeSet<Variable>,
) {
    if collecting_connection_variables() {
        return;
    }
    if defer_condition_snapshot() {
        return;
    }

    // A live state's memory is the interned storage its last derivation
    // left, so its variables are that snapshot's remembered counts, counted
    // once per session from its derivation base's: the work of what changed,
    // not of every cell and run slot again on every collection. Where its
    // history reaches no counted snapshot, one of its chain is counted
    // whole: that is the walk every collection of it made, uncharged, before
    // the counts were kept, and it stays uncharged; the steps back to a
    // counted snapshot and the entries they changed are charged, as are the
    // snapshots its cells' loads reach.
    if let Some(shared) = crate::kernel::primitives::interned_storage_of(memory) {
        variables.extend(
            shared_memory_variable_counts(&shared, WholeCount::Uncharged)
                .keys()
                .copied(),
        );
        return;
    }
    collect_memory_bitvector_variables_whole(memory, variables);
}

/// [`collect_memory_bitvector_variables`] by visiting every entry of
/// `memory`, for a snapshot no derivation interned. The counts of
/// [`shared_memory_variable_counts`] are built from the same per-entry
/// collectors, so the two agree on every snapshot.
pub(in crate::kernel) fn collect_memory_bitvector_variables_whole(
    memory: &CMemory,
    variables: &mut BTreeSet<Variable>,
) {
    if collecting_connection_variables() {
        return;
    }
    if defer_condition_snapshot() {
        return;
    }

    for (block, contents) in memory.blocks.iter() {
        match block {
            PointerBlock::PureFunctionApplication(application) => {
                for argument in application.arguments() {
                    collect_capture_variables_in_pure_argument(
                        argument,
                        variables,
                        &mut SeenTerms::default(),
                    );
                }
            }
            PointerBlock::Symbolic(variable)
            | PointerBlock::FunctionSymbolic(variable)
            | PointerBlock::ExternalObject(variable) => {
                variables.insert(*variable);
            }
            PointerBlock::Concrete(_)
            | PointerBlock::StringLiteral { .. }
            | PointerBlock::Function(_)
            | PointerBlock::ExternalArgument
            | PointerBlock::LoadedPointer(_)
            | PointerBlock::Heap(_)
            | PointerBlock::Temporary(_) => {}
        }
        // A memory-havoc marker spells the identity it was minted with in its
        // block name instead of carrying it in a term, so a scan of the
        // state's terms alone does not see it. Reserving it here is what lets
        // every caller that must avoid what a state already mentions -- a
        // branch join's abstraction, a loop head's stream, a constructor
        // witness -- see it without harvesting block names by hand.
        for prefix in ["havoc:", "call-havoc:"] {
            if let Some(index) = block
                .strip_prefix(prefix)
                .and_then(|index| index.parse::<u64>().ok())
            {
                variables.insert(Variable(index));
            }
        }
        collect_bitvector_variables(contents.size(), variables);
    }
    for pointer in memory
        .heap
        .uninitialized_objects
        .keys()
        .chain(memory.heap.initialized.as_map().keys())
        .chain(memory.heap.object_input_domains.keys())
        .chain(memory.heap.scalar_input_domains.keys())
    {
        collect_pointer_bitvector_variables(pointer, variables);
    }
    for row in memory.heap.native_record_inputs.values() {
        collect_c_value_bitvector_variables(&CValue::Pointer(row.origin.clone()), variables);
        if let CNativeInputKind::TypedPrefix { count, .. }
        | CNativeInputKind::RecordPrefix { count, .. }
        | CNativeInputKind::AllocatedScalar { bytes: count, .. } = &row.kind
        {
            collect_integer_variables(count.as_ref(), variables);
        }
    }
    for (pointer, value) in memory.cells.concrete().iter() {
        #[cfg(test)]
        CELLS_COLLECTED.with(|visited| visited.set(visited.get() + 1));
        collect_pointer_bitvector_variables(pointer, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
    for run in memory.cells.runs() {
        collect_cell_run_bitvector_variables(run, variables);
    }
    for ((pointer, _), value) in memory.union_cells.iter() {
        collect_pointer_bitvector_variables(pointer, variables);
        collect_c_value_bitvector_variables(value, variables);
    }
    for (base, pending) in memory.heap.pending_reallocations.iter() {
        collect_pending_reallocation_variables(base, pending, variables);
    }
}

pub(crate) fn collect_c_value_bitvector_variables(
    value: &CValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        CValue::Void => {}
        CValue::Int8(bits) => collect_bitvector_variables(bits, variables),
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Int128(bits)
        | CValue::UInt128(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => collect_bitvector_variables(bits, variables),
        CValue::Pointer(pointer) => {
            collect_pointer_bitvector_variables(pointer.pointer(), variables);
            if let Some(designation) = pointer.designation() {
                // Match scalar MemoryLoad collection: its retained snapshot
                // participates in whole-memory variable/connection queries,
                // while the lexical collectors above inspect only addresses.
                if let Some(identity) = designation.loaded_identity() {
                    collect_shared_memory_bitvector_variables(identity.memory(), variables);
                    collect_stored_load_connection_variables(
                        identity.memory(),
                        identity.address(),
                        variables,
                    );
                }
                if let Some(variable) = designation.unresolved_variable() {
                    variables.insert(variable);
                }
                for term in designation.pointer_terms() {
                    collect_pointer_bitvector_variables(term, variables);
                }
                for term in designation.integer_terms() {
                    collect_shared_integer_variables(term, variables, &mut SeenTerms::default());
                }
            }
        }
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

#[cfg(test)]
mod heap_variable_projection_tests {
    use super::*;

    #[test]
    fn heap_native_metadata_counts_share_projections_and_follow_exact_deltas() {
        let mut edits = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |id| Pointer::symbolic(Variable(id));
            let layout = std::sync::Arc::new(CAggregateLayout::new(
                4,
                4,
                vec![CAggregateField::new("value", 0, CType::Int32)],
            ));
            let row = |id| CNativeRecordInput {
                origin: CPointerValue::new(pointer(10_000 + id), CType::Int32Pointer)
                    .with_designation(PointerDesignation::Unresolved(Variable(id))),
                kind: match id % 3 {
                    0 => CNativeInputKind::Record {
                        layout: layout.clone(),
                    },
                    1 => CNativeInputKind::RecordPrefix {
                        layout: layout.clone(),
                        count: IntegerTerm::Variable(Variable(20_000 + id)).into(),
                    },
                    _ => CNativeInputKind::TypedPrefix {
                        element_type: CType::Int32,
                        count: IntegerTerm::Variable(Variable(20_000 + id)).into(),
                        policy: CTypedAccessPolicy::NativeObjectOnly,
                    },
                },
            };
            let mut heap = crate::kernel::primitives::CHeapMemory::default();
            for id in 1..=size {
                heap.object_input_domains
                    .insert(pointer(30_000 + id), layout.clone());
                heap.scalar_input_domains
                    .insert(pointer(40_000 + id), CType::Int32);
                heap.native_record_inputs
                    .insert(CNativeInputIdentity::Unresolved(Variable(id)), row(id));
            }
            let cell = pointer(500_001);
            let read_memory = CMemory::new().with_block(cell.block.clone(), 8).store(
                cell.clone(),
                CValue::typed_pointer(pointer(500_002), CType::Int32Pointer),
            );
            let snapshot = intern_c_memory(read_memory);
            let read = PointerLoadIdentity::new(snapshot.clone(), cell.clone());
            heap.native_record_inputs.insert(
                CNativeInputIdentity::Loaded(read.clone()),
                CNativeRecordInput {
                    origin: CPointerValue::new(
                        Pointer::loaded_value(&snapshot, &cell),
                        CType::Int32Pointer,
                    )
                    .with_designation(PointerDesignation::Loaded(read)),
                    kind: CNativeInputKind::Record {
                        layout: layout.clone(),
                    },
                },
            );
            heap.pending_reallocations.insert(
                pointer(600_000),
                CPendingReallocation {
                    old_pointer: CPointerValue::new(pointer(70_001), CType::Int32Pointer)
                        .with_designation(PointerDesignation::Object {
                            root: pointer(80_001),
                            path: vec![PointerDomainSelection::Element(
                                IntegerTerm::Variable(Variable(90_001)).into(),
                            )]
                            .into(),
                            base: pointer(100_001),
                            element_type: CType::Int32,
                            stride: 4,
                            count: IntegerTerm::Variable(Variable(20_002)).into(),
                        }),
                    old_bytes: Bitvector32Term::Variable(Variable(110_000)),
                    zeroed_prefix: Some(Bitvector32Term::Variable(Variable(120_000))),
                    copied_cells: vec![(
                        PointerOffsetTerm::scale_int32(
                            Bitvector32Term::Variable(Variable(130_000)),
                            4,
                        ),
                        CValue::typed_pointer(pointer(140_000), CType::Int32Pointer),
                    )],
                    initialized_prefix: vec![(0, 4)],
                },
            );
            let heap = std::sync::Arc::new(heap);
            let original = heap_variable_counts(&heap, WholeCount::Charged);
            for id in [
                20_002, 70_001, 80_001, 90_001, 100_001, 110_000, 120_000, 130_000, 140_000,
                500_001, 500_002, 600_000,
            ] {
                assert!(
                    original.contains_key(&Variable(id)),
                    "complete carrier variable {id}"
                );
            }
            let selected = CMemory {
                heap: heap.clone(),
                ..CMemory::new().with_block("selected:native-read", 4)
            };
            let (projected, work) = crate::instrumentation::measure_deterministic_work(|| {
                counts_whole(&selected, WholeCount::Charged)
            });
            assert_eq!(projected, original);
            assert_eq!(work, 1, "projection scanned {size} native rows");
            let mut changed = (*heap).clone();
            changed.object_input_domains.remove(&pointer(30_001));
            changed
                .scalar_input_domains
                .insert(pointer(40_001), CType::UInt32);
            changed
                .native_record_inputs
                .remove(&CNativeInputIdentity::Unresolved(Variable(1)));
            let mut replacement = row(2);
            replacement.kind = CNativeInputKind::TypedPrefix {
                element_type: CType::Int32,
                count: IntegerTerm::Variable(Variable(900_000)).into(),
                policy: CTypedAccessPolicy::NativeObjectOnly,
            };
            changed
                .native_record_inputs
                .insert(CNativeInputIdentity::Unresolved(Variable(2)), replacement);
            let changed = std::sync::Arc::new(changed);
            let (counts, work) = crate::instrumentation::measure_deterministic_work(|| {
                heap_variable_counts(&changed, WholeCount::Charged)
            });
            edits.push(work);
            assert!(!counts.contains_key(&Variable(1)));
            assert!(!counts.contains_key(&Variable(10_001)));
            assert!(!counts.contains_key(&Variable(20_001)));
            assert!(!counts.contains_key(&Variable(30_001)));
            assert!(counts.contains_key(&Variable(900_000)));
            assert!(
                counts.contains_key(&Variable(20_002)),
                "pending full carrier still mentions the old count"
            );
            let changed_memory = CMemory {
                heap: changed.clone(),
                ..selected.clone()
            };
            assert_eq!(
                counts_from_base(original.clone(), &selected, &changed_memory),
                counts
            );
            let mut reference = BTreeSet::new();
            collect_memory_bitvector_variables_whole(&changed_memory, &mut reference);
            assert_eq!(reference, counts.keys().copied().collect());
            let mut retired = (*changed).clone();
            retired.pending_reallocations.clear();
            let retired = std::sync::Arc::new(retired);
            let retired_counts = heap_variable_counts(&retired, WholeCount::Charged);
            assert!(
                !retired_counts.contains_key(&Variable(20_002)),
                "all mentions must retire exactly once"
            );
            assert_eq!(heap_variable_counts(&heap, WholeCount::Charged), original);
            assert_eq!(heap_variable_counts(&changed, WholeCount::Charged), counts);
            assert!(
                heap_variable_counts(
                    &std::sync::Arc::new(crate::kernel::primitives::CHeapMemory::default()),
                    WholeCount::Charged
                )
                .is_empty()
            );
        }
        assert!(
            edits.iter().all(|work| *work == edits[0]),
            "selected heap edits scanned ambient metadata: {edits:?}"
        );
    }

    #[test]
    fn heap_variable_counts_follow_local_edits_and_keep_siblings_isolated() {
        for size in [16u64, 64, 256, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |id| Pointer {
                block: PointerBlock::Symbolic(Variable(id)),
                offset: PointerOffsetTerm::Constant(0),
            };
            let mut heap = crate::kernel::primitives::CHeapMemory::default();
            for id in 1..=size {
                heap.uninitialized_objects.insert(pointer(id), 4);
            }
            let heap = std::sync::Arc::new(heap);
            let original = heap_variable_counts(&heap, WholeCount::Charged);
            let selected = CMemory {
                heap: heap.clone(),
                ..CMemory::new().with_block("selected:read", 4)
            };
            let (projected, work) = crate::instrumentation::measure_deterministic_work(|| {
                counts_whole(&selected, WholeCount::Charged)
            });
            assert_eq!(projected, original);
            assert_eq!(work, 1, "a selected read enumerated {size} heap entries");
            let mut changed = (*heap).clone();
            changed.uninitialized_objects.remove(&pointer(1));
            changed.uninitialized_objects.insert(pointer(10_000), 4);
            let changed = std::sync::Arc::new(changed);
            let (counts, work) = crate::instrumentation::measure_deterministic_work(|| {
                heap_variable_counts(&changed, WholeCount::Charged)
            });
            assert!(!counts.contains_key(&Variable(1)));
            assert!(counts.contains_key(&Variable(10_000)));
            assert_eq!(counts.len(), size as usize);
            assert!(work <= 4, "local heap edit walked {size} objects: {work}");
            assert_eq!(heap_variable_counts(&heap, WholeCount::Charged), original);
            let empty = std::sync::Arc::new(crate::kernel::primitives::CHeapMemory::default());
            assert!(heap_variable_counts(&empty, WholeCount::Charged).is_empty());
            assert_eq!(heap_variable_counts(&changed, WholeCount::Charged), counts);
        }
    }
}
