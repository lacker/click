use super::functions::apply_verified_contract_resource_transition;
pub(super) use super::memory_provenance::*;
use super::prelude::*;

#[cfg(test)]
thread_local! {
    static CHECKED_FUNCTION_BODY_EXECUTIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn record_checked_function_body_execution() {
    CHECKED_FUNCTION_BODY_EXECUTIONS.with(|count| count.set(count.get() + 1));
}

#[cfg(not(test))]
fn record_checked_function_body_execution() {}

#[cfg(test)]
pub(crate) fn take_checked_function_body_execution_count() -> usize {
    CHECKED_FUNCTION_BODY_EXECUTIONS.with(|count| count.replace(0))
}

pub(in crate::kernel) mod contract_certification;
pub use contract_certification::*;
use contract_certification::{
    c_function_contract_certification_assumptions,
    certification_proves_condition_from_verified_pure_implication,
    certification_proves_context_free_forall, certification_proves_proposition,
    contract_resource_condition_cases,
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode,
    resources_certify_loadability,
};

pub fn int32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int32(bits.into())
}

pub fn uint8(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt8(bits.into())
}

/// True when `pointer` addresses within a live heap allocation of `memory`,
/// matching allocation keys either structurally or up to exact
/// materialization of the loads embedded in the key and pointer spellings.
/// Deterministic and assumption-free; never matches across an unresolved
/// havoc.
pub(crate) fn c_memory_holds_live_heap_allocation_at(
    memory: &super::CMemory,
    pointer: &Pointer,
) -> bool {
    memory.is_live_heap_address(pointer)
        || memory.heap_live_allocation_bases().any(|base| {
            base.block == pointer.block
                && super::assumptions::pointer_offsets_equal_after_exact_materialization(
                    &base.offset,
                    &pointer.offset,
                )
        })
}

pub(crate) fn c_pointers_proven_equal_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    super::reasoning::pointers_proven_equal_for_memory_resolution(left, right, assumptions)
}

/// Recognizes two condition-fact spellings as the same fact under the given
/// assumptions, with the exact matching rule the atomic prover applies when
/// it consumes a context fact: memory-resolution load equality and
/// decide-driven term equality. This is a bounded check, not a search.
pub fn c_condition_facts_match_for_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let (
        Proposition::ConditionIs(source_condition, source_value),
        Proposition::ConditionIs(target_condition, target_value),
    ) = (source, target)
    else {
        return false;
    };
    source_value == target_value
        && assumptions.condition_matches(source_condition, target_condition)
}

/// Certifies a stated condition target from one explicit condition source and
/// deterministic memory-resolution evidence. Unlike whole-fact transport,
/// this permits a target to retain an old load on one side while transporting
/// the other side to a newer snapshot.
pub fn prove_c_condition_fact_target_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    if !matches!(source, Proposition::ConditionIs(_, _))
        || !matches!(target, Proposition::ConditionIs(_, _))
    {
        return None;
    }
    let with_source = assumptions.clone().assume_proposition(source.clone());
    certification_proves_proposition(&with_source, target).then(|| {
        Theorem::new(Proposition::Implies(
            Box::new(source.clone()),
            Box::new(target.clone()),
        ))
    })
}

#[derive(Clone, Debug)]
pub struct CLoopPreservationContext {
    state: CState,
    loop_entry_state: CState,
    pure_facts: Vec<Proposition>,
}

impl CLoopPreservationContext {
    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn loop_entry_state(&self) -> &CState {
        &self.loop_entry_state
    }

    pub fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }
}

#[allow(clippy::too_many_arguments)]
pub fn c_loop_preservation_contexts(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &PureFactContext,
) -> Result<Vec<CLoopPreservationContext>, String> {
    let mut budget = ExecutionBudget::default();
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(loop_entry_state, &mut existing_variables);
    collect_c_expression_bitvector_variables(condition, &mut existing_variables);
    for check in invariant_checks {
        collect_spec_proposition_bitvector_variables(check.proposition(), &mut existing_variables);
    }
    for check in effect_checks {
        collect_loop_effect_bitvector_variables(check.effect(), &mut existing_variables);
    }
    collect_c_statement_bitvector_variables(body, &mut existing_variables);
    collect_assumption_variables(assumptions, &mut existing_variables);
    let mut variables = VerificationVariableGenerator::fresh_for(
        budget.next_verification_variable,
        existing_variables,
    );
    let (top_state, whole_loop_effect_summaries) = prepare_loop_top_state(
        loop_entry_state,
        effect_checks,
        body,
        assumptions,
        &mut budget,
        &mut variables,
    )
    .map_err(|error| format!("could not prepare loop effects: {error:?}"))?;
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    let mut contexts = Vec::new();
    for (invariant_facts, invariant_obligations) in assume_invariant_checks(
        &top_state,
        loop_entry_state,
        invariant_checks,
        assumptions,
        &whole_loop_effect_facts,
        &[],
        &mut budget,
    )
    .map_err(|error| format!("could not assume loop invariants: {error:?}"))?
    {
        for (facts, obligations) in assume_condition_truthiness(
            &top_state,
            condition,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            true,
            &mut budget,
        )
        .map_err(|error| format!("could not assume the loop condition: {error:?}"))?
        {
            let context_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
            if let Some(obligation) = obligations
                .iter()
                .find(|obligation| !context_assumptions.proves(obligation.proposition()))
            {
                return Err(format!(
                    "missing loop-head prerequisite{}: {:?}",
                    obligation
                        .context()
                        .map(|context| format!(" ({context})"))
                        .unwrap_or_default(),
                    obligation.proposition()
                ));
            }
            let mut pure_facts = facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            pure_facts.sort();
            pure_facts.dedup();
            contexts.push(CLoopPreservationContext {
                state: top_state.clone(),
                loop_entry_state: top_state.clone(),
                pure_facts,
            });
        }
    }
    Ok(contexts)
}

pub fn c_loop_invariants_hold_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let obligations = c_loop_invariant_obligations_at_back_edge(
        state,
        iteration_entry_state,
        invariant_checks,
        assumptions,
    )?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing invariant fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

pub fn c_loop_invariant_obligations_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        iteration_entry_state,
        invariant_checks,
        InvariantPhase::Preservation,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower back-edge invariants: {error:?}"))
}

pub fn c_loop_invariants_hold_at_back_edge_using(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    verify_invariant_checks_at_back_edge_using(
        state,
        iteration_entry_state,
        invariant_checks,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not replay invariant closer: {error}"))
}

pub fn c_loop_invariant_obligations_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower entry invariants: {error:?}"))
}

pub fn c_loop_effects_hold_at_back_edge(
    iteration_entry_state: &CState,
    state: &CState,
    effect_checks: &[CLoopEffectCheck],
    pure_facts: &[Proposition],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let execution_facts = pure_facts
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    let obligations = collect_loop_effect_check_obligations(
        iteration_entry_state,
        state,
        effect_checks,
        &execution_facts,
        &[],
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower back-edge effects: {error:?}"))?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing loop effect fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

pub fn c_loop_invariants_hold_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let obligations = collect_invariant_check_obligations(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower entry invariants: {error:?}"))?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing invariant fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

/// Builds a branch-independent symbolic state for a proof join.
///
/// Locals that still equal a stable function-entry value retain that identity.
/// Other scalar and pointer locals become fresh symbolic values, and non-stack
/// memory is forgotten. Exported facts and resources constrain those values at
/// the abstract frontier.
pub fn abstract_c_state_for_join(
    state: &CState,
    stable_entry_locals: &BTreeMap<String, CValue>,
) -> Result<CState, String> {
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing_variables);
    for value in stable_entry_locals.values() {
        collect_c_value_bitvector_variables(value, &mut existing_variables);
    }
    let mut variables = VerificationVariableGenerator::fresh_for(1_000_000, existing_variables);
    let mut abstract_state = state.clone();
    let mut abstract_objects = Vec::new();
    let mut preserved_blocks = BTreeSet::new();

    for (name, binding) in state.locals.bindings.iter() {
        let CLocalBinding::Object { value, c_type } = binding else {
            continue;
        };
        let abstract_value = if stable_entry_locals.get(name) == Some(value) {
            value.clone()
        } else {
            match c_type {
                CType::Void => continue,
                CType::Int32 => int32(Bitvector32Term::Variable(variables.next())),
                CType::UInt8 => uint8(Bitvector32Term::Variable(variables.next())),
                CType::Int32Pointer | CType::UInt8Pointer => {
                    CValue::Pointer(Pointer::symbolic(variables.next()))
                }
                CType::Int32Array(_) | CType::UInt8Array(_) => {
                    unreachable!("array objects use CLocalBinding::ArrayObject")
                }
            }
        };
        preserved_blocks.insert(CMemory::local_pointer(name).block);
        abstract_objects.push((name.clone(), abstract_value, *c_type));
    }

    abstract_state.memory = abstract_state
        .memory
        .with_loop_memory_havoc(variables.next(), &preserved_blocks);
    for (name, value, c_type) in abstract_objects {
        sync_stack_local(&mut abstract_state, &name, &value);
        abstract_state.locals.set_typed(name, value, c_type);
    }
    abstract_state.resources = ResourceContext::new();
    Ok(abstract_state)
}

pub fn c_variable(name: impl Into<String>) -> CExpression {
    CExpression::Variable(name.into())
}

pub fn c_addr_of(name: impl Into<String>) -> CExpression {
    CExpression::AddressOf(Box::new(c_variable(name)))
}

pub fn c_pointer_offset_bytes(pointer: CExpression, bytes: u32) -> CExpression {
    if bytes == 0 {
        pointer
    } else {
        CExpression::PointerOffsetBytes {
            pointer: Box::new(pointer),
            bytes,
        }
    }
}

pub fn c_int32_literal(value: u32) -> CExpression {
    CExpression::Value(int32(Bitvector32Term::Constant(value)))
}

pub fn c_uint8_literal(value: u8) -> CExpression {
    CExpression::Value(uint8(Bitvector32Term::Constant(u32::from(value))))
}

pub fn c_pointer_value(pointer: Pointer) -> CExpression {
    CExpression::Value(CValue::Pointer(pointer))
}

pub fn c_less_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessThan(Box::new(left), Box::new(right))
}

pub fn c_less_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessEqual(Box::new(left), Box::new(right))
}

pub fn c_greater_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterThan(Box::new(left), Box::new(right))
}

pub fn c_greater_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterEqual(Box::new(left), Box::new(right))
}

pub fn c_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Equal(Box::new(left), Box::new(right))
}

pub fn c_not_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::NotEqual(Box::new(left), Box::new(right))
}

pub fn c_not(expression: CExpression) -> CExpression {
    CExpression::Not(Box::new(expression))
}

pub fn c_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::And(Box::new(left), Box::new(right))
}

pub fn c_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Or(Box::new(left), Box::new(right))
}

pub fn c_add(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Add(Box::new(left), Box::new(right))
}

pub fn c_subtract(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Subtract(Box::new(left), Box::new(right))
}

pub fn c_multiply(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Multiply(Box::new(left), Box::new(right))
}

pub fn c_divide(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Divide(Box::new(left), Box::new(right))
}

pub fn c_remainder(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Remainder(Box::new(left), Box::new(right))
}

pub fn c_shift_left(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftLeft(Box::new(left), Box::new(right))
}

pub fn c_shift_right(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftRight(Box::new(left), Box::new(right))
}

pub fn c_bitwise_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseAnd(Box::new(left), Box::new(right))
}

pub fn c_bitwise_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseOr(Box::new(left), Box::new(right))
}

pub fn c_bitwise_xor(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseXor(Box::new(left), Box::new(right))
}

pub fn c_bitwise_not(expression: CExpression) -> CExpression {
    CExpression::BitwiseNot(Box::new(expression))
}

pub fn c_load(pointer: CExpression) -> CExpression {
    CExpression::Load(Box::new(pointer))
}

pub fn c_typed_load(pointer: CExpression, value_type: CType) -> CExpression {
    CExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
    }
}

pub fn c_index(base: CExpression, index: CExpression) -> CExpression {
    CExpression::Index(Box::new(base), Box::new(index))
}

pub fn c_assign(name: impl Into<String>, expression: CExpression) -> CStatement {
    CStatement::Assign {
        name: name.into(),
        expression,
    }
}

pub fn c_call_assign(
    target: impl Into<String>,
    function_name: impl Into<String>,
    arguments: Vec<CExpression>,
) -> CStatement {
    CStatement::CallAssign {
        target: target.into(),
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_call(function_name: impl Into<String>, arguments: Vec<CExpression>) -> CStatement {
    CStatement::Call {
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_heap_allocate(target: impl Into<String>, bytes: u32) -> CStatement {
    c_heap_allocate_sized(target, c_int32_literal(bytes))
}

pub fn c_heap_allocate_sized(target: impl Into<String>, bytes: CExpression) -> CStatement {
    CStatement::HeapAllocate {
        target: target.into(),
        bytes,
    }
}

pub fn c_heap_free(pointer: CExpression) -> CStatement {
    CStatement::HeapFree { pointer }
}

pub fn c_declare(name: impl Into<String>, c_type: CType) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
    }
}

pub fn c_assert(condition: CExpression) -> CStatement {
    CStatement::Assert {
        condition,
        label: None,
    }
}

pub fn c_labeled_assert(condition: CExpression, label: impl Into<String>) -> CStatement {
    CStatement::Assert {
        condition,
        label: Some(label.into()),
    }
}

pub fn c_seq(first: CStatement, second: CStatement) -> CStatement {
    CStatement::Seq(Box::new(first), Box::new(second))
}

pub fn c_skip() -> CStatement {
    CStatement::Skip
}

pub fn c_return(expression: CExpression) -> CStatement {
    CStatement::Return(expression)
}

pub fn c_void_value() -> CExpression {
    CExpression::Value(CValue::Void)
}

pub fn c_store(pointer: CExpression, value: CExpression) -> CStatement {
    CStatement::Store { pointer, value }
}

pub fn c_typed_store(pointer: CExpression, value: CExpression, value_type: CType) -> CStatement {
    CStatement::TypedStore {
        pointer,
        value,
        value_type,
    }
}

pub fn c_if(
    condition: CExpression,
    then_branch: CStatement,
    else_branch: CStatement,
) -> CStatement {
    CStatement::If {
        condition,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn c_while(
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(condition, invariant, Vec::new(), Vec::new(), body)
}

pub fn c_while_with_invariant_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(
        condition,
        invariant,
        invariant_checks,
        Vec::new(),
        body,
    )
}

pub fn c_while_with_invariant_and_effect_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    effect_checks: Vec<CLoopEffectCheck>,
    body: CStatement,
) -> CStatement {
    CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body: Box::new(body),
    }
}

pub fn c_parameter(name: impl Into<String>, c_type: CType) -> CParameter {
    CParameter::new(name, c_type)
}

pub fn c_function(
    return_type: CType,
    name: impl Into<String>,
    parameters: Vec<CParameter>,
    body: CStatement,
) -> CFunction {
    CFunction::new(return_type, name, parameters, body)
}

pub fn c_function_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> Option<CState> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    bind_c_function_arguments(caller_state, function, &values)
}

/// Produces the exact callee entry state used by contract verification.
///
/// Composite requirements normally use their canonical contained resources.
/// When proof replay has explicitly observed or unfolded part of a recursive
/// resource, independent certification preserves that equivalent spelling so
/// both executions use the same boundary state.
pub fn c_function_contract_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| "contract entry arguments must be concrete symbolic values".to_string())?;
    let mut budget = ExecutionBudget::default();
    match prepare_function_contract_entry_state_with_values(
        caller_state,
        function,
        &values,
        assumptions,
        &mut budget,
    ) {
        Ok(Ok(state)) => Ok(state),
        Ok(Err(error)) => Err(format!("could not prepare contract resources: {error:?}")),
        Err(limit) => Err(format!(
            "contract resource preparation hit execution limit {limit:?}"
        )),
    }
}

/// Applies a function's already-checked resource effect to a concrete replay
/// outcome. This changes only the contract-level resource/population state;
/// the C value and memory come from the supplied body execution.
pub fn apply_c_function_contract_resource_transition(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CFunctionOutcome,
    assumptions: &PureFactContext,
) -> Result<(CFunctionOutcome, Vec<ProofObligation>), String> {
    match apply_verified_contract_resource_transition(
        caller_state,
        function,
        arguments,
        outcome,
        assumptions,
        &mut ExecutionBudget::default(),
    ) {
        Ok(Ok(result)) => Ok(result),
        Ok(Err(error)) => Err(format!("contract resource transition failed: {error:?}")),
        Err(limit) => Err(format!(
            "contract resource transition hit execution limit {limit:?}"
        )),
    }
}

pub fn c_function_outcome_from_statement_outcome(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> (CFunctionOutcome, Vec<ProofObligation>) {
    function_outcome_from_body(
        caller_state,
        function,
        outcome,
        obligations,
        assumptions,
        None,
    )
}

pub fn c_function_specification(
    state: CState,
    arguments: Vec<CExpression>,
    requires: Vec<Proposition>,
    outcome: CFunctionOutcome,
) -> CFunctionSpecification {
    CFunctionSpecification::new(state, arguments, requires, outcome)
}

pub fn proposition_and(left: Proposition, right: Proposition) -> Proposition {
    Proposition::And(Box::new(left), Box::new(right))
}

pub fn proposition_and_all(mut propositions: Vec<Proposition>) -> Proposition {
    if propositions.is_empty() {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    }
    while propositions.len() > 1 {
        let mut next = Vec::with_capacity(propositions.len().div_ceil(2));
        let mut pairs = propositions.into_iter();
        while let Some(left) = pairs.next() {
            next.push(match pairs.next() {
                Some(right) => proposition_and(left, right),
                None => left,
            });
        }
        propositions = next;
    }
    propositions.pop().expect("nonempty conjunction level")
}

/// Expands C expression definedness into the exact pure proposition under
/// which evaluation reaches a value rather than undefined behavior.
pub fn c_expression_definedness_proposition(
    state: &CState,
    expression: &CExpression,
) -> Result<Proposition, ExecutionLimit> {
    let paths = evaluate_c_expression_paths(
        state,
        expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )?;
    let mut normal_paths = paths.into_iter().filter_map(|path| {
        if !matches!(path.outcome, CExpressionOutcome::Value(_)) {
            return None;
        }
        Some(proposition_and_all(
            path.facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .chain(
                    path.obligations
                        .into_iter()
                        .map(|obligation| obligation.proposition().clone()),
                )
                .collect(),
        ))
    });
    let Some(first) = normal_paths.next() else {
        return Ok(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ));
    };
    Ok(normal_paths.fold(first, |left, right| {
        Proposition::Or(Box::new(left), Box::new(right))
    }))
}

pub fn substitute_int32_variable_in_proposition(
    proposition: &Proposition,
    variable: Variable,
    value: Bitvector32Term,
) -> Proposition {
    substitute_bitvector_variable_in_proposition(proposition, variable, &value)
}

/// Planning evidence for certificate lowering: the guided instantiation
/// values the atomic prover would try for one universally quantified int32
/// fact against a target condition fact, plus every value of a
/// constant-bounded binder range. Simple replay never calls this; the
/// selected value is recorded explicitly in the emitted certificate.
pub fn forall_instantiation_candidate_values(
    quantified: &Proposition,
    target: &Proposition,
) -> Vec<Bitvector32Term> {
    let Proposition::ForAll { var, body, .. } = quantified else {
        return Vec::new();
    };
    let mut candidates = match target {
        Proposition::ConditionIs(condition, _) => {
            PureFactContext::guided_forall_condition_candidates(*var, body, condition)
        }
        _ => BTreeSet::new(),
    };
    let variables = vec![*var];
    if let Some(ranges) = crate::kernel::reasoning::finite_forall_ranges(&variables, body)
        && let [range] = ranges.as_slice()
        && usize::try_from(range.upper - range.lower + 1)
            .is_ok_and(|width| width <= crate::kernel::reasoning::FINITE_FORALL_INSTANTIATION_LIMIT)
    {
        for value in range.lower..=range.upper {
            candidates.insert(signed_i64_bitvector_constant(value));
        }
    }
    candidates.into_iter().collect()
}

/// Chooses a variable identity absent from both the free variables and logical
/// binders of the supplied propositions.
pub fn fresh_int32_variable_for_propositions(propositions: &[Proposition]) -> Variable {
    let mut reserved = BTreeSet::new();
    for proposition in propositions {
        collect_proposition_bitvector_variables(proposition, &mut reserved);
        collect_proposition_bound_variables(proposition, &mut reserved);
    }
    VerificationVariableGenerator::fresh_for(0, reserved).next()
}

pub fn c_max_body() -> CStatement {
    c_if(
        c_less_than(c_variable("a"), c_variable("b")),
        c_return(c_variable("b")),
        c_return(c_variable("a")),
    )
}

pub fn c_max_function() -> CFunction {
    c_function(
        CType::Int32,
        "max",
        vec![
            c_parameter("a", CType::Int32),
            c_parameter("b", CType::Int32),
        ],
        c_max_body(),
    )
}

pub fn c_max_environment(a: CValue, b: CValue) -> CLocalEnvironment {
    CLocalEnvironment::new().with("a", a).with("b", b)
}

pub fn c_max_state(a: CValue, b: CValue) -> CState {
    CState::new().with_local("a", a).with_local("b", b)
}

pub fn c_max_lt_condition(a: Bitvector32Term, b: Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_than(a, b)
}

pub fn prove_c_expression_evaluation(state: CState, expression: CExpression) -> Option<Theorem> {
    let outcome = evaluate_c_expression(
        &state,
        &expression,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )?;
    Some(Theorem::new(Proposition::CExpressionEvaluates {
        state,
        expression,
        outcome,
    }))
}

pub fn prove_symbolic_c_condition_evaluation(
    state: CState,
    condition: CExpression,
    assumptions: PureFactContext,
) -> SymbolicCConditionEvaluation {
    let mut budget = ExecutionBudget::default();
    let expression_paths =
        match evaluate_c_expression_paths(&state, &condition, &assumptions, &mut budget) {
            Ok(paths) => paths,
            Err(limit) => {
                return SymbolicCConditionEvaluation {
                    paths: Vec::new(),
                    limit: Some(limit),
                };
            }
        };
    let mut outcomes = Vec::new();
    for path in expression_paths {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                outcomes.extend(
                    c_truthiness_paths(value, path.facts, path.obligations, &assumptions)
                        .into_iter()
                        .map(|path| {
                            (
                                CConditionOutcome::Value(path.is_true),
                                path.facts,
                                path.obligations,
                            )
                        }),
                );
            }
            CExpressionOutcome::UndefinedBehavior(kind) => outcomes.push((
                CConditionOutcome::UndefinedBehavior(kind),
                path.facts,
                path.obligations,
            )),
            CExpressionOutcome::RuntimeError(error) => outcomes.push((
                CConditionOutcome::RuntimeError(error),
                path.facts,
                path.obligations,
            )),
        }
    }
    let paths = outcomes
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            let facts = public_execution_pure_facts(&facts);
            let proposition = Proposition::CConditionEvaluates {
                state: state.clone(),
                condition: condition.clone(),
                outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &obligations,
            ));
            SymbolicCConditionEvaluationPath {
                facts,
                obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCConditionEvaluation { paths, limit: None }
}

pub fn prove_c_statement_execution(state: CState, statement: CStatement) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, PureFactContext::new())
}

pub fn prove_c_statement_execution_under_assumptions(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, assumptions)
}

pub fn prove_symbolic_c_execution(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_execution_paths(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
) -> SymbolicCExecution {
    let paths = match execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = if execution_semantics == CExecutionSemantics::EXECUTE_BODIES {
                Proposition::CStatementExecutes {
                    state: state.clone(),
                    statement: statement.clone(),
                    outcome: path.outcome,
                }
            } else {
                Proposition::CStatementVerifies {
                    state: state.clone(),
                    statement: statement.clone(),
                    outcome: path.outcome,
                }
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
    )
    .0
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget = ExecutionBudget::default();
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        &mut budget,
    )
}

fn statement_verification_variables(
    lower_bound: u64,
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
) -> VerificationVariableGenerator {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing);
    collect_c_statement_bitvector_variables(statement, &mut existing);
    collect_assumption_variables(assumptions, &mut existing);
    collect_execution_environment_variables(environment, &mut existing);
    VerificationVariableGenerator::fresh_for(lower_bound, existing)
}

pub(crate) fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut variables = statement_verification_variables(
        budget.next_verification_variable,
        &state,
        &statement,
        &assumptions,
        &environment,
    );
    let execution = execute_c_statement_verification_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        budget,
        &mut variables,
    );
    budget.next_verification_variable = budget.next_verification_variable.max(variables.next);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_c_statement_execution_with_loop_rule(state, statement, assumptions, paths)
}

#[cfg(test)]
pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget = ExecutionBudget::default();
    prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
        state,
        statement,
        assumptions,
        environment,
        initialization_proven,
        preservation_proven,
        &mut budget,
    )
}

pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
    } = &statement
    else {
        return (
            SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
            None,
        );
    };
    let mut variables = statement_verification_variables(
        budget.next_verification_variable,
        &state,
        &statement,
        &assumptions,
        &environment,
    );
    let execution = execute_c_while_exit_paths_with_proven_phases(
        &state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
        &assumptions,
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        initialization_proven,
        preservation_proven,
        budget,
        &mut variables,
    );
    budget.next_verification_variable = budget.next_verification_variable.max(variables.next);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_c_statement_execution_with_loop_rule(state, statement, assumptions, paths)
}

fn symbolic_c_statement_execution_with_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    paths: Vec<CStatementExecutionPath>,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let loop_rule = (matches!(statement, CStatement::While { .. })
        && paths.iter().all(|path| {
            matches!(
                path.outcome,
                CStatementOutcome::Normal(_) | CStatementOutcome::VerificationDiverges
            ) && path.obligations.iter().all(ProofObligation::is_assumable)
        }))
    .then(|| CVerifiedLoopRule {
        symbolic_entry_state: state.clone(),
        loop_statement: statement.clone(),
        required_assumptions: assumptions.clone(),
        paths: paths.clone(),
        composite_resource_definitions: Vec::new(),
    });
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CStatementVerifies {
                state: state.clone(),
                statement: statement.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    (SymbolicCExecution { paths, limit: None }, loop_rule)
}

pub fn prove_symbolic_c_function_execution(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_function_execution_paths(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicCExecution {
    let paths = match execute_c_function_paths_with_contract_resources(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
        prepare_contract_resources,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = if execution_semantics == CExecutionSemantics::EXECUTE_BODIES {
                Proposition::CFunctionExecutes {
                    state: state.clone(),
                    function: function.clone(),
                    arguments: arguments.clone(),
                    outcome: path.outcome,
                }
            } else {
                Proposition::CFunctionVerifies {
                    state: state.clone(),
                    function: function.clone(),
                    arguments: arguments.clone(),
                    outcome: path.outcome,
                }
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_function_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_verification_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

/// Verifies an exact function body from its declared contract-entry resources.
///
/// Unlike ordinary proof replay, this canonicalizes composite requirements
/// before body execution. It is the independent execution used to certify
/// opaque contract claims.
pub fn prove_symbolic_c_function_contract_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
        true,
    )
}

/// Executes one whole-function judgment and seals its exact authority inputs
/// together with the resulting frontier for later contract certification.
#[allow(clippy::too_many_arguments)]
pub fn prove_checked_c_function_execution_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
) -> CCheckedFunctionExecution {
    record_checked_function_body_execution();
    let execution = match mode {
        CFunctionContractExecutionMode::VerifyLoops => {
            prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions.clone(),
                environment.clone(),
                execution_semantics,
                ExecutionBudget::default(),
                true,
            )
        }
        CFunctionContractExecutionMode::ExecuteLoops => {
            prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assumptions.clone(),
                environment.clone(),
                execution_semantics,
                ExecutionBudget::default(),
                true,
            )
        }
    };
    CCheckedFunctionExecution {
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        mode,
        execution,
        entry_derivations: Vec::new(),
        entry_prerequisites: Vec::new(),
    }
}

/// Attaches kernel-issued entry-fact derivations to a checked execution.
///
/// The checked execution remains sealed: only derivations concluding in one
/// of its exact assumptions are retained, and callers cannot manufacture a
/// [`Theorem`]. Contract certification independently discharges every
/// implication premise before using the artifact.
pub fn checked_c_function_execution_with_entry_derivations(
    mut checked: CCheckedFunctionExecution,
    derivations: Vec<Theorem>,
    prerequisites: Vec<Proposition>,
) -> CCheckedFunctionExecution {
    checked.entry_derivations = derivations
        .into_iter()
        .filter(|derivation| {
            let mut body = derivation.proposition();
            while let Proposition::Implies(_, next) = body {
                body = next;
            }
            checked.assumptions.proves_exact(body)
        })
        .collect();
    checked.entry_prerequisites = prerequisites
        .into_iter()
        .filter(|prerequisite| {
            checked.assumptions.proves_exact(prerequisite)
                && checked.entry_derivations.iter().any(|derivation| {
                    let mut conclusion = derivation.proposition();
                    while let Proposition::Implies(_, body) = conclusion {
                        conclusion = body;
                    }
                    conclusion == prerequisite
                })
        })
        .collect();
    checked
}

/// Re-expresses a checked execution from a definitionally equal ghost-resource
/// representation of the same concrete entry state.
///
/// Resource folds, unfolds, and observations can leave proof replay with a
/// different `ResourceContext` than independently reconstructed contract
/// entry. The program locals, memory, and counted populations must still be
/// exactly identical, and the kernel's bounded resource equality relation
/// must prove the two ghost representations equivalent before any execution
/// theorem is rebuilt at the contract entry state.
fn checked_execution_at_definitionally_equal_entry_state(
    checked: &CCheckedFunctionExecution,
    state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> Option<SymbolicCExecution> {
    // Recursive composites can expose an unbounded proof relation between
    // folded and projected entry contexts. Certification must not turn a
    // cache probe into that search: until recursive resource states have a
    // stable shallow identity, use the ordinary fresh execution path.
    if function
        .composite_resource_definitions()
        .iter()
        .any(CCompositeResourceDefinition::is_recursive)
    {
        return None;
    }
    let mut checked_without_ghost_difference = checked.state.clone();
    checked_without_ghost_difference.resources = state.resources.clone();
    checked_without_ghost_difference.counted_populations = state.counted_populations.clone();
    let concrete_matches = checked_without_ghost_difference == *state;
    let resources_match = crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            checked.state.memory(),
            checked.state.resources(),
            state.memory(),
            state.resources(),
            assumptions,
        );
    let populations_match = counted_populations_definitionally_equal(
        &checked.state,
        state,
        function.composite_resource_definitions(),
        assumptions,
    );
    if !concrete_matches || !resources_match || !populations_match {
        return None;
    }

    let mut paths = Vec::with_capacity(checked.execution.paths.len());
    for path in &checked.execution.paths {
        let mut conclusion = path.theorem.proposition();
        while let Proposition::Implies(_, body) = conclusion {
            conclusion = body;
        }
        let proposition = match conclusion {
            Proposition::CFunctionExecutes {
                state: proved_state,
                function: proved_function,
                arguments,
                outcome,
            } if proved_state == &checked.state
                && proved_function == function
                && arguments == &checked.arguments =>
            {
                Proposition::CFunctionExecutes {
                    state: state.clone(),
                    function: function.clone(),
                    arguments: arguments.clone(),
                    outcome: outcome.clone(),
                }
            }
            Proposition::CFunctionVerifies {
                state: proved_state,
                function: proved_function,
                arguments,
                outcome,
            } if proved_state == &checked.state
                && proved_function == function
                && arguments == &checked.arguments =>
            {
                Proposition::CFunctionVerifies {
                    state: state.clone(),
                    function: function.clone(),
                    arguments: arguments.clone(),
                    outcome: outcome.clone(),
                }
            }
            _ => return None,
        };
        paths.push(SymbolicCExecutionPath {
            assumptions: path.assumptions.clone(),
            facts: path.facts.clone(),
            effect_facts: path.effect_facts.clone(),
            obligations: path.obligations.clone(),
            theorem: Theorem::new(wrap_proof_facts(
                proposition,
                &path.assumptions,
                &path.facts,
                &path.obligations,
            )),
        });
    }
    Some(SymbolicCExecution { paths, limit: None })
}

fn counted_populations_definitionally_equal(
    left: &CState,
    right: &CState,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> bool {
    let is_observable = |population: &CCountedPopulation| {
        population.family_observation_marker
            || definitions.iter().any(|definition| {
                definition.name() == population.name && definition.is_counted_population()
            })
    };
    let left_populations = left
        .counted_populations
        .iter()
        .filter(|population| is_observable(population))
        .collect::<Vec<_>>();
    let right_populations = right
        .counted_populations
        .iter()
        .filter(|population| is_observable(population))
        .collect::<Vec<_>>();
    if left_populations.len() != right_populations.len() {
        return false;
    }
    let right_by_identity = right_populations
        .into_iter()
        .map(|population| {
            (
                (
                    population.name.as_str(),
                    population.arguments.as_slice(),
                    population.family_observation_marker,
                ),
                &population.count,
            )
        })
        .collect::<BTreeMap<_, _>>();
    left_populations.into_iter().all(|population| {
        let identity = (
            population.name.as_str(),
            population.arguments.as_slice(),
            population.family_observation_marker,
        );
        right_by_identity.get(&identity).is_some_and(|right_count| {
            let exact = population.count == **right_count;
            let proved = assumptions.proves(&Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(population.count.clone()),
                    Box::new((*right_count).clone()),
                ),
                true,
            ));
            exact || proved
        })
    })
}

/// Produces the only execution frontier accepted for opaque contract
/// certification.
///
/// The initial assumptions are derived inside the kernel solely from the
/// function's exact contract and resource entry state. Callers cannot inject
/// additional hypotheses.
pub fn prove_c_function_contract_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    derived_entry_facts: Vec<Proposition>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
) -> CFunctionContractExecution {
    prove_c_function_contract_execution_paths_with_checked_artifacts(
        state,
        function,
        arguments,
        derived_entry_facts,
        environment,
        execution_semantics,
        mode,
        &[],
    )
}

/// Certifies an opaque contract while reusing a kernel-checked whole-function
/// frontier when its sealed authority is implied by the exact contract entry.
#[allow(clippy::too_many_arguments)]
pub fn prove_c_function_contract_execution_paths_with_checked_artifacts(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    derived_entry_facts: Vec<Proposition>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
    checked_artifacts: &[CCheckedFunctionExecution],
) -> CFunctionContractExecution {
    prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems(
        state,
        function,
        arguments,
        derived_entry_facts,
        environment,
        execution_semantics,
        mode,
        checked_artifacts,
        &[],
    )
}

/// Certifies an opaque contract with kernel-issued pure theorem authorities.
#[allow(clippy::too_many_arguments)]
pub fn prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    derived_entry_facts: Vec<Proposition>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
    checked_artifacts: &[CCheckedFunctionExecution],
    pure_theorems: &[CVerifiedPureTheorem],
) -> CFunctionContractExecution {
    let pure_theorem_facts = pure_theorems
        .iter()
        .map(|verified| verified.theorem.proposition().clone())
        .collect::<Vec<_>>();
    let selection_assumptions =
        assumptions_with_propositions(&PureFactContext::new(), &derived_entry_facts);
    let Some(base_assumptions) = crate::instrumentation::measure_operation(
        function.name(),
        "contract certification",
        "contract assumptions",
        || {
            c_function_contract_certification_assumptions(
                &state,
                &function,
                &arguments,
                PureFactContext::new(),
                &selection_assumptions,
            )
        },
    ) else {
        if crate::instrumentation::enabled() {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                format!(
                    "exact certification could not construct contract assumptions for {}",
                    function.name()
                ),
            ));
        }
        return CFunctionContractExecution {
            execution: SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
        };
    };
    let Some(resource_condition_cases) = crate::instrumentation::measure_operation(
        function.name(),
        "contract certification",
        "contract resource guard cases",
        || contract_resource_condition_cases(&state, &function, &arguments, &base_assumptions),
    ) else {
        if crate::instrumentation::enabled() {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                format!(
                    "exact certification could not enumerate resource guards for {}",
                    function.name()
                ),
            ));
        }
        return CFunctionContractExecution {
            execution: SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
        };
    };
    let mut combined_paths = Vec::new();
    for case_facts in resource_condition_cases {
        let case_seed = assumptions_with_propositions(&PureFactContext::new(), &case_facts);
        let Some(mut assumptions) = crate::instrumentation::measure_operation(
            function.name(),
            "contract certification",
            "contract case assumptions",
            || {
                c_function_contract_certification_assumptions(
                    &state,
                    &function,
                    &arguments,
                    case_seed,
                    &selection_assumptions,
                )
            },
        ) else {
            if crate::instrumentation::enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::Diagnostic(format!(
                        "exact certification rejected a resource-guard case for {}",
                        function.name()
                    )),
                );
            }
            return CFunctionContractExecution {
                execution: SymbolicCExecution {
                    paths: Vec::new(),
                    limit: None,
                },
            };
        };
        let Some(mut entry_state) = c_function_entry_state(&state, &function, &arguments) else {
            return CFunctionContractExecution {
                execution: SymbolicCExecution {
                    paths: Vec::new(),
                    limit: None,
                },
            };
        };
        let has_recursive_resources = function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
        if !has_recursive_resources {
            let Some(entry_resources) = crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract entry resource expansion",
                || {
                    expand_all_composite_resource_facts(
                        entry_state.resources(),
                        function.composite_resource_definitions(),
                        entry_state.memory(),
                        &assumptions,
                    )
                },
            ) else {
                return CFunctionContractExecution {
                    execution: SymbolicCExecution {
                        paths: Vec::new(),
                        limit: None,
                    },
                };
            };
            entry_state.resources = entry_resources.clone();
            assumptions = crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract derived entry facts",
                || {
                    let mut derived_assumptions = assumptions;
                    for fact in &derived_entry_facts {
                        // Derived entry facts are predominantly loadability
                        // witnesses. Check the exact entry resources first:
                        // that is the narrow authority for those facts and
                        // avoids asking the general proposition prover to
                        // scan the growing contract context before the direct
                        // resource check succeeds.
                        let resource_certified = crate::instrumentation::measure_operation(
                            function.name(),
                            "contract certification",
                            "derived fact resource check",
                            || {
                                resources_certify_loadability(
                                    &entry_state,
                                    &entry_resources,
                                    fact,
                                    &derived_assumptions,
                                )
                            },
                        );
                        let proposition_operation = match fact {
                            Proposition::CMemoryLoadable { .. } => "derived proposition: loadable",
                            Proposition::ConditionIs(_, _) => "derived proposition: condition",
                            Proposition::CResourceSeparate { .. } => {
                                "derived proposition: resource separate"
                            }
                            Proposition::CResourceContains { .. } => {
                                "derived proposition: resource contains"
                            }
                            Proposition::ForAll { .. } => "derived proposition: forall",
                            _ => "derived proposition: other",
                        };
                        let context_free_certified = !resource_certified
                            && matches!(fact, Proposition::ForAll { .. })
                            && crate::instrumentation::measure_operation(
                                function.name(),
                                "contract certification",
                                "derived forall context-free check",
                                || certification_proves_context_free_forall(fact),
                            );
                        let proposition_certified = !resource_certified
                            && !context_free_certified
                            && crate::instrumentation::measure_operation(
                                function.name(),
                                "contract certification",
                                proposition_operation,
                                || certification_proves_proposition(&derived_assumptions, fact),
                            );
                        if !resource_certified {
                            crate::instrumentation::measure_operation(
                                function.name(),
                                "contract certification",
                                if proposition_certified {
                                    "derived proposition result: proved"
                                } else {
                                    "derived proposition result: unproved"
                                },
                                || (),
                            );
                        }
                        if resource_certified || context_free_certified || proposition_certified {
                            derived_assumptions = crate::instrumentation::measure_operation(
                                function.name(),
                                "contract certification",
                                "derived fact insertion",
                                || derived_assumptions.assume_proposition(fact.clone()),
                            );
                        }
                    }
                    derived_assumptions
                },
            );
        } else {
            // The caller state already contains the proof-directed
            // recursive projections certified above. Preserve that
            // targeted boundary; globally expanding it would erase child
            // composites and expose unrelated recursive branches.
            let mut entry_resources = entry_state.resources().clone();
            for fact in &derived_entry_facts {
                if assumptions.proves_exact(fact) {
                    assumptions = assumptions.assume_proposition(fact.clone());
                    continue;
                }
                if let Proposition::CMemoryLoadable { base, bytes, .. } = &fact
                    && let Some(bytes) = bytes.as_const()
                {
                    let projected = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(1),
                    ));
                    if let Some(exposed) = expose_composite_resource_fact(
                        &entry_resources,
                        &projected,
                        function.composite_resource_definitions(),
                        entry_state.memory(),
                        &assumptions,
                    ) {
                        entry_resources = exposed.unchecked_with_fact(projected);
                        assumptions = assumptions.assume_proposition(fact.clone());
                        continue;
                    }
                    if resource_context_has_structural_read(
                        &entry_resources,
                        base,
                        bytes,
                        &assumptions,
                    ) {
                        entry_resources = entry_resources.unchecked_with_fact(projected);
                        assumptions = assumptions.assume_proposition(fact.clone());
                        continue;
                    }
                }
                if resources_certify_loadability(&entry_state, &entry_resources, fact, &assumptions)
                {
                    if let Proposition::CMemoryLoadable { base, .. } = &fact {
                        entry_resources = entry_resources.unchecked_with_fact(
                            CResourceFact::view_memory(CMemoryRange::new(
                                base.clone(),
                                Bitvector32Term::Constant(0),
                                Bitvector32Term::Constant(1),
                            )),
                        );
                    }
                    assumptions = assumptions.assume_proposition(fact.clone());
                    continue;
                }
                let proves_fact = match &fact {
                    Proposition::ConditionIs(condition, value) => {
                        assumptions.proves_condition_exact_or_snapshot(condition, *value)
                            || assumptions.decide(condition) == Some(*value)
                    }
                    Proposition::Not(body) => match body.as_ref() {
                        Proposition::ConditionIs(condition, value) => {
                            assumptions.proves_condition_exact_or_snapshot(condition, !*value)
                                || assumptions.decide(condition) == Some(!*value)
                        }
                        _ => assumptions.proves_exact(fact),
                    },
                    _ => assumptions.proves_exact(fact),
                };
                if proves_fact {
                    assumptions = assumptions.assume_proposition(fact.clone());
                }
            }
            entry_state.resources = entry_resources;
        }
        // Explicit entry theorem applications can justify a selected
        // evaluator prerequisite even when ghost-resource opening prevents
        // reusing the checked execution's exact entry state. Admit only an
        // exact selected fact, from an opaque kernel theorem attached to an
        // otherwise matching checked execution, after every implication
        // premise follows from the reconstructed contract context.
        for checked in checked_artifacts {
            if checked.function != function
                || checked.arguments != arguments
                || checked.environment != environment
                || checked.execution_semantics != execution_semantics
                || checked.mode != mode
            {
                continue;
            }
            // Replay attached kernel derivations in certificate order. A
            // later explicit theorem application may use a fact established
            // by an earlier one, but only selected evaluator prerequisites
            // escape into the reconstructed execution context.
            let mut derivation_assumptions = assumptions.clone();
            for derivation in &checked.entry_derivations {
                let mut body = derivation.proposition();
                let mut premises_hold = true;
                while let Proposition::Implies(premise, next) = body {
                    if !certification_proves_proposition(&derivation_assumptions, premise) {
                        premises_hold = false;
                        break;
                    }
                    body = next;
                }
                if premises_hold {
                    derivation_assumptions =
                        derivation_assumptions.assume_proposition(body.clone());
                    if checked.entry_prerequisites.contains(body) {
                        assumptions = assumptions.assume_proposition(body.clone());
                    }
                }
            }
        }
        let matches_execution_metadata_except_state = |checked: &CCheckedFunctionExecution| {
            checked.function == function
                && checked.arguments == arguments
                && checked.environment == environment
                && checked.execution_semantics == execution_semantics
                && checked.mode == mode
                && checked.assumptions.has_same_reasoning_policy(&assumptions)
                && checked.execution.limit().is_none()
                && !checked.execution.paths().is_empty()
        };
        let derivation_dischargeable = |derivation: &Theorem, conclusion: &Proposition| {
            let mut body = derivation.proposition();
            while let Proposition::Implies(premise, next) = body {
                if !certification_proves_proposition(&assumptions, premise) {
                    return false;
                }
                body = next;
            }
            body == conclusion
        };
        let checked_premise_is_authorized =
            |checked: &CCheckedFunctionExecution, premise: &Proposition| {
                assumptions.proves(premise)
                    || checked
                        .entry_derivations
                        .iter()
                        .any(|derivation| derivation_dischargeable(derivation, premise))
            };
        let reusable = checked_artifacts.iter().find(|checked| {
            checked.state == state
                && matches_execution_metadata_except_state(checked)
                && checked
                    .assumptions
                    .pure_facts()
                    .into_iter()
                    .all(|premise| checked_premise_is_authorized(checked, &premise))
        });
        let entry_resource_rebase_supported = !function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
        let rebased_reuse = (reusable.is_none() && entry_resource_rebase_supported)
            .then(|| {
                checked_artifacts
                    .iter()
                    .filter(|checked| matches_execution_metadata_except_state(checked))
                    .find(|checked| {
                        checked
                            .assumptions
                            .pure_facts()
                            .into_iter()
                            .all(|premise| checked_premise_is_authorized(checked, &premise))
                    })
                    .and_then(|checked| {
                        crate::instrumentation::measure_operation(
                            function.name(),
                            "contract certification",
                            "contract checked entry resource equivalence",
                            || {
                                checked_execution_at_definitionally_equal_entry_state(
                                    checked,
                                    &state,
                                    &function,
                                    &assumptions,
                                )
                            },
                        )
                    })
            })
            .flatten();
        // A surface proof can split at function entry and independently check
        // the complete function under `condition` and `not condition`. Neither
        // artifact alone is valid under the unsplit contract assumptions, but
        // together their frontiers are exhaustive. Keep this composition in
        // the kernel: callers cannot manufacture artifacts, the exact
        // execution metadata must match, every non-branch premise must follow
        // from the reconstructed contract context, and both polarities of one
        // exact condition must be present.
        let partition_reuse =
            (reusable.is_none() && rebased_reuse.is_none() && entry_resource_rebase_supported)
                .then(|| {
                    let candidates = checked_artifacts
                        .iter()
                        .filter(|checked| matches_execution_metadata_except_state(checked))
                        .filter_map(|checked| {
                            let mut unproved = checked
                                .assumptions
                                .pure_facts()
                                .into_iter()
                                .filter(|premise| !checked_premise_is_authorized(checked, premise));
                            let premise = unproved.next()?;
                            if unproved.next().is_some() {
                                return None;
                            }
                            let Proposition::ConditionIs(condition, value) = premise else {
                                return None;
                            };
                            Some((checked, condition, value))
                        })
                        .collect::<Vec<_>>();
                    for (left_index, (left, left_condition, left_value)) in
                        candidates.iter().enumerate()
                    {
                        if let Some((right, _, _)) = candidates[left_index + 1..].iter().find(
                            |(_, right_condition, right_value)| {
                                right_condition == left_condition && right_value != left_value
                            },
                        ) {
                            let left = checked_execution_at_definitionally_equal_entry_state(
                                left,
                                &state,
                                &function,
                                &assumptions,
                            )?;
                            let right = checked_execution_at_definitionally_equal_entry_state(
                                right,
                                &state,
                                &function,
                                &assumptions,
                            )?;
                            let mut paths = left.paths;
                            paths.extend(right.paths);
                            return Some(SymbolicCExecution { paths, limit: None });
                        }
                    }
                    None
                })
                .flatten();
        let body_operation = if reusable.is_some() {
            "contract checked body reuse"
        } else if rebased_reuse.is_some() {
            "contract checked body resource-rebased reuse"
        } else if partition_reuse.is_some() {
            "contract checked body partition reuse"
        } else {
            "contract body symbolic execution"
        };
        let mut execution = crate::instrumentation::measure_operation(
            function.name(),
            "contract certification",
            body_operation,
            || match (reusable, rebased_reuse, partition_reuse) {
                (Some(checked), _, _) => checked.execution.clone(),
                (None, Some(execution), _) => execution,
                (None, None, Some(execution)) => execution,
                (None, None, None) => {
                    record_checked_function_body_execution();
                    match mode {
                        CFunctionContractExecutionMode::VerifyLoops => {
                            prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
                                state.clone(),
                                function.clone(),
                                arguments.clone(),
                                assumptions,
                                environment.clone(),
                                execution_semantics,
                                ExecutionBudget::default(),
                                true,
                            )
                        }
                        CFunctionContractExecutionMode::ExecuteLoops => {
                            prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
                                state.clone(),
                                function.clone(),
                                arguments.clone(),
                                assumptions,
                                environment.clone(),
                                execution_semantics,
                                ExecutionBudget::default(),
                                true,
                            )
                        }
                    }
                }
            },
        );
        for path in &mut execution.paths {
            let mut certification_assumptions = path.assumptions.clone();
            for obligation in &path.obligations {
                let Proposition::ConditionIs(condition, value) = obligation.proposition() else {
                    continue;
                };
                if certification_proves_proposition(
                    &certification_assumptions,
                    obligation.proposition(),
                ) || pure_theorem_facts.iter().any(|fact| {
                    certification_proves_condition_from_verified_pure_implication(
                        &certification_assumptions,
                        fact,
                        condition,
                        *value,
                    )
                }) {
                    certification_assumptions = certification_assumptions
                        .assume_proposition(obligation.proposition().clone());
                }
            }
            path.assumptions = certification_assumptions;
        }
        if crate::instrumentation::enabled()
            && execution.paths.is_empty()
            && execution.limit.is_none()
        {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                format!(
                    "exact certification executed a resource-guard case for {} but produced no consistent path",
                    function.name()
                ),
            ));
        }
        if let Some(limit) = execution.limit {
            return CFunctionContractExecution {
                execution: SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
            };
        }
        combined_paths.extend(execution.paths);
    }
    CFunctionContractExecution {
        execution: SymbolicCExecution {
            paths: combined_paths,
            limit: None,
        },
    }
}

pub fn prove_c_function_satisfies_specification(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification_with_environment(
        function,
        specification,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
}

pub fn prove_c_function_satisfies_specification_with_environment(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    let paths = execute_c_function_paths(
        specification.state(),
        &function,
        specification.arguments(),
        &specification_assumptions,
        &environment,
        execution_semantics,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some()
        || path.facts.iter().any(ExecutionPureFact::is_public)
        || !path.obligations.is_empty()
        || &path.outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let proposition = requires.iter().rev().fold(
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        },
        |body, requirement| Proposition::Implies(Box::new(requirement.clone()), Box::new(body)),
    );
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_function_satisfies_specification_and_propositions(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: PureFactContext,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        assumptions.clone(),
    )?;

    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    if propositions
        .iter()
        .any(|proposition| !specification_assumptions.proves(proposition))
    {
        return None;
    }

    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CFunctionSatisfiesSpecification {
            function: function.clone(),
            specification: specification.clone(),
        })
        .chain(propositions)
        .collect(),
    );
    let proposition = specification
        .requires()
        .iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
        });
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_statement_executes_and_propositions(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.facts.is_empty() || !path.obligations.is_empty() {
        return None;
    }
    if propositions
        .iter()
        .any(|proposition| !assumptions.proves(proposition))
    {
        return None;
    }
    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CStatementExecutes {
            state,
            statement,
            outcome: path.outcome,
        })
        .chain(propositions)
        .collect(),
    );
    Some(Theorem::new(wrap_proof_facts(
        conclusion,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_max_lt_returns_right(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(a_value, b_value.clone());
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), true);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: b_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, true)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_c_max_not_lt_returns_left(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits, b_bits);
    let state = c_max_state(a_value.clone(), b_value);
    let assumptions = PureFactContext::new().assume_condition(condition.clone(), false);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: a_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, false)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

/// Signed int32 increment preserves a strict upper bound as a non-strict
/// bound. The strict premise also rules out signed overflow: if `value` were
/// `INT_MAX`, no int32 `upper` could be greater than it.
pub fn prove_int32_increment_upper_bound(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), upper.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            upper,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// A signed int32 increment is strictly greater than its input when a strict
/// upper bound rules out overflow.
pub fn prove_int32_increment_strictly_increases(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            value.clone(),
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed int32 increment preserves a non-strict lower bound when a strict
/// upper bound rules out signed overflow.
pub fn prove_int32_increment_lower_bound(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), value.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            lower,
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(lower_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Increment preserves a signed lower bound, in greater-equal surface order.
pub fn prove_int32_increment_greater_equal_lower_bound(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            lower,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(lower_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Increment makes a nonnegative signed gap strictly positive.
pub fn prove_int32_increment_strict_greater_lower_bound(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let lower_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), lower.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
            lower,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(lower_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed int32 increment preserves non-strict order when a strict upper
/// bound rules out overflow. Since `lower <= value < upper`, neither increment
/// can wrap past `INT_MAX`.
pub fn prove_int32_increment_preserves_order(
    value: Bitvector32Term,
    lower: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let order_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), value.clone()),
        true,
    );
    let upper_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(value.clone(), upper), true);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::add(lower, Bitvector32Term::Constant(1)),
            Bitvector32Term::add(value, Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(order_premise),
        Box::new(Proposition::Implies(
            Box::new(upper_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A value at least one greater than `lower` is strictly greater than
/// `lower`. The first premise explicitly proves that forming the successor did
/// not wrap in signed int32 arithmetic.
pub fn prove_int32_successor_le_implies_lt(
    lower: Bitvector32Term,
    value: Bitvector32Term,
) -> Theorem {
    let successor = Bitvector32Term::add(lower.clone(), Bitvector32Term::Constant(1));
    let no_overflow_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(lower.clone(), successor.clone()),
        true,
    );
    let bound_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(successor, value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(lower, value), true);
    Theorem::new(Proposition::Implies(
        Box::new(no_overflow_premise),
        Box::new(Proposition::Implies(
            Box::new(bound_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Two signed int32 values are equal when the first is no greater than the
/// second and is not strictly less than it.
pub fn prove_int32_le_antisymmetric(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let reverse_le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(right.clone(), left.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(le_premise),
        Box::new(Proposition::Implies(
            Box::new(reverse_le_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A signed int32 value at most another is equal to it when it is not
/// strictly smaller.
pub fn prove_int32_le_and_not_lt_implies_eq(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let not_lt_premise = Proposition::Not(Box::new(Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    )));
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(le_premise),
        Box::new(Proposition::Implies(
            Box::new(not_lt_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A signed int32 value no greater than another and unequal to it is strictly
/// smaller. The explicit inequality premise keeps this deterministic rule on
/// the simple-certificate surface instead of relying on arithmetic search.
pub fn prove_int32_le_and_neq_implies_lt(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let le_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let neq_premise = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
        false,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), true);
    Theorem::new(Proposition::Implies(
        Box::new(le_premise),
        Box::new(Proposition::Implies(
            Box::new(neq_premise),
            Box::new(conclusion),
        )),
    ))
}

/// A signed int32 value at least another is equal to it when it is not
/// strictly greater.
pub fn prove_int32_ge_and_not_gt_implies_eq(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let ge_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
        true,
    );
    let not_gt_premise = Proposition::Not(Box::new(Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
        true,
    )));
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(ge_premise),
        Box::new(Proposition::Implies(
            Box::new(not_gt_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Any signed int32 value that is at least one is nonnegative.
pub fn prove_int32_positive_is_nonnegative(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed strict order implies signed non-strict order.
pub fn prove_int32_lt_implies_le(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(left, right), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// The negation of signed strict order implies the reverse non-strict order.
pub fn prove_int32_not_lt_implies_ge(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = Proposition::Not(Box::new(Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    )));
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(left, right), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Any strictly positive signed int32 value is nonnegative.
pub fn prove_int32_strictly_positive_is_nonnegative(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value, Bitvector32Term::Constant(0)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Incrementing a signed int32 value below `INT_MAX` is defined.
pub fn prove_int32_increment_below_max_is_defined(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(
            Box::new(value),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Independently proves and universally closes a pure int32 implication.
///
/// Every free bitvector variable in the requirements and conclusion must be
/// listed exactly once. This is the sole constructor for authority that lets
/// a Click pure theorem participate in whole-contract certification.
pub fn prove_universally_quantified_pure_implication(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
) -> Option<CVerifiedPureTheorem> {
    let declared = variables.iter().copied().collect::<BTreeSet<_>>();
    if declared.len() != variables.len() {
        return None;
    }
    let mut occurring = BTreeSet::new();
    for proposition in requirements.iter().chain(std::iter::once(&conclusion)) {
        collect_proposition_bitvector_variables(proposition, &mut occurring);
    }
    if occurring != declared {
        return None;
    }
    let assumptions = assumptions_with_propositions(&PureFactContext::new(), &requirements);
    if !assumptions.proves(&conclusion) {
        return None;
    }
    let implication = requirements
        .into_iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement), Box::new(body))
        });
    let proposition =
        variables
            .into_iter()
            .rev()
            .fold(implication, |body, var| Proposition::ForAll {
                var,
                sort: Sort::CInt32,
                body: Box::new(body),
            });
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(proposition),
    })
}

fn rewrite_int32_term_by_exact_equality(
    term: &Bitvector32Term,
    from: &Bitvector32Term,
    to: &Bitvector32Term,
) -> Bitvector32Term {
    if term == from {
        return to.clone();
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            rewrite_int32_term_by_exact_equality(left, from, to),
            rewrite_int32_term_by_exact_equality(right, from, to),
        )
    };
    match term {
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::add(left, right)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::subtract(left, right)
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Multiply(Box::new(left), Box::new(right))
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Divide(Box::new(left), Box::new(right))
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Remainder(Box::new(left), Box::new(right))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ArithmeticShiftRight(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseAnd(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseOr(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::BitwiseXor(Box::new(left), Box::new(right))
        }
        Bitvector32Term::BitwiseNot(value) => Bitvector32Term::BitwiseNot(Box::new(
            rewrite_int32_term_by_exact_equality(value, from, to),
        )),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: condition.clone(),
            then_term: Box::new(rewrite_int32_term_by_exact_equality(then_term, from, to)),
            else_term: Box::new(rewrite_int32_term_by_exact_equality(else_term, from, to)),
        },
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| rewrite_int32_term_by_exact_equality(argument, from, to))
                    .collect(),
            }
        }
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _)
        | Bitvector32Term::RangeFold { .. } => term.clone(),
    }
}

/// Independently checks an explicit sequence of int32 equality rewrites and
/// context-free normalization before issuing whole-contract authority.
///
/// This is deliberately a certificate checker, not an algebraic search: each
/// supplied equality must follow from the theorem requirements, must occur in
/// the current equality goal, and is applied in the supplied orientation.
pub fn prove_universally_quantified_pure_implication_by_int32_rewrites(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
    rewrites: Vec<Proposition>,
) -> Option<CVerifiedPureTheorem> {
    let assumptions = assumptions_with_propositions(&PureFactContext::new(), &requirements);
    let mut goal = conclusion.clone();
    for rewrite in rewrites {
        if !assumptions.proves(&rewrite) {
            return None;
        }
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(from, to), true) = rewrite
        else {
            return None;
        };
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal
        else {
            return None;
        };
        let rewritten_left = rewrite_int32_term_by_exact_equality(&left, &from, &to);
        let rewritten_right = rewrite_int32_term_by_exact_equality(&right, &from, &to);
        if rewritten_left == *left && rewritten_right == *right {
            return None;
        }
        goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(rewritten_left), Box::new(rewritten_right)),
            true,
        );
    }
    if !PureFactContext::new().proves(&goal) {
        return None;
    }
    let declared = variables.iter().copied().collect::<BTreeSet<_>>();
    if declared.len() != variables.len() {
        return None;
    }
    let mut occurring = BTreeSet::new();
    for proposition in requirements.iter().chain(std::iter::once(&conclusion)) {
        collect_proposition_bitvector_variables(proposition, &mut occurring);
    }
    if occurring != declared {
        return None;
    }
    let implication = requirements
        .into_iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement), Box::new(body))
        });
    let proposition =
        variables
            .into_iter()
            .rev()
            .fold(implication, |body, var| Proposition::ForAll {
                var,
                sort: Sort::CInt32,
                body: Box::new(body),
            });
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(proposition),
    })
}

/// Adding one on the left of a signed int32 value below the maximum is
/// defined.
pub fn prove_int32_one_plus_below_max_is_defined(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(Bitvector32Term::Constant(1), value),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Adding one on the left strictly increases a signed int32 value below the
/// maximum.
pub fn prove_int32_one_plus_strictly_increases(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            value.clone(),
            Bitvector32Term::Add(Box::new(Bitvector32Term::Constant(1)), Box::new(value)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Adding a nonnegative signed int32 amount within the remaining positive
/// headroom is defined.
pub fn prove_int32_nonnegative_add_within_max_is_defined(
    value: Bitvector32Term,
    amount: Bitvector32Term,
) -> Theorem {
    let amount_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), amount.clone()),
        true,
    );
    let within_headroom = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            value.clone(),
            Bitvector32Term::Subtract(
                Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
                Box::new(amount.clone()),
            ),
        ),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_add_overflows(value, amount), false);
    Theorem::new(Proposition::Implies(
        Box::new(amount_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(within_headroom),
            Box::new(conclusion),
        )),
    ))
}

/// Subtracting a nonnegative signed int32 amount no larger than the value is
/// defined.
pub fn prove_int32_nonnegative_subtract_within_value_is_defined(
    value: Bitvector32Term,
    amount: Bitvector32Term,
) -> Theorem {
    let amount_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), amount.clone()),
        true,
    );
    let amount_within_value = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(amount.clone(), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_subtract_overflows(value, amount),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(amount_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(amount_within_value),
            Box::new(conclusion),
        )),
    ))
}

/// A defined signed addition with a nonnegative right operand is at least its
/// left operand.
pub fn prove_int32_add_nonnegative_right_is_at_least_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let right_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), right.clone()),
        true,
    );
    let addition_is_defined = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), Bitvector32Term::add(left, right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(right_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(addition_is_defined),
            Box::new(conclusion),
        )),
    ))
}

/// A defined signed addition with a nonnegative left operand is at least its
/// right operand.
pub fn prove_int32_add_nonnegative_left_is_at_least_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let left_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), left.clone()),
        true,
    );
    let addition_is_defined = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(left.clone(), right.clone()),
        false,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(right.clone(), Bitvector32Term::add(left, right)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(left_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(addition_is_defined),
            Box::new(conclusion),
        )),
    ))
}

/// Decrementing a positive signed int32 value produces a nonnegative value.
pub fn prove_int32_positive_predecessor_is_nonnegative(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1))),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Decrementing a signed int32 value strictly above one leaves at least one.
pub fn prove_int32_above_one_predecessor_is_at_least_one(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(Bitvector32Term::Subtract(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Sealed authority for the fixed predecessor bound used by independent
/// contract certification. Unlike a bare [`Theorem`], callers cannot build
/// this evidence from an untrusted proposition.
pub fn certify_int32_above_one_predecessor_is_at_least_one() -> CVerifiedPureTheorem {
    let variable = Variable(0);
    let implication =
        prove_int32_above_one_predecessor_is_at_least_one(Bitvector32Term::Variable(variable));
    CVerifiedPureTheorem {
        theorem: Theorem::new(Proposition::ForAll {
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(implication.proposition().clone()),
        }),
    }
}

/// Decrementing a nonnegative signed int32 value preserves a non-strict
/// upper bound: nonnegativity rules out the `INT_MIN` wraparound, so the
/// predecessor stays strictly below the value and hence at most the bound.
pub fn prove_int32_nonnegative_predecessor_upper_bound(
    value: Bitvector32Term,
    bound: Bitvector32Term,
) -> Theorem {
    let nonnegative_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let bound_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value.clone(), bound.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Subtract(Box::new(value), Box::new(Bitvector32Term::Constant(1))),
            bound,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(nonnegative_premise),
        Box::new(Proposition::Implies(
            Box::new(bound_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Decrementing a positive signed int32 value strictly decreases it.
pub fn prove_int32_positive_predecessor_strictly_decreases(value: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Subtract(
                Box::new(value.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            value,
        ),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed non-strict order followed by strict order is strict order.
pub fn prove_int32_le_lt_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed strict order absorbs a non-strict upper extension.
pub fn prove_int32_lt_le_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed strict order is transitive.
pub fn prove_int32_lt_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_than(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed non-strict order is transitive.
pub fn prove_int32_le_transitive(
    first: Bitvector32Term,
    middle: Bitvector32Term,
    last: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(first.clone(), middle.clone()),
        true,
    );
    let second_premise =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(middle, last.clone()), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(first, last), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed non-strict greater-than order is transitive.
pub fn prove_int32_ge_transitive(
    last: Bitvector32Term,
    middle: Bitvector32Term,
    first: Bitvector32Term,
) -> Theorem {
    let first_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(last.clone(), middle.clone()),
        true,
    );
    let second_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(middle, first.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(last, first), true);
    Theorem::new(Proposition::Implies(
        Box::new(first_premise),
        Box::new(Proposition::Implies(
            Box::new(second_premise),
            Box::new(conclusion),
        )),
    ))
}

/// Signed greater-equal is the reversed spelling of signed less-equal.
pub fn prove_int32_ge_implies_reversed_le(
    greater: Bitvector32Term,
    lower: Bitvector32Term,
) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(greater.clone(), lower.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(lower, greater), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Signed non-strict order is preserved when written in reversed greater-or-equal form.
pub fn prove_int32_le_implies_reversed_ge(
    lower: Bitvector32Term,
    greater: Bitvector32Term,
) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lower.clone(), greater.clone()),
        true,
    );
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_greater_equal(greater, lower), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

pub fn prove_memory_load(memory: CMemory, pointer: Pointer) -> Theorem {
    let outcome = memory.load(&pointer);
    Theorem::new(Proposition::CMemoryLoads {
        memory,
        pointer,
        outcome,
    })
}

pub fn prove_memory_load_after_store_same(
    memory: CMemory,
    pointer: Pointer,
    value: CValue,
) -> Theorem {
    let stored = memory.store(pointer.clone(), value.clone());
    Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer,
        outcome: CExpressionOutcome::Value(value),
    })
}

pub fn prove_memory_load_after_store_other(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
) -> Option<Theorem> {
    if stored_pointer == loaded_pointer {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer: loaded_pointer,
        outcome,
    }))
}

pub fn prove_memory_load_after_store_distinct_under_assumptions(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
    assumptions: PureFactContext,
) -> Option<Theorem> {
    if !pointers_proven_distinct(&stored_pointer, &loaded_pointer, &assumptions) {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CMemoryLoads {
            memory: stored,
            pointer: loaded_pointer,
            outcome,
        },
        &assumptions,
        &[],
        &[],
    )))
}

/// Unsound partial while-rule, fenced to kernel tests. NOT an axiom.
///
/// This is deliberately not exported: it is `#[cfg(test)]`-only and
/// `pub(super)`, so it does not exist in a release build and no caller
/// outside `crate::kernel` can reach it. `Theorem::new` is `pub(super)`, so
/// `Proposition::CWhileInvariantRule` is unconstructible as a theorem from
/// outside the kernel too.
///
/// What it checks:
/// - every proposition in `invariant` is provable from `assumptions`, i.e.
///   the invariant holds on entry in the caller's `state`;
/// - there is *at least one* condition-fork context in which the condition is
///   true where the body runs to a single `Normal` path with no leftover
///   facts or obligations, and every proposition in `preserved` is provable;
/// - there is *at least one* condition-fork context in which the condition is
///   false where `postcondition` is provable.
///
/// What it does NOT check, and why that makes it unsound as a while rule:
/// - preservation in *every* condition-true fork, and the exit postcondition
///   in *every* condition-false fork. Both quantifiers are `any`, not `all`,
///   so a fork that breaks the invariant is simply skipped.
/// - any relation between `preserved` and what `body` actually does. The
///   body's post-state is matched as `CStatementOutcome::Normal(_)` and
///   discarded, and `preserved` is discharged against the *pre-body*
///   assumption context. A `preserved` list that holds before the body and
///   fails after it is accepted; see the kernel test
///   `while_invariant_rule_ignores_what_the_body_does_to_the_invariant`.
/// - genericity of `state` / `assumptions`. There is no havoc of the
///   locations the loop modifies, so preservation is shown for one step out
///   of the caller's specific state and does not generalize to an arbitrary
///   iteration.
/// - termination, and framing of memory across iterations.
///
/// Why it is fenced rather than fixed: the sound loop path already exists as
/// `c_loop_preservation_contexts` / `c_loop_invariants_hold_at_back_edge`
/// over state-parametric `CLoopInvariantCheck` (`SpecProposition`), with
/// `prepare_loop_top_state` supplying the havoc. Making this rule sound means
/// evaluating the invariant at the body's post-state, which a flat
/// `Vec<Proposition>` invariant plus a caller-supplied `preserved` cannot
/// express — the fix is to carry `CLoopInvariantCheck` instead, which changes
/// the shape of `Proposition::CWhileInvariantRule` and duplicates machinery
/// that already exists. That redesign is not worth it for a rule with no
/// callers, so the rule is fenced instead.
#[cfg(test)]
pub(super) fn prove_c_while_invariant_rule(
    state: CState,
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
    assumptions: PureFactContext,
    preserved: Vec<Proposition>,
    postcondition: Proposition,
) -> Option<Theorem> {
    if invariant
        .iter()
        .any(|invariant| !assumptions.proves(invariant))
    {
        return None;
    }

    let loop_assumptions = assumptions_with_propositions(&assumptions, &invariant);
    let step_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, true)
        .into_iter()
        .any(|step_assumptions| {
            let body_paths = execute_c_statement_paths(
                &state,
                &body,
                &step_assumptions,
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
                &mut ExecutionBudget::default(),
            );
            let Ok(body_paths) = body_paths else {
                return false;
            };
            let mut body_paths = body_paths.into_iter();
            let Some(body_path) = body_paths.next() else {
                return false;
            };
            if body_paths.next().is_some()
                || !body_path.facts.is_empty()
                || !body_path.obligations.is_empty()
                || !matches!(body_path.outcome, CStatementOutcome::Normal(_))
            {
                return false;
            }
            preserved
                .iter()
                .all(|preserved| step_assumptions.proves(preserved))
        });

    if !step_ok {
        return None;
    }

    let exit_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, false)
        .into_iter()
        .any(|exit_assumptions| exit_assumptions.proves(&postcondition));

    if !exit_ok {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition: Box::new(postcondition),
        },
        &assumptions,
        &[],
        &[],
    )))
}

/// True when a term's nesting depth exceeds the limit, counting through
/// embedded memory snapshots. Bounded walk: returns as soon as the limit is
/// crossed, so the check itself stays shallow-stack on pathological terms.
pub(crate) fn bitvector_term_deeper_than(term: &Bitvector32Term, limit: usize) -> bool {
    fn term_depth_exceeds(term: &Bitvector32Term, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        match term {
            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                memory_depth_exceeds(memory, remaining - 1)
                    || pointer_depth_exceeds(pointer, remaining - 1)
            }
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                term_depth_exceeds(left, remaining - 1) || term_depth_exceeds(right, remaining - 1)
            }
            Bitvector32Term::BitwiseNot(value) => term_depth_exceeds(value, remaining - 1),
            Bitvector32Term::If {
                condition,
                then_term,
                else_term,
            } => {
                condition_depth_exceeds(condition, remaining - 1)
                    || term_depth_exceeds(then_term, remaining - 1)
                    || term_depth_exceeds(else_term, remaining - 1)
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                term_depth_exceeds(start, remaining - 1)
                    || term_depth_exceeds(end, remaining - 1)
                    || term_depth_exceeds(initial, remaining - 1)
                    || term_depth_exceeds(body, remaining - 1)
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => arguments
                .iter()
                .any(|argument| term_depth_exceeds(argument, remaining - 1)),
        }
    }
    fn condition_depth_exceeds(condition: &ConditionTerm, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        match condition {
            ConditionTerm::Bitvector32SignedLessThan(left, right)
            | ConditionTerm::Bitvector32SignedLessEqual(left, right)
            | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
            | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
            | ConditionTerm::Bitvector32Equal(left, right)
            | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
            | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
            | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
            | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
            | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
                term_depth_exceeds(left, remaining - 1) || term_depth_exceeds(right, remaining - 1)
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                offset_depth_exceeds(left, remaining - 1)
                    || offset_depth_exceeds(right, remaining - 1)
            }
            ConditionTerm::PointerEqual(left, right) => {
                pointer_depth_exceeds(left, remaining - 1)
                    || pointer_depth_exceeds(right, remaining - 1)
            }
            ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
        }
    }
    fn pointer_depth_exceeds(pointer: &Pointer, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        offset_depth_exceeds(&pointer.offset, remaining - 1)
    }
    fn offset_depth_exceeds(offset: &PointerOffsetTerm, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        match offset {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
            PointerOffsetTerm::Add(left, right) => {
                offset_depth_exceeds(left, remaining - 1)
                    || offset_depth_exceeds(right, remaining - 1)
            }
            PointerOffsetTerm::Int32Scaled { value, .. } => {
                term_depth_exceeds(value, remaining - 1)
            }
        }
    }
    fn memory_depth_exceeds(memory: &CMemory, remaining: usize) -> bool {
        if remaining == 0 {
            return true;
        }
        memory.cells.iter().any(|(pointer, value)| {
            pointer_depth_exceeds(pointer, remaining - 1)
                || match value {
                    CValue::Void => false,
                    CValue::Int32(term) | CValue::UInt8(term) => {
                        term_depth_exceeds(term, remaining - 1)
                    }
                    CValue::Pointer(pointer) => pointer_depth_exceeds(pointer, remaining - 1),
                }
        })
    }
    term_depth_exceeds(term, limit)
}
