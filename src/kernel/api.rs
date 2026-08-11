use super::functions::apply_verified_contract_resource_transition;
pub(super) use super::memory_provenance::*;
use super::prelude::*;

pub(in crate::kernel) mod contract_certification;
pub use contract_certification::*;
use contract_certification::{
    c_function_contract_certification_assumptions, certification_proves_proposition,
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

pub(crate) fn c_pointers_proven_equal_for_memory_resolution(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    super::reasoning::pointers_proven_equal_for_memory_resolution(left, right, assumptions)
}

/// Certifies a stated condition target from one explicit condition source and
/// deterministic memory-resolution evidence. Unlike whole-fact transport,
/// this permits a target to retain an old load on one side while transporting
/// the other side to a newer snapshot.
pub fn prove_c_condition_fact_target_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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

    for (name, binding) in &state.locals.bindings {
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    let Some(first) = propositions.pop() else {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    };

    propositions
        .into_iter()
        .rev()
        .fold(first, |right, left| proposition_and(left, right))
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
        &Assumptions::new(),
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
        &Assumptions::new(),
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
    assumptions: Assumptions,
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
    prove_symbolic_c_execution(state, statement, Assumptions::new())
}

pub fn prove_c_statement_execution_under_assumptions(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, assumptions)
}

pub fn prove_symbolic_c_execution(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    let selection_assumptions =
        assumptions_with_propositions(&Assumptions::new(), &derived_entry_facts);
    let Some(base_assumptions) = c_function_contract_certification_assumptions(
        &state,
        &function,
        &arguments,
        Assumptions::new(),
        &selection_assumptions,
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
    let Some(resource_condition_cases) =
        contract_resource_condition_cases(&state, &function, &arguments, &base_assumptions)
    else {
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
        let case_seed = assumptions_with_propositions(&Assumptions::new(), &case_facts);
        let Some(mut assumptions) = c_function_contract_certification_assumptions(
            &state,
            &function,
            &arguments,
            case_seed,
            &selection_assumptions,
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
            let Some(entry_resources) = expand_all_composite_resource_facts(
                entry_state.resources(),
                function.composite_resource_definitions(),
                entry_state.memory(),
                &assumptions,
            ) else {
                return CFunctionContractExecution {
                    execution: SymbolicCExecution {
                        paths: Vec::new(),
                        limit: None,
                    },
                };
            };
            entry_state.resources = entry_resources.clone();
            for fact in &derived_entry_facts {
                if certification_proves_proposition(&assumptions, fact)
                    || resources_certify_loadability(
                        &entry_state,
                        &entry_resources,
                        fact,
                        &assumptions,
                    )
                {
                    assumptions = assumptions.assume_proposition(fact.clone());
                }
            }
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
        let execution = match mode {
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
        };
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
    let assumptions = Assumptions::new().assume_condition(condition.clone(), true);
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
    let assumptions = Assumptions::new().assume_condition(condition.clone(), false);
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
    assumptions: Assumptions,
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
    assumptions: Assumptions,
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
