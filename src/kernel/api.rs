use super::functions::{
    apply_verified_contract_resource_transition,
    construct_c_function_resource as construct_c_function_resource_checked,
    function_return_resources_definitionally_established,
};
pub(super) use super::memory_provenance::*;
use super::prelude::*;
use crate::instrumentation::ContractFallback;
use std::sync::Arc;

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
mod algebraic_cases;
pub(in crate::kernel) use algebraic_cases::algebraic_constructor_case_equations;
pub use algebraic_cases::algebraic_constructor_cases;
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

pub fn bool_value(bits: impl Into<Bitvector32Term>) -> CValue {
    let bits = bits.into();
    CValue::Bool(Bitvector32Term::if_then_else(
        ConditionTerm::equal(bits, Bitvector32Term::Constant(0)),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ))
}

pub fn int16(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int16(bits.into())
}

pub fn uint8(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt8(bits.into())
}

pub fn uint16(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt16(bits.into())
}

pub fn uint32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt32(bits.into())
}

pub fn int64(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int64(bits.into())
}

pub fn uint64(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt64(bits.into())
}

pub fn float32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Float32(bits.into())
}

pub fn float64(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Float64(bits.into())
}

/// True when `pointer` addresses within a live heap allocation of `memory`,
/// matching allocation keys either structurally or up to exact
/// materialization of the loads embedded in the key and pointer forms.
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

/// Recognizes two condition-fact forms as the same fact under the given
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
    whole_loop_effect_facts: Vec<Proposition>,
}

/// A body state produced by a checked preservation proof that may be the
/// final loop iteration. The proof layer supplies the facts retained at that
/// body frontier; the kernel independently checks the post-body condition
/// before exporting the state as a loop exit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CLoopFinalExitCandidate {
    state: CState,
    pure_facts: Vec<Proposition>,
}

impl CLoopFinalExitCandidate {
    pub(crate) fn new(state: CState, pure_facts: Vec<Proposition>) -> Self {
        Self { state, pure_facts }
    }

    pub(crate) fn state(&self) -> &CState {
        &self.state
    }

    pub(crate) fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }
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

    /// Effect summaries generated by this loop's whole-span checks. A
    /// step-span structural effect must not use one of these summaries as if
    /// it were the effect of a single iteration; nested execution effects
    /// remain available separately on the checked path.
    pub fn whole_loop_effect_facts(&self) -> &[Proposition] {
        &self.whole_loop_effect_facts
    }
}

#[allow(clippy::too_many_arguments)]
pub fn c_loop_preservation_contexts(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    body: &CStatement,
    assumptions: &PureFactContext,
) -> Result<Vec<CLoopPreservationContext>, String> {
    c_loop_preservation_contexts_with_mode(
        loop_entry_state,
        condition,
        invariant_checks,
        effect_checks,
        resource_specs,
        body,
        assumptions,
        false,
    )
}

/// Computes loop-body preservation contexts for a C `do ... while` loop.
/// Unlike a pre-tested `while`, the first body entry cannot assume that the
/// post-test condition is true; the condition only guards later iterations.
pub fn c_do_while_preservation_contexts(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    body: &CStatement,
    assumptions: &PureFactContext,
) -> Result<Vec<CLoopPreservationContext>, String> {
    c_loop_preservation_contexts_with_mode(
        loop_entry_state,
        condition,
        invariant_checks,
        effect_checks,
        resource_specs,
        body,
        assumptions,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn c_loop_preservation_contexts_with_mode(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    resource_specs: &[CResourceSpec],
    body: &CStatement,
    assumptions: &PureFactContext,
    do_while: bool,
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
    let mut variables =
        KernelVariableGenerator::fresh_for(budget.next_kernel_variable, existing_variables);
    let head = prepare_loop_top_state(
        loop_entry_state,
        effect_checks,
        resource_specs,
        body,
        assumptions,
        &mut budget,
        &mut variables,
    )
    .map_err(|error| format!("could not prepare loop effects: {error:?}"))?;
    if let Some(failure) = head.resource_failures.first() {
        return Err(failure.clone());
    }
    // Preservation runs the body with the loop's declared resources.
    let top_state = head.body;
    let whole_loop_effect_summaries = head.summaries;
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
        let condition_contexts = if do_while {
            vec![(invariant_facts.clone(), invariant_obligations.clone())]
        } else {
            assume_condition_truthiness(
                &top_state,
                condition,
                assumptions,
                &invariant_facts,
                &invariant_obligations,
                true,
                &mut budget,
            )
            .map_err(|error| format!("could not assume the loop condition: {error:?}"))?
        };
        for (facts, obligations) in condition_contexts {
            let context_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
            if let Some(obligation) = obligations.iter().find(|obligation| {
                !required_obligation_is_exactly_discharged(
                    &context_assumptions,
                    obligation.proposition(),
                )
            }) {
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
                loop_entry_state: loop_entry_state.clone(),
                pure_facts,
                whole_loop_effect_facts: whole_loop_effect_summaries.clone(),
            });
        }
    }
    Ok(contexts)
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

/// Refuses a loop `decreases` component whose variables can be written
/// through an escaped address. See the termination module for the rule.
pub fn c_reject_address_escaped_loop_measures(
    function_name: &str,
    measures: &[CExpression],
    body: &CStatement,
) -> Result<(), String> {
    crate::kernel::termination::c_reject_address_escaped_loop_measures(
        function_name,
        measures,
        body,
    )
}

/// The source form of one declared `decreases` component, for diagnostics.
pub fn c_ranking_measure_source(measure: &CExpression) -> String {
    crate::kernel::termination::c_ranking_measure_display(measure)
}

/// The source form of a whole declared `decreases` clause, for diagnostics.
pub fn c_ranking_measures_source(measures: &[CExpression]) -> String {
    crate::kernel::termination::c_ranking_measures_display(measures)
}

/// The ranked loop's back-edge bundle members, after its invariants.
///
/// `iteration_entry_state` reads each declared component at preserve entry
/// and `state` at the back edge. The member order is fixed by
/// `collect_loop_ranking_obligations`; see that function for the shape.
pub fn c_loop_ranking_obligations_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    ranking_measures: &[CExpression],
) -> Result<Vec<ProofObligation>, String> {
    collect_loop_ranking_obligations(state, iteration_entry_state, ranking_measures)
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
            "missing invariant fact{}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default()
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
    abstract_c_state_for_join_across(state, std::slice::from_ref(&state), stable_entry_locals)
}

/// Builds one arm's abstract join state using a variable reservation shared
/// by every sibling arm. Nested joins may already contain abstract variables;
/// reserving the union makes the next abstraction fresh and deterministic
/// across all siblings rather than dependent on which arm was abstracted
/// earlier.
pub fn abstract_c_state_for_join_across(
    state: &CState,
    sibling_states: &[&CState],
    stable_entry_locals: &BTreeMap<String, CValue>,
) -> Result<CState, String> {
    abstract_c_state_for_join_across_with_policy(state, sibling_states, stable_entry_locals, false)
}

/// Builds a branch-interface abstraction while retaining non-scalar memory
/// when every checked arm has the exact same such memory. This avoids
/// forgetting an already-established immutable frame merely because scalar
/// locals differ across the branch. Any disagreement uses the ordinary
/// conservative memory havoc.
pub fn abstract_c_state_for_interface_join_across(
    state: &CState,
    sibling_states: &[&CState],
    stable_entry_locals: &BTreeMap<String, CValue>,
) -> Result<CState, String> {
    abstract_c_state_for_join_across_with_policy(state, sibling_states, stable_entry_locals, true)
}

fn abstract_c_state_for_join_across_with_policy(
    state: &CState,
    sibling_states: &[&CState],
    stable_entry_locals: &BTreeMap<String, CValue>,
    preserve_exact_common_memory: bool,
) -> Result<CState, String> {
    let mut existing_variables = BTreeSet::new();
    for sibling in sibling_states {
        crate::instrumentation::record_deterministic_work(
            sibling.locals.bindings.len()
                + sibling.memory.blocks.len()
                + sibling.memory.cells.len()
                + sibling.memory.union_cells.len()
                + sibling.memory.ended_local_blocks.len()
                + sibling.resources().facts().len()
                + sibling.counted_populations.len(),
        );
        collect_c_state_bitvector_variables(sibling, &mut existing_variables);
        for block in sibling.memory.blocks.keys() {
            if let Some(index) = block
                .strip_prefix("havoc:")
                .and_then(|index| index.parse::<u64>().ok())
            {
                existing_variables.insert(Variable(index));
            }
        }
    }
    for value in stable_entry_locals.values() {
        crate::instrumentation::record_deterministic_work(1);
        collect_c_value_bitvector_variables(value, &mut existing_variables);
    }
    let mut variables = KernelVariableGenerator::fresh_for(1_000_000, existing_variables);
    let mut abstract_state = state.clone();
    // A nested arm may already carry a memory-havoc marker from an inner
    // join. Retain the union on every sibling so the enclosing abstraction is
    // deterministic without discarding any memory-distinction history.
    for sibling in sibling_states {
        for (block, contents) in sibling.memory.blocks.iter() {
            if block.starts_with("havoc:") {
                std::sync::Arc::make_mut(&mut abstract_state.memory.blocks)
                    .insert(block.clone(), contents.clone());
            }
        }
    }
    abstract_state.next_local_lifetime = sibling_states
        .iter()
        .map(|sibling| sibling.next_local_lifetime)
        .max()
        .unwrap_or(state.next_local_lifetime);
    let mut abstract_objects = Vec::new();
    let mut preserved_blocks = BTreeSet::new();

    for (name, binding) in state.locals.bindings.iter() {
        crate::instrumentation::record_deterministic_work(1);
        let CLocalBinding::Object {
            value,
            c_type,
            slot,
            ..
        } = binding
        else {
            continue;
        };
        let abstract_value = if stable_entry_locals.get(name) == Some(value) {
            value.clone()
        } else {
            match c_type {
                CType::Void => continue,
                CType::Bool => CValue::Bool(Bitvector32Term::if_then_else(
                    ConditionTerm::Variable(variables.next()),
                    Bitvector32Term::Constant(1),
                    Bitvector32Term::Constant(0),
                )),
                CType::VoidPointer => {
                    CValue::typed_pointer(Pointer::symbolic(variables.next()), *c_type)
                }
                CType::Int16 => int16(Bitvector32Term::Variable(variables.next())),
                CType::Int32 => int32(Bitvector32Term::Variable(variables.next())),
                CType::Int64 => CValue::Int64(Bitvector32Term::Variable(variables.next())),
                CType::UInt32 => uint32(Bitvector32Term::Variable(variables.next())),
                CType::UInt8 => uint8(Bitvector32Term::Variable(variables.next())),
                CType::UInt16 => uint16(Bitvector32Term::Variable(variables.next())),
                CType::UInt64 => CValue::UInt64(Bitvector32Term::Variable(variables.next())),
                CType::Float32 => CValue::Float32(Bitvector32Term::Variable(variables.next())),
                CType::Float64 => CValue::Float64(Bitvector32Term::Variable(variables.next())),
                CType::Int16Pointer
                | CType::UInt16Pointer
                | CType::Int32Pointer
                | CType::UInt8Pointer
                | CType::UInt32Pointer
                | CType::Int64Pointer
                | CType::UInt64Pointer
                | CType::Int16PointerPointer
                | CType::UInt16PointerPointer
                | CType::Int32PointerPointer
                | CType::UInt8PointerPointer
                | CType::UInt32PointerPointer
                | CType::Int64PointerPointer
                | CType::UInt64PointerPointer
                | CType::Float32Pointer
                | CType::Float64Pointer
                | CType::Float32PointerPointer
                | CType::Float64PointerPointer => {
                    CValue::typed_pointer(Pointer::symbolic(variables.next()), *c_type)
                }
                CType::FunctionPointer(_) => {
                    CValue::typed_pointer(Pointer::symbolic_function(variables.next()), *c_type)
                }
                CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::Int16Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int64Array(_)
                | CType::UInt64Array(_)
                | CType::Float32Array(_)
                | CType::Float64Array(_) => {
                    unreachable!("array objects use CLocalBinding::ArrayObject")
                }
            }
        };
        preserved_blocks.insert(slot.block.clone());
        abstract_objects.push((name.clone(), abstract_value, *c_type));
    }

    let comparable_memory = |state: &CState| {
        crate::instrumentation::record_deterministic_work(
            state.memory.blocks.len()
                + state.memory.cells.len()
                + state.memory.union_cells.len()
                + state.memory.ended_local_blocks.len(),
        );
        let mut memory = state.memory.clone();
        std::sync::Arc::make_mut(&mut memory.blocks)
            .retain(|block, _| !preserved_blocks.contains(block));
        std::sync::Arc::make_mut(&mut memory.cells)
            .retain(|pointer, _| !preserved_blocks.contains(&pointer.block));
        std::sync::Arc::make_mut(&mut memory.union_cells)
            .retain(|(pointer, _), _| !preserved_blocks.contains(&pointer.block));
        memory
    };
    let common_memory = preserve_exact_common_memory && {
        let expected = comparable_memory(state);
        sibling_states
            .iter()
            .all(|sibling| comparable_memory(sibling) == expected)
    };
    if !common_memory {
        if preserve_exact_common_memory {
            let sibling_memories = sibling_states
                .iter()
                .map(|sibling| &sibling.memory)
                .collect::<Vec<_>>();
            abstract_state.memory = abstract_state.memory.with_interface_memory_havoc(
                variables.next(),
                &preserved_blocks,
                &sibling_memories,
            )?;
        } else {
            abstract_state.memory = abstract_state.memory.with_loop_memory_havoc(
                variables.next(),
                &preserved_blocks,
                None,
            );
        }
    }
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

pub fn c_function_address(name: impl Into<String>) -> CExpression {
    CExpression::FunctionAddress(name.into())
}

/// The values a composite definition binds its existential witnesses to for
/// `composite` under `memory` and `assumptions`, in declaration order. This
/// is the same deterministic choice body instantiation makes, so a surface
/// substitution of witness names agrees with the kernel's own expansion.
pub fn composite_resource_witness_values(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<CValue>> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = CState::new().with_memory(memory.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    let assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    super::functions::bind_composite_witnesses_with_held(
        definition,
        arguments,
        &mut state,
        resources,
        &assumptions,
    )
}

pub fn c_cast(expression: CExpression, target_type: CType) -> CExpression {
    c_cast_with_pointee_volatile(expression, target_type, false)
}

pub fn c_cast_with_pointee_volatile(
    expression: CExpression,
    target_type: CType,
    pointee_volatile: bool,
) -> CExpression {
    c_cast_with_pointee_qualifiers(expression, target_type, pointee_volatile, false)
}

pub fn c_cast_with_pointee_qualifiers(
    expression: CExpression,
    target_type: CType,
    pointee_volatile: bool,
    pointee_constant: bool,
) -> CExpression {
    CExpression::Cast {
        expression: Box::new(expression),
        target_type,
        pointee_volatile,
        pointee_constant,
    }
}

pub fn c_conditional(
    condition: CExpression,
    then_branch: CExpression,
    else_branch: CExpression,
) -> CExpression {
    CExpression::Conditional {
        condition: Box::new(condition),
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn c_float_classification(
    expression: CExpression,
    classification: CFloatClassification,
) -> CExpression {
    CExpression::FloatClassification {
        expression: Box::new(expression),
        classification,
    }
}

pub fn c_float_negate(expression: CExpression) -> CExpression {
    CExpression::FloatNegate(Box::new(expression))
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

pub fn c_uint32_literal(value: u32) -> CExpression {
    CExpression::Value(uint32(Bitvector32Term::Constant(value)))
}

pub fn c_int64_literal(value: i64) -> CExpression {
    CExpression::Value(int64(Bitvector32Term::Int64Constant(value)))
}

pub fn c_uint64_literal(value: u64) -> CExpression {
    CExpression::Value(uint64(Bitvector32Term::UInt64Constant(value)))
}

pub fn c_float32_literal(bits: u32) -> CExpression {
    CExpression::Value(float32(Bitvector32Term::Constant(bits)))
}

pub fn c_float64_literal(bits: u64) -> CExpression {
    CExpression::Value(float64(Bitvector32Term::UInt64Constant(bits)))
}

pub fn c_pointer_value(pointer: Pointer) -> CExpression {
    CExpression::Value(CValue::pointer(pointer))
}

pub fn c_typed_pointer_value(pointer: Pointer, c_type: CType) -> CExpression {
    CExpression::Value(CValue::typed_pointer(pointer, c_type))
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
        volatile: false,
    }
}

/// Construct one checked sequential access to the typed cell reached by
/// `pointer`.  This is the kernel projection used by `READ_ONCE` and the
/// lvalue side of `WRITE_ONCE`/`rcu_assign_pointer`; it is deliberately an
/// observable sequential access, not an atomic or release/acquire operation.
pub fn c_volatile_typed_load(pointer: CExpression, value_type: CType) -> CExpression {
    CExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
        volatile: true,
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
    c_heap_allocate_sized_with_zeroed(target, bytes, false)
}

pub fn c_heap_allocate_sized_with_zeroed(
    target: impl Into<String>,
    bytes: CExpression,
    zeroed: bool,
) -> CStatement {
    CStatement::HeapAllocate {
        target: target.into(),
        bytes,
        zeroed,
    }
}

pub fn c_heap_free(pointer: CExpression) -> CStatement {
    CStatement::HeapFree { pointer }
}

pub fn c_declare(name: impl Into<String>, c_type: CType) -> CStatement {
    c_declare_volatile(name, c_type, false)
}

pub fn c_declare_volatile(name: impl Into<String>, c_type: CType, volatile: bool) -> CStatement {
    c_declare_qualified(name, c_type, volatile, false)
}

pub fn c_declare_qualified(
    name: impl Into<String>,
    c_type: CType,
    volatile: bool,
    pointee_volatile: bool,
) -> CStatement {
    c_declare_with_all_qualifiers(name, c_type, volatile, pointee_volatile, false, false)
}

pub fn c_declare_with_all_qualifiers(
    name: impl Into<String>,
    c_type: CType,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
        volatile,
        pointee_volatile,
        constant,
        pointee_constant,
    }
}

pub fn c_declare_aggregate(name: impl Into<String>, layout: CAggregateLayout) -> CStatement {
    CStatement::DeclareAggregate {
        name: name.into(),
        layout,
    }
}

pub fn c_copy_aggregate(
    target: CExpression,
    source: CExpression,
    layout: CAggregateLayout,
) -> CStatement {
    CStatement::CopyAggregate {
        target,
        source,
        layout,
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
    CStatement::Seq(Arc::new(first), Arc::new(second))
}

pub fn c_skip() -> CStatement {
    CStatement::Skip
}

pub fn c_break() -> CStatement {
    CStatement::Break
}

pub fn c_continue() -> CStatement {
    CStatement::Continue
}

pub fn c_switch(expression: CExpression, cases: Vec<CSwitchCase>) -> CStatement {
    CStatement::Switch { expression, cases }
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
        volatile: false,
    }
}

/// Construct the checked sequential store used by the kernel pointer
/// publication primitives.  It has ordinary C memory effects plus one
/// ordered access fact; it does not provide a concurrent-reader or
/// release/acquire theorem.
pub fn c_volatile_typed_store(
    pointer: CExpression,
    value: CExpression,
    value_type: CType,
) -> CStatement {
    CStatement::TypedStore {
        pointer,
        value,
        value_type,
        volatile: true,
    }
}

pub fn c_update(
    target: CExpression,
    operator: CUpdateOperator,
    operand: CExpression,
) -> CStatement {
    CStatement::Update {
        target,
        operator,
        operand,
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
        resource_specs: Vec::new(),
        ranking_measures: Vec::new(),
        do_while: false,
        body: Box::new(body),
    }
}

impl CStatement {
    /// Declares the resources a loop holds for itself.
    ///
    /// An empty declaration leaves the loop inheriting the enclosing resource
    /// context, which is what every loop without `owns` or `views` clauses
    /// does. A statement that is not a loop head keeps its shape: only a loop
    /// carries resource declarations.
    pub fn with_loop_resource_specs(mut self, specs: Vec<CResourceSpec>) -> Self {
        if specs.is_empty() {
            return self;
        }
        if let Self::While { resource_specs, .. } = &mut self {
            *resource_specs = specs;
        }
        self
    }

    /// Declares the loop's `decreases` components in source order.
    ///
    /// An empty declaration leaves the loop unranked, which is what every
    /// loop without a `decreases` clause is. The components travel with the
    /// loop head so the back-edge invariant bundle and the whole-function
    /// termination pass agree on exactly which measure was checked.
    pub fn with_loop_ranking_measures(mut self, measures: Vec<CExpression>) -> Self {
        if measures.is_empty() {
            return self;
        }
        if let Self::While {
            ranking_measures, ..
        } = &mut self
        {
            *ranking_measures = measures;
        }
        self
    }
}

pub fn c_do_while(condition: CExpression, body: CStatement) -> CStatement {
    c_do_while_with_invariant_and_effect_checks(condition, Vec::new(), Vec::new(), body)
}

pub fn c_do_while_with_invariant_and_effect_checks(
    condition: CExpression,
    invariant_checks: Vec<CLoopInvariantCheck>,
    effect_checks: Vec<CLoopEffectCheck>,
    body: CStatement,
) -> CStatement {
    CStatement::While {
        condition,
        invariant: Vec::new(),
        invariant_checks,
        effect_checks,
        resource_specs: Vec::new(),
        ranking_measures: Vec::new(),
        do_while: true,
        body: Box::new(body),
    }
}

pub fn c_continue_with_step(step: CStatement) -> CStatement {
    CStatement::ContinueWithStep {
        step: Box::new(step),
    }
}

/// Lowers the body of a C `for` loop to the existing `while` representation.
/// A normal body completion reaches the appended step through the sequence;
/// a `continue` must execute that same step before returning to the loop head.
/// Nested loops are opaque here because their `continue` statements target
/// those inner loops instead.
pub fn c_for_body_with_step(body: CStatement, step: CStatement) -> CStatement {
    fn rewrite(statement: CStatement, step: &CStatement) -> CStatement {
        match statement {
            CStatement::Continue => c_continue_with_step(step.clone()),
            CStatement::Seq(first, second) => c_seq(
                rewrite((*first).clone(), step),
                rewrite((*second).clone(), step),
            ),
            CStatement::If {
                condition,
                then_branch,
                else_branch,
            } => c_if(
                condition,
                rewrite(*then_branch, step),
                rewrite(*else_branch, step),
            ),
            CStatement::Switch { expression, cases } => c_switch(
                expression,
                cases
                    .into_iter()
                    .map(|case| CSwitchCase {
                        value: case.value,
                        body: Box::new(rewrite(*case.body, step)),
                    })
                    .collect(),
            ),
            // A nested loop consumes its own `continue` outcome.
            statement @ CStatement::While { .. } => statement,
            statement => statement,
        }
    }

    c_seq(rewrite(body, &step), step)
}

pub fn c_parameter(name: impl Into<String>, c_type: CType) -> CParameter {
    CParameter::new(name, c_type)
}

pub fn c_parameter_with_aggregate_layout(
    name: impl Into<String>,
    c_type: CType,
    layout: CAggregateLayout,
) -> CParameter {
    CParameter::new(name, c_type).with_aggregate_layout(layout)
}

pub fn c_function(
    return_type: CType,
    name: impl Into<String>,
    parameters: Vec<CParameter>,
    body: CStatement,
) -> CFunction {
    CFunction::new(return_type, name, parameters, body)
}

/// Lowers a spec proposition at `state`, the one lowering every proof-side
/// proposition and every contract clause share. `entry_state` is what
/// `old(...)` refers to. The result is the proposition on the lowering's
/// single path with the facts its loads introduced and the obligations
/// they left open (a load the state does not show loadable); `None` when
/// the lowering fails or splits into several paths.
pub fn c_lower_spec_proposition_at_state(
    state: &CState,
    proposition: &SpecProposition,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(Proposition, Vec<Proposition>, Vec<Proposition>), String> {
    let (proposition, facts, obligations, _) = c_lower_spec_proposition_at_state_with_provenance(
        state,
        proposition,
        entry_state,
        assumptions,
    )?;
    Ok((proposition, facts, obligations))
}

/// [`c_lower_spec_proposition_at_state`], also reporting the head chain of
/// the lowered proposition: which of its outermost nodes this lowering
/// inserted as a guard, which were written, and the exact kernel variable
/// each written universal bound its written name to. A proof that
/// introduces the head of this goal reads the record instead of inferring
/// the correspondence from the shape the written syntax happens to share.
pub fn c_lower_spec_proposition_at_state_with_provenance(
    state: &CState,
    proposition: &SpecProposition,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<
    (
        Proposition,
        Vec<Proposition>,
        Vec<Proposition>,
        LoweringIntroductions,
    ),
    String,
> {
    let (goal, facts, obligations, introductions) =
        c_lower_spec_proposition_with_checked_obligations(
            state,
            proposition,
            entry_state,
            assumptions,
        )?;
    Ok((
        goal,
        facts,
        obligations
            .into_iter()
            .map(|obligation| obligation.proposition().clone())
            .collect(),
        introductions,
    ))
}

/// Proof-side lowering keeps mandatory verification conditions distinct from
/// assumable evaluation obligations until the caller checks their evidence.
pub(crate) fn c_lower_spec_proposition_with_checked_obligations(
    state: &CState,
    proposition: &SpecProposition,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<
    (
        Proposition,
        Vec<Proposition>,
        Vec<ProofObligation>,
        LoweringIntroductions,
    ),
    String,
> {
    let lowering_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .defer_non_exact_loadability_obligations();
    let mut budget = ExecutionBudget::default();
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        state,
        proposition,
        entry_state,
        &lowering_assumptions,
        &mut budget,
    )
    .map_err(|limit| match limit {
        ExecutionLimit::UnsupportedIntegerExistentialBody => {
            "Integer existential bodies must currently be pure and total".to_string()
        }
        limit => format!("the kernel lowering hit {limit:?}"),
    })?;
    let [path] = paths.as_slice() else {
        return Err(format!(
            "the kernel lowering produced {} paths, not one",
            paths.len()
        ));
    };
    Ok((
        path.proposition.clone(),
        path.facts
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect(),
        path.obligations.clone(),
        path.introductions.clone(),
    ))
}

/// Evaluates a spec expression at `state`: the one evaluation every
/// proof-side expression and every contract expression share. `entry_state`
/// is what `old(...)` refers to. The result is the value on the evaluation's
/// single path with the load obligations the path left open.
pub fn c_evaluate_spec_expression_at_state(
    state: &CState,
    expression: &SpecExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(CValue, Vec<Proposition>), String> {
    let (value, obligations) = c_evaluate_spec_expression_with_checked_obligations(
        state,
        expression,
        entry_state,
        assumptions,
    )?;
    Ok((
        value,
        obligations
            .into_iter()
            .map(|obligation| obligation.proposition().clone())
            .collect(),
    ))
}

/// Retains mandatory conversion conditions for proof-side expression capture.
pub(crate) fn c_evaluate_spec_expression_with_checked_obligations(
    state: &CState,
    expression: &SpecExpression,
    entry_state: Option<&CState>,
    assumptions: &PureFactContext,
) -> Result<(CValue, Vec<ProofObligation>), String> {
    let lowering_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .defer_non_exact_loadability_obligations();
    let mut budget = ExecutionBudget::default();
    let paths = evaluate_spec_expression_paths_with_loop_entry(
        state,
        expression,
        entry_state,
        &lowering_assumptions,
        &mut budget,
    )
    .map_err(|limit| format!("the kernel evaluation hit {limit:?}"))?;
    let [path] = paths.as_slice() else {
        return Err(format!(
            "the kernel evaluation produced {} paths, not one",
            paths.len()
        ));
    };
    Ok((path.value.clone(), path.obligations.clone()))
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
    let mut entry = bind_c_function_arguments(caller_state, function, &values)?;
    // This API rebinds a proof frontier, including an explicitly unfolded
    // entry representation. It is not the modular call ownership transfer.
    entry.instance_field_scope = caller_state.instance_field_scope.clone();
    Some(entry)
}

/// Produces the exact callee entry state used by contract verification.
///
/// Composite requirements normally use their canonical contained resources.
/// When proof execution has explicitly observed or unfolded part of a recursive
/// resource, independent certification preserves that equivalent form so
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

/// Whether a body outcome establishes every resource the contract returns,
/// by the rule contract certification applies to a `produces` claim. A proof
/// consults this before reading the outcome through the contract's resource
/// transition, so the surface accepts exactly the exits certification does.
pub fn c_function_return_resources_definitionally_established(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    function_return_resources_definitionally_established(
        caller_state,
        function,
        arguments,
        outcome,
        assumptions,
    )
}

/// Applies a function's already-checked resource effect to a concrete body
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

/// Prepares the count interpretation used to prove a function's return
/// resource invariants, without transferring the body's ownership. This
/// creates no theorem or invariant facts: the eventual specification must
/// still be certified against the checked exit outcome. In particular callers
/// must not project resource invariant facts from this provisional state.
pub(crate) fn function_body_with_return_counts(
    body: &CFunctionOutcome,
    checked_exit: &CFunctionOutcome,
) -> CFunctionOutcome {
    match (body, checked_exit) {
        (
            CFunctionOutcome::Return { value, state },
            CFunctionOutcome::Return {
                state: exit_state, ..
            },
        ) => {
            let mut state = state.clone();
            state.counted_populations = exit_state.counted_populations.clone();
            CFunctionOutcome::Return {
                value: value.clone(),
                state,
            }
        }
        _ => body.clone(),
    }
}

/// Applies a kernel-checked, zero-source construction of one abstract token
/// to a function outcome state.
pub fn construct_c_function_resource(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    result: &CValue,
    constructed: &CResourceFact,
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    match construct_c_function_resource_checked(
        state,
        function,
        arguments,
        result,
        constructed,
        assumptions,
    ) {
        Ok(Ok(state)) => Ok(state),
        Ok(Err(error)) => Err(format!("resource construction failed: {error:?}")),
        Err(limit) => Err(format!(
            "resource construction hit execution limit {limit:?}"
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
    let mut budget = ExecutionBudget::for_c_expression(expression);
    let paths =
        evaluate_c_expression_paths(state, expression, &PureFactContext::new(), &mut budget)?;
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

/// Introduces an int32 universal's binder into a proposition without allowing
/// it to reuse a variable identity already present in the surrounding proof
/// facts. The body is the scope of the binder, so alpha-renaming it before
/// exposing that scope is what makes the operation safe at a proof-object
/// boundary rather than relying on a surface lowerer's numbering convention.
pub(crate) fn freshen_int32_forall_body(
    binder: Variable,
    body: &Proposition,
    surrounding: &[Proposition],
) -> (Variable, Proposition) {
    if !surrounding
        .iter()
        .any(|proposition| proposition_variables(proposition).contains(&binder))
    {
        return (binder, body.clone());
    }
    let mut propositions = surrounding.to_vec();
    propositions.push(body.clone());
    let fresh = fresh_int32_variable_for_propositions(&propositions);
    let body =
        substitute_int32_variable_in_proposition(body, binder, Bitvector32Term::Variable(fresh));
    (fresh, body)
}

/// Planning evidence for certificate lowering: the guided instantiation
/// values the atomic prover would try for one universally quantified int32
/// fact against a target condition fact, plus every value of a
/// constant-bounded binder range. Simple check never calls this; the
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
        && let Ok(width) = usize::try_from(range.upper - range.lower + 1)
    {
        crate::instrumentation::record_deterministic_work(width);
        for value in range.lower..=range.upper {
            candidates.insert(signed_i64_bitvector_constant(value));
        }
    }
    candidates.into_iter().collect()
}

/// Returns only target-guided universal-instantiation values.
///
/// Unlike [`forall_instantiation_candidate_values`], this query does not
/// enumerate or solve the quantified body's finite range. Proof-object smart
/// search uses it while probing indexed universals so an irrelevant retained
/// range cannot trigger project-scale reasoning before a candidate is known
/// to match the focused atomic goal.
pub fn forall_guided_instantiation_candidate_values(
    quantified: &Proposition,
    target: &Proposition,
) -> Vec<Bitvector32Term> {
    let Proposition::ForAll { var, body, .. } = quantified else {
        return Vec::new();
    };
    match target {
        Proposition::ConditionIs(condition, _) => {
            PureFactContext::guided_forall_condition_candidates(*var, body, condition)
                .into_iter()
                .collect()
        }
        _ => Vec::new(),
    }
}

/// Chooses a variable identity absent from both the free variables and logical
/// binders of the supplied propositions.
pub fn fresh_int32_variable_for_propositions(propositions: &[Proposition]) -> Variable {
    let mut reserved = BTreeSet::new();
    for proposition in propositions {
        reserved.extend(proposition_variables(proposition));
    }
    KernelVariableGenerator::fresh_for(0, reserved).next()
}

/// Collects every free variable and logical binder identity in one
/// proposition. Proof facts retain this set incrementally so freshness checks
/// do not rebuild the entire ambient fact list for each universal intro.
pub(crate) fn proposition_variables(proposition: &Proposition) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_proposition_bitvector_variables(proposition, &mut variables);
    collect_proposition_bound_variables(proposition, &mut variables);
    variables
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
    let mut budget = ExecutionBudget::for_c_expression(&expression);
    let outcome = evaluate_c_expression(&state, &expression, &PureFactContext::new(), &mut budget)?;
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
    let mut budget = ExecutionBudget::for_c_expression(&condition);
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
    let budget = ExecutionBudget::for_c_statement(&statement);
    prove_symbolic_c_execution_with_budget(state, statement, assumptions, budget)
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
    let budget = ExecutionBudget::for_c_statement(&statement);
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
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
    let budget = ExecutionBudget::for_c_statement(&statement);
    prove_symbolic_c_execution_paths_with_budget(state, statement, assumptions, budget)
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
    let budget = ExecutionBudget::for_c_statement(&statement);
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
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
        .map(|mut path| {
            if let Some(memory) = statement_outcome_memory(&path.outcome) {
                path.facts.extend(
                    memory
                        .string_literal_loadable_facts()
                        .into_iter()
                        .map(ExecutionPureFact::certified),
                );
            }
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
    let mut budget = ExecutionBudget::for_c_statement_verification(&statement);
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        &mut budget,
    )
}

fn statement_kernel_variables(
    lower_bound: u64,
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
) -> KernelVariableGenerator {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing);
    collect_c_statement_bitvector_variables(statement, &mut existing);
    collect_assumption_variables(assumptions, &mut existing);
    KernelVariableGenerator::fresh_for_with_shared_reservations(
        lower_bound,
        existing,
        execution_environment_variable_index(environment),
    )
}

pub(crate) fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut variables = statement_kernel_variables(
        budget.next_kernel_variable,
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
    budget.next_kernel_variable = budget.next_kernel_variable.max(variables.next);
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
    let paths = paths
        .into_iter()
        .map(|mut path| {
            if let Some(memory) = statement_outcome_memory(&path.outcome) {
                path.facts.extend(
                    memory
                        .string_literal_loadable_facts()
                        .into_iter()
                        .map(ExecutionPureFact::certified),
                );
            }
            path
        })
        .collect();
    symbolic_c_statement_execution_with_loop_rule(state, statement, assumptions, paths)
}

fn statement_outcome_memory(outcome: &CStatementOutcome) -> Option<&CMemory> {
    match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state) => Some(state.memory()),
        CStatementOutcome::Return { state, .. } => Some(state.memory()),
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => None,
    }
}

#[cfg(test)]
pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases(
    state: CState,
    statement: CStatement,
    assumptions: PureFactContext,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: Vec<CLoopFinalExitCandidate>,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget = ExecutionBudget::for_c_statement_verification(&statement);
    prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
        state,
        statement,
        assumptions,
        environment,
        initialization_proven,
        preservation_proven,
        final_exit_candidates,
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
    final_exit_candidates: Vec<CLoopFinalExitCandidate>,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs,
        ranking_measures,
        body,
        do_while,
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
    let mut variables = statement_kernel_variables(
        budget.next_kernel_variable,
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
        resource_specs,
        ranking_measures,
        body,
        &assumptions,
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        initialization_proven,
        preservation_proven,
        &final_exit_candidates,
        budget,
        &mut variables,
        *do_while,
    );
    budget.next_kernel_variable = budget.next_kernel_variable.max(variables.next);
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
        loop_index: None,
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
    let budget = ExecutionBudget::for_c_function(&function, &arguments);
    prove_symbolic_c_function_execution_with_budget(state, function, arguments, assumptions, budget)
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
    let budget = ExecutionBudget::for_c_function(&function, &arguments);
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
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
    let budget = ExecutionBudget::for_c_function(&function, &arguments);
    prove_symbolic_c_function_execution_paths_with_budget(
        state,
        function,
        arguments,
        assumptions,
        budget,
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
    let budget = ExecutionBudget::for_c_function(&function, &arguments);
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
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
    let budget = ExecutionBudget::for_c_function_verification(&function, &arguments);
    prove_symbolic_c_function_verification_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
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
/// Unlike ordinary proof execution, this canonicalizes composite requirements
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
    let budget = ExecutionBudget::for_c_function_verification(&function, &arguments);
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        true,
    )
}

/// Executes one whole-function judgment and retains its exact authority inputs
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
                ExecutionBudget::for_c_function_verification(&function, &arguments),
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
                ExecutionBudget::for_c_function(&function, &arguments),
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
        entry_representation_origin: None,
        checked_call_events: Default::default(),
    }
}

pub(in crate::kernel) fn proof_evidence_conclusion(theorem: &Theorem) -> &Proposition {
    let mut conclusion = theorem.proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    conclusion
}

pub(in crate::kernel) fn proof_evidence_assumptions(
    theorem: &Theorem,
    base: &PureFactContext,
) -> PureFactContext {
    let mut assumptions = base.clone();
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        assumptions = assumptions.assume_proposition(premise.as_ref().clone());
        proposition = body;
    }
    assumptions
}

/// Whether `premise` is `fact` or one of its conjuncts. Conjunction
/// elimination is the one structural rule the proof object applies to retained
/// facts: a kernel theorem lists the context it executed under as atomic
/// condition facts, while a loop step retains the lowered invariant it
/// assumed as one conjunction, so `And(a, b)` retained is `a` retained.
fn retained_fact_contains(fact: &Proposition, premise: &Proposition) -> bool {
    fact == premise
        || matches!(
            fact,
            Proposition::And(left, right)
                if retained_fact_contains(left, premise) || retained_fact_contains(right, premise)
        )
}

/// The first premise of a retained transition theorem that is not retained,
/// if any. A premise is retained when it is an
/// exact fact of the entry context, of the context the theorem was proved
/// under (`CheckedExecutionEvent::Context`), of the candidate path, an
/// obligation, or a resource-certified loadability. A loadability premise
/// may also be covered by a loadability fact of the retained context over a
/// wider range of the same block (a callee's requirement inside the caller's
/// `loadable(p[0..n])`), which is the one range rule the executor
/// discharged it with. Nothing else is derived.
pub(in crate::kernel) fn proof_evidence_unretained_premise(
    theorem: &Theorem,
    assumptions: &PureFactContext,
    executed_under: Option<&PureFactContext>,
    execution_facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
    state: &CState,
    function_entry_resource_facts: Option<&PureFactContext>,
) -> Option<Proposition> {
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        if !(assumptions.proves_exact(premise)
            || executed_under.is_some_and(|context| context.proves_exact(premise))
            || execution_facts
                .iter()
                .any(|fact| retained_fact_contains(fact.proposition(), premise))
            || obligations
                .iter()
                .any(|obligation| obligation.proposition() == premise.as_ref())
            || resources_certify_loadability(state, state.resources(), premise, assumptions)
            || (matches!(premise.as_ref(), Proposition::CMemoryLoadable { .. })
                && executed_under
                    .is_some_and(|context| loadable_covered_by_fact(context, premise)))
            || (matches!(
                premise.as_ref(),
                Proposition::CResourceContains { .. } | Proposition::CResourceSeparate { .. }
            ) && function_entry_resource_facts
                .is_some_and(|facts| facts.proves_exact(premise))))
        {
            return Some(premise.as_ref().clone());
        }
        proposition = body;
    }
    None
}

pub(crate) fn execution_evidence_states_match(
    function: &CFunction,
    left: &CState,
    right: &CState,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let mut left_without_ghost_difference = left.clone();
    left_without_ghost_difference.resources = right.resources.clone();
    left_without_ghost_difference.counted_populations = right.counted_populations.clone();
    left_without_ghost_difference == *right
        && contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            left.memory(),
            left.resources(),
            right.memory(),
            right.resources(),
            assumptions,
        )
        && counted_populations_definitionally_equal(
            left,
            right,
            function.composite_resource_definitions(),
            assumptions,
        )
}

/// Checks the representation-only state change permitted before the first C
/// operation. Resource scopes may materialize otherwise unchanged symbolic
/// loads, but cannot alter locals, local-object cells, heap lifetime state,
/// resource meaning, or population counts.
pub(crate) fn function_entry_representation_states_match(
    function: &CFunction,
    left: &CState,
    right: &CState,
    assumptions: &PureFactContext,
) -> bool {
    left.locals == right.locals
        && left.memory.heap == right.memory.heap
        && left.local_cell_values().eq(right.local_cell_values())
        && c_memories_definitionally_equal(left.memory(), right.memory(), assumptions)
        && contract_certification::resource_contexts_definitionally_equal_with_definitions(
            function.composite_resource_definitions(),
            left.memory(),
            left.resources(),
            right.memory(),
            right.resources(),
            assumptions,
        )
        && counted_populations_definitionally_equal(
            left,
            right,
            function.composite_resource_definitions(),
            assumptions,
        )
}

pub(in crate::kernel) fn proof_evidence_function_refines_same_source(
    original: &CFunction,
    checked: &CFunction,
) -> bool {
    original.return_type() == checked.return_type()
        && original.name() == checked.name()
        && original.parameters() == checked.parameters()
        && original.source_body() == checked.source_body()
        && original.resource_requires() == checked.resource_requires()
        && original.resource_ensures() == checked.resource_ensures()
        && original.resource_constructors() == checked.resource_constructors()
        && original.contract_requires() == checked.contract_requires()
        && original.contract_ensures() == checked.contract_ensures()
        && original.contract_mutable() == checked.contract_mutable()
        && original.contract_effect_claim_required() == checked.contract_effect_claim_required()
        && original.contract_claims() == checked.contract_claims()
        && original.opaque_contract_supported() == checked.opaque_contract_supported()
        && original.composite_resource_definitions() == checked.composite_resource_definitions()
        && original.predicate_unfoldings() == checked.predicate_unfoldings()
}

pub(in crate::kernel) fn proof_evidence_initial_state(
    events: &[crate::kernel::proof::CheckedExecutionEvent],
) -> Option<&CState> {
    use crate::kernel::proof::CheckedExecutionEvent;

    events.iter().find_map(|event| match event {
        CheckedExecutionEvent::ProofCase(_)
        | CheckedExecutionEvent::Context(_)
        | CheckedExecutionEvent::Call(_) => None,
        CheckedExecutionEvent::ResourceObservation(observation) => Some(observation.before_state()),
        CheckedExecutionEvent::ResourceRewrite(rewrite) => Some(rewrite.before_state()),
        CheckedExecutionEvent::Statement(theorem) | CheckedExecutionEvent::Condition(theorem) => {
            match proof_evidence_conclusion(theorem) {
                Proposition::CStatementVerifies { state, .. }
                | Proposition::CConditionEvaluates { state, .. } => Some(state),
                _ => None,
            }
        }
        CheckedExecutionEvent::Branch(branch) => Some(branch.start_state()),
    })
}

/// Every proof-case arm in the traces must be valid, a path may pass
/// through one partition once, and every constructor must be represented
/// by a retained trace or a kernel-checked contradiction in its partition.
/// The arms' own facts are what the
/// proof object assumes on each path; no restatement of the cases from outside
/// the traces is consulted.
pub(in crate::kernel) fn proof_case_partitions_are_exhaustive(
    evidence: &[crate::kernel::proof::PersistentSequence<
        crate::kernel::proof::CheckedExecutionEvent,
    >],
) -> bool {
    use crate::kernel::proof::CheckedExecutionEvent;

    fn collect(
        events: &[CheckedExecutionEvent],
        covered: &mut std::collections::BTreeMap<usize, Vec<bool>>,
        path_partitions: &mut std::collections::BTreeSet<usize>,
    ) -> bool {
        for event in events {
            match event {
                CheckedExecutionEvent::ProofCase(arm) => {
                    if !arm.is_valid() || !path_partitions.insert(arm.identity()) {
                        return false;
                    }
                    covered
                        .entry(arm.identity())
                        .or_insert_with(|| arm.excluded_cases())[arm.arm_index()] = true;
                }
                CheckedExecutionEvent::Branch(branch) => {
                    for arm_index in 0..2 {
                        let mut nested_partitions = std::collections::BTreeSet::new();
                        if !collect(
                            branch.arm_events(arm_index),
                            covered,
                            &mut nested_partitions,
                        ) {
                            return false;
                        }
                    }
                }
                CheckedExecutionEvent::Statement(_)
                | CheckedExecutionEvent::Call(_)
                | CheckedExecutionEvent::Condition(_)
                | CheckedExecutionEvent::Context(_)
                | CheckedExecutionEvent::ResourceObservation(_)
                | CheckedExecutionEvent::ResourceRewrite(_) => {}
            }
        }
        true
    }

    let mut covered = std::collections::BTreeMap::new();
    for trace in evidence {
        let mut path_partitions = std::collections::BTreeSet::new();
        if !collect(&trace.to_vec(), &mut covered, &mut path_partitions) {
            return false;
        }
    }
    covered
        .values()
        .all(|arms| !arms.is_empty() && arms.iter().all(|covered| *covered))
}

#[cfg(test)]
mod proof_case_evidence_tests {
    use super::*;
    use crate::kernel::proof::{
        CheckedProofCasePartition, ExecutionFrontier, ExecutionProofCore, OutcomeEvidenceFork,
        ProofFacts,
    };

    fn case_partition(
        root: &ProofFacts,
    ) -> (Arc<CheckedProofCasePartition>, Proposition, Proposition) {
        let then_fact = Proposition::Predicate {
            name: "case".to_string(),
            arguments: Vec::new(),
        };
        let else_fact = Proposition::Not(Box::new(then_fact.clone()));
        let partition =
            CheckedProofCasePartition::check(root, then_fact.clone(), else_fact.clone())
                .expect("complementary facts should create a checked partition");
        (partition, then_fact, else_fact)
    }

    #[test]
    fn proof_case_family_requires_both_arms_once_per_path() {
        let root = ProofFacts::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut then_core =
            ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        assert!(then_core.record_proof_case_arm(
            partition.clone(),
            0,
            root.with_fact(then_fact.clone())
        ));
        let mut else_core =
            ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        assert!(else_core.record_proof_case_arm(partition.clone(), 1, root.with_fact(else_fact)));
        let evidence = vec![
            then_core.execution_evidence[0].clone(),
            else_core.execution_evidence[0].clone(),
        ];

        assert!(proof_case_partitions_are_exhaustive(&evidence));
        // One arm alone does not exhaust the partition.
        assert!(!proof_case_partitions_are_exhaustive(&evidence[..1]));
        // A path may pass through a partition once.
        let mut duplicate_then_core = then_core.clone();
        assert!(
            duplicate_then_core.record_proof_case_arm(partition, 0, root.with_fact(then_fact),)
        );
        assert!(!proof_case_partitions_are_exhaustive(&[
            duplicate_then_core.execution_evidence[0].clone(),
            else_core.execution_evidence[0].clone(),
        ]));
    }

    #[test]
    fn outcome_evidence_fork_splits_traces_in_candidate_order() {
        let root = ProofFacts::default();
        let (partition, then_fact, else_fact) = case_partition(&root);
        let mut core = ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        // Two candidate paths with one trace each; the second is forked.
        let function = c_function(
            CType::Int32,
            "fork",
            Vec::new(),
            c_return(c_int32_literal(0)),
        );
        let entry_state =
            c_function_entry_state(&CState::new(), &function, &[]).expect("entry state");
        let skip_return = |value: u32| {
            Theorem::new(Proposition::CStatementVerifies {
                state: entry_state.clone(),
                statement: CStatement::Skip,
                outcome: CStatementOutcome::Return {
                    value: int32(value),
                    state: entry_state.clone(),
                },
            })
        };
        core.record_statement_outcomes(
            &function,
            &[],
            &[
                (skip_return(0), &[][..], &[][..]),
                (skip_return(1), &[][..], &[][..]),
            ],
            PureFactContext::new(),
        )
        .expect("skip outcomes advance the entry frontier");
        assert_eq!(core.execution_evidence.len(), 2);

        // A plan must cover every trace.
        assert!(
            core.fork_outcome_evidence(&[OutcomeEvidenceFork::Keep])
                .is_err()
        );
        // Arm facts must extend the root by exactly the arm's case fact.
        assert!(
            core.fork_outcome_evidence(&[
                OutcomeEvidenceFork::Keep,
                OutcomeEvidenceFork::Split {
                    partition: partition.clone(),
                    arm_facts: [
                        root.with_fact(else_fact.clone()),
                        root.with_fact(then_fact.clone())
                    ],
                },
            ])
            .is_err()
        );
        core.fork_outcome_evidence(&[
            OutcomeEvidenceFork::Keep,
            OutcomeEvidenceFork::Split {
                partition: partition.clone(),
                arm_facts: [root.with_fact(then_fact), root.with_fact(else_fact)],
            },
        ])
        .expect("a well-formed plan forks the second trace");
        assert_eq!(core.execution_evidence.len(), 3);
        assert_eq!(core.execution_evidence[0].len(), 2);
        assert_eq!(core.execution_evidence[1].len(), 3);
        assert_eq!(core.execution_evidence[2].len(), 3);
        assert!(proof_case_partitions_are_exhaustive(
            &core.execution_evidence.to_vec()
        ));
        // The forked traces share the original's prefix.
        assert!(
            core.execution_evidence[1]
                .suffix_since(&core.execution_evidence[0])
                .is_none()
        );
    }

    #[test]
    fn nested_outcome_evidence_is_exhaustive_and_rejects_corrupt_inner_arms() {
        let root = ProofFacts::default();
        let (outer, positive, negative) = case_partition(&root);
        let outer_facts = [root.with_fact(positive), root.with_fact(negative)];
        let inner_positive = Proposition::Predicate {
            name: "inner".into(),
            arguments: Vec::new(),
        };
        let inner_negative = Proposition::Not(Box::new(inner_positive.clone()));
        let inner = CheckedProofCasePartition::check(
            &outer_facts[0],
            inner_positive.clone(),
            inner_negative.clone(),
        )
        .unwrap();
        let inner_facts = [
            outer_facts[0].with_fact(inner_positive),
            outer_facts[0].with_fact(inner_negative),
        ];
        let plan = |corrupt| OutcomeEvidenceFork::NestedSplit {
            partition: outer.clone(),
            arm_facts: outer_facts.clone(),
            arms: [
                Box::new(OutcomeEvidenceFork::Split {
                    partition: inner.clone(),
                    arm_facts: if corrupt {
                        [inner_facts[1].clone(), inner_facts[0].clone()]
                    } else {
                        inner_facts.clone()
                    },
                }),
                Box::new(OutcomeEvidenceFork::Keep),
            ],
        };
        let mut core = ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        assert!(core.fork_outcome_evidence(&[plan(true)]).is_err());
        assert_eq!(
            core.execution_evidence.len(),
            1,
            "a rejected tree changes nothing"
        );
        core.fork_outcome_evidence(&[plan(false)]).unwrap();
        assert_eq!(core.execution_evidence.len(), 3);
        assert_eq!(
            core.execution_evidence
                .iter()
                .map(|trace| trace.len())
                .collect::<Vec<_>>(),
            [2, 2, 1]
        );
        let traces = core.execution_evidence.to_vec();
        assert!(proof_case_partitions_are_exhaustive(&traces));
        assert!(
            !proof_case_partitions_are_exhaustive(&traces[1..]),
            "losing an inner arm is not exhaustive"
        );
    }
}

/// Reports whether an exact pure-fact context is contradictory.
///
/// Proof orchestration uses this before treating a derived contradiction as
/// path-exclusion evidence: explosion in an already-inconsistent context is
/// not proof that a sibling branch owns the path.
pub fn pure_fact_context_is_inconsistent(assumptions: &PureFactContext) -> bool {
    assumptions.is_inconsistent()
}

/// Reifies one exact context fact as the explicit identity implication
/// `fact -> fact`. This is intentionally not a general proposition prover:
/// callers that want a derived resource invariant must plan and record that
/// derivation before asking the kernel to issue theorem authority.
fn theorem_from_exact_context_fact(
    assumptions: &PureFactContext,
    conclusion: Proposition,
) -> Option<Theorem> {
    if !assumptions.proves_exact(&conclusion) {
        return None;
    }
    let proposition = Proposition::Implies(Box::new(conclusion.clone()), Box::new(conclusion));
    Some(Theorem::new(proposition))
}

/// Certifies the exact count lower bound witnessed by owned declared-resource
/// authority in a concrete ghost state. The returned theorem is bound to the
/// proposition reconstructed here and retains its contextual proof premises;
/// callers cannot use resource possession to bless an unrelated arithmetic
/// fact.
pub fn prove_owned_resource_count_lower_bound(
    state: &CState,
    owned: &CResourceFact,
    claimed: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    if !state.resources().satisfies_fact(owned, assumptions) {
        return None;
    }
    let quantity = owned.owned_quantity_term()?.clone();
    let (name, arguments) = match owned.resource() {
        CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
            (name, arguments)
        }
        CResource::Memory(_) | CResource::Instance(_) => return None,
    };
    let count = match state.counted_population(name, arguments) {
        Some(count) => count.clone(),
        None => {
            let zero = Bitvector32Term::Constant(0);
            let quantity_is_zero = quantity == zero
                || certification_proves_proposition(
                    assumptions,
                    &Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(quantity.clone()),
                            Box::new(zero.clone()),
                        ),
                        true,
                    ),
                );
            if !quantity_is_zero {
                return None;
            }
            zero
        }
    };
    let conclusion =
        Proposition::ConditionIs(ConditionTerm::signed_less_equal(quantity, count), true);
    if claimed != &conclusion {
        return None;
    }
    theorem_from_exact_context_fact(assumptions, conclusion)
}

/// Certifies the nonnegativity invariant carried by an owned declared-resource
/// coefficient in a concrete ghost state.
pub fn prove_owned_resource_quantity_nonnegative(
    state: &CState,
    owned: &CResourceFact,
    claimed: &Proposition,
    assumptions: &PureFactContext,
) -> Option<Theorem> {
    if !state.resources().satisfies_fact(owned, assumptions) {
        return None;
    }
    let quantity = owned.owned_quantity_term()?.clone();
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), quantity),
        true,
    );
    if claimed != &conclusion {
        return None;
    }
    theorem_from_exact_context_fact(assumptions, conclusion)
}

/// Re-expresses a checked execution from a definitionally equal ghost-resource
/// representation of the same concrete entry state.
///
/// Resource folds, unfolds, and observations can leave the proof state with a
/// different `ResourceContext` than independently reconstructed contract
/// entry. The program locals, memory, and counted populations must still be
/// exactly identical, and the kernel's bounded resource equality relation
/// must prove the two ghost representations equivalent before any execution
/// theorem is rebuilt at the contract entry state.
/// A short, dump-free description of an artifact premise for a certification
/// diagnostic.
fn describe_contract_reuse_premise(premise: &Proposition) -> String {
    fn resource_name(resource: &CResource) -> &str {
        match resource {
            CResource::Composite { name, .. } | CResource::Token { name, .. } => name,
            CResource::Memory(_) => "memory",
            CResource::Instance(instance) => instance.name(),
        }
    }
    match premise {
        Proposition::Predicate { name, .. } => format!("the predicate identity `{name}`"),
        Proposition::CResourceContains { parent, .. } => {
            format!(
                "a containment fact under resource `{}`",
                resource_name(parent)
            )
        }
        Proposition::CResourceSeparate { left, right } => format!(
            "a separation fact between `{}` and `{}`",
            resource_name(left),
            resource_name(right)
        ),
        Proposition::ConditionIs(..) | Proposition::Not(_) => "a condition fact".to_string(),
        _ => "a pure fact".to_string(),
    }
}

fn checked_execution_at_definitionally_equal_entry_state(
    checked: &CCheckedFunctionExecution,
    state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> Option<SymbolicCExecution> {
    // An artifact completed through a kernel-issued `CheckedFunctionEntry`
    // records the contract caller state it was tied to, and the proof object
    // already checked that its entry representation is definitionally equal
    // to the entry derived from that state. No second equivalence search is
    // needed for it.
    let entry_origin_matches = checked.entry_representation_origin.as_ref() == Some(state);
    if !entry_origin_matches {
        // Recursive composites can expose an unbounded proof relation between
        // folded and projected entry contexts. Certification must not turn a
        // cache probe into that search: without a kernel-issued entry tying
        // the artifact to this state, decline.
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
        if checked_without_ghost_difference != *state {
            return None;
        }
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
        if !resources_match || !populations_match {
            return None;
        }
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

pub(crate) fn counted_populations_definitionally_equal(
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
                    population.arguments.as_ref(),
                    population.family_observation_marker,
                ),
                &population.count,
            )
        })
        .collect::<BTreeMap<_, _>>();
    left_populations.into_iter().all(|population| {
        let identity = (
            population.name.as_str(),
            population.arguments.as_ref(),
            population.family_observation_marker,
        );
        right_by_identity.get(&identity).is_some_and(|right_count| {
            let exact = population.count == **right_count;
            let proved = certification_proves_proposition(
                assumptions,
                &Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(population.count.clone()),
                        Box::new((*right_count).clone()),
                    ),
                    true,
                ),
            );
            exact || proved
        })
    })
}

/// Certifies an opaque contract from kernel-checked whole-function
/// executions: an artifact is reused when its retained authority is implied
/// by the exact contract entry. Certification never executes the body
/// itself; with no reusable artifact it produces no paths and the reason.
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
    let base_assumptions = match crate::instrumentation::measure_operation(
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
                &pure_theorem_facts,
            )
        },
    ) {
        Ok(assumptions) => assumptions,
        Err(reason) => {
            if crate::instrumentation::enabled() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::Diagnostic(format!(
                        "exact certification could not construct contract assumptions for {}: {reason}",
                        function.name()
                    )),
                );
            }
            return CFunctionContractExecution::failed(reason);
        }
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
        return CFunctionContractExecution::failed(
            "could not enumerate the undecided resource guards of the contract entry".to_string(),
        );
    };
    let mut cases = Vec::new();
    let mut reuse_diagnostic = None;
    for case_facts in resource_condition_cases {
        let case_seed = assumptions_with_propositions(&PureFactContext::new(), &case_facts);
        let mut assumptions = match crate::instrumentation::measure_operation(
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
                    &pure_theorem_facts,
                )
            },
        ) {
            Ok(assumptions) => assumptions,
            Err(reason) => {
                if crate::instrumentation::enabled() {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::Diagnostic(format!(
                            "exact certification rejected a resource-guard case for {}: {reason}",
                            function.name()
                        )),
                    );
                }
                return CFunctionContractExecution::failed(format!(
                    "in one resource-guard case of the contract entry, {reason}"
                ));
            }
        };
        let Some(mut entry_state) = c_function_entry_state(&state, &function, &arguments) else {
            return CFunctionContractExecution::failed(
                "could not build the contract entry state from the call arguments".to_string(),
            );
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
                return CFunctionContractExecution::failed(
                    "could not expand the composite resources of the contract entry state"
                        .to_string(),
                );
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
                            && (pure_theorem_facts.contains(fact)
                                || crate::instrumentation::measure_operation(
                                    function.name(),
                                    "contract certification",
                                    "derived forall context-free check",
                                    || certification_proves_context_free_forall(fact),
                                ));
                        let theorem_predicate_certified = !resource_certified
                            && !context_free_certified
                            && certification_proves_predicate_from_verified_pure_implications(
                                &derived_assumptions,
                                &pure_theorem_facts,
                                fact,
                            );
                        let proposition_certified = !resource_certified
                            && !context_free_certified
                            && !theorem_predicate_certified
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
                                if context_free_certified
                                    || theorem_predicate_certified
                                    || proposition_certified
                                {
                                    "derived proposition result: proved"
                                } else {
                                    "derived proposition result: unproved"
                                },
                                || (),
                            );
                        }
                        if resource_certified
                            || context_free_certified
                            || theorem_predicate_certified
                            || proposition_certified
                        {
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
                if certification_proves_predicate_from_verified_pure_implications(
                    &assumptions,
                    &pure_theorem_facts,
                    fact,
                ) {
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
        // Contract requirements are lowered to their bodies, while a claim
        // proof may assume the registered predicate identity itself. Each
        // registered unfolding is definitional, so an identity whose
        // instantiated body and side obligations the contract context proves
        // is a renaming of an assumption the context already holds.
        let raw_entry_state = c_function_entry_state(&state, &function, &arguments);
        let mut reuse_assumptions = assumptions.clone();
        if let Some(raw_entry_state) = raw_entry_state.as_ref() {
            let mut budget = ExecutionBudget::default();
            for unfolding in function.predicate_unfoldings() {
                let Some((predicate, body)) =
                    contract_certification::instantiate_contract_predicate_unfolding(
                        raw_entry_state,
                        unfolding,
                        &assumptions,
                        &mut budget,
                    )
                else {
                    continue;
                };
                if certification_proves_proposition(&assumptions, &body) {
                    reuse_assumptions = reuse_assumptions.assume_proposition(predicate);
                }
            }
        }
        // A claim proof opens entry composites and assumes the containment
        // and separation facts of their children. Derive those facts from the
        // kernel definitions at the contract entry state, expanding only the
        // composites some artifact premise names, so the work is bounded by
        // the premises rather than by the resource depth.
        {
            let definitions = function.composite_resource_definitions();
            let mut composites = Vec::new();
            for fact in raw_entry_state
                .iter()
                .flat_map(|raw| raw.resources().facts().iter())
                .chain(entry_state.resources().facts().iter())
            {
                // Containment is definitional: it depends on the composite's
                // body at the entry memory, not on whether the contract owns
                // or views it, so evaluate every composite as owned.
                if matches!(fact.resource(), CResource::Composite { .. }) {
                    let owned = CResourceFact::own(fact.resource().clone());
                    if !composites.contains(&owned) {
                        composites.push(owned);
                    }
                }
            }
            let mut expanded = std::collections::BTreeSet::new();
            loop {
                let named = checked_artifacts
                    .iter()
                    .filter(|checked| matches_execution_metadata_except_state(checked))
                    .flat_map(|checked| checked.assumptions.pure_facts())
                    .filter(|premise| {
                        matches!(
                            premise,
                            Proposition::CResourceContains { .. }
                                | Proposition::CResourceSeparate { .. }
                        ) && !certification_proves_proposition(&reuse_assumptions, premise)
                    })
                    .flat_map(|premise| match premise {
                        Proposition::CResourceContains { parent, .. } => vec![parent],
                        Proposition::CResourceSeparate { left, right } => vec![left, right],
                        _ => Vec::new(),
                    })
                    .filter(|resource| {
                        matches!(resource, CResource::Composite { .. })
                            && !expanded.contains(resource)
                    })
                    .collect::<std::collections::BTreeSet<_>>();
                let wanted = named
                    .into_iter()
                    .filter_map(|resource| {
                        composites
                            .iter()
                            .find(|fact| fact.resource() == &resource)
                            .cloned()
                    })
                    .collect::<Vec<_>>();
                if wanted.is_empty() {
                    break;
                }
                for composite in wanted {
                    expanded.insert(composite.resource().clone());
                    let Some(propositions) =
                        crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                            &composite,
                            definitions,
                            entry_state.memory(),
                            &reuse_assumptions,
                        )
                    else {
                        continue;
                    };
                    for proposition in propositions {
                        if let Proposition::CResourceContains { child, .. } = &proposition
                            && matches!(child, CResource::Composite { .. })
                        {
                            composites.push(CResourceFact::own(child.clone()));
                        }
                        reuse_assumptions = reuse_assumptions.assume_proposition(proposition);
                    }
                }
            }
        }
        let checked_premise_is_authorized =
            |_checked: &CCheckedFunctionExecution, premise: &Proposition| {
                certification_proves_proposition(&reuse_assumptions, premise)
            };
        let authorized = |checked: &CCheckedFunctionExecution| {
            checked
                .assumptions
                .pure_facts()
                .into_iter()
                .all(|premise| checked_premise_is_authorized(checked, &premise))
        };
        let candidates = checked_artifacts
            .iter()
            .filter(|checked| matches_execution_metadata_except_state(checked))
            .collect::<Vec<_>>();
        // Every checked execution reusable at this entry is one path set the
        // claims may be judged over. Proofs of one function structure their
        // paths differently (a proof that joins two arms publishes the
        // joined path; another publishes each arm) and may run at different
        // representations of the entry (one observed a resource first), and
        // a claim completed on one proof's outcome is matched against that
        // proof's paths. An artifact at the contract's exact entry state is
        // taken as is; one at another representation is rebased onto this
        // entry, which pays the definitional equivalence check only for it.
        let mut alternatives: Vec<CContractPathSet> = crate::instrumentation::measure_operation(
            function.name(),
            "contract certification",
            "contract checked body reuse",
            || {
                candidates
                    .iter()
                    .filter(|checked| checked.state == state && authorized(checked))
                    .map(|checked| CContractPathSet {
                        paths: checked.execution.paths.clone(),
                        completion_origin_state: Some(checked.state.clone()),
                    })
                    .collect()
            },
        );
        alternatives.extend(crate::instrumentation::measure_operation(
            function.name(),
            "contract certification",
            "contract checked body resource-rebased reuse",
            || {
                candidates
                    .iter()
                    .filter(|checked| checked.state != state && authorized(checked))
                    .filter_map(|checked| {
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
                        .map(|execution| CContractPathSet {
                            paths: execution.paths,
                            completion_origin_state: Some(checked.state.clone()),
                        })
                    })
                    .collect::<Vec<_>>()
            },
        ));
        if alternatives.is_empty() {
            // Two artifacts whose single unauthorized entry premises are one
            // condition and its negation together cover the entry: their
            // paths form one path set.
            let partition_reuse = || -> Option<CContractPathSet> {
                let partitioned = candidates
                    .iter()
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
                        Some((*checked, condition, value))
                    })
                    .collect::<Vec<_>>();
                for (left_index, (left, left_condition, left_value)) in
                    partitioned.iter().enumerate()
                {
                    let Some((right, _, _)) = partitioned[left_index + 1..].iter().find(
                        |(_, right_condition, right_value)| {
                            right_condition == left_condition && right_value != left_value
                        },
                    ) else {
                        continue;
                    };
                    let origin = (left.state == right.state).then(|| left.state.clone());
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
                    return Some(CContractPathSet {
                        paths,
                        completion_origin_state: origin,
                    });
                }
                None
            };
            alternatives.extend(crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract checked body partition reuse",
                partition_reuse,
            ));
        }
        let reused = !alternatives.is_empty();
        if !reused {
            // Certification never executes the body: reuse either applies
            // or the caller gets no paths and the reason.
            let mut cause = ContractFallback::NoMatchingArtifact;
            let mut detail = format!(
                "no checked execution of `{}` matched the contract's execution mode",
                function.name()
            );
            for checked in &candidates {
                if checked.state != state {
                    if cause == ContractFallback::NoMatchingArtifact {
                        cause = ContractFallback::EntryStateDelta;
                        detail = format!(
                            "the checked execution of `{}` started at a different entry state than the contract and could not be rebased onto it",
                            function.name()
                        );
                    }
                    continue;
                }
                let unauthorized = checked
                    .assumptions
                    .pure_facts()
                    .into_iter()
                    .find(|premise| !checked_premise_is_authorized(checked, premise));
                cause = match &unauthorized {
                    Some(Proposition::Predicate { .. }) => {
                        ContractFallback::UnauthorizedPredicatePremise
                    }
                    Some(
                        Proposition::CResourceContains { .. }
                        | Proposition::CResourceSeparate { .. },
                    ) => ContractFallback::UnauthorizedResourcePremise,
                    Some(_) | None => ContractFallback::UnauthorizedPremise,
                };
                detail = match &unauthorized {
                    Some(premise) => format!(
                        "the checked execution of `{}` assumed {} at entry, which the contract context cannot derive",
                        function.name(),
                        describe_contract_reuse_premise(premise)
                    ),
                    None => format!(
                        "the checked execution of `{}` could not be reused at the contract entry",
                        function.name()
                    ),
                };
                break;
            }
            crate::instrumentation::record_contract_fallback(cause);
            crate::instrumentation::measure_operation(
                function.name(),
                "contract certification",
                "contract checked body unavailable",
                || (),
            );
            reuse_diagnostic = Some(detail);
        }
        for set in &mut alternatives {
            // A reused path carries the proof's own entry premises. Every one
            // of them was just authorized from the reconstructed contract
            // context, so the context itself, with the predicate identities
            // and relation facts derived above, is a sound entry context for
            // the path and is what claim certification needs to see:
            // requirement bodies and derived entry facts the proof never
            // spelled out.
            if reused {
                for path in &mut set.paths {
                    let entry_premises = path.assumptions.pure_facts();
                    path.facts
                        .retain(|fact| !entry_premises.contains(fact.proposition()));
                    path.assumptions = reuse_assumptions.clone();
                }
            }
            for path in &mut set.paths {
                let mut certification_assumptions = path.assumptions.clone();
                for obligation in &path.obligations {
                    let Proposition::ConditionIs(condition, value) = obligation.proposition()
                    else {
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
        }
        cases.push(alternatives);
    }
    let mut checked_call_events = crate::kernel::proof::CheckedCallEvents::default();
    for artifact in checked_artifacts {
        checked_call_events.extend(&artifact.checked_call_events);
    }
    CFunctionContractExecution {
        cases,
        reuse_diagnostic,
        checked_call_events,
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

/// A signed int32 value strictly below another value's successor is no
/// greater than that value. This remains valid when the successor wraps:
/// then the strict premise is unsatisfiable.
pub fn prove_int32_lt_successor_implies_le(
    value: Bitvector32Term,
    upper: Bitvector32Term,
) -> Theorem {
    let successor = Bitvector32Term::add(upper.clone(), Bitvector32Term::Constant(1));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(value.clone(), successor),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::signed_less_equal(value, upper), true);
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
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
    let not_lt_premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
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
    let not_gt_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(left.clone(), right.clone()),
        false,
    );
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

/// Strict signed int32 order implies disequality.
pub fn prove_int32_lt_implies_neq(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        false,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// The negation of signed strict order implies the reverse non-strict order.
pub fn prove_int32_not_lt_implies_ge(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(left.clone(), right.clone()),
        false,
    );
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

/// The empty Integer fold law, guarded by the endpoint ordering.
pub fn prove_integer_range_fold_empty(
    index: IntegerRangeFoldIndex,
    initial: IntegerTerm,
    accumulator: Variable,
    item: Variable,
    body: IntegerTerm,
) -> Theorem {
    let guard = match &index {
        IntegerRangeFoldIndex::Int32 { start, end } => {
            ConditionTerm::signed_less_equal(end.value().clone(), start.value().clone())
        }
        IntegerRangeFoldIndex::Integer { start, end } => {
            ConditionTerm::integer_less_equal(end.as_ref().clone(), start.as_ref().clone())
        }
    };
    let fold = IntegerTerm::range_fold(index, initial.clone(), accumulator, item, body);
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(guard, true)),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(fold.into(), initial.into()),
            true,
        )),
    ))
}

/// The append-one Integer fold law.  The Int32 carrier includes the checked
/// increment premise; neither carrier is expanded over the range.
pub fn prove_integer_range_fold_append(
    index: IntegerRangeFoldIndex,
    initial: IntegerTerm,
    accumulator: Variable,
    item: Variable,
    body: IntegerTerm,
) -> Option<Theorem> {
    if matches!(&index, IntegerRangeFoldIndex::Integer { .. }) && accumulator == item {
        return None;
    }
    let (extended, guard, item_value) = match &index {
        IntegerRangeFoldIndex::Int32 { start, end } => {
            let original_end = end.value().clone();
            let increment =
                Bitvector32Term::add(original_end.clone(), Bitvector32Term::Constant(1));
            let guard =
                ConditionTerm::signed_less_equal(start.value().clone(), end.value().clone());
            let safe = ConditionTerm::signed_less_than(
                end.value().clone(),
                Bitvector32Term::Constant(i32::MAX as u32),
            );
            let extended = IntegerRangeFoldIndex::Int32 {
                start: start.clone(),
                end: SharedIntegerRangeEndpoint::intern(increment),
            };
            let item_value = IntegerTerm::from_machine(MachineIntegerType::Int32, original_end)?;
            (
                extended,
                Proposition::And(
                    Box::new(Proposition::ConditionIs(guard, true)),
                    Box::new(Proposition::ConditionIs(safe, true)),
                ),
                item_value,
            )
        }
        IntegerRangeFoldIndex::Integer { start, end } => {
            let increment = IntegerTerm::add(end.as_ref().clone(), IntegerTerm::constant_i64(1));
            let guard =
                ConditionTerm::integer_less_equal(start.as_ref().clone(), end.as_ref().clone());
            let extended = IntegerRangeFoldIndex::Integer {
                start: start.clone(),
                end: increment.into(),
            };
            (
                extended,
                Proposition::ConditionIs(guard, true),
                end.as_ref().clone(),
            )
        }
    };
    let original_initial = initial.clone();
    let c_item = matches!(&index, IntegerRangeFoldIndex::Int32 { .. });
    let prior = IntegerTerm::range_fold(index, initial, accumulator, item, body.clone());
    let stepped = crate::kernel::reasoning::instantiate_integer_range_fold_step(
        &body,
        accumulator,
        &prior,
        item,
        &item_value,
        c_item,
    )
    .ok()?;
    let extended_fold =
        IntegerTerm::range_fold(extended, original_initial, accumulator, item, body);
    Some(Theorem::new(Proposition::Implies(
        Box::new(guard),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(extended_fold.into(), stepped.into()),
            true,
        )),
    )))
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

/// Universally closes a pure int32 implication that a checked proof already
/// established.
///
/// The kernel does not re-prove the conclusion. `completion` is the durable
/// record a completed [`ProofObject`](crate::kernel::proof::ProofObject)
/// issues for its root judgment, and this constructor checks only that the
/// record is the one the claimed implication describes: the proof's goal is
/// exactly `conclusion`, the facts its root branch assumed are exactly
/// `requirements`, and every free bitvector variable of both is listed exactly
/// once in `variables`. This is the sole constructor for authority that lets
/// a Click pure theorem participate in whole-contract certification.
pub(crate) fn prove_universally_quantified_pure_implication(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
    completion: &crate::kernel::proof::CheckedProposition,
) -> Option<CVerifiedPureTheorem> {
    checked_pure_implication_matches(&requirements, &conclusion, completion)
        .then(|| universally_close_pure_implication(requirements, conclusion, variables))?
}

/// Whether one completed proof is exactly a proof of `conclusion` from
/// `requirements`.
///
/// Both checks are exact: proposition identity, and set identity between the
/// root branch's assumed facts and the explicit requirements. The fact store
/// deduplicates equal top-level facts at construction, so a repeated
/// requirement is not a mismatch.
fn checked_pure_implication_matches(
    requirements: &[Proposition],
    conclusion: &Proposition,
    completion: &crate::kernel::proof::CheckedProposition,
) -> bool {
    completion.proposition() == conclusion
        && completion
            .root_assumptions()
            .to_vec()
            .into_iter()
            .collect::<BTreeSet<_>>()
            == requirements.iter().cloned().collect::<BTreeSet<_>>()
}

/// Folds the explicit requirements and binders around an established
/// conclusion. Every caller must already have checked the completion.
fn universally_close_pure_implication(
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

/// Opens one verified concrete target as a local named-contract refinement
/// problem for a pure theorem proof.
///
/// No project search occurs: both names are exact map lookups, and a concrete
/// target must already carry a verified or explicitly external rule.
pub fn c_function_contract_refinement_context(
    environment: &CExecutionEnvironment,
    contract_name: &str,
    target_name: &str,
) -> Option<CFunctionContractRefinementContext> {
    let contract = environment.get_function_contract(contract_name)?;
    let function = if let Some(rule) = environment.get_verified_function_rule(target_name) {
        &rule.function
    } else {
        &environment
            .get_external_function_rule(target_name)?
            .function
    };
    prepare_function_contract_refinement_context(
        contract,
        function,
        &mut ExecutionBudget::default(),
    )
}

/// The explicit refinement theorem a refused concrete formation needs.
///
/// Both names are exact map lookups into the same tables the formation check
/// reads, so the printed skeleton states the obligation that was refused.
///
/// `declared_parameter_spellings` lets the caller spell parameter types this
/// interface cannot: a struct pointer is kept as a layout, so the struct tag
/// comes from the contract's source declaration. A position left empty keeps
/// the spelling this interface derives from the modeled type.
pub fn c_named_contract_refinement_theorem_skeleton(
    environment: &CExecutionEnvironment,
    contract_name: &str,
    target_name: &str,
    declared_parameter_spellings: &[Option<String>],
) -> Option<String> {
    let contract = environment.get_function_contract(contract_name)?;
    let function = if let Some(rule) = environment.get_verified_function_rule(target_name) {
        &rule.function
    } else {
        &environment
            .get_external_function_rule(target_name)?
            .function
    };
    Some(named_contract_refinement_theorem_skeleton(
        contract,
        function,
        declared_parameter_spellings,
    ))
}

/// Opens one named contract as an implementation of another for the same
/// exact symbolic function-pointer value.
///
/// Both contract names are exact environment lookups. The source fact remains
/// an explicit premise of the theorem authority issued after refinement; this
/// operation does not infer contracts from a signature or inspect project
/// functions.
pub fn c_contract_refinement_context(
    environment: &CExecutionEnvironment,
    target_contract_name: &str,
    source_contract_name: &str,
    pointer: &CValue,
) -> Option<CFunctionContractRefinementContext> {
    let target = environment.get_function_contract(target_contract_name)?;
    let source = environment.get_function_contract(source_contract_name)?;
    let CValue::Pointer(pointer) = pointer else {
        return None;
    };
    if pointer.c_type() != target.function_pointer_type()
        || pointer.c_type() != source.function_pointer_type()
        || !matches!(pointer.pointer().block, PointerBlock::FunctionSymbolic(_))
        || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
    {
        return None;
    }
    let mut context = super::functions::contract_refinement_context_for_interface(
        target,
        source.name(),
        source.interface(),
        &mut ExecutionBudget::default(),
    )?;
    context.pointer = pointer.clone();
    context.source_contract = Some(source.clone());
    Some(context)
}

/// Returns the shared arbitrary argument values introduced by a refinement
/// theorem's `unfold(Contract)` step.
pub fn c_function_contract_refinement_arguments(
    context: &CFunctionContractRefinementContext,
) -> &[CValue] {
    &context.argument_values
}

/// Returns the symbolic entry state used to lower explicit proof conditions.
pub fn c_function_contract_refinement_entry_state(
    context: &CFunctionContractRefinementContext,
) -> CState {
    function_contract_refinement_entry_state(context)
}

pub fn c_function_contract_refinement_obligations(
    context: &CFunctionContractRefinementContext,
) -> Option<CFunctionContractRefinementObligations> {
    prepare_contract_refinement_obligations(context)
}

impl CFunctionContractRefinementObligations {
    pub fn entry(&self) -> &CState {
        &self.entry
    }
    pub fn post(&self) -> &CState {
        &self.post
    }
    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

/// Issues contract authority only from the exact closed ordinary proof obligation.
pub(crate) fn prove_c_function_contract_refinement(
    context: &CFunctionContractRefinementContext,
    conclusion: Proposition,
    proof: &crate::kernel::proof::CheckedProposition,
) -> Option<CVerifiedPureTheorem> {
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [
        state @ Term::CState(_),
        Term::CValue(CValue::Pointer(pointer)),
    ] = arguments.as_slice()
    else {
        return None;
    };
    if name != &context.contract.predicate_name()
        || pointer != &context.pointer
        || pointer.c_type() != context.contract.function_pointer_type()
    {
        return None;
    }

    let obligations = prepare_contract_refinement_obligations(context)?;
    if !proof.is_closed() || proof.proposition() != &obligations.proposition {
        return None;
    }
    let theorem = match &context.source_contract {
        None => {
            if context.pointer.pointer().block
                != PointerBlock::Function(context.function_name.clone())
            {
                return None;
            }
            conclusion
        }
        Some(source) => {
            let PointerBlock::FunctionSymbolic(variable) = &context.pointer.pointer().block else {
                return None;
            };
            let premise = Proposition::Predicate {
                name: source.predicate_name(),
                arguments: vec![
                    state.clone(),
                    Term::CValue(CValue::Pointer(context.pointer.clone())),
                ],
            };
            Proposition::ForAll {
                var: *variable,
                sort: Sort::CPointer(context.pointer.c_type()),
                body: Box::new(Proposition::Implies(
                    Box::new(premise),
                    Box::new(conclusion),
                )),
            }
        }
    };
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(theorem),
    })
}

mod contract_interface_identity;

/// A checked one-call wrapper proves a contract implication. The wrapper's
/// only extra inputs are source contracts for its last, arbitrary callback
/// parameter. Its body must call precisely that parameter with every other
/// parameter in order. No target-contract assumption authorizes this call.
pub(crate) fn prove_executed_contract_refinement(
    environment: &CExecutionEnvironment,
    source_names: &[&str],
    target_name: &str,
    conclusion: Proposition,
    rule: &CVerifiedFunctionRule,
) -> Option<CVerifiedPureTheorem> {
    if source_names.is_empty() {
        return None;
    }
    let target = environment.get_function_contract(target_name)?;
    let mut function = rule.function.clone();
    let callback = function.pop_parameter()?;
    if callback.c_type() != target.function_pointer_type() {
        return None;
    }
    let arguments = function
        .parameters()
        .iter()
        .map(|parameter| CExpression::Variable(parameter.name().to_string()))
        .collect();
    let call = if function.return_type() == CType::Void {
        CStatement::Call {
            function_name: callback.name().to_string(),
            arguments,
        }
    } else {
        CStatement::Seq(
            Arc::new(CStatement::CallAssign {
                target: "result".into(),
                function_name: callback.name().to_string(),
                arguments,
            }),
            Arc::new(CStatement::Return(CExpression::Variable("result".into()))),
        )
    };
    if function.body() != &call || function.source_body() != &call {
        return None;
    }
    for source_name in source_names.iter().rev() {
        let source = environment.get_function_contract(source_name)?;
        if callback.c_type() != source.function_pointer_type() {
            return None;
        }
        let source_requirement = SpecProposition::Predicate {
            name: source.predicate_name(),
            arguments: vec![SpecPredicateArgument::Value(SpecExpression::CExpression(
                CExpression::Variable(callback.name().to_string()),
            ))],
        };
        if function.pop_contract_requirement()? != source_requirement {
            return None;
        }
    }
    if !contract_interface_identity::same_interface(target, &function) {
        return None;
    }
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [
        state @ Term::CState(_),
        Term::CValue(CValue::Pointer(pointer)),
    ] = arguments.as_slice()
    else {
        return None;
    };
    let PointerBlock::FunctionSymbolic(variable) = pointer.pointer().block else {
        return None;
    };
    if name != &target.predicate_name()
        || pointer.c_type() != target.function_pointer_type()
        || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
    {
        return None;
    }
    let mut implication = conclusion.clone();
    for source_name in source_names.iter().rev() {
        let premise = Proposition::Predicate {
            name: environment
                .get_function_contract(source_name)?
                .predicate_name(),
            arguments: vec![
                state.clone(),
                Term::CValue(CValue::Pointer(pointer.clone())),
            ],
        };
        implication = Proposition::Implies(Box::new(premise), Box::new(implication));
    }
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(Proposition::ForAll {
            var: variable,
            sort: Sort::CPointer(pointer.c_type()),
            body: Box::new(implication),
        }),
    })
}

/// The declared interface of a verified or explicitly external project
/// function: its parameter types in order, then its return type. Two exact map
/// lookups, so a concrete `executes` clause is checked against the same C
/// signature the call rule will use.
pub fn c_project_function_signature(
    environment: &CExecutionEnvironment,
    name: &str,
) -> Option<(Vec<CType>, CType)> {
    let function = project_function_interface(environment, name)?;
    Some((
        function
            .parameters()
            .iter()
            .map(|parameter| parameter.c_type())
            .collect(),
        function.return_type(),
    ))
}

fn project_function_interface<'a>(
    environment: &'a CExecutionEnvironment,
    name: &str,
) -> Option<&'a CFunction> {
    if let Some(rule) = environment.get_verified_function_rule(name) {
        return Some(&rule.function);
    }
    Some(&environment.get_external_function_rule(name)?.function)
}

/// A checked one-call wrapper proves that a named project function satisfies a
/// named contract. The wrapper takes the contract's own interface and no extra
/// inputs; its body must be precisely one call to `callee_name` with every
/// parameter in order, so what the wrapper was verified to do is what that one
/// call does. No target-contract assumption authorizes this call, and no
/// source contract is quantified over: the source is the callee's own verified
/// or explicitly external contract, already used by the checked call.
pub(crate) fn prove_executed_concrete_contract_refinement(
    environment: &CExecutionEnvironment,
    callee_name: &str,
    target_name: &str,
    conclusion: Proposition,
    rule: &CVerifiedFunctionRule,
) -> Option<CVerifiedPureTheorem> {
    let target = environment.get_function_contract(target_name)?;
    // The callee has to be a function this project has a rule for. An
    // unverified name would make the checked call vacuous.
    project_function_interface(environment, callee_name)?;
    let function = rule.function.clone();
    let arguments = function
        .parameters()
        .iter()
        .map(|parameter| CExpression::Variable(parameter.name().to_string()))
        .collect();
    let call = if function.return_type() == CType::Void {
        CStatement::Call {
            function_name: callee_name.to_string(),
            arguments,
        }
    } else {
        CStatement::Seq(
            Arc::new(CStatement::CallAssign {
                target: "result".into(),
                function_name: callee_name.to_string(),
                arguments,
            }),
            Arc::new(CStatement::Return(CExpression::Variable("result".into()))),
        )
    };
    if function.body() != &call || function.source_body() != &call {
        return None;
    }
    if !contract_interface_identity::same_interface(target, &function) {
        return None;
    }
    let Proposition::Predicate { name, arguments } = &conclusion else {
        return None;
    };
    let [Term::CState(_), Term::CValue(CValue::Pointer(pointer))] = arguments.as_slice() else {
        return None;
    };
    if pointer.pointer().block != PointerBlock::Function(callee_name.to_string()) {
        return None;
    }
    if name != &target.predicate_name()
        || pointer.c_type() != target.function_pointer_type()
        || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
    {
        return None;
    }
    Some(CVerifiedPureTheorem {
        theorem: Theorem::new(conclusion),
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
        Bitvector32Term::UnsignedDivide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::UnsignedDivide(Box::new(left), Box::new(right))
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::Remainder(Box::new(left), Box::new(right))
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::UnsignedRemainder(Box::new(left), Box::new(right))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::ArithmeticShiftRight(Box::new(left), Box::new(right))
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::LogicalShiftRight(Box::new(left), Box::new(right))
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
        Bitvector32Term::Float32Negate(value) => Bitvector32Term::Float32Negate(Box::new(
            rewrite_int32_term_by_exact_equality(value, from, to),
        )),
        Bitvector32Term::Float32Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::Float32Binary {
            operator: *operator,
            left: Box::new(rewrite_int32_term_by_exact_equality(left, from, to)),
            right: Box::new(rewrite_int32_term_by_exact_equality(right, from, to)),
        },
        Bitvector32Term::Float64Negate(value) => Bitvector32Term::Float64Negate(Box::new(
            rewrite_int32_term_by_exact_equality(value, from, to),
        )),
        Bitvector32Term::Float64Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::Float64Binary {
            operator: *operator,
            left: Box::new(rewrite_int32_term_by_exact_equality(left, from, to)),
            right: Box::new(rewrite_int32_term_by_exact_equality(right, from, to)),
        },
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
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => term.clone(),
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _)
        | Bitvector32Term::PointerAddress(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::Int64FromUInt32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::UInt32From64(_)
        | Bitvector32Term::UInt64FromInt32(_)
        | Bitvector32Term::UInt64FromInt64(_)
        | Bitvector32Term::Int64Add(_, _)
        | Bitvector32Term::Int64Subtract(_, _)
        | Bitvector32Term::Int64Multiply(_, _)
        | Bitvector32Term::Int64Divide(_, _)
        | Bitvector32Term::Int64Remainder(_, _)
        | Bitvector32Term::Int64ShiftLeft(_, _)
        | Bitvector32Term::Int64ArithmeticShiftRight(_, _)
        | Bitvector32Term::Int64BitwiseAnd(_, _)
        | Bitvector32Term::Int64BitwiseOr(_, _)
        | Bitvector32Term::Int64BitwiseXor(_, _)
        | Bitvector32Term::Int64BitwiseNot(_)
        | Bitvector32Term::UInt64Add(_, _)
        | Bitvector32Term::UInt64Subtract(_, _)
        | Bitvector32Term::UInt64Multiply(_, _)
        | Bitvector32Term::UInt64Divide(_, _)
        | Bitvector32Term::UInt64Remainder(_, _)
        | Bitvector32Term::UInt64ShiftLeft(_, _)
        | Bitvector32Term::UInt64LogicalShiftRight(_, _)
        | Bitvector32Term::UInt64BitwiseAnd(_, _)
        | Bitvector32Term::UInt64BitwiseOr(_, _)
        | Bitvector32Term::UInt64BitwiseXor(_, _)
        | Bitvector32Term::UInt64BitwiseNot(_)
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::IntegerToMachine { .. } => term.clone(),
    }
}

/// Universally closes a pure int32 implication whose checked proof rewrote the
/// conclusion by an explicit ordered list of int32 equalities.
///
/// This is deliberately a certificate validator, and it neither proves the
/// conclusion nor proves a rewrite. `completion` carries the closed judgment,
/// exactly as in [`prove_universally_quantified_pure_implication`]. Each
/// supplied equality is *cited*: it must be exactly available among the
/// requirements (a requirement, or a conjunct of one), must actually rewrite
/// the equality goal reached so far, and is applied in the supplied
/// orientation. Reordering the list, dropping one, or naming an equality the
/// requirements do not contain is therefore rejected.
pub(crate) fn prove_universally_quantified_pure_implication_by_int32_rewrites(
    requirements: Vec<Proposition>,
    conclusion: Proposition,
    variables: Vec<Variable>,
    rewrites: Vec<Proposition>,
    completion: &crate::kernel::proof::CheckedProposition,
) -> Option<CVerifiedPureTheorem> {
    if !checked_pure_implication_matches(&requirements, &conclusion, completion) {
        return None;
    }
    let mut goal = conclusion.clone();
    for rewrite in rewrites {
        crate::kernel::proof::fact_reasoning::exactly_available_fact(&rewrite, &requirements)?;
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
    universally_close_pure_implication(requirements, conclusion, variables)
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

/// Moving one unit between nonnegative summands preserves their signed int32
/// sum. A positive right summand leaves both adjusted operands nonnegative,
/// while definedness of the original sum supplies the shared upper bound that
/// rules out overflow in the increment and recomposed sum.
pub fn prove_int32_move_one_from_right_to_left_preserves_sum(
    total: Bitvector32Term,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let left_is_nonnegative = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), left.clone()),
        true,
    );
    let right_is_positive = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), right.clone()),
        true,
    );
    let original_sum = Bitvector32Term::add(left.clone(), right.clone());
    let total_is_original_sum = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(total.clone()), Box::new(original_sum)),
        true,
    );
    let incremented = Bitvector32Term::add(left.clone(), Bitvector32Term::Constant(1));
    let decremented = Bitvector32Term::Subtract(
        Box::new(right.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let adjusted_sum = Bitvector32Term::add(incremented, decremented);
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(total), Box::new(adjusted_sum)),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(left_is_nonnegative),
        Box::new(Proposition::Implies(
            Box::new(right_is_positive),
            Box::new(Proposition::Implies(
                Box::new(total_is_original_sum),
                Box::new(conclusion),
            )),
        )),
    ))
}

/// Kernel-issued universally quantified authority for the unit-transfer sum rule.
pub fn certify_int32_move_one_from_right_to_left_preserves_sum() -> CVerifiedPureTheorem {
    let total = Variable(0);
    let left = Variable(1);
    let right = Variable(2);
    let implication = prove_int32_move_one_from_right_to_left_preserves_sum(
        Bitvector32Term::Variable(total),
        Bitvector32Term::Variable(left),
        Bitvector32Term::Variable(right),
    );
    CVerifiedPureTheorem {
        theorem: Theorem::new(forall_int32(
            total,
            forall_int32(left, forall_int32(right, implication.proposition().clone())),
        )),
    }
}

/// Mathematical bounds on the exact sum establish signed C addition safety.
pub fn prove_int32_add_defined_by_integer_bounds(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::Int32, value)
            .expect("every int32 bit pattern has a mathematical interpretation")
    };
    let sum: SharedIntegerTerm =
        IntegerTerm::Add(observe(left.clone()).into(), observe(right.clone()).into()).into();
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerGreaterEqual(
                sum.clone(),
                IntegerTerm::constant_i64(i64::from(i32::MIN)).into(),
            ),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    sum,
                    IntegerTerm::constant_i64(i64::from(i32::MAX)).into(),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_add_overflows(left, right),
                false,
            )),
        )),
    ))
}

/// A checked round trip through a machine carrier preserves an Integer
/// precisely within that carrier's representable range.
pub fn prove_integer_machine_round_trip(
    value: IntegerTerm,
    destination: MachineIntegerType,
) -> Theorem {
    let (lower, upper) = super::spec::integer_machine_bounds(destination);
    let converted = Bitvector32Term::IntegerToMachine {
        value: value.clone().into(),
        destination,
    };
    let observed = IntegerTerm::from_machine(destination, converted)
        .expect("machine observation has an integral carrier");
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerGreaterEqual(value.clone().into(), lower.into()),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(value.clone().into(), upper.into()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(observed.into(), value.into()),
                true,
            )),
        )),
    ))
}

/// Exact mathematical observation of a defined signed 32-bit addition.
/// The overflow premise is essential: the machine term alone is modular.
pub fn prove_int32_add_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_int32_operation_to_integer(left, right, false)
}

/// Signed int32 order is preserved by its exact mathematical observation.
/// Every int32 bit pattern has an Integer interpretation, so this law needs
/// only the corresponding C order premise and no definedness side condition.
pub fn prove_int32_less_equal_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::Int32, value)
            .expect("every int32 bit pattern has a mathematical interpretation")
    };
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let conclusion = Proposition::ConditionIs(
        ConditionTerm::IntegerLessEqual(observe(left).into(), observe(right).into()),
        true,
    );
    Theorem::new(Proposition::Implies(
        Box::new(premise),
        Box::new(conclusion),
    ))
}

/// Exact mathematical observation of a defined signed 32-bit subtraction.
pub fn prove_int32_subtract_to_integer(left: Bitvector32Term, right: Bitvector32Term) -> Theorem {
    prove_int32_operation_to_integer(left, right, true)
}

fn prove_int32_operation_to_integer(
    left: Bitvector32Term,
    right: Bitvector32Term,
    subtract: bool,
) -> Theorem {
    let observe = |value| {
        IntegerTerm::from_machine(MachineIntegerType::Int32, value)
            .expect("every int32 bit pattern has a mathematical interpretation")
    };
    let (overflow, machine, mathematical) = if subtract {
        (
            ConditionTerm::signed_subtract_overflows(left.clone(), right.clone()),
            Bitvector32Term::Subtract(Box::new(left.clone()), Box::new(right.clone())),
            IntegerTerm::Subtract(observe(left).into(), observe(right).into()),
        )
    } else {
        (
            ConditionTerm::signed_add_overflows(left.clone(), right.clone()),
            Bitvector32Term::Add(Box::new(left.clone()), Box::new(right.clone())),
            IntegerTerm::Add(observe(left).into(), observe(right).into()),
        )
    };
    Theorem::new(Proposition::Implies(
        Box::new(Proposition::ConditionIs(overflow, false)),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(observe(machine).into(), mathematical.into()),
            true,
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

/// Kernel-issued authority for the fixed predecessor bound used by independent
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

/// Signed greater-equal is the reversed form of signed less-equal.
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
