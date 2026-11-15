use super::*;
use crate::kernel::unary_term;
use crate::kernel::{
    CompareRelation, KernelTerm, MachineBinaryOp, MachineIntegerType,
    MachineOperandView as Operand, MachineUnaryOp, SharedMachineIntegerTerm,
};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{bits32_constant, constant_u32};

mod contract_claims;
mod input_initialization;
mod retained_syntax;
pub use contract_claims::*;

/// Exhaustive contract-entry alternatives constructed before a body proof.
/// The caller, declared subject and case contexts are retained together;
/// registration consumes these contexts without reconstructing the entry.
#[derive(Clone)]
pub(crate) struct PreparedContractEntryCases {
    identity: Arc<()>,
    pub(super) guard_cases: Vec<Vec<Proposition>>,
    pub(super) state: ExecutionState,
    pub(super) function: ProgramFunction,
    pub(super) arguments: Vec<ProgramExpression>,
    pub(super) byte_order: Proposition,
    pub(super) raw_entry_state: ExecutionState,
    pub(super) closing_entry: Arc<RetainedClosingEntry>,
    closing_footprint: std::sync::OnceLock<RetainedClosingFootprint>,
    pub(super) cases: Vec<PreparedContractEntryCase>,
}

#[derive(Clone, Debug)]
pub(super) struct PreparedContractEntryCase {
    pub(super) assumptions: PureFactContext,
    pub(super) entry_state: ExecutionState,
    pub(super) closing_entry: Arc<RetainedClosingEntry>,
}

impl std::fmt::Debug for PreparedContractEntryCases {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedContractEntryCases")
            .field("function", &self.function.name())
            .field("cases", &self.cases.len())
            .finish_non_exhaustive()
    }
}

impl PartialEq for PreparedContractEntryCases {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.identity, &other.identity)
    }
}
impl Eq for PreparedContractEntryCases {}

impl PreparedContractEntryCases {
    #[cfg(test)]
    pub(crate) fn case_count(&self) -> usize {
        self.cases.len()
    }

    pub(crate) fn caller_state(&self) -> &ExecutionState {
        &self.state
    }

    pub(crate) fn closing_entry(&self) -> &RetainedClosingEntry {
        &self.closing_entry
    }

    pub(crate) fn retain_closing_footprint(
        &self,
        transfer: &crate::kernel::functions::CheckedBoundaryResourceTransfer,
        assumptions: &PureFactContext,
    ) {
        let footprint = RetainedClosingFootprint::from_transfer(transfer, assumptions);
        let _ = self.closing_footprint.set(footprint);
    }
}

/// Consume executions produced by this opened entry. Their root premises and
/// entry representation were fixed by the producer; no premise authorization,
/// resource rebasing, or execution-metadata reconstruction occurs here.
#[cfg(test)]
fn execution_from_owned_contract_entry(
    entry: &Arc<PreparedContractEntryCases>,
    artifacts: &[CheckedFunctionExecution],
) -> FunctionContractExecution {
    let selected = artifacts
        .iter()
        .filter(|artifact| {
            crate::instrumentation::record_deterministic_work(1);
            artifact
                .entry_authority
                .as_ref()
                .is_some_and(|authority| Arc::ptr_eq(authority.cases(), entry))
        })
        .collect::<Vec<_>>();
    if selected.is_empty() {
        return FunctionContractExecution::failed(
            "the contract has no execution produced by its opened entry".into(),
        );
    }
    execution_from_bound_contract_entry(entry, &selected)
}

/// Package the explicit outputs of this root's own completed strategies.
/// Their entry binding was fixed when the ordinary proof opened them.
#[cfg(test)]
fn execution_from_bound_contract_entry(
    entry: &Arc<PreparedContractEntryCases>,
    selected: &[&CheckedFunctionExecution],
) -> FunctionContractExecution {
    let cases = entry
        .cases
        .iter()
        .map(|_| {
            selected
                .iter()
                .map(|checked| {
                    crate::instrumentation::record_deterministic_work(1);
                    ContractPathSet {
                        closed_exit_obligations: checked.closed_exit_obligations.clone(),
                        boundary_transfers: vec![
                            checked.boundary_transfer().cloned();
                            checked.execution.paths.len()
                        ],
                        paths: checked.execution.paths.clone(),
                        checked_resource_claims: checked.checked_resource_claims.clone(),
                        checked_resource_transitions: checked.checked_resource_transitions.clone(),
                        deferred_contract_exits: checked.deferred_contract_exits.clone(),
                        deferred_contract_exit_errors: checked
                            .deferred_contract_exit_errors
                            .clone(),
                        checked_returned_resources: checked.checked_returned_resources.clone(),
                        completion_origin_state: Some(checked.state.clone()),
                        completion_path_origins: checked
                            .execution
                            .paths
                            .iter()
                            .map(|path| path.theorem.clone())
                            .collect(),
                    }
                })
                .collect()
        })
        .collect::<Vec<_>>();
    let mut checked_call_events = crate::kernel::proof::CheckedCallEvents::default();
    let mut applied_tactics = BTreeSet::new();
    for artifact in selected {
        checked_call_events.extend(&artifact.checked_call_events);
        applied_tactics.extend(artifact.applied_tactics.iter().cloned());
    }
    FunctionContractExecution {
        pointer_result: super::super::object_types::execution_pointer_result(&cases),
        cases,
        reuse_diagnostic: None,
        reuse_unauthorized_premise: None,
        reuse_entry_resources: vec![],
        reuse_context_facts: vec![],
        checked_call_events,
        loop_semantics: if selected
            .iter()
            .all(|artifact| artifact.execution_semantics.loops == LoopSemantics::ApplyVerifiedRules)
        {
            LoopSemantics::ApplyVerifiedRules
        } else {
            LoopSemantics::Verify
        },
        applied_tactics,
        checked_callees: super::super::termination::merge_checked_callees(
            selected
                .iter()
                .map(|artifact| artifact.checked_callees.as_ref()),
        ),
    }
}

pub(crate) fn prepare_function_contract_entry_cases(
    entry: ContractEntry,
    byte_order: Proposition,
) -> Result<PreparedContractEntryCases, String> {
    let ContractEntry {
        subject,
        assumptions,
        facts,
        resources,
        ..
    } = entry;
    let state = &subject.state;
    let function = &subject.function;
    let arguments = &subject.arguments;
    let base_assumptions = assumptions.assume_proposition(byte_order.clone());
    let closing_facts = facts
        .iter()
        .filter(|fact| {
            matches!(
                fact.origin(),
                ContractEntryFactOrigin::CompositeDefinition
                    | ContractEntryFactOrigin::PopulationFact
                    | ContractEntryFactOrigin::Observable
            )
        })
        .map(|fact| fact.proposition().clone())
        .collect();
    let closing_entry = Arc::new(RetainedClosingEntry::from_producer(
        state.clone(),
        function,
        arguments.to_vec(),
        resources.state,
        resources.required,
        resources.checked,
        base_assumptions.clone(),
        closing_facts,
    ));
    let resource_condition_cases = contract_resource_condition_cases(
        state,
        function,
        arguments,
        &base_assumptions.clone().assume_entry_clause_extents(),
    )
    .ok_or("could not enumerate the undecided resource guards of the contract entry")?;
    let raw_entry_state = program_function_entry_state(state, function, arguments)
        .ok_or("could not build the contract entry state from the call arguments")?;
    let has_recursive_resources = function
        .composite_resource_definitions()
        .iter()
        .any(CompositeResourceDefinition::is_recursive);
    let mut cases = Vec::with_capacity(resource_condition_cases.len());
    for case_facts in &resource_condition_cases {
        crate::instrumentation::record_deterministic_work(1);
        let assumptions = assumptions_with_propositions(&base_assumptions, case_facts);
        let entry_state = if has_recursive_resources {
            // Keep proof-directed projections for recursive resources.
            raw_entry_state.clone()
        } else {
            let resources = super::super::functions::expand_all_composite_resource_facts_at_state(
                raw_entry_state.resources(),
                function.composite_resource_definitions(),
                &raw_entry_state,
                &assumptions,
            )
            .ok_or("could not expand the composite resources of the contract entry state")?;
            raw_entry_state.clone().with_resource_context(resources)
        };
        let closing_case =
            Arc::new(closing_entry.for_case(function, entry_state.clone(), assumptions.clone()));
        cases.push(PreparedContractEntryCase {
            assumptions,
            entry_state,
            closing_entry: closing_case,
        });
    }
    Ok(PreparedContractEntryCases {
        identity: Arc::new(()),
        guard_cases: resource_condition_cases,
        state: state.clone(),
        function: function.clone(),
        arguments: arguments.to_vec(),
        byte_order,
        raw_entry_state,
        closing_entry,
        closing_footprint: std::sync::OnceLock::new(),
        cases,
    })
}

#[cfg(test)]
thread_local! {
    static GUARD_CASE_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn guard_case_builds() -> usize {
    GUARD_CASE_BUILDS.with(std::cell::Cell::get)
}

/// Returns an exhaustive set of proof-only cases for undecided guards on
/// composite resources required directly at function entry.
///
/// A contract such as `owns nullable(p)` denotes either an empty resource or
/// its guarded body. Exact certification must check both meanings when the
/// caller leaves the guard symbolic, even if the C body contains no matching
/// `if`. The cases below are generated wholly from the kernel contract and
/// always include both truth values, so they add no trusted hypothesis.
pub(crate) fn contract_resource_condition_cases(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
) -> Option<Vec<Vec<Proposition>>> {
    #[cfg(test)]
    GUARD_CASE_BUILDS.with(|count| count.set(count.get() + 1));
    let entry_state = program_function_entry_state(caller_state, function, arguments)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let required_resources = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        function.composite_resource_definitions(),
        &assumptions.clone().assume_entry_clause_extents(),
        &mut budget,
    )
    .ok()?
    .ok()?;
    let mut guards = Vec::new();
    for resource in required_resources.facts() {
        let Resource::Composite {
            name,
            arguments: resource_arguments,
        } = resource.resource()
        else {
            continue;
        };
        let definition = function
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == name)?;
        let Some(condition) = definition.condition() else {
            continue;
        };
        if definition.parameters().len() != resource_arguments.len() {
            return None;
        }
        let mut condition_state = ExecutionState::new()
            .with_memory(entry_state.memory().clone())
            .with_resource_context(required_resources.clone());
        for (parameter, value) in definition
            .parameters()
            .iter()
            .zip(resource_arguments.iter())
        {
            let value = value.as_program_value()?;
            if parameter.program_type() != value.program_type() {
                return None;
            }
            condition_state.locals.set_typed(
                parameter.name().to_string(),
                value.clone(),
                parameter.program_type(),
            );
        }
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &condition_state,
            condition,
            None,
            &lowering_assumptions,
            &mut budget,
        )
        .ok()?;
        let [path] = paths.as_slice() else {
            return None;
        };
        if !path.obligations.iter().all(|obligation| {
            crate::kernel::PureFactContext::settles_exactly(assumptions, obligation.proposition())
        }) {
            return None;
        }
        if !guards.contains(&path.proposition) {
            guards.push(path.proposition.clone());
        }
    }
    // A conditional produced resource is also a contract-entry case split.
    // Its guard selects whether the post-state effect exists, so exact
    // certification must check both selections when the caller leaves the
    // pre-state symbolic. Callers with an established guard still take the
    // single selected route at ordinary call application time.
    for resource in function.resource_ensures() {
        let Some(condition) = resource.guard() else {
            continue;
        };
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &entry_state,
            condition,
            Some(&entry_state),
            &lowering_assumptions,
            &mut budget,
        )
        .ok()?;
        let [path] = paths.as_slice() else {
            return None;
        };
        if !path.obligations.iter().all(|obligation| {
            crate::kernel::PureFactContext::settles_exactly(assumptions, obligation.proposition())
        }) {
            return None;
        }
        if !guards.contains(&path.proposition) {
            guards.push(path.proposition.clone());
        }
    }

    let mut cases = vec![Vec::new()];
    for guard in guards {
        let negated = negate_contract_case_proposition(&guard);
        let mut next = Vec::new();
        for facts in cases {
            let case_assumptions = assumptions_with_propositions(assumptions, &facts);
            if crate::kernel::PureFactContext::settles_exactly(&case_assumptions, &guard)
                || crate::kernel::PureFactContext::settles_exactly(&case_assumptions, &negated)
            {
                next.push(facts);
                continue;
            }
            let mut when_true = facts.clone();
            when_true.push(guard.clone());
            next.push(when_true);
            let mut when_false = facts;
            when_false.push(negated.clone());
            next.push(when_false);
        }
        budget.check_path_width(next.len()).ok()?;
        cases = next;
    }
    Some(cases)
}

fn negate_contract_case_proposition(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !*value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// Splits a proposition into its conjunct leaves.
fn proposition_conjuncts(proposition: &Proposition, into: &mut Vec<Proposition>) {
    match proposition {
        Proposition::And(left, right) => {
            proposition_conjuncts(left, into);
            proposition_conjuncts(right, into);
        }
        other => into.push(other.clone()),
    }
}

/// Converts a nonnegative pointer displacement to a byte count. Symbolic
/// scaling and addition are admitted only with bounds that make the 32-bit
/// term agree with the pointer offset's exact integer arithmetic.
fn certification_binary(
    assumptions: &PureFactContext,
    operator: MachineBinaryOp,
    left: Operand<'_>,
    right: Operand<'_>,
) -> SharedMachineIntegerTerm {
    let format = MachineIntegerType::Int32;
    let root = crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
        format,
        operator,
        KernelTerm::retained_machine_operand(format, left),
        KernelTerm::retained_machine_operand(format, right),
    );
    assumptions.simplify_machine_operand_under_assumptions(Operand::Shared(&root), format)
}

fn pointer_offset_bytes(
    assumptions: &PureFactContext,
    offset: &PointerOffsetTerm,
) -> Option<SharedMachineIntegerTerm> {
    let literal =
        |n| SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, MachineTerm::constant(n));
    if let Some(bytes) = offset.as_const() {
        return u32::try_from(bytes).ok().map(literal);
    }
    let zero = MachineTerm::constant(0);
    let max = i32::MAX as u32;
    let le =
        |a: Operand<'_>, b: Operand<'_>| certification_proves_signed_le_views(assumptions, a, b);
    match offset {
        PointerOffsetTerm::Constant(_)
        | PointerOffsetTerm::Variable(_)
        | PointerOffsetTerm::Int64Scaled { .. } => None,
        PointerOffsetTerm::Add(left, right) => {
            let left = pointer_offset_bytes(assumptions, left)?;
            let right = pointer_offset_bytes(assumptions, right)?;
            let sum = certification_binary(
                assumptions,
                MachineBinaryOp::Add,
                left.operand_view(),
                right.operand_view(),
            );
            (le(Operand::Legacy(&zero), left.operand_view())
                && le(Operand::Legacy(&zero), right.operand_view())
                && le(Operand::Legacy(&zero), sum.operand_view())
                && le(left.operand_view(), sum.operand_view())
                && le(right.operand_view(), sum.operand_view()))
            .then_some(sum)
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            let width = u32::try_from(*byte_width).ok().filter(|width| *width > 0)?;
            let limit = MachineTerm::constant(max / width);
            (le(Operand::Legacy(&zero), value.operand_view())
                && (width == 1 || le(value.operand_view(), Operand::Legacy(&limit))))
            .then(|| {
                if width == 1 {
                    value.clone()
                } else {
                    certification_binary(
                        assumptions,
                        MachineBinaryOp::Multiply,
                        value.operand_view(),
                        Operand::Legacy(&MachineTerm::constant(width)),
                    )
                }
            })
        }
    }
}

/// The byte distance from `fact_offset` to `goal_offset` when the goal
/// offset extends the fact offset additively.
fn pointer_offset_byte_delta(
    assumptions: &PureFactContext,
    goal_offset: &PointerOffsetTerm,
    fact_offset: &PointerOffsetTerm,
) -> Option<SharedMachineIntegerTerm> {
    if goal_offset == fact_offset {
        return Some(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::constant(0),
        ));
    }
    if let PointerOffsetTerm::Add(left, right) = goal_offset {
        if left.as_ref() == fact_offset {
            return pointer_offset_bytes(assumptions, right);
        }
        if right.as_ref() == fact_offset {
            return pointer_offset_bytes(assumptions, left);
        }
    }
    None
}

fn split_additive_constant(term: Operand<'_>) -> (SharedMachineIntegerTerm, u32) {
    if let Some((MachineIntegerType::Int32, MachineBinaryOp::Add, [left, right])) = term.binary() {
        if let Some(value) = right.word32_constant() {
            return (left.retain(MachineIntegerType::Int32), value);
        }
        if let Some(value) = left.word32_constant() {
            return (right.retain(MachineIntegerType::Int32), value);
        }
    }
    (term.retain(MachineIntegerType::Int32), 0)
}

/// Certifies a loadability goal from an assumed wider loadable fact over the
/// same memory state: the goal's base must sit at a provably in-bounds
/// byte offset within the fact's span.
/// Whether `state` justifies a load obligation a lowering left open: the
/// assumptions state the loadability exactly, the memory holds the cells, or
/// the resources permit the read. A load under a premise is judged with the
/// premise assumed; a quantified load is left to certification.
pub fn execution_state_justifies_loadability_obligation(
    state: &ExecutionState,
    obligation: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    match obligation {
        Proposition::Implies(premise, body) => {
            let assumptions = assumptions
                .clone()
                .assume_proposition(premise.as_ref().clone());
            execution_state_justifies_loadability_obligation(state, body, &assumptions)
        }
        Proposition::And(left, right) => {
            execution_state_justifies_loadability_obligation(state, left, assumptions)
                && execution_state_justifies_loadability_obligation(state, right, assumptions)
        }
        Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => {
            if assumptions.proves_exact(obligation) {
                return true;
            }
            let loadable = Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: pointer.clone(),
                bytes: MachineTerm::constant(value_type.byte_width()),
                wide: false,
            };
            execution_state_justifies_loadability_obligation(state, &loadable, assumptions)
                && assumptions
                    .clone()
                    .assume_proposition(loadable)
                    .proves_memory_read_defined(memory, pointer, *value_type)
        }
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } => {
            assumptions.proves_exact(obligation)
                || matches!(memory.load(base), ExpressionOutcome::Value(_))
                || match bytes.as_const() {
                    Some(width) => {
                        memory.is_loadable_concretely(base, width)
                            || state
                                .resources()
                                .permits_memory_read(base, width, assumptions)
                    }
                    None => crate::kernel::resource_context_has_symbolic_range_read(
                        state.resources(),
                        base,
                        bytes,
                        assumptions,
                    ),
                }
                || assumptions.proves_memory_loadable_for_memory_resolution(memory, base, bytes)
                || symbolic_base_aliases_a_held_cell(memory, base, assumptions)
        }
        _ => true,
    }
}

/// A pointer the proof names by a value, such as a model's pointer field,
/// has a symbolic block of its own, and no cell is filed under it. When a
/// stated equality names the object it points to, the read is of that
/// object's cell. Follow the equality one hop to a pointer memory files a
/// cell under, which may itself be a pointer read from memory. The aliases
/// are read by key and an alias of an alias is not followed, so the work is
/// bounded by the equalities stated about this one pointer.
fn symbolic_base_aliases_a_held_cell(
    memory: &Memory,
    base: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    if !matches!(base.block, PointerBlock::Symbolic(_)) {
        return false;
    }
    let Some(offset) = base
        .offset
        .as_const()
        .and_then(|offset| u32::try_from(offset).ok())
    else {
        return false;
    };
    let object = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    assumptions.exact_pointer_aliases(&object).any(|alias| {
        crate::instrumentation::record_deterministic_work(1);
        matches!(
            memory.load(&alias.offset_by_bytes(offset)),
            ExpressionOutcome::Value(_)
        )
    })
}

/// Reject a read of freed memory unless a checked path fact proves that the
/// guard containing the read is false. The guarded obligation itself remains
/// subject to ordinary certification.
pub fn program_loadability_obligation_impossible_with_assumptions(
    obligation: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    match obligation {
        Proposition::Implies(premise, body) => {
            program_loadability_obligation_impossible_with_assumptions(body, assumptions)
                && !crate::kernel::PureFactContext::settles_exactly(
                    assumptions,
                    &negate_contract_case_proposition(premise),
                )
        }
        Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
            program_loadability_obligation_impossible_with_assumptions(body, assumptions)
        }
        Proposition::And(left, right) => {
            program_loadability_obligation_impossible_with_assumptions(left, assumptions)
                || program_loadability_obligation_impossible_with_assumptions(right, assumptions)
        }
        Proposition::MemoryLoadable { memory, base, .. } => {
            memory.is_ended_local_address(base)
                || memory.is_deallocated_heap_address(base, &PureFactContext::new())
                || memory.freed_heap_allocation_may_contain(base, &PureFactContext::new())
        }
        _ => false,
    }
}

pub fn loadable_covered_by_fact(assumptions: &PureFactContext, goal: &Proposition) -> bool {
    let Proposition::MemoryLoadable {
        memory,
        base,
        bytes,
        wide: false,
    } = goal
    else {
        return false;
    };
    // Exact membership stays indexed. A covering source must be unambiguous
    // at an indexed address shape, or explicitly selected by the planner;
    // this fallback must not reopen an ambient block scan after checking
    // has already declined its candidate buckets.
    crate::instrumentation::record_deterministic_work(1);
    let covered = assumptions.contains_assumed_exact(goal)
        || assumptions
            .memory_loadable_candidates_for_base(base)
            .any(|fact| {
                let Proposition::MemoryLoadable {
                    memory: fact_memory,
                    base: fact_base,
                    bytes: fact_bytes,
                    wide: false,
                } = fact
                else {
                    return false;
                };
                if fact_base.block != base.block {
                    return false;
                }
                // Loadability of a covering span transports across differences in
                // embedded memory states and recorded write effects just like an exact-range
                // fact does.
                if fact_memory != memory
                    && !crate::kernel::reasoning::memory_range_still_available(
                        fact_memory,
                        memory,
                        base,
                        assumptions,
                    )
                    && !memories_canonically_equal(fact_memory, memory)
                    && !memories_connected_by_effects(fact_memory, memory, assumptions)
                {
                    return false;
                }
                // The region rule reasons at element granularity and can cover a
                // constant-size cell even when its symbolic byte offset is too wide
                // for this rule's signed arithmetic.
                if assumptions
                    .simplify_bitvector_under_assumptions(bytes)
                    .as_const()
                    .is_some_and(|byte_width| {
                        assumptions.proves_loadable_cell_from_region_elements(
                            fact_base, fact_bytes, base, byte_width,
                        )
                    })
                {
                    return true;
                }
                let Some(delta_bytes) =
                    pointer_offset_byte_delta(assumptions, &base.offset, &fact_base.offset)
                else {
                    return false;
                };
                let delta = assumptions.simplify_machine_operand_under_assumptions(
                    delta_bytes.operand_view(),
                    MachineIntegerType::Int32,
                );
                let width = assumptions.simplify_machine_operand_under_assumptions(
                    Operand::Legacy(bytes),
                    MachineIntegerType::Int32,
                );
                let span = assumptions.simplify_machine_operand_under_assumptions(
                    Operand::Legacy(fact_bytes),
                    MachineIntegerType::Int32,
                );
                if let (Some(delta), Some(width), Some(span)) = (
                    delta.operand_view().word32_constant(),
                    width.operand_view().word32_constant(),
                    span.operand_view().word32_constant(),
                ) {
                    return u64::from(delta) + u64::from(width) <= u64::from(span);
                }
                let start = MachineTerm::constant(0);
                let end = certification_binary(
                    assumptions,
                    MachineBinaryOp::Add,
                    delta.operand_view(),
                    width.operand_view(),
                );
                let le = |a: Operand<'_>, b: Operand<'_>| {
                    certification_proves_signed_le_views(assumptions, a, b)
                };
                // Preserve the signed nonwrapping-sum rule: both addends are
                // nonnegative and the sum has not fallen below its first one.
                let nonwrapping_sum =
                    crate::kernel::assumptions::signed_byte_sum_is_nonwrapping_views(
                        delta.operand_view(),
                        width.operand_view(),
                        end.operand_view(),
                        le,
                    );
                let ends_in_bounds = nonwrapping_sum
                    && ((le(Operand::Legacy(&start), span.operand_view())
                        && le(end.operand_view(), span.operand_view()))
                        || {
                            let (end_base, end_shift) = split_additive_constant(end.operand_view());
                            let (span_base, span_shift) =
                                split_additive_constant(span.operand_view());
                            end_shift <= i32::MAX as u32
                                && span_shift <= i32::MAX as u32
                                && end_shift <= span_shift
                                && le(Operand::Legacy(&start), end_base.operand_view())
                                && le(Operand::Legacy(&start), span_base.operand_view())
                                && le(end_base.operand_view(), end.operand_view())
                                && le(end_base.operand_view(), span_base.operand_view())
                        });
                if ends_in_bounds {
                    return true;
                }
                false
            });
    if covered {
        crate::kernel::record_implicit_reasoning_provenance(assumptions, goal);
    }
    covered
}

/// Certifies `left <= right` by the exact rules: two constants compare,
/// an exact assumed fact, or the bounded order prover.
fn certification_proves_signed_le_views(
    assumptions: &PureFactContext,
    left: Operand<'_>,
    right: Operand<'_>,
) -> bool {
    if let (Some(left), Some(right)) = (left.word32_constant(), right.word32_constant()) {
        return (left as i32) <= (right as i32);
    }
    let condition = crate::kernel::machine_integer::comparison::condition_for_operand_views(
        MachineIntegerType::Int32,
        CompareRelation::LessEqual,
        [left, right],
    );
    assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), true))
        || assumptions.proves_order_condition_for_memory_resolution(&condition, true)
}

fn collect_shallow_term_variables(term: &MachineTerm, variables: &mut BTreeSet<Variable>) {
    match term {
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            ..
        }
        | MachineTerm::BoolCast { .. } => {}

        MachineTerm::Constant { .. }
        | cast_term!(Int64From32, _)
        | cast_term!(Int64FromUInt32, _)
        | cast_term!(UInt64From32, _)
        | cast_term!(UInt32From64, _)
        | cast_term!(UInt64FromInt32, _)
        | cast_term!(UInt64FromInt64, _)
        | crate::kernel::binary_wide_term!(..)
        | crate::kernel::unary_wide_term!(..) => {}
        MachineTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        crate::kernel::binary_bitvector32_term!(left, right) => {
            collect_shallow_term_variables(left, variables);
            collect_shallow_term_variables(right, variables);
        }
        MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            collect_shallow_term_variables(left, variables);
            collect_shallow_term_variables(right, variables);
        }
        unary_term!(Bits32, BitwiseNot, inner)
        | MachineTerm::Float32Negate(inner)
        | MachineTerm::Float64Negate(inner) => {
            collect_shallow_term_variables(inner, variables);
        }
        MachineTerm::If {
            then_term,
            else_term,
            ..
        } => {
            collect_shallow_term_variables(then_term, variables);
            collect_shallow_term_variables(else_term, variables);
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_shallow_term_variables(start, variables);
            collect_shallow_term_variables(end, variables);
            collect_shallow_term_variables(initial, variables);
            collect_shallow_term_variables(body, variables);
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_shallow_term_variables(argument, variables);
            }
        }
        MachineTerm::ClickFunctionApplication { .. } | MachineTerm::AlgebraicMatch { .. } => {}
        // The memory state may contain a large symbolic state. Only
        // variables outside nested loads can be the surrounding
        // quantified index. Variables in the loaded address belong to
        // the base expression (for example the owner parameter), not to
        // that index.
        MachineTerm::MemoryLoad(_, _, _) => {}
        MachineTerm::PointerAddress(_, _) | MachineTerm::IntegerToMachine { .. } => {}
    }
}

fn collect_shallow_operand_variables(term: Operand<'_>, variables: &mut BTreeSet<Variable>) {
    let mut pending = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(term) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if let Operand::Legacy(term) = term {
            collect_shallow_term_variables(term, variables);
            continue;
        }
        let Operand::Shared(root) = term else {
            unreachable!()
        };
        if !seen.insert(root.id()) {
            continue;
        }
        if let Some((_, _, children)) = term.fold() {
            pending.extend(children);
            continue;
        }
        if let Some(leaf) = root.machine_conversion_leaf() {
            collect_shallow_term_variables(leaf, variables);
            continue;
        }
        if let Some(variable) = term.variable() {
            variables.insert(*variable);
        } else if let Some((format, _, [left, right])) = term.binary() {
            if format.format().bits() == 32 {
                pending.push(right);
                pending.push(left);
            }
        } else if let Some((format, MachineUnaryOp::BitwiseNot, child)) = term.unary() {
            if format.format().bits() == 32 {
                pending.push(child);
            }
        }
        // Casts, wide operations, reads and Integer payloads are opaque to
        // this binder-coordinate query, exactly as in its native rule.
    }
}

/// Certifies a universally-quantified loadability side-obligation from
/// assumed loadable facts: the bound premises become facts about the free
/// bound variable, and the loadable body must then be covered by a wider
/// assumed span.
fn forall_loadable_covered_by_fact(assumptions: &PureFactContext, goal: &Proposition) -> bool {
    let Proposition::ForAll {
        sort: Sort::ProgramInt32 | Sort::Bitvector32,
        body,
        ..
    } = goal
    else {
        return false;
    };
    let mut premises = Vec::new();
    let mut conclusion = body.as_ref();
    while let Proposition::Implies(premise, rest) = conclusion {
        proposition_conjuncts(premise, &mut premises);
        conclusion = rest.as_ref();
    }
    if !matches!(conclusion, Proposition::MemoryLoadable { .. }) {
        return false;
    }
    let premise_assumptions = assumptions_with_propositions(assumptions, &premises);
    loadable_covered_by_fact(&premise_assumptions, conclusion)
}

/// An explicitly quantified loadability fact supplies a cell when its guard
/// holds. A proposition about a load's value supplies no validity evidence.
pub(in crate::kernel) fn quantified_int32_fact_certifies_loadable_cell(
    assumptions: &PureFactContext,
    memory: &Memory,
    base: &Pointer,
) -> bool {
    if crate::kernel::assumptions::reasoning_interrupted() {
        return false;
    }
    fn collect_shallow_offset_variables(
        offset: &PointerOffsetTerm,
        variables: &mut BTreeSet<Variable>,
    ) {
        match offset {
            PointerOffsetTerm::Constant(_) => {}
            PointerOffsetTerm::Variable(variable) => {
                variables.insert(*variable);
            }
            PointerOffsetTerm::Add(left, right) => {
                collect_shallow_offset_variables(left, variables);
                collect_shallow_offset_variables(right, variables);
            }
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => {
                collect_shallow_operand_variables(value.operand_view(), variables);
            }
        }
    }

    fn implication_parts(body: &Proposition) -> (Vec<Proposition>, &Proposition) {
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            proposition_conjuncts(premise, &mut premises);
            conclusion = rest.as_ref();
        }
        (premises, conclusion)
    }

    let mut target_variables = BTreeSet::new();
    if let PointerBlock::Symbolic(variable) = base.block {
        target_variables.insert(variable);
    }
    collect_shallow_offset_variables(&base.offset, &mut target_variables);
    // Only a universal concluding loadability can certify the cell.
    let loadable = crate::kernel::assumptions::UniversalConclusionKey::Loadable;
    let exact_binder_candidates = assumptions.universals_concluding(loadable).filter(
        |fact| matches!(fact, Proposition::ForAll { var, .. } if target_variables.contains(var)),
    );
    let renamed_binder_candidates = assumptions.universals_concluding(loadable).filter(
        |fact| matches!(fact, Proposition::ForAll { var, .. } if !target_variables.contains(var)),
    );
    exact_binder_candidates
        .chain(renamed_binder_candidates)
        .any(|fact| {
            if crate::kernel::assumptions::reasoning_interrupted() {
                return false;
            }
            let Proposition::ForAll {
                var: fact_var,
                sort: Sort::ProgramInt32 | Sort::Bitvector32,
                body,
                ..
            } = fact
            else {
                return false;
            };
            let exact_target = target_variables.contains(fact_var).then_some(*fact_var);
            exact_target
                .into_iter()
                .chain(
                    target_variables
                        .iter()
                        .copied()
                        .filter(|target| target != fact_var),
                )
                .any(|target_var| {
                    if crate::kernel::assumptions::reasoning_interrupted() {
                        return false;
                    }
                    let Some(instantiated) = substitute_quantified_body_capture_free(
                        body,
                        *fact_var,
                        target_var,
                        &Sort::ProgramInt32,
                    ) else {
                        return false;
                    };
                    let (premises, conclusion) = implication_parts(&instantiated);
                    let premises_hold = premises.iter().all(|premise| {
                        !crate::kernel::assumptions::reasoning_interrupted()
                            && matches!(premise, Proposition::ConditionIs(_, _))
                            && PureFactContext::settles_exactly(assumptions, premise)
                    });
                    premises_hold
                        && match conclusion {
                            Proposition::MemoryLoadable {
                                memory: fact_memory,
                                base: fact_base,
                                bytes,
                                wide: false,
                            } => {
                                bytes.as_const() == Some(4)
                                    && crate::kernel::reasoning::memory_range_still_available(
                                        fact_memory,
                                        memory,
                                        fact_base,
                                        assumptions,
                                    )
                                    && (canonicalize_pointer_loads(fact_base)
                                        == canonicalize_pointer_loads(base)
                                        || pointers_proven_equal_for_memory_resolution(
                                            fact_base,
                                            base,
                                            assumptions,
                                        ))
                            }
                            _ => false,
                        }
                })
        })
}

/// Certifies an existential requirement side-obligation (typically the
/// loadability safety of an existential requirement body) from an assumed
/// existential alpha-equal to it: its witness supplies the bound variable,
/// its body conjuncts become facts, and the obligation body must then
/// certify pointwise. Only the alpha-equal existentials, read from the
/// identity bucket, are tried; across the gate and the unit tests they were
/// the only ones that ever certified, and trying every other existential of
/// the sort was a search for which one to use.
pub(in crate::kernel) fn certification_proves_exists_obligation_from_facts(
    assumptions: &PureFactContext,
    obligation: &Proposition,
) -> bool {
    let Proposition::Exists {
        var, sort, body, ..
    } = obligation
    else {
        return false;
    };
    let fact_candidates = assumptions
        .stated_identity_bucket(obligation)
        .cloned()
        .collect::<Vec<_>>();
    fact_candidates.iter().any(|fact| {
        let Proposition::Exists {
            var: fact_var,
            sort: fact_sort,
            body: fact_body,
            ..
        } = fact
        else {
            return false;
        };
        if fact_sort != sort {
            return false;
        }
        let Some(renamed) =
            substitute_quantified_body_capture_free(fact_body, *fact_var, *var, sort)
        else {
            return false;
        };
        let mut witness_facts = Vec::new();
        proposition_conjuncts(&renamed, &mut witness_facts);
        let witness_assumptions = assumptions_with_propositions(assumptions, &witness_facts);
        let mut goals = Vec::new();
        proposition_conjuncts(body, &mut goals);
        goals.iter().all(|goal| {
            PureFactContext::settles_exactly(&witness_assumptions, goal)
                || loadable_covered_by_fact(&witness_assumptions, goal)
                // Nested existentials recurse: the inner obligation matches
                // an inner assumed existential the same way.
                || certification_proves_exists_obligation_from_facts(&witness_assumptions, goal)
        })
    })
}

/// Renders a kernel runtime error for a certification diagnostic. Contract
/// errors carry a sentence written for the user; the structured variants have
/// no kernel-side rendering of their payload, so they are named by kind rather
/// than dumped as internal state.
pub(in crate::kernel) fn describe_certification_runtime_error(error: &RuntimeError) -> String {
    match error {
        RuntimeError::PointerConversion(message)
        | RuntimeError::EnumVariant(message)
        | RuntimeError::FunctionContract(message)
        | RuntimeError::UnsuppliedResourceValue(message) => {
            message.clone()
        }
        RuntimeError::PendingCallObligations(pending) => format!(
            "call cannot finish while {} proof obligation(s) remain", pending.len()
        ),
        RuntimeError::ContractResourceDiagnostic { reason, .. } => reason.clone(),
        RuntimeError::UnboundVariable(name) => format!("unbound variable `{name}`"),
        RuntimeError::UnknownFunction(name) => format!("unknown function `{name}`"),
        RuntimeError::MissingVerifiedFunctionRule(name) => {
            format!("the sidecar states no contract for `{name}`")
        }
        RuntimeError::UnsupportedOpaqueFunctionContract(name) => {
            format!("the contract of `{name}` refers to an unavailable program point")
        }
        RuntimeError::AbstractFunctionPointerCall(name) => {
            format!("no named contract is available for function pointer `{name}`")
        }
        RuntimeError::TypeMismatch => "type mismatch".to_string(),
        RuntimeError::HeapAllocationSize => RuntimeError::HEAP_ALLOCATION_SIZE_MESSAGE.to_string(),
        RuntimeError::HeapAllocationSizeAboveInt32 => {
            RuntimeError::HEAP_ALLOCATION_SIZE_ABOVE_INT32_MESSAGE.to_string()
        }
        RuntimeError::WideRangeRespellingMayWrap(no_wrap) => format!(
            "a range of {}-byte elements needs its endpoint times {} to not wrap (at most UINT64_MAX)",
            no_wrap
                .range
                .memory_range()
                .map_or(0, crate::kernel::MemoryRange::element_width),
            no_wrap.factor
        ),
        RuntimeError::LoadTypeMismatch { .. } => error.kernel_summary(),
        RuntimeError::IndeterminatePointeeType => {
            "a pointer operation has no known pointee type".to_string()
        }
        RuntimeError::WrongArity { expected, actual } => {
            format!("wrong argument count: expected {expected}, got {actual}")
        }
        RuntimeError::MissingReturn => "missing return".to_string(),
        RuntimeError::MutexStorageScopeEnd { local, .. } => format!("initialized mutex storage must outlive local `{local}`"),
        RuntimeError::MutexStorageInUse { .. } => "allocation storage still contains an initialized mutex".into(),
        RuntimeError::MutexStorageSeparationRequired { .. } => "requires separation between retired allocation and initialized mutex storage".into(),
        RuntimeError::MutexStorageWrite { .. } => "requires separation from initialized mutex storage".into(),
        RuntimeError::MissingMutexStorageAlignment { .. } => "requires aligned mutex storage".into(),
        RuntimeError::UnsupportedMutexStorageRetirement => "allocation retirement in a preserving guard contract needs checked mutex lifetime authority".into(),
        RuntimeError::MissingMutexGuard { .. } => {
            "a required mutex_guard resource is not available".to_string()
        }
        RuntimeError::MissingMutexLive { .. } => {
            "a required mutex_live resource is not available".to_string()
        }
        RuntimeError::MissingMutexUse { .. } => {
            "a required mutex_use resource is not available".to_string()
        }
        RuntimeError::MissingMutexInvariant { .. } => {
            "the protected resource selected at mutex initialization must be restored".to_string()
        }
        RuntimeError::MissingResource { .. } => "a required resource is not available".to_string(),
        RuntimeError::UnestablishedAssemblyFact { .. } => {
            "assembling a required view from the caller's bytes requires an exact body fact".to_string()
        }
        RuntimeError::UnbackedReturnedView { .. } => {
            RuntimeError::UNBACKED_RETURNED_VIEW.to_string()
        }
        RuntimeError::UninitializedMutex { .. } => {
            "the mutex has not been initialized on this path".to_string()
        }
        RuntimeError::UnsupportedConcurrentMutex => {
            "Click cannot yet verify pthread workers sharing an initialized mutex".to_string()
        }
        RuntimeError::InvalidFree(reason) => match reason {
            InvalidFree::InteriorPointer => {
                "cannot free an interior pointer; free requires the allocation base".to_string()
            }
            InvalidFree::NonHeapPointer => {
                "cannot free a pointer that is not a live heap allocation".to_string()
            }
            InvalidFree::DoubleFree => {
                "cannot free an allocation whose lifetime has already ended".to_string()
            }
        },
        RuntimeError::UnresolvedAllocationOutcome => {
            "an unresolved allocation outcome".to_string()
        }
        RuntimeError::LiveAllocationLeak { .. } => {
            "a live allocation is neither returned nor freed".to_string()
        }
        RuntimeError::StaleResourceAfterFree { .. } => {
            "a resource would remain usable after its allocation is freed".to_string()
        }
        RuntimeError::DuplicateResource { .. } => {
            "the same resource is declared twice".to_string()
        }
        RuntimeError::OverlappingOwnedMemoryResources { .. } => {
            "two owned memory resource clauses overlap".to_string()
        }
        RuntimeError::ProducedCompositeOverlapsHeldResource { .. } => {
            "a produced composite's body overlaps a resource the caller already holds".to_string()
        }
        RuntimeError::LoanRefusal(diagnostic) => format_loan_refusal_diagnostic(diagnostic),
    }
}

fn format_loan_refusal_diagnostic(diagnostic: &crate::kernel::LoanRefusalDiagnostic) -> String {
    format!(
        "stable-view {} refused: {}; {}{}",
        format_loan_operation(diagnostic.operation),
        format_loan_category(diagnostic.category),
        format_loan_subject(diagnostic),
        format_loan_ids(diagnostic),
    )
}

fn format_loan_category(category: crate::kernel::LoanRefusalCategory) -> &'static str {
    match category {
        crate::kernel::LoanRefusalCategory::ProvenOverlap => "a required resource overlaps",
        crate::kernel::LoanRefusalCategory::SeparationUnproved => {
            "resource separation was not proved"
        }
        crate::kernel::LoanRefusalCategory::WrongHolder => "the holder is wrong",
        crate::kernel::LoanRefusalCategory::WrongArena => "the authority arena is wrong",
        crate::kernel::LoanRefusalCategory::WrongScope => "the loan scope is wrong",
        crate::kernel::LoanRefusalCategory::ActiveDependency => "an active dependency remains",
        crate::kernel::LoanRefusalCategory::StalePredecessor => "the predecessor is stale",
        crate::kernel::LoanRefusalCategory::Recovery => "recovery evidence is invalid",
        crate::kernel::LoanRefusalCategory::Lifetime => "the loan lifetime is invalid",
        crate::kernel::LoanRefusalCategory::Unsupported => "the resource shape is unsupported",
        crate::kernel::LoanRefusalCategory::Missing => "loan backing or binding is missing",
        crate::kernel::LoanRefusalCategory::InvalidEvidence => "loan evidence is invalid",
    }
}

fn format_loan_subject(diagnostic: &crate::kernel::LoanRefusalDiagnostic) -> &'static str {
    let subject = diagnostic.subject();
    if subject.resource_fact().is_some() {
        "selected resource"
    } else if subject.memory_range().is_some() {
        "selected memory range"
    } else {
        "the selected loan boundary"
    }
}

fn format_loan_ids(diagnostic: &crate::kernel::LoanRefusalDiagnostic) -> String {
    let subject = diagnostic.subject();
    let mut ids = Vec::new();
    if let Some((arena, ordinal)) = subject.loan_id() {
        ids.push(format!("loan {arena}:{ordinal}"));
    }
    if let Some((arena, ordinal)) = subject.scope_id() {
        ids.push(format!("scope {arena}:{ordinal}"));
    }
    if let Some((arena, ordinal)) = subject.share_id() {
        ids.push(format!("share {arena}:{ordinal}"));
    }
    if let Some((arena, ordinal)) = subject.support_id() {
        ids.push(format!("support {arena}:{ordinal}"));
    }
    if let Some(clause) = diagnostic.source_clause() {
        ids.push(format!("clause {clause}"));
    }
    if let Some(step) = diagnostic.source_step() {
        ids.push(format!("step {step}"));
    }
    if ids.is_empty() {
        String::new()
    } else {
        format!(" ({})", ids.join(", "))
    }
}

fn format_loan_operation(operation: crate::kernel::LoanRefusalOperation) -> &'static str {
    match operation {
        crate::kernel::LoanRefusalOperation::Validate => "validation",
        crate::kernel::LoanRefusalOperation::Plan => "planning",
        crate::kernel::LoanRefusalOperation::Entry => "entry transition",
        crate::kernel::LoanRefusalOperation::Recovery => "recovery",
        crate::kernel::LoanRefusalOperation::Transition => "transition",
        crate::kernel::LoanRefusalOperation::MemoryAccess => "memory access",
    }
}

/// Where one fact of a function's contract entry comes from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ContractEntryFactOrigin {
    /// The type range of a narrow integer parameter, and the range of a
    /// `bool` parameter's cast (rule C1).
    NarrowRange,
    /// A fact the lowering of `requires` clause `index` produced beside it.
    RequirementLowering(usize),
    /// The lowered `requires` clause `index` itself.
    Requirement(usize),
    /// A bound on a counted population at entry.
    PopulationCount,
    /// A declared resource quantity.
    ResourceQuantity,
    /// Disjointness of the transferred and the borrowed entry clauses.
    Partition,
    /// A guard that a stated memory range's extent is well formed.
    Extent,
    /// Loadability of a stated clause range at the entry memory.
    ClauseLoadable,
    /// Initialized typed reads promised by an admitted input clause.
    ClauseInitialized,
    /// A declared fact of a composite resource the entry holds, at any depth.
    CompositeDefinition,
    /// A declared fact of a tracked population.
    PopulationFact,
    /// A verification condition of a lowered `requires` clause.
    RequirementObligation,
    /// A relation the expanded entry resources state: separation, containment.
    Observable,
    /// The facts of the instance arm the requirements select.
    Publication,
    /// The identity of a registered predicate whose body the entry holds.
    PredicateIdentity,
    /// A fact of `requires` clause `index` where that clause is the body of
    /// a registered predicate: what the predicate says once unfolded.
    PredicateBody(usize),
}

/// The subject captured by the entry producer; preparing cases consumes it
/// with its facts, so a caller cannot pair an entry with a different subject.
#[derive(Clone)]
struct ContractEntrySubject {
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
}

impl std::fmt::Debug for ContractEntrySubject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ContractEntrySubject")
            .field("function", &self.function.name())
            .field("arguments", &self.arguments.len())
            .finish_non_exhaustive()
    }
}

/// One fact a function may assume at entry, with where it comes from.
#[derive(Clone, Debug)]
pub struct ContractEntryFact {
    origin: ContractEntryFactOrigin,
    proposition: Proposition,
}

impl ContractEntryFact {
    pub fn origin(&self) -> ContractEntryFactOrigin {
        self.origin
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

struct ContractEntryFactLog(Vec<ContractEntryFact>);

impl ContractEntryFactLog {
    /// Assumes `proposition` and records it with its origin.
    fn assume(
        &mut self,
        assumptions: PureFactContext,
        origin: ContractEntryFactOrigin,
        proposition: Proposition,
    ) -> PureFactContext {
        self.0.push(ContractEntryFact {
            origin,
            proposition: proposition.clone(),
        });
        assumptions.assume_proposition(proposition)
    }
}

/// What a function may assume at its entry, built once from its contract.
///
/// The facts are the kernel's lowering of the contract at the entry state:
/// each `requires` clause, the ranges of its parameters, and what its entry
/// resources state. A caller applying the function's rule discharges this
/// same lowering, so a body proved from these facts is proved from what its
/// callers establish.
#[derive(Clone, Debug)]
pub struct ContractEntry {
    subject: ContractEntrySubject,
    assumptions: PureFactContext,
    facts: Vec<ContractEntryFact>,
    /// The propositions of `facts`, for membership.
    stated: BTreeSet<Proposition>,
    /// The entry state holding the contract's expanded entry resources.
    resources: ContractEntryResources,
}

#[derive(Clone, Debug)]
struct ContractEntryResources {
    state: ExecutionState,
    required: ResourceContext,
    checked: Arc<[crate::kernel::functions::CheckedResourceFact]>,
}

impl ContractEntry {
    /// The entry facts in the order the contract yields them.
    pub fn facts(&self) -> &[ContractEntryFact] {
        &self.facts
    }

    /// Whether this is an actual output of the entry producer. Selecting the
    /// proof's input premises must not promote alternate, derivable spellings
    /// into additional assumptions whose consequences need re-authorization.
    pub(crate) fn explicitly_states(&self, proposition: &Proposition) -> bool {
        self.stated.contains(proposition)
    }

    /// Whether the entry states `proposition`: it is one of the entry facts,
    /// a conjunction or resource composition of them, or one of them up to
    /// the names of its bound variables. A lookup, never a search.
    pub fn states(&self, proposition: &Proposition) -> bool {
        self.stated.contains(proposition)
            || self.assumptions.proves_exact(proposition)
            || self.assumptions.states_required_goal(proposition)
            || self.resources_supply(proposition)
    }

    /// Whether `proposition` is the loadability of memory the entry's
    /// resources hold.
    fn resources_supply(&self, proposition: &Proposition) -> bool {
        matches!(proposition, Proposition::MemoryLoadable { .. })
            && resources_certify_loadability(
                &self.resources.state,
                self.resources.state.resources(),
                proposition,
                &self.assumptions,
            )
    }
}

/// Builds the contract entry of `function` called with `arguments` at
/// `caller_state`, or says why the contract has none.
pub fn program_function_contract_entry(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
) -> Result<ContractEntry, String> {
    let (assumptions, facts, resources) =
        program_function_contract_entry_facts(caller_state, function, arguments)?;
    let predicate_bodies = function
        .contract_requires()
        .iter()
        .map(|requirement| {
            function
                .predicate_unfoldings()
                .iter()
                .any(|unfolding| unfolding.body() == requirement)
        })
        .collect::<Vec<_>>();
    let facts = facts
        .into_iter()
        .map(|mut fact| {
            if let ContractEntryFactOrigin::Requirement(index)
            | ContractEntryFactOrigin::RequirementLowering(index) = fact.origin
                && predicate_bodies.get(index) == Some(&true)
            {
                fact.origin = ContractEntryFactOrigin::PredicateBody(index);
            }
            fact
        })
        .collect();
    let mut entry_facts = ContractEntryFactLog(facts);
    // A `requires` clause that names a registered predicate is lowered to
    // the predicate's body. Each registered unfolding is definitional, so an
    // identity whose instantiated body and side obligations the entry proves
    // holds with it, and is the form a proof names.
    let mut identities = Vec::new();
    if let Some(entry_state) = program_function_entry_state(caller_state, function, arguments) {
        let mut budget = ExecutionBudget::for_new_execution();
        for unfolding in function.predicate_unfoldings() {
            let Some((predicate, body)) = instantiate_contract_predicate_unfolding(
                &entry_state,
                unfolding,
                &assumptions,
                &mut budget,
            ) else {
                continue;
            };
            if PureFactContext::settles_exactly(&assumptions, &body) {
                identities.push(predicate);
            }
        }
    }
    let assumptions = identities
        .into_iter()
        .fold(assumptions, |assumptions, identity| {
            entry_facts.assume(
                assumptions,
                ContractEntryFactOrigin::PredicateIdentity,
                identity,
            )
        });
    let stated = entry_facts
        .0
        .iter()
        .map(|fact| fact.proposition.clone())
        .collect();
    Ok(ContractEntry {
        subject: ContractEntrySubject {
            state: caller_state.clone(),
            function: function.clone(),
            arguments: arguments.to_vec(),
        },
        assumptions,
        facts: entry_facts.0,
        stated,
        resources,
    })
}

/// Builds the assumptions an exact contract certification runs under, or says
/// why it could not. The failure text is reported to the user: certification
/// with no paths and no reason is a dead end for whoever wrote the contract,
/// so every exit below names what stopped it.
fn program_function_contract_entry_facts(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
) -> Result<
    (
        PureFactContext,
        Vec<ContractEntryFact>,
        ContractEntryResources,
    ),
    String,
> {
    let mut assumptions = PureFactContext::new();
    let mut entry_facts = ContractEntryFactLog(Vec::new());
    if let Some(message) =
        crate::kernel::functions::guard_contract_refusal(function.contract_interface())
    {
        return Err(message.into());
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let Some(mut entry_state) = program_function_entry_state(caller_state, function, arguments)
    else {
        return Err("could not build the contract entry state from the call arguments".to_string());
    };
    if function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some())
    {
        let argument_values = arguments
            .iter()
            .map(|argument| match argument {
                ProgramExpression::Value(value) => Some(value.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                "an aggregate contract argument is not a value at the contract entry".to_string()
            })?;
        entry_state = match prepare_function_contract_entry_state_with_values(
            caller_state,
            function,
            &argument_values,
            &assumptions,
            &mut budget,
        ) {
            Ok(Ok(state)) => state,
            Ok(Err(error)) => {
                return Err(format!(
                    "could not build the aggregate contract entry state: {}",
                    describe_certification_runtime_error(&error)
                ));
            }
            Err(limit) => {
                return Err(format!(
                    "building the aggregate contract entry state stopped at {}",
                    limit.describe()
                ));
            }
        };
    }
    // Rust slices and fixed array references are valid bounded references,
    // even when the contract observes only metadata. This supplies no readable bytes.
    for parameters in [
        function.parameters(),
        function.contract_interface().value_parameters(),
    ] {
        for (index, parameter) in parameters.iter().enumerate() {
            if let Some(bytes) = parameter.fixed_reference_extent {
                let pointer_value = entry_state.locals.get_native(parameter.name());
                let Some(ProgramValue::Pointer(pointer)) = pointer_value.as_deref() else {
                    return Err("array reference entry argument is not a pointer value".into());
                };
                if let Some(coverage) = pointer.opaque_coverage_fact(&MemoryRange::new_wide(
                    pointer.pointer().clone(),
                    MachineTerm::uint64_constant(0),
                    MachineTerm::uint64_constant(u64::from(bytes)),
                    1,
                )) {
                    assumptions =
                        entry_facts.assume(assumptions, ContractEntryFactOrigin::Extent, coverage);
                }
            }
            let Some(length_index) = parameter.slice_length_parameter else {
                continue;
            };
            let pointer_value = entry_state.locals.get_native(parameter.name());
            let Some(ProgramValue::Pointer(pointer)) = pointer_value.as_deref() else {
                return Err("slice entry argument is not a pointer value".into());
            };
            let length_parameter = &parameters[index + length_index];
            let length_value = entry_state.locals.get_native(length_parameter.name());
            let Some(ProgramValue::UInt64(length)) =
                length_value.as_deref().map(ProgramValue::numeric_value)
            else {
                return Err("slice entry length is not a native unsigned value".into());
            };
            let width = parameter
                .program_type()
                .pointee_type()
                .expect("slice pointer")
                .byte_width();
            assumptions = entry_facts.assume(
                assumptions,
                ContractEntryFactOrigin::Extent,
                Proposition::ConditionIs(
                    ConditionTerm::uint64_less_equal(
                        length.clone(),
                        MachineTerm::uint64_constant(i64::MAX as u64 / u64::from(width)),
                    ),
                    true,
                ),
            );
            if let Some(coverage) = pointer.opaque_coverage_fact(&MemoryRange::new_wide(
                pointer.pointer().clone(),
                MachineTerm::uint64_constant(0),
                length.clone(),
                width,
            )) {
                assumptions =
                    entry_facts.assume(assumptions, ContractEntryFactOrigin::Extent, coverage);
            }
        }
    }
    // A `bool` parameter's cast holds 0 or 1 (rule C1b). A narrow integer
    // parameter is a value of its own format, whose range is the format's.
    for argument in arguments {
        if let ProgramExpression::Value(value) = argument
            && let Some(facts) = program_bool_cast_range_facts(value)
        {
            for fact in facts {
                assumptions =
                    entry_facts.assume(assumptions, ContractEntryFactOrigin::NarrowRange, fact);
            }
        }
    }
    let mut requirement_obligations = Vec::new();
    for (requirement_index, requirement) in function.contract_requires().iter().enumerate() {
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads()
            .assume_entry_clause_extents();
        let paths = match lower_spec_proposition_at_state_with_loop_entry(
            &entry_state,
            requirement,
            None,
            &lowering_assumptions,
            &mut budget,
        ) {
            Ok(paths) => paths,
            Err(limit) => {
                if crate::instrumentation::enabled() {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::Diagnostic(format!(
                            "contract requirement lowering stopped at {} for {}",
                            limit.describe(),
                            function.name()
                        )),
                    );
                }
                return Err(format!(
                    "lowering `requires` clause {} stopped at {}",
                    requirement_index + 1,
                    limit.describe()
                ));
            }
        };
        let path = if let [path] = paths.as_slice() {
            path
        } else {
            let proposition_matches = paths
                .iter()
                .filter(|path| assumptions.proves_exact(&path.proposition))
                .collect::<Vec<_>>();
            if let [path] = proposition_matches.as_slice() {
                *path
            } else {
                let consistent = paths
                    .iter()
                    .filter(|path| {
                        !assumptions_with_propositions(
                            &assumptions,
                            &path
                                .facts
                                .iter()
                                .map(|fact| fact.proposition().clone())
                                .collect::<Vec<_>>(),
                        )
                        .is_inconsistent()
                    })
                    .collect::<Vec<_>>();
                let [path] = consistent.as_slice() else {
                    if crate::instrumentation::enabled() {
                        crate::instrumentation::emit(
                            crate::instrumentation::VerificationEvent::Diagnostic(format!(
                                "contract requirement for {} lowered to {} paths; {} are already stated and {} remained consistent",
                                function.name(),
                                paths.len(),
                                proposition_matches.len(),
                                consistent.len(),
                            )),
                        );
                    }
                    return Err(format!(
                        "`requires` clause {} lowered to {} paths, of which {} are already \
                         stated and {} stayed consistent; the contract entry needs exactly one",
                        requirement_index + 1,
                        paths.len(),
                        proposition_matches.len(),
                        consistent.len(),
                    ));
                };
                *path
            }
        };
        for obligation in &path.obligations {
            if !requirement_obligations.contains(obligation) {
                requirement_obligations.push(obligation.clone());
            }
        }
        for fact in &path.facts {
            assumptions = entry_facts.assume(
                assumptions,
                ContractEntryFactOrigin::RequirementLowering(requirement_index),
                fact.proposition().clone(),
            );
        }
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::Requirement(requirement_index),
            path.proposition.clone(),
        );
    }
    let quantity_assumptions = match quantified_resource_requirement_assumptions(
        &entry_state,
        function.resource_requires(),
        function.composite_resource_definitions(),
        &assumptions,
        &mut budget,
    ) {
        Ok(Ok(assumptions)) => assumptions,
        Ok(Err(error)) => {
            return Err(format!(
                "could not evaluate a declared resource quantity in the contract entry \
                 resources: {}",
                describe_certification_runtime_error(&error)
            ));
        }
        Err(limit) => {
            return Err(format!(
                "evaluating the declared resource quantities of the contract entry resources \
                 stopped at {}",
                limit.describe()
            ));
        }
    };
    for proposition in quantity_assumptions {
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::ResourceQuantity,
            proposition,
        );
    }
    // The trusted contract-entry builder creates its admissible premise context.
    // Attach the selected caller input to that context once, before the
    // contract clauses are evaluated; clause reads never publish a frame.
    caller_state
        .resources()
        .synchronize_memory_equalities(&assumptions);
    entry_state
        .resources()
        .synchronize_memory_equalities(&assumptions);
    let (required_resources, required_entry_clauses) =
        match evaluate_function_resource_context_with_metadata(
            &entry_state,
            function.resource_requires(),
            function.composite_resource_definitions(),
            &assumptions.clone().assume_entry_clause_extents(),
            &mut budget,
        ) {
            Ok(Ok(evaluated)) => evaluated,
            Ok(Err(error)) => {
                return Err(format!(
                    "could not evaluate the contract entry resources: {}",
                    describe_certification_runtime_error(&error)
                ));
            }
            Err(limit) => {
                return Err(format!(
                    "evaluating the contract entry resources stopped at {}",
                    limit.describe()
                ));
            }
        };
    // The entry partition: a transferred clause and a borrowed `views`
    // clause of this contract denote disjoint memory. The proof side spells
    // the same facts from the same clause list
    // (`evaluate_entry_resource_context`) and keeps the ones this entry
    // states. `functions::contract_entry_partition_facts` carries the rule
    // and its soundness argument; the fail-closed call-site planner is what
    // discharges the claim, so a caller owes nothing extra for it.
    for fact in crate::kernel::contract_entry_partition_facts(&required_entry_clauses) {
        assumptions = entry_facts.assume(assumptions, ContractEntryFactOrigin::Partition, fact);
    }
    // Each clause states its own range, and the proof side holds each one as
    // written: its byte-count guards and its loadability at entry. The
    // required context below may have joined two clauses that abut, such as
    // `x[0..(i + 1)]` and `x[j..(j + 1)]` under `i + 1 == j`, into one range
    // whose guards no longer mention either clause's bounds; recovering
    // `0 <= j` or `viewable(x[j..(j + 1)])` from `x[0..(j + 1)]` would need
    // order reasoning through that equality. The joined range is exactly
    // the union of the clauses, so each clause's own facts hold of it.
    for clause in &required_entry_clauses {
        let Some(range) = clause
            .fact
            .memory_view_range()
            .or_else(|| clause.fact.memory_own_range())
        else {
            continue;
        };
        let mut well_formed = true;
        for guard in crate::kernel::admitted_memory_range_extent_facts(range) {
            let guard_is_false = match &guard {
                Proposition::ConditionIs(condition, true) => {
                    assumptions.decide(condition) == Some(false)
                }
                _ => false,
            };
            if guard_is_false {
                well_formed = false;
            } else {
                assumptions =
                    entry_facts.assume(assumptions, ContractEntryFactOrigin::Extent, guard);
            }
        }
        // A range its own guards refute states no memory to read.
        if !well_formed {
            continue;
        }
        // Active clauses have already been evaluated, retaining their source
        // index and entry range. Publish the contract's initialization promise
        // once, without evaluating its base or enumerating its cells again.
        if let Some(segment) = clause
            .section_index
            .and_then(|index| function.resource_requires().get(index))
            .and_then(|resource| resource.term().memory_segment())
            && let Some(fact) = input_initialization::initialized_input_range_fact(
                &entry_state,
                function.contract_interface(),
                segment,
                range,
            )?
        {
            assumptions = entry_facts.assume(
                assumptions,
                ContractEntryFactOrigin::ClauseInitialized,
                fact,
            );
        }
        // A wide range states the wide liveness fact.
        if range.wide_bounds().is_some() {
            assumptions = entry_facts.assume(
                assumptions,
                ContractEntryFactOrigin::ClauseLoadable,
                range.loadable_fact(entry_state.memory()),
            );
            continue;
        }
        let width = range.element_width();
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::ClauseLoadable,
            Proposition::MemoryLoadable {
                memory: entry_state.memory().clone(),
                base: range
                    .base()
                    .offset_by_elements(range.start().clone(), width),
                bytes: MachineTerm::multiply(
                    MachineTerm::subtract(range.end().clone(), range.start().clone()),
                    MachineTerm::constant(width),
                ),
                wide: false,
            },
        );
    }
    for fact in required_resources.facts() {
        if let Some(coverage) = fact.allocation_bounds_fact(&assumptions) {
            assumptions =
                entry_facts.assume(assumptions, ContractEntryFactOrigin::Extent, coverage);
        }
        // Owned ranges carry their byte-count guards exactly as viewed ranges
        // do: the clause states the same range, and the loadability rules read
        // both at element granularity.
        let Some(range) = fact.memory_view_range().or_else(|| fact.memory_own_range()) else {
            continue;
        };
        for guard in crate::kernel::admitted_memory_range_extent_facts(range) {
            let guard_is_false = match &guard {
                Proposition::ConditionIs(condition, true) => {
                    assumptions.decide(condition) == Some(false)
                }
                _ => false,
            };
            if !guard_is_false {
                assumptions =
                    entry_facts.assume(assumptions, ContractEntryFactOrigin::Extent, guard);
            }
        }
    }
    // A declared fact may read a tracked population (`count(...)`), which
    // only the entry state holds, so the facts are evaluated at the state.
    let expanded =
        super::super::functions::expand_all_composite_resource_facts_and_propositions_at_state(
            &required_resources,
            function.composite_resource_definitions(),
            &entry_state,
            &assumptions,
        );
    let (expanded_resources, resource_definition_facts) = expanded.ok_or_else(|| {
        "could not evaluate the composite resource facts required at the contract entry".to_string()
    })?;
    // A composite's contained ranges are stated ranges too, and their
    // byte-count guards ride with the composite wherever it is held. Install
    // them here as well, so what the certified entry context knows about an
    // expanded range matches what the proof side installed for it.
    for fact in expanded_resources.facts() {
        if let Some(coverage) = fact.allocation_bounds_fact(&assumptions) {
            assumptions =
                entry_facts.assume(assumptions, ContractEntryFactOrigin::Extent, coverage);
        }
        let Some(range) = fact.memory_view_range().or_else(|| fact.memory_own_range()) else {
            continue;
        };
        for guard in crate::kernel::admitted_memory_range_extent_facts(range) {
            let guard_is_false = match &guard {
                Proposition::ConditionIs(condition, true) => {
                    assumptions.decide(condition) == Some(false)
                }
                _ => false,
            };
            if !guard_is_false {
                assumptions =
                    entry_facts.assume(assumptions, ContractEntryFactOrigin::Extent, guard);
            }
        }
    }
    for proposition in resource_definition_facts {
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::CompositeDefinition,
            proposition,
        );
    }
    let population_facts = evaluate_resource_population_fact_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        &entry_state,
        &assumptions,
    )
    .ok_or_else(|| {
        "could not evaluate the tracked populations of the contract entry resources".to_string()
    })?;
    for fact in population_facts {
        assumptions =
            entry_facts.assume(assumptions, ContractEntryFactOrigin::PopulationFact, fact);
    }
    let expanded_required_resources = ({
        super::super::functions::expand_all_composite_resource_facts_at_state(
            &required_resources,
            function.composite_resource_definitions(),
            &entry_state,
            &assumptions,
        )
    })
    .ok_or_else(|| {
        "could not expand the composite resource ownership required at the contract entry"
            .to_string()
    })?;
    let mut entry_resources = {
        super::super::functions::expand_all_composite_resource_facts_at_state(
            entry_state.resources(),
            function.composite_resource_definitions(),
            &entry_state,
            &assumptions,
        )
        .ok_or("could not project the checked authority control at contract entry")?
    }
    .normalized(&assumptions);
    let mut missing = Vec::new();
    for (index, required) in expanded_required_resources.facts().iter().enumerate() {
        let exposed = expose_composite_resource_fact(
            &entry_resources,
            required,
            function.composite_resource_definitions(),
            entry_state.memory(),
            &assumptions,
        )
        .or_else(|| {
            let Resource::Memory(required_range) = required.resource() else {
                return None;
            };
            let has_same_base = entry_resources.facts().iter().any(|available| {
                let Resource::Memory(available_range) = available.resource() else {
                    return false;
                };
                crate::kernel::assumptions::pointers_equal_ignoring_memories(
                    available_range.base(),
                    required_range.base(),
                )
            });
            (has_same_base && entry_resources.satisfies_fact(required, &assumptions))
                .then(|| entry_resources.clone())
        })
        .or_else(|| {
            // Expanding the authority entry opens every held composite one
            // level, including a viewed child the entry already projected.
            // A view is duplicable, so the unexpanded entry still holding
            // it satisfies the requirement and consumes nothing.
            (required.is_view()
                && entry_state
                    .resources()
                    .satisfies_fact(required, &assumptions))
            .then(|| entry_resources.clone())
        });
        let Some(exposed) = exposed else {
            missing.push((index, required));
            continue;
        };
        entry_resources = exposed;
    }
    if !missing.is_empty() {
        let missing = missing
            .into_iter()
            .map(|(index, required)| {
                let kind = match required.resource() {
                    Resource::Emp => "separation::emp".into(),
                    Resource::Star(_) => "separating conjunction".into(),
                    Resource::Footprint(fp) => fp.source.clone(),
                    Resource::Parameter(v) => format!("resource parameter {v:?}"),
                    Resource::Memory(range) => {
                        format!("memory in {}", range.base().block)
                    }
                    Resource::PopulationAuthority(description) => {
                        format!("population authority for {}", description.family())
                    }
                    Resource::Composite { name, .. } => format!("composite {name}"),
                    Resource::Token { name, .. } => format!("token {name}"),
                    Resource::MutexGuard(_) => "mutex guard".to_string(),
                    Resource::MutexLive(_) => "mutex lifetime".to_string(),
                    Resource::MutexUse(_) => "mutex use".to_string(),
                    Resource::Publication(_) => "publication right".to_string(),
                    Resource::Instance(instance) => format!("instance {}", instance.name()),
                    Resource::Iterated(iterated) => {
                        format!("iterated ownership of {}", iterated.owner())
                    }
                };
                format!("{index}: {kind}")
            })
            .collect::<Vec<_>>();
        let detail = format!(
            "the caller's resources do not satisfy the contract entry requirements ({}/{}, \
             missing {})",
            entry_resources.facts().len(),
            expanded_required_resources.facts().len(),
            missing.join(", ")
        );
        if crate::instrumentation::enabled() {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                detail.clone(),
            ));
        }
        return Err(detail);
    }
    // An owned declared resource or authority witnesses its population's
    // count. Expose the count facts the checked ledger derives for it to
    // independent contract certification; the surface `observe` tactic names
    // the same invariant for proof scripts.
    for required in required_resources.facts() {
        if required.owned_quantity_term().is_none() {
            continue;
        }
        let (name, arguments) = match required.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                continue;
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                (name.as_str(), arguments.as_ref())
            }
            Resource::PopulationAuthority(description) => {
                (description.family(), description.arguments())
            }
            Resource::Instance(instance) => (instance.name(), instance.arguments()),
            Resource::Memory(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_) => continue,
        };
        // Retain the same authenticated population facts as a written
        // count requirement. Owning a member entails its lower bound even
        // when the contract first mentions count in a postcondition.
        let Some(mut arguments) = arguments
            .iter()
            .map(|argument| {
                let AlgebraicValue::Program(value) = argument else {
                    return None;
                };
                Some(Some(SpecExpression::Value(value.clone())))
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        if let Resource::PopulationAuthority(description) = required.resource()
            && let Some(arity) = description.population_arity()
        {
            arguments.resize(arity, None);
        }
        // A concrete member also witnesses the anchored wildcard total.
        // Evaluate both observations through the checked ledger rather than
        // equating either total to the helper's locally owned quantity.
        let mut observations = vec![arguments.clone()];
        if arguments.len() > 1 && arguments[1..].iter().any(Option::is_some) {
            let mut wildcard = vec![None; arguments.len()];
            wildcard[0] = arguments[0].clone();
            observations.push(wildcard);
        }
        for arguments in observations {
            let expression = SpecExpression::CountedResourceCount {
                name: name.to_owned(),
                arguments,
            };
            let Ok(paths) = crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
                &entry_state,
                &expression,
                &assumptions,
                &BTreeMap::new(),
                &mut budget,
            ) else {
                continue;
            };
            let [path] = paths.as_slice() else {
                continue;
            };
            if !path.obligations.iter().all(|obligation| {
                PureFactContext::settles_exactly(&assumptions, obligation.proposition())
            }) {
                continue;
            }
            for fact in &path.facts {
                assumptions = entry_facts.assume(
                    assumptions,
                    ContractEntryFactOrigin::PopulationCount,
                    fact.proposition().clone(),
                );
            }
        }
    }
    if !requirement_obligations.iter().all(|obligation| {
        // Definedness travels with the assumption. A heap-dependent
        // `requires` cannot be true in a state where its loads do not
        // denote, so assuming the requirement already entails the
        // loadability its evaluation needed: the caller had to establish
        // the requirement, and the same obligations are proof obligations
        // on the caller's side (see the path-obligation check in
        // `prepare_function_claim_path`; only counted-population
        // post-transition conditions are deferred to result-aware surface
        // finalization).
        //
        // Arithmetic domains are mandatory at the call/use site; unlike a
        // ranking or conversion certificate they also belong to the stated
        // precondition being assumed here. The caller's requirement path
        // retains them as mandatory obligations.
        if obligation.is_assumable() || obligation.evaluation_domain {
            return true;
        }

        assumptions.proves_exact(obligation.proposition())
            || resources_certify_loadability(
                &entry_state,
                &entry_resources,
                obligation.proposition(),
                &assumptions,
            )
            || loadable_covered_by_fact(&assumptions, obligation.proposition())
            || forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
            || certification_proves_exists_obligation_from_facts(
                &assumptions,
                obligation.proposition(),
            )
    }) {
        if crate::instrumentation::enabled() {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                "contract entry resources do not certify requirement safety".to_string(),
            ));
        }
        return Err(
            "the contract entry resources do not show that every `requires` clause is safe to \
             evaluate"
                .to_string(),
        );
    }
    for obligation in requirement_obligations {
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::RequirementObligation,
            obligation.proposition().clone(),
        );
    }
    let observable_facts = entry_resources
        .observable_facts(&assumptions)
        .map_err(|error| {
            let detail = match error {
                ResourceContextValidityError::DuplicateOwnedResourceFact(_) => {
                    "the same resource is owned twice"
                }
                ResourceContextValidityError::InvalidExclusiveAccess(_) => {
                    "a field-bearing resource instance or mutex guard is not owned exclusively"
                }
                ResourceContextValidityError::OverlappingOwnedMemoryResources { .. } => {
                    "two owned memory resources overlap"
                }
            };
            format!("the contract entry resources are not a valid context: {detail}")
        })?;
    for proposition in observable_facts {
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::Observable,
            proposition,
        );
    }
    // Expansion replaces an unconditional composite by its body members, so
    // the composition above no longer names that composite. A proof still
    // holds the composite as one owner beside the other entry resources;
    // state that partition too, so its separation from them is available.
    for proposition in entry_state
        .resources()
        .observable_facts_assuming_valid(&assumptions)
    {
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::Observable,
            proposition,
        );
    }
    entry_state = entry_state.with_resource_context(entry_resources.clone());
    // The contract-entry publication: the arms the requirements refute and
    // the facts of the arm they leave, which a proof starts from as part of
    // the entry.
    let publication = crate::kernel::publish_instance_arms(
        &entry_resources,
        function.composite_resource_definitions(),
        &entry_state,
        &assumptions,
    );
    for proposition in publication
        .model_facts
        .into_iter()
        .chain(publication.arm_facts)
    {
        assumptions = entry_facts.assume(
            assumptions,
            ContractEntryFactOrigin::Publication,
            proposition,
        );
    }
    Ok((
        assumptions,
        entry_facts.0,
        ContractEntryResources {
            state: entry_state,
            required: required_resources,
            checked: required_entry_clauses.into(),
        },
    ))
}

pub(super) fn instantiate_contract_predicate_unfolding(
    entry_state: &ExecutionState,
    unfolding: &PredicateUnfolding,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<(Proposition, Proposition)> {
    let (predicate, predicate_obligations, body, body_obligations) =
        instantiate_contract_predicate_unfolding_with_obligations(
            entry_state,
            None,
            unfolding,
            assumptions,
            budget,
        )?;
    predicate_obligations
        .iter()
        .chain(&body_obligations)
        .all(|obligation| assumptions.proves_exact(obligation))
        .then_some((predicate, body))
}

/// Lowers a registered predicate and its body at `state`; `entry_state` is
/// the function entry an `old(...)` argument refers to when the predicate is
/// instantiated at a post-state.
pub(super) fn instantiate_contract_predicate_unfolding_with_obligations(
    state: &ExecutionState,
    entry_state: Option<&ExecutionState>,
    unfolding: &PredicateUnfolding,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<(Proposition, Vec<Proposition>, Proposition, Vec<Proposition>)> {
    let lower = |spec: &SpecProposition, budget: &mut ExecutionBudget| {
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            state,
            spec,
            entry_state,
            &lowering_assumptions,
            budget,
        )
        .ok()?;
        let [path] = paths.as_slice() else {
            return None;
        };
        Some((
            path.proposition.clone(),
            path.obligations
                .iter()
                .map(|obligation| obligation.proposition().clone())
                .collect(),
        ))
    };
    let (predicate, predicate_obligations) = lower(&unfolding.predicate, budget)?;
    let (body, body_obligations) = lower(&unfolding.body, budget)?;
    Some((predicate, predicate_obligations, body, body_obligations))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_symbolic_program_function_verification_paths(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    assumptions: PureFactContext,
    environment: ExecutionEnvironment,
    execution_semantics: ExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
    defer_conditional_resource_effect: bool,
) -> SymbolicExecution {
    let existing = crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "kernel variable collection",
        || {
            let mut existing = BTreeSet::new();
            collect_execution_state_bitvector_variables(&state, &mut existing);
            collect_program_function_bitvector_variables(&function, &mut existing);
            for argument in &arguments {
                collect_program_expression_bitvector_variables(argument, &mut existing);
            }
            collect_assumption_variables(&assumptions, &mut existing);
            collect_execution_environment_variables(&environment, &mut existing);
            existing
        },
    );
    let mut variables = KernelVariableGenerator::fresh_for_execution(existing);
    let paths = match crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "verification path execution",
        || {
            execute_program_function_verification_paths(
                &state,
                &function,
                &arguments,
                &assumptions,
                ExecutionContext::new(&environment, execution_semantics),
                &mut budget,
                &mut variables,
                prepare_contract_resources,
                defer_conditional_resource_effect,
            )
        },
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "checked path theorem assembly",
        || {
            paths
                .into_iter()
                .map(|path| {
                    let effect_facts = memory_effect_execution_facts(&path.facts);
                    let facts = public_execution_pure_facts(&path.facts);
                    let proposition = Proposition::ProgramFunctionVerifies {
                        state: Box::new(state.clone()),
                        function: Box::new(function.clone()),
                        arguments: arguments.clone(),
                        outcome: path.outcome,
                    };
                    let theorem = Theorem::new(wrap_proof_facts(
                        proposition,
                        &assumptions,
                        &facts,
                        &path.obligations,
                    ));
                    SymbolicExecutionPath {
                        call_parameters: None,
                        completion_origin: None,
                        call_result: None,
                        assumptions: assumptions.clone(),
                        post_assumptions: None,
                        facts,
                        effect_facts,
                        obligations: path.obligations,
                        theorem,
                        loan_evidence: path.loan_evidence,
                    }
                })
                .collect()
        },
    );

    SymbolicExecution { paths, limit: None }
}

pub fn program_function_execution_candidates_from_outcomes(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    paths: Vec<(
        FunctionOutcome,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    )>,
) -> FunctionExecutionCandidates {
    program_function_execution_candidates_from_outcomes_with_loan_evidence(
        state,
        function,
        arguments,
        paths
            .into_iter()
            .map(|(outcome, facts, obligations)| {
                (
                    outcome,
                    facts.into(),
                    obligations,
                    crate::kernel::loans::empty_checked_loan_evidence_sequence(),
                )
            })
            .collect(),
    )
}

pub(crate) fn program_function_execution_candidates_from_outcomes_with_loan_evidence(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    paths: Vec<(
        FunctionOutcome,
        ExecutionFacts,
        Vec<ProofObligation>,
        crate::kernel::loans::CheckedLoanCallEvidenceSequence,
    )>,
) -> FunctionExecutionCandidates {
    let paths: Vec<_> = paths
        .into_iter()
        .map(|(outcome, facts, obligations, loan_evidence)| {
            let effect_facts = memory_effect_execution_facts(&facts);
            let facts = public_execution_pure_facts(&facts);
            FunctionExecutionCandidate {
                data: Arc::new(FunctionExecutionCandidateData {
                    outcome: Arc::new(outcome),
                    facts,
                    effects_public_first: execution_effects_are_public_first(&effect_facts),
                    effect_facts,
                    obligations: Arc::new(obligations),
                    loan_evidence,
                }),
            }
        })
        .collect();
    program_function_execution_candidates_from_retained_paths(state, function, arguments, paths)
}

/// Re-publish immutable untrusted candidates without copying their outcome
/// states or re-classifying their already partitioned fact streams.
pub(crate) fn program_function_execution_candidates_from_retained_paths(
    state: ExecutionState,
    function: ProgramFunction,
    arguments: Vec<ProgramExpression>,
    paths: Vec<FunctionExecutionCandidate>,
) -> FunctionExecutionCandidates {
    #[cfg(test)]
    ExecutionFacts::record_published_storage(
        false,
        paths.len(),
        paths
            .iter()
            .flat_map(|path| [path.facts(), path.effect_facts()]),
    );
    FunctionExecutionCandidates {
        data: std::sync::Arc::new(FunctionExecutionCandidatesData {
            state,
            function: Arc::new(function),
            arguments: Arc::new(arguments),
            common_facts: (paths.len() == 1).then(|| paths[0].facts().clone()),
            paths: paths.into(),
        }),
    }
}

/// Retain disjoint, checked arm publications as vector subtrees. This is
/// still untrusted candidate data; trace completion certifies every outcome.
pub(crate) fn concat_retained_function_candidates(
    state: ExecutionState,
    arms: [&FunctionExecutionCandidates; 2],
    common_facts: ExecutionFacts,
) -> FunctionExecutionCandidates {
    let mut paths = arms[0].data.paths.clone();
    paths.append_shared(&arms[1].data.paths);
    FunctionExecutionCandidates {
        data: Arc::new(FunctionExecutionCandidatesData {
            state,
            function: arms[0].data.function.clone(),
            arguments: arms[0].data.arguments.clone(),
            paths,
            common_facts: Some(common_facts),
        }),
    }
}

fn execution_effects_are_public_first(facts: &ExecutionFacts) -> bool {
    let mut private_seen = false;
    for fact in facts {
        if fact.is_public() {
            if private_seen {
                return false;
            }
        } else {
            private_seen = true;
        }
    }
    true
}

/// Classify only the new suffix. The caller has already suppressed identical
/// facts against the candidate's combined execution facts, just as it does
/// before publishing a fresh outcome. Preserve re-publication's public-then-
/// private effect order without re-classifying the complete guard stream.
/// All certification remains independent.
pub(crate) fn program_function_execution_candidate_with_additional_facts(
    candidate: &FunctionExecutionCandidate,
    additional: &ExecutionFacts,
) -> FunctionExecutionCandidate {
    if additional.is_empty() && candidate.data.effects_public_first {
        return candidate.clone();
    }
    let public = public_execution_pure_facts(additional);
    let added_effects = memory_effect_execution_facts(additional);
    let mut data = candidate.data.as_ref().clone();
    data.facts.extend_shared(&public);
    if !data.effects_public_first {
        // The former reconstruction reads existing public facts first, then
        // private effects. New facts follow that combined existing stream.
        let mut effects = data.effect_facts.filtered(|fact| fact.is_public());
        effects.extend_shared(&data.effect_facts.filtered(|fact| !fact.is_public()));
        data.effect_facts = effects;
        data.effects_public_first = true;
    }
    if !added_effects.is_empty() {
        data.effect_facts.extend_shared(&added_effects);
        data.effects_public_first = execution_effects_are_public_first(&data.effect_facts);
    }
    FunctionExecutionCandidate {
        data: Arc::new(data),
    }
}

pub fn prove_program_function_satisfies_specification_from_symbolic_path(
    function: ProgramFunction,
    specification: FunctionSpecification,
    path: &SymbolicExecutionPath,
) -> Option<Theorem> {
    let mut proved = path.theorem().proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proved {
        premises.push(premise.as_ref().clone());
        proved = body;
    }
    let (state, proved_function, arguments, outcome, verifies) = match proved {
        Proposition::ProgramFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, false),
        Proposition::ProgramFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, true),
        _ => return None,
    };
    if **state != *specification.state()
        || **proved_function != function
        || arguments != specification.arguments()
        || outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let conclusion = if verifies {
        Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function: Box::new(function),
            specification: Box::new(specification),
        }
    } else {
        Proposition::ProgramFunctionSatisfiesSpecification {
            function: Box::new(function),
            specification: Box::new(specification),
        }
    };
    let proposition = requires
        .into_iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement), Box::new(body))
        });
    Some(Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(proposition, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    ))
}

fn certified_function_path_parts<'a>(
    function: &ProgramFunction,
    path: &'a SymbolicExecutionPath,
) -> Option<(
    &'a ExecutionState,
    &'a [ProgramExpression],
    &'a FunctionOutcome,
    PureFactContext,
)> {
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let (state, proved_function, arguments, outcome) = match proposition {
        Proposition::ProgramFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        }
        | Proposition::ProgramFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome),
        _ => return None,
    };
    if **proved_function != *function {
        return None;
    }
    // `path.assumptions` contains only entry premises. Execution facts are
    // body/post evidence and are added by claim preparation after required
    // entry resources and their definitions have been evaluated.
    Some((state, arguments, outcome, path.assumptions.clone()))
}

fn resource_contexts_definitionally_equal(
    function: &ProgramFunction,
    left_memory: &Memory,
    left: &ResourceContext,
    right_memory: &Memory,
    right: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    resource_contexts_definitionally_equal_with_definitions(
        function.composite_resource_definitions(),
        left_memory,
        left,
        right_memory,
        right,
        assumptions,
    )
}

pub(in crate::kernel) fn resource_contexts_definitionally_equal_with_definitions(
    composite_resource_definitions: &[CompositeResourceDefinition],
    left_memory: &Memory,
    left: &ResourceContext,
    right_memory: &Memory,
    right: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let relation_facts = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: relation facts",
        || {
            [(left, left_memory), (right, right_memory)]
                .into_iter()
                .flat_map(|(resources, memory)| {
                    resources.facts().iter().filter_map(move |fact| {
                        matches!(fact.resource(), Resource::Composite { .. })
                            .then(|| {
                                evaluate_composite_resource_relation_propositions(
                                    fact,
                                    composite_resource_definitions,
                                    memory,
                                    assumptions,
                                )
                            })
                            .flatten()
                    })
                })
                .flatten()
                .collect::<Vec<_>>()
        },
    );
    let enriched_assumptions = assumptions_with_propositions(assumptions, &relation_facts);
    let assumptions = &enriched_assumptions;
    let _assumptions_memo_scope =
        crate::kernel::assumptions::PureFactContextIdScope::enter(assumptions);
    let facts_directly_match = |left: &ResourceFact, right: &ResourceFact| match (left, right) {
        (ResourceFact::Own(left, left_quantity), ResourceFact::Own(right, right_quantity))
            if left_quantity == right_quantity =>
        {
            crate::kernel::assumptions::resources_equal_ignoring_memories(left, right)
                && resources_directly_match(left, right, assumptions)
        }
        (ResourceFact::View(left), ResourceFact::View(right)) => {
            crate::kernel::assumptions::resources_equal_ignoring_memories(left, right)
                && resources_directly_match(left, right, assumptions)
        }
        _ => false,
    };
    let directly_equal = |left: &ResourceContext, right: &ResourceContext| {
        left.facts().iter().all(|fact| {
            right
                .direct_match_candidates(fact)
                .any(|available| facts_directly_match(available, fact))
                || right.satisfies_fact(fact, assumptions)
        }) && right.facts().iter().all(|fact| {
            left.direct_match_candidates(fact)
                .any(|available| facts_directly_match(available, fact))
                || left.satisfies_fact(fact, assumptions)
        })
    };
    let definitionally_covers =
        |available: &ResourceContext, required: &ResourceContext, memory: &Memory| {
            required.facts().iter().all(|fact| {
                expose_composite_resource_fact(
                    available,
                    fact,
                    composite_resource_definitions,
                    memory,
                    assumptions,
                )
                .is_some()
            })
        };
    if crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: direct",
        || directly_equal(left, right),
    ) {
        return true;
    }
    if left_memory == right_memory
        && crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "resource equality: same-memory definitions",
            || {
                // Check the requested fold/unfold relation before searching
                // every combination of exposed composites. In particular an
                // unfolded child cannot expose its folded parent: consumption
                // checks that direction by the parent's definition directly.
                resource_contexts_definitionally_equivalent_by_consumption(
                    left,
                    right,
                    composite_resource_definitions,
                    left_memory,
                    assumptions,
                ) || (definitionally_covers(left, right, left_memory)
                    && definitionally_covers(right, left, left_memory))
            },
        )
    {
        return true;
    }
    let expanded_left = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: expand left",
        || {
            crate::kernel::functions::expand_all_composite_resource_facts_with_composites(
                left,
                composite_resource_definitions,
                left_memory,
                assumptions,
            )
        },
    );
    let expanded_right = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: expand right",
        || {
            crate::kernel::functions::expand_all_composite_resource_facts_with_composites(
                right,
                composite_resource_definitions,
                right_memory,
                assumptions,
            )
        },
    );
    let Some((expanded_left, left_composites)) = expanded_left else {
        return false;
    };
    let Some((expanded_right, right_composites)) = expanded_right else {
        return false;
    };
    // Comparing the fully opened contexts equates a composite on one side
    // with its pieces on the other. Holding a composite asserts its body
    // facts, so reading one side as the other reassembles every composite
    // the other side does not also hold, and each such composite's body
    // facts must hold in the memory of the side that has only its pieces.
    // A loop back edge otherwise returned `owns c(p)` from a body whose C
    // store had falsified a fact of `c` and never refolded it.
    let reassembly_holds = |composites: &[ResourceFact],
                            other: &ResourceContext,
                            other_composites: &[ResourceFact],
                            other_expanded: &ResourceContext,
                            other_memory: &Memory| {
        composites.iter().all(|composite| {
            other_composites.contains(composite)
                || other.satisfies_fact(composite, assumptions)
                || crate::kernel::functions::assembled_composite_body_facts_hold(
                    composite,
                    composite_resource_definitions,
                    other_memory,
                    other_expanded,
                    assumptions,
                )
        })
    };
    crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: expanded direct",
        || directly_equal(&expanded_left, &expanded_right),
    ) && reassembly_holds(
        &left_composites,
        right,
        &right_composites,
        &expanded_right,
        right_memory,
    ) && reassembly_holds(
        &right_composites,
        left,
        &left_composites,
        &expanded_left,
        left_memory,
    )
}

/// Structural equality up to renaming of bound variables at every quantifier
/// depth; bound variables are freshened per lowering pass, so nested
/// quantified facts never match syntactically.
fn fresh_alpha_comparison_variable(
    left_body: &Proposition,
    right_body: &Proposition,
    left_binder: Variable,
    right_binder: Variable,
) -> Variable {
    let mut reserved = proposition_variables(left_body);
    reserved.extend(proposition_variables(right_body));
    crate::kernel::reasoning::collect_proposition_bound_variables(left_body, &mut reserved);
    crate::kernel::reasoning::collect_proposition_bound_variables(right_body, &mut reserved);
    reserved.insert(left_binder);
    reserved.insert(right_binder);
    KernelVariableGenerator::fresh_for(0, reserved).next()
}

fn freshen_proposition_bodies(
    sort: &Sort,
    left_binder: Variable,
    left_body: &Proposition,
    right_binder: Variable,
    right_body: &Proposition,
) -> (Proposition, Proposition) {
    let fresh = fresh_alpha_comparison_variable(left_body, right_body, left_binder, right_binder);
    if matches!(
        sort,
        Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _)
    ) {
        let pointer = match sort {
            Sort::ProgramPointer(ProgramType::FunctionPointer(_)) => {
                Pointer::symbolic_function(fresh)
            }
            Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _) => Pointer::symbolic(fresh),
            _ => unreachable!("pointer freshening only handles pointer sorts"),
        };
        (
            substitute_pointer_variable_in_proposition(left_body, left_binder, &pointer),
            substitute_pointer_variable_in_proposition(right_body, right_binder, &pointer),
        )
    } else {
        (
            substitute_bitvector_variable_in_proposition(
                left_body,
                left_binder,
                &MachineTerm::Variable(fresh),
            ),
            substitute_bitvector_variable_in_proposition(
                right_body,
                right_binder,
                &MachineTerm::Variable(fresh),
            ),
        )
    }
}

pub(crate) fn propositions_alpha_equivalent_under_binders(
    sort: &Sort,
    left_binder: Variable,
    left_body: &Proposition,
    right_binder: Variable,
    right_body: &Proposition,
) -> bool {
    let (left_body, right_body) =
        freshen_proposition_bodies(sort, left_binder, left_body, right_binder, right_body);
    propositions_alpha_equivalent(&left_body, &right_body)
}

/// Aligns a quantified fact with a goal binder only when that target name is
/// not a free variable of the fact body. Reusing the goal binder otherwise
/// would capture an unrelated free variable; callers must reject that match.
pub(crate) fn substitute_quantified_body_capture_free(
    body: &Proposition,
    binder: Variable,
    target: Variable,
    sort: &Sort,
) -> Option<Proposition> {
    if binder != target && proposition_variables(body).contains(&target) {
        return None;
    }
    Some(
        if matches!(
            sort,
            Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _)
        ) {
            let pointer = match sort {
                Sort::ProgramPointer(ProgramType::FunctionPointer(_)) => {
                    Pointer::symbolic_function(target)
                }
                Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _) => {
                    Pointer::symbolic(target)
                }
                _ => unreachable!("pointer substitution only handles pointer sorts"),
            };
            substitute_pointer_variable_in_proposition(body, binder, &pointer)
        } else {
            substitute_bitvector_variable_in_proposition(
                body,
                binder,
                &MachineTerm::Variable(target),
            )
        },
    )
}

pub(crate) fn propositions_alpha_equivalent(left: &Proposition, right: &Proposition) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::Exists {
                var: left_var,
                sort: left_sort,
                body: left_body,
                ..
            },
            Proposition::Exists {
                var: right_var,
                sort: right_sort,
                body: right_body,
                ..
            },
        ) => {
            left_sort == right_sort && {
                let (left_body, right_body) = freshen_proposition_bodies(
                    left_sort, *left_var, left_body, *right_var, right_body,
                );
                propositions_alpha_equivalent(&left_body, &right_body)
            }
        }
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
                ..
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
                ..
            },
        ) => {
            left_sort == right_sort && {
                let (left_body, right_body) = freshen_proposition_bodies(
                    left_sort, *left_var, left_body, *right_var, right_body,
                );
                propositions_alpha_equivalent(&left_body, &right_body)
            }
        }
        (Proposition::And(al, ar), Proposition::And(bl, br))
        | (Proposition::Or(al, ar), Proposition::Or(bl, br))
        | (Proposition::Implies(al, ar), Proposition::Implies(bl, br)) => {
            propositions_alpha_equivalent(al, bl) && propositions_alpha_equivalent(ar, br)
        }
        (Proposition::Not(a), Proposition::Not(b)) => propositions_alpha_equivalent(a, b),
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            left_value == right_value
                && (retained_syntax::conditions_equal(left_condition, right_condition)
                    || condition_with_canonicalized_loads(left_condition)
                        .zip(condition_with_canonicalized_loads(right_condition))
                        .is_some_and(|(left, right)| left == right))
        }
        (
            Proposition::Equal(Term::Algebraic(al), Term::Algebraic(ar)),
            Proposition::Equal(Term::Algebraic(bl), Term::Algebraic(br)),
        ) => retained_syntax::algebraic_equal(al, bl) && retained_syntax::algebraic_equal(ar, br),
        (
            Proposition::MemoryLoadable {
                memory: left_memory,
                base: left_base,
                bytes: left_bytes,
                wide: false,
            },
            Proposition::MemoryLoadable {
                memory: right_memory,
                base: right_base,
                bytes: right_bytes,
                wide: false,
            },
        ) => {
            canonicalize_pointer_loads(left_base) == canonicalize_pointer_loads(right_base)
                && canonicalize_atomic_loads(left_bytes)
                    == canonicalize_atomic_loads(right_bytes)
                // Loadability depends on the state's blocks, not its
                // cached cell values. Retired automatic blocks are part of
                // the state marker too.
                && left_memory.blocks == right_memory.blocks
                && left_memory.forgotten.ended_local_blocks == right_memory.forgotten.ended_local_blocks
        }
        _ => false,
    }
}

/// Splits both offsets into non-constant atoms plus a constant shift,
/// resolves atoms whose scaled values equality facts pin to a constant, and
/// requires the remaining atoms to match pairwise. Runs the bounded constant
/// resolver once per atom at top level, never inside the resolution
/// recursion.
fn pointer_offsets_equal_with_resolved_atoms(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    let resolve = |offset: &PointerOffsetTerm| {
        let (atoms, mut constant) = crate::kernel::reasoning::offset_atoms_and_constant(offset);
        let mut unresolved = Vec::new();
        for atom in atoms {
            if let PointerOffsetTerm::Int32Scaled { value, byte_width } = &atom
                && let Some(known) =
                    assumptions.known_signed_constant_after_normalization_view(value.operand_view())
            {
                constant += known * byte_width;
                continue;
            }
            unresolved.push(atom);
        }
        (unresolved, constant)
    };
    let (left_atoms, left_constant) = resolve(left);
    let (mut right_atoms, right_constant) = resolve(right);
    if left_constant != right_constant {
        return false;
    }
    // Scaled values compare through state-bridged load equality: two
    // forms of one loaded field.
    let scaled_values_bridged = |left: Operand<'_>, right: Operand<'_>| {
        crate::kernel::reasoning::int32_operand_values_equal_for_memory_resolution(
            left,
            right,
            assumptions,
        ) || left
            .read_source()
            .zip(right.read_source())
            .is_some_and(|(left, right)| assumptions.memory_loads_proven_equal(&left, &right))
            || crate::kernel::explicit_atomic_equality_from_memory_derivations_views(
                left,
                right,
                assumptions,
            )
    };
    let atoms_match = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
        if left == right
            || assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
                left.clone(),
                right.clone(),
            )) == Some(true)
            || assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
                right.clone(),
                left.clone(),
            )) == Some(true)
        {
            return true;
        }
        let (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) = (left, right)
        else {
            return false;
        };
        if left_width != right_width {
            return false;
        }
        // A chain of stated offset equalities is not walked here: each
        // stated one is an equality-graph edge the bridged comparison reads,
        // and chaining them through state-bridged endpoints was a search
        // over every condition fact.
        scaled_values_bridged(left_value.operand_view(), right_value.operand_view())
    };
    for atom in &left_atoms {
        let Some(position) = right_atoms
            .iter()
            .position(|candidate| atoms_match(atom, candidate))
        else {
            return false;
        };
        right_atoms.remove(position);
    }
    right_atoms.is_empty()
}

/// Whether a universally quantified fact, instantiated at the terms of
/// `condition`, states that condition with premises `premise_holds` accepts.
/// The instantiation is read off the condition; nothing is searched for.
pub(crate) fn condition_holds_by_instantiated_fact(
    assumptions: &PureFactContext,
    condition: &ConditionTerm,
    value: bool,
    premise_holds: &dyn Fn(&Proposition) -> bool,
) -> bool {
    crate::instrumentation::measure_operation(
        "kernel",
        "certification proposition",
        "certification proof: quantified condition facts",
        || {
            // Only a universal concluding a condition of this shape can
            // state it (`program_condition_facts_equivalent_for_memory_resolution`
            // relates one relation to itself).
            assumptions
                .universals_concluding(
                    crate::kernel::assumptions::UniversalConclusionKey::of_condition(condition),
                )
                .any(|fact| {
                    assumptions
                        .forall_instantiations_for_condition(fact, condition)
                        .into_iter()
                        .any(|instance| {
                            let mut body = &instance;
                            let mut premises = Vec::new();
                            while let Proposition::Implies(premise, rest) = body {
                                premises.push(premise.as_ref());
                                body = rest;
                            }
                            let Proposition::ConditionIs(_, instance_value) = body else {
                                return false;
                            };
                            *instance_value == value
                                && program_condition_facts_equivalent_for_memory_resolution(
                                    body,
                                    &Proposition::ConditionIs(condition.clone(), value),
                                    assumptions,
                                )
                                && premises.into_iter().all(premise_holds)
                        })
                })
        },
    )
}

/// Whether a bare condition holds by the memory-resolution rules: the
/// facts state it about the same values read at other states, or the
/// bounded order prover derives it. This is what `transport` checks.
pub(crate) fn condition_holds_by_memory_resolution(
    assumptions: &PureFactContext,
    condition: &ConditionTerm,
    value: bool,
) -> bool {
    match (condition, value) {
        (ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left, right }, true) => {
            names_of_one_cell_framed(left, right, assumptions)
                || int32_values_proven_equal_for_memory_resolution(left, right, assumptions)
                || assumptions
                    .has_anchored_bitvector_equality_fact_for_memory_resolution(left, right)
                || assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(
                        left.as_ref().clone(),
                        right.as_ref().clone(),
                    ),
                    true,
                ) && assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ),
                    true,
                )
        }
        // A 64-bit read (an `unsigned long` word) is framed the way a 32-bit
        // one is: the recorded history shows one version of the cell. The
        // remaining 32-bit routes read the int32 graph and stay 32-bit only.
        (ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::Equal, left, right }, true) => {
            names_of_one_cell_framed(left, right, assumptions)
                || assumptions.proves_order_condition_for_memory_resolution(condition, value)
                || assumptions.has_matching_condition_fact_for_memory_resolution(condition, value)
        }
        // Two complete reads of one cell carry one value even where each spells
        // its coordinate from its own base (`n + 8` and `old(n) + 8`), as the
        // state-modulo condition matchers already accept.
        (ConditionTerm::PointerValueEqual(left, right), true) => {
            assumptions.contains_known(&Proposition::ConditionIs(condition.clone(), true))
                || (assumptions.pointer_designations_match(left, right)
                    && (pointers_proven_equal_for_memory_resolution(
                        left.pointer(),
                        right.pointer(),
                        assumptions,
                    ) || crate::kernel::memory_provenance::complete_pointer_reads_equal_across_frame(
                        left.pointer(),
                        right.pointer(),
                        assumptions,
                    )))
        }
        (ConditionTerm::PointerEqual(left, right), true) => {
            pointers_proven_equal_for_memory_resolution(left, right, assumptions)
                || assumptions.pointers_known_equal(left, right)
                || pointer_read_has_recorded_value(left, right, assumptions)
        }
        (ConditionTerm::PointerOffsetEqual(left, right), true) => {
            pointer_offsets_proven_equal_for_memory_resolution(left, right, assumptions)
                || pointer_offsets_equal_with_resolved_atoms(left, right, assumptions)
        }
        _ => {
            assumptions.proves_order_condition_for_memory_resolution(condition, value)
                || assumptions.has_matching_condition_fact_for_memory_resolution(condition, value)
        }
    }
}

/// Two load variables for one address are equal when the cell is framed
/// across the effects between the states they were read from: the
/// bounded, memoized unchanged-load check over recorded derivations and
/// effect facts, consulting no resolution fuel.
fn names_of_one_cell_framed(
    left: &MachineTerm,
    right: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let (MachineTerm::Variable(left_variable), MachineTerm::Variable(right_variable)) =
        (left, right)
    else {
        return false;
    };
    let (Some(left), Some(right)) = (
        crate::kernel::eval::registered_load_origin_term_for_variable(left_variable),
        crate::kernel::eval::registered_load_origin_term_for_variable(right_variable),
    ) else {
        return false;
    };
    let (
        MachineTerm::MemoryLoad(left_memory, left_pointer, left_kind),
        MachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (&left, &right)
    else {
        return false;
    };
    if left_kind != right_kind {
        return false;
    }
    if left_pointer == right_pointer {
        return crate::kernel::explicit_atomic_equality_from_memory_derivations(
            &left,
            &right,
            assumptions,
        );
    }
    // Two spellings of one proven-equal address read the same bytes. The
    // separation facts may name either spelling, so the history is read at
    // each in turn, never at an address merely related to them.
    pointers_proven_equal_for_memory_resolution(left_pointer, right_pointer, assumptions)
        && [left_pointer, right_pointer].into_iter().any(|pointer| {
            crate::kernel::explicit_atomic_equality_from_memory_derivations(
                &MachineTerm::MemoryLoad(left_memory.clone(), pointer.clone(), *left_kind),
                &MachineTerm::MemoryLoad(right_memory.clone(), pointer.clone(), *right_kind),
                assumptions,
            )
        })
}

fn match_quantified_int32_term(
    pattern: &MachineTerm,
    target: &MachineTerm,
    binders: &BTreeSet<Variable>,
    substitutions: &mut BTreeMap<Variable, MachineTerm>,
) -> bool {
    if let MachineTerm::Variable(variable) = pattern
        && binders.contains(variable)
    {
        return match substitutions.get(variable) {
            Some(existing) => existing == target,
            None => {
                substitutions.insert(*variable, target.clone());
                true
            }
        };
    }
    if let (Some((operator, pattern_left, pattern_right)), Some((other, target_left, target_right))) =
        (pattern.as_binary(), target.as_binary())
        && operator == other
        && operator.is_bitvector32()
    {
        return match_quantified_int32_term(pattern_left, target_left, binders, substitutions)
            && match_quantified_int32_term(pattern_right, target_right, binders, substitutions);
    }
    match (pattern, target) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            constant_u32(*left) == constant_u32(*right)
        }
        (MachineTerm::Variable(left), MachineTerm::Variable(right)) => left == right,
        (
            unary_term!(Bits32 @ pattern_format, BitwiseNot, pattern),
            unary_term!(Bits32 @ target_format, BitwiseNot, target),
        ) if pattern_format == target_format => {
            match_quantified_int32_term(pattern, target, binders, substitutions)
        }
        _ => pattern == target,
    }
}

/// Instantiates every binder in one closed theorem from its condition
/// conclusion. Matching is a single structural pass; premises are then
/// certified normally under the resulting exact substitution.
pub(super) fn certification_proves_condition_from_verified_pure_implication(
    assumptions: &PureFactContext,
    fact: &Proposition,
    target: &ConditionTerm,
    target_value: bool,
) -> bool {
    let mut binder_order = Vec::new();
    let mut body = fact;
    while let Proposition::ForAll {
        var, body: inner, ..
    } = body
    {
        binder_order.push(*var);
        body = inner;
    }
    if binder_order.is_empty() {
        return false;
    }
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, rest) = body {
        premises.push(premise.as_ref().clone());
        body = rest;
    }
    let Proposition::ConditionIs(pattern, pattern_value) = body else {
        return false;
    };
    if *pattern_value != target_value {
        return false;
    }
    let binders = binder_order.iter().copied().collect::<BTreeSet<_>>();
    let mut substitutions = BTreeMap::new();
    let matched = match (pattern, target) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: pattern_left,
                right: pattern_right,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: target_left,
                right: target_right,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: pattern_left,
                right: pattern_right,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: target_left,
                right: target_right,
            },
        ) => {
            match_quantified_int32_term(pattern_left, target_left, &binders, &mut substitutions)
                && match_quantified_int32_term(
                    pattern_right,
                    target_right,
                    &binders,
                    &mut substitutions,
                )
        }
        _ => false,
    };
    if !matched || substitutions.len() != binders.len() {
        return false;
    }
    premises.into_iter().all(|premise| {
        let premise = substitute_bitvector_variables_in_proposition(&premise, &substitutions);
        PureFactContext::settles_exactly(assumptions, &premise)
    })
}

pub(super) fn resources_certify_loadability(
    state: &ExecutionState,
    resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    match proposition {
        Proposition::ForAll { body, .. } => {
            return resources_certify_loadability(state, resources, body, assumptions);
        }
        Proposition::Implies(premise, conclusion) => {
            let assumptions = assumptions
                .clone()
                .assume_proposition(premise.as_ref().clone());
            return resources_certify_loadability(state, resources, conclusion, &assumptions);
        }
        Proposition::And(left, right) => {
            return resources_certify_loadability(state, resources, left, assumptions)
                && resources_certify_loadability(state, resources, right, assumptions);
        }
        _ => {}
    }
    let Proposition::MemoryLoadable {
        memory,
        base,
        bytes,
        wide: false,
    } = proposition
    else {
        return false;
    };
    memory_states_proven_equal_at_pointer(memory, state.memory(), base, assumptions)
        && (bytes
            .as_const()
            .is_some_and(|bytes| resource_context_has_read(resources, base, bytes, assumptions))
            || crate::kernel::resource_context_has_symbolic_range_read(
                resources,
                base,
                bytes,
                assumptions,
            ))
}

fn contract_endpoints_certify_loadability(
    entry_state: &ExecutionState,
    entry_resources: &ResourceContext,
    post_state: &ExecutionState,
    post_resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    resources_certify_loadability(entry_state, entry_resources, proposition, assumptions)
        || resources_certify_loadability(post_state, post_resources, proposition, assumptions)
}

#[cfg(test)]
mod shared_contract_operand_tests {
    use super::*;
    use crate::kernel::KernelTermExport;

    #[test]
    fn shared_contract_read_matches_stored_arithmetic_without_export() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "contract-expression-cell".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let written = MachineTerm::add(
            MachineTerm::Variable(Variable(1017151)),
            MachineTerm::constant(7),
        );
        let before = crate::kernel::Memory::new().with_block("contract-expression-cell", 4);
        let after = before
            .clone()
            .store(pointer.clone(), ProgramValue::Int32(written.clone()));
        let load = |memory| {
            SharedMachineIntegerTerm::index(
                MachineIntegerType::Int32,
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(memory),
                    Box::new(pointer.clone()),
                    crate::kernel::LoadKind::Int32,
                ),
            )
        };
        let before = load(before);
        let after = load(after);
        let written = SharedMachineIntegerTerm::index(MachineIntegerType::Int32, written);
        let assumptions = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        assert!(
            crate::kernel::explicit_atomic_equality_from_memory_derivations_views(
                after.operand_view(),
                written.operand_view(),
                &assumptions
            )
        );
        assert!(
            !crate::kernel::explicit_atomic_equality_from_memory_derivations_views(
                before.operand_view(),
                written.operand_view(),
                &assumptions
            )
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_contract_index_equality_keeps_read_states_and_sources() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "contract-index".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let load = |id| {
            let memory = crate::kernel::Memory::new()
                .with_block("contract-index", 4)
                .store(
                    pointer.clone(),
                    ProgramValue::Int32(MachineTerm::Variable(Variable(id))),
                );
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        let a = load(1017152);
        let b = load(1017153);
        let offset = |term| PointerOffsetTerm::Int32Scaled {
            value: SharedMachineIntegerTerm::index(MachineIntegerType::Int32, term),
            byte_width: 4,
        };
        let left = offset(a.clone());
        let right = offset(b.clone());
        let equation = ConditionTerm::equal(
            MachineTerm::Variable(Variable(1017152)),
            MachineTerm::Variable(Variable(1017153)),
        );
        let empty = PureFactContext::new();
        let related = empty.clone().assume_condition(equation.clone(), true);
        let exports = KernelTermExport::machine_export_count();
        assert!(pointer_offsets_equal_with_resolved_atoms(
            &left, &left, &empty
        ));
        assert!(!pointer_offsets_equal_with_resolved_atoms(
            &left, &right, &empty
        ));
        assert!(pointer_offsets_equal_with_resolved_atoms(
            &left, &right, &related
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_byte_offsets_keep_bounds_and_width_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1017121));
        let offset = PointerOffsetTerm::Int32Scaled {
            value: SharedMachineIntegerTerm::index(MachineIntegerType::Int32, x.clone()),
            byte_width: 4,
        };
        let empty = PureFactContext::new();
        let lower = ConditionTerm::signed_greater_equal(x.clone(), MachineTerm::constant(0));
        let upper =
            ConditionTerm::signed_less_equal(x.clone(), MachineTerm::constant(i32::MAX as u32 / 4));
        let lower_only = empty.clone().assume_condition(lower.clone(), true);
        let bounded = lower_only.clone().assume_condition(upper, true);
        let exports = KernelTermExport::machine_export_count();
        assert!(pointer_offset_bytes(&empty, &offset).is_none());
        let bytes = pointer_offset_bytes(&bounded, &offset).expect("selected bounds");
        assert!(pointer_offset_bytes(&lower_only, &offset).is_none());
        assert!(
            pointer_offset_bytes(
                &bounded,
                &PointerOffsetTerm::Int64Scaled {
                    value: SharedMachineIntegerTerm::index(
                        MachineIntegerType::Int64,
                        MachineTerm::int64_from_32(x)
                    ),
                    byte_width: 4,
                    unsigned: false,
                }
            )
            .is_none()
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(bytes.operand_view().binary().is_some());
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    use crate::kernel::KernelTermExport;
    include!(
        "../../scaling_tests/kernel/api/contract_certification/shared_contract_operand_tests.rs"
    );
}

#[cfg(test)]
mod prepared_entry_cases_tests {
    use super::*;

    pub(super) fn fixture(
        guards: usize,
        unrelated: usize,
    ) -> (ExecutionState, ProgramFunction, Vec<ProgramExpression>) {
        let mut parameters = Vec::new();
        let mut arguments = Vec::new();
        let mut definitions = Vec::new();
        let mut requirements = Vec::new();
        let mut resources = ResourceContext::new();
        for index in 0..guards {
            let name = format!("guarded_{index}");
            let parameter = format!("flag_{index}");
            let value =
                ProgramValue::Int32(MachineTerm::Variable(Variable(600_000 + index as u64)));
            parameters.push(program_parameter(&parameter, ProgramType::Int32));
            arguments.push(ProgramExpression::Value(value.clone()));
            requirements.push(ResourceSpec::composite(
                ResourceAccessMode::Own,
                name.clone(),
                vec![crate::kernel::program_expression::variable(&parameter)],
                vec![ProgramType::Int32],
            ));
            resources = resources
                .unchecked_with_fact(ResourceFact::own_composite(name.clone(), vec![value]));
            definitions.push(CompositeResourceDefinition::new(
                name,
                vec![program_parameter("flag", ProgramType::Int32)],
                Some(SpecProposition::Comparison {
                    left: SpecExpression::ProgramExpression(
                        crate::kernel::program_expression::variable("flag"),
                    ),
                    operator: ComparisonOperator::NotEqual,
                    right: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
                }),
                false,
                vec![ResourceSpec::token(
                    ResourceAccessMode::Own,
                    format!("token_{index}"),
                    vec![],
                    vec![],
                )],
                vec![],
            ));
        }
        let function = program_function(
            ProgramType::Int32,
            "guarded_entry",
            parameters,
            program_return(crate::kernel::program_expression::int32_literal(0)),
        )
        .with_resource_summary(requirements, vec![])
        .with_contract(
            (0..unrelated)
                .map(|index| SpecProposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                    resource_state_dependent: false,
                })
                .collect(),
            vec![],
            vec![],
            vec![],
            true,
        )
        .with_composite_resource_definitions(definitions);
        (
            ExecutionState::new().with_resource_context(resources),
            function,
            arguments,
        )
    }

    #[test]
    fn opening_retains_all_entry_alternatives_and_their_resource_states() {
        let (state, function, arguments) = fixture(2, 0);
        let opened = crate::kernel::proof::OpenedContractEntry::open(
            &state,
            &function,
            &arguments,
            &Vec::<Proposition>::new(),
            &ExecutionEnvironment::new(),
        )
        .unwrap();
        let prepared = opened.prepared_cases().clone();
        assert_eq!(prepared.case_count(), 4);
        assert_eq!(prepared.guard_cases.len(), 4);
        for (case, guards) in prepared.cases.iter().zip(&prepared.guard_cases) {
            assert_eq!(guards.len(), 2);
            for guard in guards {
                assert!(case.assumptions.proves_exact(guard));
                assert!(
                    !case
                        .assumptions
                        .proves_exact(&negate_contract_case_proposition(guard))
                );
            }
        }
        let token_counts = prepared
            .cases
            .iter()
            .map(|case| case.entry_state.resources().facts().len())
            .collect::<Vec<_>>();
        assert_eq!(token_counts, vec![2, 1, 1, 0]);
        let core = opened.into_execution_core();
        // Registration can inspect missing coverage, but must not invent new cases.
        let before = guard_case_builds();
        for _ in 0..2 {
            let execution = prove_prepared_function_contract_execution_paths(
                &prepared,
                function.clone(),
                ExecutionEnvironment::new(),
                ExecutionSemantics::APPLY_VERIFIED_RULES,
                FunctionContractExecutionMode::VerifyLoops,
                &[],
                &[],
            );
            assert_eq!(execution.cases.len(), 4);
            assert!(
                !execution.is_complete(),
                "unproved cases do not become completed coverage"
            );
        }
        assert_eq!(
            guard_case_builds(),
            before,
            "registration consumes the retained alternatives"
        );
        let _ = core;
        let foreign = program_function(
            ProgramType::Int32,
            "other",
            vec![],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let refused = prove_prepared_function_contract_execution_paths(
            &prepared,
            foreign,
            ExecutionEnvironment::new(),
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
            &[],
            &[],
        );
        assert!(!refused.is_complete());
        assert!(
            refused
                .reuse_diagnostic()
                .unwrap()
                .contains("another function or target")
        );
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/api/contract_certification/prepared_entry_cases.rs");
    }
}

#[cfg(test)]
mod entry_authority_tests {
    use super::*;
    use crate::kernel::proof::OpenedContractEntry;

    pub(super) fn checked_execution(
        unrelated: usize,
        extra_premise: Option<Proposition>,
    ) -> Result<(Arc<PreparedContractEntryCases>, CheckedFunctionExecution), &'static str> {
        checked_execution_with_subject(unrelated, extra_premise, false)
    }

    fn checked_execution_with_subject(
        unrelated: usize,
        extra_premise: Option<Proposition>,
        replace_entry_status: bool,
    ) -> Result<(Arc<PreparedContractEntryCases>, CheckedFunctionExecution), &'static str> {
        let function = program_function(
            ProgramType::Void,
            "entry_authority",
            vec![],
            ProgramStatement::Skip,
        )
        .with_contract(
            (0..unrelated)
                .map(|i| SpecProposition::Predicate {
                    name: format!("requirement_{i}"),
                    arguments: vec![],
                    resource_state_dependent: false,
                })
                .collect(),
            vec![],
            vec![],
            vec![FunctionContractClaim::body_safety()],
            true,
        );
        let caller = ExecutionState::new();
        let environment = ExecutionEnvironment::new();
        let opened = OpenedContractEntry::open(
            &caller,
            &function,
            &[],
            &Vec::<Proposition>::new(),
            &environment,
        )
        .unwrap();
        let entry = opened.prepared_cases().clone();
        let state = opened.entry_state().clone();
        let mut assumptions = opened.facts().assumptions().clone();
        let theorem = Proposition::ProgramStatementVerifies {
            state: Box::new(state.clone()),
            statement: Box::new(ProgramStatement::Skip),
            outcome: StatementOutcome::Normal(Box::new(state.clone())),
        };
        let mut core = opened.into_execution_core();
        core.record_statement_transition(
            &function,
            &[],
            Theorem::new(theorem),
            assumptions.clone(),
            &[],
            &[],
        )
        .map_err(|refusal| refusal.reason)?;
        let (outcome, obligations) = program_function_outcome_from_statement_outcome(
            &caller,
            &function,
            StatementOutcome::Return {
                value: ProgramValue::Void.into(),
                state: Box::new(state),
            },
            vec![],
            &assumptions,
        );
        let candidates = program_function_execution_candidates_from_outcomes(
            caller,
            function.clone(),
            vec![],
            vec![(outcome, vec![], obligations)],
        );
        if let Some(premise) = extra_premise {
            assumptions = assumptions.assume_proposition(premise);
        }
        let subject = if replace_entry_status {
            function.clone().with_program_entry()
        } else {
            function.clone()
        };
        let checked = core.checked_function_execution(
            &candidates,
            &subject,
            assumptions,
            environment,
            ExecutionSemantics::APPLY_VERIFIED_RULES,
            FunctionContractExecutionMode::VerifyLoops,
        )?;
        Ok((entry, checked))
    }

    #[test]
    fn execution_cannot_substitute_program_entry_metadata() {
        assert!(
            matches!(checked_execution_with_subject(0, None, true), Err(reason) if reason.contains("entry and source"))
        );
    }

    #[test]
    fn owned_admission_requires_the_producer_entry_identity() {
        let (entry, checked) = checked_execution(0, None).unwrap();
        let (foreign, _) = checked_execution(0, None).unwrap();
        assert_eq!(entry.function, foreign.function);
        assert_ne!(entry, foreign);
        let admitted = execution_from_owned_contract_entry(&entry, std::slice::from_ref(&checked));
        assert_eq!(admitted.cases.len(), 1);
        assert_eq!(admitted.cases[0][0].paths.len(), 1);
        assert!(
            execution_from_owned_contract_entry(&foreign, &[checked])
                .cases
                .is_empty()
        );
    }

    #[test]
    fn caller_proposed_premises_do_not_become_opened_contract_assumptions() {
        let extra = Proposition::Predicate {
            name: "not_a_requirement".into(),
            arguments: vec![],
        };
        let (_, checked) = checked_execution(0, Some(extra.clone())).unwrap();
        assert!(!checked.assumptions.proves_exact(&extra));
        assert!(checked.entry_authority.is_some());
    }

    #[test]
    fn an_independent_execution_cannot_claim_opened_entry_authority() {
        let (entry, checked) = checked_execution(0, None).unwrap();
        let independent = prove_checked_program_function_execution_with_environment(
            checked.state.clone(),
            checked.function.clone(),
            checked.arguments.clone(),
            checked.assumptions.clone(),
            checked.environment.clone(),
            checked.execution_semantics,
            checked.mode,
        );
        assert!(independent.entry_authority.is_none());
        assert!(
            execution_from_owned_contract_entry(&entry, &[independent])
                .cases
                .is_empty()
        );
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/api/contract_certification/entry_authority.rs");
    }
}
