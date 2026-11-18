use super::ResourceReference;
use super::loans::{
    CheckedLoanCallEvidence, CompositeLoanBacking, CompositeProjectionEvidence, LoanId, LoanLedger,
    LoanRefusal, LoanRefusalOperation, LoanRefusalSubject, LoanViewBinding, LoanViewBindings,
    StableViewTransferPlan, append_checked_loan_evidence, empty_checked_loan_evidence_sequence,
    plan_stable_view_transfer_with_protocol_effect,
};
use super::model_fields::{ModelFieldOrigin, ModelMint, algebraic_value_variable};
use super::population_authority::storage_creation::CreationEvents;
use super::prelude::*;
use super::spec::walk::{SpecNode, Visit, spec_tree_all};
use super::thread_confinement::confined_resource_name;
use crate::kernel::ResourceDescription;
use crate::kernel::unary_term;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::kernel::{bits32_constant, int64_constant, uint64_constant};
use std::sync::Arc;

#[cfg(test)]
mod aggregate_return_tests;
mod construction_return;
#[cfg(test)]
mod exit_partition_tests;
#[cfg(test)]
mod literal_objects;
mod mixed_return_resources;
pub(in crate::kernel) use mixed_return_resources::ReturnedEntryPartition;
mod produced_argument_supply;
mod return_loan_backing;
mod summary_transfer;
use mixed_return_resources::{
    ConstructedReturnBodies, ConsumedCellReturns, EvaluatedReturnResources, FreshAllocationReturn,
    ProducedBorrowingPiece, ProjectedReturnResource, ReturnOwnershipOrigin,
    project_return_resource_cores,
};
pub(in crate::kernel) use mixed_return_resources::{
    EscrowRecoveryBoundary, FramedReturnPartition, ReturnResourceTransfer, ReturnedConsumedCell,
    ReturnedFreshAllocation, ReturnedOwnershipPartition,
};
pub(in crate::kernel) use summary_transfer::SummaryResourceTransferRule;
#[cfg(test)]
mod produced_argument_supply_tests;
use produced_argument_supply::prepare_produced_argument_supply;

fn execute_program_function_body_paths(
    state: &ExecutionState,
    function: &ProgramFunction,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    execute_function_body_paths(
        state,
        function,
        assumptions,
        execution_context,
        budget,
        &mut super::eval::StatementJudgment::Executes,
    )
}

/// A function body under `judgment`, following its forward `goto`s: each
/// jump continues from the target's remaining statements, at most once per
/// target along a path.
fn execute_function_body_paths(
    state: &ExecutionState,
    function: &ProgramFunction,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut super::eval::StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let initial = super::eval::execute_statement_paths(
        state,
        function.body(),
        assumptions,
        execution_context,
        budget,
        judgment,
    )?;
    if function.control_target_count() == 0 {
        return Ok(initial);
    }
    let mut pending = initial
        .into_iter()
        .map(|path| (path, 0usize))
        .collect::<Vec<_>>();
    let mut completed = Vec::new();
    while let Some((path, jump_count)) = pending.pop() {
        let StatementOutcome::Jump {
            target,
            state: jump_state,
        } = &path.outcome
        else {
            completed.push(path);
            continue;
        };
        let Some(target) = function.control_target(*target) else {
            completed.push(invalid_goto_path(
                path,
                "goto refers to an unknown function target",
            ));
            continue;
        };
        if jump_count >= function.control_target_count() {
            completed.push(invalid_goto_path(path, "goto control flow is not forward"));
            continue;
        }
        let suffix = super::eval::execute_statement_paths_with_prefix(
            jump_state,
            &target.remaining,
            assumptions,
            execution_context,
            &path.facts,
            &path.obligations,
            &path.loan_evidence,
            budget,
            judgment,
        )?;
        pending.extend(
            suffix
                .into_iter()
                .map(|suffix_path| (suffix_path, jump_count + 1)),
        );
    }
    budget.check_path_width(completed.len())?;
    Ok(completed)
}

fn invalid_goto_path(path: StatementExecutionPath, message: &str) -> StatementExecutionPath {
    StatementExecutionPath {
        call_parameters: None,
        loop_invariant_correspondence: Default::default(),
        call_result: None,
        outcome: StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
            message.to_string(),
        )),
        facts: path.facts,
        obligations: path.obligations,
        loan_evidence: path.loan_evidence,
    }
}

#[cfg(test)]
mod callback_contract_tests;

#[cfg(test)]
mod pointee_const_return_tests;
use std::collections::VecDeque;

// Resource-clause evaluation reports the exact checked resource that a
// failed expression tried to read.  The section worklist below captures that
// fact while each clause runs, allowing only clauses that depend on a newly
// supplied fact to be retried.
thread_local! {
    static RESOURCE_DEPENDENCY_CAPTURE: std::cell::RefCell<Option<Vec<ResourceFact>>> =
        const { std::cell::RefCell::new(None) };
    #[cfg(test)]
    static RESOURCE_CLAUSE_ATTEMPTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn record_resource_dependency(resource: ResourceFact) {
    RESOURCE_DEPENDENCY_CAPTURE.with(|capture| {
        let mut captured = capture.borrow_mut();
        let Some(dependencies) = captured.as_mut() else {
            return;
        };
        if !dependencies.contains(&resource) {
            dependencies.push(resource);
        }
    });
}

fn capture_resource_dependencies<T>(operation: impl FnOnce() -> T) -> (T, Vec<ResourceFact>) {
    RESOURCE_DEPENDENCY_CAPTURE.with(|capture| {
        let previous = capture.replace(Some(Vec::new()));
        let result = operation();
        let captured = capture.replace(previous).unwrap_or_default();
        // Resource expression evaluation can call another checked contract
        // boundary.  Preserve nested missing-resource observations in the
        // enclosing clause's capture instead of dropping them when the inner
        // capture is restored.
        if let Some(active) = capture.borrow_mut().as_mut() {
            for dependency in &captured {
                if !active.contains(dependency) {
                    active.push(dependency.clone());
                }
            }
        }
        (result, captured)
    })
}

#[cfg(test)]
pub(crate) fn measure_resource_clause_attempts<T>(operation: impl FnOnce() -> T) -> (T, usize) {
    RESOURCE_CLAUSE_ATTEMPTS.with(|attempts| {
        let previous = attempts.replace(0);
        let result = operation();
        let measured = attempts.replace(previous);
        (result, measured)
    })
}

#[cfg(test)]
fn record_resource_clause_attempt() {
    RESOURCE_CLAUSE_ATTEMPTS.with(|attempts| attempts.set(attempts.get() + 1));
}
/// Resource descriptions can be checked before their transfer is proved.
/// Checked call application restores entry borrows per emitted occurrence.
/// A selected consumed scalar can also return by explicit transfer; other
/// outputs still pass through description admission.
#[derive(Clone, Copy)]
enum ReturnResourceComposition<'a> {
    ApplyTransfers(&'a ConsumedCellReturns),
    FramedTransfers {
        _rule: FramedCallRule<'a>,
        transfers: &'a ConsumedCellReturns,
    },
    BodyReturn {
        state: &'a ExecutionState,
        frame: &'a ResourceContext,
        allocations: Option<(&'a CreationEvents, &'a CreationEvents)>,
        consumed: &'a ConsumedCellReturns,
    },
    ValidateDescriptions,
}

impl<'a> ReturnResourceComposition<'a> {
    fn for_rule(rule: Option<FramedCallRule<'a>>, transfers: &'a ConsumedCellReturns) -> Self {
        match rule {
            Some(rule) => Self::FramedTransfers {
                _rule: rule,
                transfers,
            },
            None => Self::ApplyTransfers(transfers),
        }
    }

    fn frames_outputs(self) -> bool {
        matches!(self, Self::FramedTransfers { .. })
    }

    fn consumed_children(self) -> Option<&'a ConsumedCellReturns> {
        match self {
            Self::ApplyTransfers(plan)
            | Self::FramedTransfers {
                transfers: plan, ..
            } => Some(plan),
            Self::BodyReturn {
                consumed,
                allocations: Some(_),
                ..
            } => Some(consumed),
            _ => None,
        }
    }

    fn body_return(self) -> Option<(&'a ExecutionState, &'a ResourceContext)> {
        match self {
            Self::BodyReturn { state, frame, .. } => Some((state, frame)),
            _ => None,
        }
    }

    fn allocation_events(self) -> Option<(&'a CreationEvents, &'a CreationEvents)> {
        match self {
            Self::BodyReturn { allocations, .. } => allocations,
            _ => None,
        }
    }

    fn restores_entry_borrows(self) -> bool {
        match self {
            Self::ApplyTransfers(_) | Self::FramedTransfers { .. } | Self::BodyReturn { .. } => {
                true
            }
            _ => false,
        }
    }

    fn origin_for_return(
        self,
        clause: usize,
        entry_borrow: bool,
        fact: &ResourceFact,
    ) -> ReturnOwnershipOrigin {
        if let Some((creator, events)) = self.allocation_events() {
            return FreshAllocationReturn::from_created_owner(fact, creator, events)
                .map(ReturnOwnershipOrigin::FreshAllocation)
                .unwrap_or(ReturnOwnershipOrigin::Description);
        }
        if entry_borrow {
            return ReturnOwnershipOrigin::EntryBorrow;
        }
        if let Some(transfers) = self.consumed_children()
            && let Some(transfer) = transfers.get(clause)
        {
            return ReturnOwnershipOrigin::ConsumedCell(transfer);
        }
        ReturnOwnershipOrigin::Description
    }

    fn constructed_summary_output(self, clause: usize) -> Option<&'a ResourceFact> {
        match self {
            Self::ApplyTransfers(transfers) | Self::FramedTransfers { transfers, .. } => {
                transfers.constructed.get(&clause)
            }
            _ => None,
        }
    }
}

/// Entry-state borrows restored to the residual frame from which they were lent.
/// New produced ownership does not use this transfer. Construction is private
/// to call application; this is proof state, not a term.
pub(in crate::kernel) struct ReturnedCallBorrows {
    frame: ResourceContext,
    outputs: ResourceContext,
}

impl ReturnedCallBorrows {
    pub(in crate::kernel) fn into_parts(self) -> (ResourceContext, ResourceContext) {
        (self.frame, self.outputs)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FunctionResourceTransfer {
    helper_call: Option<Arc<super::mutexes::helper_contracts::HelperCall>>,
    /// The complete checked entry transition.  The two partitions are kept
    /// explicitly so callers cannot accidentally treat a borrowed view as a
    /// consumed capability when reconstructing the caller successor.
    borrowed_inputs: Vec<CheckedResourceFact>,
    consumed_inputs: Vec<CheckedResourceFact>,
    /// Checked callee-side borrowed ownership paired with an equivalent
    /// caller-side spelling selected by the exclusive reservation planner.
    /// This is output-sized call-boundary pairing, not a search through
    /// the caller frame.
    canonical_borrowed_owners: Vec<(ResourceFact, ResourceFact)>,
    consumed_cell_returns: ConsumedCellReturns,
    allocation_creator: Option<CreationEvents>,
    callee_resources: ResourceContext,
    /// Resources left in the caller after the entry requirements have been
    /// consumed; this is the caller frame for the remainder of the call.
    caller_resources_after_requirements: ResourceContext,
    /// Filled by the verified-application preparer once entry guards and
    /// dependent addresses have been checked.  It is the sole memory-effect
    /// projection used by modular call havoc and its effect fact.
    memory_effects: Vec<MemoryRange>,
    resource_effect_bound: Option<Resource>,
    post_outputs: Option<ResourceContext>,
    /// Every evaluated ensured view, kept beside the composed return
    /// resources so the recovery routes see each one exactly once even
    /// when composition merges or normalizes it away.
    candidate_output_views: Vec<ResourceFact>,
    returned_entry_partition: Option<mixed_return_resources::ReturnedEntryPartition>,
    /// Each viewed piece in the one-level frontier of an ensured owned
    /// composite, with that composite's head: the borrows a produced
    /// composite packages, which the caller side binds to exactly one loan of
    /// this call (step 7).
    produced_borrowing_pieces: Vec<ProducedBorrowingPiece>,
    /// Stable-view transition, when this call was prepared through the
    /// planner. The plan owns the checked successor ledger and is consumed
    /// only after postconditions have been evaluated.
    stable_view_plan: Option<StableViewTransferPlan>,
    /// The bytes of this call's checked view frontier that a planned stable
    /// view does not name directly: a composite view's checked one-level
    /// pieces, and the intrinsic and empty-composite views, which never reach
    /// the planner at all. The declared mutable effects are compared against
    /// these as well, because an effect may not widen the authority the call
    /// actually received (D9). Each piece carries the owned occurrence behind
    /// it, for the same partition read the planned views get: a composite
    /// view's pieces carry that composite's support, while an intrinsic or
    /// empty-composite view has no owner in the caller's context and carries
    /// none, so its bytes are always compared arithmetically.
    checked_view_frontier: Vec<(MemoryRange, Option<ResourceOccurrenceId>)>,
}

/// An authenticated function-entry plan. Its private fields prevent proof
/// clients from replacing the checked clauses with a later field spelling.
pub(crate) struct CheckedBoundaryResourceTransfer {
    function: Arc<ProgramFunction>,
    arguments: Vec<ProgramExpression>,
    caller: ExecutionState,
    callee: ExecutionState,
    transfer: FunctionResourceTransfer,
}

impl std::fmt::Debug for CheckedBoundaryResourceTransfer {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CheckedBoundaryResourceTransfer")
            .field("function", &self.function.name())
            .finish_non_exhaustive()
    }
}

impl PartialEq for CheckedBoundaryResourceTransfer {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}

impl Eq for CheckedBoundaryResourceTransfer {}

impl CheckedBoundaryResourceTransfer {
    pub(crate) fn callee_entry(&self) -> &ExecutionState {
        &self.callee
    }

    pub(crate) fn checked_entry_clauses(&self) -> Vec<CheckedResourceFact> {
        transfer_entry_clauses(&self.transfer)
    }

    pub(crate) fn checked_function(&self) -> &ProgramFunction {
        self.function.as_ref()
    }

    fn matches(
        &self,
        caller: &ExecutionState,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
    ) -> bool {
        std::ptr::eq(self.function.as_ref(), function)
            && self.arguments == arguments
            && self.caller.memory().diagnostic_identity() == caller.memory().diagnostic_identity()
            && self.caller.shares_non_memory_storage_with(caller)
    }
}

pub(crate) fn capture_checked_boundary_resource_transfer(
    caller: &ExecutionState,
    function: Arc<ProgramFunction>,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Arc<CheckedBoundaryResourceTransfer>, RuntimeError>> {
    let Some(values) = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(RuntimeError::TypeMismatch));
    };
    let Some(callee) = bind_contract_proof_arguments(caller, &function, &values) else {
        return Ok(Err(RuntimeError::TypeMismatch));
    };
    let transfer = match prepare_function_resource_transfer(
        caller,
        &callee,
        &function,
        assumptions,
        budget,
        true,
        ResourceTransitionPurpose::FunctionBoundary,
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    let callee = callee_state_with_resource_transfer(callee, &transfer);
    Ok(Ok(Arc::new(CheckedBoundaryResourceTransfer {
        function,
        arguments: arguments.to_vec(),
        caller: caller.clone(),
        callee,
        transfer,
    })))
}

fn callee_state_with_resource_transfer(
    callee_state: ExecutionState,
    transfer: &FunctionResourceTransfer,
) -> ExecutionState {
    let callee_state = callee_state.with_resource_context(transfer.callee_resources.clone());
    let Some(plan) = &transfer.stable_view_plan else {
        return callee_state;
    };
    callee_state
        .with_loan_ledger(Some(plan.ledger.clone()))
        .with_loan_participant(Some(plan.callee_participant()))
        .with_loan_view_bindings(plan.callee_view_bindings().clone())
}

/// Resource expansion failures report a bounded clause frontier. Raw context
/// Debug includes persistent indexes and memory states unrelated to the
/// failing call, so it must never be part of an ordinary user diagnostic.
fn bounded_contract_resource_frontier(resources: &ResourceContext) -> String {
    let mut heads = Vec::new();
    for fact in resources.facts().iter().take(8) {
        let label = match fact.resource() {
            Resource::Composite { name, .. } | Resource::Token { name, .. } => {
                name.chars().take(64).collect::<String>()
            }
            Resource::PopulationAuthority(description) => format!(
                "authority({})",
                description.family().chars().take(64).collect::<String>()
            ),
            _ => format!("{:?}", fact.family()),
        };
        heads.push(format!(
            "{} {label}",
            if fact.is_own() { "owns" } else { "views" }
        ));
    }
    let omitted = resources.facts().len().saturating_sub(heads.len());
    if omitted > 0 {
        heads.push(format!("and {omitted} more clauses"));
    }
    heads.join(", ")
}

/// Enumerate only the explicit owned transfer and its plain contained resources.
/// Each definition lookup is indexed; the ambient caller frame is never walked.
fn population_transfer_frontier<'a>(
    facts: impl Iterator<Item = &'a ResourceFact>,
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> Result<Vec<ResourceFact>, RuntimeError> {
    enum Work {
        Fact(ResourceFact),
        Leave(String),
    }
    let mut frontier = Vec::new();
    let mut active = BTreeSet::new();
    let mut work = Vec::new();
    for fact in facts {
        work.push(Work::Fact(fact.clone()));
        while let Some(item) = work.pop() {
            let fact = match item {
                Work::Leave(name) => {
                    active.remove(&name);
                    continue;
                }
                Work::Fact(fact) => fact,
            };
            if let ResourceFact::Own(Resource::Composite { name, .. }, quantity) = &fact
                && quantity.as_const() == Some(1)
                && let Ok(index) = definitions.binary_search_by(|definition| {
                    crate::instrumentation::record_deterministic_work(1);
                    definition.name().cmp(name)
                })
                && let definition = &definitions[index]
                && definition.resource_parameters().is_empty()
                && definition.instance_schema.is_none()
                && definition.matched.is_none()
                && definition.witnesses.is_empty()
                && definition.condition.is_none()
                && !definition.facts_claim_liveness
                && definition.children.is_empty()
                && definition.contains().iter().all(|child| {
                    matches!(
                        child.term(),
                        ResourceTerm::Memory(_) | ResourceTerm::Composite { .. }
                    ) && child.access() == ResourceAccessMode::Own
                        && child.quantity() == &ResourceQuantity::One
                        && child.guard().is_none()
                        && child.resource_arguments().is_empty()
                })
                && definition
                    .contains()
                    .iter()
                    .any(|child| matches!(child.term(), ResourceTerm::Composite { .. }))
            {
                if !active.insert(name.clone()) {
                    return Err(RuntimeError::FunctionContract(
                        "contained resource transfer has a recursive body".into(),
                    ));
                }
                let singleton = ResourceContext::new().unchecked_with_fact(fact.clone());
                let children = expand_composite_resource_fact(
                    &singleton,
                    &fact,
                    std::slice::from_ref(definition),
                    &crate::kernel::ProgramPoint::of_memory(memory),
                    assumptions,
                )
                .ok_or_else(|| {
                    RuntimeError::FunctionContract(
                        "cannot instantiate contained resource transfer".into(),
                    )
                })?;
                work.push(Work::Leave(name.clone()));
                work.extend(children.facts().iter().rev().cloned().map(Work::Fact));
            }
            frontier.push(fact);
        }
    }
    Ok(frontier)
}

/// Mirror the checked owned contract partition in the population ledger.
/// A composite outside a registered population follows ordinary resource
/// transfer; authority itself must always name a registered population.
pub(super) fn transfer_population_call_facts<'a>(
    mut state: ExecutionState,
    from: &ExecutionState,
    to: &ExecutionState,
    validation_state: &ExecutionState,
    facts: impl Iterator<Item = &'a ResourceFact>,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<ExecutionState, RuntimeError> {
    let Some(from_events) = from.population_effects.creation.as_ref() else {
        return Ok(state);
    };
    let Some(to_events) = to.population_effects.creation.as_ref() else {
        return Err(RuntimeError::FunctionContract(
            "population call lost its invocation identity".into(),
        ));
    };
    let Some(mut events) = state.population_effects.creation.clone() else {
        return Err(RuntimeError::FunctionContract(
            "population call lost its creation history".into(),
        ));
    };
    let mut transferred_anchors = BTreeSet::new();
    let frontier =
        population_transfer_frontier(facts, definitions, validation_state.memory(), assumptions)?;
    for fact in &frontier {
        if let Some((base, _)) = fact.allocation() {
            // A returned allocation can name the same storage through the
            // call's result. Read its unique concrete storage coordinate from
            // the checked equality index; this moves an existing anchor and
            // grants neither allocation nor creation authority.
            let base = assumptions.equality_graph.storage_address(base);
            if events.tracks_storage_anchor(&base.base)
                && transferred_anchors.insert(base.base.clone())
            {
                events = events
                    .transfer_call_anchor(from_events, to_events, &base.base)
                    .map_err(|refusal| {
                        RuntimeError::FunctionContract(format!(
                            "allocation companion transfer refused: {refusal}"
                        ))
                    })?;
            }
            continue;
        }
        if let ResourceFact::Own(Resource::Composite { name, .. }, quantity) = fact
            && quantity.as_const() == Some(1)
            && let Ok(index) = definitions.binary_search_by(|definition| {
                crate::instrumentation::record_deterministic_work(1);
                definition.name().cmp(name)
            })
            && let definition = &definitions[index]
            && definition
                .contains()
                .iter()
                .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
        {
            let (children, _) = validation_state
                .checked_authority_wrapper_body(fact, definition, assumptions)
                .map_err(|reason| {
                    RuntimeError::FunctionContract(format!(
                        "population call control transfer refused: {reason}"
                    ))
                })?;
            let memory_count = children
                .iter()
                .filter(|child| child.memory_own_range().is_some())
                .count();
            let authorities = children
                .iter()
                .filter_map(|child| match child {
                    ResourceFact::Own(Resource::PopulationAuthority(description), quantity)
                        if quantity.as_const() == Some(1) =>
                    {
                        Some(description)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let allocations = children
                .iter()
                .filter_map(ResourceFact::allocation)
                .collect::<Vec<_>>();
            if memory_count == 0
                || authorities.is_empty()
                || allocations.len() > 1
                || children.len() != authorities.len() + memory_count + allocations.len()
            {
                return Err(RuntimeError::FunctionContract(
                    "population call control requires owned memory, authorities, and at most one allocation".into(),
                ));
            }
            for description in &authorities {
                events = events
                    .transfer_call_fact(from_events, to_events, description, true)
                    .map_err(|refusal| {
                        RuntimeError::FunctionContract(format!(
                            "population call control transfer refused: {refusal}"
                        ))
                    })?;
            }
            let description = authorities[0];
            if let Some((base, _)) = allocations.first() {
                let Some(
                    [crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))],
                ) = (description.arguments()).fixed_values::<1>()
                else {
                    return Err(RuntimeError::FunctionContract(
                        "population call control needs one pointer anchor".into(),
                    ));
                };
                if *base != pointer.address() {
                    return Err(RuntimeError::FunctionContract(
                        "population call allocation does not match its authority anchor".into(),
                    ));
                }
                // An external control carries its checked allocation fact,
                // but no C creation event or creator right. Its authority
                // custody moved above; only real anchors have an additional
                // creation-ledger capability to transfer.
                if !events.recognizes_imported_population(description)
                    && transferred_anchors.insert(base.base.clone())
                {
                    events = events
                        .transfer_call_anchor(from_events, to_events, &base.base)
                        .map_err(|refusal| {
                            RuntimeError::FunctionContract(format!(
                                "population call allocation transfer refused: {refusal}"
                            ))
                        })?;
                }
            }
            continue;
        }
        if let ResourceFact::Own(Resource::Instance(instance), quantity) = fact {
            let description = ResourceDescription::from_instance(instance);
            if events.tracks_population(&description)
                && !events.recognizes_imported_population(&description)
            {
                events = events
                    .transfer_call_fact_quantity(
                        from_events,
                        to_events,
                        &description,
                        false,
                        quantity.native_compat(),
                        assumptions,
                    )
                    .map_err(|refusal| {
                        RuntimeError::FunctionContract(format!(
                            "named population call transfer refused: {refusal}"
                        ))
                    })?;
            }
            continue;
        }
        let (description, authority_fact, quantity) = match fact {
            ResourceFact::Own(Resource::PopulationAuthority(description), quantity)
                if quantity.as_const() == Some(1) =>
            {
                (description.clone(), true, quantity)
            }
            ResourceFact::Own(Resource::Composite { name, arguments }, quantity) => (
                ResourceDescription::new(
                    name.clone(),
                    arguments.clone(),
                    ResourceFieldSchema::new(vec![]).expect("empty schema"),
                ),
                false,
                quantity,
            ),
            ResourceFact::Own(Resource::PopulationAuthority(_), _) => {
                return Err(RuntimeError::FunctionContract(
                    "population call requires one exact authority".into(),
                ));
            }
            _ => continue,
        };
        if !authority_fact && !events.tracks_population(&description) {
            continue;
        }
        events = events
            .transfer_call_fact_quantity(
                from_events,
                to_events,
                &description,
                authority_fact,
                quantity.native_compat(),
                assumptions,
            )
            .map_err(|refusal| {
                RuntimeError::FunctionContract(format!(
                    "population call transfer refused: {refusal}; declared {} of {}",
                    quantity
                        .as_const()
                        .map_or_else(|| "quantity".into(), |quantity| quantity.to_string()),
                    description.family(),
                ))
            })?;
    }
    Arc::make_mut(&mut state.population_effects).creation = Some(events);
    Ok(state)
}

/// Rejoins returned owned pieces with their immediate indexed neighbours on
/// the non-stable-view route. Stable-view recovery restores each exact escrow
/// without normalizing its block. Neither route rebuilds the caller frame.
fn rejoin_borrowed_memory(
    resources: ResourceContext,
    transfer: &FunctionResourceTransfer,
    assumptions: &PureFactContext,
) -> ResourceContext {
    let seeds = transfer
        .borrowed_inputs
        .iter()
        .filter(|input| input.fact.memory_own_range().is_some())
        .map(|input| input.fact.clone())
        .collect::<Vec<_>>();
    if seeds.is_empty() {
        return resources;
    }
    resources.rejoined_memory_around(&seeds, assumptions)
}

/// `output_assumptions` carries the call's certified output facts (the
/// callee's ensures) on top of `assumptions`, for matching a produced
/// composite's viewed pieces, which are evaluated at the post-state, against
/// the descriptions lent at entry. It is not used to decide obligations.
/// `return_resources` and `transfer.candidate_output_views` come from the same
/// contract-return construction: the latter names every newly declared view.
/// The unchanged frame and supported owner projections need no new authority.
fn recover_candidate_stable_view_resources(
    caller_state: &ExecutionState,
    callee_state: &ExecutionState,
    transfer: &FunctionResourceTransfer,
    return_resources: ResourceContext,
    escrow_boundary: EscrowRecoveryBoundary,
    assumptions: &PureFactContext,
    output_assumptions: &PureFactContext,
    obligations: &[ProofObligation],
) -> Result<
    (
        ResourceContext,
        Option<LoanLedger>,
        Option<super::loans::LoanParticipantId>,
        LoanViewBindings,
        Option<Arc<CheckedLoanCallEvidence>>,
    ),
    RuntimeError,
> {
    let Some(plan) = &transfer.stable_view_plan else {
        if let Some(produced) = transfer.produced_borrowing_pieces.first() {
            let (head, piece) = (&produced.support.head, &produced.piece);
            return Err(RuntimeError::FunctionContract(format!(
                "produced borrowing composite `{}` packages a view `{}` that no viewed input of this call backs",
                head.diagnostic_summary(),
                piece.diagnostic_summary()
            )));
        }
        return Ok((
            rejoin_borrowed_memory(return_resources, transfer, assumptions),
            caller_state.loan_ledger().cloned(),
            caller_state.loan_participant(),
            caller_state.loan_view_bindings().clone(),
            None,
        ));
    };
    let Some(actual_ledger) = callee_state.loan_ledger() else {
        return Err(RuntimeError::LoanRefusal(Box::new(
            LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Recovery),
        )));
    };
    if actual_ledger != &plan.ledger {
        return Err(RuntimeError::LoanRefusal(Box::new(
            LoanRefusal::StalePredecessor.diagnostic(LoanRefusalOperation::Recovery),
        )));
    }
    if callee_state.loan_participant() != Some(plan.callee_participant()) {
        return Err(RuntimeError::LoanRefusal(Box::new(
            LoanRefusal::WrongHolder.diagnostic(LoanRefusalOperation::Recovery),
        )));
    }
    // A call with nothing lent still has step 7 work when it consumed a
    // borrowing composite (its hold is released) or produced one (its
    // borrow must be backed, which no loan of this call can do).
    if !plan.has_stable_views()
        && plan.mutex_uses.is_empty()
        && plan.transferred_holds.is_empty()
        && transfer.produced_borrowing_pieces.is_empty()
    {
        return Ok((
            rejoin_borrowed_memory(return_resources, transfer, assumptions),
            caller_state.loan_ledger().cloned(),
            caller_state.loan_participant(),
            caller_state.loan_view_bindings().clone(),
            None,
        ));
    }
    // Do not use the path assumptions to decide this: they intentionally
    // include the obligation list for later proof discharge, which would
    // make an unresolved return condition appear already proved. Candidate
    // recovery remains fail-closed for ordinary calls. Preparation alone may
    // retain a conditional successor: its obligations stay attached, and the
    // proof driver cannot publish it until it has proved every one at input.
    if !obligations.is_empty() && !assumptions.retains_required_obligations() {
        return Err(RuntimeError::PendingCallObligations(obligations.into()));
    }
    // Escaping borrows (step 7). Every viewed piece a produced or returned
    // owned composite packages must be backed by exactly one loan of this
    // call: a view lent here (the composite keeps that loan open and holds
    // it), or the hold binding the composite itself brought in (the callee
    // returned it, so it keeps its borrow). None, or more than one, is
    // refused: a composite describing memory no loan stabilizes would let
    // the caller write or free what the composite still reads, and an
    // ambiguous backing cannot be elided.
    let mut escaping =
        std::collections::BTreeMap::<LoanId, Vec<super::loans::EscapingComposite>>::new();
    let mut rebound_heads =
        BTreeMap::<ResourceOccurrenceId, (ResourceFact, LoanViewBinding)>::new();
    let mut escaped_occurrences = BTreeSet::new();
    let backing_sources =
        return_loan_backing::ReturnLoanBackings::from_plan(plan, output_assumptions);
    for produced in &transfer.produced_borrowing_pieces {
        let head = &produced.support.head;
        let piece = &produced.piece;
        let selected = backing_sources.select(head, piece, &plan.ledger, output_assumptions);
        let (backing_count, entering, selected_loan) = match selected {
            Ok(source) => (1, source.entering, Some(source.loan)),
            Err(ambiguous) => (if ambiguous { 2 } else { 0 }, None, None),
        };
        match (backing_count, entering) {
            (0, _) => {
                return Err(RuntimeError::FunctionContract(format!(
                    "produced borrowing composite `{}` packages a view `{}` that no viewed input of this call backs",
                    head.diagnostic_summary(),
                    piece.diagnostic_summary()
                )));
            }
            (1, Some(binding)) => {
                if rebound_heads
                    .get(&produced.support.occurrence)
                    .is_some_and(|(_, existing)| existing != &binding)
                {
                    return Err(RuntimeError::FunctionContract(format!(
                        "produced borrowing composite `{}` has no occurrence to carry its borrow",
                        head.diagnostic_summary()
                    )));
                }
                rebound_heads
                    .entry(produced.support.occurrence)
                    .or_insert_with(|| (head.clone(), binding));
            }
            (1, None) => {
                let loan = selected_loan.expect("the producer selected one backing loan");
                if escaped_occurrences.insert((loan, produced.support.occurrence)) {
                    escaping
                        .entry(loan)
                        .or_default()
                        .push(produced.support.clone());
                }
            }
            _ => {
                return Err(RuntimeError::FunctionContract(format!(
                    "produced borrowing composite `{}` packages a view `{}` that more than one viewed input of this call could back; the borrow cannot be elided",
                    head.diagnostic_summary(),
                    piece.diagnostic_summary()
                )));
            }
        }
    }
    let retained_holds = rebound_heads
        .values()
        .filter_map(|(_, binding)| binding.hold)
        .collect::<BTreeSet<_>>();
    let consumed_holds = plan
        .transferred_holds
        .iter()
        .filter(|(fact, binding)| {
            !binding
                .hold
                .is_some_and(|hold| retained_holds.contains(&hold))
                && !return_resources.contains_exact_representation(fact)
        })
        .map(|(_, binding)| binding.clone())
        .collect::<Vec<_>>();
    let mut residual = return_resources;
    for fact in plan.mutex_use_requirements.values() {
        residual = residual
            .without_fact_delaying_normalization(fact, assumptions)
            .ok_or_else(|| RuntimeError::MissingResource {
                resource: Box::new(fact.clone()),
            })?;
    }

    // A return view can only survive the call scope when it is one of the
    // checked child views that entered the call, when the caller already held
    // a checked outer view that entails it, or when the return published it as
    // a supported projection of an exact owned occurrence the caller still
    // holds.  In particular, an owned input must not let a callee mint an
    // unrelated view whose binding would otherwise be composed into the
    // recovered caller frame after the child scope closes, and a view is never
    // accepted merely because some equal owner happens to satisfy it.
    let returned_inputs = plan
        .stable_views()
        .iter()
        .map(|view| view.requirement.fact.clone())
        .collect::<BTreeSet<_>>();
    let mut checked_return_views = std::collections::BTreeSet::new();
    // Only this call's newly published views need return-authority checks.
    // The residual also contains the unchanged caller frame; produced owner
    // projections already retain their checked support occurrences.
    for fact in &transfer.candidate_output_views {
        if !fact.is_view() || !checked_return_views.insert((*fact).clone()) {
            continue;
        }
        let returned_input = returned_inputs.contains(fact);
        let preserved_outer = caller_state
            .loan_ledger()
            .zip(caller_state.loan_participant())
            .is_some_and(|(ledger, participant)| {
                caller_state
                    .loan_view_bindings()
                    .select_returned_view_authority(fact, caller_state.resources(), assumptions)
                    .is_some_and(|authority| {
                        ledger
                            .validate_returned_view_authority(authority, participant)
                            .is_ok()
                    })
            });
        // A duplicable core published from an exact returned owned occurrence
        // is an observation of that ownership, not a second live capability:
        // the reverse index drops it when the occurrence is consumed or its
        // memory support is invalidated.  Requiring the recorded occurrence
        // keeps this distinct from fact equality against an ambient owner.
        let projected_from_owner =
            residual
                .exact_projection_support(fact)
                .is_some_and(|(support_occurrence, support)| {
                    residual.support_occurrence_is_live(support_occurrence, support)
                });
        // A view of read-only storage is intrinsic read authority rather
        // than a capability this call lent, minted, or must recover: no
        // path may write those bytes, so nothing has to stabilize them,
        // and the caller held the same authority before the call. Entry
        // already decides it with this exact block test, in
        // `install_borrowed_contract_inputs` (such a contract input view
        // gets no borrowed root) and in `intrinsic_read_views` (such a
        // requirement is supplied without a ledger transition; see the
        // implicit-local-authority rule in docs/internals/stable-views.md).
        // The return route has to admit it on the
        // same terms, or a call that merely carries one across its
        // boundary would be refused for having no binding that was never
        // created. Ordinary mutable storage, file-static globals included,
        // is not read-only and still needs one of the three routes above.
        let intrinsic_read_only = matches!(
            fact.resource(),
            Resource::Memory(range)
                if caller_state.memory().is_read_only_block(&range.base().base)
        );
        if !returned_input && !preserved_outer && !projected_from_owner && !intrinsic_read_only {
            return Err(RuntimeError::UnbackedReturnedView {
                view: Box::new((*fact).clone()),
            });
        }
    }
    for stable_view in plan.stable_views() {
        if residual.contains_exact_representation(&stable_view.requirement.fact) {
            residual = residual
                .without_fact(&stable_view.requirement.fact, assumptions)
                .ok_or_else(|| {
                    RuntimeError::FunctionContract(
                        "stable-view return retained an unrecoverable view".to_string(),
                    )
                })?;
        }
    }
    // Recover into the actual constructed return. The loan operation admits
    // each recovered source once and retains that successor, including the
    // output cores' exact support metadata.
    let mut recovery = plan.clone().recover_returned_views(
        residual,
        &escrow_boundary,
        assumptions,
        &escaping,
        &consumed_holds,
    )?;
    retain_rebound_composite_holds(&mut recovery, &mut rebound_heads, plan.caller_participant())?;
    let loan_evidence = Arc::new(CheckedLoanCallEvidence::new(
        plan.clone(),
        recovery.ledger.clone(),
        recovery.terminal_ledger.clone(),
        recovery.transitions.clone(),
        recovery.hold_base_ledger.clone(),
        recovery.hold_transitions.clone(),
    ));
    // Recheck the kernel-issued discharge evidence from the exact callee root
    // before installing the canonical predecessor root in the caller state.
    recovery
        .recheck_transitions(actual_ledger, plan.caller_participant())
        .map_err(|error| {
            RuntimeError::LoanRefusal(Box::new(error.diagnostic_with_subject(
                LoanRefusalOperation::Recovery,
                recovery.diagnostic_subject(),
            )))
        })?;
    let recovered_ledger = recovery.ledger;
    let mut recovered_resources = recovery.resources;
    let mut recovered_bindings = recovery.view_bindings;
    for (occurrence, binding) in recovery.recovered_hold_occurrences {
        recovered_resources = recovered_resources.with_loan_dependency(occurrence, binding.clone());
        recovered_bindings = recovered_bindings.with_inserted(occurrence, binding);
    }
    // The producer retained the exact destination occurrence. Equal head
    // descriptions and unrelated ambient owners cannot select this binding.
    for escaped in recovery
        .escaped_holds
        .into_iter()
        .chain(
            rebound_heads
                .into_iter()
                .map(|(occurrence, (head, binding))| super::loans::EscapedHold {
                    occurrence,
                    head,
                    binding,
                }),
        )
    {
        (recovered_resources, recovered_bindings) =
            install_returned_composite_hold(recovered_resources, recovered_bindings, escaped)?;
    }
    Ok((
        recovered_resources,
        Some(recovered_ledger),
        Some(plan.caller_participant()),
        recovered_bindings,
        Some(loan_evidence),
    ))
}

/// A retained input hold may support one returned owner directly. Further
/// returned occurrences get distinct holds under the same read authority.
fn retain_rebound_composite_holds(
    recovery: &mut super::loans::StableViewRecovery,
    heads: &mut BTreeMap<ResourceOccurrenceId, (ResourceFact, LoanViewBinding)>,
    caller: super::loans::LoanParticipantId,
) -> Result<(), RuntimeError> {
    let mut assigned = BTreeSet::new();
    for (_, binding) in heads.values_mut() {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("retain returned composite hold", 1);
        let hold = binding
            .hold
            .expect("a transferred composite carries a hold");
        if !assigned.insert(hold) {
            let (ledger, hold, transition) = recovery
                .ledger
                .hold_with_transition(binding, caller)
                .map_err(|error| {
                    RuntimeError::LoanRefusal(Box::new(
                        error.diagnostic(LoanRefusalOperation::Recovery),
                    ))
                })?;
            recovery.ledger = ledger;
            recovery.hold_transitions.push(transition);
            binding.hold = Some(hold);
        }
    }
    Ok(())
}

/// Attach the hold produced by recovery to its selected returned owner.
/// This consumes the producer's destination identity, without a head census.
fn install_returned_composite_hold(
    resources: ResourceContext,
    bindings: LoanViewBindings,
    escaped: super::loans::EscapedHold,
) -> Result<(ResourceContext, LoanViewBindings), RuntimeError> {
    let _checking =
        crate::instrumentation::CheckingWorkScope::new("install returned composite hold", 1);
    if resources
        .loan_dependency(escaped.occurrence)
        .is_some_and(|existing| existing != &escaped.binding)
    {
        return Err(RuntimeError::FunctionContract(format!(
            "produced borrowing composite `{}` has no occurrence to carry its borrow",
            escaped.head.diagnostic_summary()
        )));
    }
    Ok((
        resources.with_loan_dependency(escaped.occurrence, escaped.binding.clone()),
        bindings.with_inserted(escaped.occurrence, escaped.binding),
    ))
}

/// One normalized resource clause after its address/argument loads have been
/// checked.  The fact alone is deliberately not enough for a transition:
/// an owned fact can be borrowed at the contract boundary, and an instance
/// can retain entry identity while its fields are checked at post state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CheckedResourceFact {
    pub(crate) fact: ResourceFact,
    pub(crate) role: ResourceTransferRole,
    pub(crate) state_source: ResourceStateSource,
    pub(crate) clause_position: Option<(usize, usize)>,
    /// Index of this leaf in the normalized resource section, when it was
    /// evaluated from a contract. Distinct leaves may share a source clause.
    pub(crate) section_index: Option<usize>,
    /// Caller-selected exact named authority for a mutex-use loan. The
    /// planner must consume this source, never select by address instead.
    pub(crate) selected_mutex_source: Option<std::sync::Arc<(Variable, ResourceFact)>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FunctionMemoryEffectProjection {
    ranges: Vec<MemoryRange>,
    evidence_facts: ExecutionFacts,
    /// The owned requirement each projected range came out of, for the ranges
    /// a checked resource transition produced. An explicit effect segment
    /// names no requirement and appears here not at all; the call site reads
    /// this only to recover an effect's caller-side source occurrence and never to
    /// widen or narrow the ranges themselves.
    range_sources: Vec<(MemoryRange, ResourceFact)>,
}

impl FunctionMemoryEffectProjection {
    pub(crate) fn ranges(&self) -> &[MemoryRange] {
        &self.ranges
    }
}

/// Candidate calls must account for explicit mutable effects separately from
/// the resource transition.  A mutable range is safe beside a lent view only
/// when the kernel has concrete interval evidence or an existing separation
/// fact; an unknown alias is rejected conservatively.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CandidateMemoryRangeRelation {
    Disjoint,
    Overlap,
    SeparationUnproved,
}

/// Whether the kernel's arithmetic proves two ranges separate under the
/// current path assumptions.  This is the separation counterpart of
/// `memory_ranges_proven_overlapping` and follows it exactly: equal element
/// widths, one base frame reached by a syntactic base delta, and the same
/// decision procedure asked for the ordering `end <= start`.  The frame
/// change is directional, so both orders are tried.  An undecided ordering
/// stays undecided, so an unknown alias is still reported as unproved
/// separation rather than as disjointness.
fn candidate_memory_ranges_proven_separate(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // This arithmetic rule uses signed 32-bit indices; wide ranges are undecided.
    if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
        return false;
    }
    if left.element_width() != right.element_width() {
        return false;
    }
    let separate_in_frame = |anchor: &MemoryRange, other: &MemoryRange| {
        crate::instrumentation::record_deterministic_work(1);
        let Some(base_delta) = other
            .base()
            .shared_element_index_from_base_with_width(anchor.base(), anchor.element_width())
        else {
            return false;
        };
        let other_start = crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Legacy(other.start()),
        );
        let other_end = crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Legacy(other.end()),
        );
        assumptions.decide(&crate::kernel::assumptions::index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(anchor.end()),
            other_start.operand_view(),
        )) == Some(true)
            || assumptions.decide(&crate::kernel::assumptions::index_comparison(
                CompareRelation::LessEqual,
                other_end.operand_view(),
                MachineOperandView::Legacy(anchor.start()),
            )) == Some(true)
    };
    separate_in_frame(left, right) || separate_in_frame(right, left)
}

/// Index the projected effect ranges by the owned occurrence each was
/// reserved out of: the projection says which requirement produced a range,
/// and the plan says which caller occurrence supplied that requirement.
/// Two sources claiming one range, or one requirement reserved from two
/// occurrences, would not be a partition; such a key records no support
/// rather than picking a support, which leaves that effect on the arithmetic
/// comparison.
fn reserved_effect_support_index(
    range_sources: &[(MemoryRange, ResourceFact)],
    reserved_ownership_supports: &[(ResourceFact, ResourceOccurrenceId)],
) -> BTreeMap<MemoryRange, Option<BTreeSet<ResourceOccurrenceId>>> {
    let mut by_requirement = BTreeMap::<&ResourceFact, Option<ResourceOccurrenceId>>::new();
    for (fact, support) in reserved_ownership_supports {
        by_requirement
            .entry(fact)
            .and_modify(|known| {
                if *known != Some(*support) {
                    *known = None;
                }
            })
            .or_insert(Some(*support));
    }
    // One canonical range may come from several requirements -- the unnamed
    // footprint comes from every requirement that reaches unnamed memory --
    // so each range keeps the set of occurrences it was reserved out of, and
    // loses its support when any of them has none.
    let mut index = BTreeMap::<MemoryRange, Option<BTreeSet<ResourceOccurrenceId>>>::new();
    for (range, source) in range_sources {
        let support = by_requirement.get(source).copied().flatten();
        let entry = index
            .entry(canonical_memory_range(range.clone()))
            .or_insert_with(|| Some(BTreeSet::new()));
        match support {
            Some(support) => {
                if let Some(supports) = entry {
                    supports.insert(support);
                }
            }
            None => *entry = None,
        }
    }
    index
}

/// The partition read at a call: a mutable effect reserved out of one owned
/// occurrence and a view lent from a different owned occurrence are bytewise
/// disjoint by the resource context's partition invariant (step 4), so the
/// relation is settled by reservation support and the arithmetic oracle is not
/// consulted. This never decides a pair the other way: an effect with no
/// reservation behind it (an explicit `mutable` segment, or a range a
/// composite expansion produced) and a view with no owner behind it (an
/// intrinsic or empty-composite view) carry no support, and an effect and
/// a view from the same occurrence -- a partial borrow of one owner, D8 --
/// still need the arithmetic proof. An effect reserved out of several
/// occurrences is disjoint from a view lent from none of them.
fn effect_is_disjoint_from_view_by_support(
    reserved_effect_supports: &BTreeMap<MemoryRange, Option<BTreeSet<ResourceOccurrenceId>>>,
    effect: &MemoryRange,
    viewed_support: Option<ResourceOccurrenceId>,
) -> bool {
    let Some(viewed_support) = viewed_support else {
        return false;
    };
    let Some(Some(effect_supports)) =
        reserved_effect_supports.get(&canonical_memory_range(effect.clone()))
    else {
        return false;
    };
    !effect_supports.is_empty() && !effect_supports.contains(&viewed_support)
}

fn candidate_memory_ranges_relation(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> CandidateMemoryRangeRelation {
    let relation = candidate_memory_ranges_relation_by_bounds(left, right, assumptions);
    // Only an undecided pair reaches the arithmetic oracle, so a proven
    // overlap can never be reinterpreted as separation and the concrete
    // comparison keeps deciding the common case without a query.
    if relation == CandidateMemoryRangeRelation::SeparationUnproved
        && candidate_memory_ranges_proven_separate(left, right, assumptions)
    {
        return CandidateMemoryRangeRelation::Disjoint;
    }
    relation
}

fn candidate_memory_ranges_relation_by_bounds(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> CandidateMemoryRangeRelation {
    if left.base().blocks_proven_distinct(right.base())
        || assumptions
            .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(left, right)
    {
        return CandidateMemoryRangeRelation::Disjoint;
    }
    if left.base() == right.base() {
        // One base, so the element indexes scaled to bytes place both ranges
        // in the same coordinates. The indexes are the *signed* numbers
        // `memory_range_byte_count` scales, which is the reading
        // `resources_structurally_separate` takes on the same comparison:
        // zero-extended, `a[-1..2]`'s start landed four gigabytes above
        // `a[0..1]`'s end and the two shared cells were reported `Disjoint`.
        // `Disjoint` is final here — `candidate_memory_ranges_relation` only
        // consults the arithmetic oracle for a pair this leaves undecided —
        // so it suppressed the `LoanRefusal` a caller's overlapping effect
        // and view owe each other.
        let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
            left.signed_constant_start(),
            left.signed_constant_end(),
            right.signed_constant_start(),
            right.signed_constant_end(),
        ) else {
            return CandidateMemoryRangeRelation::SeparationUnproved;
        };
        let left_width = i64::from(left.element_width());
        let right_width = i64::from(right.element_width());
        let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
            left_start.checked_mul(left_width),
            left_end.checked_mul(left_width),
            right_start.checked_mul(right_width),
            right_end.checked_mul(right_width),
        ) else {
            return CandidateMemoryRangeRelation::SeparationUnproved;
        };
        return if left_end <= right_start || right_end <= left_start {
            CandidateMemoryRangeRelation::Disjoint
        } else {
            CandidateMemoryRangeRelation::Overlap
        };
    }
    // Wide intervals cannot be normalized to a signed 32-bit byte count.
    if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    }
    // Different bases. `byte_footprint` puts each range's first element in
    // the block's own coordinates through `offset_by_elements`, which
    // sign-extends, so the two starts are already signed numbers. The byte
    // counts stay `u32`: a count that is negative as an `int32` reads as a
    // range longer than the address space, which can only report *less*
    // separation, never more.
    let (left_base, left_bytes) = left.byte_footprint();
    let (right_base, right_bytes) = right.byte_footprint();
    let Some(left_start) = left_base.offset.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(right_start) = right_base.offset.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(left_length) = left_bytes.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(right_length) = right_bytes.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(left_end) = left_start.checked_add(i64::from(left_length)) else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(right_end) = right_start.checked_add(i64::from(right_length)) else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    if left_base.base != right_base.base {
        CandidateMemoryRangeRelation::SeparationUnproved
    } else if left_end <= right_start || right_end <= left_start {
        CandidateMemoryRangeRelation::Disjoint
    } else {
        CandidateMemoryRangeRelation::Overlap
    }
}

#[derive(Clone, Debug)]
enum VerifiedAllocationDeltaError {
    Runtime(RuntimeError),
    InconsistentReturnedAllocation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum AllocationContinuity {
    Same,
    Distinct,
    /// The blocks may be one, but the sizes have different formats (D5).
    CrossKind,
    Undecided(ConditionTerm),
    Inconsistent,
}

fn canonical_memory_range(range: MemoryRange) -> MemoryRange {
    let base = Address {
        base: range.base().base.clone(),
        offset: crate::kernel::eval::canonical_offset_term(&range.base().offset),
    };
    let (start, end) = range.bound_terms();
    range.with_bounds(
        base,
        crate::kernel::eval::canonical_term(start),
        crate::kernel::eval::canonical_term(end),
    )
}

fn function_needs_outcome_resource_transfer(function: &ProgramFunction) -> bool {
    !function.resource_constructors().is_empty()
        || (!function.exceptional_signature().is_empty()
            && (!function.resource_requires().is_empty()
                || !function.resource_ensures().is_empty()))
        || function
            .composite_resource_definitions()
            .iter()
            .any(CompositeResourceDefinition::needs_outcome_resource_transfer)
}

fn function_changes_declared_resource_quantities(function: &ProgramFunction) -> bool {
    function.resource_requires() != function.resource_ensures()
}

/// Applies one explicitly authorized abstract-token construction to a return
/// state. Construction is a zero-source resource event: unlike a transfer,
/// it does not consume a caller resource or rely on a body representation.
pub(super) fn construct_program_function_resource(
    state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    result: &ProgramValue,
    constructed: &ResourceFact,
    assumptions: &PureFactContext,
) -> ExecutionResult<Result<ExecutionState, RuntimeError>> {
    // Constructing a token of a known ordinary abstract family creates no
    // population member; any other construction would need its authority.
    let ordinary_token = matches!(
        constructed.resource(),
        Resource::Token { name, .. }
            if function.contract_interface().is_ordinary_abstract_family(name)
    );
    if !ordinary_token {
        return Ok(Err(RuntimeError::FunctionContract(
            "generic resource construction cannot create members".to_string(),
        )));
    }
    let Some(mut evaluation_state) = program_function_entry_state(state, function, arguments)
    else {
        return Ok(Err(RuntimeError::FunctionContract(
            "could not bind function arguments for resource construction".to_string(),
        )));
    };
    if function.return_type() != ProgramType::Void {
        set_function_result(&mut evaluation_state, function, result.clone());
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let mut authorized = false;
    for specification in function.resource_constructors() {
        let candidate = match evaluate_function_resource_spec(
            &evaluation_state,
            specification,
            assumptions,
            &mut budget,
        )? {
            Ok(candidate) => candidate,
            Err(error) => return Ok(Err(error)),
        };
        if candidate == *constructed {
            authorized = true;
            break;
        }
    }
    if !authorized {
        return Ok(Err(RuntimeError::FunctionContract(
            "resource construction is not authorized by the function contract".to_string(),
        )));
    }
    let ResourceFact::Own(Resource::Token { .. }, quantity) = constructed else {
        return Ok(Err(RuntimeError::FunctionContract(
            "resource construction requires one owned abstract token".to_string(),
        )));
    };
    if quantity.as_const() != Some(1) {
        return Ok(Err(RuntimeError::FunctionContract(
            "resource construction creates exactly one token".to_string(),
        )));
    }
    if state.resources().contains_exact_representation(constructed) {
        return Ok(Err(RuntimeError::FunctionContract(
            "resource construction would duplicate an existing token".to_string(),
        )));
    }
    let resources = match state
        .resources()
        .clone()
        .try_compose_with_fact(constructed.clone(), assumptions)
    {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };
    Ok(Ok(state.clone().with_resource_context(resources)))
}

fn complete_void_fallthrough(
    function: &ProgramFunction,
    outcome: StatementOutcome,
) -> StatementOutcome {
    match (function.return_type(), outcome) {
        (ProgramType::Void, StatementOutcome::Normal(state)) => {
            super::eval::return_authority_refusal(&state).unwrap_or(StatementOutcome::Return {
                value: ProgramValue::Void.into(),
                state,
            })
        }
        (_, outcome) => outcome,
    }
}

#[cfg(test)]
pub(super) fn execute_program_function_paths(
    state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<FunctionPath>> {
    execute_program_function_paths_with_contract_resources(
        state,
        function,
        arguments,
        assumptions,
        execution_context,
        budget,
        false,
        false,
    )
}

/// Executes a called function's body across its paths.
///
/// `prepare_contract_resources` says whether the body runs from the contract's
/// own entry resources. A whole-function judgment over a bare caller frame
/// executes the body in that frame; the contract routes cross the resource
/// boundary, so the views the contract declares become loans of this
/// application and recovery returns them.
/// The body runs under the concrete judgment, which unrolls loops.
#[allow(clippy::too_many_arguments)]
pub(super) fn execute_program_function_paths_with_contract_resources(
    state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    prepare_contract_resources: bool,
    defer_conditional_resource_effect: bool,
) -> ExecutionResult<Vec<FunctionPath>> {
    execute_function_paths(
        state,
        function,
        arguments,
        assumptions,
        execution_context,
        budget,
        prepare_contract_resources,
        defer_conditional_resource_effect,
        &mut super::eval::StatementJudgment::Executes,
    )
}

/// Refresh only caller slots named by the completed body's store events.
/// Callee execution has its own bindings and cannot update these by name.
fn refresh_returned_local_bindings_from_stores(
    outcome: &mut FunctionOutcome,
    facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) {
    let state = match outcome {
        FunctionOutcome::Return { state, .. } | FunctionOutcome::Throw { state, .. } => state,
        _ => return,
    };
    for fact in facts.fact_iter() {
        let Some(store) = fact.certified_store_data() else {
            continue;
        };
        crate::instrumentation::record_deterministic_work(1);
        // Refresh the object whose bytes were written, including interior
        // byte stores. The return state's value is authoritative, rather
        // than an earlier store's value or a narrower cell at its address.
        crate::kernel::eval::refresh_scalar_local_after_memory_store(
            state,
            &store.pointer,
            &store.value,
            assumptions,
        );
    }
}

/// `ProgramFunctionVerifies` for `function` applied to `arguments`.
#[cfg(test)]
pub(super) fn execute_program_function_verification_paths(
    state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
    prepare_contract_resources: bool,
    defer_conditional_resource_effect: bool,
) -> ExecutionResult<Vec<FunctionPath>> {
    execute_function_paths(
        state,
        function,
        arguments,
        assumptions,
        execution_context,
        budget,
        prepare_contract_resources,
        defer_conditional_resource_effect,
        &mut super::eval::StatementJudgment::Verifies(variables),
    )
}

/// Profiles `operation` under `name` when the verification judgment runs
/// it; an execution's work is attributed to its caller.
fn measured_under<T>(
    verifies: bool,
    function: &ProgramFunction,
    name: &str,
    operation: impl FnOnce() -> T,
) -> T {
    if verifies {
        crate::instrumentation::measure_operation(
            function.name(),
            "independent kernel execution",
            name,
            operation,
        )
    } else {
        operation()
    }
}

/// `function` applied to `arguments` under `judgment`: arguments are
/// evaluated and bound, the contract's resources are prepared when the
/// judgment is over a whole function, the body runs, and each body outcome
/// becomes a function outcome at the boundary. The two judgments differ in
/// one step, which says so: verification installs the recursion anchor of a
/// function that declares a measure.
fn execute_function_paths(
    state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    prepare_contract_resources: bool,
    defer_conditional_resource_effect: bool,
    judgment: &mut super::eval::StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<FunctionPath>> {
    let verifies = matches!(judgment, super::eval::StatementJudgment::Verifies(_));
    budget.consume_function_call()?;
    if arguments.len() != function.parameters().len() {
        return Ok(vec![FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::WrongArity {
                expected: function.parameters().len(),
                actual: arguments.len(),
            }),
            Vec::new().into(),
            Vec::new(),
        )]);
    }

    let mut paths = Vec::new();
    for arguments_path in measured_under(
        verifies,
        function,
        "verification argument evaluation",
        || {
            evaluate_retained_program_arguments_paths(
                state,
                arguments,
                assumptions,
                budget,
                Some(execution_context.environment),
            )
        },
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(FunctionPath::new(
                outcome,
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let native_arguments = arguments_path
            .values
            .iter()
            .map(|value| value.native().into_owned())
            .collect::<Vec<_>>();
        if let Some(undefined_behavior) = freed_pointer_argument_conversion(
            state,
            function.contract_interface(),
            &native_arguments,
            &path_assumptions,
        ) {
            paths.push(FunctionPath::new(
                FunctionOutcome::UndefinedBehavior(undefined_behavior),
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }
        if let Some(refusal) = incompatible_pointer_argument(
            state,
            function.name(),
            function.contract_interface(),
            &native_arguments,
            &path_assumptions,
        ) {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(refusal),
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }
        let Some((argument_values, argument_obligations)) = coerce_program_function_arguments(
            function,
            &native_arguments,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                    argument_binding_error(function, &native_arguments).to_string(),
                )),
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        };
        let Some(callee_state) = bind_program_function_arguments_retained(
            state,
            function,
            &argument_values,
            &arguments_path.values,
        ) else {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
                arguments_path.facts,
                argument_obligations,
            ));
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
        );
        let (callee_state, resource_transfer) = if prepare_contract_resources {
            // The contract boundary of a whole-function judgment: the body
            // runs from the resources the contract declares, consumed
            // definitionally. Lending is the call site's job (the planner in
            // `execute_program_function_call_paths`) and the proof's entry
            // construction (`execution_state_with_borrowed_contract_inputs`); a
            // judgment over a body that already happened must not lend again.
            let resource_transfer = match prepare_function_resource_transfer(
                state,
                &callee_state,
                function,
                &body_assumptions,
                budget,
                true,
                ResourceTransitionPurpose::FunctionBoundary,
            )? {
                Ok(resource_transfer) => resource_transfer,
                Err(error) => {
                    paths.push(FunctionPath::new(
                        FunctionOutcome::RuntimeError(error),
                        arguments_path.facts,
                        argument_obligations,
                    ));
                    continue;
                }
            };
            (
                callee_state_with_resource_transfer(callee_state, &resource_transfer),
                Some(resource_transfer),
            )
        } else {
            (callee_state, None)
        };
        // A body that is judged as a whole is judged from its own entry, so
        // this is where the declared `decreases` measure is read and the
        // recursion anchor installed. The anchor is derived from the function
        // in hand, not from anything a caller supplies, and a function that
        // declares no measure gets the environment unchanged.
        //
        // Execution runs the body as it is, so it has no anchor to install:
        // a recursive call there executes, and the budget bounds it.
        let anchor = match judgment {
            super::eval::StatementJudgment::Verifies(_) => {
                crate::kernel::termination::program_function_recursion_anchor(
                    function,
                    &callee_state,
                    &body_assumptions,
                    budget,
                )
            }
            super::eval::StatementJudgment::Executes => Ok(None),
        };
        let anchored_environment = match anchor {
            Ok(Some(anchor)) => std::borrow::Cow::Owned(
                execution_context
                    .environment
                    .clone()
                    .with_recursion_anchor(anchor),
            ),
            Ok(None) => std::borrow::Cow::Borrowed(execution_context.environment),
            Err(message) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
                    arguments_path.facts,
                    argument_obligations,
                ));
                continue;
            }
        };
        let body_paths = measured_under(verifies, function, "verification body execution", || {
            execute_function_body_paths(
                &callee_state,
                function,
                &body_assumptions,
                ExecutionContext::new(&anchored_environment, execution_context.semantics),
                budget,
                judgment,
            )
        })?;
        for body_path in body_paths {
            let Some((mut facts, obligations)) =
                measured_under(verifies, function, "verification fact merge", || {
                    merge_execution_pure_facts_and_obligations(
                        &arguments_path.facts,
                        &argument_obligations,
                        &body_path.facts,
                        &body_path.obligations,
                        assumptions,
                    )
                })
            else {
                continue;
            };
            if let Some(parameter) = modified_by_value_aggregate_parameter_with_current_ensure(
                &callee_state,
                &body_path.outcome,
                function,
            ) {
                paths.push(FunctionPath::new(FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                        format!(
                            "by-value aggregate parameter `{parameter}` is modified, but a postcondition reads its current state"
                        ),
                    )), facts, obligations));
                continue;
            }
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations, loan_evidence) = if defer_conditional_resource_effect {
                without_loan_evidence(function_outcome_from_body(
                    state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
                    obligations,
                    &return_assumptions,
                    None,
                ))
            } else if let Some(resource_transfer) = &resource_transfer {
                if resource_transfer.stable_view_plan.is_some()
                    || function_needs_outcome_resource_transfer(function)
                {
                    function_outcome_from_body_with_resource_transfer(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        resource_transfer,
                        &argument_values,
                        true,
                        budget,
                    )?
                } else if function_changes_declared_resource_quantities(function) {
                    without_loan_evidence(function_outcome_from_body_changing_quantities(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                    )?)
                } else {
                    without_loan_evidence(function_outcome_from_body(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        None,
                    ))
                }
            } else {
                without_loan_evidence(function_outcome_from_body(
                    state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
                    obligations,
                    &return_assumptions,
                    None,
                ))
            };

            append_string_literal_loadable_facts(function, &outcome, &mut facts);

            paths.push(FunctionPath {
                call_parameters: None,
                outcome,
                facts,
                obligations,
                loan_evidence: append_checked_loan_evidence(
                    &body_path.loan_evidence,
                    loan_evidence,
                ),
            });
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

mod authority_contracts;
pub(in crate::kernel) use authority_contracts::*;

#[cfg(test)]
mod authority_helper_admission_tests;

pub(super) fn execute_program_function_call_paths(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<FunctionPath>> {
    if contract_reaches_population(function.contract_interface())
        && execution_context
            .environment
            .get_verified_function_rule(function.name())
            .is_none()
        && !execution_context
            .environment
            .get_external_function_rule(function.name())
            .is_some_and(|rule| {
                rule.is_scoped_unselected()
                    || authority_preserves_assumed_resource_contract(
                        rule.function.contract_interface(),
                    )
            })
    {
        let error = authority_call_refusal();
        return Ok(vec![FunctionPath::new(
            FunctionOutcome::RuntimeError(error),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    if let Some(selected) = execution_context
        .environment
        .selected_call_contract
        .as_deref()
    {
        let pointer = Address::function(function.name());
        let owned = contracts_for_pointer(
            &pointer,
            assumptions,
            execution_context.environment,
            &function.function_pointer_type(),
        );
        let contracts = owned.iter().collect::<Vec<_>>();
        if !contracts.iter().any(|contract| contract.name() == selected) {
            return Ok(vec![resource_call_failure(
                "selected contract is not established for this function with its call signature",
            )]);
        }
        return execute_program_function_contracts_paths(
            caller_state,
            &contracts,
            arguments,
            assumptions,
            execution_context.environment,
            budget,
        );
    }
    if let Some(rule) = execution_context
        .environment
        .get_external_function_rule(function.name())
    {
        // External summaries use the same body-independent application
        // interface as verified rules, but remain an assumption: do not
        // repackage one as `VerifiedFunctionRule`, whose type carries body
        // safety evidence. Applying the shared rule engine does not execute,
        // inspect, or certify the external body's storage.
        let binder_application = match selected_call_binder_application(
            rule.function.name(),
            rule.function.contract_interface(),
            caller_state,
            execution_context.environment,
            Some(&mut *budget),
        ) {
            Ok(application) => application,
            Err(message) => return Ok(vec![resource_call_failure(message)]),
        };
        return execute_verified_function_applications(
            caller_state,
            &[FunctionContractApplication {
                pointer_result: None,
                name: rule.function.name(),
                interface_name: rule.function.name(),
                interface: rule.function.contract_interface(),
                storage: Some(&rule.function),
                evidence: None,
                framed_rule: rule
                    .is_scoped_unselected()
                    .then_some(FramedCallRule::ScopedHypothesis { _rule: rule }),
                representation_copy: rule.representation_copy(),
                value_arguments: &[],
            }],
            None,
            binder_application
                .as_ref()
                .map(|application| (0, application)),
            arguments,
            assumptions,
            execution_context.environment,
            budget,
        );
    }
    // A header-provided `static inline` or `static __always_inline` helper
    // is called like any other function once it has a verified contract:
    // the contract is the call boundary. Only a helper with no contract runs
    // its checked C body at the call site, on the caller's own resources,
    // including while the surrounding function is being contract-certified.
    let executes_inline_body = function.has_inline_body()
        && execution_context
            .environment
            .get_verified_function_rule(function.name())
            .is_none();
    // A binder map selects a contract boundary, and an inline body run in
    // place has none: the body runs on the caller's resources, so the map
    // would bind nothing and silently mean something other than what the
    // proof wrote.
    if executes_inline_body
        && execution_context
            .environment
            .selected_call_binders
            .as_ref()
            .is_some_and(|transport| transport.names_call_to(function.name()))
    {
        return Ok(vec![resource_call_failure(
            "a binder map cannot select a contract for a `static inline` helper that has none: its body executes at the call site on the caller's resources; give the helper a Click contract, or step the call with `step()`",
        )]);
    }
    // Every other callee is opaque: its verified rule is the call. Bodies
    // are checked once, against their contracts, in their own proofs; a call
    // never runs one.
    if !executes_inline_body {
        let Some(rule) = execution_context
            .environment
            .get_verified_function_rule(function.name())
        else {
            let error = if function.verified_direct_contract_supported() {
                RuntimeError::MissingVerifiedFunctionRule(function.name().to_string())
            } else {
                RuntimeError::UnsupportedOpaqueFunctionContract(function.name().to_string())
            };
            return Ok(vec![FunctionPath::new(
                FunctionOutcome::RuntimeError(error),
                Vec::new().into(),
                Vec::new(),
            )]);
        };
        return execute_verified_function_rule(
            caller_state,
            rule,
            arguments,
            assumptions,
            execution_context.environment,
            budget,
        );
    }
    budget.consume_function_call()?;
    if arguments.len() != function.parameters().len() {
        return Ok(vec![FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::WrongArity {
                expected: function.parameters().len(),
                actual: arguments.len(),
            }),
            Vec::new().into(),
            Vec::new(),
        )]);
    }

    let mut paths = Vec::new();
    for arguments_path in evaluate_retained_program_arguments_paths(
        caller_state,
        arguments,
        assumptions,
        budget,
        Some(execution_context.environment),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(FunctionPath::new(
                outcome,
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let native_arguments = arguments_path
            .values
            .iter()
            .map(|value| value.native().into_owned())
            .collect::<Vec<_>>();
        if let Some(undefined_behavior) = freed_pointer_argument_conversion(
            caller_state,
            function.contract_interface(),
            &native_arguments,
            &path_assumptions,
        ) {
            paths.push(FunctionPath::new(
                FunctionOutcome::UndefinedBehavior(undefined_behavior),
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }
        if let Some(refusal) = incompatible_pointer_argument(
            caller_state,
            function.name(),
            function.contract_interface(),
            &native_arguments,
            &path_assumptions,
        ) {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(refusal),
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }
        let Some((argument_values, argument_obligations)) = coerce_program_function_arguments(
            function,
            &native_arguments,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                    argument_binding_error(function, &native_arguments).to_string(),
                )),
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        };
        if let Some(outcome) = aggregate_argument_read_refusal(
            caller_state,
            function.parameters(),
            &argument_values,
            &path_assumptions,
        ) {
            paths.push(FunctionPath::new(
                outcome,
                arguments_path.facts,
                argument_obligations,
            ));
            continue;
        }
        let Some(callee_state) = bind_program_function_arguments_retained(
            caller_state,
            function,
            &argument_values,
            &arguments_path.values,
        ) else {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
                arguments_path.facts,
                argument_obligations,
            ));
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
        );
        // An inline body is call-site code: it runs on the caller's own
        // resources and leaves the caller whatever it did not consume.
        // There is no contract boundary to transfer across. Under stable
        // views that includes the caller's loan ledger: the body's stores
        // are checked against the caller's active loans, its own view
        // clauses lend nothing, and any call it makes plans from and
        // recovers to the caller's ledger, whose evidence the path keeps.
        let callee_state = callee_state.with_resource_context(caller_state.resources().clone());
        let previous_inline_call = budget.inline_call_name.replace(function.name().to_string());
        let body_paths = execute_program_function_body_paths(
            &callee_state,
            function,
            &body_assumptions,
            execution_context,
            budget,
        );
        budget.inline_call_name = previous_inline_call;
        for body_path in body_paths? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &arguments_path.facts,
                &argument_obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations) = function_outcome_from_body(
                caller_state,
                function,
                complete_void_fallthrough(function, body_path.outcome),
                obligations,
                &return_assumptions,
                None,
            );
            let mut outcome = outcome;
            refresh_returned_local_bindings_from_stores(&mut outcome, &facts, &return_assumptions);
            paths.push(FunctionPath {
                call_parameters: None,
                outcome,
                facts,
                obligations,
                loan_evidence: body_path.loan_evidence,
            });
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// The successor of one statement-free application of a verified tactic rule.
#[derive(Clone)]
pub(crate) struct TacticRuleTransition {
    pub(crate) state: ExecutionState,
    pub(crate) facts: ExecutionFacts,
    /// The execution's kernel-variable mark after the application, which
    /// the caller installs so later steps cannot reuse an identity it minted.
    pub(crate) next_kernel_variable: u64,
}

/// Why a tactic application was refused. A missing precondition is kept as
/// the proposition, so the surface can name it in the reader's spelling.
#[derive(Clone, Debug)]
pub(crate) enum TacticApplicationRefusal {
    /// A precondition, with the kernel's own description of why it is owed
    /// (a recursion measure's descent, for one).
    MissingRequirement(Proposition, Option<String>),
    Refused(String),
}

/// Whether a certified body runs no code: it is one `return;` of no value.
fn body_runs_no_code(body: &ProgramStatement) -> bool {
    match body {
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)) => true,
        ProgramStatement::Seq(statements) => {
            matches!(statements.first().as_ref(), ProgramStatement::Skip)
                && body_runs_no_code(&statements.rest())
        }
        _ => false,
    }
}

/// Applies the verified rule of `name` at `state` with no C call statement.
///
/// The rule must be one certified for a procedure whose whole body is
/// `return;`. Such a procedure runs no code, so a call to it may be inserted
/// anywhere without changing what the program does; applying its rule here is
/// exactly that call, and the call boundary's own checks bind the selected
/// instances, consume and produce them, and add the `ensures` facts. This is
/// how a user-defined tactic is applied.
///
/// Every precondition the application emits must already be an available
/// fact in `facts`. A tactic application is a simple step: nothing is
/// searched for.
pub(crate) fn apply_verified_tactic_rule(
    state: &ExecutionState,
    name: &str,
    arguments: &[ProgramValue],
    facts: &crate::kernel::proof::PureFactStore,
    environment: &ExecutionEnvironment,
    next_kernel_variable: u64,
) -> Result<TacticRuleTransition, TacticApplicationRefusal> {
    use TacticApplicationRefusal::Refused;
    let function = environment
        .get_function(name)
        .ok_or_else(|| Refused(format!("unknown tactic `{name}`")))?;
    if !body_runs_no_code(function.body()) {
        return Err(Refused(format!(
            "`{name}` is a C function, not a tactic; its rule applies only at a call"
        )));
    }
    // A selected tactic is certified in this run (or held as its recursion
    // hypothesis while it is); an unselected one is the run's scoped
    // assumption, exactly as an unselected C callee is. Nothing else may
    // stand in for its contract.
    if environment.get_verified_function_rule(name).is_none()
        && !environment
            .get_external_function_rule(name)
            .is_some_and(ExternalFunctionRule::is_scoped_unselected)
    {
        return Err(Refused(format!(
            "tactic `{name}` has no verified rule in this proof"
        )));
    }
    let expressions = arguments
        .iter()
        .cloned()
        .map(ProgramExpression::Value)
        .collect::<Vec<_>>();
    let mut budget = ExecutionBudget::continuing_from(next_kernel_variable);
    let paths = execute_program_function_call_paths(
        state,
        function,
        &expressions,
        facts.assumptions(),
        ExecutionContext::apply_verified_rules(environment),
        &mut budget,
    )
    .map_err(|limit| Refused(format!("applying tactic `{name}` stopped at {limit}")))?;
    let [path] = paths.as_slice() else {
        return Err(Refused(format!(
            "applying tactic `{name}` produced {} outcomes; an application has exactly one",
            paths.len()
        )));
    };
    let after = match &path.outcome {
        FunctionOutcome::Return { state, .. } => state.clone(),
        FunctionOutcome::RuntimeError(error) => {
            return Err(Refused(format!(
                "tactic `{name}` could not be applied: {error}"
            )));
        }
        FunctionOutcome::UndefinedBehavior(behavior) => {
            return Err(Refused(format!(
                "tactic `{name}` could not be applied: undefined behavior: {}",
                behavior.description()
            )));
        }
        FunctionOutcome::Throw { .. } | FunctionOutcome::VerificationDiverges => {
            return Err(Refused(format!("tactic `{name}` has no ordinary outcome")));
        }
    };
    for obligation in &path.obligations {
        if !facts.contains(&obligation.proposition) {
            return Err(TacticApplicationRefusal::MissingRequirement(
                obligation.proposition.clone(),
                obligation.context.clone(),
            ));
        }
    }
    Ok(TacticRuleTransition {
        state: *after,
        facts: path.facts.clone(),
        next_kernel_variable: budget.next_kernel_variable(),
    })
}

fn execute_verified_function_rule(
    caller_state: &ExecutionState,
    rule: &VerifiedFunctionRule,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<FunctionPath>> {
    // A call step's binder map names exactly this call.
    // The map is the whole binding: every instance binder the callee declares
    // is looked up once, and nothing else is consulted.
    let binder_application = match selected_call_binder_application(
        rule.function.name(),
        rule.function.contract_interface(),
        caller_state,
        environment,
        Some(&mut *budget),
    ) {
        Ok(application) => application,
        Err(message) => return Ok(vec![resource_call_failure(message)]),
    };
    execute_verified_function_applications(
        caller_state,
        &[FunctionContractApplication {
            pointer_result: rule.pointer_result.as_deref(),
            name: rule.function.name(),
            interface_name: rule.function.name(),
            interface: rule.function.contract_interface(),
            storage: Some(&rule.function),
            evidence: Some(&rule.function),
            framed_rule: Some(FramedCallRule::Verified { _rule: rule }),
            representation_copy: None,
            value_arguments: &[],
        }],
        None,
        binder_application
            .as_ref()
            .map(|application| (0, application)),
        arguments,
        assumptions,
        environment,
        budget,
    )
}

/// Prepare one worker summary with its ownership still withheld. Only the
/// internal thread transition calls this; pthread declarations are not wired.
pub(super) fn suspend_verified_worker(
    caller_state: &ExecutionState,
    rule: &VerifiedFunctionRule,
    argument: ProgramValue,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(super::threads::WorkerCompletion, Vec<ProofObligation>), String>> {
    if !rule
        .function
        .contract_interface()
        .exceptional_signature()
        .is_empty()
    {
        return Ok(Err(
            "exceptional workers are outside the scoped thread profile".to_string(),
        ));
    }
    let mut completions = Vec::new();
    let paths = execute_verified_function_applications_with_suspension(
        caller_state,
        &[FunctionContractApplication {
            pointer_result: rule.pointer_result.as_deref(),
            name: rule.function.name(),
            interface_name: rule.function.name(),
            interface: rule.function.contract_interface(),
            storage: Some(&rule.function),
            evidence: Some(&rule.function),
            framed_rule: Some(FramedCallRule::Verified { _rule: rule }),
            representation_copy: None,
            value_arguments: &[],
        }],
        None,
        None,
        &[ProgramExpression::Value(argument)],
        assumptions,
        environment,
        budget,
        Some(&mut completions),
    )?;
    if let Some(FunctionPath {
        outcome: FunctionOutcome::RuntimeError(error),
        ..
    }) = paths.first()
    {
        return Ok(Err(super::api::describe_certification_runtime_error(error)));
    }
    Ok(unique_worker_completion(paths.is_empty(), completions))
}

pub(super) fn unique_worker_completion(
    no_failure_paths: bool,
    mut completions: Vec<(super::threads::WorkerCompletion, Vec<ProofObligation>)>,
) -> Result<(super::threads::WorkerCompletion, Vec<ProofObligation>), String> {
    if !no_failure_paths || completions.len() != 1 {
        return Err("worker application must produce exactly one checked completion".to_string());
    }
    Ok(completions.pop().expect("one completion"))
}

/// The binding of a callee's instance binders to the caller's instances for
/// a call to `function`.
///
/// A `step(callee, { binder: instance })` map names it. A binder the
/// map leaves out, or every binder when the step wrote no map, is bound when
/// only one binding is possible: the callee declares one binder of that
/// resource family and arity, and the caller owns exactly one instance of
/// it. Anything else stays unbound and the application engine refuses it,
/// so two candidates are never chosen between. A wrong but unique candidate
/// is not accepted either: the bound instance still has to satisfy the
/// callee's requirement, arguments included, when the contract is applied.
///
/// The transported instances are exactly the function's own `owns`,
/// `consumes`, and `produces` binders. Cost is one indexed bucket lookup
/// per declared binder.
fn selected_call_binder_application(
    function_name: &str,
    interface: &FunctionContractInterface,
    caller_state: &ExecutionState,
    environment: &ExecutionEnvironment,
    produced_names: Option<&mut ExecutionBudget>,
) -> Result<Option<ResourceCallApplication>, &'static str> {
    let written = environment
        .selected_call_binders
        .as_ref()
        .filter(|transport| transport.names_call_to(function_name))
        .map(|transport| transport.bindings.clone());
    // Only the binders required at entry are checked here; a `produces`
    // binder has no instance to check until the call returns.
    let parameters = interface
        .resource_requires()
        .iter()
        .filter(|resource| resource.binding_identity().is_some())
        .cloned()
        .collect::<Vec<_>>();
    let mut inferred = BTreeMap::new();
    for parameter in &parameters {
        crate::instrumentation::record_deterministic_work(1);
        let Some(identity) = parameter.instance_identity() else {
            continue;
        };
        if written
            .as_ref()
            .is_some_and(|bindings| bindings.contains_key(&identity))
        {
            continue;
        }
        let Some(shape) = instance_binder_shape(parameter) else {
            continue;
        };
        if parameters
            .iter()
            .filter(|other| instance_binder_shape(other) == Some(shape))
            .count()
            != 1
        {
            continue;
        }
        let [only] = caller_state
            .resources()
            .owned_instances_of_shape(shape.0, shape.1)[..]
        else {
            continue;
        };
        inferred.insert(identity, only.identity());
    }
    // An instance the call only produces, which the proof does not name,
    // is the caller's under a fresh identity: it binds nothing the caller
    // holds, and a later call finds it as the only instance of its family.
    if let Some(budget) = produced_names {
        let required = parameters
            .iter()
            .filter_map(ResourceSpec::binding_identity)
            .collect::<BTreeSet<_>>();
        for produced in interface.resource_ensures() {
            crate::instrumentation::record_deterministic_work(1);
            let Some(identity) = produced.instance_identity() else {
                continue;
            };
            if required.contains(&identity)
                || inferred.contains_key(&identity)
                || written
                    .as_ref()
                    .is_some_and(|bindings| bindings.contains_key(&identity))
            {
                continue;
            }
            let fresh = budget
                .allocate_kernel_variable()
                .map_err(|_| "a produced instance could not be named")?;
            inferred.insert(identity, fresh);
        }
    }
    let bindings = match (written, inferred.is_empty()) {
        (None, true) => return Ok(None),
        (Some(written), true) => written,
        (written, false) => {
            for (binder, instance) in written.iter().flat_map(|written| written.iter()) {
                inferred.insert(*binder, *instance);
            }
            std::sync::Arc::new(inferred)
        }
    };
    ResourceCallApplication::bind(parameters, bindings, caller_state).map(Some)
}

/// A function exit at which a `produces` binder is held under no name takes
/// the one owned instance of the binder's family that no name holds, as a
/// call binds a binder its map leaves out: the instance is renamed to the
/// binder's identity. So does an `owns` binder whose entry instance a call
/// consumed, `owns state: boxed(slot.item)` lent to a callee that returns
/// the resource as a new instance. An instance no name holds is one a call produced
/// under an identity the kernel chose, from the execution range; a binder
/// or a proof's name, `let { left: l } = unfold(t)`, holds its instance
/// under the surface's identity, which the exit never takes. Nothing is
/// matched by name or position, and two candidates are never chosen
/// between. The binder's arguments are
/// checked where its clause is, so a rename at other arguments fails there.
pub(crate) fn exit_with_unheld_produced_binders_adopted(
    function: &ProgramFunction,
    outcome: FunctionOutcome,
    assumptions: &PureFactContext,
) -> FunctionOutcome {
    let FunctionOutcome::Return { value, state } = outcome else {
        return outcome;
    };
    let binders = function
        .resource_requires()
        .iter()
        .chain(function.resource_ensures())
        .filter_map(ResourceSpec::instance_identity)
        .collect::<BTreeSet<_>>();
    let mut state = *state;
    for produced in function.resource_ensures() {
        crate::instrumentation::record_deterministic_work(1);
        let Some(identity) = produced.instance_identity() else {
            continue;
        };
        if state.resources().owned_instance(identity).is_some() {
            continue;
        }
        let Some(shape) = instance_binder_shape(produced) else {
            continue;
        };
        if function
            .resource_ensures()
            .iter()
            .filter(|other| instance_binder_shape(other) == Some(shape))
            .count()
            != 1
        {
            continue;
        }
        let [only] = state
            .resources()
            .owned_instances_of_shape(shape.0, shape.1)
            .into_iter()
            .filter(|instance| {
                !binders.contains(&instance.identity())
                    && instance.identity().0 >= crate::kernel::ExecutionBudget::KERNEL_VARIABLE_BASE
            })
            .collect::<Vec<_>>()[..]
        else {
            continue;
        };
        let Some(adopted) = ResourceInstance::new_with_resource_arguments(
            identity,
            only.name.clone(),
            only.arguments.clone(),
            only.schema.clone(),
            only.fields.clone(),
            only.resource_arguments().to_vec(),
        ) else {
            continue;
        };
        let held = ResourceFact::own(Resource::Instance(only.clone()));
        let Some(resources) = state
            .resources()
            .clone()
            .without_fact_incrementally(&held, assumptions)
        else {
            continue;
        };
        state = state.clone().with_resource_context(
            resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(adopted))),
        );
    }
    FunctionOutcome::Return {
        value,
        state: Box::new(state),
    }
}

/// The resource family and arity an instance binder is declared at.
fn instance_binder_shape(parameter: &ResourceSpec) -> Option<(&str, usize)> {
    let ResourceTerm::Instance { resource, .. } = parameter.term() else {
        return None;
    };
    let ResourceTerm::Composite {
        name, arguments, ..
    } = resource.as_ref()
    else {
        return None;
    };
    Some((name.as_str(), arguments.len()))
}

/// Theorem and contract-premise capabilities for the Hoare frame rule.
/// Scoped hypotheses and established named contracts remain conditional on
/// their premises; neither becomes concrete body-safety evidence.
#[derive(Clone, Copy)]
enum FramedCallRule<'a> {
    Verified {
        _rule: &'a VerifiedFunctionRule,
    },
    ScopedHypothesis {
        _rule: &'a ExternalFunctionRule,
    },
    Named {
        _rule: &'a EstablishedFunctionContract,
    },
}

/// One candidate contract application. The interface is the complete input
/// to callback preparation. Optional concrete storage supplies only the
/// declaration identity needed to lower a direct function's global and
/// static names. Optional concrete evidence is consulted only by verified
/// direct calls for body-specific safety checks and loadable literal facts.
/// Named callbacks carry no concrete storage or body evidence; their
/// established contract premises supply a separate frame-rule capability.
/// External assumptions carry storage but no body proof evidence.
#[derive(Clone, Copy)]
struct FunctionContractApplication<'a> {
    pointer_result: Option<&'a PurePointerResult>,
    /// Concrete callee name used for diagnostics and call attribution.
    name: &'a str,
    /// Nominal interface name used to distinguish candidates and their source
    /// requirement metadata.
    interface_name: &'a str,
    interface: &'a FunctionContractInterface,
    storage: Option<&'a ProgramFunction>,
    evidence: Option<&'a ProgramFunction>,
    /// A theorem or an established contract premise; concrete
    /// declaration storage alone never grants this frame rule.
    framed_rule: Option<FramedCallRule<'a>>,
    /// The checked representation-copy effect of a recognized byte-copy
    /// declaration, if this application is one.
    representation_copy: Option<RepresentationCopyEffect>,
    /// The values a named contract's fact fixed for its value parameters.
    value_arguments: &'a [ProgramValue],
}

fn representation_copy_arguments(
    values: &[ProgramValue],
    effect: RepresentationCopyEffect,
) -> Option<(&Address, &Address, &ProgramValue)> {
    let ProgramValue::Pointer(destination) = values.get(effect.destination_argument)? else {
        return None;
    };
    let ProgramValue::Pointer(source) = values.get(effect.source_argument)? else {
        return None;
    };
    Some((
        destination.address(),
        source.address(),
        values.get(effect.bytes_argument)?,
    ))
}

fn constant_representation_copy_count(bytes: &ProgramValue) -> Option<i64> {
    match bytes {
        ProgramValue::UInt64(bytes) => i64::try_from(bytes.uint64_as_const()?).ok(),
        ProgramValue::Int32(bytes) => Some(i64::from(bytes.as_const()? as i32)),
        _ => None,
    }
}

/// Either the source is initialized, so an ordinary call transition can
/// keep old destination initialization, or the transition replaces it using
/// the exact copied span. Unknown placement cannot establish either rule.
fn representation_copy_initialization(
    memory: &SymbolicMemory,
    values: &[ProgramValue],
    effect: RepresentationCopyEffect,
    inputs: &[CheckedResourceFact],
    assumptions: &PureFactContext,
) -> Result<Option<RepresentationCopyRange>, &'static str> {
    let refusal = "memcpy with a possibly uninitialized source requires exact offsets and length and an automatic or heap destination";
    let (destination, source, count) =
        representation_copy_arguments(values, effect).ok_or(refusal)?;
    let bytes = constant_representation_copy_count(count);
    if bytes == Some(0) {
        return Ok(None);
    }
    // The recognized library declaration has exactly one source view. Use
    // its checked range (including the index kind selected when lending it).
    let source_view = inputs
        .iter()
        .filter(|input| input.fact.is_view())
        .find_map(|input| input.fact.memory_range())
        .ok_or(refusal)?;
    if call_initialization::representation_copy_source_is_initialized(
        memory,
        source_view,
        assumptions,
    ) {
        return Ok(None);
    }
    if !destination.base.is_local_block() && !matches!(destination.base, AddressBase::Heap(_)) {
        return Err(refusal);
    }
    let bytes = bytes
        .and_then(|bytes| u32::try_from(bytes).ok())
        .ok_or(refusal)?;
    for address in [source, destination] {
        address
            .offset
            .as_const()
            .and_then(|start| start.checked_add(i64::from(bytes)))
            .ok_or(refusal)?;
    }
    Ok(Some(RepresentationCopyRange {
        destination: destination.clone(),
        source: source.clone(),
        bytes,
    }))
}

/// Transfers initialized typed cells across a recognized byte-copy call.
///
/// Only a cell whose complete byte representation lies inside the copied
/// source range moves, and only when both endpoints are constant so the offset
/// mapping and the alignment test are exact. A cell the copy would split, a
/// symbolic range, or a misaligned destination is left alone: the destination
/// keeps its post-havoc state, so the transfer can only add observations the
/// copy's `click::bytes::equal` guarantee already justified. An untyped source has no
/// cells, so a raw byte copy still establishes nothing typed.
pub(in crate::kernel) fn transfer_representation_copy_cells(
    entry_memory: &SymbolicMemory,
    argument_values: &[ProgramValue],
    memory: SymbolicMemory,
    effect: RepresentationCopyEffect,
) -> SymbolicMemory {
    representation_copy_cell_moves(entry_memory, argument_values, effect)
        .into_iter()
        .fold(memory, |memory, (pointer, value)| {
            memory.store(pointer, value)
        })
}

/// The destination cells a recognized byte copy plants, in source order.
///
/// The source cells are found with one bounded range query, so this work is
/// the copied span's cell count plus one, independent of every other cell
/// in memory.
pub(in crate::kernel) fn representation_copy_cell_moves(
    entry_memory: &SymbolicMemory,
    argument_values: &[ProgramValue],
    effect: RepresentationCopyEffect,
) -> Vec<(Address, ProgramValue)> {
    let Some((destination, source, bytes)) = representation_copy_arguments(argument_values, effect)
    else {
        return Vec::new();
    };
    let bytes = constant_representation_copy_count(bytes);
    let (Some(source_offset), Some(destination_offset), Some(bytes)) = (
        source.offset.as_const(),
        destination.offset.as_const(),
        bytes,
    ) else {
        return Vec::new();
    };
    if bytes <= 0 {
        return Vec::new();
    }
    let source_block = source.base.clone();
    let destination_block = destination.base.clone();
    // A checked byte copy requires disjoint ranges, including within one block.
    let Some(destination_end) = destination_offset.checked_add(bytes) else {
        return Vec::new();
    };
    if source_block == destination_block
        && source_offset < destination_end
        && destination_offset < source_offset.saturating_add(bytes)
    {
        return Vec::new();
    }
    // Constant offsets order before every other offset form and among
    // themselves by value, and a copied cell of positive width starts in
    // `source_offset .. source_offset + bytes`. This range is therefore
    // exactly the candidate cells. A cell at `i64::MAX` cannot fit its
    // positive width, so saturating the end loses no candidate.
    let start = Address {
        base: source_block.clone(),
        offset: AddressOffset::Constant(source_offset),
    };
    let end = Address {
        base: source_block,
        offset: AddressOffset::Constant(source_offset.saturating_add(bytes)),
    };
    crate::instrumentation::record_deterministic_work(1);
    let mut moves = Vec::new();
    for (cell, value) in entry_memory.cells.range(start..end) {
        crate::instrumentation::record_deterministic_work(1);
        let Some(cell_offset) = cell.offset.as_const() else {
            continue;
        };
        let width = i64::from(value.byte_width());
        if width == 0 {
            continue;
        }
        let relative = cell_offset - source_offset;
        if relative < 0 || relative + width > bytes {
            continue;
        }
        let destination_cell_offset = destination_offset + relative;
        // The copied bytes preserve the source value, but a typed observation
        // at a misaligned destination is not a defined load.
        if destination_cell_offset % width != 0 {
            continue;
        }
        moves.push((
            Address {
                base: destination_block.clone(),
                offset: AddressOffset::Constant(destination_cell_offset),
            },
            value.clone(),
        ));
    }
    moves
}

fn execute_verified_function_applications(
    caller_state: &ExecutionState,
    applications: &[FunctionContractApplication<'_>],
    selected_contract: Option<usize>,
    resource_application: Option<(usize, &ResourceCallApplication)>,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<FunctionPath>> {
    // Exact contract certification may encounter a conditional produced
    // effect inside a caller's body. If the guard is not established at the
    // call boundary, split the verified contract application before applying
    // its resource transition. This reruns only the body-independent call
    // rule; neither the caller nor callee C body is executed again.
    if environment.allows_conditional_resource_cases() {
        let cases = applications.iter().find_map(|application| {
            application
                .evidence
                .or(application.storage)
                .and_then(|function| {
                    crate::kernel::api::contract_certification::contract_resource_condition_cases(
                        caller_state,
                        function,
                        arguments,
                        assumptions,
                    )
                })
        });
        if let Some(cases) = cases.filter(|cases| cases.len() > 1) {
            let mut split_paths = Vec::new();
            for case in cases {
                let case_assumptions = assumptions_with_propositions(assumptions, &case);
                let case_paths = execute_verified_function_applications_with_suspension(
                    caller_state,
                    applications,
                    selected_contract,
                    resource_application,
                    arguments,
                    &case_assumptions,
                    environment,
                    budget,
                    None,
                )?;
                for mut path in case_paths {
                    if is_deferred_conditional_resource_effect_outcome(&path.outcome) {
                        continue;
                    }
                    path.facts
                        .extend(case.iter().cloned().map(ExecutionPureFact::new));
                    split_paths.push(path);
                }
            }
            if !split_paths.is_empty() {
                budget.check_path_width(split_paths.len())?;
                return Ok(split_paths);
            }
        }
    }

    let paths = execute_verified_function_applications_with_suspension(
        caller_state,
        applications,
        selected_contract,
        resource_application,
        arguments,
        assumptions,
        environment,
        budget,
        None,
    )?;
    Ok(paths)
}

fn is_deferred_conditional_resource_effect_outcome(outcome: &FunctionOutcome) -> bool {
    matches!(
        outcome,
        FunctionOutcome::RuntimeError(error)
            if is_deferred_conditional_resource_effect_error(error)
    )
}

fn execute_verified_function_applications_with_suspension(
    caller_state: &ExecutionState,
    applications: &[FunctionContractApplication<'_>],
    selected_contract: Option<usize>,
    resource_application: Option<(usize, &ResourceCallApplication)>,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
    mut suspended: Option<&mut Vec<(super::threads::WorkerCompletion, Vec<ProofObligation>)>>,
) -> ExecutionResult<Vec<FunctionPath>> {
    if applications.is_empty() {
        return Ok(vec![FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                "call requires at least one contract application".to_string(),
            )),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    let application = applications[0];
    // A throwing interface is applied alone, whether it is a direct callee's
    // own or a named contract a call through a pointer is made under.
    if applications
        .iter()
        .any(|application| !application.interface.exceptional_signature().is_empty())
        && (applications.len() != 1
            || selected_contract.is_some()
            || resource_application.is_some()
            || !application.interface.verified_direct_contract_supported()
            || application
                .evidence
                .or(application.storage)
                .is_some_and(|function| {
                    !function.verified_direct_contract_supported()
                        || function.contract_interface() != application.interface
                }))
    {
        return Ok(vec![FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::UnsupportedOpaqueFunctionContract(
                application.name.to_string(),
            )),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    // Every named instance the callee declares must be bound by the selected
    // application. The check is one map lookup per declared binder, so an
    // unbound binder is refused here rather than transported silently.
    if let Some((unbound_function, unbound_binder)) =
        applications
            .iter()
            .enumerate()
            .find_map(|(index, application)| {
                let bindings = resource_application
                    .filter(|(selected, _)| *selected == index)
                    .map(|(_, application)| &application.bindings);
                application
                    .interface
                    .resource_requires()
                    .iter()
                    .chain(application.interface.resource_ensures())
                    .find(|resource| {
                        // A pthread callback's mutex-use binder names its
                        // own checked input share. There is no source-level
                        // call map at the runtime callback boundary; the
                        // worker planner selects and authenticates the
                        // concrete typed authority before granting it.
                        if suspended.is_some()
                            && resource.role() == ResourceTransferRole::Borrow
                            && resource.access() == ResourceAccessMode::Own
                            && matches!(
                                resource.term(),
                                ResourceTerm::MutexUse {
                                    protected: Some(_),
                                    ..
                                }
                            )
                        {
                            return false;
                        }
                        resource.binding_identity().is_some_and(|identity| {
                            !bindings.is_some_and(|bindings| bindings.contains_key(&identity))
                        })
                    })
                    .map(|resource| {
                        (
                            application.name.to_string(),
                            resource.binding_name().unwrap_or("<unnamed>").to_string(),
                        )
                    })
            })
    {
        return Ok(vec![FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                "calls with named resource instances require checked binder transport: `{unbound_function}` has an unbound instance binder `{unbound_binder}`; bind it in `step(..., {{ {unbound_binder}: instance }})`"
            ))),
            vec![].into(),
            vec![],
        )]);
    }
    budget.consume_function_call()?;
    let existing_variables = crate::instrumentation::measure_operation(
        application.name,
        "verified function rule application",
        "verified call variable collection",
        || {
            let mut existing_variables = BTreeSet::new();
            collect_execution_state_bitvector_variables(caller_state, &mut existing_variables);
            for application in applications {
                collect_program_function_contract_interface_bitvector_variables(
                    application.interface,
                    &mut existing_variables,
                );
            }
            for argument in arguments {
                collect_program_expression_bitvector_variables(argument, &mut existing_variables);
            }
            existing_variables
        },
    );
    // The facts' variables are reserved by their ceiling rather than
    // collected: collecting walked every fact, and every state a fact
    // names, at every call.
    let mut variables = KernelVariableGenerator::fresh_for_execution(existing_variables)
        .reserving_through(assumptions.execution_variable_ceiling());
    let memory_identity = variables.next_in(budget)?;
    let result_identity = variables.next_in(budget)?;
    let exceptional_payload_identity =
        match !application.interface.exceptional_signature().is_empty() {
            true => Some(variables.next_in(budget)?),
            false => None,
        };
    let mut paths = Vec::new();
    'arguments: for arguments_path in evaluate_retained_program_arguments_paths(
        caller_state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(FunctionPath::new(
                outcome,
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }

        let mut applicable = Vec::new();
        let mut first_failure = None;
        let mut selected_position = None;
        for (index, application) in applications.iter().enumerate() {
            // The written selector fixes the transition before its premises
            // are proved. Other interfaces must establish applicability at
            // entry; they cannot borrow the selected call's pending premises.
            let retain_selected =
                assumptions.retains_required_obligations() && selected_contract == Some(index);
            let prepared = prepare_verified_function_call(
                caller_state,
                *application,
                index,
                arguments,
                arguments_path.clone(),
                (applications.len() > 1 || selected_contract.is_some()) && !retain_selected,
                assumptions,
                environment,
                budget,
                resource_application
                    .filter(|(selected, _)| *selected == index)
                    .map(|(_, application)| application),
                suspended.is_some(),
            )?;
            match prepared {
                Ok(prepared) => {
                    if selected_contract == Some(index) {
                        selected_position = Some(applicable.len());
                    }
                    applicable.push(prepared);
                }
                Err(failure) => {
                    if selected_contract == Some(index) {
                        paths.push(failure);
                        continue 'arguments;
                    }
                    if first_failure.is_none() {
                        first_failure = Some(failure);
                    }
                }
            }
        }
        if applicable.is_empty() {
            paths.push(first_failure.expect("a nonempty set of callback contracts"));
            continue;
        }
        // Pure conjunction does not duplicate an ownership ledger. An explicit
        // selector chooses one resource transition; absent that choice, do not
        // represent alternative ownership as paths or separating ownership.
        if selected_contract.is_none()
            && applicable.len() > 1
            && applicable.iter().any(|call| {
                !call.interface.resource_requires().is_empty()
                    || !call.interface.resource_ensures().is_empty()
                    || !call.interface.resource_constructors().is_empty()
                    || !call.transfer.memory_effects.is_empty()
            })
        {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                    "ambiguous callback resource transition; use step(Contract) to select one"
                        .to_string(),
                )),
                arguments_path.facts,
                arguments_path.obligations,
            ));
            continue;
        }
        // Supplementary guarantees are interpreted on the shared post-memory,
        // not an alternative output ledger. In particular, resource counts must
        // not accidentally be evaluated against that interface's input ledger.
        let independent_guarantees_only = selected_contract.is_some()
            && applicable.iter().any(|call| {
                !call.interface.resource_requires().is_empty()
                    || !call.interface.resource_ensures().is_empty()
            });
        let primary = applicable.remove(selected_position.unwrap_or(0));
        let PreparedVerifiedFunctionCall {
            name,
            interface_name,
            candidate_ordinal,
            has_exact_write_ranges,
            storage,
            evidence,
            framed_rule,
            interface,
            argument_values,
            entry_state,
            entry_contract_state,
            mut transfer,
            mut facts,
            mut obligations,
            effective_assumptions,
            bindings: selected_bindings,
        } = primary;
        let additional_calls = applicable.into_iter();
        // The planner has checked these effects against the views this call
        // lends; the caller's other active loans (its own contract inputs,
        // an enclosing call's loans) are checked here, so a summary can
        // never havoc memory that is lent elsewhere.
        let call_site = || {
            CallRequirementSite::for_requirement(
                name,
                interface_name,
                candidate_ordinal,
                arguments,
                caller_state.memory(),
            )
        };
        let write_requirements = if suspended.is_some() || !has_exact_write_ranges {
            // Worker admission has its own effect rules. Folded or guarded
            // projections can widen an effect to a span containing bytes
            // the callee cannot write.
            if let Some(diagnostic) = entry_state.loan_ledger().and_then(|ledger| {
                transfer.memory_effects.iter().find_map(|range| {
                    ledger.memory_access_refusal(
                        range,
                        &effective_assumptions,
                        LoanRefusalOperation::MemoryAccess,
                    )
                })
            }) {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(Box::new(diagnostic))),
                    facts,
                    obligations,
                ));
                continue;
            }
            Vec::new()
        } else {
            verified_call_loan_requirements(
                caller_state.loan_ledger(),
                &transfer.memory_effects,
                call_site,
                interface.contract_requires().len(),
                "verified call write separation",
            )
        };
        // A checked mutex-use call may execute runtime lock/unlock operations.
        // Their representation writes are authorized by the selected use
        // transfer, not by the contract's ordinary mutable footprint. Keep
        // this effect separate from `transfer.memory_effects`, whose ranges
        // must pass the ordinary mutex-storage write reservation.
        let mut mutex_storage_effects = transfer
            .stable_view_plan
            .as_ref()
            .into_iter()
            .flat_map(|plan| &plan.mutex_uses)
            .map(|use_plan| {
                let mutex = match use_plan.source_resource().resource() {
                    Resource::MutexUse(identity) => &identity.mutex,
                    Resource::MutexLive(identity) => &identity.mutex,
                    _ => unreachable!("checked use call source"),
                };
                MemoryRange::new_with_element_width(
                    mutex.clone(),
                    0u32.into(),
                    crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin()
                        .mutex_storage_bytes
                        .into(),
                    1,
                )
            })
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        if let Some(helper) = &transfer.helper_call {
            let Resource::MutexUse(usage) = helper.required.resource() else {
                unreachable!()
            };
            let range = MemoryRange::new_with_element_width(
                usage.mutex.clone(),
                0u32.into(),
                crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin()
                    .mutex_storage_bytes
                    .into(),
                1,
            );
            if !mutex_storage_effects.contains(&range) {
                mutex_storage_effects.push(range);
            }
        }
        if let Some(diagnostic) = mutex_storage_effects.iter().find_map(|range| {
            transfer
                .stable_view_plan
                .as_ref()
                .and_then(|plan| {
                    plan.ledger.memory_access_refusal(
                        range,
                        &effective_assumptions,
                        LoanRefusalOperation::MemoryAccess,
                    )
                })
                .or_else(|| {
                    entry_state.stable_loan_memory_access_refusal(
                        range,
                        &effective_assumptions,
                        LoanRefusalOperation::MemoryAccess,
                    )
                })
        }) {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(Box::new(diagnostic))),
                facts,
                obligations,
            ));
            continue;
        }
        let copy_initialization = if let Some(effect) = application.representation_copy
            && !transfer.memory_effects.is_empty()
        {
            match representation_copy_initialization(
                &entry_state.memory,
                &argument_values,
                effect,
                &transfer.borrowed_inputs,
                &effective_assumptions,
            ) {
                Ok(copy) => copy,
                Err(message) => {
                    paths.push(FunctionPath::new(
                        FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                            message.into(),
                        )),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            }
        } else {
            None
        };
        let memory = if transfer.memory_effects.is_empty() {
            entry_state.memory.clone()
        } else {
            // The caller keeps its residual resources outside the transfer,
            // and the callee writes only memory it owns, so the havoc keeps
            // every cell an owned residual member holds.
            // Stable views escrow their owned backing outside the residual.
            // The checked loan plan protects that backing from the callee's
            // writes just as it protects the remaining caller-owned frame.
            let caller_frame = transfer
                .caller_resources_after_requirements
                .clone()
                .unchecked_with_facts(escrowed_owners(&transfer).iter().cloned());
            let kept = call_kept_ownership(
                &caller_frame,
                interface.composite_resource_definitions(),
                &entry_state,
                &effective_assumptions,
            )
            .with_caller_before_transfer(caller_state.resources());
            entry_state.memory.clone().with_call_memory_havoc_with_copy(
                memory_identity,
                &transfer.memory_effects,
                &effective_assumptions,
                Some(&kept),
                copy_initialization.as_ref(),
            )
        };
        let mut exceptional_path = if let Some(payload_identity) = exceptional_payload_identity {
            Some(exceptional_direct_function_path(
                caller_state,
                interface,
                evidence.or(storage),
                framed_rule,
                &argument_values,
                &entry_state,
                &entry_contract_state,
                &transfer,
                memory.clone(),
                facts.clone(),
                obligations.clone(),
                &effective_assumptions,
                payload_identity,
                budget,
            )?)
        } else {
            None
        };
        // A recognized byte-copy declaration transfers initialized typed
        // cells across the copy. It runs after the external contract's havoc,
        // so the copies' `click::bytes::equal` guarantee is what makes the transferred
        // values the checked ones, and it is the only thing that turns the
        // destination's freshly owned bytes into typed observations.
        let memory = if let Some(effect) = application.representation_copy {
            transfer_representation_copy_cells(
                &entry_state.memory,
                &argument_values,
                memory,
                effect,
            )
        } else {
            memory
        };
        let memory = if mutex_storage_effects.is_empty() {
            memory
        } else {
            let identity = if transfer.memory_effects.is_empty() {
                memory_identity
            } else {
                variables.next_in(budget)?
            };
            memory.with_storage_memory_havoc(
                identity,
                &mutex_storage_effects,
                &effective_assumptions,
            )
        };
        let mut worker_effects = transfer.memory_effects.clone();
        worker_effects.extend(mutex_storage_effects.iter().cloned());
        let result = if interface.aggregate_return_mode() == AggregateReturnMode::Construction {
            let Some(result) = construction_return::summary_result(&entry_state, interface) else {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                        "construction summary requires its checked destination".into(),
                    )),
                    facts,
                    obligations,
                ));
                continue;
            };
            result
        } else {
            // Only a modular call assumes the declared output guarantee.
            // The function's own proof still checks its actual returned value.
            let result = symbolic_contract_result(interface, result_identity)
                .with_pointer_object_class(interface.return_object_type_guarantee.clone());
            let arguments = argument_values
                .iter()
                .cloned()
                .map(PureFunctionArgument::Value)
                .collect::<Vec<_>>();
            let (all_null, evidence) =
                super::spec::pure_pointer_result_class(application.pointer_result, &arguments);
            if let ProgramValue::Pointer(mut pointer) = result {
                if all_null {
                    pointer.replace_pointer(Address::null());
                }
                ProgramValue::Pointer(pointer.with_object_type_evidence(evidence))
            } else {
                result
            }
        };
        let mut post_state = entry_state.clone().with_memory(memory);
        if interface.aggregate_return_mode() == AggregateReturnMode::Construction
            || interface.construction_parameter().is_some()
        {
            construction_return::initialize_summary(&mut post_state, &entry_contract_state);
        }
        // Construction initialization is part of this checked call effect,
        // so its endpoint must include the initialized value fields.
        if !worker_effects.is_empty() {
            let mut effect = ExecutionPureFact::internal(Proposition::MemoryEffectSummary {
                before: entry_state.memory.clone(),
                after: post_state.memory.clone(),
                mutable_ranges: worker_effects.clone(),
            })
            .into_certified();
            if mutex_storage_effects.is_empty()
                && interface.aggregate_return_mode() != AggregateReturnMode::Construction
                && interface.construction_parameter().is_none()
            {
                effect.resource_effect_bound = transfer.resource_effect_bound.clone().map(Arc::new);
            }
            facts.push(effect);
        }
        // Protocol effects remain in the caller scope. The ordinary summary
        // partition below is recovered before this checked successor is
        // published, so no call-local hold can escape or be discarded.
        let helper_effect = if let Some(helper) = &transfer.helper_call {
            let payload = helper
                .contract
                .payload
                .as_ref()
                .and_then(|spec| spec.instance_identity())
                .and_then(|formal| {
                    selected_bindings
                        .as_ref()
                        .and_then(|bindings| bindings.get(&formal).copied())
                });
            let definition = match helper.required.resource() {
                Resource::MutexUse(usage) => usage.protected.as_ref().and_then(|description| {
                    environment
                        .modeled_mutex_definitions
                        .get(description.family())
                }),
                _ => unreachable!("checked helper use"),
            };
            let protocol_input = caller_state.clone().with_memory(post_state.memory.clone());
            match super::mutexes::helper_contracts::apply_call_effect(
                &protocol_input,
                &helper.source,
                &helper.required,
                helper.contract.effect,
                helper.guard.as_ref(),
                payload,
                definition,
                &environment.modeled_mutex_definition_list,
                &effective_assumptions,
                budget,
            ) {
                Ok((successor, evidence, ranges)) => {
                    if !ranges.is_empty() {
                        worker_effects.extend(ranges.iter().cloned());
                        facts.push(
                            ExecutionPureFact::internal(Proposition::MemoryEffectSummary {
                                before: post_state.memory.clone(),
                                after: successor.memory.clone(),
                                mutable_ranges: ranges,
                            })
                            .into_certified(),
                        );
                    }
                    post_state.set_memory_directly(successor.memory.clone());
                    post_state.mutex_ledger = successor.mutex_ledger.clone();
                    post_state.opaque_mutex_acquisitions =
                        successor.opaque_mutex_acquisitions.clone();
                    Some((successor, evidence))
                }
                Err(error) => {
                    let Resource::MutexUse(usage) = helper.required.resource() else {
                        unreachable!()
                    };
                    paths.push(FunctionPath::new(
                        FunctionOutcome::RuntimeError(error.into_runtime_error(&usage.mutex)),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            }
        } else {
            None
        };
        // A typed use permits the callee to modify the protected state. A
        // summary must forget the concrete escrow's previous observations.
        if let Some(plan) = &transfer.stable_view_plan {
            let mut failure = None;
            for use_plan in &plan.mutex_uses {
                let required = use_plan.required_resource();
                let Resource::MutexUse(usage) = required.resource() else {
                    unreachable!()
                };
                let Some(protected) = &usage.protected else {
                    continue;
                };
                let Some(definition) = environment
                    .modeled_mutex_definitions
                    .get(protected.family())
                else {
                    failure = Some(RuntimeError::FunctionContract(
                        "typed mutex call requires a guarded resource definition".into(),
                    ));
                    break;
                };
                let before = post_state.memory.clone();
                match super::mutexes::MutexLedger::havoc_protected_for_call(
                    &post_state,
                    &usage.mutex,
                    definition,
                    &environment.modeled_mutex_definition_list,
                    &effective_assumptions,
                    budget,
                ) {
                    Ok((fresh, ranges)) => {
                        if !ranges.is_empty() {
                            worker_effects.extend(ranges.iter().cloned());
                            facts.push(
                                ExecutionPureFact::internal(Proposition::MemoryEffectSummary {
                                    before,
                                    after: fresh.memory.clone(),
                                    mutable_ranges: ranges,
                                })
                                .into_certified(),
                            );
                        }
                        post_state = fresh;
                    }
                    Err(error) => {
                        failure = Some(error.into_runtime_error(&usage.mutex));
                        break;
                    }
                }
            }
            if let Some(error) = failure {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
        }
        if interface.return_type() != ProgramType::Void {
            set_contract_result(&mut post_state, interface, result.clone());
        }
        // A `produces` binder owns nothing at entry: the call creates the
        // instance under the identity the caller's `let` introduced. It is
        // built once, here, so the population transition and the returned
        // resources agree on its fresh fields.
        let mut produced_instances = BTreeMap::new();
        // Current arguments of a produced instance are read at return, where
        // the contract's input instances still address cells their decided
        // arms or unmatched bodies owned (`produces after: state(region->arena)`
        // beside a consumed region). These views come only from the contract's inputs
        // and are computed once. Entry arguments use entry_contract_state.
        let mut produced_argument_state: Option<ExecutionState> = None;
        let mut prepared_outputs = Vec::new();
        for resource in interface.resource_ensures() {
            let Some(identity) = resource.instance_identity() else {
                continue;
            };
            let Some(schema) = resource.instance_schema() else {
                continue;
            };
            // A produced binder is fresh at the callee boundary even when
            // its caller-facing name reuses a consumed input's identity.
            // Looking it up through the entry binding map would find that
            // input and incorrectly retain its old resource arguments.
            if resource.role() == ResourceTransferRole::Borrow {
                continue;
            }
            let Some(produced) = selected_bindings
                .as_ref()
                .and_then(|bindings| bindings.get(&identity).copied())
            else {
                continue;
            };
            if transfer
                .helper_call
                .as_ref()
                .and_then(|helper| helper.contract.payload.as_ref())
                .and_then(ResourceSpec::instance_identity)
                == Some(identity)
                && let Some((successor, _)) = &helper_effect
            {
                let Some(instance) = successor.owned_resource_instance(produced) else {
                    return Ok(vec![resource_call_failure(
                        "mutex helper did not produce its protected state",
                    )]);
                };
                produced_instances.insert(identity, instance.clone());
                continue;
            }
            let Some(instance_resource) = resource.instance_resource_spec() else {
                continue;
            };
            // This temporary clause evaluates C argument shape only. The
            // original spec's reference arguments are captured separately.
            let instance_resource = instance_resource.with_resource_arguments(Vec::new());
            if produced_argument_state.is_none() {
                // Use the same decided-arm read authority as ordinary return
                // clauses, visiting only this call's inputs, never its frame.
                let mut views = instance_arm_views(
                    &transfer.callee_resources,
                    interface.composite_resource_definitions(),
                    &post_state,
                    &effective_assumptions,
                );
                views.extend(transfer.callee_resources.facts().iter().flat_map(|fact| {
                    unmatched_instance_body_views(
                        fact,
                        interface.composite_resource_definitions(),
                        &post_state,
                        &effective_assumptions,
                    )
                }));
                let mut argument_state = post_state.clone().with_resource_context(
                    post_state.resources().clone().unchecked_with_facts(views),
                );
                // A primitive output can make a named output's argument
                // readable. Construct those facts once, before minting named
                // outputs, and hand them to the return transition unchanged.
                prepared_outputs = prepare_produced_argument_supply(
                    &entry_contract_state,
                    &mut argument_state,
                    interface,
                    &effective_assumptions,
                    budget,
                )?;
                produced_argument_state = Some(argument_state);
            }
            let argument_state = produced_argument_state.as_ref().expect("initialized above");
            // Each argument keeps its declared state. In particular, an
            // `old(...)` argument uses entry read authority, not the fresh
            // post-call memory used for current arguments.
            let (name, arguments) = match evaluate_function_resource_spec_with_entry(
                &entry_contract_state,
                argument_state,
                &instance_resource,
                &effective_assumptions,
                budget,
            )? {
                Ok(ResourceFact::Own(Resource::Composite { name, arguments }, quantity))
                    if quantity.as_const() == Some(1) =>
                {
                    (name, arguments)
                }
                Ok(_) => {
                    return Ok(vec![resource_call_failure(
                        "a produced resource instance requires an owned resource definition",
                    )]);
                }
                Err(error) => {
                    return Ok(vec![FunctionPath::new(
                        FunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    )]);
                }
            };
            let fields = fresh_resource_instance_fields(
                schema,
                ModelFieldMintSite {
                    identity: produced,
                    minted_by: &ModelMint::Produced {
                        callee: std::sync::Arc::from(application.name),
                    },
                },
                &mut variables,
                budget,
            )?;
            let references =
                match evaluate_resource_reference_arguments(&entry_contract_state, resource) {
                    Ok(references) => references,
                    Err(error) => {
                        return Ok(vec![FunctionPath::new(
                            FunctionOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        )]);
                    }
                };
            produced_instances.insert(
                identity,
                ResourceInstance::new_with_resource_arguments(
                    produced,
                    name,
                    arguments,
                    schema.clone(),
                    fields,
                    references,
                )
                .expect("fresh symbolic fields have their declared types"),
            );
        }
        let callee_resources = if produced_instances.is_empty() {
            transfer.callee_resources.clone()
        } else {
            transfer.callee_resources.clone().unchecked_with_facts(
                produced_instances
                    .values()
                    .map(|instance| ResourceFact::own(Resource::Instance(instance.clone()))),
            )
        };
        let transition_state = post_state.clone().with_resource_context(callee_resources);
        post_state.population_access = transition_state.population_access.clone();
        post_state.observed_population_families = transition_state.observed_population_families;
        let caller_resources_after_requirements =
            transfer.caller_resources_after_requirements.clone();
        post_state.resources = caller_resources_after_requirements.clone();
        // Returned ownership keeps its identity, not its old field values.
        // Only the ensures below relate fresh post-fields to the entry state.
        for resource in interface.resource_ensures() {
            let Some(identity) = resource.instance_identity() else {
                continue;
            };
            let after = if let Some(produced) = produced_instances.get(&identity) {
                produced.clone()
            } else {
                let Some(before) = entry_contract_state.owned_resource_instance(identity) else {
                    return Ok(vec![resource_call_failure(
                        "returned resource parameter is not owned at call entry",
                    )]);
                };
                let fields = fresh_resource_instance_fields(
                    before.schema(),
                    ModelFieldMintSite {
                        identity: before.identity,
                        minted_by: &ModelMint::CallReturn {
                            callee: std::sync::Arc::from(application.name),
                        },
                    },
                    &mut variables,
                    budget,
                )?;
                let mut after = before.clone();
                after.fields = fields;
                after
            };
            if resource.role() == ResourceTransferRole::Produce
                && let Some(events) = &post_state.population_effects.creation
            {
                let description = ResourceDescription::from_instance(&after);
                if events.tracks_population(&description) {
                    let scope = events
                        .governing_authority(&description)
                        .expect("tracked named population");
                    let authority = ResourceFact::own(Resource::PopulationAuthority(scope));
                    if !transfer
                        .callee_resources
                        .satisfies_fact(&authority, &effective_assumptions)
                    {
                        return Ok(vec![FunctionPath::new(
                            FunctionOutcome::RuntimeError(RuntimeError::MissingResource {
                                resource: Box::new(authority),
                            }),
                            facts,
                            obligations,
                        )]);
                    }
                    let next = if events.recognizes_imported_population(&description) {
                        events.checked_imported_instance_exchange(
                            &after,
                            true,
                            &effective_assumptions,
                        )
                    } else {
                        events.checked_instance_exchange(
                            &ResourceReference::from_instance(&after),
                            true,
                        )
                    };
                    match next {
                        Ok(next) => {
                            Arc::make_mut(&mut post_state.population_effects).creation = Some(next)
                        }
                        Err(refusal) => {
                            return Ok(vec![resource_call_failure(&format!(
                                "named helper creation refused: {refusal}"
                            ))]);
                        }
                    }
                }
            }
            post_state.resources = match post_state
                .resources
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [ResourceFact::own(Resource::Instance(after))],
                    &effective_assumptions,
                ) {
                Ok(resources) => resources,
                Err(error) => {
                    return Ok(vec![FunctionPath::new(
                        FunctionOutcome::RuntimeError(resource_context_runtime_error(error)),
                        facts,
                        obligations,
                    )]);
                }
            };
        }
        let output_resource_state =
            with_bound_contract_interface_argument_views(&post_state, interface, &argument_values);
        let entry_resource_state =
            with_bound_contract_interface_argument_views(&entry_state, interface, &argument_values);

        // Coordinate ensures are certified by the callee independently of
        // return admission. Carry them to the ownership producer before it
        // selects finite input pieces. Ledger observations remain later.
        let mut coordinate_facts = ExecutionFacts::new();
        let coordinate_context =
            assumptions_with_path_context(&effective_assumptions, &facts, &obligations);
        // This input view contains the checked clauses, never the ambient
        // caller frame, when the lowerer needs entry-state read authority.
        let coordinate_entry = entry_resource_state
            .clone()
            .with_resource_context(transfer.callee_resources.clone());
        let early_coordinates = !interface.resource_ensures().is_empty();
        if early_coordinates {
            add_verified_function_ensure_facts_selected_with_interface(
                &mut coordinate_facts,
                &obligations,
                &output_resource_state,
                &coordinate_entry,
                interface,
                interface
                    .contract_ensures()
                    .iter()
                    .filter(|ensure| return_coordinate_ensure(ensure)),
                &coordinate_context,
                budget,
            )?;
        }
        let return_assumptions =
            assumptions_with_path_context(&coordinate_context, &coordinate_facts, &[]);

        let return_resource_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call return resource evaluation",
        );
        let ContractReturnResources {
            output_resources,
            return_resources,
            escrow_boundary,
            ensured_views: returned_views,
            produced_borrowing_pieces,
            returned_entry_partition,
        } = match evaluate_contract_return_resources(
            &caller_resources_after_requirements,
            escrowed_owners(&transfer),
            &transfer.canonical_borrowed_owners,
            &transfer.borrowed_inputs,
            &transfer_entry_clauses(&transfer),
            &entry_resource_state,
            &output_resource_state,
            name,
            interface,
            &prepared_outputs,
            ReturnResourceComposition::for_rule(framed_rule, &transfer.consumed_cell_returns),
            &return_assumptions,
            budget,
        )? {
            Ok(resources) => resources,
            Err(error) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
        };
        transfer.returned_entry_partition = returned_entry_partition;
        transfer.candidate_output_views = returned_views;
        transfer.produced_borrowing_pieces = produced_borrowing_pieces;
        if helper_effect.is_some()
            && (!transfer.candidate_output_views.is_empty()
                || !transfer.produced_borrowing_pieces.is_empty())
        {
            paths.push(resource_call_failure("unsupported mutex helper call: escaping views and borrowing resources are not supported"));
            continue;
        }
        drop(return_resource_timing);
        transfer.post_outputs = Some(return_resources);
        let return_resources = transfer
            .post_outputs
            .as_ref()
            .expect("the checked transition records post outputs")
            .clone();

        // Lower the ensures before reconciling allocation ownership so the
        // transition can prove exact continuity when the contract states it.
        // An undecided continuity relation remains symbolic in this one call
        // successor; it is not an execution-path split.
        post_state.resources = return_resources.clone();
        let produced = match produced_memory_initialization(
            &entry_resource_state,
            &output_resource_state,
            interface,
            post_state.memory.clone(),
            &effective_assumptions,
            &mut facts,
            budget,
        )? {
            Ok(memory) => memory,
            Err(error) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
        };
        post_state.set_memory_directly(produced);
        let authority_release_retires = {
            match authority_release_retires_control(
                &entry_contract_state,
                &post_state,
                interface,
                checked_consumed_population_control(interface, &transfer),
                &effective_assumptions,
                budget,
            )? {
                Ok(retires) => retires,
                Err(error) => {
                    paths.push(FunctionPath::new(
                        FunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            }
        };
        if authority_release_retires {
            let Some(member) = checked_consumed_population_member(interface, &transfer).cloned()
            else {
                paths.push(resource_call_failure(
                    "final release lost its checked entry member",
                ));
                continue;
            };
            let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = member
            else {
                paths.push(resource_call_failure(
                    "final release requires one exact member",
                ));
                continue;
            };
            let description = ResourceDescription::new(
                name,
                arguments,
                ResourceFieldSchema::new(vec![]).expect("empty schema"),
            );
            let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
                (description.arguments()).fixed_values::<1>()
            else {
                paths.push(resource_call_failure(
                    "final release needs one pointer anchor",
                ));
                continue;
            };
            let Some(events) = post_state.population_effects.creation.as_ref() else {
                paths.push(resource_call_failure(
                    "final release lost its creation history",
                ));
                continue;
            };
            // Entry field expressions can denote an empty batch even though
            // the resource planner has already omitted its zero member rights.
            let exchange_quantity = if !events.owns_imported_population_member(&description)
                && crate::kernel::quantity_condition_holds(
                    &effective_assumptions,
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(quantity.native_compat().clone()),
                        right: Box::new(MachineTerm::constant(0)),
                    },
                ) {
                MachineTerm::constant(0)
            } else {
                quantity.native_compat().clone()
            };
            let (spent, _) = match events.checked_member_exchange_quantity(
                &pointer.address().base,
                &description,
                false,
                &exchange_quantity,
                &effective_assumptions,
            ) {
                Ok(exchange) => exchange,
                Err(refusal) => {
                    paths.push(resource_call_failure(&format!(
                        "final release member transition refused: {refusal}"
                    )));
                    continue;
                }
            };
            // A consumed control can package additional authority families.
            // Select them from its checked entry body, before the helper's
            // stores change any field-valued arguments or count relations.
            let Some(control) = checked_consumed_population_control(interface, &transfer) else {
                paths.push(resource_call_failure(
                    "final release lost its checked entry control",
                ));
                continue;
            };
            let Resource::Composite {
                name: control_name, ..
            } = control.resource()
            else {
                paths.push(resource_call_failure(
                    "final release requires a control resource",
                ));
                continue;
            };
            let Some(definition) = interface.composite_resource_definition(control_name) else {
                paths.push(resource_call_failure(
                    "final release lost its control definition",
                ));
                continue;
            };
            let (children, _) = match entry_contract_state.checked_authority_wrapper_body(
                control,
                definition,
                &effective_assumptions,
            ) {
                Ok(body) => body,
                Err(error) => {
                    paths.push(resource_call_failure(&error));
                    continue;
                }
            };
            let retirement = if spent.recognizes_imported_population(&description) {
                spent.checked_retire_imported(&description, &effective_assumptions)
            } else {
                spent.checked_retire(&pointer.address().base, &description)
            };
            let (retired, _) = match retirement {
                Ok(exchange) => exchange,
                Err(refusal) => {
                    paths.push(resource_call_failure(&format!(
                        "final release authority retirement refused: {refusal}"
                    )));
                    continue;
                }
            };
            let mut retired = retired;
            for child in children {
                let Resource::PopulationAuthority(additional) = child.resource() else {
                    continue;
                };
                if additional == &description {
                    continue;
                }
                let retirement = if retired.recognizes_imported_population(additional) {
                    retired.checked_retire_imported(additional, &effective_assumptions)
                } else if let Some(crate::kernel::ResourceFieldValue::Program(
                    ProgramValue::Pointer(anchor),
                )) = additional.arguments().first()
                {
                    retired.checked_retire(&anchor.address().base, additional)
                } else {
                    paths.push(resource_call_failure(
                        "final release authority needs a pointer anchor",
                    ));
                    continue 'arguments;
                };
                retired = match retirement {
                    Ok((next, _)) => next,
                    Err(refusal) => {
                        paths.push(resource_call_failure(&format!(
                            "final release authority retirement refused: {refusal}"
                        )));
                        continue 'arguments;
                    }
                };
            }
            Arc::make_mut(&mut post_state.population_effects).creation = Some(retired);
        }
        // Named consumption follows the checked input partition. The ordinary
        // planner removes exact custody; this advances only the population ledger.
        {
            for checked in &transfer.consumed_inputs {
                let Resource::Instance(instance) = checked.fact.resource() else {
                    continue;
                };
                let description = ResourceDescription::from_instance(instance);
                let Some(events) = post_state.population_effects.creation.as_ref() else {
                    continue;
                };
                if !events.tracks_population(&description) {
                    continue;
                }
                let next = if events.recognizes_imported_population(&description) {
                    events.checked_imported_instance_consumption(instance)
                } else {
                    events.checked_instance_exchange(
                        &ResourceReference::from_instance(instance),
                        false,
                    )
                };
                match next {
                    Ok(next) => {
                        Arc::make_mut(&mut post_state.population_effects).creation = Some(next)
                    }
                    Err(refusal) => {
                        paths.push(resource_call_failure(&format!(
                            "named helper consumption refused: {refusal}"
                        )));
                        continue 'arguments;
                    }
                }
            }
        }
        // A suspended locked worker's change is applied at its join instead.
        let defer_locked_exchange =
            suspended.is_some() && authority_mutex_member_helper_contract(interface);
        let mut deferred_exchange = Vec::new();
        // Publish the checked population delta before lowering postcondition counts.
        let member_effects = if authority_release_retires {
            Vec::new()
        } else if authority_mutex_member_helper_contract(interface) {
            locked_helper_member_effects(interface).unwrap_or_default()
        } else if authority_consumes_member_contract(interface)
            || authority_produces_member_contract(interface)
            || authority_exchanges_member_contract(interface)
        {
            authority_checked_member_effects(interface)
        } else {
            Vec::new()
        };
        if !member_effects.is_empty() {
            for (produce, member_spec) in member_effects {
                let mut produced_member = if produce {
                    match evaluate_function_resource_spec_with_entry(
                        &entry_contract_state,
                        &post_state,
                        member_spec,
                        &effective_assumptions,
                        budget,
                    )? {
                        Ok(fact) => Some(fact),
                        Err(error) => {
                            paths.push(FunctionPath::new(
                                FunctionOutcome::RuntimeError(error),
                                facts,
                                obligations,
                            ));
                            continue 'arguments;
                        }
                    }
                } else {
                    None
                };
                if let Some(output) = &mut produced_member
                    && let Some(effects) = authority_quantity_exchange_effects(interface)
                {
                    let input_spec = effects[0].1;
                    let input = interface
                        .resource_requires()
                        .iter()
                        .position(|spec| std::ptr::eq(spec, input_spec))
                        .and_then(|index| {
                            transfer
                                .consumed_inputs
                                .iter()
                                .find(|checked| checked.section_index == Some(index))
                        });
                    let Some(input) = input else {
                        paths.push(resource_call_failure(
                            "quantity exchange has no checked consumed member",
                        ));
                        continue 'arguments;
                    };
                    if !crate::kernel::resources_directly_match(
                        input.fact.resource(),
                        output.resource(),
                        &effective_assumptions,
                    ) {
                        paths.push(resource_call_failure(
                            "quantity exchange must return members of the same population",
                        ));
                        continue 'arguments;
                    }
                    *output = ResourceFact::own_quantity(
                        input.fact.resource().clone(),
                        output.owned_quantity_term().expect("owned output").clone(),
                    );
                }
                let consumed_member = if produce {
                    None
                } else {
                    interface
                        .resource_requires()
                        .iter()
                        .position(|spec| std::ptr::eq(spec, member_spec))
                        .and_then(|index| {
                            transfer
                                .consumed_inputs
                                .iter()
                                .find(|checked| checked.section_index == Some(index))
                        })
                        .map(|checked| checked.fact.clone())
                };
                let Some(ResourceFact::Own(Resource::Composite { name, arguments }, quantity)) =
                    produced_member.as_ref().or(consumed_member.as_ref())
                else {
                    paths.push(resource_call_failure(
                        "population helper has no checked member transfer",
                    ));
                    continue 'arguments;
                };
                let description = ResourceDescription::new(
                    name.clone(),
                    arguments.clone(),
                    ResourceFieldSchema::new(vec![]).expect("empty schema"),
                );
                let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(
                    pointer,
                ))) = description.arguments().first()
                else {
                    paths.push(resource_call_failure(
                        "population helper needs one pointer anchor",
                    ));
                    continue 'arguments;
                };
                let Some(events) = post_state.population_effects.creation.as_ref() else {
                    paths.push(resource_call_failure(
                        "population helper lost its creation history",
                    ));
                    continue 'arguments;
                };
                let anchor = pointer.address();
                if produce
                    && !events.recognizes_imported_population(&description)
                    && (anchor.offset != AddressOffset::Constant(0)
                        || !(matches!(&anchor.base, AddressBase::Heap(_))
                            && post_state.memory.live_heap_block_size(anchor).is_some()
                            || anchor.base.is_local_block()
                                && post_state.memory.has_block(&anchor.base)))
                {
                    paths.push(resource_call_failure("Requires live base storage for R(p)"));
                    continue 'arguments;
                }
                let exclusive = interface
                    .composite_resource_definition(name)
                    .is_some_and(CompositeResourceDefinition::has_fixed_exclusive_memory);
                if defer_locked_exchange {
                    deferred_exchange.push(super::threads::DeferredMemberExchange {
                        block: anchor.base.clone(),
                        description,
                        produce,
                        quantity: quantity.as_ref().clone(),
                        exclusive,
                    });
                    continue;
                }
                let exchange = if exclusive {
                    events.checked_exclusive_member_exchange_quantity(
                        &anchor.base,
                        &description,
                        produce,
                        quantity.native_compat(),
                        &effective_assumptions,
                    )
                } else {
                    events.checked_member_exchange_quantity(
                        &anchor.base,
                        &description,
                        produce,
                        quantity.native_compat(),
                        &effective_assumptions,
                    )
                };
                let (next, _) = match exchange {
                    Ok(exchange) => exchange,
                    Err(refusal) => {
                        paths.push(resource_call_failure(&format!(
                            "population helper member transition refused: {refusal}"
                        )));
                        continue 'arguments;
                    }
                };
                Arc::make_mut(&mut post_state.population_effects).creation = Some(next);
            }
        }
        // Postconditions are lowered against the caller's own states, so
        // their reads are the caller's reads.
        let canonical_entry_contract_state = entry_contract_state.clone();
        // With no transferred input or output resources, there is no allocation
        // to continue, retire, or publish. Lower the ensures only against the
        // final state, where they will be filed as call facts.
        let allocation_delta =
            if transfer.callee_resources.is_empty() && output_resources.is_empty() {
                Ok(VerifiedAllocationDelta {
                    memory: post_state.memory.clone(),
                    effects: ExecutionFacts::new(),
                    retired_allocations: Vec::new(),
                    continued_tokens: Vec::new(),
                })
            } else {
                let provisional_post_contract_state = with_bound_contract_interface_argument_views(
                    &post_state,
                    interface,
                    &argument_values,
                );
                let provisional_post_contract_state = match checked_contract_control_read_state(
                    &provisional_post_contract_state,
                    &output_resources,
                    interface,
                    &effective_assumptions,
                ) {
                    Ok(state) => state,
                    Err(error) => {
                        paths.push(FunctionPath::new(
                            FunctionOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        ));
                        continue;
                    }
                };
                let mut provisional_facts = facts.clone();
                provisional_facts.extend_shared(&coordinate_facts);
                let provisional_ensure_timing = crate::instrumentation::OperationTiming::new(
                    name,
                    "verified function rule application",
                    "verified call provisional ensure lowering",
                );
                add_verified_function_ensure_facts_selected_with_interface(
                    &mut provisional_facts,
                    &obligations,
                    &provisional_post_contract_state,
                    &canonical_entry_contract_state,
                    interface,
                    interface
                        .contract_ensures()
                        .iter()
                        .filter(|ensure| !early_coordinates || !return_coordinate_ensure(ensure)),
                    &effective_assumptions,
                    budget,
                )?;
                drop(provisional_ensure_timing);

                let _allocation_delta_timing = crate::instrumentation::OperationTiming::new(
                    name,
                    "verified function rule application",
                    "verified call heap allocation delta",
                );
                let allocation_assumptions = assumptions_with_path_context(
                    &effective_assumptions,
                    &provisional_facts,
                    &obligations,
                );
                apply_verified_heap_allocation_delta(
                    post_state.memory.clone(),
                    &entry_state.memory,
                    &transfer.callee_resources,
                    &caller_resources_after_requirements,
                    &output_resources,
                    interface,
                    &allocation_assumptions,
                    if suspended.is_some() {
                        post_state.loan_ledger()
                    } else {
                        None
                    },
                    caller_state,
                    &post_state,
                )
            };
        let VerifiedAllocationDelta {
            memory,
            effects: allocation_effects,
            retired_allocations,
            continued_tokens,
        } = match allocation_delta {
            Ok(result) => result,
            Err(VerifiedAllocationDeltaError::Runtime(error)) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
            Err(VerifiedAllocationDeltaError::InconsistentReturnedAllocation) => continue,
        };
        // The caller receives back the very token it lent for an allocation
        // the call continues, so its creation anchor, its live heap claim, and
        // a later `free` all name the block the caller allocated.
        let Some((output_resources, return_resources)) =
            with_continued_allocation_tokens(output_resources, &continued_tokens).zip(
                with_continued_allocation_tokens(return_resources, &continued_tokens),
            )
        else {
            paths.push(resource_call_failure(
                "a continued allocation token is not among the call's returned resources",
            ));
            continue;
        };
        facts.extend(allocation_effects);
        post_state.set_memory(memory);
        if let Some(error) = retired_allocations.iter().find_map(|range| {
            post_state
                .retire_population_storage(&range.base().base)
                .err()
        }) {
            paths.push(FunctionPath::new(
                FunctionOutcome::RuntimeError(error),
                facts,
                obligations,
            ));
            continue;
        }
        let post_contract_state =
            with_bound_contract_interface_argument_views(&post_state, interface, &argument_values);
        let returned_body_state = post_contract_state.clone();
        let post_contract_state = match checked_contract_control_read_state(
            &post_contract_state,
            &output_resources,
            interface,
            &effective_assumptions,
        ) {
            Ok(state) => state,
            Err(error) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
        };
        {
            let body_assumptions =
                assumptions_with_path_context(&effective_assumptions, &facts, &obligations);
            let composite_outputs = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_facts(
                    output_resources
                        .facts()
                        .iter()
                        .filter(|fact| matches!(fact.resource(), Resource::Composite { .. }))
                        .cloned(),
                );
            let Some((_, body_facts)) =
                expand_all_composite_resource_facts_and_propositions_at_state(
                    &composite_outputs,
                    interface.composite_resource_definitions(),
                    &returned_body_state,
                    &body_assumptions,
                )
            else {
                paths.push(resource_call_failure(
                    "could not instantiate the checked returned resource bodies",
                ));
                continue;
            };
            facts.extend(body_facts.into_iter().map(ExecutionPureFact::certified));
        }
        let ensure_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call ensure lowering",
        );
        add_verified_function_ensure_facts_selected_with_interface(
            &mut facts,
            &obligations,
            &post_contract_state,
            &canonical_entry_contract_state,
            interface,
            interface.contract_ensures().iter(),
            &effective_assumptions,
            budget,
        )?;
        drop(ensure_timing);
        if !output_resources.is_empty() {
            let ensured_assumptions =
                assumptions_with_path_context(&effective_assumptions, &facts, &obligations);
            facts.extend(
                checked_returned_instance_body_facts(
                    &output_resources,
                    interface,
                    &post_contract_state,
                    &ensured_assumptions,
                )
                .into_iter()
                .map(ExecutionPureFact::certified),
            );
        }
        // The applicable interfaces share the result and post-call point,
        // but bind their own argument names against the original entry state.
        for additional in additional_calls {
            let mut additional_facts = additional.facts;
            let entry_fact_count = additional_facts.len();
            let mut additional_post = additional.entry_state.clone().with_memory_of(&post_state);
            if additional.interface.return_type() != ProgramType::Void {
                set_contract_result(&mut additional_post, additional.interface, result.clone());
            }
            let additional_post = with_bound_contract_interface_argument_views(
                &additional_post,
                additional.interface,
                &additional.argument_values,
            );
            add_verified_function_ensure_facts_selected_with_interface(
                &mut additional_facts,
                &additional.obligations,
                &additional_post,
                &additional.entry_contract_state,
                additional.interface,
                additional
                    .interface
                    .contract_ensures()
                    .iter()
                    .filter(|ensure| {
                        !independent_guarantees_only
                            || spec_proposition_is_state_independent(ensure)
                            || spec_proposition_supports_stateful_memory_refinement(ensure)
                    }),
                &additional.effective_assumptions,
                budget,
            )?;
            facts.extend(additional_facts.into_iter().skip(entry_fact_count));
        }

        if let Some(completions) = suspended.as_deref_mut() {
            // Only the exact child authorities produced by the checked worker
            // loan plan may cross this boundary. A nested or invented use
            // remains subject to ordinary thread confinement.
            let worker_mutex_uses: BTreeSet<_> = transfer
                .stable_view_plan
                .iter()
                .flat_map(|plan| &plan.mutex_uses)
                .filter_map(|usage| usage.callee_resource().ok())
                .collect();
            if let Some(name) = transfer
                .callee_resources
                .facts()
                .iter()
                .chain(output_resources.facts())
                .find_map(|fact| {
                    // A worker receives an exact authority through the
                    // creation ledger below, as at a sequential call boundary.
                    if worker_mutex_uses.contains(fact)
                        || (matches!(fact, ResourceFact::Own(Resource::PopulationAuthority(_), _)))
                    {
                        None
                    } else {
                        confined_resource_name(fact, interface.composite_resource_definitions())
                    }
                })
            {
                paths.push(resource_call_failure(&format!(
                    "resource `{name}` is thread confined and cannot cross a worker boundary"
                )));
                continue;
            }
            // Definition-level confinement is only an admission rule. The
            // checked partition and loan plan still conserve the authority
            // that a worker receives, and the storage checks below keep the
            // parent's implicit stack/global accesses out of that transfer.
            // In preparation, the parent statement retains these prerequisites
            // and the driver proves them before publishing either create outcome.
            let supported = (obligations.is_empty()
                || effective_assumptions.retains_required_obligations())
                && transfer
                    .stable_view_plan
                    .as_ref()
                    .is_some_and(|plan| plan.supports_suspended_memory_recovery())
                && transfer.candidate_output_views.is_empty()
                && transfer.produced_borrowing_pieces.is_empty()
                && transfer
                    .callee_resources
                    .facts()
                    .iter()
                    .all(|fact| match fact {
                        ResourceFact::Own(Resource::Memory(range), quantity) => {
                            quantity.as_const() == Some(1)
                                && is_external_memory_pointer(range.base())
                        }
                        _ => true,
                    })
                && worker_effects
                    .iter()
                    .all(|range| is_external_memory_pointer(range.base()))
                && output_resources.facts().iter().all(|fact| match fact {
                    ResourceFact::Own(Resource::Memory(range), quantity) => {
                        quantity.as_const() == Some(1) && is_external_memory_pointer(range.base())
                    }
                    ResourceFact::Own(_, _) => true,
                    ResourceFact::View(_) => false,
                });
            if !supported {
                paths.push(resource_call_failure(
                    "suspended worker requires discharged preconditions, explicit ownership of external memory, and nonescaping views",
                ));
                continue;
            }
            let Some(plan) = transfer.stable_view_plan else {
                paths.push(resource_call_failure(
                    "suspended worker requires a checked resource partition",
                ));
                continue;
            };
            let creation = {
                let (Some(after), Some(parent), Some(worker)) = (
                    post_state.population_effects.creation.as_ref(),
                    caller_state.population_effects.creation.as_ref(),
                    entry_state.population_effects.creation.as_ref(),
                ) else {
                    paths.push(resource_call_failure(
                        "suspended worker lost its creation history",
                    ));
                    continue;
                };
                Some(super::threads::WorkerCreation {
                    parent_after_create: after.return_to(parent),
                    worker: worker.clone(),
                    definitions: interface.composite_resource_definitions().to_vec(),
                    deferred: deferred_exchange.clone(),
                })
            };
            completions.push((
                super::threads::WorkerCompletion::checked(
                    plan,
                    output_resources,
                    post_state.memory.clone(),
                    worker_effects,
                    facts,
                    post_state.mutex_ledger.clone(),
                    creation,
                )
                .with_entry_partition(transfer.returned_entry_partition),
                obligations,
            ));
            // The internal caller checks there is exactly one completion.
            // No worker guarantee or ownership is published as a call return.
            continue;
        }

        let return_assumptions = assumptions_with_path_context(&effective_assumptions, &facts, &[]);
        let (
            return_resources,
            return_ledger,
            return_participant,
            return_view_bindings,
            loan_evidence,
        ) = match recover_candidate_stable_view_resources(
            caller_state,
            &post_state,
            &transfer,
            return_resources,
            escrow_boundary,
            &effective_assumptions,
            &return_assumptions,
            &obligations,
        ) {
            Ok(recovered) => recovered,
            Err(error) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
        };

        let mut return_state = caller_state.clone();
        return_state.set_memory_of(&post_state);
        refresh_call_written_locals(
            &mut return_state,
            &transfer.memory_effects,
            &effective_assumptions,
        );
        return_state.resources = return_resources;
        return_state.loan_ledger = return_ledger;
        return_state.loan_participant = return_participant;
        return_state = return_state.with_loan_view_bindings(return_view_bindings);
        return_state.thread_ledger = post_state.thread_ledger.clone();
        return_state.mutex_ledger = post_state.mutex_ledger.clone();
        return_state.mutex_input_reservations = post_state.mutex_input_reservations.clone();
        return_state.opaque_mutex_acquisitions = post_state.opaque_mutex_acquisitions.clone();
        let mut helper_evidence = empty_checked_loan_evidence_sequence();
        if let Some((successor, evidence)) = helper_effect {
            if return_state.loan_ledger != caller_state.loan_ledger
                || return_state.loan_participant != caller_state.loan_participant
            {
                paths.push(resource_call_failure(
                    "mutex helper protocol effect requires completed ordinary loan recovery",
                ));
                continue;
            }
            return_state.loan_ledger = successor.loan_ledger;
            return_state.loan_participant = successor.loan_participant;
            helper_evidence = evidence;
        }
        // A callee's proof names are scoped to that call. Its checked return
        // restores the caller's names against the recovered occurrences below.
        return_state.named_mutex_authorities = caller_state.named_mutex_authorities.clone();
        if let Some(bindings) = selected_bindings.as_ref() {
            for resource in interface.resource_ensures() {
                let Some((formal, binder)) = resource.mutex_authority_binding() else {
                    continue;
                };
                if resource.role() == ResourceTransferRole::Produce {
                    let Some(actual) = bindings.get(&formal).copied() else {
                        paths.push(resource_call_failure(&format!(
                            "call map omits produced mutex authority binder `{binder}`"
                        )));
                        continue 'arguments;
                    };
                    let required = match evaluate_function_resource_spec_with_entry(
                        &entry_contract_state,
                        &post_state,
                        resource,
                        &effective_assumptions,
                        budget,
                    )? {
                        Ok(fact) => fact,
                        Err(error) => {
                            paths.push(FunctionPath::new(
                                FunctionOutcome::RuntimeError(error),
                                facts,
                                obligations,
                            ));
                            continue 'arguments;
                        }
                    };
                    return_state = match return_state.bind_named_mutex_authority(actual, &required)
                    {
                        Ok(state) => state,
                        Err(_) => {
                            paths.push(resource_call_failure(
                                "produced mutex guard has no fresh owned acquisition",
                            ));
                            continue 'arguments;
                        }
                    };
                    continue;
                }
                if resource.role() != ResourceTransferRole::Borrow {
                    continue;
                }
                let Some(actual) = bindings.get(&formal).copied() else {
                    paths.push(resource_call_failure(&format!(
                        "call map omits returned mutex authority binder `{binder}`"
                    )));
                    continue 'arguments;
                };
                let Some(fact) = caller_state.resolve_named_mutex_authority(actual) else {
                    paths.push(resource_call_failure(&format!(
                        "Requires owns mutex authority `{binder}`"
                    )));
                    continue 'arguments;
                };
                return_state = match return_state.rebind_named_mutex_authority(actual, fact) {
                    Ok(rebound) => rebound,
                    Err(_) => {
                        paths.push(resource_call_failure(&format!(
                            "returned mutex authority `{binder}` does not preserve the selected acquisition or initialization"
                        )));
                        continue 'arguments;
                    }
                };
            }
        }
        return_state.population_access = post_state.population_access.clone();
        return_state.observed_population_families = post_state.observed_population_families.clone();
        {
            let returned = match transfer_population_call_facts(
                post_state.clone(),
                &entry_state,
                caller_state,
                &post_state,
                output_resources.facts().iter(),
                interface.composite_resource_definitions(),
                &return_assumptions,
            ) {
                Ok(state) => state,
                Err(error) => {
                    paths.push(FunctionPath::new(
                        FunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            };
            let returned = match locked_helper_population(
                interface,
                &transfer,
                &entry_contract_state,
                &effective_assumptions,
                budget,
            )? {
                Ok(populations) => {
                    let mut returned = returned;
                    let mut refused = None;
                    for description in &populations {
                        let back = returned
                            .population_effects
                            .creation
                            .as_ref()
                            .zip(entry_state.population_effects.creation.as_ref())
                            .zip(caller_state.population_effects.creation.as_ref())
                            .ok_or(crate::kernel::population_authority::storage_creation::CreationRefusal::MissingAuthority)
                            .and_then(|((events, callee), caller)| {
                                events.transfer_call_fact(callee, caller, description, true)
                            });
                        match back {
                            Ok(events) => {
                                Arc::make_mut(&mut returned.population_effects).creation =
                                    Some(events)
                            }
                            Err(refusal) => {
                                refused = Some(refusal);
                                break;
                            }
                        }
                    }
                    if let Some(refusal) = refused {
                        paths.push(resource_call_failure(&format!(
                            "locked helper did not return its population authority: {refusal}"
                        )));
                        continue;
                    }
                    returned
                }
                Err(error) => {
                    paths.push(FunctionPath::new(
                        FunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            };
            let finished = returned
                .population_effects
                .creation
                .as_ref()
                .expect("checked population call has a ledger")
                .finish_call(
                    caller_state
                        .population_effects
                        .creation
                        .as_ref()
                        .expect("checked population caller has a ledger"),
                );
            match finished {
                Ok(events) => {
                    Arc::make_mut(&mut return_state.population_effects).creation = Some(events)
                }
                Err(refusal) => {
                    paths.push(resource_call_failure(&format!(
                        "population helper retained ownership: {refusal}"
                    )));
                    continue;
                }
            }
        }
        return_state = match checked_returned_control_wrappers(
            return_state,
            &output_resources,
            interface,
            &effective_assumptions,
        ) {
            Ok(state) => state,
            Err(error) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
        };
        return_state.next_local_frame = post_state.next_local_frame;
        return_state.next_local_lifetime = post_state.next_local_lifetime;
        let outcome = FunctionOutcome::Return {
            value: ExecutionValue::from(result)
                .retain_pointer_result()
                .retain_float_result()
                .into(),
            state: Box::new(return_state),
        };
        if let Some(function) = evidence {
            append_string_literal_loadable_facts(function, &outcome, &mut facts);
        }
        let call_parameters = CallParameters::of(&entry_contract_state, interface);
        // The checked return partition recovers this call's loans. The
        // transition that uses it still owes separation from the caller's
        // pre-existing loans, on both normal and exceptional paths.
        if let Some(path) = &mut exceptional_path
            && matches!(path.outcome, FunctionOutcome::Throw { .. })
        {
            path.obligations.extend(write_requirements.iter().cloned());
        }
        obligations.extend(write_requirements);
        // The retirement ranges are the consumed allocation tokens at
        // entry. Return facts may decide continuity, but they cannot prove
        // that retiring one of those allocations was permitted.
        if suspended.is_none() {
            obligations.extend(verified_call_loan_requirements(
                entry_state.loan_ledger(),
                &retired_allocations,
                call_site,
                interface.contract_requires().len() + transfer.memory_effects.len(),
                "verified call allocation retirement separation",
            ));
        }
        paths.push(FunctionPath {
            outcome,
            facts,
            obligations,
            loan_evidence: super::loans::concat_checked_loan_evidence(
                &loan_evidence
                    .map(|evidence| {
                        append_checked_loan_evidence(
                            &empty_checked_loan_evidence_sequence(),
                            Some(evidence),
                        )
                    })
                    .unwrap_or_else(empty_checked_loan_evidence_sequence),
                &helper_evidence,
            ),
            call_parameters: call_parameters.clone(),
        });
        if let Some(mut path) = exceptional_path {
            path.call_parameters = call_parameters;
            paths.push(path);
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn verified_call_loan_requirements(
    ledger: Option<&LoanLedger>,
    effects: &[MemoryRange],
    call_site: impl FnOnce() -> CallRequirementSite,
    first_ordinal: usize,
    context: &str,
) -> Vec<ProofObligation> {
    let Some(ledger) = ledger else {
        return Vec::new();
    };
    let mut requirements = effects
        .iter()
        .enumerate()
        .filter_map(|(index, range)| {
            ledger
                .memory_access_requirement(range)
                .map(|requirement| (index, requirement))
        })
        .peekable();
    if requirements.peek().is_none() {
        return Vec::new();
    }
    let site = Arc::new(call_site());
    requirements
        .map(|(index, requirement)| {
            ProofObligation::verification_condition(requirement)
                .with_call_requirement_site(Arc::new(CallRequirementSource::new(
                    site.clone(),
                    first_ordinal + index,
                    None,
                    false,
                    None,
                )))
                .with_context(context)
        })
        .collect()
}

fn refresh_call_written_locals(
    state: &mut ExecutionState,
    effects: &[MemoryRange],
    assumptions: &PureFactContext,
) {
    // A modular write changes address-backed scalar bindings as well as
    // memory. Visit only blocks named by this effect or its checked alias
    // class, never the caller's unrelated local environment.
    let mut refreshed_blocks = BTreeSet::new();
    for range in effects {
        for block in std::iter::once(range.base().base.clone()).chain(
            assumptions
                .equality_graph
                .local_slot_alias_blocks(range.base()),
        ) {
            if !refreshed_blocks.insert(block.clone()) {
                continue;
            }
            let slot = Address {
                base: block,
                offset: AddressOffset::Constant(0),
            };
            crate::kernel::eval::refresh_scalar_local_from_memory(state, &slot, assumptions);
        }
    }
}

/// Builds the exceptional successor of a modular call: a direct call, whose
/// function declaration supplies storage identity (not necessarily body
/// evidence: targeted proofs may assume an unselected callee's checked
/// interface), or a call through a pointer under a named contract, which has
/// no declaration.
/// Entry checking and footprint-bounded memory havoc are shared with the
/// normal application, but the payload and certified facts are specific to
/// this outcome. Keeping this path separate is what prevents ordinary
/// `ensures` from becoming exceptional facts (and vice versa).
fn exceptional_direct_function_path(
    caller_state: &ExecutionState,
    interface: &FunctionContractInterface,
    evidence: Option<&ProgramFunction>,
    framed_rule: Option<FramedCallRule<'_>>,
    argument_values: &[ProgramValue],
    entry_state: &ExecutionState,
    entry_contract_state: &ExecutionState,
    transfer: &FunctionResourceTransfer,
    memory: SymbolicMemory,
    mut facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    effective_assumptions: &PureFactContext,
    payload_identity: Variable,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<FunctionPath> {
    debug_assert!(interface.verified_direct_contract_supported());
    debug_assert!(interface.resource_constructors().is_empty());
    let payload_type = interface
        .exceptional_signature()
        .payload_type()
        .expect("exceptional interface");
    let payload = symbolic_call_result(payload_type, payload_identity);
    let mut post_state = entry_state.clone().with_memory(memory.clone());
    post_state
        .locals
        .set_typed(CONTRACT_EXCEPTION, payload.clone(), payload_type);
    let post_contract_state =
        with_bound_contract_interface_argument_views(&post_state, interface, argument_values);
    add_verified_function_ensure_facts_selected_with_interface(
        &mut facts,
        &obligations,
        &post_contract_state,
        entry_contract_state,
        interface,
        interface.exceptional_ensures().iter(),
        effective_assumptions,
        budget,
    )?;

    if !transfer.memory_effects.is_empty() {
        facts.push(
            ExecutionPureFact::internal(Proposition::MemoryEffectSummary {
                before: entry_state.memory.clone(),
                after: memory.clone(),
                mutable_ranges: transfer.memory_effects.clone(),
            })
            .into_certified(),
        );
    }
    let post_assumptions = assumptions_with_path_context(effective_assumptions, &facts, &[]);
    let ContractReturnResources {
        return_resources,
        escrow_boundary,
        ensured_views,
        produced_borrowing_pieces,
        returned_entry_partition,
        ..
    } = match evaluate_contract_return_resources(
        &transfer.caller_resources_after_requirements,
        escrowed_owners(transfer),
        &transfer.canonical_borrowed_owners,
        &transfer.borrowed_inputs,
        &transfer_entry_clauses(transfer),
        entry_contract_state,
        &post_contract_state,
        evidence.map_or("exceptional call", |function| function.name()),
        interface,
        &[],
        ReturnResourceComposition::for_rule(framed_rule, &transfer.consumed_cell_returns),
        &post_assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => {
            return Ok(FunctionPath::new(
                FunctionOutcome::RuntimeError(error),
                facts,
                obligations,
            ));
        }
    };
    let mut transfer = transfer.clone();
    transfer.returned_entry_partition = returned_entry_partition;
    transfer.candidate_output_views = ensured_views;
    transfer.produced_borrowing_pieces = produced_borrowing_pieces;
    post_state.resources = return_resources.clone();
    let (resources, ledger, participant, bindings, loan_evidence) =
        match recover_candidate_stable_view_resources(
            caller_state,
            &post_state,
            &transfer,
            return_resources,
            escrow_boundary,
            effective_assumptions,
            &post_assumptions,
            &obligations,
        ) {
            Ok(recovered) => recovered,
            Err(error) => {
                return Ok(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
            }
        };
    let mut throw_state = caller_state.clone();
    throw_state.set_memory(memory);
    refresh_call_written_locals(
        &mut throw_state,
        &transfer.memory_effects,
        &post_assumptions,
    );
    throw_state.resources = resources;
    throw_state.loan_ledger = ledger;
    throw_state.loan_participant = participant;
    throw_state = throw_state.with_loan_view_bindings(bindings);
    throw_state.next_local_frame = post_state.next_local_frame;
    throw_state.next_local_lifetime = post_state.next_local_lifetime;
    throw_state.restore_population_creation_after_call(
        caller_state.population_effects.creation.as_ref(),
        post_state.population_effects.creation.as_ref(),
    );
    let outcome = FunctionOutcome::Throw {
        value: payload.into(),
        state: Box::new(throw_state),
    };
    if let Some(evidence) = evidence {
        append_string_literal_loadable_facts(evidence, &outcome, &mut facts);
    }
    let mut path = FunctionPath::new(outcome, facts, obligations);
    path.loan_evidence = loan_evidence
        .map(|evidence| {
            append_checked_loan_evidence(&empty_checked_loan_evidence_sequence(), Some(evidence))
        })
        .unwrap_or_else(empty_checked_loan_evidence_sequence);
    Ok(path)
}

struct PreparedVerifiedFunctionCall<'a> {
    /// The nominal callee name used for diagnostics and attribution. It is not
    /// a source-body handle for named callbacks.
    name: &'a str,
    interface_name: &'a str,
    candidate_ordinal: usize,
    has_exact_write_ranges: bool,
    /// Concrete declaration identity for global and static storage lowering.
    /// This is not evidence that the function body was checked.
    storage: Option<&'a ProgramFunction>,
    /// Concrete evidence is present only for a verified direct rule. Named
    /// contracts and external assumptions deliberately carry none.
    evidence: Option<&'a ProgramFunction>,
    /// A theorem or an established contract premise; concrete
    /// declaration storage alone never grants this frame rule.
    framed_rule: Option<FramedCallRule<'a>>,
    /// The body-independent interface used to prepare this application. It is
    /// explicit even when it is the concrete function's own interface, so
    /// callback and ordinary calls cannot silently grow separate evaluators.
    interface: &'a FunctionContractInterface,
    argument_values: Vec<ProgramValue>,
    entry_state: ExecutionState,
    entry_contract_state: ExecutionState,
    transfer: FunctionResourceTransfer,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    effective_assumptions: PureFactContext,
    /// The binder map this interface was selected with, if any. A `produces`
    /// binder reads its caller-side identity from exactly this map.
    bindings: Option<std::sync::Arc<BTreeMap<Variable, Variable>>>,
}

/// Finds the exact source state carried by a lowered pure requirement.
/// This is deliberately narrower than the general recursive variable walker:
/// only the logical/condition/bitvector shapes admitted by the source-backed
/// classifier are visited, with the same finite structural budget.
fn source_load_state_for_proposition(
    proposition: &Proposition,
) -> ExecutionResult<Option<MemoryStateIdentity>> {
    const MAX_NODES: usize = 4096;
    enum Work<'a> {
        Proposition(&'a Proposition),
        Condition(&'a ConditionTerm),
        Bitvector(&'a MachineTerm),
    }
    let mut work = vec![Work::Proposition(proposition)];
    let mut visited = 0usize;
    let mut memory_identity = None;
    while let Some(item) = work.pop() {
        visited = visited.saturating_add(1);
        crate::instrumentation::record_deterministic_work(1);
        if visited > MAX_NODES {
            return Err(ExecutionLimit::ExpressionSteps);
        }
        if crate::kernel::assumptions::reasoning_interrupted() {
            return Err(ExecutionLimit::Deadline);
        }
        match item {
            Work::Proposition(Proposition::ConditionIs(condition, _)) => {
                work.push(Work::Condition(condition.native_compat()));
            }
            Work::Proposition(Proposition::And(left, right))
            | Work::Proposition(Proposition::Or(left, right))
            | Work::Proposition(Proposition::Implies(left, right)) => {
                work.push(Work::Proposition(right));
                work.push(Work::Proposition(left));
            }
            Work::Proposition(Proposition::Not(body))
            | Work::Proposition(Proposition::ForAll { body, .. })
            | Work::Proposition(Proposition::Exists { body, .. }) => {
                work.push(Work::Proposition(body));
            }
            Work::Proposition(_) => return Ok(None),
            Work::Condition(crate::kernel::binary_bitvector_condition!(left, right)) => {
                work.push(Work::Bitvector(right));
                work.push(Work::Bitvector(left));
            }
            Work::Condition(ConditionTerm::Constant(_))
            | Work::Condition(ConditionTerm::Variable(_)) => {}
            Work::Condition(_) => return Ok(None),
            Work::Bitvector(bits32_constant!(_))
            | Work::Bitvector(int64_constant!(_))
            | Work::Bitvector(uint64_constant!(_)) => {}
            Work::Bitvector(MachineTerm::Variable(variable)) => {
                if crate::kernel::is_load_variable(variable) {
                    let Some((origin, _)) =
                        crate::kernel::registered_load_origin_for_variable(variable)
                    else {
                        return Ok(None);
                    };
                    let identity = MemoryStateIdentity::of(origin.memory());
                    if memory_identity.is_some_and(|known| known != identity) {
                        return Ok(None);
                    }
                    memory_identity = Some(identity);
                }
            }
            Work::Bitvector(term @ MachineTerm::MemoryLoad(..)) => {
                let read = crate::kernel::eval::scalar_read_observation(
                    crate::kernel::MachineOperandView::Legacy(term),
                )
                .expect("structural read observation");
                let origin = read.origin.unwrap_or(read.memory);
                let identity = MemoryStateIdentity::of(origin.memory());
                if memory_identity.is_some_and(|known| known != identity) {
                    return Ok(None);
                }
                memory_identity = Some(identity);
            }
            Work::Bitvector(crate::kernel::binary_bitvector32_term!(left, right)) => {
                work.push(Work::Bitvector(right));
                work.push(Work::Bitvector(left));
            }
            Work::Bitvector(unary_term!(Int32, BitwiseNot, body)) => {
                work.push(Work::Bitvector(body));
            }
            Work::Bitvector(_) => return Ok(None),
        }
    }
    Ok(memory_identity)
}

/// Register only the controls explicitly returned by this call. Custody and
/// their bodies have already crossed the checked resource-transfer boundary.
fn checked_returned_control_wrappers(
    mut state: ExecutionState,
    frontier: &ResourceContext,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, RuntimeError> {
    for fact in frontier.facts() {
        let ResourceFact::Own(Resource::Composite { name, .. }, _) = fact else {
            continue;
        };
        let Some(definition) = interface.composite_resource_definition(name) else {
            continue;
        };
        if definition
            .contains()
            .iter()
            .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
        {
            state = state
                .with_checked_current_control_wrapper(fact, definition, assumptions)
                .map_err(RuntimeError::FunctionContract)?;
        }
    }
    Ok(state)
}

/// Retains only the transfer's explicit memory delta beside the persistent
/// caller frame. No expansion or scan of unrelated frame resources is needed.
/// An aliasing or otherwise invalid composition supplies no separation fact.
fn checked_contract_control_read_state(
    state: &ExecutionState,
    frontier: &ResourceContext,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, RuntimeError> {
    let mut resources = state.resources().clone();
    for fact in frontier.facts() {
        let ResourceFact::Own(Resource::Composite { name, .. }, _) = fact else {
            continue;
        };
        let Some(definition) = interface.composite_resource_definition(name) else {
            continue;
        };
        if !definition
            .contains()
            .iter()
            .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
        {
            continue;
        }
        let Some(owned) = resources
            .directly_supporting_fact(fact, assumptions)
            .filter(|candidate| candidate.is_own())
            .cloned()
        else {
            // An entry checker may already have exposed this control body.
            continue;
        };
        let (children, _) = state
            .checked_authority_wrapper_body(&owned, definition, assumptions)
            .map_err(RuntimeError::FunctionContract)?;
        let without_head = resources
            .without_fact_incrementally(&owned, assumptions)
            .ok_or_else(|| RuntimeError::MissingResource {
                resource: Box::new(fact.clone()),
            })?;
        // The selected held wrapper supplies its body beside this frame.
        // Keep the constructed successor; an equal ambient child is not a
        // replacement for the ownership removed with the parent.
        resources = without_head
            .install_established_partition(children, assumptions)
            .map(|(context, _)| context)
            .map_err(resource_context_runtime_error)?;
    }
    Ok(state.clone().with_resource_context(resources))
}

fn prepare_verified_function_call<'a>(
    caller_state: &ExecutionState,
    application: FunctionContractApplication<'a>,
    candidate_ordinal: usize,
    source_arguments: &[ProgramExpression],
    arguments_path: ArgumentsPath<ExecutionValue>,
    require_established: bool,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
    resource_application: Option<&ResourceCallApplication>,
    suspend_worker: bool,
) -> ExecutionResult<Result<PreparedVerifiedFunctionCall<'a>, FunctionPath>> {
    let contract_interface = application.interface;
    if contract_reaches_population(contract_interface)
        && ((suspend_worker && application.evidence.is_none())
            || (application.evidence.is_none()
                && !environment
                    .get_external_function_rule(application.name)
                    .is_some_and(ExternalFunctionRule::is_scoped_unselected)
                && !authority_preserves_assumed_resource_contract(contract_interface)))
    {
        let error = authority_call_refusal();
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(error),
            arguments_path.facts,
            arguments_path.obligations,
        )));
    }
    if contract_reaches_population(contract_interface)
        && !authority_supports_resource_contract(contract_interface)
    {
        return Ok(Err(resource_call_failure(
            "helper contract needs conserved owns resources, a checked consumes/produces effect, or a supported unit exchange",
        )));
    }
    if contract_interface.contract_requirement_sources().len()
        != contract_interface.contract_requires().len()
    {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                "call requirement source map does not match the selected contract".to_string(),
            )),
            arguments_path.facts,
            arguments_path.obligations,
        )));
    }
    let mut call_requirement_site = None;
    let initial_obligation_count = arguments_path.obligations.len();
    let path_assumptions = assumptions_with_path_context(
        assumptions,
        &arguments_path.facts,
        &arguments_path.obligations,
    );
    let native_arguments = arguments_path
        .values
        .iter()
        .map(|value| value.native().into_owned())
        .collect::<Vec<_>>();
    if let Some(undefined_behavior) = freed_pointer_argument_conversion(
        caller_state,
        contract_interface,
        &native_arguments,
        &path_assumptions,
    ) {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::UndefinedBehavior(undefined_behavior),
            arguments_path.facts,
            arguments_path.obligations,
        )));
    }
    if let Some(refusal) = incompatible_pointer_argument(
        caller_state,
        application.name,
        contract_interface,
        &native_arguments,
        &path_assumptions,
    ) {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(refusal),
            arguments_path.facts,
            arguments_path.obligations,
        )));
    }
    let Some((mut argument_values, argument_obligations)) = coerce_contract_arguments(
        contract_interface,
        &native_arguments,
        &arguments_path.obligations,
        &path_assumptions,
    ) else {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                contract_argument_binding_error(
                    contract_interface,
                    application.name,
                    &native_arguments,
                ),
            )),
            arguments_path.facts,
            arguments_path.obligations,
        )));
    };
    if let Some(outcome) = aggregate_argument_read_refusal(
        caller_state,
        contract_interface.parameters(),
        &argument_values,
        &path_assumptions,
    ) {
        return Ok(Err(FunctionPath::new(
            outcome,
            arguments_path.facts,
            argument_obligations,
        )));
    }
    if let Some(refusal) = crate::kernel::object_types::check_requirements(
        application.name,
        contract_interface.parameters(),
        contract_interface.object_type_requirements(),
        &mut argument_values,
        caller_state.memory(),
        &path_assumptions,
    ) {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(refusal),
            arguments_path.facts,
            argument_obligations,
        )));
    }
    let Some(mut entry_state) = bind_contract_arguments(
        caller_state,
        contract_interface,
        &argument_values,
        application.storage,
        &arguments_path.values,
    ) else {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                contract_argument_binding_error(
                    contract_interface,
                    application.name,
                    &argument_values,
                ),
            )),
            arguments_path.facts,
            argument_obligations,
        )));
    };
    // A named contract's value parameters take the values its fact fixed,
    // as the call parameters take the call's arguments. A function's own
    // contract value parameters, `let n: uint64;`, take the values the
    // proof's call map gives or the one held instance each one's clause
    // selects. The choice is not trusted: the requirements are then checked
    // at those values.
    let selected_value_arguments;
    let application_value_arguments = if application.value_arguments.is_empty()
        && !contract_interface.value_parameters().is_empty()
    {
        selected_value_arguments = match call_value_arguments(
            application.name,
            contract_interface,
            caller_state,
            &entry_state,
            environment,
            &path_assumptions,
            budget,
        )? {
            Ok(values) => values,
            Err(message) => {
                return Ok(Err(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
                    arguments_path.facts,
                    argument_obligations,
                )));
            }
        };
        selected_value_arguments.as_slice()
    } else {
        application.value_arguments
    };
    if application_value_arguments.len() != contract_interface.value_parameters().len() {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                "contract `{}` needs values for its value parameters",
                application.interface_name
            ))),
            arguments_path.facts,
            argument_obligations,
        )));
    }
    let mut checked_value_arguments = std::borrow::Cow::Borrowed(application_value_arguments);
    if contract_interface
        .object_type_requirements()
        .get_max()
        .is_some_and(|(index, _)| *index >= contract_interface.parameters().len())
        && let Some(refusal) = crate::kernel::object_types::check_value_requirements(
            application.name,
            contract_interface,
            checked_value_arguments.to_mut(),
            caller_state.memory(),
            &path_assumptions,
        )
    {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(refusal),
            arguments_path.facts,
            argument_obligations,
        )));
    }
    let application_value_arguments = checked_value_arguments.as_ref();
    for (parameter, value) in contract_interface
        .value_parameters()
        .iter()
        .zip(application_value_arguments)
    {
        entry_state.locals.set_typed_qualified_with_all_qualifiers(
            parameter.binding_name().clone(),
            value.clone(),
            parameter.program_type(),
            SymbolicMemory::value_parameter_pointer(parameter.binding_name()),
            false,
            false,
            false,
            false,
        );
    }
    let path_assumptions =
        assumptions_with_path_context(assumptions, &arguments_path.facts, &argument_obligations);
    if let Some(application) = resource_application {
        entry_state.resource_bindings = Some(application.bindings.clone());
        // The bound instances are clauses of one contract, so they are
        // addressed as one section: an instance whose argument loads a cell
        // a sibling's unmatched body owns reads it through that sibling.
        if let Err(error) = evaluate_resource_clauses_against_whole_section(
            &entry_state,
            &entry_state,
            &application.parameters,
            contract_interface.composite_resource_definitions(),
            &path_assumptions,
            budget,
        )? {
            return Ok(Err(FunctionPath::new(
                FunctionOutcome::RuntimeError(error),
                arguments_path.facts,
                argument_obligations,
            )));
        }
        for parameter in application.parameters.iter() {
            let Some((formal, _)) = parameter.mutex_authority_binding() else {
                continue;
            };
            let Some(actual) = application.bindings.get(&formal) else {
                continue;
            };
            let expected = evaluate_function_resource_spec_with_entry(
                &entry_state,
                &entry_state,
                parameter,
                &path_assumptions,
                budget,
            )?;
            let error = match expected {
                Ok(expected)
                    if caller_state.resolve_named_mutex_authority(*actual) == Some(&expected)
                        || (matches!(expected.resource(), Resource::MutexUse(_))
                            && caller_state
                                .resolve_named_mutex_authority(*actual)
                                .is_some_and(|source| {
                                    match (source.resource(), expected.resource()) {
                                        (Resource::MutexLive(live), Resource::MutexUse(usage)) => {
                                            live.mutex == usage.mutex
                                                && live.epoch.is_some()
                                                && usage.initialization.is_none_or(|generation| {
                                                    live.epoch == Some(generation)
                                                })
                                        }
                                        (
                                            Resource::MutexUse(selected),
                                            Resource::MutexUse(usage),
                                        ) => {
                                            selected.mutex == usage.mutex
                                                && selected.initialization.is_some()
                                                && usage.initialization.is_none_or(|generation| {
                                                    selected.initialization == Some(generation)
                                                })
                                        }
                                        _ => false,
                                    }
                                })) =>
                {
                    None
                }
                Ok(expected) => Some(RuntimeError::MissingResource {
                    resource: Box::new(expected),
                }),
                Err(error) => Some(error),
            };
            if let Some(error) = error {
                return Ok(Err(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    arguments_path.facts,
                    argument_obligations,
                )));
            }
        }
    }
    let mut facts = arguments_path.facts;
    let selected_instance_facts = selected_resource_instance_case_facts(
        caller_state,
        resource_application.map(|application| application.bindings.as_ref()),
        contract_interface.composite_resource_definitions(),
        &path_assumptions,
    );
    facts.extend(
        selected_instance_facts
            .iter()
            .cloned()
            .map(ExecutionPureFact::new),
    );
    let path_assumptions =
        assumptions_with_path_context(assumptions, &facts, &argument_obligations);
    let transfer = match crate::instrumentation::measure_operation(
        application.name,
        "verified function rule application",
        "verified call resource transfer preparation",
        || {
            prepare_contract_resource_transfer(
                caller_state,
                &entry_state,
                application.name,
                contract_interface,
                &path_assumptions,
                budget,
                false,
                if suspend_worker {
                    ResourceTransitionPurpose::SuspendedWorker
                } else {
                    ResourceTransitionPurpose::CallSite
                },
            )
        },
    )? {
        Ok(transfer) => transfer,
        Err(error) => {
            return Ok(Err(FunctionPath::new(
                FunctionOutcome::RuntimeError(error),
                facts,
                argument_obligations,
            )));
        }
    };
    let callee_identity_state = entry_state.clone();
    // A locked call from a proof that holds only a typed `mutex_use` share
    // enters the escrowed population there first, as a lock would: a fresh
    // total, the caller's own members, and no count observation. The ledger
    // then lends it to the call like any held population, and the caller's
    // own exit check compares the declared change with the calls' changes.
    if !suspend_worker {
        let populations = match locked_helper_population(
            contract_interface,
            &transfer,
            &callee_identity_state,
            &path_assumptions,
            budget,
        )? {
            Ok(populations) => populations,
            Err(error) => return Ok(Err(resource_call_failure(&format!("{error}")))),
        };
        for description in &populations {
            let (Some(caller_events), Some(callee_events), Some(entry_events)) = (
                caller_state.population_effects.creation.as_ref(),
                callee_identity_state.population_effects.creation.as_ref(),
                entry_state.population_effects.creation.as_ref(),
            ) else {
                continue;
            };
            if caller_events.recognizes_population_authority(description) {
                continue;
            }
            let member = Resource::Composite {
                name: description.family().to_owned(),
                arguments: description.arguments().to_vec().into(),
            };
            let Some(owned) = caller_state
                .resources
                .exact_resource_facts(&member)
                .into_iter()
                .filter_map(|fact| fact.owned_quantity_term().and_then(MachineTerm::as_const))
                .try_fold(0u32, u32::checked_add)
            else {
                return Ok(Err(resource_call_failure(
                    "locked helper caller holds an unbounded number of members",
                )));
            };
            let entered = entry_events
                .import_acquired_control_population(description, owned)
                .and_then(|events| {
                    events.transfer_call_fact(callee_events, caller_events, description, true)
                })
                .and_then(|events| {
                    if owned == 0 {
                        Ok(events)
                    } else {
                        events.transfer_call_fact_quantity(
                            callee_events,
                            caller_events,
                            description,
                            false,
                            &MachineTerm::constant(owned),
                            &path_assumptions,
                        )
                    }
                });
            match entered {
                Ok(events) => {
                    Arc::make_mut(&mut entry_state.population_effects).creation = Some(events)
                }
                Err(refusal) => {
                    return Ok(Err(resource_call_failure(&format!(
                        "locked helper population cannot enter the caller's proof: {refusal}"
                    ))));
                }
            }
        }
    }
    entry_state = callee_state_with_resource_transfer(entry_state, &transfer);
    entry_state = match transfer_population_call_facts(
        entry_state,
        caller_state,
        &callee_identity_state,
        caller_state,
        transfer
            .borrowed_inputs
            .iter()
            .chain(&transfer.consumed_inputs)
            .map(|checked| &checked.fact),
        contract_interface.composite_resource_definitions(),
        &path_assumptions,
    ) {
        Ok(state) => state,
        Err(
            RuntimeError::FunctionContract(message)
            | RuntimeError::UnsuppliedResourceValue(message),
        ) => {
            return Ok(Err(resource_call_failure(&message)));
        }
        Err(error) => return Ok(Err(resource_call_failure(&format!("{error}")))),
    };
    if !suspend_worker {
        let lent = match locked_helper_population(
            contract_interface,
            &transfer,
            &callee_identity_state,
            &path_assumptions,
            budget,
        )? {
            Ok(lent) => lent,
            Err(error) => return Ok(Err(resource_call_failure(&format!("{error}")))),
        };
        for description in &lent {
            let lent = entry_state
                .population_effects
                .creation
                .as_ref()
                .zip(caller_state.population_effects.creation.as_ref())
                .zip(callee_identity_state.population_effects.creation.as_ref())
                .ok_or("locked helper call lost its creation history")
                .and_then(|((events, caller), callee)| {
                    events
                        .transfer_call_fact(caller, callee, description, true)
                        .map_err(|_| "locked helper requires the caller's population authority")
                });
            match lent {
                Ok(events) => {
                    Arc::make_mut(&mut entry_state.population_effects).creation = Some(events)
                }
                Err(error) => return Ok(Err(resource_call_failure(error))),
            }
        }
    }
    // The checked loan plan identifies each selected use source and its
    // derived callee share. Move only those names, then rebind unchanged raw
    // authorities to their newly inserted occurrences.
    if let Some(plan) = transfer.stable_view_plan.as_ref() {
        for use_plan in &plan.mutex_uses {
            let Some(actual) = use_plan.selected_alias() else {
                continue;
            };
            let derived = match use_plan.callee_resource() {
                Ok(derived) => derived,
                Err(_) => {
                    return Ok(Err(resource_call_failure(
                        "selected mutex use has no checked callee share",
                    )));
                }
            };
            entry_state = match entry_state.transport_named_mutex_use(
                actual,
                use_plan.source_resource(),
                &derived,
            ) {
                Ok(transferred) => transferred,
                Err(_) => {
                    return Ok(Err(resource_call_failure(
                        "transferred mutex use is not the selected owned occurrence",
                    )));
                }
            };
        }
    }
    if let Some(selected) = resource_application {
        for parameter in selected.parameters.iter() {
            if matches!(parameter.term(), ResourceTerm::MutexUse { .. }) {
                continue;
            }
            let Some((formal, binder)) = parameter.mutex_authority_binding() else {
                continue;
            };
            let Some(actual) = selected.bindings.get(&formal).copied() else {
                return Ok(Err(resource_call_failure(&format!(
                    "call map omits mutex authority binder `{binder}`"
                ))));
            };
            let Some(fact) = caller_state.resolve_named_mutex_authority(actual) else {
                return Ok(Err(resource_call_failure(&format!(
                    "Requires owns mutex authority `{binder}`"
                ))));
            };
            entry_state = match entry_state.rebind_named_mutex_authority(actual, fact) {
                Ok(rebound) => rebound,
                Err(_) => {
                    return Ok(Err(resource_call_failure(&format!(
                        "transferred mutex authority `{binder}` is not the selected owned occurrence"
                    ))));
                }
            };
        }
    }
    let entry_contract_state = with_bound_contract_interface_argument_views(
        &entry_state,
        contract_interface,
        &argument_values,
    );
    // The callee's pure preconditions are read in the state its entry will
    // hold: the transferred clause set, opened through the composite
    // definitions the way the callee's own entry opens it. A precondition
    // that reads a cell a transferred composite owns (`requires node->left
    // != 0` beside `owns pair(node)`) is then justified by the clause set at
    // the call exactly as at the entry, instead of becoming a caller
    // obligation about a folded composite. The opened context is read here
    // only; the transfer itself keeps the folded heads.
    let precondition_state = if entry_contract_state
        .resources()
        .facts()
        .iter()
        .any(|fact| matches!(fact.resource(), Resource::Composite { .. }))
    {
        let definitions = contract_interface.composite_resource_definitions();
        let opened = {
            expand_all_composite_resource_facts_at_state(
                entry_contract_state.resources(),
                definitions,
                &entry_contract_state,
                &path_assumptions,
            )
        };
        opened
            .map(|opened| entry_contract_state.clone().with_resource_context(opened))
            .unwrap_or_else(|| entry_contract_state.clone())
    } else {
        entry_contract_state.clone()
    };
    let mut obligations = argument_obligations;
    // A call from inside an open update must restore the body before
    // another contract can observe it.
    for input in transfer
        .borrowed_inputs
        .iter()
        .chain(&transfer.consumed_inputs)
    {
        if let Resource::Composite { name, arguments } | Resource::Token { name, arguments } =
            input.fact.resource()
            && caller_state.population_body_is_open(name, arguments)
        {
            return Ok(Err(FunctionPath::new(FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                    "population body is open; pass explicit body pieces instead of population membership".into(),
                )), facts, obligations)));
        }
    }
    // Reuse an existing caller partition only for exact entry borrows.
    // Exposed callee pieces do not trigger another ownership inference here.
    {
        #[cfg(test)]
        let _fast =
            crate::kernel::search::FastOperationScope::enter("call entry composition retention");
        let _timing = crate::instrumentation::OperationTiming::new(
            application.name,
            "verified function rule application",
            "call entry composition retention",
        );
        let original_flat_partition = transfer.helper_call.is_none()
            && transfer.consumed_inputs.is_empty()
            && !transfer.borrowed_inputs.is_empty()
            && transfer.borrowed_inputs.iter().all(|input| {
                input.fact.memory_own_range().is_some()
                    && caller_state
                        .resources()
                        .contains_exact_representation(&input.fact)
            });
        if original_flat_partition {
            facts.push(ExecutionPureFact::new(Proposition::ResourceComposition(
                caller_state.resources().clone(),
            )));
        }
    }

    let mut established_requirements = Vec::new();
    let mut retained_requirements = Vec::new();
    let requirement_timing = crate::instrumentation::OperationTiming::new(
        application.name,
        "verified function rule application",
        "verified call requirement checking",
    );
    // Each requirement is checked under the call's path context plus every
    // obligation and requirement the earlier ones established. Build that
    // context once and extend it by what each requirement adds: rebuilding
    // it from the growing lists per requirement was quadratic in the
    // requirement count. The lists are sets of assumptions, so the order in
    // which later entries join them names the same context.
    let mut requirement_context =
        assumptions_with_path_context(&path_assumptions, &facts, &obligations);
    let mut assumed_obligations = obligations.len();
    let mut assumed_requirements = 0;
    for (requirement_ordinal, requirement) in
        contract_interface.contract_requires().iter().enumerate()
    {
        requirement_context = assumptions_with_path_context(
            &requirement_context,
            &[],
            &obligations[assumed_obligations..],
        );
        assumed_obligations = obligations.len();
        requirement_context = assumptions_with_propositions(
            &requirement_context,
            &established_requirements[assumed_requirements..],
        );
        assumed_requirements = established_requirements.len();
        let requirement_assumptions = &requirement_context;
        let lowering_assumptions = requirement_assumptions
            .clone()
            .allow_symbolic_contract_loads();
        let mut requirement_source: Option<std::sync::Arc<CallRequirementSource>> = None;
        let source_load_state = std::cell::Cell::new(None);
        let mut source_for_requirement = || {
            if let Some(source) = &requirement_source {
                return source.clone();
            }
            let site = call_requirement_site
                .get_or_insert_with(|| {
                    let mut site = CallRequirementSite::for_requirement(
                        application.name,
                        application.interface_name,
                        candidate_ordinal,
                        source_arguments,
                        &caller_state.memory,
                    );
                    site.value_arguments = contract_interface
                        .value_parameters()
                        .iter()
                        .zip(application_value_arguments)
                        .map(|(parameter, value)| (parameter.name().to_owned(), value.clone()))
                        .collect();
                    if let Some(selected) = resource_application {
                        site.resource_arguments = selected
                            .parameters
                            .iter()
                            .filter_map(|parameter| {
                                let identity = parameter.binding_identity()?;
                                let actual = selected.bindings.get(&identity)?;
                                Some((parameter.binding_name()?.to_owned(), identity, *actual))
                            })
                            .collect();
                    }
                    std::sync::Arc::new(site)
                })
                .clone();
            let source = std::sync::Arc::new(CallRequirementSource::new(
                site,
                requirement_ordinal,
                contract_interface
                    .contract_requirement_source(requirement_ordinal)
                    .unwrap_or(None),
                // The interface carries the checked source-map capability;
                // using it keeps this metadata body-independent for named
                // callbacks while matching concrete direct-call metadata.
                contract_interface
                    .contract_requirement_source(requirement_ordinal)
                    .is_some_and(|source_requirement_ordinal| {
                        source_requirement_ordinal.is_some()
                            && spec_proposition_is_state_independent(requirement)
                    }),
                source_load_state.get(),
            ));
            requirement_source = Some(source.clone());
            source
        };
        let requirement_paths = lower_spec_proposition_at_state_with_loop_entry(
            &precondition_state,
            requirement,
            Some(&precondition_state),
            &lowering_assumptions,
            budget,
        )?;
        let mut load_state = None;
        let mut load_state_consistent = true;
        for requirement_path in &requirement_paths {
            let Some(identity) = source_load_state_for_proposition(&requirement_path.proposition)?
            else {
                continue;
            };
            if load_state.is_some_and(|known| known != identity) {
                load_state_consistent = false;
            } else {
                load_state = Some(identity);
            }
        }
        if load_state_consistent {
            source_load_state.set(load_state);
        }
        if requirement_paths.is_empty() {
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_call_requirement_site(source_for_requirement())
                    .with_context(format!("{} precondition", application.name)),
            );
            continue;
        }
        for requirement_path in requirement_paths {
            let path_assumptions = assumptions_with_path_context(
                requirement_assumptions,
                &requirement_path.facts,
                &requirement_path.obligations,
            );
            for path_obligation in &requirement_path.obligations {
                // The guards this wrap inserts are the obligation's complete
                // recorded head chain: the path obligation under them is a
                // kernel load or overflow condition, which no written
                // connective introduced.
                let (guarded, guard_introductions) = wrap_path_context_with_introductions(
                    path_obligation.proposition().clone(),
                    &requirement_path.facts,
                    &[],
                );
                // Discharge is an exact route or an emitted obligation. A
                // guard the exact routes do not cover is emitted as a
                // required verification condition at the call step,
                // carrying the head chain recorded for it, for the proof
                // side to discharge. The kernel searches for no proof of it.
                // A load the precondition performs is authorized by the
                // clause set the callee receives: the opened transferred
                // context permits the read, so the condition is discharged
                // as it is at the callee's own entry. Only load-shaped
                // conditions are judged this way; the state check answers
                // nothing about any other proposition.
                let load_condition_is_justified = !assumptions.retains_required_obligations()
                    && loadability_obligation_shape(path_obligation.proposition())
                    && super::api::contract_certification::execution_state_justifies_loadability_obligation(
                        &precondition_state,
                        &guarded,
                        requirement_assumptions,
                    );
                if !assumptions.retains_required_obligations()
                    && (load_condition_is_justified
                        || required_obligation_is_exactly_discharged(
                            requirement_assumptions,
                            &guarded,
                        ))
                {
                    super::assumptions::record_consulted_premises(
                        requirement_assumptions,
                        &guarded,
                    );
                } else {
                    let call_requirement_site = source_for_requirement();
                    obligations.push(
                        ProofObligation::verification_condition(guarded.clone())
                            .with_introductions(guard_introductions)
                            .with_call_requirement_site(call_requirement_site.clone())
                            .with_context(format!("{} precondition", application.name)),
                    );
                }
                established_requirements.push(guarded);
            }
            // A concrete function's refinement of a named contract consults
            // no path fact, so it is decided even where every consulted fact
            // must be explicit: nothing on the proof side could prove it.
            let contract_requirement_is_proven = function_contract_requirement_is_proven(
                &requirement_path.proposition,
                &path_assumptions,
                environment,
                !assumptions.retains_required_obligations(),
                budget,
            )?;
            let requirement_is_proven = contract_requirement_is_proven
                || !assumptions.retains_required_obligations()
                    && super::assumptions::capture_implicit_consulted_premises(|| {
                        if contract_requirement_is_proven {
                            return true;
                        }
                        // Range bounds are the definition of this atomic source
                        // clause. User-written logical structure still needs its
                        // ordinary explicit proof rather than this unpacking.
                        if matches!(requirement, SpecProposition::ResourceSeparate { .. }) {
                            return separation_requirement_parts_are_established(
                                &path_assumptions,
                                &requirement_path.proposition,
                            );
                        }
                        match &requirement_path.proposition {
                            Proposition::ConditionIs(condition, value) => {
                                path_assumptions.proves_exact(&requirement_path.proposition)
                                    || path_assumptions
                                        .has_matching_condition_fact_for_memory_resolution(
                                            condition.native_compat(),
                                            *value,
                                        )
                            }
                            Proposition::ResourceSeparate { .. }
                                if requirement_path.proposition.memory_separation().is_some() =>
                            {
                                let (left, right) = requirement_path
                                    .proposition
                                    .memory_separation()
                                    .expect("the guard matched a memory separation");
                                path_assumptions.proves_exact(&requirement_path.proposition)
                                    || path_assumptions
                                        .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                                            left, right,
                                        )
                            }
                            proposition => path_assumptions.proves_exact(proposition),
                        }
                    });
            if requirement_is_proven {
                super::assumptions::record_consulted_premises(
                    &path_assumptions,
                    &requirement_path.proposition,
                );
            }
            // The guards this wrap inserts, then the head chain the
            // requirement's own lowering recorded. The record comes from the
            // lowering that produced the obligation, so an introduction on
            // it reaches a hidden guard exactly as on a lowered goal.
            let requirement_introductions = requirement_path.introductions;
            let (guarded_requirement, guards) = wrap_path_context_with_introductions(
                requirement_path.proposition,
                &requirement_path.facts,
                &requirement_path.obligations,
            );
            let mut introductions = guards;
            introductions.extend(requirement_introductions);
            if !requirement_is_proven {
                // Same rule as the guard above: exact routes, then an
                // emitted required verification condition. The general
                // prover decides no precondition.
                if !assumptions.retains_required_obligations()
                    && required_obligation_is_exactly_discharged(
                        requirement_assumptions,
                        &guarded_requirement,
                    )
                {
                    super::assumptions::record_consulted_premises(
                        requirement_assumptions,
                        &guarded_requirement,
                    );
                } else {
                    let call_requirement_site = source_for_requirement();
                    obligations.push(
                        ProofObligation::verification_condition(guarded_requirement.clone())
                            .with_introductions(introductions)
                            .with_call_requirement_site(call_requirement_site.clone())
                            .with_context(format!("{} precondition", application.name)),
                    );
                }
            }
            // The call-local context assumes earlier pending requirements.
            // Publishing evidence from that context would let a call prove
            // its own prerequisites. Only the incoming checked context can
            // independently establish an input fact for the continuation.
            // Prepared steps publish their input proof delta in the driver.
            // They must not rediscover or republish that evidence here.
            if !assumptions.retains_required_obligations()
                && super::reasoning::path_facts::call_input_fact_is_already_known(
                    assumptions,
                    &guarded_requirement,
                )
            {
                retained_requirements.push(guarded_requirement.clone());
            }
            established_requirements.push(guarded_requirement);
        }
    }
    // Publish only independently proved input evidence. Each proposition
    // keeps its pre-state reads and models; nothing is reevaluated here.
    facts.extend(
        retained_requirements
            .into_iter()
            .map(ExecutionPureFact::new),
    );
    drop(requirement_timing);

    // The callee is given each of its ranges' span guards on entry
    // (`program_function_contract_entry_facts`), among them `start <= end`. The
    // planner shows each range lies inside one the caller holds, which
    // gives every other guard from the held range's own, but not the order:
    // an inverted range `bytes[5..2]` lies inside `bytes[0..8]` by its
    // endpoints alone. So the caller proves the order here, under its path,
    // the arguments and the callee's established requirements.
    let guard_context = assumptions_with_propositions(
        &assumptions_with_path_context(
            &requirement_context,
            &[],
            &obligations[assumed_obligations..],
        ),
        &established_requirements[assumed_requirements..],
    );
    for fact in transfer.callee_resources.facts() {
        crate::instrumentation::record_deterministic_work(1);
        let Some(range) = fact.memory_view_range().or_else(|| fact.memory_own_range()) else {
            continue;
        };
        let order = match range.wide_bounds() {
            Some((start, end)) => ConditionTerm::uint64_less_equal(start.clone(), end.clone()),
            None => ConditionTerm::signed_less_equal(range.start().clone(), range.end().clone()),
        };
        match guard_context.decide(&order) {
            Some(true) => {}
            Some(false) => {
                return Ok(Err(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                        "`{}` would be handed a range that ends before it starts; its \
                             `views` and `owns` bounds have to be in order at this call",
                        application.name
                    ))),
                    facts,
                    obligations,
                )));
            }
            None => {
                let guard = Proposition::condition_is(order, true);
                if required_obligation_is_exactly_discharged(&guard_context, &guard) {
                    super::assumptions::record_consulted_premises(&guard_context, &guard);
                } else {
                    obligations.push(
                        ProofObligation::verification_condition(guard)
                            .with_context(format!("{} range bounds", application.name)),
                    );
                }
            }
        }
    }

    // Applicability is determined entirely at entry. In particular, pending
    // obligations must not be assumed to authorize this interface's effects
    // or make its guarantees available to another candidate.
    if require_established && obligations.len() != initial_obligation_count {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                "no callback contract has established preconditions".to_string(),
            )),
            facts,
            obligations,
        )));
    }

    // A self-call inside the certification of a function that declares an
    // expression `decreases` measure owes the descent, after the callee's
    // preconditions and read at the same state they were read at: the
    // callee's parameters hold this call's arguments there, and a measure
    // that reads memory sees the memory the callee will see. The obligations
    // are ordinary verification conditions on this path, so a proof that does
    // not discharge them does not get past the step, and an undischarged one
    // is a premise of the path theorem.
    //
    // The anchor names the function being certified and the other members
    // of its recursive component, and is installed only for that function,
    // so an ordinary call to another verified function is untouched, and so
    // is every function that declares no measure. It is placed after the
    // applicability gate above so a callback candidate is still selected by
    // its preconditions alone.
    if let Some(anchor) = environment.recursion_anchor()
        && anchor.ranks_call_to(application.name)
        && let Some(descent) = anchor.structural_resource.as_ref()
    {
        let passed = contract_interface
            .recursion_resource()
            .and_then(|index| contract_interface.resource_requires().get(index));
        let failure = if let Some(spec) = passed {
            match evaluate_function_resource_spec(
                &precondition_state,
                spec,
                &path_assumptions,
                budget,
            )? {
                Ok(fact) => descent.check(caller_state, &fact, &path_assumptions).err(),
                Err(_) => Some("the callee's resource measure could not be read"),
            }
        } else {
            Some("the callee declares no anonymous resource measure")
        };
        if let Some(failure) = failure {
            obligations.push(ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context(format!("{} structural recursion measure does not descend: the call to `{}` must receive a retained child witness of the entry resource: {failure}; unfold or observe its owned child before the call", anchor.function(), application.name)));
        }
    } else if let Some(anchor) = environment.recursion_anchor()
        && anchor.ranks_call_to(application.name)
        && let Some(entry) = anchor.structural_entry()
    {
        // A structural measure is ranked by the instance this call passes for
        // the callee's own measured binder: its model must be strictly
        // contained in the model the certified function's binder held at its
        // entry, through the arms this path's facts decide. The decision is
        // the loop back edge's, so nothing here proves by cases or unfolds.
        let failure = match contract_interface.recursion_binder() {
            None => Some(format!(
                "`{}` is in `{}`'s recursive component but declares no structural \
                 `decreases` binder; every member of a component ranked by structural \
                 binders must declare one",
                application.name,
                anchor.function()
            )),
            Some(binder) => {
                let passed = contract_interface
                    .resource_binder_identity(binder)
                    .and_then(|formal| {
                        resource_application.and_then(|call| call.bindings.get(&formal))
                    })
                    .and_then(|actual| caller_state.resources().owned_instance(*actual));
                match passed {
                    None => Some(format!(
                        "the call to `{}` passes no owned instance for its measured binder \
                         `{binder}`, so its structural descent cannot be ranked",
                        application.name
                    )),
                    Some(next) => crate::kernel::loops::structural_instance_descent_failure(
                        entry,
                        next,
                        &format!(
                            "{} recursion measure `decreases {binder}`",
                            anchor.function()
                        ),
                        &format!("the call to `{}` passes", application.name),
                        &format!("`{}` held at its entry", anchor.function()),
                        contract_interface.composite_resource_definitions(),
                        &path_assumptions,
                    ),
                }
            }
        };
        if let Some(message) = failure {
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_context(message),
            );
        }
    } else if let Some(anchor) = environment.recursion_anchor()
        && anchor.ranks_call_to(application.name)
    {
        // A self-call ranks the measure the anchor was derived from, so the
        // two states being compared are readings of one declared object. An
        // interface applied under this name that declares a different
        // measure is refused rather than ranked by the wrong one. A call to a
        // peer reads the peer's own declared measure, so the peer must
        // declare one; the descent below checks that its shape matches.
        let called_measure = contract_interface.recursion_measure();
        let mismatch = if anchor.function() == application.name {
            called_measure != Some(anchor.components())
        } else {
            called_measure.is_none()
        };
        if mismatch {
            let message = if anchor.function() == application.name {
                format!(
                    "the contract applied for the recursive call to `{}` declares a different \
                     `decreases` measure than the one being certified",
                    application.name
                )
            } else {
                format!(
                    "`{}` is in `{}`'s recursive component but declares no expression \
                     `decreases` measure; every member of a component ranked by expression \
                     measures must declare one, of the same shape",
                    application.name,
                    anchor.function()
                )
            };
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_context(message),
            );
        } else {
            // Stable-view recovery cannot use pending obligations as return
            // authority. Drop a ranking obligation only when the caller's
            // already-established facts discharge its exact proposition;
            // neither other pending requirements nor the ranking obligations
            // themselves may be treated as premises for that decision.
            let established_descent_assumptions =
                assumptions_with_path_context(assumptions, &facts, &[]);
            let descent_assumptions =
                assumptions_with_path_context(&path_assumptions, &facts, &obligations);
            match crate::kernel::termination::collect_recursion_descent_obligations(
                anchor,
                application.name,
                called_measure.unwrap_or_default(),
                &precondition_state,
                &descent_assumptions,
                budget,
            ) {
                Ok(descent) => obligations.extend(descent.into_iter().filter(|obligation| {
                    !required_obligation_is_exactly_discharged(
                        &established_descent_assumptions,
                        obligation.proposition(),
                    )
                })),
                // A measure with no value at the call state is a proof failure
                // at the call, never a silently skipped descent.
                Err(message) => obligations.push(
                    ProofObligation::verification_condition(false_equals_true_proposition())
                        .with_context(message),
                ),
            }
        }
    }

    let call_entry_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let effective_assumptions =
        assumptions_with_propositions(&call_entry_assumptions, &established_requirements)
            .transport_memory_load_condition_facts();

    if let Some(message) = call_initialization::uninitialized_call_input(
        &entry_contract_state.memory,
        contract_interface,
        transfer
            .borrowed_inputs
            .iter()
            .chain(&transfer.consumed_inputs),
        application.representation_copy.is_some(),
        &call_entry_assumptions,
    ) {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
            facts,
            obligations,
        )));
    }

    let footprint_state = entry_contract_state.clone();
    let footprint_timing = crate::instrumentation::OperationTiming::new(
        application.name,
        "verified function rule application",
        "verified call mutable footprint lowering",
    );
    // Reassemble the transition in source order from its role partitions.
    // This keeps the effect projection tied to the checked role-bearing
    // inputs rather than to a normalized context that erased source metadata.
    let mut checked_transition_inputs = transfer.borrowed_inputs.clone();
    checked_transition_inputs.extend(transfer.consumed_inputs.clone());
    checked_transition_inputs.sort_by_key(|checked| checked.clause_position);
    let projection = match project_contract_memory_effects(
        &footprint_state,
        contract_interface,
        Some(&checked_transition_inputs),
        &effective_assumptions,
        budget,
    )? {
        Ok(projection) => projection,
        Err(message) => {
            return Ok(Err(FunctionPath::new(
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                    "could not evaluate mutable footprint: {message}"
                ))),
                facts,
                obligations,
            )));
        }
    };
    // The joint transfer planner has already proved that every mutable input
    // is disjoint from each lent range. Preserve that precise footprint here;
    // rejecting all mutation would also reject the supported viewed-field /
    // owned-field partition.
    let mutable_ranges = projection.ranges;
    if let Some(error) = mutable_ranges.iter().find_map(|range| {
        super::mutexes::storage_write_refusal(caller_state, range, &effective_assumptions)
    }) {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(error),
            facts,
            obligations,
        )));
    }
    let projection_range_sources = projection.range_sources;
    {
        // Compare the effects against the complete checked view frontier, not
        // just the views whose requirement is a plain memory range. A
        // composite view's bytes are its checked one-level pieces, and the
        // intrinsic and empty-composite views never reach the planner at
        // all; the transfer carries both groups for exactly this check.
        //
        // The pair is read by reservation support first. A valid resource context is a
        // partition, so an effect reserved out of one owned occurrence and a
        // view lent from a different one are bytewise disjoint by
        // construction; asking the arithmetic oracle about two symbolic
        // ranges it cannot order would refuse what the caller's own partition
        // already settles. Only an effect and a view drawn from the *same*
        // occurrence -- a partial borrow of one owner (D8) -- still need the
        // arithmetic proof, and a range with no support on either side
        // always does.
        let reserved_effect_supports = transfer
            .stable_view_plan
            .as_ref()
            .map(|plan| {
                reserved_effect_support_index(
                    &projection_range_sources,
                    &plan.reserved_ownership_supports,
                )
            })
            .unwrap_or_default();
        let viewed_ranges = transfer
            .stable_view_plan
            .as_ref()
            .map(StableViewTransferPlan::stable_views)
            .unwrap_or_default()
            .iter()
            .filter_map(|stable_view| {
                Some((
                    stable_view.requirement.fact.memory_range()?,
                    Some(stable_view.support),
                ))
            })
            .chain(
                transfer
                    .checked_view_frontier
                    .iter()
                    .map(|(range, support)| (range, *support)),
            );
        for (viewed_range, viewed_support) in viewed_ranges {
            if let Some((mutable_range, relation)) = mutable_ranges
                .iter()
                .filter(|mutable_range| {
                    !effect_is_disjoint_from_view_by_support(
                        &reserved_effect_supports,
                        mutable_range,
                        viewed_support,
                    )
                })
                .map(|mutable_range| {
                    (
                        mutable_range,
                        candidate_memory_ranges_relation(
                            mutable_range,
                            viewed_range,
                            &effective_assumptions,
                        ),
                    )
                })
                .find(|(_, relation)| *relation != CandidateMemoryRangeRelation::Disjoint)
            {
                let subject = LoanRefusalSubject::with_range(mutable_range.clone());
                let diagnostic = match relation {
                    CandidateMemoryRangeRelation::Overlap => LoanRefusal::ActiveDependency
                        .proven_overlap_diagnostic(LoanRefusalOperation::MemoryAccess, subject),
                    CandidateMemoryRangeRelation::SeparationUnproved => {
                        LoanRefusal::UnsupportedPartition
                            .diagnostic_with_subject(LoanRefusalOperation::MemoryAccess, subject)
                    }
                    CandidateMemoryRangeRelation::Disjoint => unreachable!(),
                };
                return Ok(Err(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::LoanRefusal(Box::new(diagnostic))),
                    facts,
                    obligations,
                )));
            }
        }
    }
    for fact in projection.evidence_facts {
        if !facts.contains(&fact) {
            facts.push(fact);
        }
    }
    drop(footprint_timing);
    // The projection above is also retained on the transition record below;
    // no later call path reconstructs the footprint from source clauses.
    let mut transfer = transfer;
    transfer.consumed_cell_returns.retain_frontier(
        projection_range_sources
            .iter()
            .map(|(range, _)| range.clone()),
        &effective_assumptions,
    );
    if caller_state.resources().structural_witnesses.is_some() {
        for input in transfer
            .borrowed_inputs
            .iter()
            .chain(&transfer.consumed_inputs)
        {
            transfer
                .caller_resources_after_requirements
                .retire_owned_structural_input(
                    caller_state.resources(),
                    &input.fact,
                    &path_assumptions,
                );
        }
    }
    let has_exact_write_ranges = if contract_interface.resource_derived_mutable_frame() {
        projection_range_sources
            .iter()
            .all(|(_, source)| source.memory_own_range().is_some())
    } else {
        contract_interface
            .contract_mutable()
            .iter()
            .all(|segment| segment.guard().is_none())
    };
    transfer.memory_effects = mutable_ranges.clone();
    // A resource-derived call is authorized by exactly these checked inputs,
    // borrowed and consumed alike: its write set is projected from them
    // above and from nothing else, so they bound its footprint. A produced
    // output is not an input and does not widen it. Keep them opaque; do not
    // enumerate a recursive body.
    if contract_interface.resource_derived_mutable_frame()
        && !contract_interface.resource_derived_frame_mixed()
    {
        // The transfer already selected the caller's equivalent owner. Use
        // that recorded spelling, rather than retaining a callee parameter or
        // a read expression whose value can change across this call.
        let canonical: BTreeMap<_, _> = transfer
            .canonical_borrowed_owners
            .iter()
            .map(|(checked, caller)| (checked, caller))
            .collect();
        let mut bound = None;
        for input in &checked_transition_inputs {
            let selected = canonical.get(&input.fact).copied().unwrap_or(&input.fact);
            if let ResourceFact::Own(resource, quantity) = selected {
                if quantity.as_const() != Some(1) {
                    bound = None;
                    break;
                }
                crate::instrumentation::record_deterministic_work(1);
                bound = Some(match bound {
                    None => resource.clone(),
                    Some(previous) => Resource::star(previous, resource.clone()),
                });
            }
        }
        transfer.resource_effect_bound = bound;
    }

    // A direct store into read-only storage is rejected where it is
    // executed, but a modular call performs its writes abstractly through
    // this footprint. Without the same check, passing read-only storage to
    // a callee that declares it mutable would let the call store there:
    // string-literal bytes are the reachable case, since C models a
    // literal as an ordinary `uint8*` and no qualifier catches it.
    if let Some(range) = mutable_ranges
        .iter()
        .find(|range| entry_state.memory.is_read_only_block(&range.base().base))
    {
        return Ok(Err(FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                "mutable footprint covers read-only storage `{}`",
                range.base().base
            ))),
            facts,
            obligations,
        )));
    }

    Ok(Ok(PreparedVerifiedFunctionCall {
        name: application.name,
        interface_name: application.interface_name,
        candidate_ordinal,
        has_exact_write_ranges,
        storage: application.storage,
        evidence: application.evidence,
        framed_rule: application.framed_rule,
        interface: contract_interface,
        argument_values,
        entry_state,
        entry_contract_state,
        transfer,
        facts,
        obligations,
        effective_assumptions,
        bindings: resource_application.map(|application| application.bindings.clone()),
    }))
}

/// An instantiated nominal interface together with the premise that grants
/// it for this function value. Only fact lookup constructs this capability;
/// a bare `FunctionContract` declaration has no frame-rule authority.
#[derive(Clone, Debug)]
pub(super) struct EstablishedFunctionContract {
    contract: FunctionContract,
    _premise: Proposition,
}

impl std::ops::Deref for EstablishedFunctionContract {
    type Target = FunctionContract;
    fn deref(&self) -> &Self::Target {
        &self.contract
    }
}

#[derive(Clone, Copy)]
struct NamedContractApplication<'a> {
    contract: &'a FunctionContract,
    framed_rule: Option<FramedCallRule<'a>>,
}

impl std::ops::Deref for NamedContractApplication<'_> {
    type Target = FunctionContract;
    fn deref(&self) -> &Self::Target {
        self.contract
    }
}

/// The contracts facts attach to a function value, each with the values
/// its fact fixes for its value parameters, that apply to a call of type
/// `function_type`. A fact whose values do not have its contract's value
/// parameter types contributes nothing.
pub(super) fn contracts_for_pointer(
    pointer: &Address,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    function_type: &ProgramType,
) -> Vec<EstablishedFunctionContract> {
    assumptions
        .function_contract_facts_for(pointer)
        .filter_map(|(name, fact)| {
            let contract = environment.get_function_contract(&name)?;
            let Proposition::Predicate { arguments, .. } = &fact else {
                return None;
            };
            let values = arguments
                .iter()
                .skip(2)
                .map(|argument| match argument {
                    Term::ProgramValue(value) => Some(value.clone()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?;
            Some(EstablishedFunctionContract {
                contract: contract.instantiated(&values)?,
                _premise: fact,
            })
        })
        .filter(|contract| &contract.function_pointer_type() == function_type)
        .collect()
}

pub(super) fn execute_program_function_contracts_paths(
    caller_state: &ExecutionState,
    contracts: &[&EstablishedFunctionContract],
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<FunctionPath>> {
    let applications = contracts
        .iter()
        .map(|contract| NamedContractApplication {
            contract,
            framed_rule: Some(FramedCallRule::Named { _rule: contract }),
        })
        .collect::<Vec<_>>();
    execute_named_contract_applications_paths(
        caller_state,
        &applications,
        arguments,
        assumptions,
        environment,
        budget,
    )
}

fn execute_named_contract_applications_paths(
    caller_state: &ExecutionState,
    contracts: &[NamedContractApplication<'_>],
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<FunctionPath>> {
    let selected = environment.selected_call_contract.as_deref();
    let contracts = contracts
        .iter()
        .copied()
        .filter(|contract| {
            contract.proof_parameters().is_empty() || selected == Some(contract.name())
        })
        .collect::<Vec<_>>();
    if contracts.is_empty() {
        return Ok(vec![resource_call_failure(
            "resource contract requires explicit proof arguments",
        )]);
    }
    let selected_index = selected.and_then(|name| {
        contracts
            .iter()
            .position(|contract| contract.name() == name)
    });
    if selected.is_some() && selected_index.is_none() {
        return Ok(vec![resource_call_failure(
            "selected contract is not available at this call",
        )]);
    }
    let resource_application = if let Some(index) = selected_index {
        let contract = contracts[index];
        if let Some(transport) = environment
            .selected_call_binders
            .as_ref()
            .filter(|transport| transport.names_call_to(contract.name()))
        {
            if transport.arity != arguments.len() {
                return Ok(vec![resource_call_failure(
                    "selected contract call arity mismatch",
                )]);
            }
            match selected_call_binder_application(
                contract.name(),
                contract.interface(),
                caller_state,
                environment,
                None,
            ) {
                Ok(application) => application,
                Err(message) => return Ok(vec![resource_call_failure(message)]),
            }
        } else {
            let arguments = environment
                .selected_call_resource_arguments
                .as_deref()
                .unwrap_or(&[]);
            if arguments.len() != contract.proof_parameters().len() {
                return Ok(vec![resource_call_failure(
                    "resource contract proof argument arity mismatch",
                )]);
            }
            let mut bindings = BTreeMap::new();
            for (parameter, argument) in contract.proof_parameters().iter().zip(arguments) {
                let Some(identity) = parameter.instance_identity() else {
                    return Ok(vec![resource_call_failure(
                        "resource proof parameter must be an exclusive instance",
                    )]);
                };
                if bindings.insert(identity, *argument).is_some() {
                    return Ok(vec![resource_call_failure(
                        "duplicate exclusive resource proof argument",
                    )]);
                }
            }
            match ResourceCallApplication::bind(
                contract.proof_parameters().to_vec(),
                std::sync::Arc::new(bindings),
                caller_state,
            ) {
                Ok(application) => Some(application),
                Err(message) => return Ok(vec![resource_call_failure(message)]),
            }
        }
    } else {
        None
    };
    let applications = contracts
        .iter()
        .map(|application| {
            let contract = application.contract;
            FunctionContractApplication {
                pointer_result: None,
                name: contract.callee_name(),
                interface_name: contract.name(),
                interface: contract.interface(),
                storage: None,
                evidence: None,
                framed_rule: application.framed_rule,
                representation_copy: None,
                value_arguments: contract.value_arguments(),
            }
        })
        .collect::<Vec<_>>();
    execute_verified_function_applications(
        caller_state,
        &applications,
        selected_index,
        selected_index.zip(resource_application.as_ref()),
        arguments,
        assumptions,
        environment,
        budget,
    )
}

#[derive(Debug)]
struct ResourceCallApplication {
    parameters: std::sync::Arc<[ResourceSpec]>,
    bindings: std::sync::Arc<BTreeMap<Variable, Variable>>,
}

impl ResourceCallApplication {
    /// The one checked binding of a callee's instance binders to the caller's
    /// instances, whether the proof wrote a direct call map
    /// (`step(callee, { binder: instance })`) or a named contract's
    /// handle map (`step(Contract, { handle: instance })`). Each bound
    /// parameter must be an exclusive instance the caller owns now, and no
    /// instance may supply two parameters. The surface refuses both mistakes
    /// with source positions; the kernel refuses them here regardless, so a
    /// transport it did not see cannot bind what the proof state lacks. A
    /// binder the map omits is refused by the application engine, which
    /// checks completeness against the interface.
    fn bind(
        parameters: Vec<ResourceSpec>,
        bindings: std::sync::Arc<BTreeMap<Variable, Variable>>,
        caller_state: &ExecutionState,
    ) -> Result<Self, &'static str> {
        let mut actuals = BTreeSet::new();
        for parameter in &parameters {
            crate::instrumentation::record_deterministic_work(1);
            let Some(identity) = parameter.binding_identity() else {
                return Err("resource proof parameter must be an exclusive instance");
            };
            let Some(actual) = bindings.get(&identity) else {
                continue;
            };
            let owned = if parameter.mutex_authority_binding().is_some() {
                caller_state
                    .resolve_named_mutex_authority(*actual)
                    .is_some()
            } else {
                caller_state.owned_resource_instance(*actual).is_some()
            };
            if !owned {
                return Err("resource proof argument is not owned");
            }
            if !actuals.insert(*actual) {
                return Err("duplicate exclusive resource proof argument");
            }
        }
        Ok(Self {
            parameters: parameters.into(),
            bindings,
        })
    }
}

/// Whether an obligation is a load condition, possibly under the premises a
/// lowering path recorded: the only shape the opened-clause-set discharge of
/// a call precondition applies to.
fn loadability_obligation_shape(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::MemoryLoadable { .. } | Proposition::MemoryReadDefined { .. } => true,
        Proposition::Implies(_, body) => loadability_obligation_shape(body),
        Proposition::And(left, right) => {
            loadability_obligation_shape(left) && loadability_obligation_shape(right)
        }
        _ => false,
    }
}

/// The values of a function contract's value parameters at one call.
///
/// A parameter the proof's call map names takes the value it gives. Any
/// other takes its argument from the one instance the caller holds, owned
/// or viewed, that agrees with every other argument of the clause the
/// parameter appears in: `views cstr_at(s, n)` takes `n` from
/// `cstr_at(src, k)` when `s` is `src`. No instance, or two that differ at
/// the parameter, is a refusal naming the parameter; the proof can then name
/// the value. The held lookup is the indexed candidate query by the clause's
/// family and first pointer, so it reads only the caller's instances of that
/// resource. A named value grants nothing: the call still requires the
/// clause at it.
fn call_value_arguments(
    function: &str,
    interface: &FunctionContractInterface,
    caller_state: &ExecutionState,
    entry_state: &ExecutionState,
    environment: &ExecutionEnvironment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<ProgramValue>, String>> {
    let parameters = interface.value_parameters();
    let selected = environment
        .selected_call_value_arguments
        .as_ref()
        .filter(|selected| selected.0 == function)
        .map(|selected| selected.1.as_slice())
        .unwrap_or(&[]);
    // The clauses are evaluated with each parameter at a placeholder: the
    // probe only selects candidates, and a parameter position is never
    // compared.
    let mut probe_state = entry_state.clone();
    let placeholders = parameters
        .iter()
        .map(|parameter| symbolic_call_result(parameter.program_type(), Variable(0)))
        .collect::<Vec<_>>();
    super::api::bind_contract_value_parameters(&mut probe_state, parameters, &placeholders);
    let mut values = Vec::with_capacity(parameters.len());
    for parameter in parameters {
        crate::instrumentation::record_deterministic_work(1);
        // A map entry gives its parameter's value; the call then requires
        // the parameter's clause at it.
        if let Some((_, value)) = selected
            .iter()
            .find(|(written, _)| written == parameter.name())
        {
            if value.program_type() != parameter.program_type() {
                return Ok(Err(format!(
                    "call to `{function}`: the call map gives `{}` a `{}` value; it takes a `{}`",
                    parameter.name(),
                    named_contract_refinement::program_type_spelling(value.program_type()),
                    named_contract_refinement::program_type_spelling(parameter.program_type())
                )));
            }
            values.push(value.clone());
            continue;
        }
        let is_parameter = |argument: &ProgramExpression| {
            matches!(argument, ProgramExpression::Variable(name)
                if parameters.iter().any(|parameter| parameter.binding_name() == name))
        };
        let clause = interface.resource_requires().iter().find_map(|spec| {
            match spec.term() {
            ResourceTerm::Composite {
                name,
                arguments,
                argument_state_sources,
                parameter_types,
            } => arguments
                .iter()
                .position(|argument| {
                    matches!(argument, ProgramExpression::Variable(name) if name == parameter.binding_name())
                })
                .map(|position| {
                    (spec, name, arguments, argument_state_sources, parameter_types, position)
                }),
            _ => None,
        }
        });
        let Some((spec, name, arguments, argument_state_sources, parameter_types, position)) =
            clause
        else {
            return Ok(Err(format!(
                "call to `{function}` needs a value for `{}`, which no resource clause selects",
                parameter.name()
            )));
        };
        let probe = match evaluate_function_declared_resource_spec(
            &probe_state,
            &probe_state,
            spec.access(),
            ResourceFamily::Composite,
            name,
            arguments,
            argument_state_sources,
            parameter_types,
            spec.source_arguments(),
            &BTreeMap::new(),
            assumptions,
            budget,
        )? {
            Ok(fact) => fact,
            Err(_) => {
                return Ok(Err(format!(
                    "call to `{function}` could not evaluate the `{name}` clause that selects `{}`",
                    parameter.name()
                )));
            }
        };
        let Resource::Composite {
            arguments: probe_arguments,
            ..
        } = probe.resource()
        else {
            continue;
        };
        let agrees = |left: ResourceFieldValue<'_>, right: ResourceFieldValue<'_>| match (
            left.as_program_value(),
            right.as_program_value(),
        ) {
            (Some(ProgramValue::Pointer(left)), Some(ProgramValue::Pointer(right))) => {
                left.address() == right.address()
            }
            _ => left == right,
        };
        let matching_values = |candidates: &mut dyn Iterator<Item = &ResourceFact>| {
            let mut found: Vec<ProgramValue> = Vec::new();
            for candidate in candidates {
                crate::instrumentation::record_deterministic_work(1);
                let Resource::Composite {
                    name: held,
                    arguments: held_arguments,
                } = candidate.resource()
                else {
                    continue;
                };
                if held != name
                    || held_arguments.len() != probe_arguments.len()
                    || !arguments
                        .iter()
                        .zip(probe_arguments.iter().zip(held_arguments.iter()))
                        .all(|(argument, (probe, held))| {
                            is_parameter(argument) || agrees(probe, held)
                        })
                {
                    continue;
                }
                let Some(value) = held_arguments
                    .get(position)
                    .and_then(ResourceFieldValue::as_program_value)
                else {
                    continue;
                };
                if !found.contains(value) {
                    found.push(value.clone());
                }
            }
            found
        };
        let mut found = matching_values(
            &mut caller_state
                .resources()
                .direct_match_candidates_for(&probe, assumptions)
                .into_iter(),
        );
        if found.is_empty()
            && let Some(definition) = interface.composite_resource_definition(name)
        {
            found = string_literal_instance_values(
                definition,
                &(probe_arguments).native_values(),
                position,
                parameter.program_type(),
                caller_state,
                assumptions,
                budget,
            )?;
        }
        // The step that gives the value names the function as the sidecar
        // writes it: the C name of a formatted-output function or the
        // unqualified spelling of a translation-unit-local helper.
        let written = crate::languages::c::formatted_output::function_format(function)
            .map(|(output, _)| output.source_name())
            .unwrap_or_else(|| {
                ["#inline:", "#file-static:"]
                    .iter()
                    .find_map(|suffix| function.split_once(suffix).map(|(source, _)| source))
                    .unwrap_or(function)
            });
        match found.as_slice() {
            [value] => values.push(value.clone()),
            [] => {
                return Ok(Err(format!(
                    "call to `{function}` needs a held `{name}` instance to give `{0}` its value; the caller holds none that matches its other arguments; or give the value with `step({written}, {{ {0}: value }})`",
                    parameter.name()
                )));
            }
            _ => {
                return Ok(Err(format!(
                    "call to `{function}` cannot choose `{0}`: the caller holds {1} `{name}` instances that match; give the value with `step({written}, {{ {0}: value }})`",
                    parameter.name(),
                    found.len()
                )));
            }
        }
    }
    Ok(Ok(values))
}

fn resource_call_failure(message: &str) -> FunctionPath {
    FunctionPath::new(
        FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(message.into())),
        vec![].into(),
        vec![],
    )
}

/// Unpack an atomic separation clause's bounds against the same caller facts,
/// without assuming any sibling. This checks the definition of separation;
/// it is not used to discharge user-written conjunctions automatically.
fn separation_requirement_parts_are_established(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    match proposition {
        Proposition::And(left, right) => {
            separation_requirement_parts_are_established(assumptions, left)
                && separation_requirement_parts_are_established(assumptions, right)
        }
        Proposition::ConditionIs(condition, value) => {
            required_obligation_is_exactly_discharged(assumptions, proposition)
                || assumptions.has_matching_condition_fact_for_memory_resolution(
                    condition.native_compat(),
                    *value,
                )
        }
        Proposition::ResourceSeparate { .. } if proposition.memory_separation().is_some() => {
            let (left, right) = proposition
                .memory_separation()
                .expect("the guard matched a memory separation");
            required_obligation_is_exactly_discharged(assumptions, proposition)
                || assumptions
                    .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                        left, right,
                    )
        }
        _ => assumptions.proves_exact(proposition),
    }
}

/// Whether a named-contract requirement holds by the refinement check.
/// With `consult_facts` false, only an argument that is itself the address
/// of a function is decided: the judgment then reads the two declarations
/// the call names and no path fact, so a step that must make every consulted
/// fact explicit can still take it. A pointer known to be a function only
/// through facts is left to those facts' explicit route.
fn function_contract_requirement_is_proven(
    proposition: &Proposition,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    consult_facts: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    match proposition {
        Proposition::And(left, right) => Ok(function_contract_requirement_is_proven(
            left,
            assumptions,
            environment,
            consult_facts,
            budget,
        )? && function_contract_requirement_is_proven(
            right,
            assumptions,
            environment,
            consult_facts,
            budget,
        )?),
        Proposition::Predicate { name, arguments } => {
            let Some(contract_name) = FunctionContract::surface_name_from_predicate(name) else {
                return Ok(false);
            };
            let [
                Term::ExecutionState(_),
                term_source_0 @ Term::ProgramValue(_),
                values @ ..,
            ] = arguments.as_slice()
            else {
                return Ok(false);
            };
            let (Some(ProgramValue::Pointer(pointer)),) = (term_source_0.program_value_native(),)
            else {
                return Ok(false);
            };
            // Contract formation checks the complete value's graph class.
            // The lowered requirement keeps its structural read; it need not
            // contain the literal function that the read is known to equal.
            let comparison_pointer = if consult_facts {
                assumptions
                    .equality_graph
                    .pointer_value_representative(pointer)
            } else {
                pointer.clone()
            };
            let target = match comparison_pointer.address() {
                Address {
                    base: AddressBase::Function(target),
                    offset: AddressOffset::Constant(0),
                } => Some(target),
                Address {
                    base: AddressBase::FunctionSymbolic(_) | AddressBase::LoadedPointer(_),
                    offset: AddressOffset::Constant(0),
                } if matches!(pointer.program_type(), ProgramType::FunctionPointer(_)) => None,
                _ => return Ok(false),
            };
            // The fact's values fix the contract's value parameters for the
            // refinement check.
            let Some(values) = values
                .iter()
                .map(|value| match value {
                    Term::ProgramValue(value) => Some(value.clone()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(false);
            };
            let Some(contract) = environment
                .get_function_contract(contract_name)
                .and_then(|contract| contract.instantiated(&values))
            else {
                return Ok(false);
            };
            let contract = &contract;
            if pointer.program_type() != contract.function_pointer_type() {
                return Ok(false);
            }
            // A function value known only by the contracts its facts attach
            // has those contracts as its implementations: a closure instance
            // carries its own contract, fixed to its captured values.
            let Some(target) = target else {
                if !consult_facts {
                    return Ok(false);
                }
                for source in contracts_for_pointer(
                    pointer.address(),
                    assumptions,
                    environment,
                    &pointer.program_type(),
                ) {
                    if contract_refines_contract(contract, &source, assumptions, budget)? {
                        return Ok(true);
                    }
                }
                return Ok(false);
            };
            if let Some(rule) = environment.get_verified_function_rule(target) {
                return function_refines_named_contract(
                    contract,
                    &rule.function,
                    rule.function
                        .contract_interface()
                        .object_type_requirements(),
                    budget,
                );
            }
            let Some(rule) = environment.get_external_function_rule(target) else {
                return Ok(false);
            };
            function_refines_named_contract(
                contract,
                &rule.function,
                rule.function
                    .contract_interface()
                    .object_type_requirements(),
                budget,
            )
        }
        _ => Ok(false),
    }
}

mod named_contract_refinement;
pub(crate) use named_contract_refinement::*;

/// One write to file-scope or static storage that no owned range covers: a
/// store of `bytes` at `pointer`, or a summarized range a callee may write.
/// The surface spells it in source terms.
#[derive(Clone, Debug)]
pub(crate) enum StorageWriteOutsideFootprint {
    Write { pointer: Address, bytes: u32 },
    Range(MemoryRange),
}

/// Writes to file-scope or static storage that a checked path performs outside
/// the contract's owned footprint, for diagnostics. The caller
/// passes the checked resource facts and, for resource-derived contracts, the
/// already prepared projection from certification; this keeps the storage
/// decision on the same transition artifact as modular effects. `None` is
/// retained for explicit-effect callers. Caller memory reached through a
/// pointer is checked by the resource transition at each store; storage is
/// not external memory, so a contract that declares resources but no effect
/// clause is framed here instead: its storage writes must lie inside the owned
/// ranges (startup resources, owned raw ranges, and composite bodies).
pub(crate) fn storage_writes_outside_owned_footprint(
    contract: &ProgramFunction,
    entry: &ExecutionState,
    facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
    transition_resources: Option<&[CheckedResourceFact]>,
    prepared_projection: Option<&FunctionMemoryEffectProjection>,
) -> ExecutionResult<Option<Vec<StorageWriteOutsideFootprint>>> {
    let is_storage = |pointer: &Address| pointer.base.is_static_storage_block();
    let storage_writes: Vec<(Address, u32)> =
        crate::kernel::reasoning::memory_effect_write_accesses(facts)
            .into_iter()
            .filter(|(pointer, _)| is_storage(pointer))
            .collect();
    let storage_summaries: Vec<&MemoryRange> = facts
        .fact_iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::MemoryEffectSummary { mutable_ranges, .. } => Some(mutable_ranges),
            _ => None,
        })
        .flatten()
        .filter(|range| is_storage(range.base()))
        .collect();
    // Most contracts never touch storage; do not evaluate their owned
    // footprint at all.
    if storage_writes.is_empty() && storage_summaries.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let owned = if let Some(projection) = prepared_projection {
        projection.ranges().to_vec()
    } else {
        let mut budget = ExecutionBudget::beside_live_state();
        match project_contract_memory_effects(
            entry,
            contract.contract_interface(),
            transition_resources,
            assumptions,
            &mut budget,
        )? {
            Ok(projection) => projection.ranges().to_vec(),
            Err(_) => return Ok(None),
        }
    };
    let mut outside = Vec::new();
    for (pointer, write_bytes) in &storage_writes {
        if !storage_write_within_owned_footprint(pointer, *write_bytes, &owned, assumptions) {
            outside.push(StorageWriteOutsideFootprint::Write {
                pointer: pointer.clone(),
                bytes: *write_bytes,
            });
        }
    }
    // Most writes fit one declared range. Build the indexed union only when
    // a summary crosses adjacent owned fields; it grants no new resources.
    let joined_owned = std::cell::OnceCell::new();
    for range in storage_summaries {
        if !owned.iter().any(|parent| {
            super::assumptions::memory_range_shallowly_contained_with_facts(
                range,
                parent,
                assumptions,
            )
        }) && !joined_owned
            .get_or_init(|| {
                ResourceContext::new()
                    .unchecked_with_facts(owned.iter().cloned().map(ResourceFact::own_memory))
            })
            .satisfies_fact(&ResourceFact::own_memory(range.clone()), assumptions)
        {
            outside.push(StorageWriteOutsideFootprint::Range(range.clone()));
        }
    }
    Ok(Some(outside))
}

fn storage_write_within_owned_footprint(
    pointer: &Address,
    write_bytes: u32,
    owned: &[MemoryRange],
    assumptions: &PureFactContext,
) -> bool {
    let write = MemoryRange::new_with_element_width(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(write_bytes),
        1,
    );
    owned.iter().any(|range| {
        // A wide range has no 32-bit byte footprint; it is read in its own
        // element coordinates only.
        if range.wide_bounds().is_some() {
            return storage_write_within_owned_elements(pointer, write_bytes, range, assumptions);
        }
        let (base, bytes) = range.byte_footprint();
        let owned_bytes =
            MemoryRange::new_with_element_width(base, MachineTerm::constant(0), bytes, 1);
        super::assumptions::memory_range_shallowly_contained_with_facts(
            &write,
            &owned_bytes,
            assumptions,
        ) || storage_write_within_owned_elements(pointer, write_bytes, range, assumptions)
    })
}

/// Whether a write of `write_bytes` at `pointer` lies inside `range`, read in
/// the range's own element coordinates: `buf + 4 * j` is element `j` of an
/// `int32` range over `buf`, and it is inside `buf[s..e]` exactly when
/// `s <= j` and `j < e`.
///
/// The byte comparison beside it needs a constant distance between the two
/// addresses, so a symbolic index is never placed by it. Here the distance is
/// [`ExactElementDelta`]: the one symbolic index sign-extended plus an exact
/// `i64` constant, which is what the pointer offset denotes. The written
/// elements are `[index + c, index + c + k)` for `k = write_bytes / width`,
/// and each endpoint comparison is posed only in a form whose int32 reading is
/// the exact one: against constant endpoints as `s - c <= index` and
/// `index < e - c - (k - 1)`, the constants computed in `i64`, and against
/// symbolic endpoints only with `c = 0`, as `s <= index` and
/// `index + (k - 1) < e` with that addition proved not to overflow. A write that
/// does not cover whole elements, or any other shape, is left to the byte
/// comparison.
fn storage_write_within_owned_elements(
    pointer: &Address,
    write_bytes: u32,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    let width = range.element_width();
    if width == 0 || write_bytes == 0 || !write_bytes.is_multiple_of(width) {
        return false;
    }
    // One whole element at an unsigned 64-bit index. A wide range has its
    // one membership rule. A range with nonnegative constant bounds takes
    // such an index too: the bounds are the same numbers in either reading,
    // and they keep the index's byte offset exact.
    if write_bytes == width {
        if range.wide_bounds().is_some() {
            return assumptions.pointer_access_in_wide_range(pointer, width, range);
        }
        if let (Some(start), Some(end)) =
            (range.signed_constant_start(), range.signed_constant_end())
            && let (Ok(start), Ok(end)) = (u64::try_from(start), u64::try_from(end))
            && let Some(index) = pointer.shared_wide_element_index_from_base(range.base(), width)
            && index.operand_view().uint64_constant().is_none()
        {
            let holds = |condition: ConditionTerm| assumptions.decide(&condition) == Some(true);
            if (start == 0
                || holds(crate::kernel::assumptions::wide_index_comparison(
                    CompareRelation::LessEqual,
                    MachineOperandView::Legacy(&MachineTerm::uint64_constant(start)),
                    index.operand_view(),
                )))
                && holds(crate::kernel::assumptions::wide_index_comparison(
                    CompareRelation::LessThan,
                    index.operand_view(),
                    MachineOperandView::Legacy(&MachineTerm::uint64_constant(end)),
                ))
            {
                return true;
            }
        }
    }
    if range.wide_bounds().is_some() {
        return false;
    }
    let Some(delta) = pointer.exact_element_delta_from_base(range.base(), width, Some(assumptions))
    else {
        return false;
    };
    let elements = i64::from(write_bytes / width);
    let index = delta.index.clone();
    let holds = |condition: ConditionTerm| assumptions.decide(&condition) == Some(true);
    // `constant <= index` (lower) or `index < constant` (upper), for a
    // constant computed exactly: a constant outside the int32 range is
    // decided by the range itself.
    let index_at_least = |bound: i64| match i32::try_from(bound) {
        Ok(bound) => holds(crate::kernel::assumptions::index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&MachineTerm::constant(bound as u32)),
            index.operand_view(),
        )),
        Err(_) => bound < i64::from(i32::MIN),
    };
    let index_below = |bound: i64| match i32::try_from(bound) {
        Ok(bound) => holds(crate::kernel::assumptions::index_comparison(
            CompareRelation::LessThan,
            index.operand_view(),
            MachineOperandView::Legacy(&MachineTerm::constant(bound as u32)),
        )),
        Err(_) => bound > i64::from(i32::MAX),
    };
    let start = range.signed_constant_start();
    let end = range.signed_constant_end();
    let lower = match start {
        Some(start) => start
            .checked_sub(delta.constant)
            .is_some_and(index_at_least),
        None => {
            delta.constant == 0
                && holds(crate::kernel::assumptions::index_comparison(
                    CompareRelation::LessEqual,
                    MachineOperandView::Legacy(range.start()),
                    index.operand_view(),
                ))
        }
    };
    if !lower {
        return false;
    }
    match end {
        // `index + c + k <= end` is `index < end - c - (k - 1)`.
        Some(end) => end
            .checked_sub(delta.constant)
            .and_then(|end| end.checked_sub(elements - 1))
            .is_some_and(index_below),
        None if delta.constant == 0 && elements == 1 => {
            holds(crate::kernel::assumptions::index_comparison(
                CompareRelation::LessThan,
                index.operand_view(),
                MachineOperandView::Legacy(range.end()),
            ))
        }
        None if delta.constant == 0 => {
            let last = MachineTerm::constant((elements - 1) as u32);
            assumptions.decide_overflow_query(
                &crate::kernel::machine_integer::definedness::OverflowQueryView::from_operands(
                    MachineIntegerType::Int32,
                    crate::kernel::machine_integer::Operation::Add,
                    [index.operand_view(), MachineOperandView::Legacy(&last)],
                )
                .expect("int32 addition"),
            ) == Some(false)
                && holds(crate::kernel::assumptions::index_comparison(
                    CompareRelation::LessThan,
                    crate::kernel::assumptions::index_binary(
                        MachineBinaryOp::Add,
                        index.operand_view(),
                        MachineOperandView::Legacy(&last),
                    )
                    .operand_view(),
                    MachineOperandView::Legacy(range.end()),
                ))
        }
        None => false,
    }
}

#[cfg(test)]
mod storage_write_footprint_tests;

/// Project the checked resource transition's memory effects.  This is the
/// only kernel derivation of a contract write footprint: callers consume the
/// ranges and the checked load facts together, while the surface summary is
/// only source metadata used to construct the interface.
pub(crate) fn project_contract_memory_effects(
    entry: &ExecutionState,
    interface: &FunctionContractInterface,
    transition_resources: Option<&[CheckedResourceFact]>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<FunctionMemoryEffectProjection, String>> {
    project_contract_memory_effects_with_guard_policy(
        entry,
        interface,
        transition_resources,
        assumptions,
        budget,
        false,
    )
}

/// Evaluate explicit effect segments once for both call projection and
/// refinement containment.  Refinement may require guards to be decided;
/// ordinary call projection keeps an undecided guard conservatively active.
fn project_explicit_memory_segments(
    entry: &ExecutionState,
    segments: &[MemorySegment],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_decided_guards: bool,
) -> ExecutionResult<Result<(Vec<MemoryRange>, ExecutionFacts), String>> {
    let mut projection_assumptions = assumptions.clone();
    let mut ranges = BTreeSet::new();
    let mut evidence_facts = Vec::new();
    for segment in segments {
        if let Some(guard) = segment.guard() {
            match evaluate_guarded_contract_condition(guard, entry, &projection_assumptions, budget)
            {
                Some(true) => {}
                Some(false) => continue,
                None if require_decided_guards => {
                    return Ok(Err("mutable footprint guard is undecided".to_string()));
                }
                None => {}
            }
        }
        match evaluate_loop_effect_segment_with_facts(
            entry,
            segment,
            &projection_assumptions,
            budget,
        )? {
            Ok((segment, facts)) => {
                projection_assumptions =
                    assumptions_with_path_context(&projection_assumptions, &facts, &[]);
                evidence_facts.extend(facts);
                let range = canonical_memory_range(segment.into_range());
                ranges.insert(range);
            }
            Err(message) => return Ok(Err(message.into())),
        }
    }
    Ok(Ok((ranges.into_iter().collect(), evidence_facts.into())))
}

/// The canonical owned memory ranges one checked owned fact denotes, derived
/// from its definitions at `state` ([`OwnedFootprintDerivation`]), each once.
/// This is the one derivation of a resource-derived write footprint, for a
/// function's frame and a loop's declared frame alike; nothing lowered from
/// source is a second source of it. SymbolicMemory it cannot name is
/// [`MemoryRange::unnamed_footprint`]; `None` only when a family the fact
/// reaches has no definition at all.
pub(super) fn checked_owned_memory_ranges(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<Vec<MemoryRange>> {
    OwnedFootprintDerivation::new(definitions, state, assumptions).derive(fact)
}

/// Project storage dependencies once at an independent contract entry. The
/// ordinary definition walk handles folded instances, children and match arms;
/// unknown dependencies conservatively reserve an unnamed footprint.
pub(super) fn assumed_mutex_input_reservations(
    state: &ExecutionState,
    function: &ProgramFunction,
    assumptions: &PureFactContext,
) -> Option<super::mutexes::MutexInputReservations> {
    let bytes =
        crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin().mutex_storage_bytes;
    let mut ranges = Vec::new();
    let mut guard_ranges = Vec::new();
    for fact in state.resources.facts() {
        let mut derivation = OwnedFootprintDerivation::new(
            function.composite_resource_definitions(),
            state,
            assumptions,
        );
        derivation.mutex_storage_bytes = Some(bytes);
        ranges.extend(
            derivation
                .derive(fact)
                .unwrap_or_else(|| vec![MemoryRange::unnamed_footprint()]),
        );
        let mut guards = OwnedFootprintDerivation::new(
            function.composite_resource_definitions(),
            state,
            assumptions,
        );
        guards.mutex_storage_bytes = Some(bytes);
        guards.mutex_guard_only = true;
        guard_ranges.extend(
            guards
                .derive(fact)
                .unwrap_or_else(|| vec![MemoryRange::unnamed_footprint()]),
        );
    }
    super::mutexes::MutexInputReservations::from_ranges_and_guards(ranges, guard_ranges)
}

/// What a caller keeps unchanged across a call whose resource transfer left it
/// `residual`: the residual itself, whose flat owners and views the havoc finds
/// through its base index, and the owned memory of folded composites,
/// opened one body layer at `state` exactly as
/// `unfold` opens it, with composites in that body expanded.
///
/// Only exactly held bytes count. An iterated fact in an opened body is
/// skipped rather than counted at its span, field-bearing instances stay
/// opaque, and viewed composite bodies are not opened. Hidden instance memory
/// requires explicit unfolding or preservation. Composite opening is paid
/// once per call, one unit per visited composite and its body, except
/// for a family whose bodies are argument-direct: its composites are not
/// visited, and the kept memory answers for them per queried address
/// (`CallKeptRanges::range_holding`).
/// Counted membership never owns its population-wide body independently:
/// another transferred member may authorize the callee to change that body.
pub(super) fn call_kept_ownership(
    residual: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> CallKeptOwnership {
    // Flat ownership is already indexed; opaque instances add no ranges.
    // The persistent composite index answers emptiness without visiting shapes.
    if residual.owned_composite_facts().is_empty() {
        return CallKeptOwnership::new(
            residual.clone(),
            CallKeptRanges::new(
                ResourceContext::new_with_equalities(assumptions),
                vec![],
                None,
            ),
            assumptions,
        );
    }
    crate::kernel::search::ProofSearch::<ProgramFunction>::call_frame(
        residual,
        definitions,
        state,
        assumptions,
    )
}

/// The owned memory ranges of one held composite whose definition has an
/// argument-direct body, opened one layer as a call's kept memory opens a
/// composite. The body reads neither memory nor facts
/// (`CompositeResourceDefinition::has_argument_direct_body`), so the ranges
/// are a function of the fact and are opened against empty ones.
pub(in crate::kernel) fn argument_direct_composite_ranges(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
) -> Vec<MemoryRange> {
    let assumptions = PureFactContext::new();
    expand_composites_for_frame(
        &ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(fact.clone()),
        definitions,
        &SymbolicMemory::new(),
        &assumptions,
    )
    .map(|expanded| owned_memory_ranges_of(&expanded))
    .unwrap_or_default()
}

/// Expose ordinary bodies with their existing access, leaving counted heads opaque,
/// including heads nested inside an ordinary wrapper. This expansion is for
/// custody and framing, not for a checked opening of a population body.
fn expand_composites_for_frame(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    enum Visit {
        Head(ResourceFact),
        Leave(String),
    }
    let mut expanded = context.clone();
    let mut active = BTreeSet::new();
    let mut pending = context
        .facts()
        .iter()
        .filter(|fact| matches!(fact.resource(), Resource::Composite { .. }))
        .cloned()
        .map(Visit::Head)
        .collect::<Vec<_>>();
    while let Some(visit) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        let head = match visit {
            Visit::Leave(name) => {
                active.remove(&name);
                continue;
            }
            Visit::Head(head) => head,
        };
        let Resource::Composite { name, .. } = head.resource() else {
            unreachable!()
        };
        let index = definitions
            .binary_search_by(|definition| {
                crate::instrumentation::record_deterministic_work(1);
                definition.name().cmp(name)
            })
            .ok()?;
        let definition = &definitions[index];
        // An authority control's body holds the authority and the control's
        // private cells; a call frame never exposes them.
        if definition.owns_population_authority()
            || active.contains(name)
            || !expanded.contains_exact_representation(&head)
        {
            continue;
        }
        let (next, children, _) = expand_composite_resource_fact_with_children(
            &expanded,
            &head,
            std::slice::from_ref(definition),
            &crate::kernel::ProgramPoint::of_memory(memory),
            assumptions,
        )?;
        let opaque = next.contains_exact_representation(&head);
        expanded = next;
        if opaque {
            continue;
        }
        active.insert(name.clone());
        pending.push(Visit::Leave(name.clone()));
        pending.extend(
            children
                .into_iter()
                .filter(|child| matches!(child.resource(), Resource::Composite { .. }))
                .map(Visit::Head),
        );
    }
    Some(expanded)
}

#[cfg(test)]
mod counted_membership_framing_tests;

/// The owned memory ranges `context` holds directly, charged one unit each.
fn owned_memory_ranges_of(context: &ResourceContext) -> Vec<MemoryRange> {
    context
        .facts()
        .iter()
        .filter(|fact| {
            crate::instrumentation::record_deterministic_work(1);
            fact.is_own()
        })
        .filter_map(|fact| Some(canonical_memory_range(fact.memory_own_range()?.clone())))
        .collect()
}

/// A decided flat matched body owns its selected memory just as an
/// unmatched body does. Keep only that exact owned head's ordinary bytes;
/// nested instances, population authority and undecided arms stay folded.
fn matched_instance_body_ownership(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<(Vec<MemoryRange>, Vec<(ConditionTerm, bool)>)> {
    let ResourceFact::Own(Resource::Instance(instance), _) = fact else {
        return None;
    };
    let index = definitions
        .binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(instance.name())
        })
        .ok()?;
    let definition = &definitions[index];
    if definition.condition.is_some() || !definition.witnesses.is_empty() {
        return None;
    }
    let matched = definition.matched.as_ref()?;
    let (arm, constructor) =
        selected_instance_match_arm(instance, definition, definitions, assumptions).ok()?;
    if !arm.children.is_empty()
        || !arm.contains.iter().all(|spec| {
            matches!(
                spec.term(),
                ResourceTerm::Memory(_) | ResourceTerm::Token { .. }
            )
        })
    {
        return None;
    }
    let crate::kernel::ResourceFieldValue::Algebraic(model) =
        instance.fields().get(matched.field_index)?
    else {
        return None;
    };
    let projection = ResourceFieldProjection {
        identity: instance.identity(),
        children: Vec::new(),
        field_index: matched.field_index,
        at_entry: false,
    };
    // The callee entry contains transferred inputs, while this exact head is
    // in the checked caller residual. Read its body in that retained frontier.
    let mut read_state = state.clone().with_resource_context(
        ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(fact.clone()),
    );
    read_state.resource_bindings = None;
    let (clauses, projection) = matched_resource_instance_case_read_projection(
        &read_state,
        &projection,
        model,
        &constructor,
        definitions,
        assumptions,
    );
    if clauses.iter().any(|clause| {
        matches!(&clause.proposition, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Constant(false), _))))
    }) {
        return None;
    }
    let ranges = projection
        .into_iter()
        .filter_map(|fact| match fact {
            Proposition::ResourceContains { child, .. } => match *child {
                Resource::Memory(range) => Some(range),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let premises = clauses
        .into_iter()
        .filter_map(|clause| match clause.proposition {
            Proposition::ConditionIs(condition, value) => {
                Some((condition.native_compat().clone(), value))
            }
            _ => None,
        })
        .collect();
    Some((ranges, premises))
}

/// Opens an owned instance one body layer at `state`, exactly as `unfold`
/// evaluates it: the instance's own fields and arguments bound, the body's
/// clauses evaluated, and its field-free composites expanded. `None` for
/// anything but an instance whose definition is unconditional, unmatched,
/// witness-free and owns something, and for a body that does not evaluate
/// here. Charges one unit, plus the evaluation's own work.
fn open_unmatched_instance_body(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    crate::instrumentation::record_deterministic_work(1);
    let Resource::Instance(instance) = fact.resource() else {
        return None;
    };
    let index = definitions
        .binary_search_by(|definition| definition.name().cmp(instance.name()))
        .ok()?;
    let definition = &definitions[index];
    if definition.matched.is_some()
        || definition.condition.is_some()
        || !definition.witnesses.is_empty()
        || definition.contains.is_empty()
    {
        return None;
    }
    let evaluation = instance_body_evaluation(state, instance, definition).ok()?;
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        // This opens a held body's established footprint, as unfold does.
        .assume_entry_clause_spans()
        .assume_held_resource_domains();
    let mut budget = ExecutionBudget::beside_live_state();
    let Ok(Ok(body_resources)) = evaluate_function_resource_context_with_normalization(
        &evaluation,
        &definition.contains,
        &[],
        &evaluation_assumptions,
        &mut budget,
        false,
    ) else {
        return None;
    };
    let body_resources = body_resources.0;
    let expanded = if body_resources
        .facts()
        .iter()
        .any(|fact| matches!(fact.resource(), Resource::Composite { .. }))
    {
        expand_composites_for_frame(
            &body_resources,
            definitions,
            evaluation.memory(),
            &evaluation_assumptions,
        )?
    } else {
        body_resources.clone()
    };
    Some(expanded)
}

/// The composition a store at `write` of `bytes` adds to the partition law
/// when the state holds folded instances whose bodies own cached cells: the
/// owned member of `state`'s context that holds the written bytes, beside the
/// owned memory one body layer inside each owned instance of that context
/// whose pointer arguments name the base of a cell the store could drop.
///
/// **Why it is true.** `state`'s context is a valid composition held at this
/// point, and an owned instance owns exactly what its body owns, so the
/// memory its unconditional, unmatched body owns -- evaluated here, at the
/// instance's own fields and arguments, as `unfold` would evaluate it -- is
/// disjoint from every other owned member of the context and from every other
/// instance's body. Its ranges are spelled with this state's load
/// variables, so like any composition fact the claim is about addresses and
/// stays true after the store. This is a selected store-side body observation.
///
/// **What it opens.** Only instances this context holds now, never one a
/// recorded composition names: a body read at a state where the instance
/// is no longer held could name memory that is someone else's. Only one
/// layer: nested instances stay folded, and a view, an iterated clause, a
/// matched, guarded or witness-bearing body contributes nothing.
///
/// **What it costs.** A constant-time gate on the argument index, one lookup
/// in the base index for the write, then, per cached cell the store could
/// drop, one argument-index lookup per additive base spelling -- the
/// cells the ownership rung visits anyway -- and one body evaluation per
/// instance those lookups name. Instances whose arguments name no cached
/// cell's base are never visited.
///
/// The caller assumes the result before framing the store and records it as
/// a path fact, so the producer (`SymbolicMemory::without_possible_aliasing_cells`,
/// through its ownership-first rung and the composition rung of its ladder)
/// and every route that later re-asks the store-versus-load question (the
/// memory-DAG `Store` hop and both transport sites, through
/// `memory_history::owned_composition_store_separated_evidence`) read the
/// same composition and give the same answer.
pub(in crate::kernel) fn store_opened_instance_composition(
    state: &ExecutionState,
    write: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    let resources = state.resources();
    if !resources.has_owned_instances_with_pointer_arguments() {
        return None;
    }
    let definitions = crate::kernel::assumptions::frame_composite_definitions()?;
    let write = Address {
        base: write.base.clone(),
        offset: crate::kernel::memory_history::normalize_exact_memory_loads_in_pointer_offset(
            &write.offset,
            assumptions,
        ),
    };
    let write_member = assumptions
        .owned_member_holding_access(resources, &write, bytes)?
        .clone();
    let memory = state.memory();
    let candidates = crate::kernel::primitives::AliasCandidates::of_block(&write.base);
    let mut instances = BTreeMap::new();
    for (pointer, _) in memory.cells.candidate_logical_entries(&candidates) {
        crate::kernel::assumptions::owned_instances_naming_access_base(
            resources,
            &pointer,
            &mut instances,
        );
    }
    for ((pointer, _), _) in candidates.entries(&memory.union_cells) {
        crate::kernel::assumptions::owned_instances_naming_access_base(
            resources,
            pointer,
            &mut instances,
        );
    }
    let mut opened = Vec::new();
    for fact in instances.values() {
        if let Some(body) = open_unmatched_instance_body(fact, &definitions, state, assumptions) {
            opened.extend(owned_memory_ranges_of(&body));
        }
    }
    if opened.is_empty() {
        return None;
    }
    // These ranges are the selected members of the held partition, so
    // their definition supplies separation. Retain bounded known conflicts:
    // where this path's facts prove an opened range overlaps the
    // written member (two spellings of one descriptor, say), the context the
    // instance was held in was never realizable, and nothing is opened.
    ResourceContext::new()
        .install_established_partition(
            std::iter::once(write_member)
                .chain(opened)
                .map(ResourceFact::own_memory),
            assumptions,
        )
        .ok()
        .map(|(context, _)| context)
}

/// How much one owned-footprint derivation may visit: one unit per owned
/// fact, opened body and child. A footprint that needs more is summarized by
/// [`MemoryRange::unnamed_footprint`], which is sound for every consumer.
const OWNED_FOOTPRINT_WORK_LIMIT: usize = 4096;

/// The owned memory one held resource denotes, derived from its definitions
/// rather than by opening it as `unfold` would.
///
/// A plain range counts as itself and an iterated fact as the span of every
/// element it could hold, whatever its guards and holes say, since the holder
/// may take any of them. A composite or instance contributes its definition's
/// owned clauses with the parameters bound to its arguments -- and an
/// instance's fields, where they are known -- evaluated at `state`, and its
/// contained composites and named children the same way, their arguments
/// evaluated at `state` too: the definition holds there, so the memory its
/// body owns is the memory the clauses spell there. Tokens own no bytes.
///
/// Nothing needs the body to be *openable*. A matched body whose arm is not
/// decided contributes the union of its arms; an arm clause that needs a
/// binding the undecided model does not supply, and any clause that does not
/// evaluate, reaches memory no clause names here. A guarded body whose guard
/// is not decided is counted as active. A composite's existential witness is
/// bound as `unfold` binds it: to the recorded origin of its word, or else to
/// a fresh symbolic pointer no separation rule places. The descent follows
/// definitions, not unfoldings: a definition that can reach itself, directly
/// or through the family it contains, or that binds a witness in an instance
/// body, has no finite set of clause instances, and its footprint is every
/// block reachable from its pointer arguments through the fields its body
/// owns. Those blocks are not known, so the footprint is
/// [`MemoryRange::unnamed_footprint`]: every cell except the ones a rule that
/// does not read the footprint keeps (what the caller keeps owning across a
/// call, what the function keeps owning across a loop). Which definitions
/// reach unnamed memory is decided once per definition set
/// ([`CompositeResourceDefinition::owned_footprint_reaches_unnamed_memory`]),
/// so a recursive family costs one unit however many nodes are live, and a
/// finite chain of families costs one visit per layer.
///
/// Before this derivation, a footprint was enumerated by opening each held
/// instance one body layer at `state`, as `unfold` opens it. An instance that
/// could not be opened there -- one with a named child, a matched body whose
/// arm was not decided, a recursive or witness-bearing body, a nesting deeper
/// than eight layers -- and a recursive composite the expansion left folded
/// contributed nothing, so a loop or call that held one was summarized as
/// writing none of its memory, and a transport across it kept a fact about a
/// cell it wrote (`mdtests/call_through_deep_instance_chain_footprint_includes_its_memory.md`
/// and the other `*_footprint_includes_*` fixtures).
struct OwnedFootprintDerivation<'a> {
    mutex_storage_bytes: Option<u32>,
    /// Project only held guards, not live/use authority, for abstract calls.
    mutex_guard_only: bool,
    definitions: &'a [CompositeResourceDefinition],
    state: &'a ExecutionState,
    assumptions: &'a PureFactContext,
    evaluation_assumptions: PureFactContext,
    ranges: Vec<MemoryRange>,
    reaches_unnamed: bool,
    undefined_family: bool,
    work: usize,
    /// What remains to visit. The descent is a worklist rather than a
    /// recursion, so a long chain of families costs heap, not stack.
    pending: Vec<OwnedFootprintTask<'a>>,
}

/// One pending visit of [`OwnedFootprintDerivation`].
enum OwnedFootprintTask<'a> {
    /// An owned fact a body evaluated to, or the held fact itself.
    Fact(ResourceFact),
    /// A named child: its definition, its arguments evaluated at the state,
    /// and whichever of its fields the parent supplies.
    Instance {
        definition: &'a CompositeResourceDefinition,
        arguments: Vec<AlgebraicValue>,
        fields: Vec<Option<AlgebraicValue>>,
    },
}

impl<'a> OwnedFootprintDerivation<'a> {
    fn new(
        definitions: &'a [CompositeResourceDefinition],
        state: &'a ExecutionState,
        assumptions: &'a PureFactContext,
    ) -> Self {
        Self {
            definitions,
            state,
            assumptions,
            mutex_storage_bytes: None,
            mutex_guard_only: false,
            evaluation_assumptions: assumptions
                .clone()
                .allow_symbolic_contract_loads()
                .prefer_symbolic_external_loads(),
            ranges: Vec::new(),
            reaches_unnamed: false,
            undefined_family: false,
            work: 0,
            pending: Vec::new(),
        }
    }

    /// The footprint of `fact`, owned by the holder. `None` when a family
    /// it reaches has no definition in the set: the interface is malformed
    /// and the transition that needs the footprint is refused.
    fn derive(mut self, fact: &ResourceFact) -> Option<Vec<MemoryRange>> {
        self.pending.push(OwnedFootprintTask::Fact(fact.clone()));
        while let Some(task) = self.pending.pop() {
            // Past the bound the footprint is unnamed memory, which covers
            // everything the rest could have named.
            if !self.charge() {
                break;
            }
            match task {
                OwnedFootprintTask::Fact(fact) => self.owned_fact(&fact),
                OwnedFootprintTask::Instance {
                    definition,
                    arguments,
                    fields,
                } => self.instance(definition, &arguments, &fields),
            }
        }
        if self.undefined_family {
            return None;
        }
        // Arms and children of one body may spell the same clause instance.
        self.ranges.sort();
        self.ranges.dedup();
        // Adjacent members of one body are one physical range, as the
        // composition that expanded a composite normalized them. Ranges the
        // union of several arms spells may overlap, and then stay as they
        // are.
        if self.mutex_storage_bytes.is_some() {
            if self.reaches_unnamed {
                self.ranges.push(MemoryRange::unnamed_footprint());
            }
            return Some(self.ranges);
        }
        // This is the footprint of the selected held/assumed head, including
        // conservative unions of match arms, not admission of new ownership.
        // Coalesce its explicit ranges without re-proving their partition.
        let normalized = coalesce_written_resource_descriptions(
            self.ranges
                .into_iter()
                .map(ResourceFact::own_memory)
                .collect(),
            self.assumptions,
        );
        let mut ranges = normalized
            .into_iter()
            .filter_map(|fact| fact.memory_own_range().cloned())
            .collect::<Vec<_>>();
        if self.reaches_unnamed {
            ranges.push(MemoryRange::unnamed_footprint());
        }
        ranges.sort();
        ranges.dedup();
        Some(ranges)
    }

    /// Charges one unit; past the bound the footprint is unnamed.
    fn charge(&mut self) -> bool {
        self.work += 1;
        crate::instrumentation::record_deterministic_work(1);
        if self.work > OWNED_FOOTPRINT_WORK_LIMIT {
            self.reaches_unnamed = true;
            return false;
        }
        true
    }

    fn definition(&self, name: &str) -> Option<&'a CompositeResourceDefinition> {
        let definitions = self.definitions;
        match definitions.binary_search_by(|definition| definition.name().cmp(name)) {
            Ok(index) => Some(&definitions[index]),
            // A definition set assembled without sorting is still searched,
            // once per visited body.
            Err(_) => definitions
                .iter()
                .find(|definition| definition.name() == name),
        }
    }

    /// Whether the descent may enter `definition`: otherwise its footprint is
    /// unnamed memory. A set installed through a contract interface flags
    /// every definition on a cycle of families; in a set assembled otherwise,
    /// a cycle through several families is cut by the work bound.
    fn enters(&mut self, definition: &CompositeResourceDefinition) -> bool {
        if self.mutex_storage_bytes.is_some() && !definition.contains_mutex_authority {
            return false;
        }
        if definition.owned_footprint_reaches_unnamed_memory() || definition.is_recursive() {
            self.reaches_unnamed = true;
            return false;
        }
        true
    }

    fn owned_fact(&mut self, fact: &ResourceFact) {
        if !fact.is_own() {
            return;
        }
        match fact.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                self.reaches_unnamed = true;
            }
            Resource::Memory(range) => {
                if self.mutex_storage_bytes.is_none() {
                    self.ranges.push(canonical_memory_range(range.clone()));
                }
            }
            Resource::Iterated(iterated) => {
                if self.mutex_storage_bytes.is_none() {
                    self.ranges
                        .push(canonical_memory_range(iterated.spanning_range()));
                }
            }
            // A token and a mutex guard own no bytes; a guard's guarded
            // resources are separate facts that reach here on their own.
            Resource::PopulationAuthority(_) => {}
            Resource::Token { .. } => {}
            Resource::MutexUse(identity) if !self.mutex_guard_only => {
                if let Some(bytes) = self.mutex_storage_bytes {
                    self.ranges.push(MemoryRange::new_with_element_width(
                        identity.mutex.clone(),
                        0u32.into(),
                        bytes.into(),
                        1,
                    ));
                }
            }
            Resource::ConditionalMutexGuard(_) => {}
            Resource::MutexGuard(identity) => {
                if let Some(bytes) = self.mutex_storage_bytes {
                    self.ranges.push(MemoryRange::new_with_element_width(
                        identity.mutex.clone(),
                        0u32.into(),
                        bytes.into(),
                        1,
                    ));
                }
            }
            Resource::MutexLive(identity) if !self.mutex_guard_only => {
                if let Some(bytes) = self.mutex_storage_bytes {
                    self.ranges.push(MemoryRange::new_with_element_width(
                        identity.mutex.clone(),
                        0u32.into(),
                        bytes.into(),
                        1,
                    ));
                }
            }
            Resource::MutexUse(_) | Resource::Publication(_) | Resource::MutexLive(_) => {}
            Resource::Composite { name, arguments } => {
                self.composite(name, &(arguments).native_values())
            }
            Resource::Instance(instance) => {
                let Some(definition) = self.definition(instance.name()) else {
                    self.undefined_family = true;
                    return;
                };
                if definition.instance_schema.as_ref() != Some(instance.schema()) {
                    self.reaches_unnamed = true;
                    return;
                }
                let fields = instance
                    .fields()
                    .iter()
                    .map(ResourceFieldValue::into_native)
                    .map(Some)
                    .collect::<Vec<_>>();
                self.instance(definition, &(instance.arguments()).native_values(), &fields);
            }
        }
    }

    /// The parameters of `definition` bound to `arguments` in `evaluation`.
    fn bind_parameters(
        definition: &CompositeResourceDefinition,
        arguments: &[AlgebraicValue],
        evaluation: &mut ExecutionState,
    ) -> bool {
        if definition.parameters.len() != arguments.len() {
            return false;
        }
        for (parameter, argument) in definition.parameters.iter().zip(arguments) {
            let Some(value) = argument.as_program_value() else {
                return false;
            };
            if value.program_type() != parameter.program_type() {
                return false;
            }
            evaluation.locals.set_typed(
                parameter.binding_name().clone(),
                value.clone(),
                parameter.program_type(),
            );
        }
        true
    }

    fn composite(&mut self, name: &str, arguments: &[AlgebraicValue]) {
        let Some(definition) = self.definition(name) else {
            self.undefined_family = true;
            return;
        };
        if !self.enters(definition) {
            return;
        }
        if definition.instance_schema.is_some() || definition.matched.is_some() {
            self.reaches_unnamed = true;
            return;
        }
        let mut evaluation = ExecutionState::at_point(&self.state.program_point());
        evaluation.preserves_mutex_protocols = self.state.preserves_mutex_protocols;
        if !Self::bind_parameters(definition, arguments, &mut evaluation)
            || bind_composite_witnesses(definition, arguments, &mut evaluation, self.assumptions)
                .is_none()
        {
            self.reaches_unnamed = true;
            return;
        }
        self.body(
            definition,
            evaluation,
            &definition.contains,
            &[],
            &[],
            None,
            None,
        );
    }

    fn instance(
        &mut self,
        definition: &'a CompositeResourceDefinition,
        arguments: &[AlgebraicValue],
        fields: &[Option<AlgebraicValue>],
    ) {
        if !self.enters(definition) {
            return;
        }
        let Some(schema) = definition.instance_schema.as_ref() else {
            self.reaches_unnamed = true;
            return;
        };
        if schema.fields().len() != fields.len() || !definition.witnesses.is_empty() {
            self.reaches_unnamed = true;
            return;
        }
        let mut evaluation = self.state.clone();
        evaluation.resources = ResourceContext::new_with_equalities(self.assumptions);
        if self.mutex_storage_bytes.is_some() {
            evaluation.locals = LocalEnvironment::default();
        }
        if definition.matched.is_some() {
            // An arm's C names are lexical parameters and constructor
            // bindings, never incidental locals of the function holding it.
            evaluation.locals = LocalEnvironment::default();
        }
        // Interpret logical parent fields without granting body ownership.
        if let Some(values) = fields.iter().cloned().collect::<Option<Vec<_>>>()
            && let Some(instance) = ResourceInstance::new(
                Variable(u64::MAX),
                definition.name().to_string(),
                arguments.iter().cloned().collect(),
                schema.clone(),
                values.into_iter().collect(),
            )
        {
            evaluation.instance_field_scope = ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance)));
            evaluation.resource_bindings = None;
        }
        for ((name, _), value) in schema.fields().iter().zip(fields) {
            if let Some(AlgebraicValue::Program(value)) = value {
                evaluation
                    .locals
                    .set_typed(name.clone(), value.clone(), value.program_type());
            }
        }
        if !Self::bind_parameters(definition, arguments, &mut evaluation) {
            self.reaches_unnamed = true;
            return;
        }
        let Some(matched) = definition.matched.as_ref() else {
            self.body(
                definition,
                evaluation,
                &definition.contains,
                &definition.children,
                fields,
                None,
                None,
            );
            return;
        };
        for (arm, constructor) in self.footprint_arms(definition, matched, arguments, fields) {
            let mut arm_evaluation = evaluation.clone();
            if let Some(constructor) = &constructor {
                for ((name, binding_type), value) in
                    arm.bindings.iter().zip(&arm.binding_types).zip(constructor)
                {
                    if let (AlgebraicValueType::Program(_), AlgebraicValue::Program(value)) =
                        (binding_type, value)
                    {
                        arm_evaluation.locals.set_typed(
                            name.clone(),
                            value.clone(),
                            value.program_type(),
                        );
                    }
                }
            }
            self.body(
                definition,
                arm_evaluation,
                &arm.contains,
                &arm.children,
                fields,
                constructor.as_deref(),
                Some(arm),
            );
        }
    }

    /// The arms a matched body may be in: the one its model's constructor
    /// names, with that constructor's fields, when the model or the premises
    /// decide it, and otherwise every arm, with no bindings.
    fn footprint_arms(
        &self,
        definition: &'a CompositeResourceDefinition,
        matched: &'a ResourceMatchBody,
        arguments: &[AlgebraicValue],
        fields: &[Option<AlgebraicValue>],
    ) -> Vec<(&'a ResourceMatchArm, Option<Vec<AlgebraicValue>>)> {
        let constructor_arm = |variant: &str, fields: &[AlgebraicValue]| {
            matched
                .arms
                .iter()
                .find(|arm| arm.variant == variant)
                .map(|arm| vec![(arm, Some(fields.to_vec()))])
        };
        if let Some(Some(AlgebraicValue::Algebraic(model))) = fields.get(matched.field_index)
            && let AlgebraicTermNode::Constructor { variant, fields } = &model.node
            && let Some(arms) = constructor_arm(variant, fields)
        {
            return arms;
        }
        if let (Some(schema), Some(fields)) = (
            definition.instance_schema.as_ref(),
            fields.iter().cloned().collect::<Option<Vec<_>>>(),
        ) && let Some(instance) = ResourceInstance::new(
            Variable(u64::MAX),
            definition.name().to_string(),
            arguments.iter().cloned().collect(),
            schema.clone(),
            fields.into_iter().collect(),
        ) {
            let refutations =
                instance_arm_model_facts(&instance, self.definitions, self.state, self.assumptions);
            let selection = refutations.into_iter().fold(
                self.assumptions.clone(),
                PureFactContext::assume_proposition,
            );
            if let Ok((arm, constructor)) =
                selected_instance_match_arm(&instance, definition, self.definitions, &selection)
                && let AlgebraicTermNode::Constructor { fields, .. } = constructor.node
            {
                return vec![(arm, Some(fields))];
            }
        }
        matched.arms.iter().map(|arm| (arm, None)).collect()
    }

    /// One body: its guard, its owned clauses, and its named children, whose
    /// footprints are queued.
    #[allow(clippy::too_many_arguments)]
    fn body(
        &mut self,
        definition: &'a CompositeResourceDefinition,
        mut evaluation: ExecutionState,
        contains: &'a [ResourceSpec],
        children: &'a [ResourceChildSpec],
        fields: &[Option<AlgebraicValue>],
        constructor: Option<&[AlgebraicValue]>,
        matched_arm: Option<&ResourceMatchArm>,
    ) {
        let mut budget = ExecutionBudget::beside_live_state();
        // An undecided guard counts the body as active: the footprint is an
        // upper bound, and a body that is not active owns nothing extra.
        if evaluate_composite_resource_body_condition(
            definition,
            &evaluation,
            &self.evaluation_assumptions,
            &mut budget,
        ) == Some(false)
        {
            return;
        }
        for spec in contains {
            // Abstract tokens own no memory, regardless of their quantity.
            // Footprint discovery need not prove that quantity nonnegative;
            // the actual resource exchange still checks it. A population
            // authority is likewise exclusive custody without bytes.
            if matches!(
                spec.term(),
                ResourceTerm::Token { .. } | ResourceTerm::PopulationAuthority { .. }
            ) {
                continue;
            }
            let Ok(Ok(fact)) = evaluate_function_resource_spec(
                &evaluation,
                spec,
                &self.evaluation_assumptions,
                &mut budget,
            ) else {
                self.reaches_unnamed = true;
                continue;
            };
            evaluation.resources = evaluation
                .resources
                .clone()
                .unchecked_with_fact(fact.clone());
            if fact.is_own() {
                self.pending.push(OwnedFootprintTask::Fact(fact));
            }
        }
        let mut algebraic_bindings = BTreeMap::new();
        let mut integer_bindings = BTreeMap::new();
        if let (Some(constructor), Some(arm)) = (constructor, matched_arm) {
            for ((name, variable), value) in arm
                .bindings
                .iter()
                .zip(&arm.binding_variables)
                .zip(constructor)
            {
                match (variable, value) {
                    (None, AlgebraicValue::Algebraic(value)) => {
                        algebraic_bindings.insert(name.clone().into(), value.clone());
                    }
                    (Some(variable), AlgebraicValue::Integer(value)) => {
                        integer_bindings.insert(*variable, value.clone());
                    }
                    _ => {}
                }
            }
        }
        for child in children {
            let Some(child_definition) = self.definition(&child.resource) else {
                self.undefined_family = true;
                continue;
            };
            let arguments = child
                .arguments
                .iter()
                .zip(&child_definition.parameters)
                .map(|(argument, parameter)| {
                    let Ok(paths) = crate::kernel::spec::evaluate_resource_child_argument_paths(
                        &evaluation,
                        argument,
                        &self.evaluation_assumptions,
                        &algebraic_bindings,
                        &integer_bindings,
                        &mut budget,
                    ) else {
                        return None;
                    };
                    // The body holds wherever the resource is held, so the
                    // argument reads the cells the body owns there.
                    let [path] = paths.as_slice() else {
                        return None;
                    };
                    let ExpressionOutcome::Value(value) = &path.outcome else {
                        return None;
                    };
                    coerce_program_function_argument_without_obligations(&value.native(), parameter)
                        .map(AlgebraicValue::Program)
                })
                .collect::<Option<Vec<_>>>();
            let Some(arguments) = arguments.filter(|arguments| {
                arguments.len() == child.arguments.len()
                    && arguments.len() == child_definition.parameters.len()
            }) else {
                self.reaches_unnamed = true;
                continue;
            };
            let fields = child
                .field_bindings
                .iter()
                .map(|source| match source {
                    ResourceChildField::Constructor(index) => {
                        constructor.and_then(|fields| fields.get(*index).cloned())
                    }
                    ResourceChildField::Parent(index) => fields.get(*index).cloned().flatten(),
                })
                .collect::<Vec<_>>();
            self.pending.push(OwnedFootprintTask::Instance {
                definition: child_definition,
                arguments,
                fields,
            });
        }
    }
}

pub(crate) fn project_contract_memory_effects_with_guard_policy(
    entry: &ExecutionState,
    interface: &FunctionContractInterface,
    transition_resources: Option<&[CheckedResourceFact]>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_decided_guards: bool,
) -> ExecutionResult<Result<FunctionMemoryEffectProjection, String>> {
    if interface.resource_derived_mutable_frame() && interface.resource_derived_frame_mixed() {
        return Ok(Err(
            "resource-derived mutable frame mixes explicit effect segments".to_string(),
        ));
    }
    let evaluated_transition;
    let transition_resources =
        if interface.resource_derived_mutable_frame() || transition_resources.is_some() {
            match transition_resources {
                Some(resources) => Some(resources),
                None => {
                    evaluated_transition = match evaluate_function_resource_context_with_metadata(
                        entry,
                        interface.resource_requires(),
                        interface.composite_resource_definitions(),
                        assumptions,
                        budget,
                    )? {
                        Ok((_, checked)) => checked,
                        Err(error) => {
                            return Ok(Err(format!(
                                "could not evaluate resource transition: {error}"
                            )));
                        }
                    };
                    Some(evaluated_transition.as_slice())
                }
            }
        } else {
            None
        };
    if transition_resources.is_some_and(|resources| {
        resources.iter().any(|checked| {
            checked.role == ResourceTransferRole::Produce
                || checked.state_source == ResourceStateSource::Post
                || (checked.fact.is_view() && checked.role != ResourceTransferRole::Borrow)
        })
    }) {
        return Ok(Err(
            "resource transition contains an inconsistent transfer role".to_string(),
        ));
    }
    // Canonical ranges are indexed while the transition is projected. This
    // keeps duplicate wrapper members from triggering a quadratic scan.
    let mut ranges = BTreeSet::new();
    let mut evidence_facts = Vec::new();
    let mut range_sources = Vec::new();
    if let Some(resources) = transition_resources {
        for checked in resources {
            // Borrowing is a boundary role, not an access-mode rewrite:
            // `requires owns p` paired with `ensures borrowed p` still gives
            // the body write authority for the entry-selected range.
            if !checked.fact.is_own() {
                continue;
            }
            let Some(expanded) = checked_owned_memory_ranges(
                &checked.fact,
                interface.composite_resource_definitions(),
                entry,
                assumptions,
            ) else {
                if !interface.resource_derived_mutable_frame() {
                    continue;
                }
                return Ok(Err(
                    "could not expand the checked resource transition".to_string()
                ));
            };
            for range in expanded {
                // Every byte of the expansion belongs to this one requirement,
                // whatever depth it came from, so the requirement is the
                // source recorded for each of its ranges.
                range_sources.push((range.clone(), checked.fact.clone()));
                if interface.resource_derived_mutable_frame() {
                    ranges.insert(range);
                }
            }
        }
    }
    // Resource-derived contracts get their memory authority exclusively from
    // the checked transition above.  The surface `contract_mutable` list is
    // a body-proof/read-only diagnostic projection and must not be another
    // modular-call source.  Functions without resource clauses retain their
    // explicit effect segments here.
    let explicit_segments = if !interface.resource_derived_mutable_frame() {
        interface.contract_mutable()
    } else {
        &[]
    };
    let (explicit_ranges, explicit_evidence) = match project_explicit_memory_segments(
        entry,
        explicit_segments,
        assumptions,
        budget,
        require_decided_guards,
    )? {
        Ok(result) => result,
        Err(message) => return Ok(Err(message)),
    };
    ranges.extend(explicit_ranges);
    evidence_facts.extend(explicit_evidence);
    Ok(Ok(FunctionMemoryEffectProjection {
        ranges: ranges.into_iter().collect(),
        evidence_facts: evidence_facts.into(),
        range_sources,
    }))
}

/// Establish the inherited loop frame from the one checked entry transition.
/// The source segments remain attached for diagnostics, but loop execution
/// consumes these fixed ranges thereafter. In particular, a pointer field
/// changed by the body cannot retarget an inherited frame on a back edge.
pub(crate) fn establish_resource_derived_loop_frames(
    function: ProgramFunction,
    entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ProgramFunction, String>> {
    if !function.resource_derived_mutable_frame() {
        return Ok(Ok(function));
    }
    let mut transition_assumptions = assumptions.clone();
    let quantity_assumptions = match quantified_resource_requirement_assumptions(
        entry,
        function.resource_requires(),
        function
            .contract_interface()
            .composite_resource_definitions(),
        &transition_assumptions,
        budget,
    )? {
        Ok(assumptions) => assumptions,
        Err(error) => {
            return Ok(Err(format!(
                "could not evaluate resource quantities: {error}"
            )));
        }
    };
    for proposition in quantity_assumptions {
        transition_assumptions = transition_assumptions.assume_proposition(proposition);
    }
    let projection = match project_contract_memory_effects(
        entry,
        function.contract_interface(),
        None,
        &transition_assumptions,
        budget,
    )? {
        Ok(projection) => projection,
        Err(message) => return Ok(Err(message)),
    };
    fn rewrite(statement: &mut ProgramStatement, ranges: &[MemoryRange]) {
        match statement {
            ProgramStatement::Seq(statements) => {
                *statements = statements.map(|statement| {
                    let mut statement = statement.clone();
                    rewrite(std::sync::Arc::make_mut(&mut statement), ranges);
                    statement
                });
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                rewrite(then_branch, ranges);
                rewrite(else_branch, ranges);
            }
            ProgramStatement::Loop {
                test: loop_test,
                update,
                effect_checks,
                body,
                ..
            } => {
                for check in effect_checks {
                    if check.origin() == LoopEffectOrigin::InheritedResourceDerived {
                        *check = check.clone().with_validated_ranges(ranges.to_vec());
                    }
                }
                rewrite(body, ranges);
                rewrite(std::sync::Arc::make_mut(&mut loop_test.statement), ranges);
                if let Some(update) = update {
                    rewrite(std::sync::Arc::make_mut(update), ranges);
                }
            }
            ProgramStatement::Switch { cases, .. } => {
                for case in cases {
                    rewrite(&mut case.body, ranges);
                }
            }

            _ => {}
        }
    }
    let mut body = function.body().clone();
    rewrite(&mut body, projection.ranges());
    Ok(Ok(function.with_body(body)))
}

/// Whether an owned composite the interface requires has a guarded body
/// anywhere under it. A resource-derived footprint used to be lowered from
/// source with the enclosing conditions as guards on every segment beneath
/// them; the kernel now reads the definitions instead, so the refusals those
/// guards produced are unchanged.
fn requirements_reach_a_guarded_composite(interface: &FunctionContractInterface) -> bool {
    fn composite_name(spec: &ResourceSpec) -> Option<&str> {
        match spec.term() {
            ResourceTerm::Composite { name, .. } => Some(name),
            ResourceTerm::Instance { resource, .. } => match resource.as_ref() {
                ResourceTerm::Composite { name, .. } => Some(name),
                _ => None,
            },
            _ => None,
        }
    }
    fn guarded(
        name: &str,
        definitions: &[CompositeResourceDefinition],
        active: &mut BTreeSet<String>,
    ) -> bool {
        if !active.insert(name.to_string()) {
            return false;
        }
        let result = definitions
            .iter()
            .find(|definition| definition.name() == name)
            .is_some_and(|definition| {
                definition.condition().is_some()
                    || definition
                        .contains()
                        .iter()
                        .filter(|spec| spec.access() == ResourceAccessMode::Own)
                        .filter_map(composite_name)
                        .any(|child| guarded(child, definitions, active))
            });
        active.remove(name);
        result
    }
    interface
        .resource_requires()
        .iter()
        .filter(|spec| spec.access() == ResourceAccessMode::Own)
        .filter_map(composite_name)
        .any(|name| {
            guarded(
                name,
                interface.composite_resource_definitions(),
                &mut BTreeSet::new(),
            )
        })
}

fn evaluate_contract_mutable_ranges_for_interface(
    interface: &FunctionContractInterface,
    entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_unguarded: bool,
) -> ExecutionResult<Option<Vec<MemoryRange>>> {
    if require_unguarded
        && (interface
            .contract_mutable()
            .iter()
            .any(|s| s.guard().is_some())
            || (interface.resource_derived_mutable_frame()
                && requirements_reach_a_guarded_composite(interface)))
    {
        return Ok(None);
    }
    Ok(
        match project_contract_memory_effects(entry, interface, None, assumptions, budget)? {
            Ok(projection) => Some(projection.ranges),
            Err(_) => None,
        },
    )
}

/// Evaluates exactly the concrete ranges active in one explicit proof case.
///
/// Unlike automatic refinement, this never branches over a guard. Every guard
/// must already be decided by the named preconditions and the proof's written
/// case assumptions. A false guard contributes no possible write; a true guard
/// contributes its ordinary evaluated range.
/// No reaching fixture exists, and none can be written today: the only
/// caller is `function_refines_named_contract_in_case`'s `explicit_case`
/// branch, and its one call site passes `explicit_case: false`. The guard
/// decision below is route-restricted with the rest of package 10(b) so the
/// branch cannot come back carrying a proof search, but its behaviour is
/// unobserved by both fixture harnesses.
fn evaluate_decided_contract_mutable_ranges_for_interface(
    interface: &FunctionContractInterface,
    entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<MemoryRange>>> {
    let mut guard_assumptions = assumptions.clone();
    let Some(guards) = lower_refinement_mutable_guards_for_interface(
        interface,
        entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    let mut ranges = Vec::with_capacity(interface.contract_mutable().len());
    for (segment, guard) in interface.contract_mutable().iter().zip(guards) {
        if let Some(guard) = guard {
            // A refined mutable segment is included, dropped, or leaves the
            // whole footprint undecided. The decision uses the exact routes
            // only; an undecided guard refuses the refinement rather than
            // being settled by a proof search over the ambient context.
            match guard_value_by_exact_routes(&guard_assumptions, &guard) {
                Some(false) => continue,
                Some(true) => {}
                None => return Ok(None),
            }
        }
        let Ok((mut projected, _)) = project_explicit_memory_segments(
            entry,
            std::slice::from_ref(segment),
            &guard_assumptions,
            budget,
            true,
        )?
        else {
            return Ok(None);
        };
        let Some(range) = projected.pop() else {
            return Ok(None);
        };
        ranges.push(range);
    }
    Ok(Some(ranges))
}

mod contract_refinement;
use contract_refinement::*;

#[cfg(test)]
mod guarded_mutable_refinement_tests;

mod refinement_side_conditions;
pub(crate) use refinement_side_conditions::*;

#[cfg(test)]
fn add_verified_function_ensure_facts(
    facts: &mut ExecutionFacts,
    obligations: &[ProofObligation],
    post_contract_state: &ExecutionState,
    entry_contract_state: &ExecutionState,
    function: &ProgramFunction,
    effective_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    add_verified_function_ensure_facts_selected_with_interface(
        facts,
        obligations,
        post_contract_state,
        entry_contract_state,
        function.contract_interface(),
        function.contract_ensures().iter(),
        effective_assumptions,
        budget,
    )
}

fn return_coordinate_ensure(ensure: &SpecProposition) -> bool {
    matches!(
        ensure,
        SpecProposition::Comparison { .. } | SpecProposition::ResourceSeparate { .. }
    ) && spec_tree_all(SpecNode::Proposition(ensure), |node| {
        crate::instrumentation::record_deterministic_work(1);
        let allowed = match node {
            // These are values of the already emitted instance, independent
            // of ledger observations. Descendant identities are built later.
            SpecNode::Expression(SpecExpression::ResourceField { projection, .. }) => {
                projection.children.is_empty()
            }
            SpecNode::Expression(expression) => matches!(
                expression,
                SpecExpression::Value(_)
                    | SpecExpression::ProgramExpression(_)
                    | SpecExpression::MemoryLoad { .. }
                    | SpecExpression::LoopEntryState(_)
                    | SpecExpression::Cast(..)
                    | SpecExpression::PointerCoercion(..)
                    | SpecExpression::Subobject { .. }
                    | SpecExpression::PointerOffset { .. }
                    | SpecExpression::ObjectAddress(_)
                    | SpecExpression::Add(..)
                    | SpecExpression::Subtract(..)
                    | SpecExpression::Multiply(..)
            ),
            _ => true,
        };
        if allowed {
            Visit::Descend
        } else {
            Visit::Stop(())
        }
    })
}

fn add_verified_function_ensure_facts_selected_with_interface<'a>(
    facts: &mut ExecutionFacts,
    obligations: &[ProofObligation],
    post_contract_state: &ExecutionState,
    entry_contract_state: &ExecutionState,
    interface: &FunctionContractInterface,
    ensures: impl Iterator<Item = &'a SpecProposition>,
    effective_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    let mut ensures = ensures.peekable();
    if ensures.peek().is_none() {
        return Ok(());
    }
    // Every ensure is lowered under the call's context plus the facts
    // published so far, the earlier ensures' among them. Build that context
    // once and extend it by each ensure's own new facts: rebuilding it from
    // the whole fact list per ensure was quadratic in the ensure count, and
    // uncharged. The facts and obligations are sets of assumptions, so
    // assuming a later fact after the obligations names the same context.
    let opened_entry_state = {
        expand_all_composite_resource_facts_at_state(
            entry_contract_state.resources(),
            interface.composite_resource_definitions(),
            entry_contract_state,
            effective_assumptions,
        )
        .map(|resources| {
            entry_contract_state
                .clone()
                .with_resource_context(resources)
        })
    };
    let entry_contract_state = opened_entry_state.as_ref().unwrap_or(entry_contract_state);
    let mut ensure_assumptions =
        assumptions_with_path_context(effective_assumptions, facts, obligations);
    while let Some(ensure) = ensures.next() {
        let published_before = facts.len();
        // A verified callee certifies that its ensures, including the memory
        // loads used to state them, are well-defined. Lower those loads into
        // explicit path obligations here instead of asking the general prover
        // to rediscover each contextual range proof while applying the call
        // rule. The obligations are retained below as certified consequences
        // of the verified contract.
        let lowering_assumptions = ensure_assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .defer_non_exact_loadability_obligations();
        let ensure_paths = lower_spec_proposition_at_state_with_loop_entry(
            post_contract_state,
            ensure,
            Some(entry_contract_state),
            &lowering_assumptions,
            budget,
        )?;
        for ensure_path in ensure_paths {
            // Certified lowering facts are consequences of the selected
            // path, such as a checked count's entry-owned lower bound. Keep
            // their branch guards, but do not turn those consequences into
            // new caller prerequisites for the specialized ensure.
            let branch_facts = {
                ensure_path
                    .facts
                    .iter()
                    .filter(|fact| !fact.certified)
                    .cloned()
                    .collect::<ExecutionFacts>()
            };
            for fact in ensure_path.facts.iter().filter(|fact| fact.certified) {
                facts.push(ExecutionPureFact::certified(wrap_path_context(
                    fact.proposition().clone(),
                    &branch_facts,
                    &[],
                )));
            }

            for path_obligation in &ensure_path.obligations {
                facts.push(ExecutionPureFact::certified(wrap_path_context(
                    path_obligation.proposition().clone(),
                    &ensure_path.facts,
                    &[],
                )));
            }
            facts.push(ExecutionPureFact::certified(wrap_path_context(
                ensure_path.proposition.clone(),
                &ensure_path.facts,
                &[],
            )));
            let specialized_assumptions = assumptions_with_path_context(
                &ensure_assumptions,
                &ensure_path.facts,
                &ensure_path.obligations,
            );
            // The callee's ensure holds under its own leading premises. Where
            // one of those premises is exactly available at this call, the
            // consequent is available too, and publishing it saves every
            // caller an implication application. This is the kernel's modus ponens, so it
            // walks only the ensure's own implication chain and cites each
            // discharged premise exactly: an indexed hit in the call context,
            // or a premise already discharged above it in this chain. A
            // premise neither route settles ends the walk, and the ensure
            // stays available as the implication it was written as, for the
            // proof to discharge with `apply(fact)`.
            let mut specialized = ensure_path.proposition.clone();
            let mut discharged_premises: Vec<Proposition> = Vec::new();
            while let Proposition::Implies(premise, body) = specialized {
                let reversed_order = match premise.as_ref() {
                    condition_source_0 @ Proposition::ConditionIs(_, value)
                        if let Some((
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::GreaterThan,
                                left,
                                right,
                            },
                            _,
                        )) = condition_source_0.condition_native() =>
                    {
                        Some(Proposition::condition_is(
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::LessThan,
                                left: right.clone(),
                                right: left.clone(),
                            },
                            *value,
                        ))
                    }
                    condition_source_0 @ Proposition::ConditionIs(_, value)
                        if let Some((
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::GreaterEqual,
                                left,
                                right,
                            },
                            _,
                        )) = condition_source_0.condition_native() =>
                    {
                        Some(Proposition::condition_is(
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::LessEqual,
                                left: right.clone(),
                                right: left.clone(),
                            },
                            *value,
                        ))
                    }
                    condition_source_0 @ Proposition::ConditionIs(_, value)
                        if let Some((
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::LessThan,
                                left,
                                right,
                            },
                            _,
                        )) = condition_source_0.condition_native() =>
                    {
                        Some(Proposition::condition_is(
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::GreaterThan,
                                left: right.clone(),
                                right: left.clone(),
                            },
                            *value,
                        ))
                    }
                    condition_source_0 @ Proposition::ConditionIs(_, value)
                        if let Some((
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::LessEqual,
                                left,
                                right,
                            },
                            _,
                        )) = condition_source_0.condition_native() =>
                    {
                        Some(Proposition::condition_is(
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::GreaterEqual,
                                left: right.clone(),
                                right: left.clone(),
                            },
                            *value,
                        ))
                    }
                    _ => None,
                };
                // A closed premise, such as the constant condition left by
                // a decided argument comparison, settles without the call
                // context under either semantics.
                let available = {
                    crate::kernel::reasoning::path_facts::solve_builtin_prop(&premise)
                        || specialized_assumptions.states_required_goal(&premise)
                        || reversed_order.as_ref().is_some_and(|premise| {
                            specialized_assumptions.states_required_goal(premise)
                        })
                } || discharged_premises
                    .iter()
                    .any(|discharged| discharged == premise.as_ref());
                if !available {
                    specialized = Proposition::Implies(premise, body);
                    break;
                }
                discharged_premises.push((*premise).clone());
                specialized = *body;
            }
            if !discharged_premises.is_empty() {
                facts.push(ExecutionPureFact::certified(wrap_path_context(
                    specialized,
                    &branch_facts,
                    &[],
                )));
            }
        }
        // Preserve the source identity of a named predicate ensure. The
        // expanded `ensure` above is the operational authority; this exact
        // registered pair is its definitional surface identity.
        if let Some(unfolding) = interface
            .predicate_unfoldings()
            .iter()
            .find(|unfolding| unfolding.body() == ensure)
        {
            let predicate_paths = lower_spec_proposition_at_state_with_loop_entry(
                post_contract_state,
                unfolding.predicate(),
                Some(entry_contract_state),
                &lowering_assumptions,
                budget,
            )?;
            for predicate_path in predicate_paths {
                if predicate_path.obligations.is_empty() {
                    facts.push(ExecutionPureFact::certified(predicate_path.proposition));
                }
            }
        }
        // Only later ensures read this temporary context. The final delta
        // will be admitted by the checked call's actual consumers.
        if ensures.peek().is_some() {
            let published = facts.iter().skip(published_before);
            crate::instrumentation::record_deterministic_work(published.len());
            for fact in published {
                ensure_assumptions =
                    ensure_assumptions.assume_proposition(fact.proposition().clone());
            }
        }
    }
    Ok(())
}

/// No fixture in either harness reaches the refutation below; the kernel
/// test `continuity_requires_both_the_allocation_base_and_size` pins it, and
/// fails when the route is denied.
///
/// The two sizes are compared in their common format. Sizes of
/// different formats are never the same allocation's (D5): a pair whose
/// bases are not proven distinct is [`AllocationContinuity::CrossKind`].
fn allocation_continuity(
    input_base: &Address,
    input_size: &AllocationSize,
    output_base: &Address,
    output_size: &AllocationSize,
    assumptions: &PureFactContext,
) -> AllocationContinuity {
    if input_size.kind() != output_size.kind() {
        return if pointers_proven_distinct_for_memory_resolution(
            input_base,
            output_base,
            assumptions,
        ) {
            AllocationContinuity::Distinct
        } else {
            AllocationContinuity::CrossKind
        };
    }
    let (input_bytes, output_bytes) = (input_size.bytes(), output_size.bytes());
    if pointers_proven_equal_for_memory_resolution(input_base, output_base, assumptions) {
        let format = match input_size.kind() {
            AllocationSizeKind::Int32 => MachineIntegerType::Int32,
            AllocationSizeKind::UInt64 => MachineIntegerType::UInt64,
        };
        if program_values_proven_equal_for_memory_resolution(
            &input_size.token_value(),
            &output_size.token_value(),
            assumptions,
        ) {
            return AllocationContinuity::Same;
        }
        let condition = ConditionTerm::Compare {
            format,
            relation: CompareRelation::Equal,
            left: Box::new(input_bytes.clone()),
            right: Box::new(output_bytes.clone()),
        };
        // Two allocation sizes at one base are the same allocation, a
        // refuted one, or an undecided pair. The refutation uses the exact
        // fact index and the frozen condition checker on the bare condition;
        // anything else stays undecided and travels on as a condition the
        // consumer must settle.
        if required_obligation_is_exactly_discharged(
            assumptions,
            &Proposition::condition_is(condition.clone(), false),
        ) {
            AllocationContinuity::Inconsistent
        } else {
            AllocationContinuity::Undecided(condition)
        }
    } else if pointers_proven_distinct_for_memory_resolution(input_base, output_base, assumptions) {
        AllocationContinuity::Distinct
    } else {
        AllocationContinuity::Undecided(ConditionTerm::address_equal(
            input_base.clone(),
            output_base.clone(),
        ))
    }
}

#[cfg(test)]
mod allocation_continuity_tests;

/// The resource the caller keeps across a call that could still refer to an
/// allocation the call retires, or `None` when every kept resource is known
/// separate from it.
///
/// `lent` is what the caller handed the callee and `kept` the residual it
/// holds across the call, both expanded under one memory. At the call the two
/// were one valid composition, and owned memory is exclusive: two owned
/// memory facts held at once are disjoint (`MemoryResourceAlgebra`'s
/// `pair_validity_error`, the law `observable_facts_assuming_valid` states
/// for one context). So when an owned memory fact the caller lent covers
/// every byte of the allocation, each owned memory fact the caller kept is
/// disjoint from that allocation by construction and cannot refer to it after
/// the free. A kept view over exactly the bytes of a kept owned memory fact
/// (the view a caller holds of an object it also owns, such as a descriptor
/// whose cells a callee published as read authority) names only those owned
/// bytes, so it is disjoint from the allocation for the same reason. That is
/// all the partition speaks for: any other kept view, a kept composite, or any
/// kept fact when the lent owners do not cover the whole allocation, still
/// needs a separation the path facts prove (a stated `separate(memory(..),
/// memory(..))` that contains both sides, distinct blocks, disjoint constant
/// intervals, or one context's own composition).
///
/// Only the kept facts that can name the retired block are visited, from the
/// context's indexes, and the lent coverage is decided at most once from the
/// lent facts in that block. A view's owner is found by one exact lookup of
/// the same range owned once, never by a scan, so the work does not grow with
/// unrelated kept resources.
pub(in crate::kernel) fn caller_resource_left_stale_by_retirement<'a>(
    lent: &ResourceContext,
    kept: &'a ResourceContext,
    base: &Address,
    bytes: &AllocationSize,
    assumptions: &PureFactContext,
) -> Option<&'a ResourceFact> {
    let mut lent_owners_cover_allocation = None;
    for resource in kept.facts_that_may_refer_to_memory_block(&base.base) {
        let owned_by_the_caller = resource.memory_own_range().is_some()
            && resource.has_proven_positive_quantity(assumptions)
            || resource.memory_view_range().is_some_and(|range| {
                crate::instrumentation::record_deterministic_work(1);
                kept.contains_exact_representation(&ResourceFact::own(Resource::Memory(
                    range.clone(),
                )))
            });
        if owned_by_the_caller
            && *lent_owners_cover_allocation.get_or_insert_with(|| {
                lent_owned_memory_covers_allocation(lent, base, bytes, assumptions)
            })
        {
            continue;
        }
        if resource.is_proven_separate_from_allocation(base, bytes, assumptions) {
            continue;
        }
        return Some(resource);
    }
    None
}

/// Whether one owned memory fact of `lent` covers the allocation's whole
/// byte range `base[0..bytes]`. Coverage is the ordinary proof-aware
/// `memory_range_covers`, so the owner may spell the range in another element
/// width or with provably equal endpoints.
fn lent_owned_memory_covers_allocation(
    lent: &ResourceContext,
    base: &Address,
    bytes: &AllocationSize,
    assumptions: &PureFactContext,
) -> bool {
    if let Some(constant) = bytes.int32_bytes().and_then(MachineTerm::as_const)
        && constant > 0
    {
        return lent.owns_storage_access(base, constant, assumptions);
    }
    let allocation = bytes.byte_range(base.clone());
    lent.directly_supporting_fact(&ResourceFact::own_memory(allocation), assumptions)
        .is_some()
}

fn apply_verified_heap_allocation_delta(
    mut memory: SymbolicMemory,
    entry_memory: &SymbolicMemory,
    input_resources: &ResourceContext,
    preserved_caller_resources: &ResourceContext,
    output_resources: &ResourceContext,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
    worker_ledger: Option<&LoanLedger>,
    mutex_state: &ExecutionState,
    output_state: &ExecutionState,
) -> Result<VerifiedAllocationDelta, VerifiedAllocationDeltaError> {
    let mut effects = Vec::new();
    let mut retired_allocations = Vec::new();
    let mut continued_tokens = Vec::new();
    // What the callee consumed is read where it was consumed: at the call's
    // entry. The post-call memory may have rewritten a pointer field the lent
    // resources owned, so an allocation named through it at the post state
    // is not the allocation the caller handed over.
    let expand_allocations =
        |resources: &ResourceContext, state: &ExecutionState, memory: &SymbolicMemory| {
            let projection_state = state
                .clone()
                .with_memory(memory.clone())
                .with_resource_context(resources.clone());
            expand_all_composite_resource_facts_at_state(
                resources,
                interface.composite_resource_definitions(),
                &projection_state,
                assumptions,
            )
        };
    let input =
        expand_allocations(input_resources, mutex_state, entry_memory).ok_or_else(|| {
            VerifiedAllocationDeltaError::Runtime(RuntimeError::FunctionContract(
                "could not inspect input allocation effects at call".to_string(),
            ))
        })?;
    let output = expand_allocations(output_resources, output_state, &memory).ok_or_else(|| {
        VerifiedAllocationDeltaError::Runtime(RuntimeError::FunctionContract(
            "could not inspect output allocation effects at call".to_string(),
        ))
    })?;
    let allocation_assumptions = input
        .observable_facts_assuming_valid(assumptions)
        .into_iter()
        .fold(assumptions.clone(), |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });
    let input_allocations = input
        .facts()
        .iter()
        .filter_map(|fact| {
            fact.allocation_size()
                .map(|(pointer, bytes)| (fact, pointer, bytes))
        })
        .collect::<Vec<_>>();
    // The caller's untouched resources are expanded only when the callee
    // consumed an allocation: they are what may still expose it, continue
    // it, or be left stale by its retirement. A call that consumes none
    // (an allocator, or a call on unrelated memory) never asks them, so it
    // costs nothing in the live objects the caller keeps; expanding them
    // anyway made every call linear in them.
    //
    // Returned projections describe the successor allocation. They decide
    // whether an input allocation continues, but they are not resources that
    // survived from the caller and therefore cannot be stale after the old
    // allocation is freed.
    let preserved = if input_allocations.is_empty() {
        ResourceContext::new()
    } else {
        expand_allocations(preserved_caller_resources, mutex_state, &memory).ok_or_else(|| {
            VerifiedAllocationDeltaError::Runtime(RuntimeError::FunctionContract(
                "could not inspect preserved caller allocation effects at call".to_string(),
            ))
        })?
    };
    // Every allocation this call returns or keeps is a continuity candidate
    // unless its block is proven distinct: a different block spelling is not
    // a different allocation (two reads of `p->data` are two blocks), and a
    // missed candidate would assert a free the contract never promised.
    // The call's own returned tokens, as the contract states them; a token
    // inside a returned composite is not one the caller holds directly.
    let returned_tokens = output_resources
        .facts()
        .iter()
        .filter(|fact| fact.allocation().is_some())
        .collect::<Vec<_>>();
    let output_allocations = output
        .facts()
        .iter()
        .chain(preserved.facts())
        .filter_map(|fact| {
            fact.allocation_size().map(|(base, bytes)| {
                (
                    base.address().clone(),
                    bytes,
                    returned_tokens.contains(&fact).then_some(fact),
                )
            })
        })
        .collect::<Vec<_>>();

    for (fact, pointer, bytes) in input_allocations {
        let base = pointer.address().clone();
        if output
            .cached_support_exposing_fact(fact, &allocation_assumptions)
            .is_some()
            || (preserved
                .cached_support_exposing_fact(fact, &allocation_assumptions)
                .is_some())
            || expose_composite_resource_fact(
                &output,
                fact,
                interface.composite_resource_definitions(),
                &memory,
                &allocation_assumptions,
            )
            .is_some()
        {
            // The call returns the consumed allocation. When it spells the
            // returned token by another block (`result` proven equal to
            // `p`), that token continues the consumed one, and its creation
            // anchor returns under the consumed block's name. Only the
            // call's own returned tokens are compared.
            for (output_base, output_bytes, returned) in &output_allocations {
                if let Some(returned) = returned
                    && output_base.base != base.base
                    && matches!(
                        allocation_continuity(
                            &base,
                            &bytes,
                            output_base,
                            output_bytes,
                            &allocation_assumptions,
                        ),
                        AllocationContinuity::Same
                    )
                    && !continued_tokens
                        .iter()
                        .any(|(token, _): &(ResourceFact, ResourceFact)| token == *returned)
                {
                    continued_tokens.push(((*returned).clone(), fact.clone()));
                }
            }
            continue;
        }
        let candidates = output_allocations
            .iter()
            .filter(|(output_base, _, _)| !base.blocks_proven_distinct(output_base))
            .collect::<Vec<_>>();
        let mut continuity_is_undecided = false;
        if !candidates.is_empty() {
            let mut retained = false;
            for (output_base, output_bytes, returned) in candidates {
                match allocation_continuity(
                    &base,
                    &bytes,
                    output_base,
                    output_bytes,
                    &allocation_assumptions,
                ) {
                    AllocationContinuity::Same => {
                        retained = true;
                        if let Some(returned) = returned
                            && output_base.base != base.base
                            && !continued_tokens.iter().any(|(token, _)| token == *returned)
                        {
                            continued_tokens.push(((*returned).clone(), fact.clone()));
                        }
                    }
                    AllocationContinuity::Distinct => {}
                    AllocationContinuity::Undecided(_) => continuity_is_undecided = true,
                    AllocationContinuity::Inconsistent => {
                        return Err(VerifiedAllocationDeltaError::InconsistentReturnedAllocation);
                    }
                    AllocationContinuity::CrossKind => {
                        return Err(VerifiedAllocationDeltaError::Runtime(
                            RuntimeError::FunctionContract(format!(
                                "the call consumes an allocation with {} byte count and returns \
                                 one that may be the same block with {} byte count; a heap \
                                 block's size keeps one format",
                                allocation_size_kind_spelling(bytes.kind()),
                                allocation_size_kind_spelling(output_bytes.kind()),
                            )),
                        ));
                    }
                }
            }
            if retained {
                continue;
            }
        }
        // Both retirement outcomes give up the input allocation's identity.
        // A retained caller resource must be separate from its entire extent.
        if let Some(resource) = caller_resource_left_stale_by_retirement(
            &input,
            &preserved,
            &base,
            &bytes,
            &allocation_assumptions,
        ) {
            return Err(VerifiedAllocationDeltaError::Runtime(
                RuntimeError::StaleResourceAfterFree {
                    resource: Box::new(resource.clone()),
                },
            ));
        }
        let allocation_range = bytes.byte_range(base.clone());
        // Suspended worker admission still checks before publishing its
        // separately recoverable state. Ordinary calls carry an obligation.
        if let Some(diagnostic) = worker_ledger.and_then(|ledger| {
            ledger.memory_access_refusal(
                &allocation_range,
                &allocation_assumptions,
                LoanRefusalOperation::MemoryAccess,
            )
        }) {
            return Err(VerifiedAllocationDeltaError::Runtime(
                RuntimeError::LoanRefusal(Box::new(diagnostic)),
            ));
        }
        if let Some(error) = super::mutexes::storage_retirement_refusal(
            mutex_state,
            &allocation_range,
            &allocation_assumptions,
        ) {
            return Err(VerifiedAllocationDeltaError::Runtime(error));
        }

        // The allocation token names the whole object. Spell its extent
        // through a byte pointer at the root, retaining the original address
        // and provenance but dropping any narrower pointer bounds.
        retired_allocations
            .push(allocation_range.with_pointer_carrier(&pointer.clone().with_root_bounds()));
        if continuity_is_undecided {
            // An undecided return admits a free, but does not assert one.
            memory = memory.retire_contract_heap_allocation_claim(
                &base,
                bytes.bytes(),
                &allocation_assumptions,
            );
            continue;
        }
        let before_free = memory.clone();
        if memory.live_heap_block_size(&base).is_none() {
            memory = memory
                .with_heap_allocation_claim(base.clone(), bytes.clone())
                .ok_or(VerifiedAllocationDeltaError::Runtime(
                    RuntimeError::InvalidFree(InvalidFree::NonHeapPointer),
                ))?;
        }
        memory = memory
            .free_heap_block(&base, assumptions)
            .map_err(|error| {
                VerifiedAllocationDeltaError::Runtime(RuntimeError::InvalidFree(error))
            })?;
        effects.push(ExecutionPureFact::internal(
            Proposition::HeapAllocationFreed {
                before: before_free,
                after: memory.clone(),
                allocation_base: base,
                bytes: bytes.clone(),
            },
        ));
    }

    // Only what the call returns can be a new allocation. An allocation one
    // of the caller's untouched resources exposes was the caller's before
    // the call, so this call has nothing to claim for it.
    for fact in output.facts() {
        if let Some(coverage) = fact.allocation_bounds_fact(&allocation_assumptions) {
            effects.push(ExecutionPureFact::new(coverage));
        }
        let Some((base, _)) = fact.allocation() else {
            continue;
        };
        if input.satisfies_fact(fact, &allocation_assumptions)
            || memory.live_heap_block_size(base).is_some()
        {
            continue;
        }
        let (_, bytes) = fact
            .allocation_size()
            .expect("an allocation token states its size");
        memory = memory
            .with_heap_allocation_claim(base.clone(), bytes)
            .ok_or_else(|| {
                VerifiedAllocationDeltaError::Runtime(RuntimeError::FunctionContract(
                    "returned allocation conflicts with an existing or deallocated identity"
                        .to_string(),
                ))
            })?;
    }
    Ok(VerifiedAllocationDelta {
        memory,
        effects: effects.into(),
        retired_allocations,
        continued_tokens,
    })
}

/// Replaces each returned allocation token that continues a consumed one by
/// the consumed token: the same allocation, spelled by the block the caller
/// lent.
fn with_continued_allocation_tokens(
    context: ResourceContext,
    continued_tokens: &[(ResourceFact, ResourceFact)],
) -> Option<ResourceContext> {
    continued_tokens
        .iter()
        .try_fold(context, |context, (returned, consumed)| {
            Some(
                context
                    .without_exact_representation(returned)?
                    .unchecked_with_fact(consumed.clone()),
            )
        })
}

/// The memory and facts after a verified call's allocation effects, with
/// the complete ranges of consumed allocations the call retires and, for each returned allocation
/// token proven to continue a consumed one under another block spelling
/// (`result` proven equal to `p`), that returned token and the consumed
/// token it continues.
struct VerifiedAllocationDelta {
    memory: SymbolicMemory,
    effects: ExecutionFacts,
    retired_allocations: Vec<MemoryRange>,
    continued_tokens: Vec<(ResourceFact, ResourceFact)>,
}

mod call_arguments;
pub(crate) use call_arguments::*;

/// Installs the stable global and static-local bindings needed by a function's
/// entry and contract states. Existing memory is preserved so nested calls
/// observe writes performed by their caller. Ordinary function entry declares
/// missing storage without restoring its initializer; reads then remain
/// symbolic until a caller state or a precondition constrains them. The
/// startup-only storage constructor passes `true` to materialize initializers.
/// Static locals use a function-qualified block identity and are therefore
/// initialized once for the whole symbolic execution, not once per call frame.
pub(crate) fn initialize_program_function_globals(
    state: &ExecutionState,
    function: &ProgramFunction,
) -> ExecutionState {
    initialize_program_function_globals_owned(state.clone(), function, false)
}

/// `memory` with the static-storage pointer `name` names cached as the read
/// of its cell: the load at its version point, which a read of it there
/// returns anyway. A resource clause based at the pointer seeds cells at the
/// address it holds; the cache keeps a later read of the pointer from asking
/// whether those seeded cells alias it. Function entry leaves static storage
/// without contents, so nothing else caches the read. Other names, and a cell
/// already held, leave `memory` unchanged.
pub(crate) fn with_static_pointer_read_cached(
    state: &ExecutionState,
    memory: SymbolicMemory,
    name: impl Into<BindingName>,
) -> SymbolicMemory {
    let name = name.into();
    let locals = state.locals();
    let (Some(program_type), Some(slot)) = (locals.object_type(&name), locals.slot(&name)) else {
        return memory;
    };
    if !locals.is_global_object(&name)
        || !program_type.is_object_pointer()
        || !slot.base.is_static_storage_block()
        || !memory.has_block(&slot.base)
        || memory.known_value(slot).is_some()
    {
        return memory;
    }
    let source = crate::kernel::intern_memory(memory.clone());
    memory.materialize_cell_from_source(slot.clone(), program_type, source)
}

/// Constructs a fresh startup state, never an ordinary call transition.
/// Storage identities coalesce aliases before permissions are issued. No
/// incoming state is accepted, so this cannot replenish consumed resources.
///
/// Startup storage is as large as the program's static objects, so each of
/// its per-object, per-element, and per-range loops is a cooperative
/// checkpoint. `None` means a run limit stopped construction; the partial
/// state is dropped and the caller reports the limit.
pub(crate) fn initialize_program_program_storage(
    functions: impl IntoIterator<Item = ProgramFunction>,
) -> Option<ExecutionState> {
    let mut state = ExecutionState::new();
    for function in functions {
        state = initialize_program_function_globals_owned(state, &function, true);
        // Private source spellings are lexical bindings, not program globals.
        state.locals = LocalEnvironment::default();
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
    }
    state.resources = initial_static_resources(&state.memory, || {})?;
    Some(state)
}

/// The blocks holding an array of structs laid out as the zero runs of
/// [`aggregate_array_zero_runs`] leave it: runs of one stride `stride` and
/// one count `count`, based within the first element, filling the block,
/// at least one of them stepping over more than its own cell, and every
/// concrete cell of the block a written field, of its run's width, at one of
/// the runs' slots. Every element then holds cells of the same widths at the
/// same offsets, so the block's cells repeat with period `stride` and the
/// block is one range of `count` struct-sized elements. Costs the block's
/// runs and concrete cells, not its elements.
fn periodic_struct_array_blocks(
    memory: &SymbolicMemory,
    constant_offset: impl Fn(&Address) -> u32,
) -> BTreeMap<AddressBase, (u32, u32)> {
    // Each run and each concrete cell examined charges a unit. Nothing here
    // stops early: the caller's next checkpoint, one visit later, does.
    let mut runs_by_block = BTreeMap::<&AddressBase, Vec<&CellRun>>::new();
    for run in memory.cells.runs() {
        crate::instrumentation::record_deterministic_work(1);
        runs_by_block.entry(&run.base().base).or_default().push(run);
    }
    let mut periodic = BTreeMap::new();
    for (block, runs) in runs_by_block {
        let (stride, count) = (runs[0].element_width(), runs[0].count());
        let strided = runs
            .iter()
            .any(|run| run.element_width() != run.value_width());
        let aligned = runs.iter().all(|run| {
            run.element_width() == stride
                && run.count() == count
                && constant_offset(run.base()) + run.value_width() <= stride
        });
        let fills_block = stride.checked_mul(count).is_some_and(|bytes| {
            memory
                .blocks
                .get(block)
                .and_then(|block| block.size().as_const())
                == Some(bytes)
        });
        if !strided || !aligned || !fills_block {
            continue;
        }
        let written_fields = AliasCandidates::only_block(block)
            .entries(memory.cells.concrete())
            .all(|(pointer, value)| {
                crate::instrumentation::record_deterministic_work(1);
                runs.iter().any(|run| {
                    run.slot_index(pointer).is_some() && run.value_width() == value.byte_width()
                })
            });
        if written_fields {
            periodic.insert(block.clone(), (stride, count));
        }
    }
    periodic
}

/// Partition physical storage using its initialized cell types. Adjacent
/// cells of one width form an ordinary typed array range; padding and opaque
/// union storage remain byte ranges.
///
/// The cells are read as the store holds them: a concrete cell is one span
/// of its width, and each stretch of a run's live slots is one span of
/// contiguous cells, so a million-element array initialized as one run
/// costs its stretches, not its elements.
///
/// The one exception to typing by cell width is an array of structs whose
/// elements all hold the same cells ([`periodic_struct_array_blocks`]): its
/// block is one range of struct-sized elements, which owns exactly the
/// bytes the per-field ranges would, padding included. Partitioned by cell
/// width it would be a range per field per element, so its permissions
/// would cost the array's length.
///
/// Every visit charges one unit and is a checkpoint; `None` means a run
/// limit stopped the partition.
fn initial_static_resources(
    memory: &SymbolicMemory,
    mut count_visit: impl FnMut(),
) -> Option<ResourceContext> {
    let mut visit = || {
        count_visit();
        crate::instrumentation::deadline_exceeded()
    };
    let constant_offset = |pointer: &Address| {
        let AddressOffset::Constant(offset) = pointer.offset else {
            unreachable!("static initializers have constant cell offsets");
        };
        u32::try_from(offset).expect("static cell offset")
    };
    // Each block's initialized spans: start, end and cell width.
    let mut spans_by_block = BTreeMap::<AddressBase, Vec<(u32, u32, u32)>>::new();
    // An array of structs whose every element holds the same cells is one
    // range of struct-sized elements, however many there are.
    let periodic = periodic_struct_array_blocks(memory, constant_offset);
    for (block, &(stride, count)) in &periodic {
        if visit() {
            return None;
        }
        spans_by_block
            .entry(block.clone())
            .or_default()
            .push((0, stride * count, stride));
    }
    for (pointer, value) in memory.cells.concrete().iter() {
        if visit() {
            return None;
        }
        if periodic.contains_key(&pointer.base) {
            continue;
        }
        let offset = constant_offset(pointer);
        spans_by_block
            .entry(pointer.base.clone())
            .or_default()
            .push((offset, offset + value.byte_width(), value.byte_width()));
    }
    for run in memory.cells.runs() {
        if periodic.contains_key(&run.base().base) {
            continue;
        }
        let spans = spans_by_block.entry(run.base().base.clone()).or_default();
        let width = run.value_width();
        for (low, high) in run.holes().gap_intervals(run.count()) {
            if visit() {
                return None;
            }
            if run.element_width() == width {
                let start = constant_offset(&run.slot_pointer(low));
                spans.push((start, start + (high - low) * width, width));
            } else {
                for index in low..high {
                    let start = constant_offset(&run.slot_pointer(index));
                    spans.push((start, start + width, width));
                }
            }
        }
    }
    for spans in spans_by_block.values_mut() {
        spans.sort_unstable();
    }
    // Startup data is built before a proof context exists. This structural
    // input is published at proof admission, not by a permission query.
    let mut resources = ResourceContext::default();
    for (identity, block) in memory.blocks.iter() {
        if visit() {
            return None;
        }
        let size = block.size().as_const().expect("static block size");
        let mut ranges = Vec::<(u32, u32, u32)>::new();
        let mut cursor = 0;
        for &(offset, span_end, width) in spans_by_block.get(identity).into_iter().flatten() {
            if visit() {
                return None;
            }
            assert!(offset >= cursor && span_end <= size);
            if offset > cursor {
                ranges.push((cursor, offset, 1));
            }
            if let Some((_, end, previous_width)) = ranges.last_mut()
                && *end == offset
                && *previous_width == width
            {
                *end = span_end;
            } else {
                ranges.push((offset, span_end, width));
            }
            cursor = span_end;
        }
        if cursor < size {
            ranges.push((cursor, size, 1));
        }
        for (start, end, width) in ranges {
            if visit() {
                return None;
            }
            let range = MemoryRange::new_with_element_width(
                Address {
                    base: identity.clone(),
                    offset: AddressOffset::Constant(i64::from(start)),
                },
                MachineTerm::constant(0),
                MachineTerm::constant((end - start) / width),
                width,
            );
            resources = resources.unchecked_with_fact(if block.is_read_only() {
                ResourceFact::view_memory(range)
            } else {
                ResourceFact::own_memory(range)
            });
        }
    }
    Some(resources)
}

#[cfg(test)]
mod program_entry_tests;

mod globals_and_aggregates;
pub(in crate::kernel) use globals_and_aggregates::*;

#[cfg(test)]
mod aggregate_union_copy_tests;

fn evaluate_resource_population_body_resources(
    required_resources: &ResourceContext,
    callee_state: &ExecutionState,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    include_ordinary: bool,
) -> ExecutionResult<Result<ResourceContext, RuntimeError>> {
    let mut body_resources = ResourceContext::new_with_equalities(assumptions);
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    for required in required_resources.facts() {
        let (name, arguments) = match required.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                continue;
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                (name, arguments)
            }
            Resource::Memory(_)
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_) => continue,
        };
        let Some(definition) = definitions
            .iter()
            .find(|definition| definition.name() == name)
        else {
            continue;
        };
        if !include_ordinary {
            continue;
        }
        if definition.parameters().len() != arguments.len() {
            return Ok(Err(RuntimeError::FunctionContract(format!(
                "counted population `{name}` received the wrong number of arguments"
            ))));
        }
        let mut population_state = callee_state.clone();
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let Some(argument) = argument.as_program_value() else {
                return Ok(Err(RuntimeError::TypeMismatch));
            };
            if parameter.program_type() != argument.program_type() {
                return Ok(Err(RuntimeError::TypeMismatch));
            }
            population_state.locals.set_typed(
                parameter.binding_name().clone(),
                argument.clone(),
                parameter.program_type(),
            );
        }
        let Some(body_active) = evaluate_composite_resource_body_condition(
            definition,
            &population_state,
            &evaluation_assumptions,
            budget,
        ) else {
            return Ok(Err(RuntimeError::FunctionContract(format!(
                "counted population `{name}` body condition is not decidable"
            ))));
        };
        if !body_active {
            continue;
        }
        for contained in definition.contains() {
            let fact = match evaluate_function_resource_spec(
                &population_state,
                contained,
                &evaluation_assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            if !body_resources.satisfies_fact(&fact, assumptions) {
                body_resources =
                    match body_resources.install_established_partition([fact], assumptions) {
                        Ok((resources, _)) => resources,
                        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
                    };
            }
        }
    }
    Ok(Ok(body_resources))
}

fn bind_contract_proof_arguments(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    argument_values: &[ProgramValue],
) -> Option<ExecutionState> {
    let mut callee_state =
        bind_program_function_arguments(caller_state, function, argument_values)?;
    if let Some(events) = caller_state
        .population_effects
        .creation
        .as_ref()
        .filter(|events| events.has_opaque_import())
    {
        Arc::make_mut(&mut callee_state.population_effects).creation =
            Some(events.enter_proof_entry());
    }
    Some(callee_state)
}

fn prepare_function_resource_transfer(
    caller_state: &ExecutionState,
    callee_state: &ExecutionState,
    function: &ProgramFunction,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
    purpose: ResourceTransitionPurpose,
) -> ExecutionResult<Result<FunctionResourceTransfer, RuntimeError>> {
    prepare_contract_resource_transfer(
        caller_state,
        callee_state,
        function.name(),
        function.contract_interface(),
        assumptions,
        budget,
        preserve_explicit_representation,
        purpose,
    )
}

/// Unfolds exactly the folded composite owners a call's own requirements
/// need, and nothing else.
///
/// The definitional transfer consumes each requirement with
/// [`consume_resource_fact_definitionally`], which unfolds a caller composite
/// on demand. The stable-view planner instead selects concrete backing before
/// it lends anything, so it needs the same frontier present as facts. Only a
/// composite whose expansion actually supplies an unsupported requirement is
/// opened, so an unrelated folded resource keeps its packaging and stays
/// re-foldable in the residual, and only non-recursive definitions are
/// opened, which keeps a recursive frontier an explicit refusal.
fn candidate_planning_resources(
    caller_resources: &ResourceContext,
    requirements: &[CheckedResourceFact],
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> ResourceContext {
    let supported = |resources: &ResourceContext, requirement: &CheckedResourceFact| {
        resources
            .directly_supporting_owned_entry(&requirement.fact, assumptions)
            .is_some()
            || (requirement.fact.is_view()
                && !resources
                    .view_occurrences_for_fact(&requirement.fact, assumptions)
                    .is_empty())
    };
    let mut resources = caller_resources.clone();
    for requirement in requirements {
        // A viewed composite requirement is lent folded, through the checked
        // composite backing, so opening it here would destroy the head that
        // is the restoration recipe. An owned composite requirement is
        // transferred, not lent: a held composite that contains it one level
        // down is opened to supply it, exactly as the definitional route
        // consumes it (the caller keeps the other pieces and refolds).
        if (requirement.fact.is_view()
            && matches!(requirement.fact.resource(), Resource::Composite { .. }))
            || supported(&resources, requirement)
        {
            continue;
        }
        // Exactly one level, and only the composite that actually answers
        // this requirement: an expansion that does not supply it is not a
        // reason to destroy its packaging.
        let opened = resources
            .facts()
            .iter()
            .filter(|fact| {
                fact.is_own()
                    && matches!(fact.resource(), Resource::Composite { name, .. }
                    if definitions.iter().any(|definition| {
                        definition.name() == name && !definition.is_recursive()
                    }))
            })
            .cloned()
            .collect::<Vec<_>>()
            .into_iter()
            .find_map(|composite| {
                crate::instrumentation::record_deterministic_work(1);
                expand_composite_resource_fact(
                    &resources,
                    &composite,
                    definitions,
                    &crate::kernel::ProgramPoint::of_memory(memory),
                    assumptions,
                )
                .filter(|expanded| supported(expanded, requirement))
            });
        if let Some(opened) = opened {
            resources = opened;
        }
    }
    resources
}

/// One checked owned-interface-to-viewed-implementation adapter for a
/// composite view (docs/internals/stable-views.md).
struct CompositeViewAdapter {
    /// The planning resources this adapter works from. Unchanged in the
    /// owned-composite form; in the materialized form the caller's covering
    /// owners have been replaced by the head below.
    resources: ResourceContext,
    /// The owned composite the lend escrows.
    head: ResourceFact,
    /// The viewed descriptions the loan permits beside its own head.
    adapted: Vec<ResourceFact>,
    /// What recovery hands back instead of the head, when the head was
    /// materialized for this call.
    restored: Vec<ResourceFact>,
}

/// Back a viewed composite `C(args)` the caller does not own by an owned
/// description of the same authority.
///
/// The rule: `C`'s kernel-checked one-level frontier, evaluated in the
/// caller's memory, must be covered piecewise by owned authority the caller
/// holds, and `C`'s definition facts must already hold at the call. They are
/// what `observe(C)` publishes inside the callee, so they are established
/// here rather than assumed. Two covering forms are admitted:
///
/// * an owned composite `D` in the caller whose own checked frontier covers
///   `C`'s: `D`'s head is escrowed and `views C(args)` becomes an additional
///   permitted description of that loan, exactly like a projection. Recovery
///   restores `D`;
/// * the caller's owned frontier itself: `owns C(args)` is materialized out
///   of exactly those facts for the call, and recovery restores them, so a
///   `views` requirement leaves the caller's packaging as it found it.
///
/// Anything else is refused by returning `None`, which leaves the ordinary
/// missing-backing diagnostic naming the viewed clause. A counted population
/// is refused: its body is population-wide, not one unit's frontier. So is a
/// borrowing composite, whose fold needs step 7's hold.
///
/// The materialized head carries no sidecar binding, so a hold a consumed
/// owned occurrence carried does not travel with it. That direction only
/// costs a later refusal -- the hold stays in the ledger and the loan behind
/// it cannot be ended -- and no owned frontier piece carries one today,
/// since a hold lives on the viewed piece an unfold hands it to.
fn candidate_composite_view_adapter(
    resources: &ResourceContext,
    required: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    caller_state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    unestablished: &mut Option<UnestablishedCompositeFact>,
) -> ExecutionResult<Option<CompositeViewAdapter>> {
    let Resource::Composite { name, arguments } = required.resource() else {
        return Ok(None);
    };
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == name)
    else {
        return Ok(None);
    };
    if definition.owns_population_authority()
        || definition.is_recursive()
        || !definition.facts_are_loan_stable()
    {
        return Ok(None);
    }
    let head = ResourceFact::own(required.resource().clone());
    let Some(frontier) = checked_one_level_frontier(&head, definitions, caller_state, assumptions)
    else {
        return Ok(None);
    };
    // An empty frontier protects nothing and is handled before planning; an
    // exclusive instance cannot be viewed at all (D12). A borrowing
    // composite -- one whose body views storage it does not own -- is step
    // 7's mechanism: folding one places a hold on the loan behind the viewed
    // piece, which this rule does not do, so it stays out of the adapter.
    if frontier.is_empty()
        || frontier
            .iter()
            .any(|child| !child.is_own() || matches!(child.resource(), Resource::Instance(_)))
    {
        return Ok(None);
    }
    let mut gap = None;
    let facts_hold = composite_definition_facts_hold(
        definition,
        &(arguments).native_values(),
        caller_state,
        assumptions,
        budget,
        &mut gap,
    )?;
    // A backing below is owned authority the view would be assembled from.
    // Where one exists but a body fact does not hold, the refusal names that
    // fact; a caller with no backing has nothing to assemble, and its
    // refusal stays the missing view.
    let mut refuse_for_the_fact = || {
        *unestablished = gap.take();
        Ok(None)
    };
    // The materialized form: the caller's own owners already cover the
    // frontier piecewise, so the head is exactly those facts under another
    // name and recovery gives them back unchanged.
    if let Some(remaining) = remove_frontier(resources.clone(), &frontier, assumptions)
        && let Ok(materialized) = remaining.try_compose_with_fact(head.clone(), assumptions)
    {
        if !facts_hold {
            return refuse_for_the_fact();
        }
        return Ok(Some(CompositeViewAdapter {
            resources: materialized,
            head,
            adapted: Vec::new(),
            restored: frontier,
        }));
    }
    // The owned-composite form: one folded owner in the caller whose checked
    // frontier covers this one. Only the caller's own composite facts are
    // examined, and each is expanded at most once.
    let owners = resources
        .facts()
        .iter()
        .filter(|fact| fact.is_own() && matches!(fact.resource(), Resource::Composite { .. }))
        .cloned()
        .collect::<Vec<_>>();
    for owner in owners {
        crate::instrumentation::record_deterministic_work(1);
        let Resource::Composite {
            name: owner_name, ..
        } = owner.resource()
        else {
            continue;
        };
        let Some(owner_definition) = definitions
            .iter()
            .find(|definition| definition.name() == owner_name)
        else {
            continue;
        };
        // An authority control's head is not the restoration recipe a lend
        // needs: restoring it must restore the authority's ledger state too.
        if owner_definition.owns_population_authority()
            || owner_definition.is_recursive()
            || !owner_definition.facts_are_loan_stable()
        {
            continue;
        }
        // The escrow has to name one occurrence, as a same-composite lend
        // does: two equal-looking owners are not the same authority (law 5).
        if resources.owned_occurrences_for_fact(&owner).len() != 1 {
            continue;
        }
        let Some(owner_frontier) =
            checked_one_level_frontier(&owner, definitions, caller_state, assumptions)
        else {
            continue;
        };
        if checked_frontier_coverage(owner_frontier, &frontier, assumptions).is_none() {
            continue;
        }
        if !facts_hold {
            return refuse_for_the_fact();
        }
        return Ok(Some(CompositeViewAdapter {
            resources: resources.clone(),
            head: owner,
            adapted: vec![required.clone()],
            restored: Vec::new(),
        }));
    }
    Ok(None)
}

/// The kernel's own one-level expansion of one owned composite head, read in
/// the caller's memory. This is the same boundary the composite lend and
/// `project` use, so nothing enters a loan that the definition does not
/// contain.
pub(super) fn checked_one_level_frontier(
    head: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    caller_state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<Vec<ResourceFact>> {
    // Expand only the selected head. Checked construction attaches the trusted
    // equality graph before dependent children are added, without importing the
    // caller's ambient resources or changing the loan's backing judgment.
    let singleton = ResourceContext::new()
        .try_compose_with_fact(head.clone(), assumptions)
        .ok()?;
    #[cfg(test)]
    singleton.observe_composite_context();
    let (_, children, _) = expand_composite_resource_fact_with_children(
        &singleton,
        head,
        definitions,
        &caller_state.program_point(),
        assumptions,
    )?;
    Some(children)
}

/// Consume the requested frontier from the owner's checked expansion alone.
/// The residual is proof-local; the adapter escrows and recovers the owner head.
pub(super) fn checked_frontier_coverage(
    owner_frontier: Vec<ResourceFact>,
    required: &[ResourceFact],
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    // This whole input has already been checked by expansion. Checked
    // construction retains the trusted graph's resource payload for coverage;
    // equality selects candidates, and ordinary consumption checks authority.
    let covering = ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(
        coalesce_written_resource_descriptions(owner_frontier, assumptions),
    );
    #[cfg(test)]
    covering.observe_composite_context();
    remove_frontier(covering, required, assumptions)
}

/// Removes a checked frontier from a context piecewise, or reports that the
/// context does not cover it. Each piece is consumed incrementally, so a
/// wider owned range is split rather than swallowed whole.
fn remove_frontier(
    mut resources: ResourceContext,
    frontier: &[ResourceFact],
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    for piece in frontier {
        crate::instrumentation::record_deterministic_work(1);
        resources = resources.without_fact_incrementally(piece, assumptions)?;
    }
    Some(resources)
}

struct UnestablishedCompositeFact {
    proposition: Proposition,
    source: Option<Box<ResourceBodyFactSource>>,
}

/// Whether a composite definition's body facts already hold at the call.
///
/// This mirrors what the surface `fold` requires of the facts it re-asserts:
/// each fact is lowered at the state the definition's parameters are bound
/// in and must be available by the kernel's exact routes. There is no search
/// here; a fact the caller has not established is a prompt refusal the proof
/// can answer with an explicit step.
/// The first missing fact keeps its lowered judgment and written clause,
/// with the call's argument bindings, for the assembly refusal.
fn composite_definition_facts_hold(
    definition: &CompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    caller_state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    unestablished: &mut Option<UnestablishedCompositeFact>,
) -> ExecutionResult<bool> {
    if definition.facts().is_empty() {
        return Ok(true);
    }
    if definition.parameters().len() != arguments.len() {
        return Ok(false);
    }
    let mut state = ExecutionState::at_point(&caller_state.program_point())
        .with_resource_context(caller_state.resources().clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let Some(argument) = argument.as_program_value() else {
            return Ok(false);
        };
        if parameter.program_type() != argument.program_type() {
            return Ok(false);
        }
        state.locals.set_typed(
            parameter.binding_name().clone(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    if bind_composite_witnesses(definition, arguments, &mut state, assumptions).is_none() {
        return Ok(false);
    }
    if evaluate_composite_resource_body_condition(definition, &state, assumptions, budget)
        != Some(true)
    {
        return Ok(false);
    }
    for (index, fact) in definition.facts().iter().enumerate() {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &state,
            fact,
            Some(&state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        let mut established = assumptions.clone();
        for load in &path.facts {
            established = established.assume_proposition(load.proposition().clone());
        }
        // The same exact routes a fold and a reassembled composite use
        // (`assembled_composite_body_facts_hold`): a quantified fact the
        // caller states is the body's up to its binder and the registered
        // loads that binder names.
        if !(contract_refinement_proves(&established, &path.proposition)
            || established.settles_exactly(&path.proposition)
            || resource_body_fact_is_established(&established, &path.proposition)
            || string_literal_fact_holds(&path.proposition, &mut Vec::new()))
        {
            let source = definition.fact_source_spelling(index).map(|spelling| {
                Box::new(ResourceBodyFactSource {
                    spelling: spelling.to_owned(),
                    bindings: definition
                        .parameters()
                        .iter()
                        .zip(arguments)
                        .map(|(parameter, argument)| {
                            (
                                parameter.name().to_owned(),
                                argument
                                    .as_program_value()
                                    .expect("the definition's C arguments were bound above")
                                    .clone(),
                            )
                        })
                        .collect(),
                })
            });
            *unestablished = Some(UnestablishedCompositeFact {
                proposition: path.proposition.clone(),
                source,
            });
            return Ok(false);
        }
    }
    Ok(true)
}

/// The values of the instance parameter at `position` for which a composite
/// over a string literal holds, its other arguments fixed: for `cstr_at(p,
/// len)` with `p` into a literal, the one `len` its bytes give. A literal has
/// no held instance, but its bytes decide the definition's facts, so the
/// call chooses the value they leave; the call then assembles the view from
/// the literal's bytes and checks those facts again. Every candidate value
/// lies within the literal, since the definition's frontier covers it.
fn string_literal_instance_values(
    definition: &CompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    position: usize,
    parameter_type: ProgramType,
    caller_state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProgramValue>> {
    if definition.is_recursive()
        || definition.owns_population_authority()
        || !definition.witnesses().is_empty()
        || definition.facts().is_empty()
    {
        return Ok(Vec::new());
    }
    let Some(remaining) = arguments.iter().enumerate().find_map(|(index, argument)| {
        let Some(ProgramValue::Pointer(pointer)) = argument.as_program_value() else {
            return None;
        };
        let pointer = pointer.address();
        let AddressBase::StringLiteral { bytes, .. } = &pointer.base else {
            return None;
        };
        let offset = usize::try_from(pointer.offset.as_const()?).ok()?;
        (index != position)
            .then(|| bytes.len().checked_sub(offset))
            .flatten()
    }) else {
        return Ok(Vec::new());
    };
    let mut values = Vec::new();
    for value in 0..remaining {
        crate::instrumentation::record_deterministic_work(1);
        let Some(candidate) = string_literal_instance_constant(parameter_type, value) else {
            return Ok(Vec::new());
        };
        let mut instance = arguments.to_vec();
        instance[position] = AlgebraicValue::Program(candidate.clone());
        if composite_definition_facts_hold(
            definition,
            &instance,
            caller_state,
            assumptions,
            budget,
            &mut None,
        )? {
            values.push(candidate);
        }
    }
    Ok(values)
}

fn string_literal_instance_constant(
    program_type: ProgramType,
    value: usize,
) -> Option<ProgramValue> {
    let value = u32::try_from(value).ok()?;
    Some(match program_type {
        ProgramType::UInt64 => ProgramValue::UInt64(MachineTerm::uint64_constant(u64::from(value))),
        ProgramType::Int64 => ProgramValue::Int64(MachineTerm::uint64_constant(u64::from(value))),
        ProgramType::UInt32 => ProgramValue::UInt32(MachineTerm::uint32_constant(value)),
        ProgramType::Int32 => ProgramValue::Int32(MachineTerm::constant(value)),
        _ => return None,
    })
}

/// Whether `fact` is a composite every piece of whose checked one-level
/// expansion is a range of string-literal bytes, and whose body facts those
/// bytes decide: a composite over read-only storage that holds by
/// construction, such as `cstr_at(p, len)` with `p` into a literal.
fn string_literal_composite_holds(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    let Resource::Composite { name, arguments } = fact.resource() else {
        return Ok(false);
    };
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == name)
    else {
        return Ok(false);
    };
    if definition.is_recursive()
        || definition.owns_population_authority()
        || !definition.witnesses().is_empty()
        || !definition.facts_are_loan_stable()
    {
        return Ok(false);
    }
    let literal_pointer = |argument: ResourceFieldValue<'_>| {
        matches!(argument.as_program_value(), Some(ProgramValue::Pointer(pointer))
            if matches!(pointer.address().base, AddressBase::StringLiteral { .. }))
    };
    let pointers_are_literal = arguments.iter().all(|argument| {
        !matches!(argument.as_program_value(), Some(ProgramValue::Pointer(_)))
            || literal_pointer(argument)
    });
    if !pointers_are_literal || !arguments.iter().any(literal_pointer) {
        return Ok(false);
    }
    let owned = ResourceFact::own(fact.resource().clone());
    let Some(frontier) = checked_one_level_frontier(&owned, definitions, state, assumptions) else {
        return Ok(false);
    };
    let within_literals = !frontier.is_empty()
        && frontier.iter().all(|piece| {
            let Some(range) = piece.memory_range() else {
                return false;
            };
            let (base, bytes) = range.byte_footprint();
            let AddressBase::StringLiteral { bytes: literal, .. } = &base.base else {
                return false;
            };
            match (base.offset.as_const(), bytes.as_const()) {
                (Some(start), Some(length)) => {
                    start >= 0
                        && start
                            .checked_add(i64::from(length))
                            .is_some_and(|end| end <= literal.len() as i64)
                }
                _ => false,
            }
        });
    if !within_literals {
        return Ok(false);
    }
    composite_definition_facts_hold(
        definition,
        &(arguments).native_values(),
        state,
        assumptions,
        budget,
        &mut None,
    )
}

/// The pieces of a viewed composite whose checked one-level expansion is
/// only memory in local blocks, as views, with the first body fact the
/// caller's state does not establish. The definition is restricted as for a
/// literal's view.
fn local_storage_composite_pieces(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<(Vec<ResourceFact>, Option<UnestablishedCompositeFact>)>> {
    let Resource::Composite { name, arguments } = fact.resource() else {
        return Ok(None);
    };
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == name)
    else {
        return Ok(None);
    };
    if definition.is_recursive()
        || definition.owns_population_authority()
        || !definition.witnesses().is_empty()
        || !definition.facts_are_loan_stable()
    {
        return Ok(None);
    }
    let owned = ResourceFact::own(fact.resource().clone());
    let Some(frontier) = checked_one_level_frontier(&owned, definitions, state, assumptions) else {
        return Ok(None);
    };
    let mut pieces = Vec::with_capacity(frontier.len());
    for piece in &frontier {
        let Some(range) = piece.memory_range() else {
            return Ok(None);
        };
        if !range.base().base.is_local_block() {
            return Ok(None);
        }
        pieces.push(ResourceFact::view_memory(range.clone()));
    }
    if pieces.is_empty() {
        return Ok(None);
    }
    let mut unestablished = None;
    if !composite_definition_facts_hold(
        definition,
        &(arguments).native_values(),
        state,
        assumptions,
        budget,
        &mut unestablished,
    )? && unestablished.is_none()
    {
        return Ok(None);
    }
    Ok(Some((pieces, unestablished)))
}

/// The widest string literal whose bytes a fact is decided over.
const STRING_LITERAL_FACT_BYTES: i64 = 4096;

/// Whether `proposition` holds of string-literal bytes alone. A literal's
/// block is read-only and holds the bytes its identity carries, so a read of
/// it at a constant in-bounds offset is that byte, in every state. A
/// universal over a bounded range is decided instance by instance, and every
/// leaf must then hold with no context: a load from any other storage, or at
/// an offset the bounds do not fix, leaves the fact undecided. The one
/// exception is `defined(...)` of a read at a constant offset, which also
/// holds when the read's state stores a value of its width at that cell. `bindings`
/// holds the enclosing universals' instantiated values, which the registered
/// address of a read inside them still names.
fn string_literal_fact_holds(
    proposition: &Proposition,
    bindings: &mut Vec<(Variable, MachineTerm)>,
) -> bool {
    string_literal_fact_value(proposition, bindings) == Some(true)
}

fn string_literal_fact_value(
    proposition: &Proposition,
    bindings: &mut Vec<(Variable, MachineTerm)>,
) -> Option<bool> {
    crate::instrumentation::record_deterministic_work(1);
    match proposition {
        Proposition::And(left, right) => Some(
            string_literal_fact_value(left, bindings)?
                && string_literal_fact_value(right, bindings)?,
        ),
        Proposition::Or(left, right) => Some(
            string_literal_fact_value(left, bindings)?
                || string_literal_fact_value(right, bindings)?,
        ),
        Proposition::Not(inner) => Some(!string_literal_fact_value(inner, bindings)?),
        Proposition::Implies(guard, conclusion) => {
            if !string_literal_fact_value(guard, bindings)? {
                return Some(true);
            }
            string_literal_fact_value(conclusion, bindings)
        }
        Proposition::ForAll { var, body, .. } => {
            // A body that holds whatever the variable is, such as one whose
            // guard is false, needs no instance.
            if string_literal_fact_value(body, bindings) == Some(true) {
                return Some(true);
            }
            let ranges = crate::kernel::reasoning::finite_forall_ranges_allowing_empty(
                std::slice::from_ref(var),
                body,
                true,
            )?;
            let [range] = ranges.as_slice() else {
                return None;
            };
            if range.upper.saturating_sub(range.lower) > STRING_LITERAL_FACT_BYTES {
                return None;
            }
            for value in range.lower..=range.upper {
                let constant = range.constant(value);
                let instance =
                    crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
                        body, *var, &constant,
                    );
                bindings.push((*var, constant));
                let holds = string_literal_fact_value(&instance, bindings);
                bindings.pop();
                if holds != Some(true) {
                    return holds.map(|_| false);
                }
            }
            Some(true)
        }
        // Every byte of a literal is initialized when its block is installed.
        Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
            ..
        } => {
            let pointer = string_literal_pointer_with_bindings(pointer, bindings);
            let offset = pointer.offset.as_const()?;
            let AddressBase::StringLiteral { bytes, .. } = &pointer.base else {
                // Any other read is defined when the state holds a stored
                // value of the read's width at that very cell, as a local
                // array's bytes after their stores do.
                let cell = Address {
                    base: pointer.base.clone(),
                    offset: AddressOffset::Constant(offset),
                };
                return match memory.load(&cell) {
                    ExpressionOutcome::Value(value)
                        if value.program_type().byte_width() == value_type.byte_width() =>
                    {
                        Some(true)
                    }
                    _ => None,
                };
            };
            let offset = usize::try_from(offset).ok()?;
            let width = usize::try_from(value_type.byte_width()).ok()?;
            (offset.checked_add(width)? <= bytes.len()).then_some(true)
        }
        Proposition::ConditionIs(..) => {
            let leaf = string_literal_reads_resolved(proposition, bindings)?;
            if crate::kernel::proof::fact_reasoning::normalizes_context_free(&leaf) {
                Some(true)
            } else if let Proposition::ConditionIs(condition, value) = &leaf
                && crate::kernel::proof::fact_reasoning::normalizes_context_free(
                    &Proposition::condition_is(condition.clone(), !value),
                )
            {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn string_literal_pointer_with_bindings(
    pointer: &Address,
    bindings: &[(Variable, MachineTerm)],
) -> Address {
    let mut pointer = pointer.clone();
    for (bound, value) in bindings {
        pointer = crate::kernel::reasoning::substitute_bitvector_variable_in_pointer(
            &pointer, *bound, value,
        );
    }
    pointer
}

/// `leaf` with each read of a string literal at a constant in-bounds offset
/// replaced by the byte there, or `None` when a read is of anything else.
fn string_literal_reads_resolved(
    leaf: &Proposition,
    bindings: &[(Variable, MachineTerm)],
) -> Option<Proposition> {
    let mut variables = BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_bitvector_variables(
        leaf,
        &mut variables,
    );
    let mut resolved = leaf.clone();
    for variable in variables {
        if !crate::kernel::is_load_variable(&variable) {
            continue;
        }
        let MachineTerm::MemoryLoad(_, pointer, kind) =
            crate::kernel::eval::registered_load_term_for_variable(&variable)?
        else {
            return None;
        };
        let pointer = string_literal_pointer_with_bindings(&pointer, bindings);
        let AddressBase::StringLiteral { bytes, .. } = &pointer.base else {
            return None;
        };
        let offset = pointer.offset.as_const()?;
        let byte = *bytes.get(usize::try_from(offset).ok()?)?;
        let value = match kind {
            LoadKind::UInt8 => MachineTerm::narrow_constant(
                crate::kernel::MachineIntegerType::UInt8,
                u128::from(byte),
            ),
            LoadKind::Int8 => MachineTerm::narrow_constant(
                crate::kernel::MachineIntegerType::Int8,
                u128::from(byte),
            ),
            _ => return None,
        };
        resolved = crate::kernel::reasoning::substitute_bitvector_variable_in_proposition(
            &resolved, variable, &value,
        );
    }
    Some(resolved)
}

/// Why a contract's resource transition is being prepared. The two purposes
/// consume the same declared requirements from the same caller context and
/// hand the callee the same authority; they differ only in whether the
/// caller lends. `call_site_and_function_boundary_transitions_agree_on_the_callee_entry`
/// pins that agreement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ResourceTransitionPurpose {
    /// A call site: the caller lends its authority, so the views the callee
    /// declares become loans of this application and recovery returns them.
    CallSite,
    /// A worker call suspended across pthread create/join. Reborrowing a
    /// caller view reserves a separate reader share while the parent keeps
    /// one for another child.
    SuspendedWorker,
    /// A function's own boundary: a whole-function judgment executes,
    /// certifies, or reads the body's outcome from the resources the contract
    /// declares, consumed definitionally. The loan roots of its input views
    /// come from the proof's entry construction
    /// (`execution_state_with_borrowed_contract_inputs`), never from this transition,
    /// so nothing is lent twice; no call-site transfer record exists for
    /// such a judgment to rebuild from.
    FunctionBoundary,
}

impl ResourceTransitionPurpose {
    fn lends(self) -> bool {
        self != Self::FunctionBoundary
    }
}

fn spec_contains_mutex_authority(
    interface: &FunctionContractInterface,
    spec: &ResourceSpec,
) -> bool {
    matches!(
        spec.family(),
        ResourceFamily::MutexGuard | ResourceFamily::MutexLive | ResourceFamily::MutexUse
    ) || spec.contained_definition_name().is_some_and(|name| {
        interface
            .composite_resource_definition(name)
            .is_some_and(|definition| definition.contains_mutex_authority)
    })
}

pub(crate) fn preserves_mutex_protocols(interface: &FunctionContractInterface) -> bool {
    interface
        .resource_requires()
        .iter()
        .any(|spec| spec_contains_mutex_authority(interface, spec))
}

pub(crate) fn guard_contract_refusal(
    interface: &FunctionContractInterface,
) -> Option<&'static str> {
    match super::mutexes::helper_contracts::classify(interface) {
        Ok(Some(_)) => return None,
        Err(message) => return Some(message),
        Ok(None) => {}
    }
    interface
        .resource_requires()
        .iter()
        .chain(interface.resource_ensures())
        .any(|spec| {
            spec_contains_mutex_authority(interface, spec)
                && (!matches!(
                    spec.family(),
                    ResourceFamily::Instance
                        | ResourceFamily::MutexGuard
                        | ResourceFamily::MutexLive
                        | ResourceFamily::MutexUse
                ) || spec.role() != ResourceTransferRole::Borrow
                    || spec.is_view())
        })
        .then_some("mutex authority contracts currently require preserving owned inputs")
}

fn private_aggregate_storage_owner(slot: Address, layout: &AggregateLayout) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new_with_element_width(
        slot,
        MachineTerm::constant(0),
        MachineTerm::constant(layout.size_bytes()),
        1,
    ))
}

fn with_private_aggregate_parameter_owners(
    mut resources: ResourceContext,
    callee: &ExecutionState,
    interface: &FunctionContractInterface,
) -> ResourceContext {
    // Only the selected parameters, never the caller's unrelated frame.
    // Argument binding has already allocated each slot independently.
    for parameter in interface.parameters() {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(layout) = parameter.aggregate_layout()
            && let Some(slot) = callee.locals.slot(parameter.binding_name().clone())
        {
            resources = resources
                .unchecked_with_fact(private_aggregate_storage_owner(slot.clone(), layout));
        }
    }
    resources
}

/// Prepares the resource transition of one contract application; see
/// [`ResourceTransitionPurpose`] for the two routes.
fn prepare_contract_resource_transfer(
    caller_state: &ExecutionState,
    callee_state: &ExecutionState,
    interface_name: &str,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
    purpose: ResourceTransitionPurpose,
) -> ExecutionResult<Result<FunctionResourceTransfer, RuntimeError>> {
    let transfer = prepare_contract_resource_transfer_unexplained(
        caller_state,
        callee_state,
        interface_name,
        interface,
        assumptions,
        budget,
        preserve_explicit_representation,
        purpose,
    )?;
    // SymbolicMemory a live mutex's initialization consumed is missing because the
    // mutex holds it; name the mutex rather than the bytes.
    // An allocation the caller holds only in the other size format is
    // named with both formats (D5). A wide range held in another element
    // width names the product that must not wrap.
    Ok(transfer.map_err(|error| match &error {
        RuntimeError::MissingResource { resource } => match resource.as_ref() {
            ResourceFact::Own(Resource::Memory(range), _) => {
                super::mutexes::consumed_storage_refusal(caller_state, range, assumptions)
                    .or_else(|| {
                        caller_state
                            .resources
                            .wide_range_respelling_refusal(range, assumptions)
                            .map(|no_wrap| {
                                RuntimeError::WideRangeRespellingMayWrap(Box::new(no_wrap))
                            })
                    })
                    .unwrap_or(error)
            }
            fact if fact.allocation().is_some() => {
                allocation_size_kind_refusal(&caller_state.resources, fact, assumptions)
                    .unwrap_or(error)
            }
            _ => error,
        },
        _ => error,
    }))
}

/// The refusal for a required `allocation(base, bytes)` whose block the
/// context holds with a byte count of the other format: a 32-bit (`int32`)
/// spelling of a 64-bit (`uint64`) block's size, or the reverse. Tokens of
/// different formats never match (`design/heap-allocation-sizes.md`, D5), so the
/// ordinary refusal would only report the token missing. The held token is
/// found by base through the context's argument index, as `free` finds it.
pub(in crate::kernel) fn allocation_size_kind_refusal(
    resources: &ResourceContext,
    required: &ResourceFact,
    assumptions: &PureFactContext,
) -> Option<RuntimeError> {
    let (required_base, required_size) = required.allocation_size()?;
    let query =
        ResourceFact::own_designated_allocation(required_base.clone(), &AllocationSize::int32(0));
    let held_kind = resources
        .direct_match_candidates_for(&query, assumptions)
        .into_iter()
        .filter_map(ResourceFact::allocation_size)
        .find(|(base, size)| {
            size.kind() != required_size.kind()
                && crate::kernel::resource_arguments_proven_equal(
                    &ProgramValue::Pointer((*base).clone().with_type(ProgramType::Int32Pointer))
                        .into(),
                    &ProgramValue::Pointer(
                        required_base.clone().with_type(ProgramType::Int32Pointer),
                    )
                    .into(),
                    assumptions,
                )
        })
        .map(|(_, size)| size.kind())?;
    Some(RuntimeError::FunctionContract(format!(
        "`allocation` states {} byte count, but the block's allocation token holds {} one: \
         a heap block's size keeps the format of its size's C type, and an `allocation` of \
         the other format does not name it; state the byte count in the block's format",
        allocation_size_kind_spelling(required_size.kind()),
        allocation_size_kind_spelling(held_kind),
    )))
}

/// How a diagnostic names a size format.
pub(in crate::kernel) fn allocation_size_kind_spelling(kind: AllocationSizeKind) -> &'static str {
    match kind {
        AllocationSizeKind::Int32 => "a 32-bit (`int32`)",
        AllocationSizeKind::UInt64 => "a 64-bit (`uint64`, `size_t`)",
    }
}

/// Retain the callee scope already established by argument binding. A
/// same-scope/independent transition carries no allocation-return authority.
fn checked_allocation_creator(
    caller: &ExecutionState,
    callee: &ExecutionState,
) -> Option<CreationEvents> {
    let caller = caller.population_effects.creation.as_ref()?;
    let callee = callee.population_effects.creation.as_ref()?;
    (!callee.same_invocation(caller)).then(|| callee.clone())
}

fn prepare_contract_resource_transfer_unexplained(
    caller_state: &ExecutionState,
    callee_state: &ExecutionState,
    _interface_name: &str,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
    purpose: ResourceTransitionPurpose,
) -> ExecutionResult<Result<FunctionResourceTransfer, RuntimeError>> {
    if let Some(message) = guard_contract_refusal(interface) {
        return Ok(Err(RuntimeError::FunctionContract(message.into())));
    }
    // Ordinary calls frame the caller's protocol ledgers through argument
    // binding and summary recovery. Their declared memory effects still pass
    // storage_write_refusal, and their resource requirements cannot manufacture
    // a guard or use permission. A helper receiving protected memory therefore
    // need not receive the lock itself. Suspended workers use a different
    // recovery path; retain its explicit protocol admission rule.
    if purpose == ResourceTransitionPurpose::SuspendedWorker
        && (caller_state.preserves_mutex_protocols
            || caller_state
                .mutex_ledger
                .as_ref()
                .is_some_and(super::mutexes::MutexLedger::has_any_mutex))
        && !preserves_mutex_protocols(interface)
    {
        return Ok(Err(RuntimeError::FunctionContract(
            "calls with live mutex protocols require contract protocol effects".into(),
        )));
    }
    if purpose.lends()
        && caller_state.loan_ledger().is_some() != caller_state.loan_participant().is_some()
    {
        return Ok(Err(RuntimeError::LoanRefusal(Box::new(
            LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Plan),
        ))));
    }
    // In particular, preparing several pure callback interfaces must not
    // repeatedly enumerate the caller's unrelated resource frame.
    if interface.resource_requires().is_empty() && !preserve_explicit_representation {
        return Ok(Ok(FunctionResourceTransfer {
            helper_call: None,
            borrowed_inputs: Vec::new(),
            consumed_inputs: Vec::new(),
            canonical_borrowed_owners: Vec::new(),
            consumed_cell_returns: ConsumedCellReturns::default(),
            allocation_creator: checked_allocation_creator(caller_state, callee_state),
            callee_resources: with_private_aggregate_parameter_owners(
                ResourceContext::new_with_equalities(assumptions),
                callee_state,
                interface,
            ),
            caller_resources_after_requirements: caller_state.resources().clone(),
            memory_effects: Vec::new(),
            resource_effect_bound: None,
            post_outputs: None,
            candidate_output_views: Vec::new(),
            returned_entry_partition: None,
            produced_borrowing_pieces: Vec::new(),
            stable_view_plan: None,
            checked_view_frontier: Vec::new(),
        }));
    }
    let preserve_explicit_representation = preserve_explicit_representation
        && interface
            .composite_resource_definitions()
            .iter()
            .any(CompositeResourceDefinition::is_recursive);
    // At a function's own boundary, a checked unfold may already have spent
    // a declared named input before C execution. Its exact receipt supplies
    // only input-clause evaluation; it never restores the live resource state.
    let mut input_evaluation_state = callee_state.clone();
    if purpose == ResourceTransitionPurpose::FunctionBoundary {
        input_evaluation_state.resource_bindings = caller_state.resource_bindings.clone();
    }
    let mut spent_named_inputs = BTreeSet::new();
    if purpose == ResourceTransitionPurpose::FunctionBoundary
        && let Some(events) = &callee_state.population_effects.creation
    {
        for spec in interface.resource_requires() {
            if spec.role() != ResourceTransferRole::Consume {
                continue;
            }
            let ResourceTerm::Instance {
                identity,
                schema,
                resource: inner_term,
                ..
            } = spec.term()
            else {
                continue;
            };
            if input_evaluation_state
                .owned_resource_instance(*identity)
                .is_some()
            {
                continue;
            }
            let inner = ResourceSpec::new(
                (**inner_term).clone(),
                ResourceAccessMode::Own,
                ResourceQuantity::One,
                spec.role(),
                spec.state_source(),
            )
            .expect("validated named resource body");
            let inner = match spec.source_arguments() {
                Some(arguments) => inner.with_source_arguments(arguments.to_vec()),
                None => inner,
            };
            let fact = match evaluate_function_resource_spec_with_entry(
                callee_state,
                callee_state,
                &inner,
                assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            let Resource::Composite { name, arguments } = fact.resource() else {
                continue;
            };
            let description =
                ResourceDescription::new(name.clone(), arguments.clone(), schema.clone());
            let actual = input_evaluation_state
                .resource_bindings
                .as_ref()
                .and_then(|bindings| bindings.get(identity))
                .copied()
                .unwrap_or(*identity);
            let Some(instance) = events.consumed_imported_instance(&description, actual) else {
                continue;
            };
            let fact = ResourceFact::own(Resource::Instance(instance.clone()));
            input_evaluation_state.resources = match input_evaluation_state
                .resources
                .try_compose_with_fact(fact, assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
            spent_named_inputs.insert(actual);
        }
    }
    let (mut required_resources, mut checked_required_resources) =
        match super::assumptions::capture_implicit_consulted_premises(|| {
            evaluate_function_resource_context_with_metadata(
                &input_evaluation_state,
                interface.resource_requires(),
                interface.composite_resource_definitions(),
                assumptions,
                budget,
            )
        })? {
            Ok(resources) => resources,
            Err(error) => return Ok(Err(error)),
        };
    for checked in &checked_required_resources {
        if checked.role == ResourceTransferRole::Consume
            && let Resource::Instance(instance) = checked.fact.resource()
            && spent_named_inputs.contains(&instance.identity())
        {
            required_resources = required_resources
                .without_fact_incrementally(&checked.fact, assumptions)
                .expect("evaluated consumed named clause");
        }
    }
    let mut canonical_population_owners = Vec::new();
    {
        let quantity_input = authority_quantity_exchange_effects(interface).and_then(|effects| {
            interface
                .resource_requires()
                .iter()
                .position(|spec| std::ptr::eq(spec, effects[0].1))
        });
        for checked in &mut checked_required_resources {
            let Resource::Composite { name, .. } = checked.fact.resource() else {
                continue;
            };
            let is_control =
                interface
                    .composite_resource_definition(name)
                    .is_some_and(|definition| {
                        definition.contains().iter().any(|child| {
                            matches!(child.term(), ResourceTerm::PopulationAuthority { .. })
                        })
                    });
            if caller_state
                .resources()
                .exact_resource_facts(checked.fact.resource())
                .into_iter()
                .any(|fact| fact.is_own())
            {
                continue;
            }
            let Some(source) = caller_state
                .resources()
                .directly_supporting_fact(&checked.fact, assumptions)
                .or_else(|| {
                    // Two units may be held as separate facts. A unit supplier
                    // identifies their exact population, not the requested
                    // quantity: ordinary partitioning and ledger transfer still
                    // require the full original input quantity below.
                    if quantity_input == checked.section_index && quantity_input.is_some() {
                        caller_state.resources().directly_supporting_fact(
                            &ResourceFact::own(checked.fact.resource().clone()),
                            assumptions,
                        )
                    } else {
                        None
                    }
                })
            else {
                continue;
            };
            if is_control {
                let definition = interface
                    .composite_resource_definition(name)
                    .expect("checked control definition");
                if caller_state
                    .checked_authority_wrapper_body(source, definition, assumptions)
                    .is_err()
                {
                    continue;
                }
            } else {
                let Resource::Composite { name, arguments } = source.resource() else {
                    continue;
                };
                let description = ResourceDescription::new(
                    name.clone(),
                    arguments.clone(),
                    ResourceFieldSchema::new(vec![]).expect("empty schema"),
                );
                if !caller_state
                    .population_effects
                    .creation
                    .as_ref()
                    .is_some_and(|events| events.tracks_population(&description))
                {
                    continue;
                }
            }
            let ResourceFact::Own(_, quantity) = &checked.fact else {
                continue;
            };
            let canonical = ResourceFact::Own(source.resource().clone(), quantity.clone());
            if canonical == checked.fact {
                continue;
            }
            let original = checked.fact.clone();
            required_resources = required_resources
                .without_fact_incrementally(&original, assumptions)
                .expect("checked contract clause is retained");
            required_resources =
                match required_resources.try_compose_with_fact(canonical.clone(), assumptions) {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(resource_context_runtime_error(error))),
                };
            canonical_population_owners.push((original, canonical.clone()));
            checked.fact = canonical;
        }
    }
    // Keep a named mutex-use requirement tied to the exact caller occurrence
    // selected by its call map. The ordinary planner may choose an anonymous
    // use by address, but a written alias must never be silently redirected.
    for checked in &mut checked_required_resources {
        let Some(index) = checked.section_index else {
            continue;
        };
        let Some(spec) = interface.resource_requires().get(index) else {
            continue;
        };
        let Some((formal, _)) = spec.mutex_authority_binding() else {
            continue;
        };
        if !matches!(checked.fact.resource(), Resource::MutexUse(_)) {
            continue;
        }
        let Some(actual) = callee_state
            .resource_bindings
            .as_ref()
            .and_then(|bindings| bindings.get(&formal))
            .copied()
        else {
            continue;
        };
        let Some(source) = caller_state.resolve_named_mutex_authority(actual) else {
            return Ok(Err(RuntimeError::MissingResource {
                resource: Box::new(checked.fact.clone()),
            }));
        };
        checked.selected_mutex_source = Some(std::sync::Arc::new((actual, source.clone())));
    }
    let helper_contract = match super::mutexes::helper_contracts::classify(interface) {
        Ok(contract) => contract,
        Err(message) => return Ok(Err(RuntimeError::FunctionContract(message.into()))),
    };
    if helper_contract.is_some() && purpose == ResourceTransitionPurpose::SuspendedWorker {
        return Ok(Err(RuntimeError::FunctionContract(
            "mutex guards cannot transfer across a worker boundary".into(),
        )));
    }
    let helper_call = if purpose == ResourceTransitionPurpose::CallSite {
        if let Some(contract) = helper_contract {
            let Some(checked) = checked_required_resources
                .iter_mut()
                .find(|checked| matches!(checked.fact.resource(), Resource::MutexUse(_)))
            else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "mutex helper requires checked use authority".into(),
                )));
            };
            let Some(selected) = checked.selected_mutex_source.as_ref() else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "mutex helper requires named access transport".into(),
                )));
            };
            let source = selected.1.clone();
            let required = checked.fact.clone();
            if let Err(error) = super::mutexes::helper_contracts::check_call_access(
                caller_state,
                &source,
                &required,
                contract.effect,
                assumptions,
            ) {
                let Resource::MutexUse(usage) = required.resource() else {
                    unreachable!()
                };
                return Ok(Err(error.into_runtime_error(&usage.mutex)));
            }
            required_resources = required_resources
                .without_fact_delaying_normalization(&required, assumptions)
                .expect("checked helper use is in its requirement context");
            required_resources = match required_resources
                .try_compose_with_facts_delaying_normalization([source.clone()], assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
            checked.fact = source.clone();
            let guard = checked_required_resources.iter().find_map(|checked| {
                matches!(checked.fact.resource(), Resource::MutexGuard(_))
                    .then(|| checked.fact.clone())
            });
            Some(Arc::new(super::mutexes::helper_contracts::HelperCall {
                contract,
                source,
                required,
                guard,
            }))
        } else {
            None
        }
    } else {
        None
    };
    // Role is section semantics, not a decoration on the access mode.  A
    // viewed fact can only be borrowed, while an owned fact may be either a
    // consumed transfer or an entry borrow returned by the contract.  A
    // produced input, or a post-state requirement, is malformed and is
    // rejected before any residual or effect projection is built.
    if checked_required_resources.iter().any(|checked| {
        checked.role == ResourceTransferRole::Produce
            || checked.state_source == ResourceStateSource::Post
            || (checked.fact.is_view() && checked.role != ResourceTransferRole::Borrow)
    }) {
        return Ok(Err(RuntimeError::FunctionContract(
            "resource requirement has an inconsistent transfer role".to_string(),
        )));
    }
    // Implicit local storage authority has no owned fact to escrow. At a
    // call site it backs a checked local loan, so writes and lifetime ends
    // remain blocked even when a worker outlives the call. Read-only storage
    // retains intrinsic read authority. An explicitly supplied owner or view
    // takes the ordinary lend/reborrow route, including stale-binding checks.
    let unsupplied_local = |range: &MemoryRange| {
        range.base().base.is_local_block()
            && callee_state.memory().has_block(&range.base().base)
            && !callee_state
                .memory()
                .requires_explicit_scalar_ownership(range.base())
            && caller_state
                .resources()
                .has_no_explicit_memory_for_local_storage(&range.base().base, assumptions)
    };
    let implicit_read_views = checked_required_resources
        .iter()
        .filter(|requirement| {
            matches!(
                requirement.fact.resource(),
                Resource::Memory(range)
                    if requirement.fact.is_view()
                        && (unsupplied_local(range)
                            || callee_state.memory().is_read_only_block(&range.base().base))
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    let mut implicit_read_views = implicit_read_views;
    // A view of a composite whose every piece is string-literal storage, such
    // as `cstr_at` of a literal, is intrinsic read authority on the same
    // terms: the literal's bytes decide the body's facts, and nothing can
    // write them.
    for requirement in &checked_required_resources {
        if requirement.fact.is_view()
            && !implicit_read_views.contains(requirement)
            && string_literal_composite_holds(
                &requirement.fact,
                interface.composite_resource_definitions(),
                callee_state,
                assumptions,
                budget,
            )?
        {
            implicit_read_views.push(requirement.clone());
            continue;
        }
        // A view of a composite whose every piece is implicit local storage,
        // such as `cstr_at` of a local `char` array, is backed the way a view
        // of those bytes is: each piece is lent as a checked local loan, and
        // the composite itself needs no owner. Its body facts are the
        // caller's to establish at the call.
        if requirement.fact.is_view()
            && !implicit_read_views.contains(requirement)
            && caller_state
                .resources()
                .directly_supporting_owned_entry(&requirement.fact, assumptions)
                .is_none()
            && caller_state
                .resources()
                .view_occurrences_for_fact(&requirement.fact, assumptions)
                .is_empty()
            && let Some((pieces, unestablished)) = local_storage_composite_pieces(
                &requirement.fact,
                interface.composite_resource_definitions(),
                callee_state,
                assumptions,
                budget,
            )?
            && pieces.iter().all(|piece| {
                piece.memory_range().is_some_and(|range| {
                    unsupplied_local(range)
                        // Bytes the caller holds through any resource, such
                        // as a folded composite over part of the array, are
                        // not implicit local storage.
                        && caller_state
                            .resources()
                            .facts_that_may_refer_to_memory_block(&range.base().base)
                            .next()
                            .is_none()
                })
            })
        {
            // The caller holds the bytes but not a body fact: name it, as a
            // refused `fold` and an assembly from owned pieces do.
            if let Some(fact) = unestablished {
                return Ok(Err(RuntimeError::UnestablishedAssemblyFact {
                    assembled: Box::new(requirement.fact.clone()),
                    fact: Box::new(fact.proposition),
                    source: fact.source,
                }));
            }
            implicit_read_views.push(requirement.clone());
            for piece in pieces {
                let piece = CheckedResourceFact {
                    fact: piece,
                    role: ResourceTransferRole::Borrow,
                    state_source: requirement.state_source,
                    clause_position: requirement.clause_position,
                    section_index: requirement.section_index,
                    selected_mutex_source: None,
                };
                if !implicit_read_views.contains(&piece) {
                    implicit_read_views.push(piece);
                }
            }
        }
    }
    let (local_read_views, intrinsic_read_views): (Vec<_>, Vec<_>) = implicit_read_views.into_iter()
        .partition(|requirement| matches!(requirement.fact.resource(), Resource::Memory(range)
            if range.base().base.is_local_block() && !callee_state.memory().is_read_only_block(&range.base().base)));
    // A composite view whose checked body is empty on this path protects no
    // bytes and holds no token, so there is nothing to lend and nothing a
    // loan could suspend (D6: an empty permission grants no dereference).
    // Demanding backing for it would turn the empty witness of a partial
    // recursive resource into a missing-backing refusal and hide the
    // structural validation that is the real verdict on such a call. Such a
    // requirement is discharged by definitional expansion instead.
    let empty_composite_views = if purpose.lends() {
        checked_required_resources
            .iter()
            .filter(|requirement| {
                requirement.fact.is_view()
                    && matches!(requirement.fact.resource(), Resource::Composite { .. })
                    && expand_all_composite_resource_facts(
                        &ResourceContext::new_with_equalities(assumptions)
                            .unchecked_with_fact(requirement.fact.clone()),
                        interface.composite_resource_definitions(),
                        &callee_state.program_point(),
                        assumptions,
                    )
                    .is_some_and(|expanded| expanded.facts().is_empty())
            })
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // D9: effects cannot overlap checked views. Implicit locals and read-only
    // storage have no owned occurrence in the caller's partition, so their
    // ranges need arithmetic separation rather than the distinct-owner rule.
    // Empty composite views protect no bytes; other composite frontiers are
    // added by the ordinary planner below.
    let mut checked_view_frontier = if purpose.lends() {
        intrinsic_read_views
            .iter()
            .chain(local_read_views.iter())
            .chain(empty_composite_views.iter())
            .filter_map(|requirement| Some((requirement.fact.memory_range().cloned()?, None)))
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // A population's cardinality lives in the population authority
    // (`crate::kernel::population_authority`), not in the resource algebra:
    // the caller holds one representative unit whose quantity is the unit,
    // while `N of p` is discharged definitionally. The stable
    // planner's exclusive reservation asks for one owned entry that directly
    // entails the whole requirement, which no representative can supply for a
    // symbolic or non-unit constant quantity, so such a requirement takes the
    // definitional route. A token population protects no memory, so the
    // ledger has nothing to say about it; a population whose body owns memory
    // is still checked against the active loans after planning.
    let population_quantity_requirements = if purpose.lends() {
        checked_required_resources
            .iter()
            .filter(|requirement| requirement_is_population_quantity(requirement))
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // A conditional composite whose guard the assumptions decide false has an
    // empty body on this path: it names no bytes, holds no token, and is
    // entailed by the empty context. That is why the definitional route
    // discharges `owns owned_item(null)` under `if item != 0` with nothing at
    // all, while the planner's exclusive reservation would demand a direct
    // owned entry for it and refuse. This is not weaker than the reservation:
    // only a decided guard collapses the body, and an undecided guard leaves
    // the composite folded, so the expansion is not empty and the requirement
    // keeps its entry. The caller residual is still consumed definitionally
    // below.
    let definitionally_empty_owned = if purpose.lends() {
        checked_required_resources
            .iter()
            .filter(|requirement| {
                requirement.fact.is_own()
                    && matches!(requirement.fact.resource(), Resource::Composite { .. })
                    && expand_all_composite_resource_facts(
                        &ResourceContext::new_with_equalities(assumptions)
                            .unchecked_with_fact(requirement.fact.clone()),
                        interface.composite_resource_definitions(),
                        &callee_state.program_point(),
                        assumptions,
                    )
                    .is_some_and(|expanded| expanded.facts().is_empty())
            })
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    let local_read_facts = local_read_views
        .iter()
        .map(|view| &view.fact)
        .collect::<std::collections::BTreeSet<_>>();
    let stable_requirements = checked_required_resources
        .iter()
        .filter(|requirement| {
            !intrinsic_read_views.contains(requirement)
                && !local_read_facts.contains(&requirement.fact)
                && !empty_composite_views.contains(requirement)
                && !population_quantity_requirements.contains(requirement)
                && !definitionally_empty_owned.contains(requirement)
        })
        .cloned()
        .collect::<Vec<_>>();
    let mut planning_resources = if purpose.lends() {
        candidate_planning_resources(
            caller_state.resources(),
            &stable_requirements,
            interface.composite_resource_definitions(),
            caller_state.memory(),
            assumptions,
        )
    } else {
        caller_state.resources().clone()
    };
    let stable_view_plan = if purpose.lends() {
        let (ledger, caller) = match (
            caller_state.loan_ledger().cloned(),
            caller_state.loan_participant(),
        ) {
            (Some(ledger), Some(caller)) => (ledger, caller),
            _ => {
                let ledger = LoanLedger::new();
                let Ok(caller) = ledger.fresh_participant() else {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "could not allocate stable-view caller participant".to_string(),
                    )));
                };
                (ledger, caller)
            }
        };
        let Ok(callee) = ledger.fresh_participant() else {
            return Ok(Err(RuntimeError::FunctionContract(
                "could not allocate stable-view callee participant".to_string(),
            )));
        };
        // A viewed composite the caller would assemble from its owned
        // pieces, mapped to the first body fact it has not established.
        let mut assembly_gaps = BTreeMap::new();
        let composite_backings = if stable_requirements.iter().any(|requirement| {
            requirement.fact.is_view()
                && matches!(requirement.fact.resource(), Resource::Composite { .. })
        }) {
            let mut backings = BTreeMap::new();
            for requirement in stable_requirements.iter().filter(|requirement| {
                requirement.fact.is_view()
                    && matches!(requirement.fact.resource(), Resource::Composite { .. })
            }) {
                // Prefer the caller's own owner for this very composite.
                // Only when there is none does the adapter look for another
                // owned description of the same authority (docs/internals/stable-views.md).
                let mut adapted = Vec::new();
                let mut restored = Vec::new();
                let mut selected = requirement.fact.clone();
                if planning_resources
                    .directly_supporting_owned_entry(&requirement.fact, assumptions)
                    .is_none()
                    // A view the caller already holds is reborrowed from its
                    // own binding, which needs no backing of its own.
                    && planning_resources
                        .view_occurrences_for_fact(&requirement.fact, assumptions)
                        .is_empty()
                {
                    let mut unestablished = None;
                    match candidate_composite_view_adapter(
                        &planning_resources,
                        &requirement.fact,
                        interface.composite_resource_definitions(),
                        caller_state,
                        assumptions,
                        budget,
                        &mut unestablished,
                    )? {
                        Some(adapter) => {
                            planning_resources = adapter.resources;
                            selected = adapter.head;
                            adapted = adapter.adapted;
                            restored = adapter.restored;
                        }
                        None => {
                            if let Some(fact) = unestablished {
                                assembly_gaps.insert(requirement.fact.clone(), fact);
                            }
                            continue;
                        }
                    }
                }
                let Some((support, owned)) = planning_resources
                    .directly_supporting_owned_entry(&selected, assumptions)
                    .map(|(support, owned)| (support, owned.clone()))
                else {
                    continue;
                };
                let owned = &owned;
                // One checked level: primitive children enter the write
                // index, nested composite children become permitted
                // descriptions that projection can open later. The head's
                // escrow protects everything under it, so nothing deeper
                // needs enumerating.
                let singleton = ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(owned.clone());
                let Some((_, expanded_children, _)) = expand_composite_resource_fact_with_children(
                    &singleton,
                    owned,
                    interface.composite_resource_definitions(),
                    &caller_state.program_point(),
                    assumptions,
                ) else {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "could not check the frontier of a composite view".to_string(),
                    )));
                };
                // A viewed piece is a description the head packages (a
                // borrowing composite, step 7): it has no owner here to
                // escrow, so it enters the loan as a permitted description
                // with no byte backing, protected by the hold its head keeps.
                if expanded_children
                    .iter()
                    .any(|fact| matches!(fact.resource(), Resource::Instance(_)))
                {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "an exclusive instance inside a composite view is unsupported".to_string(),
                    )));
                }
                // The folded head names no bytes of its own, so these checked
                // pieces are the frontier a declared mutable effect has to
                // stay out of. They are recorded before the backing consumes
                // them and only kept once the backing is accepted below. Each
                // piece carries the head's own support: the pieces are that
                // one owned occurrence's bytes, so an effect reserved from a
                // different occurrence is disjoint from them by the partition
                // invariant, exactly as it is from the head.
                let frontier_pieces = expanded_children
                    .iter()
                    .filter_map(|piece| Some((piece.memory_range().cloned()?, Some(support))))
                    .collect::<Vec<_>>();
                let Some(definition) =
                    interface
                        .composite_resource_definitions()
                        .iter()
                        .find(|definition| {
                            matches!(
                                owned.resource(),
                                Resource::Composite { name, .. } if definition.name() == name
                            )
                        })
                else {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "composite loan definition is missing".to_string(),
                    )));
                };
                // Recovery restores the exact escrowed head, so its facts are
                // re-asserted precisely as folded; that is sound only when
                // everything a fact depends on is stable for the loan.
                if !definition.facts_are_loan_stable() {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "composite body facts depend on a resource count or an allocation-liveness claim, which a stable loan does not stabilize".to_string(),
                    )));
                }
                let Some(backing) = CompositeLoanBacking::from_checked_adapter(
                    support,
                    owned.clone(),
                    expanded_children,
                    adapted,
                    restored,
                ) else {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "composite loan frontier is not a checked expansion".to_string(),
                    )));
                };
                checked_view_frontier.extend(frontier_pieces);
                backings.insert(support, backing);
            }
            backings
        } else {
            BTreeMap::new()
        };
        match plan_stable_view_transfer_with_protocol_effect(
            &planning_resources,
            &stable_requirements,
            assumptions,
            &ledger,
            caller,
            callee,
            caller_state.loan_view_bindings(),
            &composite_backings,
            purpose == ResourceTransitionPurpose::SuspendedWorker,
            helper_call.is_some(),
        ) {
            Ok(mut plan) => {
                if helper_call.is_some()
                    && (plan.has_stable_views() || !plan.transferred_holds.is_empty())
                {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "unsupported mutex helper call: stable views and borrowing resources are not supported".into())));
                }
                for use_plan in &plan.mutex_uses {
                    let fact = use_plan.source_resource();
                    let mutex = match fact.resource() {
                        Resource::MutexUse(identity) => &identity.mutex,
                        Resource::MutexLive(identity) => &identity.mutex,
                        _ => unreachable!("checked use call source"),
                    };
                    if let Some(error) = super::mutexes::acquisition_availability_refusal(
                        caller_state,
                        mutex,
                        assumptions,
                    ) {
                        return Ok(Err(error.into_runtime_error(mutex)));
                    }
                }
                if let Some(protocols) = &caller_state.mutex_ledger {
                    for use_plan in &mut plan.mutex_uses {
                        if let Err(error) = use_plan.bind_interface(protocols) {
                            return Ok(Err(match error {
                                super::loans::mutex_calls::MutexUseCallError::Unavailable(
                                    message,
                                ) => RuntimeError::FunctionContract(message.into()),
                                _ => RuntimeError::MissingResource {
                                    resource: Box::new(use_plan.source_resource().clone()),
                                },
                            }));
                        }
                    }
                }
                for use_plan in &plan.mutex_uses {
                    if use_plan.check_protected_type(assumptions).is_err() {
                        return Ok(Err(RuntimeError::MissingResource {
                            resource: Box::new(use_plan.required_resource()),
                        }));
                    }
                }
                // Argument binding may have created a fresh by-value aggregate
                // copy. Its views are backed by that checked entry allocation,
                // which does not exist in the caller's earlier memory. The
                // entry memory also retains the caller's original local blocks.
                let local_worker_bindings = if purpose == ResourceTransitionPurpose::SuspendedWorker
                {
                    Some(
                        local_read_views
                            .iter()
                            .filter_map(|requirement| {
                                caller_state
                                    .thread_ledger
                                    .as_ref()?
                                    .local_view_binding(&requirement.fact)
                                    .map(|binding| (requirement.fact.clone(), binding.clone()))
                            })
                            .collect::<BTreeMap<_, _>>(),
                    )
                } else {
                    None
                };
                if let Err(error) = plan.lend_local_views_with_worker_shares(
                    callee_state.memory(),
                    &local_read_views,
                    assumptions,
                    local_worker_bindings.as_ref(),
                ) {
                    return Ok(Err(match error {
                        super::loans::StableViewPlanError::MissingResource(resource) => {
                            RuntimeError::MissingResource {
                                resource: Box::new(resource),
                            }
                        }
                        super::loans::StableViewPlanError::UnestablishedOwnedBoundary(required) => {
                            resource_context_runtime_error(
                                ResourceContextValidityError::UnestablishedOwnedBoundary(required),
                            )
                        }
                        error => error
                            .loan_diagnostic(LoanRefusalOperation::Plan)
                            .map(|refusal| RuntimeError::LoanRefusal(Box::new(refusal)))
                            .unwrap_or_else(|| {
                                RuntimeError::FunctionContract(
                                    "local view loan could not be checked".to_string(),
                                )
                            }),
                    }));
                }
                if let Err(error) = plan.recheck_entry(&ledger) {
                    return Ok(Err(RuntimeError::LoanRefusal(Box::new(
                        error.diagnostic(LoanRefusalOperation::Entry),
                    ))));
                }
                Some(plan)
            }
            Err(error) => {
                // An owned requirement the caller cannot supply is a missing
                // owner, whatever planned it: name the fact, as the ordinary
                // resource transfer does, rather than a loan the call never
                // asked for. A view the planner cannot back is a loan matter.
                if let super::loans::StableViewPlanError::MissingResource(resource) = &error
                    && resource.is_own()
                {
                    return Ok(Err(RuntimeError::MissingResource {
                        resource: Box::new(resource.clone()),
                    }));
                }
                // A view the caller holds the pieces of, but could not
                // assemble because a body fact is unproved: name that fact,
                // as a refused `fold` does, rather than the missing loan.
                if let super::loans::StableViewPlanError::MissingResource(resource) = &error
                    && let Some(fact) = assembly_gaps.remove(resource)
                {
                    return Ok(Err(RuntimeError::UnestablishedAssemblyFact {
                        assembled: Box::new(resource.clone()),
                        fact: Box::new(fact.proposition),
                        source: fact.source,
                    }));
                }
                if let super::loans::StableViewPlanError::UnestablishedOwnedBoundary(required) =
                    &error
                {
                    return Ok(Err(resource_context_runtime_error(
                        ResourceContextValidityError::UnestablishedOwnedBoundary(required.clone()),
                    )));
                }
                if let Some(diagnostic) = error.loan_diagnostic(LoanRefusalOperation::Plan) {
                    return Ok(Err(RuntimeError::LoanRefusal(Box::new(diagnostic))));
                }
                return Ok(Err(RuntimeError::FunctionContract(
                    "stable-view call transition refused".to_string(),
                )));
            }
        }
    } else {
        None
    };
    // Excluding a counted-population requirement from the exclusive
    // reservation costs nothing for a token population, whose units protect
    // no bytes. A population whose body owns memory is a different matter:
    // its units carry write authority over that storage into the callee, so
    // it is checked against the loans this plan and the caller hold, exactly
    // as a direct owned transfer of those bytes would be.
    if let Some(plan) = &stable_view_plan {
        for requirement in &population_quantity_requirements {
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(requirement.fact.clone());
            let body = match evaluate_resource_population_body_resources(
                &singleton,
                callee_state,
                interface.composite_resource_definitions(),
                assumptions,
                budget,
                false,
            )? {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(error)),
            };
            let body = expand_all_composite_resource_facts(
                &body,
                interface.composite_resource_definitions(),
                &callee_state.program_point(),
                assumptions,
            )
            .unwrap_or(body);
            for fact in body.facts().iter().filter(|fact| fact.is_own()) {
                let Some(range) = fact.memory_range() else {
                    continue;
                };
                if let Some(diagnostic) = plan.ledger.memory_access_refusal(
                    range,
                    assumptions,
                    LoanRefusalOperation::Plan,
                ) {
                    return Ok(Err(RuntimeError::LoanRefusal(Box::new(diagnostic))));
                }
            }
        }
    }
    let canonical_resources = {
        let canonical_state = caller_state
            .clone()
            .with_resource_context(required_resources.clone());
        expand_all_composite_resource_facts_at_state(
            &required_resources,
            interface.composite_resource_definitions(),
            &canonical_state,
            assumptions,
        )
    };
    let Some(canonical_resources) = canonical_resources else {
        return Ok(Err(RuntimeError::FunctionContract(format!(
            "could not expand required composite resources before call ({})",
            bounded_contract_resource_frontier(&required_resources)
        ))));
    };
    let population_body_resources = match evaluate_resource_population_body_resources(
        &required_resources,
        callee_state,
        interface.composite_resource_definitions(),
        assumptions,
        budget,
        false,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let required_composite_heads = required_resources
        .facts()
        .iter()
        .filter_map(resource_fact_composite_head)
        .collect::<Vec<_>>();
    let caller_composite_heads = caller_state
        .resources()
        .facts()
        .iter()
        .filter_map(resource_fact_composite_head)
        .collect::<Vec<_>>();
    let has_explicit_representation = caller_state.resources().facts().len()
        != required_resources.facts().len()
        || caller_composite_heads != required_composite_heads;
    let mut callee_resources = if let Some(plan) = &stable_view_plan {
        plan.callee_resources.clone()
    } else if preserve_explicit_representation && has_explicit_representation {
        // Proof execution may have opened exactly the recursive branches needed
        // by the body with `observe` or `unfold`. Independent certification
        // must execute from that same definitionally equivalent form.
        // The transfer checks below still consume every declared requirement,
        // so this cannot weaken the function contract or affect ordinary
        // calls, which always use the canonical boundary.
        caller_state.resources().clone()
    } else {
        canonical_resources
    };
    for empty_view in &empty_composite_views {
        // The head names a resource the callee may state; its checked body is
        // empty, so composing it adds a description and no authority.
        if !callee_resources.satisfies_fact(&empty_view.fact, assumptions) {
            callee_resources = match callee_resources
                .try_compose_with_fact(empty_view.fact.clone(), assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    for requirement in &population_quantity_requirements {
        // The plan never saw this requirement, so the callee context has to
        // receive exactly what the canonical boundary would have handed it:
        // the requirement expanded through its definition, the same way
        // `canonical_resources` expands every other required resource.
        let singleton = ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_fact(requirement.fact.clone());
        let expanded = expand_all_composite_resource_facts(
            &singleton,
            interface.composite_resource_definitions(),
            &callee_state.program_point(),
            assumptions,
        )
        .unwrap_or(singleton);
        for fact in expanded.facts() {
            if callee_resources.satisfies_fact(fact, assumptions) {
                continue;
            }
            callee_resources = match callee_resources
                .try_compose_with_facts_delaying_normalization([fact.clone()], assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    for intrinsic_view in intrinsic_read_views
        .iter()
        .chain(local_read_views.iter().filter(|_| !purpose.lends()))
    {
        // The activation-local bounds rule, decided before any read is
        // attempted. Implicit local authority covers the storage the block
        // has and nothing past it, so a view running off the end is a
        // resource the caller cannot supply, whoever planned the call.
        // Merely withholding the view would let the verdict become the
        // callee's first read of the cells beyond the block, which names the
        // wrong invariant: the call is refused because the view is not
        // backed, not because the storage happens to be uninitialized.
        if matches!(
            intrinsic_view.fact.resource(),
            Resource::Memory(range)
                if range.base().base.is_local_block()
                    && !local_view_range_within_block(range, callee_state.memory())
        ) {
            return Ok(Err(RuntimeError::MissingResource {
                resource: Box::new(intrinsic_view.fact.clone()),
            }));
        }
        if !callee_resources.satisfies_fact(&intrinsic_view.fact, assumptions) {
            callee_resources = match callee_resources
                .try_compose_with_fact(intrinsic_view.fact.clone(), assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    for body_resource in population_body_resources.facts() {
        // The population owns its body even while that body is absent from
        // the caller's explicit proof context. Contract execution opens the
        // body internally after the required population unit has established
        // authority; surface proofs still need scoped `open` to use it.
        if !callee_resources.satisfies_fact(body_resource, assumptions) {
            callee_resources = match callee_resources
                .try_compose_with_facts_delaying_normalization([body_resource.clone()], assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    if preserve_explicit_representation && has_explicit_representation {
        let viewed_composites = caller_state
            .resources()
            .facts()
            .iter()
            .filter(|fact| matches!(fact, ResourceFact::View(Resource::Composite { .. })))
            .cloned()
            .collect::<Vec<_>>();
        for composite in viewed_composites {
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(composite.clone());
            if let Some(expanded) = expand_composite_resource_fact(
                &singleton,
                &composite,
                interface.composite_resource_definitions(),
                &callee_state.program_point(),
                assumptions,
            ) {
                callee_resources =
                    callee_resources.unchecked_with_facts(expanded.facts().iter().cloned());
            }
        }
    }
    // Consumption uses the normalized algebraic context so duplicate token
    // clauses retain their quantity (and diagnostics name the complete
    // requirement).  The metadata-bearing list remains the effect source;
    // normalization is not allowed to erase its role/state metadata.
    let mut required_resource_list = required_resources.facts().to_vec();
    required_resource_list.sort_by_key(resource_fact_transfer_priority);

    let mut return_resources = stable_view_plan
        .as_ref()
        .map(|plan| plan.caller_resources_after_requirements.clone())
        .unwrap_or_else(|| caller_state.resources().clone());
    // The requirements the plan did not reserve are consumed here, off the
    // residual the plan published, by the definitional route. Everything else
    // the plan already removed.
    let population_quantity_resources = population_quantity_requirements
        .iter()
        .map(|requirement| requirement.fact.resource().clone())
        .collect::<BTreeSet<_>>();
    let definitionally_empty_owned_resources = definitionally_empty_owned
        .iter()
        .map(|requirement| requirement.fact.resource().clone())
        .collect::<BTreeSet<_>>();
    for resource in required_resource_list.iter().filter(|resource| {
        stable_view_plan.is_none()
            || (resource.is_own()
                && (population_quantity_resources.contains(resource.resource())
                    || definitionally_empty_owned_resources.contains(resource.resource())))
    }) {
        // A borrowed view of the caller's own stack object needs no resource
        // from the caller, but it still has to name storage that object has.
        // A range running past the block would otherwise let the callee read
        // whatever the caller keeps beyond it: `views a[0..3]` on an
        // `int32 b[2]` used to be discharged by the block merely existing.
        if let ResourceFact::View(Resource::Memory(range)) = resource
            && range.base().base.is_local_block()
            && callee_state.memory().has_block(&range.base().base)
            && !callee_state
                .memory()
                .requires_explicit_scalar_ownership(range.base())
            && local_view_range_within_block(range, callee_state.memory())
        {
            continue;
        }
        let Some(resources) = consume_resource_fact_definitionally(
            &return_resources,
            resource,
            interface.composite_resource_definitions(),
            &caller_state.program_point(),
            assumptions,
        ) else {
            return Ok(Err(RuntimeError::MissingResource {
                resource: Box::new(resource.clone()),
            }));
        };
        return_resources = resources;
    }
    // A suspended worker's create installs the plan's residual. It must lose
    // the requirements consumed definitionally above, such as a field-free
    // member, exactly as this call's own residual does.
    let mut stable_view_plan = stable_view_plan;
    if purpose == ResourceTransitionPurpose::SuspendedWorker
        && let Some(plan) = stable_view_plan.as_mut()
    {
        plan.caller_resources_after_requirements = return_resources.clone();
    }
    let borrowed_inputs = checked_required_resources
        .iter()
        .filter(|checked| checked.role == ResourceTransferRole::Borrow)
        .map(|checked| {
            let mut checked = checked.clone();
            if let Some(fact) = stable_view_plan
                .as_ref()
                .and_then(|plan| plan.mutex_use_requirements.get(&checked.fact))
            {
                checked.fact = fact.clone();
            }
            checked
        })
        .collect();
    // Named consumption needs the governing authority in the checked input
    // partition. Its ledger effect is applied at the checked call successor.
    if purpose.lends()
        && let Some(events) = &caller_state.population_effects.creation
    {
        for checked in &checked_required_resources {
            if checked.role != ResourceTransferRole::Consume {
                continue;
            }
            let Resource::Instance(instance) = checked.fact.resource() else {
                continue;
            };
            let description = ResourceDescription::from_instance(instance);
            if !events.tracks_population(&description) {
                continue;
            }
            let scope = events
                .governing_authority(&description)
                .expect("tracked named population");
            let authority = ResourceFact::own(Resource::PopulationAuthority(scope));
            if !required_resources.satisfies_fact(&authority, assumptions) {
                return Ok(Err(RuntimeError::MissingResource {
                    resource: Box::new(authority),
                }));
            }
        }
    }
    let consumed_inputs = checked_required_resources
        .iter()
        .filter(|checked| checked.role == ResourceTransferRole::Consume)
        .cloned()
        .collect();
    let mut canonical_borrowed_owners: Vec<_> = stable_view_plan
        .as_ref()
        .into_iter()
        .flat_map(|plan| {
            plan.transferred_ownership
                .iter()
                .zip(&plan.canonical_transferred_ownership)
        })
        .filter_map(|(checked, canonical)| {
            (checked.role == ResourceTransferRole::Borrow)
                .then(|| {
                    canonical
                        .clone()
                        .map(|canonical| (checked.fact.clone(), canonical))
                })
                .flatten()
        })
        .collect();
    canonical_borrowed_owners.extend(canonical_population_owners);
    let consumed_cell_returns = if purpose == ResourceTransitionPurpose::CallSite {
        stable_view_plan
            .as_ref()
            .map(|plan| ConsumedCellReturns::prepare(interface, plan, caller_state.resources()))
            .unwrap_or_default()
    } else {
        ConsumedCellReturns::default()
    };
    Ok(Ok(FunctionResourceTransfer {
        helper_call,
        borrowed_inputs,
        consumed_inputs,
        canonical_borrowed_owners,
        consumed_cell_returns,
        allocation_creator: checked_allocation_creator(caller_state, callee_state),
        callee_resources: with_private_aggregate_parameter_owners(
            callee_resources,
            callee_state,
            interface,
        ),
        caller_resources_after_requirements: return_resources,
        memory_effects: Vec::new(),
        resource_effect_bound: None,
        post_outputs: None,
        candidate_output_views: Vec::new(),
        returned_entry_partition: None,
        produced_borrowing_pieces: Vec::new(),
        stable_view_plan,
        checked_view_frontier,
    }))
}

/// A produced memory clause sets the initialization of the bytes it returns.
/// `produces p[a..b]` returns them initialized, which the callee's exit
/// checked, so the caller holds them written. `produces uninitialized(p[a..b])`
/// claims nothing, so the caller holds them unwritten, as it holds fresh
/// `malloc` storage: a read needs a store or `defined` evidence first. Only
/// produced memory clauses are evaluated again.
fn produced_memory_initialization(
    entry_state: &ExecutionState,
    post_state: &ExecutionState,
    interface: &FunctionContractInterface,
    mut memory: SymbolicMemory,
    assumptions: &PureFactContext,
    facts: &mut ExecutionFacts,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<SymbolicMemory, RuntimeError>> {
    for resource in interface.resource_ensures() {
        let Some(segment) = resource.term().memory_segment() else {
            continue;
        };
        if resource.role() != ResourceTransferRole::Produce {
            continue;
        }
        if let Some(guard) = resource.guard() {
            match evaluate_guarded_contract_condition_with_loop_entry(
                guard,
                post_state,
                Some(entry_state),
                assumptions,
                budget,
            ) {
                Some(true) => {}
                Some(false) => continue,
                None => {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "could not select a conditional resource effect: its pre-state condition is not proven"
                            .to_string(),
                    )));
                }
            }
        }
        let fact = match evaluate_function_resource_spec_with_entry(
            entry_state,
            post_state,
            resource,
            assumptions,
            budget,
        )? {
            Ok(fact) => fact,
            Err(error) => return Ok(Err(error)),
        };
        let Resource::Memory(range) = fact.resource() else {
            continue;
        };
        let byte_span = if range.wide_bounds().is_some() {
            None
        } else {
            range.byte_footprint().1.as_const()
        };
        if byte_span == Some(0) {
            continue;
        }
        // Transfer checking established this output's authority and bounds.
        // Mark the same checked bytes at their unique concrete storage
        // anchor, so a descriptor-held alias initializes the original object.
        // This is one indexed address-class lookup, never an alias search.
        let start = assumptions
            .equality_graph
            .storage_address(&range.start_pointer());
        if segment.is_uninitialized() {
            memory = memory.with_uninitialized_object(
                start,
                byte_span.unwrap_or(SymbolicMemory::UNBOUNDED_UNWRITTEN_SPAN),
            );
            continue;
        }
        // Initialized bytes of a length known only at the call are not
        // recorded; a read of them then needs a store or `defined` evidence.
        let Some(byte_span) = byte_span else {
            continue;
        };
        match segment.value_runs() {
            Some(runs) => {
                for &(offset, length) in runs {
                    if offset
                        .checked_add(length)
                        .is_some_and(|end| end <= byte_span)
                    {
                        memory =
                            memory.with_initialized_object(&start.offset_by_bytes(offset), length);
                    }
                }
            }
            None => memory = memory.with_initialized_object(&start, byte_span),
        }
        // Only an explicit complete byte output needs this representation
        // equation. Ordinary scalar reads keep their retained roots and do
        // no extra byte-view work. Initialization is supplied above by the
        // checked output clause, never by the numeric equation.
        if byte_span == 4
            && range.element_width() == 1
            && segment.value_runs().is_none()
            && let Some(equation) = crate::kernel::eval::declared_uint32_read_representation(
                &memory,
                &start,
                budget.program_byte_order(),
            )
        {
            facts.push(ExecutionPureFact::certified(equation));
        }
    }
    Ok(Ok(memory))
}

/// Evaluates the first `count` returned resources of a contract as one
/// jointly returned context. A borrowed resource (an `owns` clause) is
/// evaluated at `entry_state`: the callee returns exactly what it was lent,
/// even when the clause's address depends on a field the body writes. Every
/// other returned resource is evaluated at `post_state`, where the result and
/// the exit memory are visible.
///
/// `entry_clauses` are the contract's own clauses as checked at entry; see
/// [`evaluate_contract_return_resource_context`].
pub(super) fn evaluate_function_return_resource_context(
    function: &ProgramFunction,
    entry_clauses: &[CheckedResourceFact],
    entry_state: &ExecutionState,
    post_state: &ExecutionState,
    count: usize,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, RuntimeError>> {
    evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        entry_clauses,
        entry_clauses,
        entry_state,
        post_state,
        count,
        &[],
        ReturnResourceComposition::ValidateDescriptions,
        assumptions,
        budget,
    )
    .map(|result| result.map(|evaluated| evaluated.resources))
}

type BorrowedResourceKey = (
    ResourceTerm,
    ResourceAccessMode,
    ResourceQuantity,
    ResourceStateSource,
);

fn borrowed_resource_key(resource: &ResourceSpec) -> BorrowedResourceKey {
    (
        resource.term().clone(),
        resource.access(),
        resource.quantity().clone(),
        resource.quantity_state_source(),
    )
}

#[cfg(test)]
mod entry_borrow_return_tests;

/// `entry_clauses` are the contract's own clauses as checked at entry, every
/// role. They are the siblings whose folded field-bearing instances supply
/// read authority to an entry-state clause; nothing else in the entry
/// frame is visited for that purpose.
#[allow(clippy::too_many_arguments)]
fn evaluate_contract_return_resource_context(
    interface: &FunctionContractInterface,
    canonical_borrowed_owners: &[(ResourceFact, ResourceFact)],
    borrowed_inputs: &[CheckedResourceFact],
    entry_clauses: &[CheckedResourceFact],
    entry_state: &ExecutionState,
    post_state: &ExecutionState,
    count: usize,
    prepared_outputs: &[Option<ResourceFact>],
    composition: ReturnResourceComposition,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<EvaluatedReturnResources, RuntimeError>> {
    let mut evaluated = EvaluatedReturnResources::for_composition(composition, assumptions);
    // `owns` requirements that are returned as entry-state borrows carry
    // caller identity in the checked transition. Re-evaluating an address
    // such as `self->pointer` in the callee entry state can replace that
    // identity with a symbolic parameter spelling, even though the resource
    // being returned is exactly the occurrence that was lent. Consume the
    // already checked owned inputs in their source order instead. Views keep
    // their ordinary evaluation path because their loan source is
    // reconstructed separately, and post-state instances carry fresh
    // fields rather than an entry fact.
    let mut canonical_by_checked = BTreeMap::<ResourceFact, VecDeque<ResourceFact>>::new();
    for (checked, canonical) in canonical_borrowed_owners {
        canonical_by_checked
            .entry(checked.clone())
            .or_default()
            .push_back(canonical.clone());
    }
    let mut canonical_for_entry_borrows = canonical_by_checked.clone();
    // An entry-state owned borrow denotes the resource checked and lent at
    // entry. Keep that evaluated fact by normalized term, in occurrence order,
    // rather than re-reading an unmaterialized field on return. The transfer
    // has already checked every fact placed here against caller ownership.
    let mut entry_borrows = BTreeMap::<BorrowedResourceKey, VecDeque<ResourceFact>>::new();
    for checked in borrowed_inputs {
        if checked.role != ResourceTransferRole::Borrow
            || checked.state_source != ResourceStateSource::Entry
            || !checked.fact.is_own()
        {
            continue;
        }
        let Some(requirement) = checked
            .section_index
            .and_then(|index| interface.resource_requires().get(index))
        else {
            continue;
        };
        if requirement.is_instance() {
            continue;
        }
        let canonical = canonical_for_entry_borrows
            .get_mut(&checked.fact)
            .and_then(VecDeque::pop_front)
            .unwrap_or_else(|| checked.fact.clone());
        entry_borrows
            .entry(borrowed_resource_key(requirement))
            .or_default()
            .push_back(canonical);
    }
    // An entry-state borrow whose address depends on a cell the contract's
    // own composites hold (`owns pair(node)` supplying the link
    // `owns pair(node->left->left)` loads) is read the way the entry read
    // it: through the clause set opened by its definitions. The opened cells
    // enter as read authority only, computed once for the entry; the
    // evaluated fact is then matched to the owner the transition lent, never
    // replaced.
    let entry_opened_views = if interface
        .resource_ensures()
        .iter()
        .take(count)
        .any(|resource| {
            resource.state_source() == ResourceStateSource::Entry
                || resource
                    .declared_argument_states()
                    .is_some_and(|retained_states| {
                        retained_states.contains(&ResourceStateSource::Entry)
                    })
        }) {
        let mut views = opened_composite_read_views(
            entry_state.resources(),
            interface.composite_resource_definitions(),
            &entry_state.program_point(),
            assumptions,
        );
        // A folded field-bearing instance the contract's own clauses checked
        // at entry supplies its unmatched body's cells the same way: the
        // entry read is repeated through the clause set that justified it.
        // Only the contract's own checked inputs are visited.
        for checked in entry_clauses {
            views.extend(unmatched_instance_body_views(
                &checked.fact,
                interface.composite_resource_definitions(),
                entry_state,
                assumptions,
            ));
            if let Some(owned) = entry_state
                .resources()
                .directly_supporting_fact(&checked.fact, assumptions)
                .filter(|fact| fact.is_own())
                && let Some((ranges, _)) = matched_instance_body_ownership(
                    owned,
                    interface.composite_resource_definitions(),
                    entry_state,
                    assumptions,
                )
            {
                views.extend(
                    ranges
                        .into_iter()
                        .map(|range| ResourceFact::View(Resource::Memory(range))),
                );
            }
        }
        views
    } else {
        Vec::new()
    };
    let mut entry_argument_views = entry_opened_views.clone();
    entry_argument_views.extend(instance_arm_views(
        entry_state.resources(),
        interface.composite_resource_definitions(),
        entry_state,
        assumptions,
    ));
    let entry_state_for_argument_reads = if entry_argument_views.is_empty() {
        entry_state.clone()
    } else {
        entry_state.clone().with_resource_context(
            entry_state
                .resources()
                .clone()
                .unchecked_with_facts(entry_argument_views.iter().cloned()),
        )
    };
    let entry_state_for_argument_reads = if interface
        .resource_ensures()
        .iter()
        .take(count)
        .any(|resource| resource.guard().is_some())
    {
        let mut resources = entry_state_for_argument_reads.resources().clone();
        for checked in entry_clauses {
            let Resource::Composite { name, .. } = checked.fact.resource() else {
                continue;
            };
            let Some(definition) = interface.composite_resource_definition(name) else {
                continue;
            };
            if !definition
                .contains()
                .iter()
                .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
            {
                continue;
            }
            // An entry checker may already have opened this control.
            // In that case the guard must use its actual authority child.
            if !resources.contains_exact_representation(&checked.fact) {
                continue;
            }
            let (children, _) = match entry_state_for_argument_reads.checked_authority_wrapper_body(
                &checked.fact,
                definition,
                assumptions,
            ) {
                Ok(body) => body,
                Err(error) => return Ok(Err(RuntimeError::FunctionContract(error))),
            };
            let Some(without_head) =
                resources.without_fact_incrementally(&checked.fact, assumptions)
            else {
                return Ok(Err(RuntimeError::MissingResource {
                    resource: Box::new(checked.fact.clone()),
                }));
            };
            resources = match without_head.install_established_partition(children, assumptions) {
                Ok((expanded, _)) => expanded,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
        entry_state_for_argument_reads.with_resource_context(resources)
    } else {
        entry_state_for_argument_reads
    };
    // A returned control preserves the authority consumed at entry. Match
    // its source spelling against only those authenticated input controls;
    // alias equality does not create a new ledger identity.
    let consumed_control_frontier = {
        ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(
            entry_clauses.iter().filter_map(|checked| {
                if checked.role != ResourceTransferRole::Consume {
                    return None;
                }
                let Resource::Composite { name, .. } = checked.fact.resource() else {
                    return None;
                };
                interface
                    .composite_resource_definition(name)
                    .filter(|definition| {
                        definition.contains().iter().any(|child| {
                            matches!(child.term(), ResourceTerm::PopulationAuthority { .. })
                        })
                    })
                    .map(|_| checked.fact.clone())
            }),
        )
    };
    // A produced member of a checked quantity exchange retains the exact
    // population of its consumed input. Canonicalize before composition and
    // ledger return, so a historical field spelling cannot strand the new
    // member under an alias. Only identity is reused; the output quantity is
    // still evaluated and its net effect independently certified.
    let quantity_output = authority_quantity_exchange_effects(interface).and_then(|effects| {
        let input_index = interface
            .resource_requires()
            .iter()
            .position(|spec| std::ptr::eq(spec, effects[0].1))?;
        let input = entry_clauses.iter().find(|checked| {
            checked.section_index == Some(input_index)
                && checked.role == ResourceTransferRole::Consume
        })?;
        let canonical = canonical_by_checked
            .get(&input.fact)
            .and_then(|facts| facts.front())
            .unwrap_or(&input.fact);
        Some((effects[1].1, canonical.resource().clone()))
    });
    // Evaluates one returned clause that has no checked entry borrow against
    // the cells the contract makes readable, including the unmatched bodies
    // of the field-bearing instances already returned beside it.
    // The cells readable while a returned clause is evaluated: the state's
    // own resources, the clauses returned so far, and the views both open.
    // One supply per state absorbs each returned fact once, so a return
    // of `n` clauses costs `n` absorptions rather than `n` per clause.
    struct ReturnSupply {
        supply: ResourceContext,
        absorbed: usize,
    }
    let new_supply = |state: &ExecutionState, entry: bool| {
        let mut views = instance_arm_views(
            state.resources(),
            interface.composite_resource_definitions(),
            state,
            assumptions,
        );
        if entry {
            views.extend(entry_opened_views.iter().cloned());
        }
        ReturnSupply {
            supply: state.resources().clone().unchecked_with_facts(views),
            absorbed: 0,
        }
    };
    let mut entry_supply: Option<ReturnSupply> = None;
    let mut post_supply: Option<ReturnSupply> = None;
    type CanonicalOwners = BTreeMap<ResourceFact, VecDeque<ResourceFact>>;
    let mut evaluate_returned = |clause_index: usize,
                                 resource: &ResourceSpec,
                                 returned: &[ResourceFact],
                                 canonical_by_checked: &mut CanonicalOwners,
                                 budget: &mut ExecutionBudget|
     -> ExecutionResult<Result<ResourceFact, RuntimeError>> {
        if let Some(Some(prepared)) = prepared_outputs.get(clause_index) {
            return Ok(Ok(prepared.clone()));
        }
        // SymbolicMemory state selection is carried by the normalized specification.
        // A named instance uses post fields while retaining entry identity.
        let (state, cached) = match resource.state_source() {
            ResourceStateSource::Entry => (entry_state, &mut entry_supply),
            ResourceStateSource::Current | ResourceStateSource::Post => {
                (post_state, &mut post_supply)
            }
        };
        let cached = cached.get_or_insert_with(|| {
            new_supply(state, resource.state_source() == ResourceStateSource::Entry)
        });
        // A returned view or a clause with no checked entry borrow still
        // evaluates against the cells the contract makes readable. A
        // field-bearing instance this return has already produced
        // supplies its decided arm's cells and its unmatched body's cells
        // to the other returned clauses, exactly as it does while the
        // entry section is evaluated. Only the contract's own returned
        // clauses are visited.
        for fact in &returned[cached.absorbed..] {
            let mut views = Vec::new();
            match fact.resource() {
                Resource::Instance(_) if cached.supply.contains_exact_representation(fact) => {}
                resource => {
                    if let Resource::Instance(instance) = resource
                        && !interface.composite_resource_definitions().is_empty()
                    {
                        views.extend(instance_arm_read_authority(
                            instance,
                            interface.composite_resource_definitions(),
                            state,
                            assumptions,
                        ));
                    }
                    cached.supply = cached.supply.clone().unchecked_with_fact(fact.clone());
                }
            }
            views.extend(unmatched_instance_body_views(
                fact,
                interface.composite_resource_definitions(),
                state,
                assumptions,
            ));
            if !views.is_empty() {
                cached.supply = cached.supply.clone().unchecked_with_facts(views);
            }
        }
        cached.absorbed = returned.len();
        let evaluation_state = state.clone().with_resource_context(cached.supply.clone());
        let evaluated = match evaluate_function_resource_spec_with_entry(
            &entry_state_for_argument_reads,
            &evaluation_state,
            resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(error) => return Ok(Err(error)),
        };
        let evaluated = if let Some((output, population)) = &quantity_output
            && std::ptr::eq(resource, *output)
        {
            if !crate::kernel::resources_directly_match(
                population,
                evaluated.resource(),
                assumptions,
            ) {
                return Ok(Err(RuntimeError::FunctionContract(
                    "quantity exchange must return members of the same population".into(),
                )));
            }
            ResourceFact::own_quantity(
                population.clone(),
                evaluated
                    .owned_quantity_term()
                    .expect("owned output")
                    .clone(),
            )
        } else if resource.role() == ResourceTransferRole::Produce {
            match consumed_control_frontier.directly_supporting_fact(&evaluated, assumptions) {
                Some(source) if source.is_own() => {
                    let ResourceFact::Own(_, quantity) = &evaluated else {
                        return Ok(Ok(evaluated));
                    };
                    ResourceFact::Own(source.resource().clone(), quantity.clone())
                }
                _ => evaluated,
            }
        } else {
            evaluated
        };
        Ok(Ok(
            if resource.role() == ResourceTransferRole::Borrow
                && resource.state_source() == ResourceStateSource::Entry
                && !resource.is_view()
            {
                canonical_by_checked
                    .get_mut(&evaluated)
                    .and_then(VecDeque::pop_front)
                    .unwrap_or(evaluated)
            } else {
                evaluated
            },
        ))
    };
    // A clause whose address loads a cell a later returned clause supplies
    // waits for it: clause order does not decide what a contract returns,
    // just as it does not decide what it requires.
    let mut deferred: Vec<(usize, &ResourceSpec, RuntimeError)> = Vec::new();
    let mut returned: Vec<ResourceFact> = Vec::new();
    for (clause_index, resource) in interface.resource_ensures().iter().take(count).enumerate() {
        if let Some(guard) = resource.guard() {
            match evaluate_guarded_contract_condition_with_loop_entry(
                guard,
                post_state,
                Some(&entry_state_for_argument_reads),
                assumptions,
                budget,
            ) {
                Some(true) => {}
                Some(false) => continue,
                None => {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "could not select a conditional resource effect: its pre-state condition is not proven"
                            .to_string(),
                    )))
                }
            }
        }
        let entry_borrow = (resource.role() == ResourceTransferRole::Borrow
            && resource.state_source() == ResourceStateSource::Entry
            && !resource.is_view())
        .then(|| borrowed_resource_key(resource))
        .and_then(|key| entry_borrows.get_mut(&key))
        .and_then(VecDeque::pop_front);
        // An instance's fields are post-state observations, so it must be
        // evaluated rather than copied from the entry fact. Its exclusive
        // identity nevertheless retains the checked entry borrow's custody.
        let return_entry_borrow = entry_borrow.is_some()
            || interface
                .resource_transfer_rule
                .borrowed_instance_outputs
                .contains(&clause_index);
        let resource =
            if let Some(constructed) = composition.constructed_summary_output(clause_index) {
                constructed.clone()
            } else if let Some(entry_borrow) = entry_borrow {
                entry_borrow
            } else {
                match evaluate_returned(
                    clause_index,
                    resource,
                    &returned,
                    &mut canonical_by_checked,
                    budget,
                )? {
                    Ok(resource) => resource,
                    Err(error) if resource_clause_failure_awaits_supply(&error) => {
                        deferred.push((clause_index, resource, error));
                        continue;
                    }
                    Err(error) => return Ok(Err(error)),
                }
            };
        // Retain the occurrence constructed by transfer or custody; descriptions
        // still need their missing relationship established by admission.
        evaluated = match evaluated.construct_clause(
            resource.clone(),
            composition.origin_for_return(clause_index, return_entry_borrow, &resource),
            Some(clause_index),
            composition,
            interface,
            assumptions,
        ) {
            Ok(evaluated) => evaluated,
            Err(error) => return Ok(Err(error)),
        };
        returned.push(resource);
    }
    // Each retry pass returns at least one waiting clause or stops, so the
    // passes are bounded by the number of clauses that waited.
    while !deferred.is_empty() {
        let waited = deferred.len();
        let mut waiting = Vec::new();
        for (clause_index, resource, error) in std::mem::take(&mut deferred) {
            match evaluate_returned(
                clause_index,
                resource,
                &returned,
                &mut canonical_by_checked,
                budget,
            )? {
                Ok(fact) => {
                    evaluated = match evaluated.construct_clause(
                        fact.clone(),
                        composition.origin_for_return(
                            clause_index,
                            interface
                                .resource_transfer_rule
                                .borrowed_instance_outputs
                                .contains(&clause_index),
                            &fact,
                        ),
                        Some(clause_index),
                        composition,
                        interface,
                        assumptions,
                    ) {
                        Ok(evaluated) => evaluated,
                        Err(error) => return Ok(Err(error)),
                    };
                    returned.push(fact);
                }
                Err(retry_error) if resource_clause_failure_awaits_supply(&retry_error) => {
                    waiting.push((clause_index, resource, error));
                }
                Err(retry_error) => return Ok(Err(retry_error)),
            }
        }
        if waiting.len() == waited {
            // Nothing returned on this pass: no order supplies the cell.
            let (_, _, error) = waiting.swap_remove(0);
            return Ok(Err(error));
        }
        deferred = waiting;
    }
    Ok(Ok(evaluated))
}

/// The memory a context's owned composites hold, opened through their
/// definitions at `at`, as read views: the authority a clause set
/// gives to the addresses its own dependent clauses load, offered to an
/// evaluation that reads the entry the way the entry itself did. Nothing is
/// owned twice; a view grants a read and no more.
fn opened_composite_read_views(
    resources: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Vec<ResourceFact> {
    if !resources
        .facts()
        .iter()
        .any(|fact| fact.is_own() && matches!(fact.resource(), Resource::Composite { .. }))
    {
        return Vec::new();
    }
    let Some(opened) = expand_all_composite_resource_facts(resources, definitions, at, assumptions)
    else {
        return Vec::new();
    };
    opened
        .facts()
        .iter()
        .filter_map(|fact| match fact {
            ResourceFact::Own(resource @ Resource::Memory(_), _) => {
                Some(ResourceFact::View(resource.clone()))
            }
            _ => None,
        })
        .collect()
}

/// The contract's own clauses a transfer checked at entry, lent and consumed
/// alike: the siblings an entry-state returned clause may read through.
fn transfer_entry_clauses(transfer: &FunctionResourceTransfer) -> Vec<CheckedResourceFact> {
    transfer
        .borrowed_inputs
        .iter()
        .chain(&transfer.consumed_inputs)
        .cloned()
        .collect()
}

/// The owned facts a call's lend escrowed. They are not in the
/// caller residual for the duration of the call, but recovery composes each
/// one back, so a check on what the caller will hold has to read them.
fn escrowed_owners(transfer: &FunctionResourceTransfer) -> &[ResourceFact] {
    transfer
        .stable_view_plan
        .as_ref()
        .map(|plan| plan.escrowed_owners())
        .unwrap_or_default()
}

#[allow(clippy::too_many_arguments)]
fn evaluate_function_return_resources(
    caller_resources_after_requirements: &ResourceContext,
    escrowed_owners: &[ResourceFact],
    canonical_borrowed_owners: &[(ResourceFact, ResourceFact)],
    borrowed_inputs: &[CheckedResourceFact],
    entry_clauses: &[CheckedResourceFact],
    entry_state: &ExecutionState,
    post_state: &ExecutionState,
    body_state: &ExecutionState,
    function: &ProgramFunction,
    allocation_creator: Option<&CreationEvents>,
    consumed_returns: &ConsumedCellReturns,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ContractReturnResources, RuntimeError>> {
    evaluate_contract_return_resources(
        caller_resources_after_requirements,
        escrowed_owners,
        canonical_borrowed_owners,
        borrowed_inputs,
        entry_clauses,
        entry_state,
        post_state,
        function.name(),
        function.contract_interface(),
        &[],
        ReturnResourceComposition::BodyReturn {
            state: body_state,
            frame: caller_resources_after_requirements,
            allocations: allocation_creator.zip(post_state.population_effects.creation.as_ref()),
            consumed: consumed_returns,
        },
        assumptions,
        budget,
    )
}

#[allow(clippy::too_many_arguments)]
fn evaluate_contract_return_resources(
    caller_resources_after_requirements: &ResourceContext,
    _escrowed_owners: &[ResourceFact],
    canonical_borrowed_owners: &[(ResourceFact, ResourceFact)],
    borrowed_inputs: &[CheckedResourceFact],
    entry_clauses: &[CheckedResourceFact],
    entry_state: &ExecutionState,
    post_state: &ExecutionState,
    interface_name: &str,
    interface: &FunctionContractInterface,
    prepared_outputs: &[Option<ResourceFact>],
    composition: ReturnResourceComposition,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ContractReturnResources, RuntimeError>> {
    let evaluated = match crate::instrumentation::measure_operation(
        interface_name,
        "contract resource transition",
        "ensured resource lowering",
        || {
            evaluate_contract_return_resource_context(
                interface,
                canonical_borrowed_owners,
                borrowed_inputs,
                entry_clauses,
                entry_state,
                post_state,
                interface.resource_ensures().len(),
                prepared_outputs,
                composition,
                assumptions,
                budget,
            )
        },
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let ensured_resources = &evaluated.resources;
    let Some(return_bodies) = ConstructedReturnBodies::try_construct(
        &evaluated,
        interface.composite_resource_definitions(),
        post_state,
        composition,
        assumptions,
    ) else {
        return Ok(Err(RuntimeError::FunctionContract(format!(
            "could not expand ensured composite resources after call ({})",
            bounded_contract_resource_frontier(ensured_resources)
        ))));
    };
    // Entry borrows rejoin their selected frame before newly described
    // ownership is checked, including the bodies of produced composites.
    let prepared = match crate::instrumentation::measure_operation(
        interface_name,
        "contract resource transition",
        "entry borrow restoration",
        || {
            evaluated.restore_entry_borrows(
                caller_resources_after_requirements.clone(),
                composition,
                assumptions,
            )
        },
    ) {
        Ok(prepared) => prepared,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };
    // Returned flat clauses are an explicit output delta. A head's boundary
    // with them is finalized here, so an overlap keeps the composite-specific
    // refusal instead of becoming an opaque body-construction failure.
    let flat_outputs = if composition.body_return().is_none() {
        prepared
            .pending
            .facts()
            .iter()
            .filter(|fact| fact.memory_own_range().is_some())
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // A composite arrives folded, so composing its head says nothing about
    // what its body covers. Check the body against the destination before the
    // head enters it, or a contract that produces a composite over bytes the
    // destination still owns turns one owner into two.
    if !composition.frames_outputs()
        && let Some(error) = crate::instrumentation::measure_operation(
            interface_name,
            "contract resource transition",
            "ensured composite frontier check",
            || {
                // Borrowed composite arguments retain their entry identity, but
                // their bodies can read post-call memory. Preserve the existing
                // check against the retained frame, before adding their heads.
                if !prepared.entry_borrow_outputs.facts().is_empty() {
                    let retained = caller_resources_after_requirements
                        .clone()
                        .unchecked_with_facts(
                            prepared.transferred_memory_outputs.facts().iter().cloned(),
                        )
                        .unchecked_with_facts(flat_outputs.iter().cloned());
                    if let Some(error) = produced_composite_frontier_conflict(
                        &retained,
                        prepared
                            .frontier_sources(ensured_resources, true)
                            .map(|(source, fact)| (fact, return_bodies.for_return(source, fact))),
                        assumptions,
                    ) {
                        return Some(error);
                    }
                }
                // Withheld escrows have their own checked finite frontier. Their
                // boundary is checked once, when that restoration receipt is
                // consumed, rather than by expanding their heads here.
                let destination = prepared
                    .frame
                    .clone()
                    .unchecked_with_facts(return_bodies.transferred_memory_frontier().cloned())
                    .unchecked_with_facts(flat_outputs.iter().cloned());
                produced_composite_frontier_conflict(
                    &destination,
                    prepared
                        .frontier_sources(ensured_resources, false)
                        .map(|(source, fact)| (fact, return_bodies.for_return(source, fact))),
                    assumptions,
                )
            },
        )
    {
        return Ok(Err(error));
    }
    let ensured_views = ensured_resources
        .facts()
        .iter()
        .filter(|fact| fact.is_view())
        .cloned()
        .collect::<Vec<_>>();
    // Every ensured view is composed into the caller and then classified by
    // where its live authority comes from. The blanket deduplication that
    // used to drop an ensured view the caller already satisfied is gone
    // (docs/internals/stable-views.md: "blanket deduplication against a caller owner is no
    // longer a valid way to discharge obligations", closed as step 6's
    // F14(c)). It was a filter against `satisfies_fact`, so an owner the
    // caller happened to hold silently answered a returned view; the
    // recovery routes in `recover_candidate_stable_view_resources` decide
    // that question now, over the declared output delta `candidate_output_views`.
    let returned_entry_partition = prepared.entry_partition();
    let (return_resources, inserted_ensured_occurrences) =
        match crate::instrumentation::measure_operation(
            interface_name,
            "contract resource transition",
            "ensured resource composition",
            || prepared.finish(assumptions),
        ) {
            Ok(resources) => resources,
            Err(error) => return Ok(Err(resource_context_runtime_error(error))),
        };
    let projected_cores_by_support = crate::instrumentation::measure_operation(
        interface_name,
        "contract resource transition",
        "ensured resource core projection",
        || {
            project_return_resource_cores(
                ensured_resources,
                &inserted_ensured_occurrences,
                &return_bodies,
                assumptions,
                &return_resources,
            )
        },
    );
    // The callee has already certified every ensured composite and its
    // instantiated body. Its duplicable cores are therefore observations of
    // certified ownership, not independent persistent caller capabilities.
    // Record their exact support so consuming that ownership removes only
    // its projections through the reverse index.
    let mut return_resources = return_resources;
    let mut produced_borrowing_pieces = Vec::new();
    let origins = evaluated
        .occurrences
        .iter()
        .map(|entry| (entry.source, entry.origin))
        .collect::<BTreeMap<_, _>>();
    let mut escrow_boundary =
        EscrowRecoveryBoundary::default().with_entry_partition(returned_entry_partition);
    for resource in projected_cores_by_support {
        let constructed_borrowing_pieces = resource.constructed_borrowing_pieces();
        let ProjectedReturnResource {
            source,
            support,
            destination: support_occurrence,
            expansion,
            projected,
            frontier: _,
            viewed_children: _,
        } = resource;
        if support.is_own() {
            let origin = origins[&source];
            let raw = if matches!(origin, ReturnOwnershipOrigin::Description)
                && !matches!(
                    support.resource(),
                    Resource::Composite { .. } | Resource::Instance(_)
                ) {
                vec![support.clone()]
            } else {
                Vec::new()
            };
            let body = if let Some(body) = return_bodies.for_return(source, &support) {
                body.escrow_boundary()
            } else {
                Vec::new()
            };
            escrow_boundary.record(support_occurrence, raw, body);
        }
        // Only the one-level frontier names the borrows this composite
        // packages; a nested composite's own body is that composite's
        // business (the 4b rule). The viewed pieces of an observed
        // population family, or of more than one unit, keep the observation
        // reading rather than an escaping loan.
        let is_population = match support.resource() {
            Resource::Composite { name, .. } => {
                support.owned_quantity_term() != Some(&MachineTerm::constant(1))
                    || post_state.observes_population_family(name)
                    || entry_state.observes_population_family(name)
            }
            _ => false,
        };
        if !is_population {
            produced_borrowing_pieces.extend(constructed_borrowing_pieces);
        }
        return_resources = return_resources
            .unchecked_with_supported_facts_from_occurrence_with_memory(
                support_occurrence,
                &support,
                projected,
                post_state.memory(),
            )
            .with_cached_supported_expansion_for_occurrence(
                support_occurrence,
                &support,
                expansion,
            );
    }
    Ok(Ok(ContractReturnResources {
        output_resources: evaluated.resources,
        return_resources,
        escrow_boundary,
        ensured_views,
        produced_borrowing_pieces,
        returned_entry_partition,
    }))
}

/// The outputs of a contract's return-resource evaluation.
pub(crate) struct ContractReturnResources {
    /// The explicit output delta, without the caller's unrelated frame.
    returned_entry_partition: Option<mixed_return_resources::ReturnedEntryPartition>,
    pub(crate) output_resources: ResourceContext,
    pub(crate) return_resources: ResourceContext,
    pub(in crate::kernel) escrow_boundary: EscrowRecoveryBoundary,
    pub(crate) ensured_views: Vec<ResourceFact>,
    pub(crate) produced_borrowing_pieces: Vec<ProducedBorrowingPiece>,
}

/// Checks every produced or ensured composite's body against the context it
/// is about to be composed into.
///
/// A valid resource context denotes a partition: every owned fact is disjoint
/// from every other fact in it, composites included. Inside one component the
/// kernel keeps that by construction, because unfolding consumes the head and
/// folding consumes the pieces. A callee's output crosses that boundary as a
/// folded head whose body was never compared with what the destination holds,
/// so without this check `produces box(p)` beside a caller that still owns
/// `p[0..1]` leaves two owners over the same byte.
///
/// Only the one-level checked frontier is compared. A nested composite child
/// is itself a fact here, not a body to reason inside; that is the same
/// "no reasoning inside composites" rule the composite lend follows.
fn produced_composite_frontier_conflict<'a>(
    destination: &ResourceContext,
    ensured: impl Iterator<
        Item = (
            &'a ResourceFact,
            Option<&'a mixed_return_resources::ConstructedReturnBody>,
        ),
    >,
    assumptions: &PureFactContext,
) -> Option<RuntimeError> {
    let mut destination = destination.clone();
    for (produced, body) in ensured {
        let name = match produced.resource() {
            Resource::Composite { name, .. } => name.as_str(),
            Resource::Instance(instance) => instance.name(),
            _ => continue,
        };
        if !produced.is_own() {
            continue;
        }
        let body = body.expect("returned family dispatch must carry a finite body");
        let frontier = body.boundary();
        // A token-only body holds no memory, instance, or nested composite a
        // destination fact could overlap: token units are a count, and counts
        // add rather than collide.
        if !body
            .frontier
            .iter()
            .chain(body.boundary().iter())
            .any(|piece| {
                piece.is_own()
                    && matches!(
                        piece.resource(),
                        Resource::Memory(_)
                            | Resource::Iterated(_)
                            | Resource::PopulationAuthority(_)
                            | Resource::Instance(_)
                            | Resource::Composite { .. }
                    )
            })
        {
            continue;
        }
        // The frontier was evaluated for one unit, and an ordinary composite
        // has no population-wide body to install instead: every unit owns the
        // same bytes this one does. Two such units are already two owners of
        // one range, and a symbolic count is not a quantity the check below
        // could compare against the destination at all. Refuse rather than
        // check one unit and call the rest checked.
        if produced
            .owned_quantity_term()
            .and_then(MachineTerm::as_const)
            != Some(1)
        {
            return Some(RuntimeError::FunctionContract(format!(
                "a produced quantity of `{name}` other than one owns memory in its \
                 body, so its units would own the same range more than once"
            )));
        }
        // Construction established the body's internal partition. Only its
        // boundary with the retained caller frame is new information.
        let (piece, held) =
            match destination.checked_frontier_boundary_conflict(frontier, assumptions) {
                Ok(Some(conflict)) => conflict,
                Ok(None) => {
                    destination = destination.unchecked_with_facts(frontier.iter().cloned());
                    continue;
                }
                Err(error) => return Some(resource_context_runtime_error(error)),
            };
        return Some(RuntimeError::ProducedCompositeOverlapsHeldResource {
            produced: Box::new(produced.clone()),
            piece: Box::new(piece),
            held: Box::new(held),
        });
    }
    None
}

/// Whether a requirement asks for a quantity of a resource population other
/// than the unit.
///
/// Only `ResourceSpec::quantified` builds one, and only over a composite or
/// token term, so this is exactly the `N of p` clause. It is not a claim
/// about one owned entry: the caller holds a representative unit while the
/// declared cardinality lives in the tracked population, so the count is
/// decided by the counted-population transition and the definitional route,
/// never by an exact-entry reservation.
fn requirement_is_population_quantity(requirement: &CheckedResourceFact) -> bool {
    matches!(
        requirement.fact.resource(),
        Resource::Composite { .. } | Resource::Token { .. }
    ) && requirement.fact.is_own()
        && requirement.fact.owned_quantity_term() != Some(&MachineTerm::constant(1))
}

fn resource_fact_composite_head(fact: &ResourceFact) -> Option<(bool, &str)> {
    let Resource::Composite { name, .. } = fact.resource() else {
        return None;
    };
    Some((fact.is_own(), name))
}

pub(super) fn prepare_function_contract_entry_state_with_values(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    argument_values: &[ProgramValue],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ExecutionState, RuntimeError>> {
    let Some(callee_state) = bind_contract_proof_arguments(caller_state, function, argument_values)
    else {
        return Ok(Err(RuntimeError::FunctionContract(format!(
            "could not bind contract-entry arguments for {}",
            function.name()
        ))));
    };
    let transfer = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "contract resource transfer preparation",
        || {
            prepare_contract_resource_transfer(
                caller_state,
                &callee_state,
                function.name(),
                function.contract_interface(),
                assumptions,
                budget,
                true,
                ResourceTransitionPurpose::FunctionBoundary,
            )
        },
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    Ok(Ok(callee_state_with_resource_transfer(
        callee_state,
        &transfer,
    )))
}

/// Binds a composite definition's existential witnesses as locals of the
/// body-evaluation state, after its parameters. A witness related to a word
/// by a `where` fact of the shape `word == address(witness) + tag` is bound
/// to that word's recorded origin, so folding and unfolding the same body
/// agree on it; a witness with no recorded origin yet (an unfold whose facts
/// are about to introduce it) is bound to a fresh symbolic pointer chosen
/// from the selected definition, witness position, arguments, and word term.
pub(super) fn bind_composite_witnesses(
    definition: &CompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    state: &mut ExecutionState,
    assumptions: &PureFactContext,
) -> Option<Vec<ProgramValue>> {
    let held = state.resources.clone();
    bind_composite_witnesses_with_held(definition, arguments, state, &held, assumptions)
}

/// [`bind_composite_witnesses`] with the held resource facts supplied
/// separately, for callers whose evaluation state carries no resources.
pub(super) fn bind_composite_witnesses_with_held(
    definition: &CompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    state: &mut ExecutionState,
    held: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<ProgramValue>> {
    bind_composite_witness_values(definition, arguments, state, Some(held), assumptions)
}

/// Shared witness producer. Returned bodies pass no held context: their
/// bindings come from declared word origins or the producer's symbolic names.
/// Explicit folds retain their separate legacy child-description discovery.
fn bind_composite_witness_values(
    definition: &CompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    state: &mut ExecutionState,
    held: Option<&ResourceContext>,
    assumptions: &PureFactContext,
) -> Option<Vec<ProgramValue>> {
    if definition.witnesses().is_empty() {
        return Some(Vec::new());
    }
    let words = indexed_witness_origin_words(definition.facts());
    use std::hash::{Hash, Hasher};
    let mut argument_hasher = std::collections::hash_map::DefaultHasher::new();
    arguments.hash(&mut argument_hasher);
    let argument_identity = argument_hasher.finish();
    let mut values = Vec::new();
    for (index, witness) in definition.witnesses().iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let word = words.get(witness.name()).copied().and_then(|word| {
            let mut budget = ExecutionBudget::beside_live_state();
            let paths = super::spec::evaluate_spec_expression_paths_with_loop_entry(
                state,
                word,
                None,
                assumptions,
                &mut budget,
            )
            .ok()?;
            let [path] = paths.as_slice() else {
                return None;
            };
            match path.value.native().as_ref() {
                ProgramValue::UInt64(term) | ProgramValue::Int64(term) => Some(term.clone()),
                _ => None,
            }
        });
        let origin = word
            .as_ref()
            .and_then(|term| {
                if term.uint64_as_const() == Some(0) {
                    return Some(Address::null());
                }
                let mut used = super::eval::pointer_tags::UsedFacts::new();
                super::eval::pointer_tags::tagged_address_form(term, assumptions, &mut used)
                    .map(|form| form.pointer)
            })
            // Explicit folds retain the legacy held-child inference when a
            // word supplies no origin. Return construction passes None and
            // never searches a retained frame or constructed sibling here.
            .or_else(|| {
                held.and_then(|held| {
                    held_child_witness(definition, witness.name(), arguments, held, assumptions)
                })
            });
        // A witness with no recorded origin is named by the content of the
        // instance that introduces it: the definition, the witness position,
        // the argument values, and the word's own value term. The word term
        // survives materializing the body's cells, which store that same
        // symbolic load, and changes when the word is stored, so every site
        // that instantiates the same body at the same word names the same
        // pointer while a later store names another.
        let pointer = origin.unwrap_or_else(|| {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            definition.name().hash(&mut hasher);
            index.hash(&mut hasher);
            argument_identity.hash(&mut hasher);
            // The canonical form names a load by its cell rather than by
            // the state it was read from, so the key is the same before
            // and after the body's cells are materialized.
            word.as_ref()
                .map(super::eval::canonical_term)
                .hash(&mut hasher);
            Address::symbolic(Variable(4_000_000_000 + hasher.finish() % 4_000_000_000))
        });
        let value = ProgramValue::typed_pointer(pointer, witness.program_type());
        state.locals.set_typed(
            witness.name().to_string(),
            value.clone(),
            witness.program_type(),
        );
        values.push(value);
    }
    Some(values)
}

/// The unique held composite fact that a `contains name(witness)` clause of
/// the body would consume, if the body has such a clause and exactly one
/// held fact of that composite exists.
fn held_child_witness(
    definition: &CompositeResourceDefinition,
    witness: &str,
    arguments: &[AlgebraicValue],
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Address> {
    // The body's own instance is never its own child.
    let own_pointers = arguments
        .iter()
        .filter_map(|argument| match argument {
            AlgebraicValue::Program(ProgramValue::Pointer(pointer)) => {
                Some(pointer.address().clone())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let child_name = definition.contains().iter().find_map(|spec| {
        let arguments = spec.declared_arguments()?;
        (spec.family() == ResourceFamily::Composite
            && matches!(arguments, [ProgramExpression::Variable(argument)] if argument.is_named(witness)))
        .then(|| spec.declared_name().expect("composite spec has a name"))
    })?;
    let mut candidates = resources
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            Resource::Composite { name, arguments } if name == child_name => {
                match arguments.fixed_values::<1>() {
                    Some([ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) => {
                        Some(pointer.address().clone())
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        // A candidate in the block of one of the body's own pointers must be
        // proven a different pointer.
        .filter(|pointer| {
            own_pointers.iter().all(|own| {
                own.base != pointer.base
                    || assumptions
                        .decide(&ConditionTerm::address_equal(pointer.clone(), own.clone()))
                        == Some(false)
            })
        });
    let first = candidates.next()?;
    candidates.all(|other| other == first).then_some(first)
}

/// Build the selected definition's witness-to-word table once, preserving the
/// first declaration and right-before-left precedence of the origin relation.
fn indexed_witness_origin_words(facts: &[SpecProposition]) -> BTreeMap<&str, &SpecExpression> {
    fn addresses<'a>(
        expression: &'a SpecExpression,
        word: &'a SpecExpression,
        words: &mut BTreeMap<&'a str, &'a SpecExpression>,
    ) {
        let mut pending = vec![expression];
        while let Some(expression) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match expression {
                SpecExpression::ProgramExpression(ProgramExpression::Cast {
                    expression,
                    target_type: ProgramType::UInt64 | ProgramType::Int64,
                    ..
                }) => {
                    if let ProgramExpression::Variable(name) = expression.as_ref()
                        && let Some(name) = name.named()
                    {
                        words.entry(name).or_insert(word);
                    }
                }
                SpecExpression::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                _ => {}
            }
        }
    }
    let mut words = BTreeMap::new();
    let mut pending = facts.iter().rev().collect::<Vec<_>>();
    while let Some(fact) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match fact {
            SpecProposition::And(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            SpecProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } => {
                addresses(right, left, &mut words);
                addresses(left, right, &mut words);
            }
            _ => {}
        }
    }
    words
}

/// Why a fold or unfold was refused. Most refusals are one fixed sentence;
/// the body-fact refusal names which fact of which arm the fold could not
/// establish, since "the body facts" of a five-fact arm sends the author to
/// read all five. The static sentence is still available to callers whose
/// own error is a static string.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceRewriteRefusal {
    Message(&'static str),
    OwnedMessage(String),
    BodyResourceMissing(Box<ResourceFact>),
    ChildArgumentNotEstablished {
        child: String,
        index: usize,
        actual: Box<AlgebraicValue>,
        required: Box<AlgebraicValue>,
    },
    /// `fold` could not establish body fact `index` (zero-based, in
    /// declaration order) of the `count` facts in `arm`, or of the
    /// definition's own facts when `arm` is `None`.
    BodyFactNotEstablished {
        arm: Option<String>,
        index: usize,
        count: usize,
        /// The fact as its declaration spells it, when known.
        spelling: Option<String>,
        proposition: Box<Proposition>,
    },
    BodyFactPrerequisiteNotEstablished {
        arm: Option<String>,
        index: usize,
        count: usize,
        proposition: Box<Proposition>,
    },
}

impl ResourceRewriteRefusal {
    pub fn describe(&self) -> String {
        match self {
            ResourceRewriteRefusal::Message(message) => (*message).to_string(),
            ResourceRewriteRefusal::OwnedMessage(message) => message.clone(),
            ResourceRewriteRefusal::BodyResourceMissing(_) => {
                "fold requires ownership of the complete instance body".into()
            }
            ResourceRewriteRefusal::ChildArgumentNotEstablished { child, index, .. } => format!(
                "child `{child}` is not proven to have the arguments the parent body gives it: argument {} equality is not established",
                index + 1
            ),
            ResourceRewriteRefusal::BodyFactPrerequisiteNotEstablished {
                arm,
                index,
                count,
                ..
            } => {
                let place = arm
                    .as_ref()
                    .map_or_else(|| "resource body".to_owned(), |arm| format!("arm `{arm}`"));
                format!(
                    "resource body fact {} of {count} in {place} has an unproved prerequisite",
                    index + 1
                )
            }
            ResourceRewriteRefusal::BodyFactNotEstablished {
                arm,
                index,
                count,
                spelling,
                ..
            } => {
                let place = match arm {
                    Some(arm) => format!("of arm `{arm}`"),
                    None => "of the resource body".to_string(),
                };
                let spelled = spelling
                    .as_ref()
                    .map(|fact| format!(": `{fact}`"))
                    .unwrap_or_default();
                format!(
                    "fold requires the instance body facts for the proposed fields: fact {} of {count} {place} is not established{spelled}",
                    index + 1
                )
            }
        }
    }
}

impl From<&'static str> for ResourceRewriteRefusal {
    fn from(message: &'static str) -> Self {
        ResourceRewriteRefusal::Message(message)
    }
}

impl From<ResourceRewriteRefusal> for &'static str {
    fn from(refusal: ResourceRewriteRefusal) -> Self {
        match refusal {
            ResourceRewriteRefusal::Message(message) => message,
            ResourceRewriteRefusal::OwnedMessage(_) => "resource rewrite refused",
            ResourceRewriteRefusal::BodyResourceMissing(_) => {
                "fold requires ownership of the complete instance body"
            }
            ResourceRewriteRefusal::ChildArgumentNotEstablished { .. } => {
                "resource child argument equality is not established"
            }
            ResourceRewriteRefusal::BodyFactNotEstablished { .. } => {
                "fold requires the instance body facts for the proposed fields"
            }
            ResourceRewriteRefusal::BodyFactPrerequisiteNotEstablished { .. } => {
                "instance body fact has an unproved prerequisite"
            }
        }
    }
}

/// A declaration-level consequence of a selected resource body. This is not
/// a fact-store delta: a clause remains here when its proposition was already
/// known, so presentation can retain its exact binder and source ordinal.
#[derive(Clone, Debug)]
pub(crate) struct ResourceBodyClauseRecord {
    pub(crate) arm: Option<String>,
    pub(crate) ordinal: usize,
    pub(crate) proposition: Proposition,
    pub(crate) introductions: LoweringIntroductions,
}

impl ResourceBodyClauseRecord {
    pub(crate) fn obligation(&self) -> ProofObligation {
        ProofObligation::verification_condition(self.proposition.clone())
            .with_introductions(self.introductions.clone())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ResourceInstanceRewriteResult {
    /// The body guard case checked by this rewrite. Unknown guards refuse the rewrite.
    pub(crate) body_active: bool,
    pub(crate) state: ExecutionState,
    /// Justified consequences to admit; either rewrite may return facts the caller
    /// already holds. Ordinary fact insertion handles those duplicates.
    pub(crate) semantic_facts: Vec<Proposition>,
    pub(crate) body_clauses: Vec<ResourceBodyClauseRecord>,
    /// The checked opening delta used to choose the body's pointer spellings.
    pub(crate) naming_facts: Vec<Proposition>,
}

/// Whether an undischarged proposition only says that an arithmetic
/// evaluation does not hit undefined behavior (for example, `x + 2` cannot
/// overflow). Unfold exposes such conditions alongside the body fact instead
/// of refusing; anything else keeps the generic conditional-proof
/// diagnostic.
fn is_pure_undefined_behavior_condition(proposition: &Proposition) -> bool {
    if crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(proposition)
        .is_some()
    {
        return true;
    }
    let Proposition::ConditionIs(condition, false) = proposition else {
        return false;
    };
    matches!(
        condition.native_compat(),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Subtract,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Multiply,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Divide,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::ShiftLeft,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Add,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Subtract,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Multiply,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Divide,
            ..
        } | ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::ShiftLeft,
            ..
        }
    )
}

/// Lower one selected body in source order. A body clause is available to a
/// later clause only after the selected resource justified it (unfold/match),
/// or after the fold's existing facts established it. Routing facts for a
/// conditional lowering must be stated in this exact accumulated context;
/// other paths being impossible is not itself evidence for a survivor.
#[allow(clippy::too_many_arguments)]
fn lower_selected_resource_body_clauses(
    evaluation: &ExecutionState,
    source: &[SpecProposition],
    arm: Option<&str>,
    integer_bindings: &BTreeMap<Variable, IntegerTerm>,
    algebraic_bindings: &BTreeMap<BindingName, AlgebraicTerm>,
    body_assumptions: &PureFactContext,
    established_assumptions: Option<&PureFactContext>,
    budget: &mut ExecutionBudget,
) -> Result<(Vec<ResourceBodyClauseRecord>, Vec<Proposition>), ResourceRewriteRefusal> {
    let program_replacements = BTreeMap::new();
    let algebraic_replacements = BTreeMap::new();
    let mut rewrite = crate::kernel::proof::term_rewrite::TermRewrite::for_checked_typed_variables(
        &program_replacements,
        integer_bindings,
        &algebraic_replacements,
    );
    rewrite.enable_registered_load_resolution();
    rewrite
        .reserve_spec_proposition_sources(source.iter())
        .map_err(|_| "resource match Integer binding substitution exceeded its checked scope")?;
    let mut context = body_assumptions.clone();
    let mut records = Vec::with_capacity(source.len());
    let mut retained_conditions = Vec::new();
    for (ordinal, clause) in source.iter().enumerate() {
        // Unfold publishes numeric observations; fold checks existing values.
        // A pointer cast restores complete-word demand in either case.
        let _word_observation =
            crate::kernel::eval::WordRepresentationScope::enter(established_assumptions.is_some());
        crate::instrumentation::record_deterministic_work(1);
        let clause = rewrite.spec_proposition(clause).map_err(
            |_| "resource match Integer binding substitution exceeded its checked scope",
        )?;
        let paths = if established_assumptions.is_none() {
            crate::kernel::spec::lower_held_resource_body_clause(
                evaluation,
                &clause,
                &context,
                algebraic_bindings,
                budget,
            )
        } else {
            crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
                evaluation,
                &clause,
                None,
                &context,
                algebraic_bindings,
                budget,
            )
        }
        .map_err(|limit| match limit {
            // A deadline is the budget, not a property of the body: say so
            // rather than suggest the fact cannot be evaluated at all.
            ExecutionLimit::Deadline => ResourceRewriteRefusal::Message(
                "evaluating an instance body fact exhausted the verification budget",
            ),
            // A worker-held or worker-changed total is the cause, not the body.
            ExecutionLimit::AuthorityCountPendingLockedWorker
            | ExecutionLimit::AuthorityCountLentToWorker => {
                ResourceRewriteRefusal::OwnedMessage(limit.describe())
            }
            limit => ResourceRewriteRefusal::OwnedMessage(format!(
                "could not evaluate instance body fact: evaluation stopped at {}",
                limit.describe()
            )),
        })?;
        let mut path = crate::kernel::api::exactly_selected_spec_proposition_path(&paths, &context)
            .ok_or("instance body fact needs an unsupported conditional proof")?
            .clone();
        if let Proposition::ConditionIs(condition, truth) = &path.proposition
            && let Some(condition) =
                crate::kernel::machine_integer::comparison::retained_arithmetic_comparison(
                    condition.native_compat(),
                )
        {
            path.proposition = Proposition::condition_is(condition, *truth);
        }
        // An undischarged pure undefined-behavior condition (unchecked
        // arithmetic) is exposed alongside the body fact instead of
        // refusing the rewrite: the author asserted the C meaning, which
        // includes definedness, and every later use re-checks it. Anything
        // else still refuses as before.
        let retained_start = retained_conditions.len();
        for fact in &path.facts {
            if required_obligation_is_exactly_discharged(&context, fact.proposition()) {
                continue;
            }
            // A certified fact is kernel evidence, such as the lower bound an
            // imported population total carries. The rewrite exposes it beside
            // the body facts; the certificate checker reruns this lowering.
            if fact.is_certified() {
                retained_conditions.push(fact.proposition().clone());
                continue;
            }
            if is_pure_undefined_behavior_condition(fact.proposition()) {
                retained_conditions.push(fact.proposition().clone());
                continue;
            }
            return Err(ResourceRewriteRefusal::BodyFactPrerequisiteNotEstablished {
                arm: arm.map(str::to_owned),
                index: ordinal,
                count: source.len(),
                proposition: Box::new(fact.proposition().clone()),
            });
        }
        for goal in &path.obligations {
            if required_obligation_is_exactly_discharged(&context, goal.proposition())
                || quantified_resource_fact_memory_obligation_is_discharged(
                    &context,
                    goal.proposition(),
                )
            {
                continue;
            }
            // An asserted resource clause includes the expression domains
            // recorded by arithmetic lowering, regardless of their logical
            // shape. SymbolicMemory/access prerequisites still require evidence.
            if goal.evaluation_domain {
                retained_conditions.push(goal.proposition().clone());
                continue;
            }
            return Err(ResourceRewriteRefusal::BodyFactPrerequisiteNotEstablished {
                arm: arm.map(str::to_owned),
                index: ordinal,
                count: source.len(),
                proposition: Box::new(goal.proposition().clone()),
            });
        }
        for condition in &retained_conditions[retained_start..] {
            context = context.assume_proposition(condition.clone());
        }
        if let Some(established) = established_assumptions
            && !established.retains_required_obligations()
            && !resource_body_fact_is_established(established, &path.proposition)
        {
            return Err(ResourceRewriteRefusal::BodyFactNotEstablished {
                arm: arm.map(str::to_owned),
                index: ordinal,
                count: source.len(),
                spelling: None,
                proposition: Box::new(path.proposition.clone()),
            });
        }
        let record = ResourceBodyClauseRecord {
            arm: arm.map(str::to_owned),
            ordinal,
            proposition: path.proposition.clone(),
            introductions: path.introductions.clone(),
        };
        context = context.assume_proposition(path.proposition.clone());
        records.push(record);
    }
    Ok((records, retained_conditions))
}

/// A fold body fact may name a memory load from before a disjoint call while
/// the selected body is lowered against the post-call frame. Exact discharge
/// remains the normal route; the checked pointer-load transport is the
/// narrowly-scoped fallback for this explicit resource clause. This keeps
/// call/frame transport out of the general fact path while still allowing a
/// resource fold to reuse a load whose stored pointer value the checked
/// memory derivation proves unchanged.
fn resource_body_fact_is_established(
    established: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    if required_obligation_is_exactly_discharged(established, proposition) {
        return true;
    }
    // A copied wide word can have a fresh read name that recurs inside its
    // packed-word equation. Query only exact 64-bit neighbors of the stated
    // endpoints and captured variables, using checked equality substitution. A
    // candidate must still be established by the original context.
    if let Some((
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    )) = (proposition).condition_native()
    {
        let mut variables = std::collections::BTreeSet::new();
        crate::kernel::reasoning::variable_collection::collect_proposition_capture_variables(
            proposition,
            &mut variables,
        );
        let endpoints = [left.as_ref().clone(), right.as_ref().clone()]
            .into_iter()
            .chain(variables.into_iter().map(MachineTerm::Variable));
        for endpoint in endpoints {
            for (alias, evidence) in established.exact_uint64_equalities(&endpoint) {
                crate::instrumentation::record_deterministic_work(1);
                let equality = Proposition::condition_is(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: Box::new(endpoint.clone()),
                        right: Box::new(alias.clone()),
                    },
                    true,
                );
                let evidence = Proposition::condition_is(evidence.clone(), true);
                if let Ok(candidate) =
                    crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality(
                        proposition,
                        &equality,
                        std::slice::from_ref(&evidence),
                    )
                    && candidate != *proposition
                    && required_obligation_is_exactly_discharged(established, &candidate)
                {
                    return true;
                }
            }
        }
    }
    // A model binding can select an equal address spelling while the
    // logical read retains its own producer identity. Reuse only the exact
    // typed read relation already checked for contract facts: it requires
    // the same recorded state and address, or a checked stored value.
    if let Some((ConditionTerm::AddressEqual(left, right), true)) = (proposition).condition_native()
        && crate::kernel::memory_history::pointer_read_has_recorded_value(left, right, established)
    {
        return true;
    }
    if matches!(&proposition, condition_source_0 @ Proposition::ConditionIs(
        _,
        true,
    ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::AddressOffsetEqual(left, right), _)) if (crate::kernel::memory_history::pointer_load_offset_proven_equal(
        left,
        right,
        established,
    )))) {
        return true;
    }
    // A field of an abstract type is read at the fold's state, while the
    // unfold or step that stated its value read it at an earlier one. The
    // two loads denote one value when the states are proven to agree at
    // its address.
    if let Proposition::ConditionIs(condition, value) = proposition
        && established.proves_algebraic_condition_modulo_states(condition.native_compat(), *value)
    {
        return true;
    }
    body_fact_is_established_through_a_pointer_alias(established, proposition)
}

/// Whether the body fact is established once one of its symbolic pointers
/// is spelled as a pointer an exact fact proves equal to it.
///
/// A proved pointer equality names one address two ways, and the lowering
/// of an arm's fact does not always choose the spelling the proof stated
/// the fact under: a frame's identity passed to a pure function can lower
/// through the C local proved equal to it while the constructor payload
/// beside it keeps the model's name. Substituting equals for equals is
/// sound, and each candidate is still checked exactly. The work is bounded
/// by the fact's own pointer variables times the exact aliases filed under
/// each, and is reached only after the exact check has refused.
fn body_fact_is_established_through_a_pointer_alias(
    established: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    // A C pointer can have both a symbolic base and a scaled offset, even
    // inside a pure-function argument. Query the actual goal's pointers,
    // rather than only bare symbolic variables. Each candidate still needs
    // exact evidence after capture-avoiding substitution. Null is excluded
    // by the collector: its aliases may include every empty link in a path.
    for pointer in crate::kernel::proof::term_rewrite::proposition_pointer_terms(proposition) {
        for alias in established.exact_pointer_aliases(&pointer) {
            let candidate =
                crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_exact(&pointer, alias)
                    .proposition(proposition);
            if candidate != *proposition
                && required_obligation_is_exactly_discharged(established, &candidate)
            {
                return true;
            }
        }
    }
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_capture_variables(
        proposition,
        &mut variables,
    );
    variables.into_iter().any(|variable| {
        established
            .exact_pointer_aliases(&Address::symbolic(variable))
            .any(|alias| {
                let candidate =
                    crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_address_variable(
                        variable, alias,
                    )
                    .proposition(proposition);
                candidate != *proposition
                    && required_obligation_is_exactly_discharged(established, &candidate)
            })
    })
}

/// Exchange one exclusive instance for its immediate memory body, or back.
/// SymbolicMemory-only bodies need no open token, including guarded/matched bodies.
/// Recursive children require explicit independent child selections.
#[cfg(test)]
pub(crate) fn rewrite_resource_instance(
    state: &ExecutionState,
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    assumptions: &PureFactContext,
    unfold: bool,
) -> Result<(ExecutionState, Vec<Proposition>), ResourceRewriteRefusal> {
    let result = rewrite_resource_instance_selecting_children(
        state,
        instance,
        definition,
        std::slice::from_ref(definition),
        assumptions,
        unfold,
        None,
    )?;
    Ok((result.state, result.semantic_facts))
}

/// The composite definition a matched arm's child names. A child of the
/// parent's own family resolves to the definition already in hand; any other
/// declared resource is looked up in the registered definitions, so the
/// child's own parameters and fields decide what the rewrite checks.
pub(in crate::kernel) fn child_composite_definition<'a>(
    definition: &'a CompositeResourceDefinition,
    definitions: &'a [CompositeResourceDefinition],
    child: &ResourceChildSpec,
) -> Result<&'a CompositeResourceDefinition, &'static str> {
    if child.resource == definition.name() {
        return Ok(definition);
    }
    definitions
        .binary_search_by(|candidate| candidate.name().cmp(&child.resource))
        .ok()
        .map(|index| &definitions[index])
        .ok_or("resource match child has no registered definition")
}

/// Reuse an immutable algebraic payload when a constructor is matched again.
/// The caller must have checked this constructor case; injectivity then makes
/// its fresh binding equal to this payload. Only variables representable by
/// Surface's algebraic binder encoding are returned. This reads one field,
/// never follows model children or searches the premise context.
pub(crate) fn arm_algebraic_payload_spelling<'a>(
    scrutinee: &'a AlgebraicTerm,
    variant: &str,
    field_index: usize,
) -> Option<&'a AlgebraicTerm> {
    crate::instrumentation::record_deterministic_work(1);
    let AlgebraicTermNode::Constructor {
        variant: known,
        fields,
    } = &scrutinee.node
    else {
        return None;
    };
    if known != variant {
        return None;
    }
    let AlgebraicValue::Algebraic(payload) = fields.get(field_index)? else {
        return None;
    };
    let AlgebraicTermNode::Variable(variable) = payload.node else {
        return None;
    };
    (variable.0 >= 4_000_000 && (variable.0 - 4_000_000).is_multiple_of(65_536)).then_some(payload)
}

/// Reference type checking uses only the declaration and immutable reference
/// identity/description. It never installs the referenced instance as owned.
fn check_instance_resource_arguments(
    evaluation: &ExecutionState,
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    assumptions: &PureFactContext,
) -> Result<(), ResourceRewriteRefusal> {
    if instance.resource_arguments().len() != definition.resource_parameters().len() {
        return Err("resource reference argument count does not match its declaration".into());
    }
    let mut formal_ids = BTreeSet::new();
    let mut budget = ExecutionBudget::beside_live_state();
    for (reference, formal) in instance
        .resource_arguments()
        .iter()
        .zip(definition.resource_parameters())
    {
        if formal
            .instance_identity()
            .is_none_or(|identity| !formal_ids.insert(identity))
        {
            return Err("resource reference parameters require distinct named binders".into());
        }
        let schema = formal
            .instance_schema()
            .ok_or("resource reference parameter requires a named resource type")?;
        let spec = formal
            .instance_resource_spec()
            .ok_or("resource reference parameter requires a named resource type")?;
        if !spec.resource_arguments().is_empty() {
            return Err("nested resource-reference parameter types are not supported yet".into());
        }
        let fact = evaluate_function_resource_spec(evaluation, &spec, assumptions, &mut budget)
            .map_err(|_| "resource reference type evaluation exceeded its budget")?
            .map_err(|error| {
                ResourceRewriteRefusal::OwnedMessage(format!(
                    "could not evaluate resource reference parameter type: {}",
                    super::api::describe_certification_runtime_error(&error)
                ))
            })?;
        let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = fact else {
            return Err("resource reference parameter requires an exclusive resource type".into());
        };
        let description = reference.description();
        if quantity.as_const() != Some(1)
            || !description.resource_arguments().is_empty()
            || description.family() != name
            || description.schema() != schema
            || description.arguments().len() != arguments.len()
            || !description
                .arguments()
                .iter()
                .zip(arguments.iter())
                .all(|(a, b)| {
                    crate::kernel::resource_field_values_proven_equal(
                        (a).into(),
                        (b).into(),
                        assumptions,
                    )
                })
        {
            let binder = formal.binding_name().unwrap_or("resource");
            let spelling = formal
                .source_arguments()
                .or_else(|| spec.source_arguments())
                .map(|arguments| arguments.join(", "));
            let required_type = match spelling {
                Some(arguments) => format!("{name}({arguments})"),
                None if arguments.is_empty() => format!("{name}()"),
                None => format!("{name}(...)"),
            };
            return Err(ResourceRewriteRefusal::OwnedMessage(format!(
                "Requires {binder}: {required_type}"
            )));
        }
    }
    Ok(())
}

pub(crate) fn rewrite_resource_instance_selecting_children(
    state: &ExecutionState,
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    unfold: bool,
    selected_children: Option<&[(String, Variable)]>,
) -> Result<ResourceInstanceRewriteResult, ResourceRewriteRefusal> {
    let _timing = (!unfold).then(|| {
        crate::instrumentation::OperationTiming::new(
            instance.name(),
            "resource fold",
            "resource instance: construct fold",
        )
    });
    rewrite_resource_instance_selecting_children_unspelled(
        state,
        instance,
        definition,
        definitions,
        assumptions,
        unfold,
        selected_children,
    )
    .map_err(|refusal| match refusal {
        // Name the unmatched body's fact as its declaration spells it; arm
        // facts carry no recorded spelling.
        ResourceRewriteRefusal::BodyFactNotEstablished {
            arm: None,
            index,
            count,
            spelling: None,
            proposition,
        } if count == definition.facts.len() => ResourceRewriteRefusal::BodyFactNotEstablished {
            arm: None,
            index,
            count,
            spelling: definition.fact_source_spelling(index).map(str::to_owned),
            proposition,
        },
        refusal => refusal,
    })
}

/// The named children of the body `instance` folds or unfolds into, as
/// the arm the premises select for its model names them, without the
/// children a resource argument supplies. This is a read-only query for
/// the Surface, which completes a fold's child map with it; it selects the
/// arm the way [`rewrite_resource_instance_selecting_children`] does and
/// checks nothing. `None` when no arm is selected.
pub(crate) fn selected_instance_child_names(
    state: &ExecutionState,
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Option<Vec<String>> {
    let children = if definition.matched.is_some() {
        let arm = match selected_instance_match_arm(instance, definition, definitions, assumptions)
        {
            Ok((arm, _)) => arm,
            Err(_) => {
                let assumptions =
                    instance_arm_model_facts(instance, definitions, state, assumptions)
                        .into_iter()
                        .fold(assumptions.clone(), PureFactContext::assume_proposition);
                selected_instance_match_arm(instance, definition, definitions, &assumptions)
                    .ok()?
                    .0
            }
        };
        arm.children.as_slice()
    } else {
        definition.children.as_slice()
    };
    let references = definition
        .resource_parameters()
        .iter()
        .filter_map(|formal| formal.instance_identity())
        .collect::<BTreeSet<_>>();
    Some(
        children
            .iter()
            .filter(|child| !references.contains(&child.binding))
            .map(|child| child.name.clone())
            .collect(),
    )
}

fn rewrite_resource_instance_selecting_children_unspelled(
    state: &ExecutionState,
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    unfold: bool,
    selected_children: Option<&[(String, Variable)]>,
) -> Result<ResourceInstanceRewriteResult, ResourceRewriteRefusal> {
    if definition.name() != instance.name()
        || definition.instance_schema.as_ref() != Some(instance.schema())
        || definition.recursive
        || !definition.witnesses.is_empty()
        || definition.parameters.len() != instance.arguments.len()
        || instance
            .arguments
            .iter()
            .zip(&definition.parameters)
            .any(|(argument, parameter)| {
                argument
                    .as_program_value()
                    .is_none_or(|value| value.program_type() != parameter.program_type())
            })
        || !instance_body_clauses_are_exchangeable(&definition.contains)
    {
        return Err(
            "instance fold/unfold requires a nonrecursive, witness-free memory body".into(),
        );
    }
    let folded_instance = instance.clone();
    let folded = ResourceFact::own(Resource::Instance(folded_instance.clone()));
    if unfold {
        if state.resources.owned_instance(instance.identity) != Some(instance) {
            return Err("instance is not exclusively owned in folded form".into());
        }
    } else if state.resources.owned_instance(instance.identity).is_some() {
        return Err("fold result identity is already in use".into());
    }
    // Capture the caller's closed graph before opening adds temporary facts.
    // Only an empty memory input is attached here; ambient frames keep their
    // existing publication. A later fold then advances the selected delta.
    state.resources.capture_empty_memory_input(assumptions);
    let mut evaluation = instance_body_evaluation(state, instance, definition)?;
    check_instance_resource_arguments(&evaluation, instance, definition, assumptions)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let mut algebraic_bindings = BTreeMap::new();
    let mut integer_bindings = BTreeMap::new();
    let mut constructor_fields = Vec::new();
    // D7 in reverse, at the point of the fold or unfold and against the
    // premises standing there. A loop body that has moved its cursor knows
    // what a child it unfolded earlier is only now, and the arm this rewrite
    // needs is the one those premises leave (A26, gap 57b). The work is this
    // one instance's own arms.
    let instance_refutations = if definition.matched.is_some() {
        instance_arm_model_facts(instance, definitions, state, assumptions)
    } else {
        Vec::new()
    };
    let selected = if definition.matched.is_some() {
        let selection_assumptions = instance_refutations
            .iter()
            .cloned()
            .fold(assumptions.clone(), PureFactContext::assume_proposition);
        let (arm, constructor) = selected_instance_match_arm(
            instance,
            definition,
            definitions,
            &selection_assumptions,
        )
        .map_err(|message| {
            if message == "resource match requires constructor evidence for the instance field" {
                let field_name = definition
                    .matched
                    .as_ref()
                    .and_then(|body| instance.schema().fields().get(body.field_index))
                    .map(|(name, _)| name.as_str())
                    .unwrap_or("<matched field>");
                ResourceRewriteRefusal::OwnedMessage(format!(
                    "cannot fold or unfold resource `{}`: matched field `{field_name}` has no known constructor; match the field first or prove an exact constructor equality",
                    instance.name(),
                ))
            } else {
                ResourceRewriteRefusal::Message(message)
            }
        })?;
        let AlgebraicTermNode::Constructor { fields, .. } = constructor.node else {
            unreachable!()
        };
        constructor_fields = fields.clone();
        for (index, value) in fields.iter().enumerate() {
            let name = arm
                .bindings
                .get(index)
                .ok_or("resource match binding count mismatch")?;
            let binding_type = arm
                .binding_types
                .get(index)
                .ok_or("resource match binding type count mismatch")?;
            let binding_variable = arm
                .binding_variables
                .get(index)
                .ok_or("resource match Integer binding identity count mismatch")?;
            match (binding_type, binding_variable, value) {
                (
                    AlgebraicValueType::Program(_) | AlgebraicValueType::ObjectPointer(_, _),
                    None,
                    AlgebraicValue::Program(value),
                ) => {
                    let ty = value.program_type();
                    evaluation.locals.set_typed(name.clone(), value.clone(), ty);
                }
                (AlgebraicValueType::Integer, Some(variable), AlgebraicValue::Integer(value)) => {
                    if integer_bindings.insert(*variable, value.clone()).is_some() {
                        return Err("resource match Integer bindings reuse an identity".into());
                    }
                }
                (AlgebraicValueType::Algebraic { .. }, None, AlgebraicValue::Algebraic(value)) => {
                    algebraic_bindings.insert(name.clone().into(), value.clone());
                }
                _ => return Err("resource match constructor binding type mismatch".into()),
            }
        }
        Some(arm)
    } else {
        None
    };
    let active = evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut budget,
    )
    .ok_or("instance fold/unfold requires a proved body guard case")?;
    let mut explicit_children = selected_children
        .unwrap_or(&[])
        .iter()
        .map(|(name, identity)| (name.as_str(), *identity))
        .collect::<BTreeMap<_, _>>();
    if explicit_children.len() != selected_children.unwrap_or(&[]).len() {
        return Err("child selection must name every selected arm child exactly once".into());
    }
    let reference_parameters = definition
        .resource_parameters()
        .iter()
        .zip(instance.resource_arguments())
        .map(|(formal, reference)| {
            formal
                .instance_identity()
                .map(|identity| (identity, reference))
                .ok_or("resource reference parameter requires a named binder")
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    // The selected arm's children, or the unmatched body's.
    let body_children = if definition.matched.is_some() {
        selected.map_or(&[][..], |arm| arm.children.as_slice())
    } else {
        check_unmatched_instance_children(instance, definition, definitions)?;
        definition.children.as_slice()
    };
    if selected_children.is_none()
        && body_children
            .iter()
            .any(|child| !reference_parameters.contains_key(&child.binding))
    {
        return Err("recursive children require explicit independent child selections".into());
    }
    for child in body_children {
        if let Some(reference) = reference_parameters.get(&child.binding)
            && let Some(selected) =
                explicit_children.insert(child.name.as_str(), reference.identity())
            && selected != reference.identity()
        {
            return Err("selected child is not the resource argument".into());
        }
    }
    // Name the child an author left out or added: the generic sentence
    // sends them to reread the whole body.
    if let Some(child) = body_children
        .iter()
        .find(|child| !explicit_children.contains_key(child.name.as_str()))
    {
        return Err(ResourceRewriteRefusal::OwnedMessage(if unfold {
            format!(
                "unfold of `{}` must bind its named child `{}`: `let {{ {}: name }} = unfold(...)`",
                definition.name(),
                child.name,
                child.name
            )
        } else {
            format!(
                "fold of `{}` must supply its named child `{}` in its child map: `{{ {}: name }}`",
                definition.name(),
                child.name,
                child.name
            )
        }));
    }
    if let Some(extra) = explicit_children.keys().find(|name| {
        !body_children
            .iter()
            .any(|child| child.name.as_str() == **name)
    }) {
        return Err(ResourceRewriteRefusal::OwnedMessage(format!(
            "`{extra}` is not a named child of `{}` here",
            definition.name()
        )));
    }
    let identities = explicit_children.values().copied().collect::<BTreeSet<_>>();
    if identities.len() != explicit_children.len() || identities.contains(&instance.identity) {
        return Err("child selection must name every selected arm child exactly once".into());
    }
    let body_specs: &[ResourceSpec] = if active {
        selected.map_or(&definition.contains, |arm| &arm.contains)
    } else {
        &[]
    };
    // An owned instance contains well-formed owned quantities. Opening it
    // may therefore expose their nonnegativity, just as it exposes owned
    // memory bounds. A proposed fold has no such authority: its quantities
    // must be proved nonnegative and actually consumed below.
    let entry_assumptions = assumptions;
    let mut opening_assumptions = assumptions.clone();
    let mut opening_facts = Vec::new();
    if unfold {
        for resource in body_specs {
            let ResourceQuantity::Count(quantity) = resource.quantity() else {
                continue;
            };
            // A false clause guard owns no quantity at all. Decide the
            // guard before deriving anything from this clause, using the
            // same checked selection as ordinary resource evaluation.
            if !resource_spec_guard_is_active(
                &evaluation,
                &evaluation,
                resource,
                &opening_assumptions,
                &mut budget,
            )
            .map_err(|_| "instance quantity guard evaluation exceeded its budget")?
            .map_err(|error| {
                ResourceRewriteRefusal::OwnedMessage(format!(
                    "instance quantity requires a proved clause guard case: {}",
                    super::api::describe_certification_runtime_error(&error)
                ))
            })? {
                continue;
            }
            let value = evaluate_loop_effect_segment_value(
                &evaluation,
                quantity,
                &opening_assumptions,
                "instance body quantity",
                &mut budget,
            )
            .map_err(|_| "instance body quantity evaluation exceeded its budget")?
            .map_err(|message| {
                ResourceRewriteRefusal::OwnedMessage(format!(
                    "could not evaluate instance body quantity: {message}"
                ))
            })?;
            let ProgramValue::Int32(quantity) = value else {
                return Err("instance body quantity must have type int32".into());
            };
            let fact = Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: Box::new(quantity),
                    right: Box::new(MachineTerm::constant(0)),
                },
                true,
            );
            opening_assumptions = opening_assumptions.assume_proposition(fact.clone());
            opening_facts.push(fact);
        }
    }
    // The exclusively owned parent already establishes these direct pointer
    // aliases. Retain them before choosing the spelling of its memory body
    // and child arguments, so opening and later closing the same arm agree.
    // Restrict this early phase to bare pointer locals: it neither reads a
    // child nor acquires any extra memory authority. A fold must prove its
    // proposed body facts and must never assume them here.
    if unfold && active && !body_children.is_empty() {
        let early = selected
            .map_or(&definition.facts, |arm| &arm.facts)
            .iter()
            .filter(|fact| match fact {
                SpecProposition::Comparison {
                    left: SpecExpression::ProgramExpression(ProgramExpression::Variable(left)),
                    operator: ComparisonOperator::Equal,
                    right: SpecExpression::ProgramExpression(ProgramExpression::Variable(right)),
                } => {
                    evaluation
                        .locals
                        .get(left)
                        .is_some_and(|value| value.pointer().is_some())
                        && evaluation
                            .locals
                            .get(right)
                            .is_some_and(|value| value.pointer().is_some())
                }
                _ => false,
            })
            .cloned()
            .collect::<Vec<_>>();
        let (clauses, conditions) = lower_selected_resource_body_clauses(
            &evaluation,
            &early,
            selected.map(|arm| arm.variant.as_str()),
            &integer_bindings,
            &algebraic_bindings,
            &opening_assumptions,
            None,
            &mut budget,
        )?;
        for fact in clauses
            .into_iter()
            .map(|clause| clause.proposition)
            .chain(conditions)
        {
            opening_assumptions = opening_assumptions.assume_proposition(fact.clone());
            opening_facts.push(fact);
        }
    }
    let assumptions = &opening_assumptions;
    // A contained authority is exclusive custody, not a readable footprint.
    // Name it from its declared type; the fold below consumes the caller's
    // actual authority, and an unfold returns the one this instance holds.
    let (authority_specs, body_specs): (Vec<&ResourceSpec>, Vec<&ResourceSpec>) = body_specs
        .iter()
        .partition(|spec| matches!(spec.term(), ResourceTerm::PopulationAuthority { .. }));
    let body_specs = body_specs.into_iter().cloned().collect::<Vec<_>>();
    let mut authorities = Vec::with_capacity(authority_specs.len());
    for spec in authority_specs {
        if spec.access() != ResourceAccessMode::Own
            || spec.quantity() != &ResourceQuantity::One
            || spec.guard().is_some()
        {
            return Err("an instance body authority requires the creation ledger".into());
        }
        let authority = evaluate_population_authority_candidate(
            &evaluation,
            &evaluation,
            spec,
            assumptions,
            &mut budget,
        )
        .map_err(|_| "instance body authority evaluation exceeded its budget")?
        .map_err(|error| {
            ResourceRewriteRefusal::OwnedMessage(format!(
                "could not evaluate instance body authority: {}",
                super::api::describe_certification_runtime_error(&error)
            ))
        })?;
        let Resource::PopulationAuthority(description) = authority.resource() else {
            return Err("instance body authority is not a population authority".into());
        };
        if !state.recognizes_population_authority(description) {
            return Err(ResourceRewriteRefusal::OwnedMessage(format!(
                "Requires owns authority({}(...))",
                description.family()
            )));
        }
        authorities.push(authority);
    }
    let body_specs = &body_specs[..];
    // Unfolding assumes the body the fold established, its clauses through
    // pointers of unseen formation included (`assume_entry_clause_spans`);
    // folding checks them.
    let body_assumptions = if unfold {
        assumptions
            .clone()
            .assume_entry_clause_spans()
            .assume_held_resource_domains()
    } else {
        assumptions.clone()
    };
    let mut body = evaluate_function_resource_context_with_normalization(
        &evaluation,
        body_specs,
        // A resource body is rewritten against its own declared memory only;
        // expanding a contained composite here would hand the body read
        // authority it has not opened.
        &[],
        &body_assumptions,
        &mut budget,
        false,
    )
    .map_err(|_| "instance body evaluation exceeded its budget")?
    .map(|(context, _)| context)
    .map_err(|error| {
        ResourceRewriteRefusal::OwnedMessage(format!(
            "could not evaluate instance memory body: {}",
            super::api::describe_certification_runtime_error(&error)
        ))
    })?;
    if !authorities.is_empty() {
        body = body
            .try_compose_into_valid_context_delaying_normalization(authorities, assumptions)
            .map_err(|error| {
                ResourceRewriteRefusal::OwnedMessage(format!(
                    "instance body repeats an authority: {error}"
                ))
            })?;
    }
    // Only the immediate declared memory justifies child-argument loads, not
    // the ambient frame or a child that has not been constructed. On fold,
    // check and consume that memory before allowing it in this scratch view.
    let mut next = state.clone();
    if !unfold {
        for fact in body.facts() {
            next.resources = next
                .resources
                .without_fact_incrementally(fact, assumptions)
                .ok_or_else(|| {
                    ResourceRewriteRefusal::BodyResourceMissing(Box::new(fact.clone()))
                })?;
        }
    }
    let mut child_evaluation = evaluation.clone();
    child_evaluation.resources = body.clone();
    let child_assumptions = assumptions.clone().require_owned_expression_loads();
    let mut resource_bindings = BTreeMap::from([(Variable(u64::MAX), instance.identity)]);
    let mut introduced_children: Vec<ResourceInstance> = Vec::new();
    let mut child_read_definitions = Vec::new();
    for child in body_children {
        crate::instrumentation::record_deterministic_work(1);
        // The child's own definition supplies the parameter types its
        // arguments are coerced to and the schema its fields must satisfy.
        let child_definition = child_composite_definition(definition, definitions, child)?;
        let child_schema = if child_definition.name() == definition.name() {
            instance.schema.clone()
        } else {
            child_definition
                .instance_schema
                .clone()
                .ok_or("resource match child requires a field-bearing definition")?
        };
        let arguments = child
            .arguments
            .iter()
            .zip(&child_definition.parameters)
            .map(|(argument, parameter)| {
                let paths = crate::kernel::spec::evaluate_resource_child_argument_paths(
                    &child_evaluation,
                    argument,
                    &child_assumptions,
                    &algebraic_bindings,
                    &integer_bindings,
                    &mut budget,
                )
                .map_err(|_| "recursive child argument evaluation exceeded its budget")?;
                // A child argument is a prerequisite of the rewrite, not a
                // proof site: it has no obligation vector to receive an
                // unmet condition. Restrict it to the retained exact routes
                // and refuse the rewrite otherwise, which is the
                // conservative equivalent of emitting the obligation.
                if paths.len() != 1
                    || paths[0].facts.iter().any(|fact| {
                        // Kernel-issued read definitions are producer outputs,
                        // not prerequisites to prove again in the parent context.
                        !fact.is_certified()
                            && !required_obligation_is_exactly_discharged(
                                &child_assumptions,
                                fact.proposition(),
                            )
                    })
                    || paths[0].obligations.iter().any(|goal| {
                        !required_obligation_is_exactly_discharged(
                            &child_assumptions,
                            goal.proposition(),
                        )
                    })
                {
                    return Err("recursive child argument requires a proved, readable expression");
                }
                match &paths[0].outcome {
                    ExpressionOutcome::Value(value) => {
                        let value = coerce_program_function_argument_without_obligations(
                            &value.native(),
                            parameter,
                        )
                        .ok_or("recursive child argument type mismatch")?;
                        // The readable expression has passed every prerequisite.
                        // Retain its producer-known term definitions before
                        // comparing or publishing child indices. This adds no
                        // hypothesis or read authority. Publish checked read
                        // equalities into the common context, so every consumer
                        // uses the same graph rather than a fold-only rule.
                        for fact in &paths[0].facts {
                            fact.retain_pointer_read_definition(assumptions);
                            if fact.is_certified()
                                && (fact.is_logical_read_equation()
                                    || fact.generated_load_binding().is_some())
                            {
                                child_read_definitions.push(fact.clone());
                            }
                        }
                        Ok(AlgebraicValue::Program(value))
                    }
                    _ => Err("could not evaluate recursive child argument"),
                }
            })
            .collect::<Result<ResourceArguments, _>>()?;
        let fields = child
            .field_bindings
            .iter()
            .map(|source| {
                match source {
                    ResourceChildField::Constructor(index) => constructor_fields
                        .get(*index)
                        .cloned()
                        .map(StoredResourceField::Input),
                    ResourceChildField::Parent(index) => instance.fields.stored_field(*index),
                }
                .ok_or("invalid child field binding")
            })
            .collect::<Result<Vec<_>, _>>()?;
        let fields = ResourceFieldValues::from_stored(fields);
        let identity = explicit_children[child.name.as_str()];
        if unfold && state.resources.owned_instance(identity).is_some() {
            return Err("unfold child result identity is already in use".into());
        }
        if !child_definition.resource_parameters().is_empty() {
            return Err("nested resource reference arguments require explicit bindings".into());
        }
        let mut child_instance = ResourceInstance::new(
            identity,
            child_definition.name().to_string(),
            arguments,
            child_schema,
            fields,
        )
        .ok_or("recursive child fields or arguments have invalid types")?;
        if child_instance.arguments.len() != child_definition.parameters.len()
            || child_instance
                .arguments
                .iter()
                .zip(&child_definition.parameters)
                .any(|(argument, parameter)| {
                    argument
                        .as_program_value()
                        .is_none_or(|value| value.program_type() != parameter.program_type())
                })
        {
            return Err("recursive child arguments have invalid types".into());
        }
        if let Some(reference) = reference_parameters.get(&child.binding)
            && !reference.matches_instance(&child_instance, assumptions)
        {
            return Err("owned child does not match the resource argument".into());
        }
        if !unfold {
            let actual = state
                .resources
                .owned_instance(identity)
                .ok_or("fold requires an owned, folded child")?;
            if actual.name != child_instance.name
                || actual.schema != child_instance.schema
                || actual.fields.len() != child_instance.fields.len()
            {
                return Err(ResourceRewriteRefusal::OwnedMessage(format!(
                    "child `{}` must be a `{}` instance; the selected one is a `{}`",
                    child.name, child_instance.name, actual.name
                )));
            }
            if actual.arguments.len() != child_instance.arguments.len() {
                return Err("resource child argument count mismatch".into());
            }
            if let Some((index, (a, b))) = actual
                .arguments
                .iter()
                .zip(child_instance.arguments.iter())
                .enumerate()
                .find(|(_, (a, b))| {
                    !crate::kernel::instance_field_values_proven_equal(
                        (a).into(),
                        (b).into(),
                        assumptions,
                    )
                })
            {
                return Err(ResourceRewriteRefusal::ChildArgumentNotEstablished {
                    child: child.name.clone(),
                    index,
                    actual: Box::new(a.into_native()),
                    required: Box::new(b.into_native()),
                });
            }
            if let Some(((field, _), _)) = actual
                .schema
                .fields()
                .iter()
                .zip(actual.fields.iter().zip(child_instance.fields.iter()))
                .find(|(_, (a, b))| {
                    !crate::kernel::resource_field_values_proven_equal(*a, *b, assumptions)
                })
            {
                return Err(ResourceRewriteRefusal::OwnedMessage(format!(
                    "child `{}` field `{field}` is not proven equal to the value the proposed parent fields give it",
                    child.name
                )));
            }
            child_instance = actual.clone();
        }
        resource_bindings.insert(child.binding, identity);
        introduced_children.push(child_instance.clone());
        body = body
            .try_compose_into_valid_context_delaying_normalization(
                [ResourceFact::own(Resource::Instance(
                    child_instance.clone(),
                ))],
                assumptions,
            )
            .map_err(|_| "child ownership is duplicated")?;
    }
    if unfold {
        next.resources = next
            .resources
            .unfold_instance_body(instance, body.facts().iter().cloned(), assumptions)
            .map_err(|error| {
                ResourceRewriteRefusal::OwnedMessage(format!(
                    "instance body overlaps existing ownership: {}",
                    super::api::describe_certification_runtime_error(
                        &resource_context_runtime_error(error)
                    )
                ))
            })?
            .ok_or("instance ownership is missing")?;
    } else {
        // The immediate body was consumed before evaluating child arguments;
        // only the selected children remain to be consumed.
        for child in &introduced_children {
            next.resources = next
                .resources
                .without_fact_incrementally(
                    &ResourceFact::own(Resource::Instance(child.clone())),
                    assumptions,
                )
                .ok_or_else(|| {
                    ResourceRewriteRefusal::BodyResourceMissing(Box::new(ResourceFact::own(
                        Resource::Instance(child.clone()),
                    )))
                })?;
        }
        next.resources = next
            .resources
            .try_compose_into_valid_context_delaying_normalization([folded.clone()], assumptions)
            .map_err(|error| {
                ResourceRewriteRefusal::OwnedMessage(format!(
                    "fold would duplicate instance ownership: {error}"
                ))
            })?;
    }
    evaluation.resources = if unfold {
        next.resources.clone()
    } else {
        state.resources.clone()
    };
    evaluation.resource_bindings = Some(std::sync::Arc::new(resource_bindings));
    let mut facts = body.observable_facts_assuming_valid(assumptions);
    facts.extend(opening_facts.iter().cloned());
    for fact in body.facts() {
        if let Some(coverage) = fact.allocation_bounds_fact(assumptions) {
            facts.push(coverage);
        }
        let Some(range) = fact.memory_range() else {
            continue;
        };
        facts.extend(crate::kernel::admitted_memory_range_span_facts(range));
        facts.push(range.loadable_fact(&state.memory));
    }
    // What a fold consumes is what holding the folded instance lets C read.
    let folded_cells = if unfold {
        Vec::new()
    } else {
        body.facts()
            .iter()
            .filter_map(ResourceFact::memory_own_range)
            .map(|range| ResourceFact::view_memory(range.clone()))
            .collect::<Vec<_>>()
    };
    facts.push(Proposition::ResourceComposition(body));
    let mut body_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    for fact in &facts {
        body_assumptions = body_assumptions.assume_proposition(fact.clone());
    }
    let facts_to_rewrite = selected.map_or(&definition.facts, |arm| &arm.facts);
    let (body_clauses, retained_conditions) = if active {
        lower_selected_resource_body_clauses(
            &evaluation,
            facts_to_rewrite,
            selected.map(|arm| arm.variant.as_str()),
            &integer_bindings,
            &algebraic_bindings,
            &body_assumptions,
            (!unfold).then_some(assumptions),
            &mut budget,
        )?
    } else {
        (Vec::new(), Vec::new())
    };
    facts.extend(body_clauses.iter().map(|clause| clause.proposition.clone()));
    facts.extend(retained_conditions);
    if unfold {
        // The arm this unfold opened is the one the premises standing here
        // leave, so the model fact that forced it is published with the
        // body's own facts: the path, and every later step, then names the
        // constructor this rewrite used.
        facts.extend(instance_refutations);
        // A child instance is born here, so this is where the premises the
        // proof already carries first say something about its model: a guard
        // that refutes one of the child's arms (D7 in reverse) publishes the
        // model fact that refutation forces. A descending loop learns
        // `left.model != Empty` from `root->left != 0`, and the walk that
        // stops learns `left.model == Empty` from `root->left == 0`.
        for child in &introduced_children {
            facts.extend(instance_arm_model_facts(
                child,
                definitions,
                &next,
                assumptions,
            ));
        }
    }
    if unfold {
        // The opened owner and the caller's loan-bound views coexist in the
        // constructed successor. Retain that persistent composition so the
        // existing borrow-partition rule can relate them. The body's isolated
        // composition alone cannot express separation from the outer frame.
        // Publish only after lowering the body: temporary body assumptions
        // must not prepare indexes over the unrelated caller frame.
        facts.extend(next.resources.observable_facts_assuming_valid(assumptions));
    }
    let mut seen = BTreeSet::new();
    let semantic_facts = if unfold {
        // These are consequences of the held instance, already justified by
        // this exchange. Deduplicate only the produced batch; ordinary fact
        // admission handles facts already held by the caller. Asking whether
        // they are stated here would force unrelated deferred fact indexes.
        facts
            .into_iter()
            .filter(|fact| seen.insert(fact.clone()))
            .collect()
    } else {
        // Folding checked each pure body clause in the current state.
        // A transported old-state fact can establish that clause without
        // already spelling the current proposition, so retain that checked
        // consequence for later ensures. Ownership and auxiliary definedness
        // facts remain scoped to checking the body.
        body_clauses
            .iter()
            .map(|clause| clause.proposition.clone())
            // As with unfold, caller membership belongs to fact admission.
            .filter(|fact| seen.insert(fact.clone()))
            .collect()
    };
    next.record_instance_population_exchange(state, instance, !unfold, assumptions)
        .map_err(ResourceRewriteRefusal::OwnedMessage)?;
    // Publish instance consumption records only after the complete rewrite is checked. It names
    // the affected identities without retaining or scanning a proof history.
    if unfold {
        next.resources
            .record_instance_consumption(instance.identity, Some(InstanceConsumption::Unfold));
        for child in &introduced_children {
            next.resources
                .record_instance_consumption(child.identity, None);
        }
    } else {
        next.resources
            .record_instance_consumption(instance.identity, None);
        for (slot, identity) in &explicit_children {
            next.resources.record_instance_consumption(
                *identity,
                Some(InstanceConsumption::FoldChild {
                    parent: instance.identity,
                    slot: (*slot).into(),
                }),
            );
        }
    }
    // Holding an instance lets C read the cells its body owns. A fold makes
    // the instance, so it publishes that read authority here, attached to
    // the new occurrence: it retires when the instance is unfolded, consumed
    // or freed. These views belong to the constructed successor and travel
    // with the resource exchange's retained evidence.
    if !unfold && let Some(folded) = next.resources.owned_instance(instance.identity).cloned() {
        let owner = ResourceFact::own(Resource::Instance(folded.clone()));
        if let Some((occurrence, _)) = next.resources.unique_owned_occurrence_for_fact(&owner) {
            // The cells are the ones this fold just consumed: the body the
            // rewrite evaluated, with the selected arm's constructor
            // bindings in scope.
            let views = folded_cells
                .into_iter()
                .filter(|view| !next.resources.contains_exact_representation(view))
                .collect::<Vec<_>>();
            if !views.is_empty() {
                next.resources = next
                    .resources
                    .clone()
                    .unchecked_with_supported_facts_from_occurrence_with_memory(
                        occurrence,
                        &owner,
                        views,
                        next.memory(),
                    );
            }
        }
    }
    // Child evaluation uses the opening context, a temporary extension of
    // the caller's facts. Once the entire exchange succeeds, carry its
    // checked read definitions to the caller's graph too. These are the
    // existing producer equations, not new public body facts.
    for fact in child_read_definitions {
        fact.retain_pointer_read_definition(entry_assumptions);
    }
    Ok(ResourceInstanceRewriteResult {
        body_active: active,
        state: next,
        semantic_facts,
        body_clauses,
        naming_facts: opening_facts,
    })
}

fn quantified_resource_fact_memory_obligation_is_discharged(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    let Proposition::ForAll { body, .. } = proposition else {
        return false;
    };
    let Proposition::Implies(antecedent, consequent) = body.as_ref() else {
        return false;
    };
    fn assume_conjuncts(
        assumptions: PureFactContext,
        proposition: &Proposition,
    ) -> PureFactContext {
        if let Proposition::And(left, right) = proposition {
            let assumptions = assume_conjuncts(assumptions, left);
            assume_conjuncts(assumptions, right)
        } else {
            assumptions.assume_proposition(proposition.clone())
        }
    }
    assume_conjuncts(assumptions.clone(), antecedent).proves_atomic_memory_or_resource(consequent)
}

mod instance_case_selection;
pub use instance_case_selection::*;

/// Exact conditional guard ingredient of a loop-owned instance. This is a
/// projection of its checked definition, not authority manufactured from a
/// mutex address. More general bodies retain the existing strict loop rule.
pub(super) fn loop_instance_guard(
    state: &ExecutionState,
    instance: &ResourceInstance,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<Option<(Address, ConditionTerm)>, String> {
    let Ok(index) = definitions.binary_search_by(|d| {
        crate::instrumentation::record_deterministic_work(1);
        d.name().cmp(instance.name())
    }) else {
        return Ok(None);
    };
    let definition = &definitions[index];
    if index
        .checked_sub(1)
        .and_then(|i| definitions.get(i))
        .is_some_and(|d| d.name() == instance.name())
        || definitions
            .get(index + 1)
            .is_some_and(|d| d.name() == instance.name())
    {
        return Err("loop guard resource has conflicting definitions".into());
    }
    if !definition.contains_mutex_authority || definition.matched.is_some() {
        return Ok(None);
    }
    let [spec] = definition.contains.as_slice() else {
        return Ok(None);
    };
    let ResourceTerm::MutexGuard {
        mutex,
        state_source,
    } = spec.term()
    else {
        return Ok(None);
    };
    let Some(condition) = definition.condition() else {
        return Ok(None);
    };
    if !definition.children.is_empty()
        || !definition.witnesses.is_empty()
        || definition.instance_schema.as_ref() != Some(instance.schema())
        || spec.guard().is_some()
        || spec.access() != ResourceAccessMode::Own
        || spec.quantity() != &ResourceQuantity::One
        || !definition.facts.is_empty()
        || definition.recursive
        || definition.parameters.len() != instance.arguments().len()
        || *state_source != ResourceStateSource::Current
        || spec.state_source() != ResourceStateSource::Current
        || spec.role() != ResourceTransferRole::Consume
    {
        return Err("conditional loop guard requires a direct guard resource body".into());
    }
    let evaluation = instance_body_evaluation(state, instance, definition)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        &evaluation,
        condition,
        None,
        assumptions,
        &mut budget,
    )
    .map_err(|limit| {
        format!(
            "evaluating the loop guard condition stopped at {}",
            limit.describe()
        )
    })?;
    let [path] = paths.as_slice() else {
        return Err("conditional loop guard requires one model condition".into());
    };
    if !path
        .obligations
        .iter()
        .all(|o| required_obligation_is_exactly_discharged(assumptions, o.proposition()))
    {
        return Err("Requires the loop guard model condition to be defined".into());
    }
    let Proposition::ConditionIs(held, true) = &path.proposition else {
        return Err("conditional loop guard currently requires a positive model comparison".into());
    };
    let pointer = evaluate_loop_effect_segment_value(
        &evaluation,
        mutex,
        assumptions,
        "loop guard mutex",
        &mut budget,
    )
    .map_err(|limit| {
        format!(
            "evaluating the loop guard mutex stopped at {}",
            limit.describe()
        )
    })?;
    let pointer = match pointer {
        Ok(ProgramValue::Pointer(pointer)) => pointer,
        Ok(_) => return Err("loop guard requires a mutex pointer".into()),
        Err(message) => return Err(message.into()),
    };
    Ok(Some((
        pointer.address().clone(),
        (held.clone()).native_compat().clone(),
    )))
}

pub(in crate::kernel) fn instance_body_guard_case(
    state: &ExecutionState,
    instance: &ResourceInstance,
    definition: &CompositeResourceDefinition,
    assumptions: &PureFactContext,
) -> Option<bool> {
    let evaluation = instance_body_evaluation(state, instance, definition).ok()?;
    evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
}

pub(super) fn expand_composite_resource_fact(
    context: &ResourceContext,
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    expand_composite_resource_fact_with_children(context, composite, definitions, at, assumptions)
        .map(|(expanded, _, _)| expanded)
}

/// The kernel's own one-level expansion of a viewed composite, packaged as
/// the evidence `LoanLedger::project` re-checks a child projection against.
/// The expansion runs over the head alone, so the admissible children come
/// from the definition and the current memory, never from the caller's
/// ambient resource context or its own list of exposed facts (D2 law 10).
pub(crate) fn checked_composite_projection_evidence(
    viewed: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> Option<CompositeProjectionEvidence> {
    // Projection checks the selected head alone. Checked construction attaches
    // its closed equality graph before expansion adds dependent child resources;
    // it must not publish or borrow authority from the ambient resource frame.
    let head = ResourceContext::new()
        .try_compose_with_fact(viewed.clone(), assumptions)
        .ok()?;
    #[cfg(test)]
    head.observe_composite_context();
    let (_, children, _) = expand_composite_resource_fact_with_children(
        &head,
        viewed,
        definitions,
        &crate::kernel::ProgramPoint::of_memory(memory),
        assumptions,
    )?;
    CompositeProjectionEvidence::from_checked_expansion(viewed.clone(), children)
}

pub(super) fn expand_composite_resource_fact_with_children(
    context: &ResourceContext,
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<ResourceFact>, Vec<ResourceFact>)> {
    construct_composite_resource_body(context, composite, definitions, at, assumptions, None, None)
        .map(|body| (body.expanded, body.children, body.raw_children))
}

/// Occurrences recorded while evaluating the body, before normalization.
/// Normalization certifies their composition but never supplies their identity.
struct CompositeBodyConstruction {
    // Values chosen by this producer, retained by returned-body construction.
    witnesses: Vec<ProgramValue>,
    expanded: ResourceContext,
    children: Vec<ResourceFact>,
    raw_children: Vec<ResourceFact>,
    occurrences: Vec<(ResourceFact, ResourceOccurrenceId)>,
    transferred: Vec<Option<mixed_return_resources::ConsumedCellReturn>>,
    opened: bool,
}

impl CompositeBodyConstruction {
    fn opaque(context: &ResourceContext) -> Self {
        Self {
            witnesses: Vec::new(),
            expanded: context.clone(),
            children: Vec::new(),
            raw_children: Vec::new(),
            occurrences: Vec::new(),
            transferred: Vec::new(),
            opened: false,
        }
    }
}

pub(in crate::kernel) struct HeldCompositeBody {
    source: ResourceOccurrenceId,
    frame: ResourceContext,
    children: Vec<ResourceFact>,
}

impl HeldCompositeBody {
    pub(in crate::kernel) fn into_parts(
        self,
    ) -> (ResourceOccurrenceId, ResourceContext, Vec<ResourceFact>) {
        (self.source, self.frame, self.children)
    }
}

#[allow(clippy::too_many_arguments)]
fn construct_composite_resource_body(
    context: &ResourceContext,
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
    selected: Option<ResourceOccurrenceId>,
    return_admission: Option<&mut mixed_return_resources::ReturnFrontierAdmission>,
) -> Option<CompositeBodyConstruction> {
    construct_composite_resource_body_with_source(
        context,
        composite,
        definitions,
        at,
        assumptions,
        selected,
        return_admission,
        CompositeBodySource::Held,
    )
}

#[derive(Clone, Copy)]
enum CompositeBodySource {
    Held,
    Description,
}

#[allow(clippy::too_many_arguments)]
fn construct_composite_resource_body_with_source(
    context: &ResourceContext,
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
    selected: Option<ResourceOccurrenceId>,
    mut return_admission: Option<&mut mixed_return_resources::ReturnFrontierAdmission>,
    source_kind: CompositeBodySource,
) -> Option<CompositeBodyConstruction> {
    let Resource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = &definitions[definitions
        .binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        })
        .ok()?];
    if definition.instance_schema.is_some() || definition.matched.is_some() {
        return None;
    }
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    // A possibly empty owned head supplies no body cell. Empty token
    // populations have no body authority to expose, so their symbolic
    // quantities still participate in ordinary transfer planning.
    if !definition.contains().is_empty()
        && !composite.is_view()
        && !composite.has_proven_positive_quantity(assumptions)
    {
        return Some(CompositeBodyConstruction::opaque(context));
    }
    // A viewed composite carries its loan dependency on the folded
    // occurrence.  Expansion must transfer that exact bundle to only the
    // newly inserted child occurrences; equal children in the ambient frame
    // are not eligible destinations.
    let source = selected.or_else(|| context.first_exact_occurrence(composite))?;
    let borrowed_parent = if composite.is_view() {
        context.loan_dependency(source).cloned()
    } else {
        None
    };
    let expansion_base = context
        .clone()
        .without_exact_representation_for_occurrence(source)?;
    let mut state = ExecutionState::at_point(at).with_resource_context(expansion_base.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_program_value()?;
        if parameter.program_type() != argument.program_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.binding_name().clone(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    let witnesses = if selected.is_some() {
        bind_composite_witness_values(
            definition,
            &(arguments).native_values(),
            &mut state,
            None,
            assumptions,
        )?
    } else {
        bind_composite_witnesses(
            definition,
            &(arguments).native_values(),
            &mut state,
            assumptions,
        )?
    };
    let mut budget = ExecutionBudget::beside_live_state();
    // Opening a held composite assumes the body its fold established
    // (`assume_entry_clause_spans`).
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        .assume_entry_clause_spans()
        .assume_held_resource_domains();
    let mut child_facts = Vec::new();
    let Some(body_active) = evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    ) else {
        // A guarded folded resource remains opaque until the current path
        // decides its condition.
        return Some(CompositeBodyConstruction::opaque(context));
    };
    for contained in if body_active {
        definition.contains()
    } else {
        &[]
    } {
        let child_result = crate::instrumentation::measure_operation(
            name,
            "composite expansion",
            "composite child lowering",
            || {
                evaluate_function_resource_spec(
                    &state,
                    contained,
                    &evaluation_assumptions,
                    &mut budget,
                )
            },
        );
        let Ok(Ok(child)) = child_result else {
            return None;
        };
        state.resources = state
            .resources
            .clone()
            .unchecked_with_fact(resource_clause_read_supply(&child, &evaluation_assumptions));
        child_facts.push(child);
    }
    let raw_children = if composite.is_own() {
        child_facts.clone()
    } else {
        child_facts
            .iter()
            .map(|fact| ResourceFact::View(fact.resource().clone()))
            .collect()
    };
    let mut transferred = Vec::new();
    if let Some(admission) = return_admission.as_deref_mut() {
        for child in &raw_children {
            transferred.push(admission.admit(child, assumptions)?);
        }
    }
    // The held head supplies the separating body and its frame relationship.
    // Normalize only its explicit body, never rediscover that relationship in
    // the ambient frame or reuse an equal ambient child's occurrence.
    let children = coalesce_written_resource_descriptions(raw_children.clone(), assumptions);
    let emitted = if selected.is_some() || return_admission.is_some() {
        raw_children.clone()
    } else {
        children.clone()
    };
    let (mut expanded, inserted) =
        if matches!(source_kind, CompositeBodySource::Description) && return_admission.is_none() {
            // This head is an unevidenced return description. Its producer must
            // construct its body against the already emitted description frontier.
            expansion_base
                .install_established_partition(emitted, assumptions)
                .ok()?
        } else {
            ResourceContext::install_held_composite_body(
                HeldCompositeBody {
                    source,
                    frame: expansion_base,
                    children: emitted,
                },
                assumptions,
            )
        };
    if let Some(binding) = borrowed_parent {
        for (child, occurrence) in &inserted {
            if child.is_view() {
                expanded = expanded.with_loan_dependency(
                    *occurrence,
                    crate::kernel::loans::LoanViewBinding {
                        viewed: child.clone(),
                        ..binding.clone()
                    },
                );
            }
        }
    }
    Some(CompositeBodyConstruction {
        witnesses,
        expanded,
        children,
        raw_children,
        occurrences: inserted,
        transferred,
        opened: true,
    })
}

/// The proposition asserting the opposite of `proposition`, without adding a
/// logical rule: a bare condition flips its value, a negation drops, and
/// anything else is wrapped in one `Not`.
fn negated_contract_proposition(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::condition_is(condition.clone(), !value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// Decide one lowered contract guard by the retained exact routes only:
/// `Some(true)` when the guard holds, `Some(false)` when its opposite does,
/// and `None` when neither is decided.
///
/// `None` is not "false". It is the answer that leaves the choice to the
/// consumer — which refuses the refinement, keeps both specification paths,
/// or emits an obligation — instead of letting a general proof search inside
/// the kernel settle a contract branch.
fn guard_value_by_exact_routes(assumptions: &PureFactContext, guard: &Proposition) -> Option<bool> {
    if required_obligation_is_exactly_discharged(assumptions, guard) {
        return Some(true);
    }
    required_obligation_is_exactly_discharged(assumptions, &negated_contract_proposition(guard))
        .then_some(false)
}

/// Decide one guard: `Some(true)`, `Some(false)`, or `None` for undecided.
///
/// Package 10(b) removed the general-prover leg, so every answer now comes
/// from the exact fact index, the frozen condition checker on a bare
/// condition, or the frozen atomic memory/resource checkers. An undecided
/// guard travels to the caller, which keeps both specification paths or
/// refuses the operation.
///
/// `resource_guard_conjunction` is the reaching fixture for a guard that is
/// not a bare condition. The obligation check below has no reaching fixture:
/// a guard is the condition of a resource body, and a resource condition must
/// be load-free, so the lowered guard path carries no obligation.
pub(super) fn evaluate_guarded_contract_condition(
    condition: &SpecProposition,
    state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<bool> {
    evaluate_guarded_contract_condition_with_loop_entry(condition, state, None, assumptions, budget)
}

pub(crate) fn evaluate_guarded_contract_condition_with_loop_entry(
    condition: &SpecProposition,
    state: &ExecutionState,
    loop_entry_state: Option<&ExecutionState>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<bool> {
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        state,
        condition,
        loop_entry_state,
        assumptions,
        budget,
    )
    .ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    if !path.obligations.iter().all(|obligation| {
        required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
    }) {
        return None;
    }
    let guard_assumptions = {
        path.facts
            .iter()
            .filter(|fact| fact.is_certified())
            .fold(assumptions.clone(), |context, fact| {
                context.assume_proposition(fact.proposition().clone())
            })
    };
    let assumptions = &guard_assumptions;
    let proves_body_condition = |proposition: &Proposition| match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves_condition_exact(condition.native_compat(), *value)
                || assumptions.decide(condition.native_compat()) == Some(*value)
                || assumptions.proves_atomic_without_search(proposition)
        }
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.proves_condition_exact(condition.native_compat(), !*value)
                    || assumptions.decide(condition.native_compat()) == Some(!*value)
                    || assumptions.proves_atomic_without_search(&Proposition::condition_is(
                        condition.clone(),
                        !*value,
                    ))
            }
            _ => false,
        },
        // No general prover leg. A guard this does not decide is undecided,
        // and the caller keeps both specification paths or refuses the
        // operation rather than having the kernel search for a proof.
        _ => required_obligation_is_exactly_discharged(assumptions, proposition),
    };
    if proves_body_condition(&path.proposition) {
        super::assumptions::record_consulted_premises(assumptions, &path.proposition);
        return Some(true);
    }
    let false_proposition = negated_contract_proposition(&path.proposition);
    if proves_body_condition(&false_proposition) {
        super::assumptions::record_consulted_premises(assumptions, &false_proposition);
        Some(false)
    } else {
        None
    }
}

/// Select one conditional resource effect from the facts available before a
/// call (or at a function's entry). A resource clause is not a new proof
/// search: its guard must already be decided by the caller's proof facts.
fn resource_spec_guard_is_active(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    resource: &ResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<bool, RuntimeError>> {
    let Some(guard) = resource.guard() else {
        return Ok(Ok(true));
    };
    match evaluate_guarded_contract_condition_with_loop_entry(
        guard,
        state,
        Some(entry_state),
        assumptions,
        budget,
    ) {
        Some(active) => Ok(Ok(active)),
        None => Ok(Err(RuntimeError::FunctionContract(
            "could not select a conditional resource effect: its pre-state condition is not proven"
                .to_string(),
        ))),
    }
}

fn evaluate_composite_resource_body_condition(
    definition: &CompositeResourceDefinition,
    state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<bool> {
    definition.condition().map_or(Some(true), |condition| {
        evaluate_guarded_contract_condition(condition, state, assumptions, budget)
    })
}

pub(super) fn expand_all_composite_resource_facts(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    expand_all_composite_resource_facts_with_composites(context, definitions, at, assumptions)
        .map(|(resources, _)| resources)
}

/// [`expand_all_composite_resource_facts`], also returning every composite
/// the expansion opened, nested ones included.
pub(super) fn expand_all_composite_resource_facts_with_composites(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<ResourceFact>)> {
    let mut opened = Vec::new();
    let mut cached = context.clone();
    let supports = context
        .composite_facts()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .flat_map(|support| {
            context
                .cached_supported_expansions(&support)
                .into_iter()
                .map(move |(occurrence, expansion)| (support.clone(), occurrence, expansion))
        })
        .collect::<Vec<_>>();
    for (support, support_occurrence, expansion) in supports {
        if expansion.as_slice() == [support.clone()] {
            continue;
        }
        cached = cached.without_exact_representation_for_occurrence(support_occurrence)?;
        opened.push(support.clone());
        let missing = expansion
            .into_iter()
            .filter(|fact| {
                !cached.contains_exact_representation(fact)
                    && !cached.covers_exact_owned_piece(fact, assumptions)
            })
            .collect::<Vec<_>>();
        // This is the selected held head's already established partition.
        cached = cached
            .install_established_partition(missing, assumptions)
            .ok()?
            .0;
    }
    let (resources, composites) =
        expand_composite_resource_context(&cached, definitions, at, assumptions)?;
    opened.extend(composites);
    Some((resources, opened))
}

/// Authority controls need their live ledger to expose the contained
/// authority. Generic composite expansion has only memory and cannot create
/// that child from a resource declaration.
fn expand_checked_authority_controls(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<ResourceFact>)> {
    let mut expanded = context.clone();
    let mut controls = Vec::new();
    for fact in context.composite_facts() {
        let Resource::Composite { name, .. } = fact.resource() else {
            continue;
        };
        let definition = definitions
            .iter()
            .find(|definition| definition.name() == name)?;
        if !definition
            .contains()
            .iter()
            .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
        {
            continue;
        }
        let (children, _) = state
            .checked_authority_wrapper_body(fact, definition, assumptions)
            .ok()?;
        expanded = expanded.without_fact_incrementally(fact, assumptions)?;
        // A checked supporting expansion may already expose an exact child.
        // Reuse that ownership rather than composing a second occurrence.
        let children = children
            .into_iter()
            .filter(|child| {
                !expanded.contains_exact_representation(child)
                    && !expanded.covers_exact_owned_piece(child, assumptions)
            })
            .collect::<Vec<_>>();
        expanded = expanded
            .install_established_partition(children, assumptions)
            .ok()?
            .0;
        controls.push(fact.clone());
    }
    Some((expanded, controls))
}

pub(super) fn expand_all_composite_resource_facts_at_state(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    let (expanded, _) =
        expand_checked_authority_controls(context, definitions, state, assumptions)?;
    expand_all_composite_resource_facts(&expanded, definitions, &state.program_point(), assumptions)
}

/// Expands only the folded branches needed to expose `target`, leaving
/// unrelated and deeper recursive resources folded.
pub(super) fn expose_composite_resource_fact(
    context: &ResourceContext,
    target: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    // Exposure unfolds composites until the target is held. A memory target
    // is looked up by structure at every context first: the indexed answer
    // for a cell an unfolded body names outright. Only when no unfolding
    // holds it by structure does each context, in the same order, answer
    // with the reasoning the resource algebra applies.
    let structural = target.memory_range().is_some();
    // A token or composite target that the starting context already holds
    // needs no unfolding, and the starting context is the first one the
    // search below would accept. Answering from the index first keeps
    // exposing each of a context's members from re-expanding every composite
    // it still holds, which made exposing all of them quadratic.
    if !structural && context.satisfies_fact(target, assumptions) {
        return Some(context.clone());
    }
    let mut visited = Vec::new();
    let mut seen = BTreeSet::new();
    let mut pending = VecDeque::from([context.clone()]);
    while let Some(context) = pending.pop_front() {
        if !seen.insert(context.clone()) {
            continue;
        }
        if (structural && context.satisfies_memory_fact_structurally(target))
            || (!structural && context.satisfies_fact(target, assumptions))
        {
            return Some(context);
        }
        // The composite whose pointer argument is the target's base by
        // structure is unfolded first: when any composite holds the cell,
        // it is that one.
        let mut composites = context
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), Resource::Composite { .. }))
            .cloned()
            .collect::<Vec<_>>();
        if let Some(required) = target.memory_range() {
            composites
                .sort_by_key(|composite| !composite_names_pointer_base(composite, required.base()));
        }
        for composite in &composites {
            let expanded = expand_composite_resource_fact(
                &context,
                composite,
                definitions,
                &crate::kernel::ProgramPoint::of_memory(memory),
                assumptions,
            )?;
            if expanded == context {
                continue;
            }
            if structural && expanded.satisfies_memory_fact_structurally(target) {
                return Some(expanded);
            }
            pending.push_back(expanded);
        }
        visited.push(context);
    }
    visited
        .into_iter()
        .find(|context| context.satisfies_fact(target, assumptions))
}

mod composite_expansion;
pub(crate) use composite_expansion::*;

/// Whether a body outcome establishes every resource the contract returns,
/// by the rule contract certification applies to a `produces` claim: each
/// returned resource, read as one jointly returned context, is satisfied by
/// the body's returned context definitionally, so a composite whose pieces
/// and facts the body holds counts as returned, and a duplicable body such
/// as a view yields any quantity, while a consumed cell the body no longer
/// holds does not.
pub(super) fn function_return_resources_definitionally_established(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: &FunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    let (value, return_state, exceptional) = match outcome {
        FunctionOutcome::Return { value, state } => (value, state, false),
        FunctionOutcome::Throw { value, state } => (value, state, true),
        _ => return false,
    };
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let Some(callee_state) =
        bind_program_function_arguments(caller_state, function, &argument_values)
    else {
        return false;
    };
    let exit_memory = if exceptional {
        return_state.memory().clone()
    } else {
        let Ok(memory) = function_exit_memory(caller_state, return_state, value, function) else {
            return false;
        };
        memory
    };
    let mut claim_return_state = return_state.clone();
    claim_return_state.set_memory(exit_memory.clone());
    let definitions = function.composite_resource_definitions();
    let post_resources = {
        expand_all_composite_resource_facts_at_state(
            claim_return_state.resources(),
            definitions,
            &claim_return_state,
            assumptions,
        )
    };
    let Some(post_resources) = post_resources else {
        return false;
    };
    let post_resource_facts = post_resources.observable_facts_assuming_valid(assumptions);
    let assumptions = assumptions_with_propositions(assumptions, &post_resource_facts);
    let mut post_state = callee_state.with_memory_continuing(&claim_return_state, exit_memory);
    post_state.resources = post_resources;
    post_state.population_access = return_state.population_access.clone();
    post_state.observed_population_families = return_state.observed_population_families.clone();
    // Preserve checked body consumption evidence when reconstructing the exit.
    post_state.population_effects = return_state.population_effects.clone();
    if exceptional {
        post_state.locals.set_typed(
            CONTRACT_EXCEPTION,
            value.clone().into_native(),
            value.native().program_type(),
        );
    } else if function.return_type() != ProgramType::Void {
        post_state.locals.set_typed(
            CONTRACT_RESULT,
            value.clone().into_native(),
            function.return_type(),
        );
    }
    let mut budget = ExecutionBudget::beside_live_state();
    if check_mutex_helper_body_return(
        caller_state,
        &claim_return_state,
        function.contract_interface(),
        &assumptions,
        &mut budget,
    )
    .is_err()
    {
        return false;
    }
    let entry_resource_state =
        with_contract_argument_views(caller_state, function, &argument_values);
    if !matches!(
        check_wildcard_consumption_at_return(
            &entry_resource_state,
            return_state,
            function.contract_interface(),
            &assumptions,
            &mut budget,
        ),
        Ok(Ok(()))
    ) || !matches!(
        check_acquired_control_member_effects(
            &entry_resource_state,
            return_state,
            function.contract_interface(),
            &assumptions,
            &mut budget,
        ),
        Ok(Ok(()))
    ) {
        return false;
    }
    let Ok(Ok(expected)) = evaluate_function_return_resource_context(
        function,
        &[],
        &entry_resource_state,
        &post_state,
        function.resource_ensures().len(),
        &assumptions,
        &mut budget,
    ) else {
        return false;
    };
    for fact in expected.facts() {
        if let Resource::MutexUse(identity) = fact.resource() {
            let Some(binding) = identity.binding else {
                return false;
            };
            let (Some(ledger), Some(holder)) =
                (return_state.loan_ledger(), return_state.loan_participant())
            else {
                return false;
            };
            if super::mutexes::helper_contracts::permits_return(return_state) {
                continue;
            }
            if ledger
                .check_assumed_mutex_use_return(binding, holder, claim_return_state.resources())
                .is_err()
            {
                return false;
            }
        }
    }
    if !expected.facts().iter().all(|fact| {
        resource_context_satisfies_definitional_fact(
            claim_return_state.resources(),
            fact,
            definitions,
            &claim_return_state.program_point(),
            &assumptions,
        )
    }) {
        return false;
    }
    // Definitional validation answers each returned clause from the whole
    // exit state and so cannot see one exclusive unit counted twice, such as
    // a folded composite returned beside one of its own body children. The
    // returned units are one multiset under both resource semantics: consume
    // them jointly.
    jointly_consume_returned_resource_units(
        claim_return_state.resources(),
        &expected,
        &post_state,
        function.contract_interface(),
        &assumptions,
    )
}

/// Definitional fact validation does not make exclusive units duplicable.
/// Consume the explicit output frontier jointly. Expansion is limited to a
/// required unit's own body and never searches unrelated available heads.
fn consume_returned_resource_unit(
    available: ResourceContext,
    required: &ResourceFact,
    state: &ExecutionState,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
    active: &mut BTreeSet<ResourceFact>,
) -> Option<ResourceContext> {
    // Views are duplicable; the caller already checked their complete
    // definitional validity before entering this quantity check.
    if required.is_view() {
        return Some(available);
    }
    if let Some(remaining) = available
        .clone()
        .without_fact_delaying_normalization(required, assumptions)
    {
        return Some(remaining);
    }
    // Only memory ranges need adjacent supplier fragments to rejoin.
    // Preserve the checked representation of composite/population exchanges.
    if required.memory_range().is_some()
        && let Some(remaining) = available
            .clone()
            .without_fact_incrementally(required, assumptions)
    {
        return Some(remaining);
    }
    let ResourceFact::Own(Resource::Composite { name, .. }, quantity) = required else {
        return None;
    };
    // Authority populations hold ledger fragments and stay linear: a
    // unit the exit state does not hold exactly is consumed through its
    // definition's body.
    interface.composite_resource_definition(name)?;

    let unit = quantity_condition_holds(
        assumptions,
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(quantity.native_compat().clone()),
            right: Box::new(MachineTerm::constant(1)),
        },
    );
    if !active.insert(required.clone()) {
        return None;
    }
    let result = (|| {
        let singleton =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(required.clone());
        let (_, _, written_children) = expand_composite_resource_fact_with_children(
            &singleton,
            required,
            interface.composite_resource_definitions(),
            &state.program_point(),
            assumptions,
        )?;
        if !unit && written_children.iter().any(ResourceFact::is_own) {
            return None;
        }
        // An empty expansion cannot manufacture a missing unit. A
        // protected empty member needs an actually held ledger fragment,
        // and a declaration with no body at all is a token that only a
        // held copy supplies: two `Permit(x)` cannot come from one. A
        // conditional body whose guard is false is refused the same way.
        if written_children.is_empty() {
            return None;
        }
        let mut remaining = available.clone();
        // The required head is a description, not a held owner. Spend each
        // written body occurrence before normalization can coalesce equal
        // memory clauses; their physical overlap does not make them duplicable.
        for child in &written_children {
            remaining = consume_returned_resource_unit(
                remaining,
                child,
                state,
                interface,
                assumptions,
                active,
            )?;
        }
        Some(remaining)
    })();
    active.remove(required);
    result
}

pub(super) fn jointly_consume_returned_resource_units(
    available: &ResourceContext,
    required: &ResourceContext,
    state: &ExecutionState,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
) -> bool {
    let mut remaining = available.clone();
    let mut active = BTreeSet::new();
    for fact in required.facts() {
        let Some(next) = consume_returned_resource_unit(
            remaining,
            fact,
            state,
            interface,
            assumptions,
            &mut active,
        ) else {
            return false;
        };
        remaining = next;
    }
    true
}

fn check_mutex_helper_body_return(
    entry: &ExecutionState,
    returned: &ExecutionState,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<(), RuntimeError> {
    use super::mutexes::helper_contracts::{self, HelperEffect};
    let Some(contract) = helper_contracts::classify(interface)
        .map_err(|message| RuntimeError::FunctionContract(message.into()))?
    else {
        return Ok(());
    };
    match contract.effect {
        HelperEffect::Acquire => {
            if !helper_contracts::same_export_permission(entry, returned)
                || !helper_contracts::permits_return(returned)
            {
                return Err(RuntimeError::FunctionContract(
                    "acquiring helper must return its owned acquired guard and lifetime dependency"
                        .into(),
                ));
            }
            let actual = helper_contracts::exported_guard(returned).expect("checked export");
            let expected = evaluate_function_resource_spec_with_entry(
                entry,
                returned,
                &contract.guard,
                assumptions,
                budget,
            )
            .map_err(|_| {
                RuntimeError::FunctionContract(
                    "mutex helper output evaluation exceeded its budget".into(),
                )
            })??;
            if expected != actual {
                return Err(RuntimeError::MissingResource {
                    resource: Box::new(expected),
                });
            }
        }
        HelperEffect::Release => {
            if returned
                .opaque_mutex_acquisitions
                .as_ref()
                .is_some_and(|held| held.has_local_hold(returned.loan_participant))
            {
                return Err(RuntimeError::FunctionContract(
                    "releasing helper must discharge its consumed guard acquisition".into(),
                ));
            }
        }
    }
    Ok(())
}

/// Whether `available` supplies `required` by its definition: directly, or,
/// for a composite, by the pieces its body names.
///
/// A composite is more than its pieces: an instance is held only while its
/// body holds, so holding it asserts every `fact` of its body. A required composite that `available` does not already hold folded
/// is assembled here from pieces, which is a fold, so each such composite's
/// body facts must be established at `memory` exactly as a checked `fold`
/// establishes them. Without this, an exit whose C stores falsified a body
/// fact published the composite anyway, and every caller then unfolded the
/// false fact. A composite `available` holds folded was checked when it was
/// folded, so it needs no second check.
pub(super) fn resource_context_satisfies_definitional_fact(
    available: &ResourceContext,
    required: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
) -> bool {
    if available.satisfies_fact(required, assumptions) {
        return true;
    }
    let Some(expanded_available) =
        expand_all_composite_resource_facts(available, definitions, at, assumptions)
    else {
        return false;
    };
    let required_context =
        ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(required.clone());
    let Some((required, assembled)) =
        expand_composite_resource_context(&required_context, definitions, at, assumptions)
    else {
        return false;
    };
    assembled.iter().all(|composite| {
        available.satisfies_fact(composite, assumptions)
            || assembled_composite_body_facts_hold(
                composite,
                definitions,
                at,
                &expanded_available,
                assumptions,
            )
    }) && required
        .facts()
        .iter()
        .all(|fact| expanded_available.satisfies_fact(fact, assumptions))
}

/// Whether the body facts of `composite` hold when it is assembled from the
/// pieces in `resources` at `memory`. Each fact is lowered at `memory` with
/// the definition's parameters bound, as a checked `fold` lowers it, and must
/// be established by the kernel's exact routes from `assumptions` and the
/// observable facts of the pieces themselves (their separation, say). There
/// is no search: a fact the path has not established refuses the assembly,
/// and the proof answers with an explicit `fold`. A body whose guard is false
/// at `memory` asserts nothing; an undecided guard refuses.
pub(super) fn assembled_composite_body_facts_hold(
    composite: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    let Resource::Composite { name, arguments } = composite.resource() else {
        return true;
    };
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == name)
    else {
        return false;
    };
    if definition.facts().is_empty() {
        return true;
    }
    if definition.parameters().len() != arguments.len() {
        return false;
    }
    let mut state = ExecutionState::at_point(at).with_resource_context(resources.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let Some(argument) = argument.as_program_value() else {
            return false;
        };
        if parameter.program_type() != argument.program_type() {
            return false;
        }
        state.locals.set_typed(
            parameter.binding_name().clone(),
            argument.clone(),
            parameter.program_type(),
        );
    }
    if bind_composite_witnesses(
        definition,
        &(arguments).native_values(),
        &mut state,
        assumptions,
    )
    .is_none()
    {
        return false;
    }
    let mut budget = ExecutionBudget::beside_live_state();
    match evaluate_composite_resource_body_condition(definition, &state, assumptions, &mut budget) {
        Some(true) => {}
        Some(false) => return true,
        None => return false,
    }
    let piece_facts = resources.observable_facts_assuming_valid(assumptions);
    let assumptions = assumptions_with_propositions(assumptions, &piece_facts);
    definition.facts().iter().all(|fact| {
        let Ok(paths) = lower_spec_proposition_at_state_with_loop_entry(
            &state,
            fact,
            Some(&state),
            &assumptions,
            &mut budget,
        ) else {
            return false;
        };
        let [path] = paths.as_slice() else {
            return false;
        };
        let established = path.facts.iter().fold(assumptions.clone(), |facts, load| {
            facts.assume_proposition(load.proposition().clone())
        });
        established.settles_exactly(&path.proposition)
            || resource_body_fact_is_established(&established, &path.proposition)
    })
}

/// True when every element of a constant-bounded memory range is concretely
/// loadable, so a view of it is represented by the materialized cells rather
/// than a resource fact.
fn view_range_concretely_loadable(memory: &SymbolicMemory, range: &MemoryRange) -> bool {
    let (Some(start), Some(end)) = (range.constant_start(), range.constant_end()) else {
        return false;
    };
    if end <= start || end - start > 64 {
        return false;
    }
    let width = match &range.base().offset {
        AddressOffset::Int32Scaled { byte_width, .. } => u32::try_from(*byte_width).unwrap_or(4),
        _ => 4,
    };
    (start..end).all(|index| {
        let pointer = Address {
            base: range.base().base.clone(),
            offset: AddressOffset::add(
                range.base().offset.clone(),
                AddressOffset::scale_int32(MachineTerm::constant(index), i64::from(width)),
            ),
        };
        memory.is_loadable_concretely(&pointer, width)
    })
}

fn consume_resource_fact_definitionally(
    available: &ResourceContext,
    required: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    at: &ProgramPoint,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    fn consume(
        available: &ResourceContext,
        required: &ResourceFact,
        definitions: &[CompositeResourceDefinition],
        at: &ProgramPoint,
        assumptions: &PureFactContext,
        seen: &mut BTreeSet<(ResourceContext, ResourceFact)>,
    ) -> Option<ResourceContext> {
        if !seen.insert((available.clone(), required.clone())) {
            return None;
        }
        // A view of memory the caller has concretely materialized is freely
        // satisfiable: read access is represented by the materialized cells,
        // mirroring the local-block view rule at call transfer.
        if let ResourceFact::View(Resource::Memory(range)) = required
            && view_range_concretely_loadable(at.memory(), range)
        {
            return Some(available.clone());
        }
        let direct_remaining = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: direct consumption",
            || {
                available
                    .clone()
                    .without_fact_delaying_normalization(required, assumptions)
            },
        );
        if let Some(remaining) = direct_remaining {
            return Some(remaining);
        }
        let normalized = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: normalization",
            || available.clone().normalized(assumptions),
        );
        if &normalized != available
            && let Some(remaining) =
                normalized.without_fact_delaying_normalization(required, assumptions)
        {
            return Some(remaining);
        }

        let required_context =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(required.clone());
        if let Some(expanded_required) = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: expand required",
            || {
                expand_composite_resource_fact(
                    &required_context,
                    required,
                    definitions,
                    at,
                    assumptions,
                )
            },
        ) {
            // Assembling a required composite from pieces is a fold: its body
            // facts must hold here, as in
            // `resource_context_satisfies_definitional_fact`.
            if !assembled_composite_body_facts_hold(
                required,
                definitions,
                at,
                available,
                assumptions,
            ) {
                return None;
            }
            let mut remaining = available.clone();
            for child in expanded_required.facts() {
                remaining = consume(&remaining, child, definitions, at, assumptions, seen)?;
            }
            return Some(remaining);
        }

        for composite in available
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), Resource::Composite { .. }))
        {
            let Some(expanded_available) = crate::instrumentation::measure_operation(
                "kernel",
                "resource containment",
                "resource containment: expand available",
                || {
                    expand_composite_resource_fact(
                        available,
                        composite,
                        definitions,
                        at,
                        assumptions,
                    )
                },
            ) else {
                continue;
            };
            if let Some(remaining) = consume(
                &expanded_available,
                required,
                definitions,
                at,
                assumptions,
                seen,
            ) {
                return Some(remaining);
            }
        }
        None
    }

    consume(
        available,
        required,
        definitions,
        at,
        assumptions,
        &mut BTreeSet::new(),
    )
}

pub(super) fn resource_context_definitionally_contains(
    available: &ResourceContext,
    required: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> bool {
    let mut remaining = available.clone();
    let mut required = required.facts().to_vec();
    required.sort_by_key(resource_fact_transfer_priority);
    for fact in &required {
        let Some(next) = consume_resource_fact_definitionally(
            &remaining,
            fact,
            definitions,
            &crate::kernel::ProgramPoint::of_memory(memory),
            assumptions,
        ) else {
            return false;
        };
        remaining = next;
    }
    true
}

pub(super) fn resource_contexts_definitionally_equivalent_by_consumption(
    left: &ResourceContext,
    right: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> bool {
    resource_context_definitionally_contains(left, right, definitions, memory, assumptions)
        && resource_context_definitionally_contains(right, left, definitions, memory, assumptions)
}

pub(crate) fn evaluate_function_resource_context(
    state: &ExecutionState,
    resources: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, RuntimeError>> {
    evaluate_function_resource_context_with_metadata(
        state,
        resources,
        definitions,
        assumptions,
        budget,
    )
    .map(|result| result.map(|(context, _)| context))
}

mod entry_partition;
pub(crate) use entry_partition::admit_declared_entry_resources;

/// Evaluate a resource section once and retain the source metadata alongside
/// each checked fact.  The ordinary context API below is a compatibility view
/// for callers that only need algebraic containment; transition/effect code
/// must use this metadata-bearing result.
pub(crate) fn evaluate_function_resource_context_with_metadata(
    state: &ExecutionState,
    resources: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(ResourceContext, Vec<CheckedResourceFact>), RuntimeError>> {
    evaluate_function_resource_context_with_normalization(
        state,
        resources,
        definitions,
        assumptions,
        budget,
        true,
    )
}

/// Loop declarations retain the new occurrences and attach inherited loan
/// bindings before normalization can combine unbound views.
pub(crate) fn evaluate_loop_resource_context(
    state: &ExecutionState,
    resources: &[ResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, RuntimeError>> {
    evaluate_function_resource_context_with_entry_and_normalization(
        state,
        state,
        resources,
        &[],
        assumptions,
        budget,
        true,
        true,
    )
    .map(|result| result.map(|(context, _)| context))
}

fn evaluate_function_resource_context_with_normalization(
    state: &ExecutionState,
    resources: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    normalize: bool,
) -> ExecutionResult<Result<(ResourceContext, Vec<CheckedResourceFact>), RuntimeError>> {
    evaluate_function_resource_context_with_entry_and_normalization(
        state,
        state,
        resources,
        definitions,
        assumptions,
        budget,
        normalize,
        false,
    )
}

fn evaluate_function_resource_context_with_entry_and_normalization(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    resources: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    normalize: bool,
    inherit_view_bindings: bool,
) -> ExecutionResult<Result<(ResourceContext, Vec<CheckedResourceFact>), RuntimeError>> {
    // `entry_state` supplies only expressions explicitly marked `old(...)`;
    // `state` supplies current/post expressions and the section's resulting
    // resource context.  Keeping both states here prevents repeated lowering
    // of one entry load from inventing a distinct resource argument.
    let evaluated = match evaluate_resource_clauses_against_whole_section(
        entry_state,
        state,
        resources,
        definitions,
        assumptions,
        budget,
    )? {
        Ok(evaluated) => evaluated,
        Err(error) => return Ok(Err(error)),
    };
    let context = ResourceContext::new_with_equalities(assumptions);
    let checked = evaluated;
    // The section's facts are composed together: one validity check and one
    // normalization for the whole section, not one per fact over the growing
    // context. Instance rewrites retain the declared memory pieces so folding
    // does not need to normalize an ambient block just to consume those
    // pieces.
    let facts = checked.iter().map(|resource| resource.fact.clone());
    let composed = if inherit_view_bindings {
        context
            .install_established_partition(facts, assumptions)
            .map(|(context, inserted)| {
                let context = state.loan_view_bindings().attach_to_inserted_views(
                    state.resources(),
                    context,
                    &inserted,
                    assumptions,
                );
                if normalize {
                    context.normalized_without_discovery(assumptions)
                } else {
                    context
                }
            })
    } else {
        // This evaluates a written separating clause list, not new caller
        // ownership. The actual fold/entry/transfer operation supplies custody.
        context
            .install_established_partition(facts, assumptions)
            .map(|(context, _)| {
                if normalize {
                    context.normalized_without_discovery(assumptions)
                } else {
                    context
                }
            })
    };
    let context = match composed {
        Ok(context) => context,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };
    Ok(Ok((context, checked)))
}

/// The **entry partition**, as facts: at a contract's entry, a transferred
/// memory clause and a borrowed `views` clause of the *same* contract denote
/// disjoint memory, so a store through one is framed from a load through the
/// other.
///
/// **The rule.** For each pair (an entry clause whose fact is owned, an entry
/// clause whose fact is viewed) this produces the ordinary explicit separation
/// `separate(memory(X), memory(Y))` — `Proposition::ResourceSeparate` over
/// two `Resource::Memory` operands, exactly the proposition a written
/// `requires separate(memory(a[0..n]), memory(g[0..1]))` lowers to. Nothing
/// new is invented: the Store ladder already spends it at
/// `memory_history::typed_store_separated_ranges_evidence`, and the caller
/// of this function installs the result as an entry fact beside the
/// `viewable(..)` fact and the byte-count guards the same clause already
/// yields.
///
/// **Why it is sound.** The claim is the ownership partition's own induction,
/// one step down. Every way a contract can be entered checks it, and each
/// check is fail-closed on the side that matters:
///
/// - an ordinary call, a self-call, a call through a function pointer or a
///   `contract` interface, and contract/implementation refinement all funnel
///   through `loans::plan_stable_view_transfer_with_bindings_and_composites`,
///   which reserves *every* owned requirement out of the caller's `residual`
///   before planning a single view, and then requires each view's backing
///   owner to still be found in that residual. A caller that hands the same
///   memory to an `owns` clause and a `views` clause is refused for want of
///   backing, never admitted;
/// - the contract's own entry is checked by
///   `api::install_borrowed_contract_inputs`, which refuses a viewed clause
///   that provably overlaps an owned one (`protected_range_proven_overlapping`)
///   and computes its partition from this very clause list;
/// - at the outer boundary it is an assumption about the environment, in the
///   same class as the ownership the contract already assumes: a precondition's
///   clauses are read as a separating conjunction.
///
/// So the caller owes nothing new for this fact. `docs/internals/resource-tracker.md`,
/// "The entry partition", carries the measured attack table.
///
/// **What it must not pair.**
///
/// - Never an owner and the *owner observation* of its own range. `owns r`
///   also publishes `views r` into a context
///   (`ResourceContext::observable_facts_assuming_valid`,
///   `MemoryResourceAlgebra::pair_validity_error`), and that view is an
///   observation of the very ownership beside it. The discriminator is the
///   origin: this reads the contract's own entry *clause list*, which holds
///   one fact per written clause, never a context's derived facts.
/// - Never two borrowed views: two `views` clauses may overlap freely.
/// - Never two owners: that pair is
///   `memory_history::owned_composition_store_separated_evidence` already
///   (Route B), and duplicating it here would be a second spelling of one rule.
/// - A clause that is not plain memory — a composite, a token, an instance —
///   has no `MemoryRange` to name, and `separate(memory(..), memory(..))`
///   cannot express its footprint without expanding it. Such a pair is
///   skipped outright rather than approximated; `owns *r` is *not* one
///   of those, because `object(r)` lowers to the plain range `r[0..size/4]`.
///
/// **Cost.** At most `#owned × #viewed` clauses of one contract, built once at
/// that contract's entry and never on a query path. This is not the eager
/// pairwise derivation `CLAUDE.md` bans: that ban is about a verifier hot
/// path, and a contract's clause list is bounded written syntax that is walked
/// once per proof. What the facts then cost is what the same clauses written
/// as `requires separate(..)` would cost, which is why a pair the block
/// algebra already decides is skipped: every memory separation the context
/// holds is one more entry the block-pair bucket a coverage or overlap query
/// lands in has to walk (`memory_range_covers`,
/// `memory_ranges_proven_overlapping`), so recording an answer those queries
/// reach anyway buys nothing and is paid for on every query.
pub(crate) fn contract_entry_partition_facts(
    entry_clauses: &[CheckedResourceFact],
) -> Vec<Proposition> {
    let transferred = entry_clauses
        .iter()
        .filter_map(|clause| clause.fact.memory_own_range())
        .collect::<Vec<_>>();
    if transferred.is_empty() {
        return Vec::new();
    }
    let borrowed = entry_clauses
        .iter()
        .filter_map(|clause| clause.fact.memory_view_range());
    let mut facts = Vec::new();
    let mut seen = BTreeSet::new();
    for viewed in borrowed {
        for owned in &transferred {
            // A property of the two ranges alone, so the body proof and
            // contract certification skip the same pairs.
            if owned.base().blocks_proven_distinct(viewed.base()) {
                continue;
            }
            let fact = Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory((*owned).clone())),
                right: Box::new(Resource::Memory(viewed.clone())),
            };
            if seen.insert(fact.clone()) {
                facts.push(fact);
            }
        }
    }
    facts
}

/// Evaluates one contract section's resource clauses against the loadability
/// the whole section supplies, and returns their resources in source order.
///
/// A base load in one clause may read a cell any other clause of the same
/// section owns or views, including a cell inside a folded composite, exactly
/// as a `requires` clause may. The first pass walks the clauses in source
/// order. If it leaves clauses unevaluated, the successful portion is expanded
/// once and the missing-resource edges recorded by each failed clause drive an
/// indexed event queue. A newly supplied memory fact therefore wakes only its
/// dependent clauses; no fixed-point round rescans all pending clauses.
///
/// Each clause contributes its resource exactly once: a clause that evaluates
/// is never revisited, and the caller composes the results once, in source
/// order. Retrying a clause that has not yet produced a resource cannot
/// double-count authority.
///
/// Clauses that no order evaluates are refused by name. That is the honest
/// verdict for a dependency cycle between two clauses and for two clauses that
/// are independently unevaluable; either way the user needs both positions.
fn evaluate_resource_clauses_against_whole_section(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    resources: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<CheckedResourceFact>, RuntimeError>> {
    evaluate_resource_clauses_in_section(
        entry_state,
        state,
        resources,
        definitions,
        assumptions,
        budget,
        true,
    )
}

/// The same indexed dependency queue also prepares the available part of a
/// call's primitive outputs. Unresolved clauses then remain for the return
/// transition, where fresh named outputs can supply their dependencies.
#[allow(clippy::too_many_arguments)]
fn evaluate_resource_clauses_in_section(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    resources: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_complete: bool,
) -> ExecutionResult<Result<Vec<CheckedResourceFact>, RuntimeError>> {
    let selected_load_values = if definitions.is_empty() {
        BTreeMap::new()
    } else {
        selected_instance_resource_load_values(state, definitions, assumptions)
    };
    let mut evaluated: Vec<Option<ResourceFact>> = vec![None; resources.len()];
    let mut active = vec![true; resources.len()];
    let mut supplied: Vec<ResourceFact> = Vec::new();
    // Each successful clause extends a shared persistent prefix. Rebuilding
    // every earlier clause for each new one makes a flat contract quadratic.
    let mut evaluation_resources = state.resources().clone();
    evaluation_resources.capture_empty_memory_input(assumptions);
    let mut failures: Vec<Option<RuntimeError>> = vec![None; resources.len()];
    let mut dependencies: Vec<Vec<ResourceFact>> = vec![Vec::new(); resources.len()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    for (index, resource) in resources.iter().enumerate() {
        match resource_spec_guard_is_active(entry_state, state, resource, assumptions, budget)? {
            Ok(true) => {}
            Ok(false) => {
                active[index] = false;
                continue;
            }
            Err(error) => return Ok(Err(error)),
        }
        let evaluation_state = state
            .clone()
            .with_resource_context(evaluation_resources.clone());
        let (outcome, missing) = evaluate_resource_clause_with_dependencies(
            entry_state,
            &evaluation_state,
            resource,
            &selected_load_values,
            assumptions,
            budget,
        )?;
        match outcome {
            Ok(resource) => {
                // The scratch prefix may already contain this exact owned
                // instance. Repeating it makes identity lookup ambiguous;
                // the final clause context still checks duplicate ownership.
                if !matches!(resource.resource(), Resource::Instance(_))
                    || !evaluation_resources.contains_exact_representation(&resource)
                {
                    evaluation_resources = evaluation_resources
                        .unchecked_with_fact(resource_clause_read_supply(&resource, assumptions));
                }
                supplied.push(resource.clone());
                evaluated[index] = Some(resource);
            }
            Err(error) => {
                failures[index] = Some(error);
                resource_clause_register_waiters(index, missing, &mut dependencies, &mut waiters);
            }
        }
    }
    // The section's supply exists only to wake a clause the first pass left
    // waiting. When every active clause already evaluated, building it would
    // expand every composite the frame holds for authority nothing reads.
    let any_clause_waits =
        (0..resources.len()).any(|index| active[index] && evaluated[index].is_none());
    let mut section_supply = if any_clause_waits {
        resource_clause_section_supply(state, &supplied, definitions, assumptions)
    } else {
        ResourceContext::new_with_equalities(assumptions)
    };
    let mut pending = VecDeque::new();
    let mut queued = vec![false; resources.len()];
    for index in 0..resources.len() {
        if any_clause_waits
            && evaluated[index].is_none()
            && dependencies[index]
                .iter()
                .any(|dependency| section_supply.satisfies_fact(dependency, assumptions))
        {
            queued[index] = true;
            pending.push_back(index);
        }
    }
    while let Some(index) = pending.pop_front() {
        queued[index] = false;
        if evaluated[index].is_some() {
            continue;
        }
        resource_clause_unregister_waiters(index, &mut dependencies, &mut waiters);
        let evaluation_state = state.clone().with_resource_context(section_supply.clone());
        let (outcome, missing) = evaluate_resource_clause_with_dependencies(
            entry_state,
            &evaluation_state,
            &resources[index],
            &selected_load_values,
            assumptions,
            budget,
        )?;
        match outcome {
            Ok(resource) => {
                let (next_supply, newly_supplied) = resource_clause_supply_with_fact(
                    section_supply,
                    resource.clone(),
                    definitions,
                    state,
                    assumptions,
                );
                section_supply = next_supply;
                supplied.push(resource.clone());
                evaluated[index] = Some(resource);
                failures[index] = None;
                for fact in newly_supplied {
                    resource_clause_enqueue_waiters(
                        &fact,
                        assumptions,
                        &section_supply,
                        &evaluated,
                        &mut queued,
                        &mut pending,
                        &dependencies,
                        &waiters,
                    );
                }
            }
            Err(error) => {
                failures[index] = Some(error);
                resource_clause_register_waiters(index, missing, &mut dependencies, &mut waiters);
            }
        }
    }
    // A clause refused for its own shape is reported at its own position: no
    // other clause's authority was ever going to repair it, so naming a pair
    // would send the user to a clause that is fine.
    let unresolved = evaluated
        .iter()
        .enumerate()
        .filter_map(|(index, resource)| (active[index] && resource.is_none()).then_some(index))
        .collect::<Vec<_>>();
    let refused = unresolved
        .iter()
        .copied()
        .filter(|index| {
            let error = failures[*index].as_ref();
            let awaits = !dependencies[*index].is_empty()
                || error.is_some_and(resource_clause_failure_awaits_supply);
            !awaits
        })
        .min_by_key(|index| resource_clause_position(resources, *index));
    if require_complete
        && let Some(index) = refused.or_else(|| {
            unresolved
                .iter()
                .copied()
                .min_by_key(|index| resource_clause_position(resources, *index))
        })
    {
        let error = failures[index]
            .take()
            .unwrap_or_else(|| RuntimeError::FunctionContract("unevaluated".to_string()));
        let cycle = refused
            .is_none()
            .then(|| {
                let source_index = resource_clause_position(resources, index).0;
                unresolved
                    .iter()
                    .copied()
                    .filter(|other| {
                        *other != index
                            && resource_clause_position(resources, *other).0 != source_index
                    })
                    .min_by_key(|other| resource_clause_position(resources, *other))
                    .map(|other| (index, other))
            })
            .flatten();
        return Ok(Err(match cycle {
            Some((index, other)) => {
                resource_clause_cycle_runtime_error(error, index, other, resources)
            }
            None => resource_clause_runtime_error(error, index, resources),
        }));
    }
    Ok(Ok(evaluated
        .into_iter()
        .enumerate()
        .filter_map(|(index, fact)| {
            fact.map(|fact| CheckedResourceFact {
                fact,
                role: resources[index].role(),
                state_source: resources[index].state_source(),
                clause_position: resources[index].clause_position(),
                section_index: Some(index),
                selected_mutex_source: None,
            })
        })
        .collect()))
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ResourceClauseDependencyKey {
    Fact(ResourceFact),
    MemoryBase(Address),
    MemoryBlock(AddressBase),
}

/// A sparse segment-tree coordinate space for a concrete memory block.
///
/// The range bounds are normalized to the block's physical byte coordinate,
/// using the pointer base's proven constant byte offset and checked element
/// widths.  Keeping the base out of the key is what lets a clause based at
/// `p + 2` wake a clause based at `p`, while refusing to compare symbolic
/// pointer offsets.  A non-concrete base or bound uses the bounded block/base
/// fallback below instead.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalSpace {
    block: AddressBase,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalNode {
    space: ResourceClauseIntervalSpace,
    /// `level` is the base-2 logarithm of the node's byte span.  The root
    /// is level 32 and the leaves are level 0; no node represents individual
    /// cells outside this fixed-depth index.
    level: u8,
    start: u32,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalWaiter {
    clause: usize,
    dependency: usize,
}

#[derive(Default)]
struct ResourceClauseIntervalIndex {
    exact: BTreeMap<ResourceClauseIntervalNode, BTreeSet<ResourceClauseIntervalWaiter>>,
    /// Subtree aggregates are used only when a query fully covers a node.
    /// Partial queries follow their two boundary paths, so a tiny supplied
    /// range never reads the root aggregate and never wakes every waiter in a
    /// block.  Each update touches at most 33 ancestors per canonical range
    /// node, independent of the number of memory cells in that range.
    subtree: BTreeMap<ResourceClauseIntervalNode, BTreeSet<ResourceClauseIntervalWaiter>>,
}

#[derive(Default)]
struct ResourceClauseWaiterIndex {
    coarse: BTreeMap<ResourceClauseDependencyKey, BTreeSet<usize>>,
    /// Concrete waiters also have a block-local fallback entry.  It is used
    /// only when the *supplied* memory fact cannot be normalized to a
    /// concrete interval: a symbolic event has no interval key to query, but
    /// its explicit block is still a sound conservative candidate boundary.
    /// Store the dependency index as well as the clause so register/remove
    /// stay symmetric when one clause waits on multiple ranges in a block.
    concrete_block_fallback: BTreeMap<AddressBase, BTreeSet<ResourceClauseIntervalWaiter>>,
    intervals: ResourceClauseIntervalIndex,
}

/// Returns a concrete, block-relative byte interval when the base and both
/// bounds have a checked signed integer interpretation.  The interval index
/// is deliberately conservative: ranges that cannot be normalized into the
/// fixed 32-bit coordinate universe remain on the symbolic block/base path.
fn resource_clause_concrete_memory_interval(
    range: &MemoryRange,
) -> Option<(ResourceClauseIntervalSpace, i64, i64)> {
    let (start, end) = crate::kernel::primitives::concrete_memory_range_bounds(range)?;
    if start >= end {
        return None;
    }
    Some((
        ResourceClauseIntervalSpace {
            block: range.base().base.clone(),
        },
        start,
        end,
    ))
}

fn resource_clause_biased_coordinate(value: i64) -> Option<u64> {
    (i64::from(i32::MIN)..=i64::from(i32::MAX))
        .contains(&value)
        .then_some((value - i64::from(i32::MIN)) as u64)
}

fn resource_clause_interval_node_start(coordinate: u64, level: u8) -> u32 {
    if level >= 32 {
        0
    } else {
        ((coordinate >> level) << level) as u32
    }
}

fn resource_clause_interval_node(
    space: &ResourceClauseIntervalSpace,
    level: u8,
    start: u32,
) -> ResourceClauseIntervalNode {
    ResourceClauseIntervalNode {
        space: space.clone(),
        level,
        start,
    }
}

mod resource_clause_worklist;
use resource_clause_worklist::*;

#[cfg(test)]
mod resource_clause_worklist_tests;

fn evaluate_resource_clause_with_dependencies(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    resource: &ResourceSpec,
    selected_load_values: &BTreeMap<(Address, ProgramType), ProgramValue>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(Result<ResourceFact, RuntimeError>, Vec<ResourceFact>)> {
    #[cfg(test)]
    record_resource_clause_attempt();
    let (result, dependencies) = capture_resource_dependencies(|| {
        evaluate_function_resource_spec_with_entry_and_selected_loads(
            entry_state,
            state,
            resource,
            selected_load_values,
            assumptions,
            budget,
        )
    });
    result.map(|result| (result, dependencies))
}

fn resource_clause_read_supply(fact: &ResourceFact, assumptions: &PureFactContext) -> ResourceFact {
    match fact.resource() {
        Resource::Memory(range)
            if fact.is_own() && fact.has_proven_positive_quantity(assumptions) =>
        {
            ResourceFact::view_memory(range.clone())
        }
        _ => fact.clone(),
    }
}

/// The read authority a section's already-evaluated clauses supply to the
/// clauses that still need one.
///
/// Expansion adds views, never ownership: a folded composite's cells become
/// readable so a later clause's base load denotes, while every owned resource
/// stays exactly where the clause set put it. This state is a scratch
/// evaluation frame and is never the section's result.

pub(in crate::kernel) fn resource_clause_section_supply(
    state: &ExecutionState,
    supplied: &[ResourceFact],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> ResourceContext {
    let mut base = state.resources().clone();
    base.capture_empty_memory_input(assumptions);
    for fact in supplied {
        if !matches!(fact.resource(), Resource::Instance(_))
            || !base.contains_exact_representation(fact)
        {
            base = base.unchecked_with_fact(resource_clause_read_supply(fact, assumptions));
        }
    }
    if definitions.is_empty() {
        return base;
    }
    // A matched instance supplies the cells of the arm this section's
    // premises select, and nothing when they select none (D7). The arm stays
    // folded either way: only its read authority is published here.
    let mut views = supplied
        .iter()
        .filter_map(|fact| match fact.resource() {
            Resource::Instance(instance) => Some(instance),
            _ => None,
        })
        .flat_map(|instance| instance_arm_read_authority(instance, definitions, state, assumptions))
        .collect::<Vec<_>>();
    // A control may contain an authority that generic composite expansion
    // cannot expose without a live population ledger. Its declared memory is
    // still readable through the folded clause, independently of that ledger.
    // Publish only views of those cells, never the authority or body ownership.
    for fact in supplied {
        views.extend(resource_clause_composite_memory_views(
            fact,
            definitions,
            state,
            assumptions,
        ));
    }
    // A field-bearing instance one of this section's own clauses supplied
    // publishes the cells its unconditional, unmatched body owns, the way a
    // field-free composite and a decided arm do. Only the section's own
    // clauses are visited, never the frame they are evaluated against.
    for fact in supplied {
        views.extend(unmatched_instance_body_views(
            fact,
            definitions,
            state,
            assumptions,
        ));
    }
    let Some(expanded) = expand_all_composite_resource_facts(
        &base,
        definitions,
        &state.program_point(),
        assumptions,
    ) else {
        return base.unchecked_with_facts(views);
    };
    views.extend(
        expanded
            .changed_facts_since(&base)
            .expect("composite expansion retains persistent resource ancestry")
            .into_iter()
            .filter(|fact| expanded.contains_exact_representation(fact))
            .filter_map(|fact| match fact.resource() {
                Resource::Memory(range) => Some(ResourceFact::view_memory(range.clone())),
                _ => None,
            }),
    );
    base.unchecked_with_facts(views)
}

/// What one frontier's premises decide about the folded matched instances a
/// context holds: the single publication point of decision D7.
///
/// `model_facts` are the negative `model != Variant` conclusions of every
/// refuted field-free arm, plus the positive `model == Variant` when
/// refutation leaves exactly one field-free arm. `views` are the cells the
/// decided arm owns, or the cells every surviving arm agrees on. `arm_facts`
/// are the decided arm's own facts that name no constructor binding.
#[derive(Clone, Debug, Default)]
pub(crate) struct ArmPublication {
    pub model_facts: Vec<Proposition>,
    pub views: Vec<ResourceFact>,
    pub arm_facts: Vec<Proposition>,
}

/// Decides the arms of every folded matched instance `context` holds, from the
/// premises in `assumptions` plus the arms' own binding-free facts.
///
/// This is decision D7, and it is decided in exactly one place. Every frontier
/// a proof passes through — contract entry lowering, contract return, a loop
/// head, a loop back edge, a loop exit, a guard conjunct, an `unfold`, a
/// frontier case split — calls this with its own premises and consumes the
/// same publication, so a refutation that fires at one of them fires at all of
/// them. `docs/concepts/resources.md` lists the sites; wiring a mechanism to
/// one site alone is what this function exists to prevent.
///
/// The order inside is the decision's own: refutation first, because a refuted
/// arm is evidence the selection reads, then read authority and the arm's own
/// facts under the premises refutation just established. That is why a guard
/// conjunct that rules out an ascending frame's `Top` arm can read the cell
/// its two surviving arms agree on.
///
/// Bounded exactly as its parts are: one pass over the instances this context
/// holds, and per instance one evaluation of its own body and one of each of
/// its own arms. Nothing project-wide or path-wide is scanned.
pub(crate) fn publish_instance_arms(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> ArmPublication {
    if definitions.is_empty() {
        return ArmPublication::default();
    }
    let instances = context
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            Resource::Instance(instance) => Some(instance),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut published = ArmPublication::default();
    for instance in &instances {
        published.model_facts.extend(instance_arm_model_facts(
            instance,
            definitions,
            state,
            assumptions,
        ));
    }
    let decided = published
        .model_facts
        .iter()
        .cloned()
        .fold(assumptions.clone(), PureFactContext::assume_proposition);
    for instance in &instances {
        published.views.extend(instance_arm_read_authority(
            instance,
            definitions,
            state,
            &decided,
        ));
        published.arm_facts.extend(decided_instance_arm_facts(
            instance,
            definitions,
            state,
            &decided,
        ));
    }
    published
}

/// The read-authority half of [`publish_instance_arms`], for the point inside
/// a frontier where a section's own clauses are being evaluated one at a time.
///
/// A frontier's publication is taken once, on the finished state, and it is
/// what decides models there. While a section is still being evaluated its
/// clauses need only to be addressable, so this publishes the cells the
/// premises already decide and re-decides nothing: refuting every arm of every
/// held instance again per clause would cost the arms of the section rather
/// than the arms of the frontier.
fn instance_arm_views(
    context: &ResourceContext,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<ResourceFact> {
    if definitions.is_empty() {
        return Vec::new();
    }
    context
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            Resource::Instance(instance) => Some(instance),
            _ => None,
        })
        .flat_map(|instance| instance_arm_read_authority(instance, definitions, state, assumptions))
        .collect()
}

/// The cells owned by the match arm this frontier's premises select for
/// `instance`, or by every arm they leave possible, as views.
///
/// This is the read-authority half of decision D7. The decision is
/// [`decide_resource_model_arm`]; what it decides is published as read
/// authority only, so a contract clause or requirement may read a cell a
/// folded matched instance owns exactly as it may read one a folded
/// `if`-bodied composite owns. Ownership is untouched: only an explicit
/// `unfold` moves the arm's cells into the proof state.
///
/// When the premises select no single arm they may still have refuted some,
/// and the arms they leave possible can agree about a cell. `parent != 0`
/// refutes an ascending frame's `Top` arm, and the `Left` and `Right` arms
/// both own `parent->rb_right`, so that cell is readable however the model
/// turns out. What is published is then the intersection of the possible arms'
/// own memory clauses: a cell one possible arm does not own is never
/// published, and an arm whose clauses cannot be evaluated here makes the
/// intersection empty rather than being skipped.
///
/// Cost is the selected arm's own clauses, or one evaluation of each possible
/// arm's clauses. An instance whose model carries no variant evidence at all,
/// or whose arms name a constructor binding in a memory clause, publishes
/// nothing.
pub(super) fn instance_arm_read_authority(
    instance: &ResourceInstance,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<ResourceFact> {
    let Ok(index) = definitions.binary_search_by(|definition| {
        crate::instrumentation::record_deterministic_work(1);
        definition.name().cmp(instance.name())
    }) else {
        return Vec::new();
    };
    let definition = &definitions[index];
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    let Some(crate::kernel::ResourceFieldValue::Algebraic(model)) =
        instance.fields().get(body.field_index)
    else {
        return Vec::new();
    };
    let variants = match decide_resource_model_arm(model, assumptions) {
        ResourceModelArmDecision::Selected(selection) => vec![selection.variant().to_owned()],
        ResourceModelArmDecision::Possible(variants) => variants,
        ResourceModelArmDecision::Open => Vec::new(),
    };
    if variants.is_empty() {
        return Vec::new();
    }
    let Ok(evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    let mut common: Option<Vec<ResourceFact>> = None;
    for variant in &variants {
        let Some(arm) = body.arms.iter().find(|arm| &arm.variant == variant) else {
            return Vec::new();
        };
        let Some(views) =
            resource_clause_memory_views(&evaluation, &arm.contains, definitions, assumptions)
        else {
            return Vec::new();
        };
        common = Some(match common {
            // Order follows the first arm's clauses, so one possible arm and a
            // selected arm publish the same list in the same order.
            Some(common) => common
                .into_iter()
                .filter(|fact| views.contains(fact))
                .collect(),
            None => views,
        });
        if common.as_ref().is_some_and(Vec::is_empty) {
            return Vec::new();
        }
    }
    common.unwrap_or_default()
}

/// The cells an unconditional, unmatched instance body owns, as views: the
/// read authority a folded field-bearing instance supplies to the sibling
/// clauses of the section that holds it.
///
/// This is the same publication a field-free composite's expansion and a
/// decided match arm make. The body is evaluated at the instance's own
/// fields and arguments, so `owns *region` in the arena example's
/// `arena_region` makes `region->arena` readable for a clause that names
/// `arena_state(region->arena)`. Nothing is owned twice and nothing is
/// opened: the instance stays folded, and only an explicit `unfold` moves its
/// cells into the proof state. A view grants a read, never a write.
///
/// A matched body publishes through [`instance_arm_read_authority`] instead,
/// a guarded body publishes nothing (its case is a proof obligation, not a
/// premise), and a body with existential witnesses publishes nothing because
/// a witness has no value until the body is opened.
///
/// Cost is one definition lookup by name and one evaluation of this one
/// instance's own memory clauses, with no composite definitions in scope, so
/// a body never re-enters this publication and nothing outside the instance
/// is visited.
pub(crate) fn unmatched_instance_body_views(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<ResourceFact> {
    let Resource::Instance(instance) = fact.resource() else {
        return Vec::new();
    };
    let Ok(index) =
        definitions.binary_search_by(|definition| definition.name().cmp(instance.name()))
    else {
        return Vec::new();
    };
    let definition = &definitions[index];
    if definition.matched.is_some()
        || definition.condition.is_some()
        || !definition.witnesses.is_empty()
        || definition.contains.is_empty()
    {
        return Vec::new();
    }
    let Ok(evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    resource_clause_memory_views(&evaluation, &definition.contains, definitions, assumptions)
        .unwrap_or_default()
}

/// The cells a body's own memory clauses own at `evaluation`, as views, or
/// `None` when those clauses cannot be evaluated there. Shared by a match
/// arm's clauses and an unmatched instance body's.
///
/// A field-free composite the body owns, such as `arena_cells(...)` inside
/// `arena_state`, owns its cells through the body as surely as a memory
/// clause does, so its expansion publishes them too. The expansion is the
/// body's own children and nothing else, so the work stays linear in the
/// body.
fn resource_clause_memory_views(
    evaluation: &ExecutionState,
    contains: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Option<Vec<ResourceFact>> {
    crate::instrumentation::record_deterministic_work(1);
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        // These are the established clauses of the held instance.
        .assume_entry_clause_spans()
        .assume_held_resource_domains();
    let mut budget = ExecutionBudget::beside_live_state();
    let Ok(Ok(body_resources)) = evaluate_function_resource_context_with_normalization(
        evaluation,
        contains,
        &[],
        &evaluation_assumptions,
        &mut budget,
        false,
    ) else {
        return None;
    };
    let body_resources = body_resources.0;
    let expanded = if body_resources
        .facts()
        .iter()
        .any(|fact| matches!(fact.resource(), Resource::Composite { .. }))
    {
        expand_all_composite_resource_facts(
            &body_resources,
            definitions,
            &evaluation.program_point(),
            &evaluation_assumptions,
        )
    } else {
        None
    };
    Some(
        expanded
            .as_ref()
            .unwrap_or(&body_resources)
            .facts()
            .iter()
            .filter_map(|fact| match fact.resource() {
                Resource::Memory(range) => Some(ResourceFact::view_memory(range.clone())),
                _ => None,
            })
            .collect(),
    )
}

/// The negation of one already-lowered body fact, in the shape the exact
/// checkers decide.
///
/// A resource body fact lowers to a bare condition in every case this rule
/// acts on, and a bare condition's negation is the same condition at the
/// other truth value; nothing else is turned inside out here.
fn refutation_of_body_fact(proposition: &Proposition) -> Option<Proposition> {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Some(Proposition::condition_is(condition.clone(), !value))
        }
        _ => None,
    }
}

/// The model facts a context's premises force on the folded matched instances
/// it holds by refuting arms: decision D7 applied to refutation.
///
/// An owned folded instance's body holds wherever the instance is held, so a
/// premise that refutes an arm's own binding-free fact refutes the arm.
/// `root->left != 0` against `tree_at`'s `HeapTree::Empty` arm `fact p == 0`
/// says the child instance's model is not `HeapTree::Empty`; `root->left == 0`
/// against the `Node` arm's `fact p != 0` says it is not a `Node`.
///
/// Two conclusions are published, both as ordinary propositions:
///
/// - `model != Variant` for each refuted arm whose constructor is field-free.
///   That is exactly the `Excluded` evidence [`select_resource_model_arm`]
///   reads, so on a two-constructor model the surviving arm is then selected.
///   An arm with fields has no negative to state, for the same reason
///   `model != Some(3)` leaves `Some` possible.
/// - `model == Variant` when refutation leaves exactly one arm and that arm's
///   constructor is field-free, because then the model has only one value
///   left. This is what gives `unfold` and proof `match` a constructor after
///   a guard has excluded every other arm.
///
/// Only a fact that names no binding of its own arm takes part: a binding is
/// an unknown of the arm, so a fact about one says nothing until the arm is
/// selected. The arm's own `owns` clauses are evaluated first, exactly as arm
/// selection evaluates the selected arm's cells, so a binding-free fact that
/// reads a cell the arm owns has the authority to read it.
///
/// This is a decision, never a search: each held instance's arms are visited
/// once, each arm's own clauses are evaluated once, and the refutation is the
/// exact-fact check. A constructor carried by the model or selected by an
/// exact equality needs no further refutation and is skipped. Nothing outside the instances held and their own arms is visited.
///
/// It also states the object classes every arm gives the instance's pointer
/// arguments ([`instance_argument_class_facts`]); those hold whatever the
/// premises decide.
///
/// [`publish_instance_arms`] calls this for every instance a frontier's
/// context holds; the two frontiers that are about one instance — the `unfold`
/// that opens it and the case split that eliminates its constructor — call it
/// directly for that instance alone.
pub(in crate::kernel) fn instance_arm_model_facts(
    instance: &ResourceInstance,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let mut facts = instance_argument_class_facts(instance, definitions);
    facts.extend(instance_arm_refutation_facts(
        instance,
        definitions,
        state,
        assumptions,
    ));
    facts
}

/// The refutation half of [`instance_arm_model_facts`]: what the premises
/// decide about the instance's model.
fn instance_arm_refutation_facts(
    instance: &ResourceInstance,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let _timing = crate::instrumentation::OperationTiming::new(
        instance.name(),
        "resource rewrite",
        "instance arm refutations",
    );
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == instance.name())
    else {
        return Vec::new();
    };
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    let Some(crate::kernel::ResourceFieldValue::Algebraic(model)) =
        instance.fields().get(body.field_index)
    else {
        return Vec::new();
    };
    // A model that already carries a constructor needs no exclusion, and only
    // a symbolic value has variant evidence at all.
    crate::instrumentation::record_deterministic_work(1);
    if !matches!(model.node, AlgebraicTermNode::Variable(_))
        || assumptions.known_algebraic_constructor(model).is_some()
    {
        // Exact constructor evidence already decides the arm; refutation
        // would only rediscover exclusions it implies.
        return Vec::new();
    }
    // The positive conclusion needs the arms to be the declared variants
    // exactly once each; the negative one does not, but one gate keeps the
    // two readings of "every other arm" the same.
    let variants = model
        .algebraic_type
        .variants
        .iter()
        .map(|variant| variant.name.as_str())
        .collect::<BTreeSet<_>>();
    if variants.len() != body.arms.len()
        || body
            .arms
            .iter()
            .any(|arm| !variants.contains(arm.variant.as_str()))
    {
        return Vec::new();
    }
    let constructor = |arm: &ResourceMatchArm| {
        let term = AlgebraicTerm {
            algebraic_type: model.algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: arm.variant.clone(),
                fields: Vec::new(),
            },
        };
        (arm.bindings.is_empty() && term.is_well_formed()).then_some(term)
    };
    // The body is evaluated, and arms are refuted, only for an answer this
    // call can still publish.
    let evaluated = std::cell::OnceCell::new();
    let refuted = |arm: &ResourceMatchArm| -> Option<bool> {
        let (evaluation, evaluation_assumptions) = evaluated
            .get_or_init(|| {
                instance_body_evaluation(state, instance, definition)
                    .ok()
                    .map(|evaluation| {
                        let evaluation_assumptions = assumptions
                            .clone()
                            .allow_symbolic_contract_loads()
                            .prefer_symbolic_external_loads();
                        (evaluation, evaluation_assumptions)
                    })
            })
            .as_ref()?;
        Some(arm_is_refuted_by_a_binding_free_fact(
            evaluation,
            arm,
            evaluation_assumptions,
            assumptions,
        ))
    };
    // Only an arm naming a constructor without fields publishes anything: its
    // exclusion, or, when it alone survives, the model's constructor. An arm
    // whose exclusion is already a fact is refuted; nothing is learned by
    // refuting it again.
    let mut published = Vec::new();
    let mut surviving = Vec::new();
    let mut unpublishable = Vec::new();
    for arm in &body.arms {
        crate::instrumentation::record_deterministic_work(1);
        let Some(excluded) = constructor(arm) else {
            unpublishable.push(arm);
            continue;
        };
        let negation = Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(excluded.clone()),
        )));
        if required_obligation_is_exactly_discharged(assumptions, &negation) {
            continue;
        }
        match refuted(arm) {
            None => return Vec::new(),
            Some(true) => published.push(negation),
            Some(false) => surviving.push(excluded),
        }
    }
    // The other arms decide only whether a sole surviving constructor is the
    // model's: each must be refuted for that.
    if let [selected] = surviving.as_slice() {
        for arm in unpublishable {
            match refuted(arm) {
                None => return Vec::new(),
                Some(true) => {}
                Some(false) => return published,
            }
        }
        published.push(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(selected.clone()),
        ));
    }
    published
}

/// Whether `assumptions` refutes one of `arm`'s own facts that names no
/// binding of the arm.
///
/// A fact naming a binding says nothing before the arm is selected: the
/// binding is an unknown the constructor would supply. A budget or evaluation
/// failure is not a refutation: the arm simply publishes nothing.
fn arm_is_refuted_by_a_binding_free_fact(
    evaluation: &ExecutionState,
    arm: &ResourceMatchArm,
    evaluation_assumptions: &PureFactContext,
    assumptions: &PureFactContext,
) -> bool {
    arm_binding_free_facts(evaluation, arm, evaluation_assumptions).any(|fact| {
        refutation_of_body_fact(&fact).is_some_and(|negation| {
            required_obligation_is_exactly_discharged(assumptions, &negation)
        })
    })
}

/// One arm's own facts that name no binding of the arm, lowered against the
/// instance's body in `evaluation`.
///
/// Facts are restricted to the comparison shape for the same reason arm
/// selection restricts its guards: a comparison of C expressions is what a
/// path condition decides. Direct value comparisons need no owned memory.
/// Other facts first evaluate the arm's `owns` clauses, exactly as arm
/// selection does, so a fact reading an arm-owned cell has its authority.
/// A fact that needs a conditional proof, or that the budget cannot lower, contributes nothing.
/// Lower facts on demand so a refuting guard stops before unused memory facts.
///
/// Cost is this arm's own clauses. Nothing outside the arm is visited.
fn arm_binding_free_facts<'a>(
    evaluation: &'a ExecutionState,
    arm: &'a ResourceMatchArm,
    evaluation_assumptions: &'a PureFactContext,
) -> impl Iterator<Item = Proposition> + 'a {
    let bound = arm.bindings.iter().cloned().collect::<BTreeSet<_>>();
    let binding_free = arm
        .facts
        .iter()
        .filter(|fact| !spec_proposition_mentions_any_name(fact, &bound))
        .collect::<Vec<_>>();
    let mut budget = ExecutionBudget::beside_live_state();
    let prepared = std::cell::OnceCell::new();
    binding_free.into_iter().filter_map(move |fact| {
        crate::instrumentation::record_deterministic_work(1);
        let lower = |state: &ExecutionState,
                     assumptions: &PureFactContext,
                     budget: &mut ExecutionBudget| {
            let paths =
                crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
                    state,
                    fact,
                    None,
                    assumptions,
                    &BTreeMap::new(),
                    budget,
                )
                .ok()?;
            let [path] = paths.as_slice() else {
                return None;
            };
            (path.facts.is_empty() && path.obligations.is_empty()).then(|| path.proposition.clone())
        };
        // Direct scalar comparisons need no owned cells. In particular,
        // checking a null guard must not evaluate every memory clause.
        let direct = match fact {
            SpecProposition::Comparison { left, right, .. } => {
                [left, right].into_iter().all(|side| {
                    matches!(
                        side,
                        SpecExpression::Value(_)
                            | SpecExpression::ProgramExpression(
                                ProgramExpression::Value(_) | ProgramExpression::Variable(_)
                            )
                    )
                })
            }
            _ => false,
        };
        if direct && let Some(proposition) = lower(evaluation, evaluation_assumptions, &mut budget)
        {
            return Some(proposition);
        }
        let (body_state, body_assumptions) = prepared
            .get_or_init(|| {
                let body_resources = evaluate_function_resource_context_with_normalization(
                    evaluation,
                    &arm.contains,
                    &[],
                    evaluation_assumptions,
                    &mut budget,
                    false,
                )
                .ok()?
                .ok()?;
                let body_state = evaluation.clone().with_resource_context(body_resources.0);
                let body_assumptions = evaluation_assumptions.clone().assume_proposition(
                    Proposition::ResourceComposition(body_state.resources().clone()),
                );
                Some((body_state, body_assumptions))
            })
            .as_ref()?;
        lower(body_state, body_assumptions, &mut budget)
    })
}

/// The object classes holding `instance` establishes for its pointer
/// arguments, whichever arm it is in.
///
/// A parameter that every arm of the matched body states equal to a typed
/// constructor binding of one class, or to null, has that class or is null:
/// a typed model field holds a pointer of its declared class or null, and the
/// fold that built the instance proved the arm's facts. So `rb_at(p)`, whose
/// `Empty` arm says `p == 0` and whose `Node` arm says `p == identity`, types
/// `p` as `struct rb_node` without opening it. The analysis reads only the
/// definition's own arm facts.
fn instance_argument_class_facts(
    instance: &ResourceInstance,
    definitions: &[CompositeResourceDefinition],
) -> Vec<Proposition> {
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == instance.name())
    else {
        return Vec::new();
    };
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    matched_argument_classes(definition, body)
        .into_iter()
        .filter_map(|(index, class)| match instance.arguments().get(index) {
            Some(crate::kernel::ResourceFieldValue::Program(value @ ProgramValue::Pointer(_))) => {
                // The receipt's value carries the class, as a checked call's
                // does: that annotation is what the graph indexes.
                let typed = value.clone().with_pointer_object_class(Some(class.clone()));
                Some(crate::kernel::object_types::checked_call_type_fact(
                    &typed, &class,
                ))
            }
            _ => None,
        })
        .collect()
}

/// The pointer parameters of `definition` that every arm of `body` ties to a
/// typed constructor binding of one class or to null, with that class.
fn matched_argument_classes(
    definition: &CompositeResourceDefinition,
    body: &ResourceMatchBody,
) -> Vec<(usize, crate::kernel::effective_type::CAccessClass)> {
    fn variable(expression: &SpecExpression) -> Option<&str> {
        match expression {
            SpecExpression::ProgramExpression(ProgramExpression::Variable(name)) => name.named(),
            _ => None,
        }
    }
    let is_null = |expression: &SpecExpression| match expression {
        SpecExpression::Value(value) => crate::kernel::spec::program_value_bitvector_term(value)
            .is_some_and(|term| term.as_const() == Some(0)),
        _ => false,
    };
    definition
        .parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| {
            let mut class = None;
            for arm in &body.arms {
                crate::instrumentation::record_deterministic_work(1);
                // `Some(None)`: the arm makes the parameter null.
                let mut arm_class = None;
                for fact in &arm.facts {
                    let SpecProposition::Comparison {
                        left,
                        operator: ComparisonOperator::Equal,
                        right,
                    } = fact
                    else {
                        continue;
                    };
                    for (own, other) in [(left, right), (right, left)] {
                        if variable(own) != Some(parameter.name()) {
                            continue;
                        }
                        if is_null(other) {
                            arm_class.get_or_insert(None);
                        } else if let Some(binding) = variable(other)
                            && let Some(position) =
                                arm.bindings.iter().position(|name| name == binding)
                            && let Some(AlgebraicValueType::ObjectPointer(_, typed)) =
                                arm.binding_types.get(position)
                        {
                            arm_class = Some(Some(typed.clone()));
                        }
                    }
                }
                match arm_class? {
                    None => {}
                    Some(typed) => match &class {
                        None => class = Some(typed),
                        Some(previous) if *previous == typed => {}
                        Some(_) => return None,
                    },
                }
            }
            class.map(|class| (index, class))
        })
        .collect()
}

/// The facts of the arm a frontier's premises decide for one folded matched
/// instance, restricted to the facts that name no constructor binding.
///
/// This is the last part of decision D7: the read authority says which cells
/// the arm owns, and this says what the arm states about them. `consumes t:
/// tree_at(root); requires t.model != HeapTree::Empty;` selects the `Node`
/// arm, whose `fact p != 0` is then an entry premise, so a walk that starts
/// with `if (root == 0)` decides the guard instead of needing an infeasible
/// `branch`.
///
/// A fact naming a binding stays unpublished: the binding is an unknown of the
/// arm, and only an `unfold` or a proof `match` names it. Cost is the decided
/// arm's own clauses.
fn decided_instance_arm_facts(
    instance: &ResourceInstance,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == instance.name())
    else {
        return Vec::new();
    };
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    let Some(crate::kernel::ResourceFieldValue::Algebraic(model)) =
        instance.fields().get(body.field_index)
    else {
        return Vec::new();
    };
    let Some(selection) = select_resource_model_arm(model, assumptions) else {
        return Vec::new();
    };
    let Some(arm) = body
        .arms
        .iter()
        .find(|arm| arm.variant == selection.variant())
    else {
        return Vec::new();
    };
    let Ok(evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    arm_binding_free_facts(&evaluation, arm, &evaluation_assumptions).collect()
}

/// Whether a resource body fact is a comparison of C expressions in which one
/// of `names` occurs. A fact of any other shape answers `true`, so the
/// refutation rule leaves it alone.
fn spec_proposition_mentions_any_name(fact: &SpecProposition, names: &BTreeSet<String>) -> bool {
    let SpecProposition::Comparison { left, right, .. } = fact else {
        return true;
    };
    [left, right].into_iter().any(|side| match side {
        SpecExpression::Value(_) => false,
        SpecExpression::ProgramExpression(expression) => names
            .iter()
            .any(|name| program_expression_mentions_variable(expression, &name.into())),
        _ => true,
    })
}

// Read-only cells declared by one positive folded composite. Both the
// initial supply and a newly resolved dependent clause publish the same
// projections, even when generic ownership expansion cannot open its head.
fn resource_clause_composite_memory_views(
    fact: &ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Vec<ResourceFact> {
    if !fact.is_view() && !fact.has_proven_positive_quantity(assumptions) {
        return Vec::new();
    }
    let Resource::Composite { name, .. } = fact.resource() else {
        return Vec::new();
    };
    let Ok(index) = definitions.binary_search_by(|definition| {
        crate::instrumentation::record_deterministic_work(1);
        definition.name().cmp(name)
    }) else {
        return Vec::new();
    };
    evaluate_composite_resource_memory_ranges(
        fact,
        &definitions[index..=index],
        &state.program_point(),
        assumptions,
    )
    .unwrap_or_default()
    .into_iter()
    .map(ResourceFact::view_memory)
    .collect()
}

/// Incrementally exposes the memory cells beneath one newly evaluated
/// composite clause.  The outer section supply already expanded all facts
/// from the previous pass; walking only this fact and its nested children
/// keeps a dependency chain proportional to its own nodes and edges instead
/// of rescanning the complete section after every successful retry.
fn resource_clause_supply_with_fact(
    mut supply: ResourceContext,
    fact: ResourceFact,
    definitions: &[CompositeResourceDefinition],
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> (ResourceContext, Vec<ResourceFact>) {
    let memory = state.memory();
    let mut added = Vec::new();
    if !supply.facts().contains(&fact) {
        supply = supply.unchecked_with_fact(fact.clone());
        added.push(fact.clone());
    }
    if definitions.is_empty() {
        return (supply, added);
    }
    if matches!(fact.resource(), Resource::Instance(_)) {
        // A newly evaluated field-bearing instance publishes its unmatched
        // body's cells exactly as the section supply does for the instances
        // the first pass evaluated.
        for view in unmatched_instance_body_views(&fact, definitions, state, assumptions) {
            if !supply.facts().contains(&view) {
                supply = supply.unchecked_with_fact(view.clone());
                added.push(view);
            }
        }
        return (supply, added);
    }
    if !matches!(fact.resource(), Resource::Composite { .. }) {
        return (supply, added);
    }
    for view in resource_clause_composite_memory_views(&fact, definitions, state, assumptions) {
        if !supply.facts().contains(&view) {
            supply = supply.unchecked_with_fact(view.clone());
            added.push(view);
        }
    }
    let mut pending = VecDeque::from([fact]);
    let mut seen = BTreeSet::new();
    while let Some(composite) = pending.pop_front() {
        if !seen.insert(composite.clone()) {
            continue;
        }
        let expansion_context = supply.clone().unchecked_with_fact(composite.clone());
        let Some((_, children, _)) = expand_composite_resource_fact_with_children(
            &expansion_context,
            &composite,
            definitions,
            &crate::kernel::ProgramPoint::of_memory(memory),
            assumptions,
        ) else {
            continue;
        };
        for child in children {
            match child.resource() {
                Resource::Footprint(_)
                | Resource::Parameter(_)
                | Resource::Emp
                | Resource::Star(_) => {}
                Resource::Memory(range) => {
                    let view = ResourceFact::view_memory(range.clone());
                    if !supply.facts().contains(&view) {
                        supply = supply.unchecked_with_fact(view.clone());
                        added.push(view);
                    }
                }
                Resource::Composite { .. } => pending.push_back(child),
                // Iterated ownership grants no read authority of its own: an
                // element is read only after it is taken out.
                Resource::Token { .. }
                | Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::Iterated(_) => {}
            }
        }
    }
    (supply, added)
}

/// Names which resource clause of a contract section could not be addressed.
///
/// Two checks reach this conclusion about the same contract: the surface
/// refuses a clause whose segment base reads a cell the contract holds no
/// authority over, and this evaluator refuses a clause whose base it cannot
/// read at all. They are one defect, so they identify the clause with one
/// wording, formatted here and in [`resource_clause_stall_note`].
pub(crate) fn resource_clause_position_note(index: usize, total: usize) -> String {
    format!("resource clause {} of {total}", index + 1)
}

/// Names two clauses that no order addresses. Clause order does not decide a
/// section, so reporting only the first position would send the user to a
/// clause that is fine on its own.
pub(crate) fn resource_clause_stall_note(index: usize, other: usize) -> String {
    format!(
        "resource clauses {} and {} cannot be evaluated in any order: each needs a cell no \
         clause evaluated before it supplies",
        index + 1,
        other + 1
    )
}

/// Names which resource clause of a contract section failed to evaluate. The
/// evaluator walks the declared clauses in order, so the position is the only
/// identification available here, and it is enough for a user to find the
/// clause. Structured errors already print the offending resource and are
/// passed through unchanged.
fn resource_clause_position(resources: &[ResourceSpec], index: usize) -> (usize, usize) {
    resources
        .get(index)
        .and_then(ResourceSpec::clause_position)
        .unwrap_or((index, resources.len()))
}

fn annotate_resource_clause_error(error: RuntimeError, note: String) -> RuntimeError {
    match error {
        RuntimeError::FunctionContract(message) => {
            RuntimeError::FunctionContract(format!("{message} ({note})"))
        }
        RuntimeError::UnsuppliedResourceValue(message) => {
            RuntimeError::UnsuppliedResourceValue(format!("{message} ({note})"))
        }
        RuntimeError::ContractResourceDiagnostic {
            reason,
            held,
            required,
            memory,
        } => RuntimeError::ContractResourceDiagnostic {
            reason: format!("{reason} ({note})"),
            held,
            required,
            memory,
        },
        error => error,
    }
}

fn resource_clause_runtime_error(
    error: RuntimeError,
    index: usize,
    resources: &[ResourceSpec],
) -> RuntimeError {
    let (index, total) = resource_clause_position(resources, index);
    annotate_resource_clause_error(error, resource_clause_position_note(index, total))
}

/// Whether a clause failed for want of a value it had to read, which is the
/// only failure another clause's authority can repair. The evaluator reports
/// a section that stalls on these as a pair; anything else is one clause's own
/// problem.
fn resource_clause_failure_awaits_supply(error: &RuntimeError) -> bool {
    match error {
        RuntimeError::ContractResourceDiagnostic { memory, .. } => memory.is_some(),
        RuntimeError::UnsuppliedResourceValue(_) => true,
        _ => false,
    }
}

/// The refusal for a resource clause value that did not evaluate. Another
/// clause may supply what it read, unless the expression may have undefined
/// behavior the facts do not rule out: no other clause's cells make `i + 1`
/// stop overflowing, so that needs a requirement.
fn unevaluated_resource_value(
    refusal: &super::loops::ValueRefusal,
    message: String,
) -> RuntimeError {
    if refusal.is_undefined_behavior() {
        RuntimeError::FunctionContract(message)
    } else {
        RuntimeError::UnsuppliedResourceValue(message)
    }
}

fn resource_clause_cycle_runtime_error(
    error: RuntimeError,
    index: usize,
    other: usize,
    resources: &[ResourceSpec],
) -> RuntimeError {
    let (index, _) = resource_clause_position(resources, index);
    let (other, _) = resource_clause_position(resources, other);
    annotate_resource_clause_error(error, resource_clause_stall_note(index, other))
}

pub(in crate::kernel) fn resource_context_runtime_error(
    error: ResourceContextValidityError,
) -> RuntimeError {
    match error {
        ResourceContextValidityError::UnsupportedOwnershipBoundary => RuntimeError::FunctionContract(error.to_string()),
        ResourceContextValidityError::UnestablishedOwnedBoundary(required) => {
            RuntimeError::PendingCallObligations(vec![ProofObligation::verification_condition(*required)
                .with_context("symbolic ownership boundary".to_string())].into())
        }
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            RuntimeError::DuplicateResource { resource: Box::new(resource) }
        }
        ResourceContextValidityError::InvalidExclusiveAccess(_) => RuntimeError::FunctionContract(
            "field-bearing resource instances and mutex guards require exclusive ownership with quantity one".into(),
        ),
        ResourceContextValidityError::OverlappingOwnedMemoryResources { left, right } => {
            RuntimeError::OverlappingOwnedMemoryResources {
                left: Box::new(left),
                right: Box::new(right),
            }
        }
    }
}

/// Resolve reference arguments without requiring or granting ownership. The
/// retained field scope may name a resource whose custody has moved elsewhere.
pub(crate) fn evaluate_resource_reference_arguments(
    state: &ExecutionState,
    spec: &ResourceSpec,
) -> Result<Vec<ResourceReference>, RuntimeError> {
    spec.resource_arguments()
        .iter()
        .map(|identity| {
            state
                .resource_instance_fields(*identity)
                .map(ResourceReference::from_instance)
                .ok_or_else(|| {
                    RuntimeError::FunctionContract(
                        "resource argument does not name an available resource reference".into(),
                    )
                })
        })
        .collect()
}

/// Evaluate a resource type without selecting or manufacturing an owned instance.
fn evaluate_resource_type(
    entry: &ExecutionState,
    state: &ExecutionState,
    resource_type: &ResourceTypeSpec,
    allow_token: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceDescription, RuntimeError>> {
    let invalid = || {
        RuntimeError::FunctionContract(if allow_token {
            "population authority requires a declared resource type".into()
        } else {
            "mutex_use requires a field-bearing resource type".into()
        })
    };
    let spec = &resource_type.resource;
    let schema = &resource_type.schema;
    if !spec.resource_arguments().is_empty() {
        return Ok(Err(invalid()));
    }
    let (family, name, arguments, argument_state_sources, parameter_types) = match spec.term() {
        ResourceTerm::Composite {
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        } => (
            ResourceFamily::Composite,
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        ),
        ResourceTerm::Token {
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        } if allow_token && schema.fields().is_empty() => (
            ResourceFamily::Token,
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        ),
        _ => return Ok(Err(invalid())),
    };
    let fact = match evaluate_function_declared_resource_spec(
        entry,
        state,
        ResourceAccessMode::Own,
        family,
        name,
        arguments,
        argument_state_sources,
        parameter_types,
        spec.source_arguments(),
        &BTreeMap::new(),
        assumptions,
        budget,
    )? {
        Ok(fact) => fact,
        Err(error) => return Ok(Err(error)),
    };
    let (name, arguments) = match fact.resource() {
        Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
            (name, arguments)
        }
        _ => return Ok(Err(invalid())),
    };
    Ok(Ok(ResourceDescription::new(
        name.clone(),
        arguments.clone(),
        schema.clone(),
    )))
}

/// Describes an authority clause for a checked proof rewrite. This evaluates
/// the declared type but grants no ownership; only the authority rewrite
/// checker may publish the returned candidate into a resource context.
pub(crate) fn evaluate_population_authority_candidate(
    entry: &ExecutionState,
    state: &ExecutionState,
    resource: &ResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceFact, RuntimeError>> {
    let ResourceTerm::PopulationAuthority {
        protected,
        population_arity,
        ..
    } = resource.term()
    else {
        return Ok(Err(RuntimeError::FunctionContract(
            "expected a population authority resource".into(),
        )));
    };
    let description =
        match evaluate_resource_type(entry, state, protected, true, assumptions, budget)? {
            Ok(description) => description,
            Err(error) => return Ok(Err(error)),
        };
    let description = match population_arity {
        Some(arity) => match description.with_population_arity(*arity) {
            Ok(description) => description,
            Err(message) => return Ok(Err(RuntimeError::FunctionContract(message.into()))),
        },
        None => description,
    };
    Ok(Ok(ResourceFact::own(Resource::PopulationAuthority(
        description,
    ))))
}

pub(super) fn evaluate_function_resource_spec(
    state: &ExecutionState,
    resource: &ResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceFact, RuntimeError>> {
    evaluate_function_resource_spec_with_entry(state, state, resource, assumptions, budget)
}

/// Resolve logical field values in a resource expression without restoring the
/// parameter's expired storage. Dereferences through a copied pointer remain
/// ordinary current-memory reads, and address-taking remains an lvalue operation.
fn resolve_retained_aggregate_fields(
    entry: &ExecutionState,
    state: &ExecutionState,
    expression: &mut ProgramExpression,
    as_value: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    budget.consume_expression_step()?;
    fn projection(expression: &ProgramExpression) -> Option<(&BindingName, SpecExpression)> {
        match expression {
            ProgramExpression::Variable(name) => {
                Some((name, SpecExpression::ProgramExpression(expression.clone())))
            }
            ProgramExpression::Subobject { pointer, .. } => projection(pointer),
            ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
                let (name, pointer) = projection(pointer)?;
                Some((
                    name,
                    SpecExpression::PointerOffset {
                        pointer: Box::new(pointer),
                        elements: Box::new(SpecExpression::Value(int32(*bytes))),
                        byte_width: 1,
                    },
                ))
            }
            _ => None,
        }
    }
    if as_value
        && let ProgramExpression::TypedLoad {
            pointer,
            value_type,
            ..
        } = expression
        && let Some((parameter, pointer)) = projection(pointer)
        && let Some(LocalBinding::AggregateObject { slot, .. }) = entry.locals.binding(parameter)
        && !state.memory.has_block(&slot.base)
        && !matches!(
            value_type,
            ProgramType::Int32Array(_)
                | ProgramType::UInt8Array(_)
                | ProgramType::Int8Array(_)
                | ProgramType::Int16Array(_)
                | ProgramType::UInt16Array(_)
                | ProgramType::UInt32Array(_)
                | ProgramType::Int128Array(_)
                | ProgramType::Int64Array(_)
                | ProgramType::UInt128Array(_)
                | ProgramType::UInt64Array(_)
                | ProgramType::Float32Array(_)
                | ProgramType::Float64Array(_)
        )
    {
        let field = SpecExpression::AggregateFieldValue {
            parameter: parameter.clone(),
            pointer: Box::new(pointer),
            value_type: *value_type,
        };
        let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_loop_entry(
            state,
            &field,
            Some(entry),
            assumptions,
            budget,
        )?;
        if let [path] = paths.as_slice()
            && path.obligations.is_empty()
        {
            *expression = ProgramExpression::Value(path.value.clone().into_native());
            return Ok(());
        }
    }
    match expression {
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::Variable(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::AddressOf(inner) | ProgramExpression::CheckedObjectAddress(inner) => {
            resolve_retained_aggregate_fields(entry, state, inner, false, assumptions, budget)?
        }
        ProgramExpression::Cast {
            expression: inner, ..
        }
        | ProgramExpression::FloatClassification {
            expression: inner, ..
        }
        | ProgramExpression::Negate(inner)
        | ProgramExpression::FloatNegate(inner)
        | ProgramExpression::EnumField { value: inner, .. }
        | ProgramExpression::EnumIs { value: inner, .. }
        | ProgramExpression::Not(inner)
        | ProgramExpression::BitwiseNot(inner)
        | ProgramExpression::Load(inner)
        | ProgramExpression::TypedLoad { pointer: inner, .. }
        | ProgramExpression::PointerOffsetBytes { pointer: inner, .. }
        | ProgramExpression::Subobject { pointer: inner, .. } => {
            resolve_retained_aggregate_fields(entry, state, inner, true, assumptions, budget)?
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                resolve_retained_aggregate_fields(entry, state, field, true, assumptions, budget)?;
            }
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            resolve_retained_aggregate_fields(entry, state, condition, true, assumptions, budget)?;
            resolve_retained_aggregate_fields(
                entry,
                state,
                then_branch,
                as_value,
                assumptions,
                budget,
            )?;
            resolve_retained_aggregate_fields(
                entry,
                state,
                else_branch,
                as_value,
                assumptions,
                budget,
            )?;
        }
        crate::kernel::binary_c_expression!(left, right) => {
            resolve_retained_aggregate_fields(entry, state, left, true, assumptions, budget)?;
            resolve_retained_aggregate_fields(entry, state, right, true, assumptions, budget)?;
        }
    }
    Ok(())
}

pub(super) fn evaluate_function_resource_spec_with_entry(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    resource: &ResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceFact, RuntimeError>> {
    evaluate_function_resource_spec_with_entry_and_selected_loads(
        entry_state,
        state,
        resource,
        &BTreeMap::new(),
        assumptions,
        budget,
    )
}

fn evaluate_function_resource_spec_with_entry_and_selected_loads(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    resource: &ResourceSpec,
    selected_load_values: &BTreeMap<(Address, ProgramType), ProgramValue>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceFact, RuntimeError>> {
    if !resource.resource_arguments().is_empty()
        && !matches!(resource.term(), ResourceTerm::Instance { .. })
    {
        return Ok(Err(RuntimeError::FunctionContract(
            "resource reference arguments require an exclusive named instance".into(),
        )));
    }
    match resource.term() {
        ResourceTerm::PopulationAuthority {
            protected,
            population_arity,
            ..
        } => {
            let description = match evaluate_resource_type(
                entry_state,
                state,
                protected,
                true,
                assumptions,
                budget,
            )? {
                Ok(description) => description,
                Err(error) => return Ok(Err(error)),
            };
            let description = match population_arity {
                Some(arity) => match description.with_population_arity(*arity) {
                    Ok(description) => description,
                    Err(message) => {
                        return Ok(Err(RuntimeError::FunctionContract(message.into())));
                    }
                },
                None => description,
            };
            let owned = ResourceFact::own(Resource::PopulationAuthority(description.clone()));
            if resource.role() == ResourceTransferRole::Borrow
                && resource.access() == ResourceAccessMode::Own
                && resource.quantity() == &ResourceQuantity::One
                && state.recognizes_population_authority(&description)
                && state.resources().satisfies_fact(&owned, assumptions)
            {
                // Evaluation only names an already owned authority. The
                // concrete call boundary transfers its registered holder;
                // standalone proof entry may recognize one opaque input.
                Ok(Ok(owned))
            } else {
                Ok(Err(RuntimeError::FunctionContract(format!(
                    "Requires owns authority({}(...))",
                    description.family(),
                ))))
            }
        }
        ResourceTerm::MutexGuard {
            mutex,
            state_source,
        } => {
            let selected = match state_source {
                ResourceStateSource::Entry => entry_state,
                _ => state,
            };
            let value = evaluate_loop_effect_segment_value(
                selected,
                mutex,
                assumptions,
                "mutex guard pointer",
                budget,
            )?;
            let Ok(ProgramValue::Pointer(pointer)) = value else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "mutex_guard expects a mutex pointer".into(),
                )));
            };
            let acquisition_state = match resource.state_source() {
                ResourceStateSource::Entry => entry_state,
                _ => state,
            };
            Ok(
                super::mutexes::guard_resource(acquisition_state, pointer.address(), false)
                    .ok_or_else(|| {
                        if resource.role() == ResourceTransferRole::Borrow {
                            RuntimeError::MissingMutexGuard {
                                mutex: pointer.address().clone(),
                            }
                        } else {
                            RuntimeError::FunctionContract(
                                "mutex_guard requires a live acquisition".into(),
                            )
                        }
                    }),
            )
        }
        ResourceTerm::MutexLive {
            mutex,
            state_source,
        } => {
            let selected = match state_source {
                ResourceStateSource::Entry => entry_state,
                _ => state,
            };
            let value = evaluate_loop_effect_segment_value(
                selected,
                mutex,
                assumptions,
                "mutex lifetime pointer",
                budget,
            )?;
            let Ok(ProgramValue::Pointer(pointer)) = value else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "mutex_live expects a mutex pointer".into(),
                )));
            };
            let initialization_state = match resource.state_source() {
                ResourceStateSource::Entry => entry_state,
                _ => state,
            };
            Ok(
                super::mutexes::live_resource(initialization_state, pointer.address(), false)
                    .ok_or_else(|| {
                        if resource.role() == ResourceTransferRole::Borrow {
                            RuntimeError::MissingMutexLive {
                                mutex: pointer.address().clone(),
                            }
                        } else {
                            RuntimeError::FunctionContract(
                                "mutex_live requires a live initialization".into(),
                            )
                        }
                    }),
            )
        }
        ResourceTerm::MutexUse {
            mutex,
            state_source,
            protected,
        } => {
            let selected = match state_source {
                ResourceStateSource::Entry => entry_state,
                _ => state,
            };
            let value = evaluate_loop_effect_segment_value(
                selected,
                mutex,
                assumptions,
                "mutex lifetime pointer",
                budget,
            )?;
            let Ok(ProgramValue::Pointer(pointer)) = value else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "mutex_use expects a mutex pointer".into(),
                )));
            };
            let initialization_state = match resource.state_source() {
                ResourceStateSource::Entry => entry_state,
                _ => state,
            };
            let mut fact = super::mutexes::use_resource(initialization_state, pointer.address());
            if let Some(protected) = protected {
                let description = match evaluate_resource_type(
                    entry_state,
                    state,
                    protected,
                    false,
                    assumptions,
                    budget,
                )? {
                    Ok(description) => description,
                    Err(error) => return Ok(Err(error)),
                };
                let Resource::MutexUse(mut identity) = fact.resource().clone() else {
                    unreachable!()
                };
                identity.protected = Some(description);
                fact = ResourceFact::own(Resource::MutexUse(identity));
            }
            Ok(Ok(fact))
        }
        ResourceTerm::Publication {
            side,
            payload,
            flag,
            state_source,
        } => {
            let selected = match state_source {
                ResourceStateSource::Entry => entry_state,
                _ => state,
            };
            let value = evaluate_loop_effect_segment_value(
                selected,
                flag,
                assumptions,
                "publication flag pointer",
                budget,
            )?;
            let Ok(ProgramValue::Pointer(pointer)) = value else {
                return Ok(Err(RuntimeError::FunctionContract(format!(
                    "{} expects an atomic flag pointer",
                    side.keyword()
                ))));
            };
            let payload = match evaluate_resource_type(
                entry_state,
                state,
                payload,
                false,
                assumptions,
                budget,
            )? {
                Ok(description) => description,
                Err(error) => return Ok(Err(error)),
            };
            Ok(Ok(ResourceFact::own(Resource::Publication(
                PublicationRight {
                    side: *side,
                    flag: pointer.address().clone(),
                    payload,
                    observed: None,
                },
            ))))
        }
        ResourceTerm::Instance {
            identity,
            schema,
            resource: inner_term,
            ..
        } => {
            let inner = match ResourceSpec::new(
                (**inner_term).clone(),
                ResourceAccessMode::Own,
                ResourceQuantity::One,
                resource.role(),
                resource.state_source(),
            ) {
                Ok(inner) => match resource.source_arguments() {
                    Some(arguments) => inner.with_source_arguments(arguments.to_vec()),
                    None => inner,
                },
                Err(error) => {
                    return Ok(Err(RuntimeError::FunctionContract(format!(
                        "invalid named resource body: {error}"
                    ))));
                }
            };
            let required = match evaluate_function_resource_spec_with_entry_and_selected_loads(
                entry_state,
                state,
                &inner,
                selected_load_values,
                assumptions,
                budget,
            )? {
                Ok(resource) => resource,
                Err(error) => return Ok(Err(error)),
            };
            let Some(instance) = state.owned_resource_instance(*identity) else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "named resource instance is not owned".into(),
                )));
            };
            let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = required
            else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "named instance requires an owned resource definition".into(),
                )));
            };
            let references = match evaluate_resource_reference_arguments(state, resource) {
                Ok(references) => references,
                Err(error) => return Ok(Err(error)),
            };
            let mismatch = if instance.resource_arguments() != references.as_slice() {
                Some("resource reference arguments differ".to_owned())
            } else if quantity.as_const() != Some(1) {
                Some("the required quantity is not one".to_owned())
            } else if instance.name() != name {
                Some("resource families differ".to_owned())
            } else if instance.schema() != schema {
                Some("resource field schemas differ".to_owned())
            } else if instance.arguments().len() != arguments.len() {
                Some("resource argument counts differ".to_owned())
            } else {
                instance
                    .arguments()
                    .iter()
                    .zip(arguments.iter())
                    .enumerate()
                    .find(|(_, (a, b))| {
                        !crate::kernel::instance_field_values_proven_equal(
                            (a).into(),
                            (b).into(),
                            assumptions,
                        )
                    })
                    .map(|(index, _)| {
                        format!(
                            "equality of resource argument {} was not established",
                            index + 1
                        )
                    })
            };
            if let Some(reason) = mismatch {
                return Ok(Err(RuntimeError::ContractResourceDiagnostic {
                    reason: format!(
                        "named resource instance does not match its contract: {reason}"
                    ),
                    held: Some(Box::new(ResourceFact::own(Resource::Instance(
                        instance.clone(),
                    )))),
                    required: Box::new(ResourceFact::Own(
                        Resource::Composite { name, arguments },
                        quantity,
                    )),
                    memory: None,
                }));
            }
            Ok(Ok(ResourceFact::own(Resource::Instance(instance.clone()))))
        }
        ResourceTerm::Iterated(spec) => {
            let mut spec = (**spec).clone();
            for expression in spec.expressions_mut() {
                resolve_retained_aggregate_fields(
                    entry_state,
                    state,
                    expression,
                    true,
                    assumptions,
                    budget,
                )?;
            }
            Ok(evaluate_iterated_resource_spec(
                state,
                &spec,
                resource.is_view(),
                assumptions,
                budget,
            )?)
        }
        ResourceTerm::Memory(segment) => {
            let element_width = segment.element_width();
            let mut segment = segment.clone();
            for expression in [&mut segment.base, &mut segment.start, &mut segment.end] {
                resolve_retained_aggregate_fields(
                    entry_state,
                    state,
                    expression,
                    true,
                    assumptions,
                    budget,
                )?;
            }
            let segment = match evaluate_loop_effect_segment(state, &segment, assumptions, budget)?
            {
                Ok(segment) => segment,
                Err(reason) => {
                    return Ok(Err(unevaluated_resource_value(
                        &reason,
                        format!(
                            "could not evaluate {} memory resource segment: {reason}",
                            if resource.is_view() {
                                "a viewed"
                            } else {
                                "an owned"
                            },
                        ),
                    )));
                }
            };
            let range = EvaluatedMemorySegment {
                element_width,
                ..segment
            }
            .into_range();
            Ok(Ok(if resource.is_view() {
                ResourceFact::view_memory(range)
            } else {
                ResourceFact::own_memory(range)
            }))
        }
        ResourceTerm::Composite {
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        }
        | ResourceTerm::Token {
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        } => {
            let family = resource.family();
            let mut fact = match evaluate_function_declared_resource_spec(
                entry_state,
                state,
                resource.access(),
                family,
                name,
                arguments,
                argument_state_sources,
                parameter_types,
                resource.source_arguments(),
                selected_load_values,
                assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            if let ResourceQuantity::Count(quantity) = resource.quantity() {
                if resource.access() != ResourceAccessMode::Own
                    || name == ResourceFact::ALLOCATION_RESOURCE_NAME
                {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "symbolic quantities require owned user-declared resources".to_string(),
                    )));
                }
                let quantity_state = match resource.quantity_state_source() {
                    ResourceStateSource::Entry => entry_state,
                    ResourceStateSource::Current | ResourceStateSource::Post => state,
                };
                let mut quantity = quantity.clone();
                resolve_retained_aggregate_fields(
                    entry_state,
                    quantity_state,
                    &mut quantity,
                    true,
                    assumptions,
                    budget,
                )?;
                let quantity = match evaluate_declared_quantity(
                    quantity_state,
                    &quantity,
                    assumptions,
                    budget,
                )? {
                    Ok(quantity) => quantity,
                    Err(error) => return Ok(Err(error)),
                };
                if !quantity_condition_holds(
                    assumptions,
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(quantity.native_compat().clone()),
                        right: Box::new(MachineTerm::constant(0)),
                    },
                ) {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "declared resource quantity is not known nonnegative; state that the \
                         quantity expression is at least 0 as a requirement, an invariant, or a \
                         fact proved in scope"
                            .to_string(),
                    )));
                }
                let ResourceFact::Own(inner, _) = fact else {
                    return Ok(Err(RuntimeError::FunctionContract(
                        "declared resource quantity did not lower to owned authority".to_string(),
                    )));
                };
                fact = ResourceFact::own_quantity_stored(inner, quantity);
            }
            Ok(Ok(fact))
        }
    }
}

/// Evaluates one iterated guarded-ownership clause to its fact: the element
/// base and index bounds as one memory segment, the guard base, and the guard
/// value, each read once in `state`. Nothing is enumerated.
pub(super) fn evaluate_iterated_resource_spec(
    state: &ExecutionState,
    spec: &crate::kernel::primitives::IteratedSpec,
    view: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceFact, RuntimeError>> {
    let failure = |what: &str| {
        Ok(Err(RuntimeError::FunctionContract(format!(
            "could not evaluate the {what} of the iterated ownership clause of `{}`",
            spec.owner
        ))))
    };
    let Ok(element) = evaluate_loop_effect_segment(state, &spec.element, assumptions, budget)?
    else {
        return failure("element range");
    };
    let guard_base = match evaluate_loop_effect_segment_value(
        state,
        &spec.guard_base,
        assumptions,
        "iterated guard base",
        budget,
    )? {
        Ok(ProgramValue::Pointer(pointer)) => pointer.into_pointer(),
        _ => return failure("guard base"),
    };
    let guard_value = match evaluate_loop_effect_segment_value_retained(
        state,
        &spec.guard_value,
        assumptions,
        "iterated guard value",
        budget,
    )? {
        Ok(value) if value.program_type() == ProgramType::Int32 => {
            let Some(value) = StoredMachineTerm::from_value(value) else {
                return failure("guard value");
            };
            value
        }
        _ => return failure("guard value"),
    };
    let Some(iterated) = crate::kernel::IteratedMemory::new(
        &spec.owner,
        element.base,
        spec.element.element_width,
        spec.stride,
        spec.start_offset,
        spec.end_offset,
        element.start,
        element.end,
        crate::kernel::IteratedGuard::new_stored(
            guard_base,
            spec.guard_cell_type,
            spec.guard_cell_width,
            spec.holds_when_equal,
            guard_value,
        ),
    ) else {
        return failure("element shape");
    };
    let resource = Resource::iterated(iterated);
    Ok(Ok(if view {
        ResourceFact::View(resource)
    } else {
        ResourceFact::own(resource)
    }))
}

/// A clause's declared resource quantity as an int32 term, or the reason it
/// has none. A read the quantity has no authority for is reported as the
/// resource it needed, the way a resource argument's is. The diagnostic
/// carries no memory state: a quantity's failure is its own, and a
/// state would mark it as waiting for a later clause to supply the cell.
fn evaluate_declared_quantity(
    state: &ExecutionState,
    quantity: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<crate::kernel::StoredMachineTerm, RuntimeError>> {
    let mut diagnostic = None;
    Ok(
        match super::loops::evaluate_resource_argument_value_retained(
            state,
            quantity,
            assumptions,
            "declared resource quantity",
            budget,
            &mut diagnostic,
        )? {
            Ok(value) => crate::kernel::StoredMachineTerm::from_value(value)
                .filter(|quantity| quantity.value().program_type() == ProgramType::Int32)
                .ok_or_else(|| {
                    RuntimeError::FunctionContract(
                        "declared resource quantity must evaluate to int32".to_string(),
                    )
                }),
            Err(message) => Err(match diagnostic {
                Some(RuntimeError::ContractResourceDiagnostic {
                    reason,
                    held,
                    required,
                    memory: _,
                }) => RuntimeError::ContractResourceDiagnostic {
                    reason,
                    held,
                    required,
                    memory: None,
                },
                _ => RuntimeError::FunctionContract(message.into()),
            }),
        },
    )
}

/// Lowers the nonnegativity conditions implicit in quantified resource
/// requirements. A function may assume these at its own entry just as it may
/// assume its ordinary `requires`; call sites still use
/// `evaluate_function_resource_spec` and must prove every condition.
pub(crate) fn quantified_resource_requirement_assumptions(
    state: &ExecutionState,
    resources: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<Proposition>, RuntimeError>> {
    let mut propositions = Vec::new();
    let mut quantity_read_state = None;
    for resource in resources {
        let ResourceQuantity::Count(quantity) = resource.quantity() else {
            continue;
        };
        let mut evaluated = evaluate_declared_quantity(
            quantity_read_state.as_ref().unwrap_or(state),
            quantity,
            assumptions,
            budget,
        )?;
        if evaluated.is_err() && quantity_read_state.is_none() {
            // This is an entry-assumption prepass, before the complete resource
            // section can be checked using the quantities' nonnegativity.
            // Let its unquantified clauses supply their ordinary read views,
            // including fields behind folded controls. Never invent a member
            // to read a quantity, or change the entry's actual ownership.
            let unquantified = resources
                .iter()
                .filter(|resource| !matches!(resource.quantity(), ResourceQuantity::Count(_)))
                .cloned()
                .collect::<Vec<_>>();
            let supplied = evaluate_resource_clauses_against_whole_section(
                state,
                state,
                &unquantified,
                definitions,
                assumptions,
                budget,
            )?;
            let read_resources = match supplied {
                Ok(clauses) => resource_clause_section_supply(
                    state,
                    &clauses
                        .into_iter()
                        .map(|clause| clause.fact)
                        .collect::<Vec<_>>(),
                    definitions,
                    assumptions,
                ),
                // Refuse to grant read authority from clauses this partial
                // section could not evaluate. Preserve the quantity's own
                // failure rather than reporting an unrelated clause error.
                Err(_) => state.resources().clone(),
            };
            quantity_read_state = Some(state.clone().with_resource_context(read_resources));
            evaluated = evaluate_declared_quantity(
                quantity_read_state
                    .as_ref()
                    .expect("quantity read frame established"),
                quantity,
                assumptions,
                budget,
            )?;
        }
        let quantity = match evaluated {
            Ok(quantity) => quantity,
            Err(error) => return Ok(Err(error)),
        };
        propositions.push(Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(quantity.native_compat().clone()),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        ));
    }
    Ok(Ok(propositions))
}

#[cfg(test)]
mod quantified_entry_read_tests;

/// An entry clause's evaluation frame can add read authority while remaining
/// at the entry point. Equal memory contents at a later point do not make
/// that later frame eligible to supply entry authority or bindings.
fn declared_resource_argument_state<'a>(
    entry_state: &'a ExecutionState,
    state: &'a ExecutionState,
    source: ResourceStateSource,
) -> &'a ExecutionState {
    match source {
        ResourceStateSource::Entry
            if std::ptr::eq(state, entry_state)
                || state
                    .program_point_id()
                    .is_some_and(|point| entry_state.program_point_id() == Some(point)) =>
        {
            state
        }
        ResourceStateSource::Entry => entry_state,
        ResourceStateSource::Current | ResourceStateSource::Post => state,
    }
}

#[cfg(test)]
mod resource_argument_point_tests;

fn evaluate_function_declared_resource_spec(
    entry_state: &ExecutionState,
    state: &ExecutionState,
    access: ResourceAccessMode,
    family: ResourceFamily,
    name: &str,
    arguments: &[ProgramExpression],
    argument_state_sources: &[ResourceStateSource],
    parameter_types: &[ProgramType],
    source_arguments: Option<&[String]>,
    selected_load_values: &BTreeMap<(Address, ProgramType), ProgramValue>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceFact, RuntimeError>> {
    if arguments.len() != parameter_types.len() || arguments.len() != argument_state_sources.len() {
        return Ok(Err(RuntimeError::FunctionContract(format!(
            "resource `{name}` received the wrong number of arguments"
        ))));
    }
    let mut values = Vec::new();
    for (index, ((argument, argument_state_source), parameter_type)) in arguments
        .iter()
        .zip(argument_state_sources)
        .zip(parameter_types)
        .enumerate()
    {
        let argument_state =
            declared_resource_argument_state(entry_state, state, *argument_state_source);
        let written = argument;
        let mut argument = argument.clone();
        resolve_retained_aggregate_fields(
            entry_state,
            argument_state,
            &mut argument,
            true,
            assumptions,
            budget,
        )?;
        let argument = &argument;
        let allocation_element_count = (name == ResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 1)
            .then(|| match argument {
                ProgramExpression::Multiply(left, right)
                    if right.as_ref()
                        == &ProgramExpression::Value(int32(ProgramType::Int32.byte_width())) =>
                {
                    Some(left.as_ref())
                }
                ProgramExpression::Multiply(left, right)
                    if left.as_ref()
                        == &ProgramExpression::Value(int32(ProgramType::Int32.byte_width())) =>
                {
                    Some(right.as_ref())
                }
                _ => None,
            })
            .flatten();
        let selected_value = if let ProgramExpression::TypedLoad {
            pointer,
            value_type,
            volatile: false,
            ..
        } = argument
        {
            match evaluate_loop_effect_segment_value(
                argument_state,
                pointer,
                assumptions,
                "selected resource field address",
                budget,
            )? {
                Ok(ProgramValue::Pointer(address))
                    if !argument_state.memory().has_known_cell_at(address.address()) =>
                {
                    selected_load_values
                        .get(&(address.address().clone(), *value_type))
                        .cloned()
                }
                _ => None,
            }
        } else {
            None
        };
        // A symbolic load can evaluate to a symbolic value even though no
        // heap cell was materialized after the modular call. A cached cell,
        // when present, follows the ordinary evaluator instead.
        let value = if let Some(value) = selected_value {
            value
        } else if let Some(element_count) = allocation_element_count {
            let count = match evaluate_loop_effect_segment_value(
                argument_state,
                element_count,
                assumptions,
                &format!("resource `{name}` argument {index} element count"),
                budget,
            )? {
                Ok(ProgramValue::Int32(count)) => count,
                Ok(_) | Err(_) => {
                    return Ok(Err(RuntimeError::FunctionContract(format!(
                        "resource `{name}` has an invalid allocation element count"
                    ))));
                }
            };
            int32(MachineTerm::multiply(
                count,
                MachineTerm::constant(ProgramType::Int32.byte_width()),
            ))
        } else {
            let mut diagnostic = None;
            let mut evaluated = super::loops::evaluate_resource_argument_value(
                argument_state,
                argument,
                assumptions,
                &format!("resource `{name}` argument {}", index + 1),
                budget,
                &mut diagnostic,
            )?;
            // An argument read at entry is read with the authority held at
            // entry. The call's own frame stands in for entry where no cell
            // changed, and adds authority, but it lacks what the call
            // consumed: a `const` unpack's lent view of the memory the
            // argument reads.
            if evaluated.is_err()
                && matches!(argument_state_source, ResourceStateSource::Entry)
                && !std::ptr::eq(argument_state, entry_state)
            {
                let mut at_entry = written.clone();
                resolve_retained_aggregate_fields(
                    entry_state,
                    entry_state,
                    &mut at_entry,
                    true,
                    assumptions,
                    budget,
                )?;
                let mut entry_diagnostic = None;
                let retried = super::loops::evaluate_resource_argument_value(
                    entry_state,
                    &at_entry,
                    assumptions,
                    &format!("resource `{name}` argument {}", index + 1),
                    budget,
                    &mut entry_diagnostic,
                )?;
                if retried.is_ok() {
                    evaluated = retried;
                }
            }
            match evaluated {
                Ok(value) => value,
                Err(error) => {
                    if let Some(mut diagnostic) = diagnostic {
                        if let (
                            Some(spelling),
                            RuntimeError::ContractResourceDiagnostic { reason, .. },
                        ) = (
                            source_arguments.and_then(|items| items.get(index)),
                            &mut diagnostic,
                        ) {
                            *reason = format!("{reason}; expression `{spelling}`");
                        }
                        return Ok(Err(diagnostic));
                    }
                    if let Some(spelling) = source_arguments.and_then(|items| items.get(index)) {
                        let action = match access {
                            ResourceAccessMode::Own => "owns",
                            ResourceAccessMode::View => "views",
                        };
                        return Ok(Err(unevaluated_resource_value(
                            &error,
                            format!(
                                "could not evaluate `{spelling}` while checking `{action} {name}({})`: {error}",
                                source_arguments.unwrap_or_default().join(", ")
                            ),
                        )));
                    }
                    return Ok(Err(unevaluated_resource_value(
                        &error,
                        format!("could not evaluate resource `{name}` argument {index}: {error}"),
                    )));
                }
            }
        };
        let accepts_allocation_pointer = name == ResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 0
            && matches!(&value, ProgramValue::Pointer(pointer) if pointer.program_type().pointee_type().is_some());
        let value = if name == ResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 1
            && let ProgramValue::UInt64(bytes) = value.numeric_value()
        {
            match uint64_allocation_size_argument(bytes, assumptions) {
                Ok(value) => value,
                Err(error) => return Ok(Err(error)),
            }
        } else {
            value
        };
        // A 64-bit `allocation` byte count is a `uint64` size (D4).
        let accepts_allocation_size = name == ResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 1
            && matches!(&value, ProgramValue::UInt64(_));
        if !accepts_allocation_pointer
            && !accepts_allocation_size
            && !parameter_type.accepts(&value)
        {
            return Ok(Err(RuntimeError::FunctionContract(format!(
                "resource `{name}` argument {index} has the wrong type"
            ))));
        }
        // Logical resource indices observe numbers; they do not store C
        // representation records or carry those records through loop models.
        values.push(match value.resource_argument_at_type(*parameter_type) {
            ProgramValue::PointerInteger(word) => *word.numeric,
            value => value,
        });
    }
    let resource = match family {
        ResourceFamily::Parameter => {
            return Ok(Err(RuntimeError::FunctionContract(
                "a resource descriptor carries no ownership".into(),
            )));
        }
        ResourceFamily::Composite => Resource::Composite {
            name: name.to_string(),
            arguments: values.into_iter().map(AlgebraicValue::Program).collect(),
        },
        ResourceFamily::Token => Resource::Token {
            name: name.to_string(),
            arguments: values.into_iter().map(AlgebraicValue::Program).collect(),
        },
        ResourceFamily::PopulationAuthority
        | ResourceFamily::Memory
        | ResourceFamily::Instance
        | ResourceFamily::MutexGuard
        | ResourceFamily::MutexLive
        | ResourceFamily::MutexUse
        | ResourceFamily::Publication
        | ResourceFamily::Iterated => {
            return Ok(Err(RuntimeError::FunctionContract(
                "declared resources cannot use the raw memory family".to_string(),
            )));
        }
    };
    Ok(Ok(match access {
        ResourceAccessMode::Own => ResourceFact::own(resource),
        ResourceAccessMode::View => ResourceFact::View(resource),
    }))
}

/// The `allocation` token argument a contract's `uint64` (`size_t`) byte
/// count states (`design/heap-allocation-sizes.md`, D4).
///
/// A constant that fits a 32-bit size is one, as `malloc` of a constant
/// `size_t` size makes it (D2). Any other value is a 64-bit size, admitted
/// under the decision `malloc` makes for one
/// ([`crate::kernel::eval::uint64_allocation_size_bytes_are_exact`]): at most
/// `PTRDIFF_MAX` and positive, and a product with a constant factor `k` only
/// with its other factor decided at most `PTRDIFF_MAX / k`. A `size_t`
/// product may wrap, and the heap reads `n * k` bytes back as `n` elements,
/// so a token whose product could have wrapped is never formed.
///
/// A clause someone else established is assumed, not decided again: a
/// contract's own entry clauses, which every caller establishes by
/// evaluating them under this decision, and the body of a held composite,
/// which its fold established (`assume_entry_clause_spans`). Every other
/// evaluation decides: a requirement at a call, a clause a function produces
/// at its exit, and one an opaque or extern call returns to its caller.
fn uint64_allocation_size_argument(
    bytes: &MachineTerm,
    assumptions: &PureFactContext,
) -> Result<ProgramValue, RuntimeError> {
    if let Some(constant) = bytes.uint64_as_const()
        && (1..=i32::MAX as u64).contains(&constant)
    {
        return Ok(int32(MachineTerm::constant(constant as u32)));
    }
    if assumptions.should_assume_entry_clause_spans()
        || crate::kernel::eval::uint64_allocation_size_bytes_are_exact(bytes, assumptions)
    {
        Ok(ProgramValue::UInt64(bytes.clone()))
    } else {
        Err(RuntimeError::FunctionContract(
            "resource `allocation` has a 64-bit byte count not proved to fit a heap block: \
             it needs `1 <= bytes <= PTRDIFF_MAX`, and a product `n * k` with a constant `k` \
             needs `1 <= n <= PTRDIFF_MAX / k`"
                .to_string(),
        ))
    }
}

fn resource_fact_transfer_priority(resource: &ResourceFact) -> u8 {
    match resource {
        ResourceFact::Own(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
            _,
        ) => 2,
        ResourceFact::View(_) => 0,
        ResourceFact::Own(Resource::Memory(_), _) => 1,
        ResourceFact::Own(
            Resource::Composite { .. }
            | Resource::Token { .. }
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_),
            _,
        ) => 2,
    }
}

fn unreturned_allocation_obligation(
    actual_state: &ExecutionState,
    returned_resources: &ResourceContext,
    function: &ProgramFunction,
    assumptions: &PureFactContext,
) -> Result<Option<(ResourceFact, Option<ResourceFact>)>, RuntimeError> {
    let Some(actual) = expand_all_composite_resource_facts_at_state(
        actual_state.resources(),
        function.composite_resource_definitions(),
        actual_state,
        assumptions,
    ) else {
        return Err(RuntimeError::FunctionContract(
            "could not inspect allocation obligations at function return".to_string(),
        ));
    };
    let mut checked_return_frontier = returned_resources.clone();
    {
        for fact in returned_resources.facts() {
            let Resource::Composite { name, .. } = fact.resource() else {
                continue;
            };
            let Some(definition) = function
                .contract_interface()
                .composite_resource_definition(name)
            else {
                continue;
            };
            if !definition
                .contains()
                .iter()
                .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
            {
                continue;
            }
            let Some(supporting) = actual_state
                .resources()
                .directly_supporting_fact(fact, assumptions)
            else {
                continue;
            };
            if !supporting.is_own() || supporting == fact {
                continue;
            }
            actual_state
                .checked_authority_wrapper_body(supporting, definition, assumptions)
                .map_err(RuntimeError::FunctionContract)?;
            checked_return_frontier = checked_return_frontier
                .without_fact_incrementally(fact, assumptions)
                .ok_or_else(|| RuntimeError::MissingResource {
                    resource: Box::new(fact.clone()),
                })?
                .unchecked_with_fact(supporting.clone());
        }
    }
    let returned_resources = &checked_return_frontier;
    let mut returned_read_state = actual_state.clone();
    {
        for fact in returned_resources.facts() {
            let Resource::Composite { name, .. } = fact.resource() else {
                continue;
            };
            let Some(definition) = function
                .contract_interface()
                .composite_resource_definition(name)
            else {
                continue;
            };
            if !definition
                .contains()
                .iter()
                .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
                || actual_state.resources().satisfies_fact(fact, assumptions)
            {
                continue;
            }
            actual_state
                .clone()
                .with_resource_context(actual.clone())
                .checked_authority_wrapper_fold_preflight(fact, definition, assumptions)
                .map_err(RuntimeError::FunctionContract)?;
            returned_read_state =
                returned_read_state.with_resource_context(returned_resources.clone());
        }
    }
    let Some(returned_resources) = expand_all_composite_resource_facts_at_state(
        returned_resources,
        function.composite_resource_definitions(),
        &returned_read_state,
        assumptions,
    ) else {
        for fact in returned_resources.facts() {
            let Resource::Composite { name, .. } = fact.resource() else {
                continue;
            };
            let Some(definition) = function
                .contract_interface()
                .composite_resource_definition(name)
            else {
                continue;
            };
            if definition
                .contains()
                .iter()
                .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
                && let Err(reason) = returned_read_state.checked_authority_wrapper_body(
                    fact,
                    definition,
                    assumptions,
                )
            {
                return Err(RuntimeError::FunctionContract(format!(
                    "could not inspect returned allocation obligations: control {name}: {reason}"
                )));
            }
        }
        return Err(RuntimeError::FunctionContract(
            "could not inspect returned allocation obligations".to_string(),
        ));
    };
    let mut budget = ExecutionBudget::beside_live_state();
    let population_bodies = match evaluate_resource_population_body_resources(
        &returned_resources,
        actual_state,
        function.composite_resource_definitions(),
        assumptions,
        &mut budget,
        false,
    ) {
        Ok(Ok(resources)) => resources,
        Ok(Err(error)) => return Err(error),
        Err(limit) => {
            return Err(RuntimeError::FunctionContract(format!(
                "counted population allocation inspection stopped at {}",
                limit.describe()
            )));
        }
    };
    let returned_resources = returned_resources
        .clone()
        .unchecked_with_facts(population_bodies.facts().iter().cloned());
    let allocation = actual
        .facts()
        .iter()
        .filter(|fact| fact.allocation().is_some())
        .find(|allocation| {
            returned_resources
                .cached_support_exposing_fact(allocation, assumptions)
                .is_none()
                && expose_composite_resource_fact(
                    &returned_resources,
                    allocation,
                    function.composite_resource_definitions(),
                    actual_state.memory(),
                    assumptions,
                )
                .is_none()
        })
        .cloned();
    Ok(allocation.map(|allocation| {
        let resource =
            resource_fact_containing_allocation(actual_state, &allocation, function, assumptions);
        (allocation, resource)
    }))
}

/// Finds the folded declared resource whose body accounts for a leaked
/// allocation. This is diagnostic metadata only: the allocation check
/// remains the authority, and failure to identify a containing resource must
/// not change verification.
fn resource_fact_containing_allocation(
    state: &ExecutionState,
    allocation: &ResourceFact,
    function: &ProgramFunction,
    assumptions: &PureFactContext,
) -> Option<ResourceFact> {
    state
        .resources()
        .facts()
        .iter()
        .filter(|fact| {
            fact.is_own()
                && matches!(
                    fact.resource(),
                    Resource::Composite { .. } | Resource::Token { .. }
                )
        })
        .find_map(|candidate| {
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(candidate.clone());
            let mut budget = ExecutionBudget::beside_live_state();
            let Ok(Ok(body)) = evaluate_resource_population_body_resources(
                &singleton,
                state,
                function.composite_resource_definitions(),
                assumptions,
                &mut budget,
                true,
            ) else {
                return None;
            };
            body.facts()
                .iter()
                .any(|fact| {
                    fact == allocation
                        || fact.core_with_assumptions(assumptions).is_some_and(|core| {
                            allocation
                                .core_with_assumptions(assumptions)
                                .is_some_and(|allocation_core| core == allocation_core)
                        })
                })
                .then(|| candidate.clone())
        })
}

/// Ends the automatic lifetimes the returning frame created.
///
/// A body executed at a call site declares its locals into the caller's own
/// memory, and nothing else retires them: without this the callee's cells stay
/// readable under the caller's next declaration of that name, and a pointer to
/// one of the callee's locals stays dereferenceable after the frame is gone.
///
/// Only identities this frame minted are retired — the generational
/// declarations and the frame-scoped parameter slots. A value-only parameter
/// is deliberately excluded: its pseudo-slot uses a separate value-parameter
/// namespace and owns no block.
///
/// Bounded by this frame's own bindings; it reads no caller state.
fn retired_automatistorage_creation_blocks(
    state: &ExecutionState,
    after: &SymbolicMemory,
) -> Vec<AddressBase> {
    state
        .locals
        .slots()
        .filter(|slot| state.memory.has_block(&slot.base) && !after.has_block(&slot.base))
        .map(|slot| slot.base.clone())
        .collect()
}

type AutomaticLifetimeInput = (usize, usize, usize, usize, usize);

struct AutomaticLifetimeRetirement {
    // Pin the input roots so their addresses cannot be reused during a session.
    input: SymbolicMemory,
    blocks: Vec<AddressBase>,
    after: SymbolicMemory,
}

thread_local! {
    static AUTOMATIC_LIFETIME_RETIREMENT: std::cell::RefCell<std::collections::HashMap<AutomaticLifetimeInput, AutomaticLifetimeRetirement>> = std::cell::RefCell::new(std::collections::HashMap::new());
}

pub(super) fn clear_automatic_lifetime_retirement() {
    AUTOMATIC_LIFETIME_RETIREMENT.with(|memo| memo.borrow_mut().clear());
}

/// Only the physical transition is reused. Callers check current loan,
/// mutex, population and return-value restrictions before calling this.
fn retire_automatic_lifetime_blocks(
    before: &SymbolicMemory,
    blocks: &[AddressBase],
) -> SymbolicMemory {
    if blocks.is_empty() {
        return before.clone();
    }
    crate::instrumentation::record_deterministic_work(1);
    let key = before.diagnostic_identity();
    let reused = AUTOMATIC_LIFETIME_RETIREMENT.with(|memo| {
        let memo = memo.borrow();
        let retained = memo.get(&key)?;
        if !before.same_storage_roots(&retained.input) || blocks.len() != retained.blocks.len() {
            return None;
        }
        crate::instrumentation::record_deterministic_work(blocks.len());
        (blocks == retained.blocks).then(|| retained.after.clone())
    });
    if let Some(after) = reused {
        return after;
    }
    let after = blocks.iter().fold(before.clone(), |memory, block| {
        memory.without_local_block(block)
    });
    AUTOMATIC_LIFETIME_RETIREMENT.with(|memo| {
        memo.borrow_mut().insert(
            key,
            AutomaticLifetimeRetirement {
                input: before.clone(),
                blocks: blocks.to_vec(),
                after: after.clone(),
            },
        );
    });
    after
}

fn end_inline_frame_automatic_lifetimes(
    state: &ExecutionState,
) -> Result<SymbolicMemory, RuntimeError> {
    let memory = &state.memory;
    let mut blocks = Vec::new();
    let mut selected = BTreeSet::new();
    for slot in state.locals.slots() {
        crate::instrumentation::record_deterministic_work(1);
        if !block_is_frame_scoped_automatic_object(&slot.base) {
            continue;
        }
        if !memory.has_block(&slot.base) {
            continue;
        }
        if !selected.insert(slot.base.clone()) {
            continue;
        }
        if let Some(error) = super::mutexes::automatic_storage_refusal(
            state,
            state
                .locals
                .name_for_slot(slot)
                .expect("indexed local slot"),
            &slot.base,
        ) {
            return Err(error);
        }
        if let Some(error) = state.population_storage_retirement_refusal(&slot.base) {
            return Err(error);
        }
        if let Some(error) = state.automatic_storage_loan_refusal(&slot.base) {
            return Err(error);
        }
        blocks.push(slot.base.clone());
    }
    Ok(retire_automatic_lifetime_blocks(memory, &blocks))
}

/// A non-inline body's declared locals have ended before its postconditions
/// are read, including locals exported through a pointer field or out-parameter.
/// Parameter storage expires too. Logical field projections use the entry
/// value independently of storage permissions. Preserve the materialized
/// aggregate result, which belongs to the caller, and caller-owned objects.
fn end_function_body_automatic_lifetimes(
    state: &ExecutionState,
    function: &ProgramFunction,
    caller: &SymbolicMemory,
    returned: Option<&ProgramValue>,
) -> Result<SymbolicMemory, RuntimeError> {
    let memory = &state.memory;
    let mut blocks = Vec::new();
    let mut selected = BTreeSet::new();
    for slot in state.locals.slots() {
        crate::instrumentation::record_deterministic_work(1);
        if slot.base.is_local_block()
            && !(function.return_aggregate_layout().is_some()
                && matches!(returned, Some(ProgramValue::Pointer(pointer)) if pointer.address().base == slot.base))
            && !caller.has_block(&slot.base)
            && memory.has_block(&slot.base)
        {
            if !selected.insert(slot.base.clone()) {
                continue;
            }
            if let Some(error) = super::mutexes::automatic_storage_refusal(
                state,
                state
                    .locals
                    .name_for_slot(slot)
                    .expect("indexed local slot"),
                &slot.base,
            ) {
                return Err(error);
            }
            if let Some(error) = state.population_storage_retirement_refusal(&slot.base) {
                return Err(error);
            }
            if let Some(error) = state.automatic_storage_loan_refusal(&slot.base) {
                return Err(error);
            }
            blocks.push(slot.base.clone());
        }
    }
    for (_, pointer) in state.aggregate_step_objects.iter() {
        crate::instrumentation::record_deterministic_work(1);
        if !caller.has_block(&pointer.base)
            && memory.has_block(&pointer.base)
            && selected.insert(pointer.base.clone())
        {
            if let Some(error) = state.population_storage_retirement_refusal(&pointer.base) {
                return Err(error);
            }
            if let Some(error) = super::mutexes::automatic_storage_refusal(
                state,
                "aggregate expression result",
                &pointer.base,
            ) {
                return Err(error);
            }
            if let Some(error) = state.automatic_storage_loan_refusal(&pointer.base) {
                return Err(error);
            }
            blocks.push(pointer.base.clone());
        }
    }
    Ok(retire_automatic_lifetime_blocks(memory, &blocks))
}

/// Whether this block is an automatic object a call frame minted for itself,
/// rather than the outermost frame's `local:<name>` or a pseudo-slot.
fn block_is_frame_scoped_automatic_object(block: &AddressBase) -> bool {
    block.starts_with("local:lifetime:") || block.starts_with("local:frame:")
}

/// Returns the caller-visible memory after a function returns.
pub(in crate::kernel) fn function_exit_memory(
    caller_state: &ExecutionState,
    callee_state: &ExecutionState,
    value: &ExecutionValue,
    function: &ProgramFunction,
) -> Result<SymbolicMemory, RuntimeError> {
    if function.return_aggregate_layout().is_some() {
        return Ok(callee_state.memory.clone());
    }
    match value.pointer() {
        Some(pointer)
            if pointer.address().base.is_local_block()
                && !caller_state.memory.has_block(&pointer.address().base) =>
        {
            let block = &pointer.address().base;
            if let Some(error) = callee_state.automatic_storage_loan_refusal(block) {
                return Err(error);
            }
            Ok(callee_state.memory.without_local_block(block))
        }
        _ => Ok(callee_state.memory.clone()),
    }
}

/// Checks allocation support using a resource context that a caller has
/// already lowered and checked.  This is the shared path for explicit
/// `produces` claims: re-evaluating the function's declared return resources
/// here would discard entry states such as `old(...)` and make the
/// allocation-lifetime closer prove the same claim a second time.
pub(crate) fn unreturned_allocation_with_checked_returned_resources(
    caller_state: &ExecutionState,
    state: &ExecutionState,
    value: &ProgramValue,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    returned_resources: &ResourceContext,
    assumptions: &PureFactContext,
    _budget: &mut ExecutionBudget,
) -> Result<Option<crate::kernel::proof::LiveAllocationObligation>, RuntimeError> {
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Err(RuntimeError::FunctionContract(
            "allocation-delta checking requires concrete symbolic contract arguments".to_string(),
        ));
    };
    let entry_state = bind_contract_proof_arguments(caller_state, function, &argument_values)
        .ok_or(RuntimeError::TypeMismatch)?;
    let mut output_state = with_contract_argument_views(state, function, &argument_values);
    if function.return_type() != ProgramType::Void {
        set_function_result(&mut output_state, function, value.clone());
    }
    let function_can_package_allocation =
        function
            .composite_resource_definitions()
            .iter()
            .any(|definition| {
                definition.contains().iter().any(|resource| {
                    resource.family() == ResourceFamily::Token
                        && resource.declared_name() == Some(ResourceFact::ALLOCATION_RESOURCE_NAME)
                })
            });
    if !function_can_package_allocation
        && !output_state
            .resources()
            .facts()
            .iter()
            .any(|fact| fact.allocation().is_some())
    {
        return Ok(None);
    }
    let Some(actual_resources) = expand_all_composite_resource_facts_at_state(
        output_state.resources(),
        function.composite_resource_definitions(),
        &output_state,
        assumptions,
    ) else {
        return Err(RuntimeError::FunctionContract(
            "could not inspect allocation obligations at function return".to_string(),
        ));
    };
    if !actual_resources
        .facts()
        .iter()
        .any(|fact| fact.allocation().is_some())
    {
        return Ok(None);
    }
    // The checked resource result lists `produces` clauses. Owned borrowed
    // inputs are returned separately by the contract, and may contain the
    // allocation (for example inside an authority-backed control).
    let borrowed = function
        .resource_requires()
        .iter()
        .filter(|spec| spec.role() == ResourceTransferRole::Borrow)
        .cloned()
        .collect::<Vec<_>>();
    let returned = if borrowed.is_empty() {
        returned_resources.clone()
    } else {
        let mut budget = ExecutionBudget::beside_live_state();
        let (_, entry_clauses) = evaluate_function_resource_context_with_metadata(
            &entry_state,
            function.resource_requires(),
            function.composite_resource_definitions(),
            &assumptions.clone().assume_entry_clause_spans(),
            &mut budget,
        )
        .map_err(|limit| RuntimeError::FunctionContract(limit.describe()))??;
        returned_resources.clone().unchecked_with_facts(
            entry_clauses
                .into_iter()
                .filter(|checked| checked.role == ResourceTransferRole::Borrow)
                .map(|checked| checked.fact)
                .filter(|fact| !returned_resources.satisfies_fact(fact, assumptions)),
        )
    };
    let Some((allocation, holder)) =
        unreturned_allocation_obligation(&output_state, &returned, function, assumptions)?
    else {
        return Ok(None);
    };
    Ok(Some(crate::kernel::proof::LiveAllocationObligation::new(
        allocation, holder,
    )))
}

pub(crate) fn unreturned_allocation_at_function_exit(
    caller_state: &ExecutionState,
    state: &ExecutionState,
    value: &ProgramValue,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Option<crate::kernel::proof::LiveAllocationObligation>, RuntimeError>> {
    let function_can_package_allocation =
        function
            .composite_resource_definitions()
            .iter()
            .any(|definition| {
                definition.contains().iter().any(|resource| {
                    resource.family() == ResourceFamily::Token
                        && resource.declared_name() == Some(ResourceFact::ALLOCATION_RESOURCE_NAME)
                })
            });
    if !function_can_package_allocation
        && !state
            .resources()
            .facts()
            .iter()
            .any(|fact| fact.allocation().is_some())
    {
        return Ok(Ok(None));
    }
    let Some(actual_resources) = expand_all_composite_resource_facts_at_state(
        state.resources(),
        function.composite_resource_definitions(),
        state,
        assumptions,
    ) else {
        return Ok(Err(RuntimeError::FunctionContract(
            "could not inspect allocation obligations at function exit".to_string(),
        )));
    };
    if !actual_resources
        .facts()
        .iter()
        .any(|fact| fact.allocation().is_some())
    {
        return Ok(Ok(None));
    }
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(RuntimeError::FunctionContract(
            "allocation-delta checking requires concrete symbolic contract arguments".to_string(),
        )));
    };
    let Some(entry_state) = bind_contract_proof_arguments(caller_state, function, &argument_values)
    else {
        return Ok(Err(RuntimeError::TypeMismatch));
    };
    let mut output_state = with_contract_argument_views(state, function, &argument_values);
    if function.return_type() != ProgramType::Void {
        set_function_result(&mut output_state, function, value.clone());
    }
    let entry_clauses = match evaluate_function_resource_context_with_metadata(
        &entry_state,
        function.resource_requires(),
        function.composite_resource_definitions(),
        &assumptions.clone().assume_entry_clause_spans(),
        budget,
    )? {
        Ok((_, clauses)) => clauses,
        Err(error) => return Ok(Err(error)),
    };
    let returned_resources = match evaluate_function_return_resource_context(
        function,
        &entry_clauses,
        &entry_state,
        &output_state,
        function.resource_ensures().len(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    match unreturned_allocation_obligation(
        &output_state,
        &returned_resources,
        function,
        assumptions,
    ) {
        Ok(obligation) => Ok(Ok(obligation.map(|(allocation, holder)| {
            crate::kernel::proof::LiveAllocationObligation::new(allocation, holder)
        }))),
        Err(error) => Ok(Err(error)),
    }
}

fn function_outcome_from_body_changing_quantities(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    outcome: StatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> ExecutionResult<(FunctionOutcome, Vec<ProofObligation>)> {
    if let Some(error) = exceptional_outcome_declaration_error(function, &outcome) {
        return Ok((FunctionOutcome::RuntimeError(error), obligations));
    }
    if matches!(&outcome, StatementOutcome::Throw { .. })
        && (!function.resource_requires().is_empty()
            || !function.resource_ensures().is_empty()
            || !function.resource_constructors().is_empty())
    {
        return Ok((
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                "exceptional outcomes with population transitions require an exceptional contract interface"
                    .to_string(),
            )),
            obligations,
        ));
    }
    let StatementOutcome::Return { value, mut state } = outcome else {
        return Ok(function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        ));
    };
    if let Some(undefined_behavior) =
        freed_pointer_return_conversion(&state, function, &value, assumptions)
    {
        return Ok((
            FunctionOutcome::UndefinedBehavior(undefined_behavior),
            obligations,
        ));
    }
    if let Some(refusal) = incompatible_pointer_return(&state, function, &value, assumptions) {
        return Ok((FunctionOutcome::RuntimeError(refusal), obligations));
    }
    let Some(value) =
        coerce_retained_function_return_value(value, function, &mut obligations, assumptions)
    else {
        return Ok((
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                "{} {RETURN_TYPE_MISMATCH}",
                function.name()
            ))),
            obligations,
        ));
    };
    if function.return_type() != ProgramType::Void {
        set_function_result(&mut state, function, value.clone());
    }
    Ok(function_outcome_from_body(
        caller_state,
        function,
        StatementOutcome::Return { value, state },
        obligations,
        assumptions,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn function_outcome_from_body_with_resource_transfer(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    outcome: StatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    transfer: &FunctionResourceTransfer,
    argument_values: &[ProgramValue],
    reestablish_population_invariants: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(
    FunctionOutcome,
    Vec<ProofObligation>,
    Option<Arc<CheckedLoanCallEvidence>>,
)> {
    if let Some(error) = exceptional_outcome_declaration_error(function, &outcome) {
        return Ok((FunctionOutcome::RuntimeError(error), obligations, None));
    }
    let (exceptional, value, mut state) = match outcome {
        StatementOutcome::Return { value, state } => (false, value, state),
        StatementOutcome::Throw { value, state } => {
            if !function.resource_constructors().is_empty()
                || function
                    .resource_requires()
                    .iter()
                    .chain(function.resource_ensures())
                    .any(|resource| {
                        resource.role() != ResourceTransferRole::Borrow
                            || !matches!(resource.term(), ResourceTerm::Memory(_))
                    })
            {
                return Ok((
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                        "exceptional exits support borrowed resources only".into(),
                    )),
                    obligations,
                    None,
                ));
            }
            (true, value, state)
        }
        other => {
            let (outcome, obligations) = function_outcome_from_body(
                caller_state,
                function,
                other,
                obligations,
                assumptions,
                None,
            );
            return Ok((outcome, obligations, None));
        }
    };
    let value = if exceptional {
        value
    } else {
        if let Some(undefined_behavior) =
            freed_pointer_return_conversion(&state, function, &value, assumptions)
        {
            return Ok((
                FunctionOutcome::UndefinedBehavior(undefined_behavior),
                obligations,
                None,
            ));
        }
        if let Some(refusal) = incompatible_pointer_return(&state, function, &value, assumptions) {
            return Ok((FunctionOutcome::RuntimeError(refusal), obligations, None));
        }
        let Some(value) =
            coerce_retained_function_return_value(value, function, &mut obligations, assumptions)
        else {
            return Ok((
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                    "{} {RETURN_TYPE_MISMATCH}",
                    function.name()
                ))),
                obligations,
                None,
            ));
        };

        value
    };

    if !exceptional
        && reestablish_population_invariants
        && let Some(error) =
            construction_return::complete_parameter(&state, function.contract_interface())
    {
        return Ok((FunctionOutcome::RuntimeError(error), obligations, None));
    }

    // A body return still names its aggregate source; copy it to the
    // caller-visible result object before retiring the source's activation.
    // Resource completion over an already completed outcome keeps its result.
    let value = if !exceptional
        && reestablish_population_invariants
        && function.return_aggregate_layout().is_some()
    {
        match complete_aggregate_return(&mut state, function, value.into_native()) {
            Ok(value) => value.into(),
            Err(AggregateReturnRefusal::UninitializedRead) => {
                return Ok((
                    FunctionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead),
                    obligations,
                    None,
                ));
            }
            Err(AggregateReturnRefusal::InvalidValue) => {
                return Ok((
                    FunctionOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    obligations,
                    None,
                ));
            }
        }
    } else {
        value
    };

    if exceptional {
        state.locals.set_typed(
            CONTRACT_EXCEPTION,
            value.clone().into_native(),
            value.native().program_type(),
        );
    } else if function.return_type() != ProgramType::Void {
        set_function_result(&mut state, function, value.clone());
    }
    let retired_memory = match end_function_body_automatic_lifetimes(
        &state,
        function,
        caller_state.memory(),
        value.native_payload(),
    ) {
        Ok(memory) => memory,
        Err(error) => return Ok((FunctionOutcome::RuntimeError(error), obligations, None)),
    };
    let retired_creation_blocks = retired_automatistorage_creation_blocks(&state, &retired_memory);
    state.set_memory(retired_memory);
    for block in retired_creation_blocks {
        if let Err(error) = state.retire_population_storage(&block) {
            return Ok((FunctionOutcome::RuntimeError(error), obligations, None));
        }
    }
    let mut named_inputs = transfer
        .consumed_inputs
        .iter()
        .filter_map(|checked| match checked.fact.resource() {
            Resource::Instance(instance) => Some(instance),
            _ => None,
        })
        .peekable();
    let has_named_input = named_inputs.peek().is_some();
    let checked_named_deaths = has_named_input
        && named_inputs.all(|instance| {
            state
                .population_effects
                .creation
                .as_ref()
                .is_some_and(|events| {
                    events
                        .consumed_imported_instance(
                            &ResourceDescription::from_instance(instance),
                            instance.identity(),
                        )
                        .is_some()
                })
        });
    let imported_named_consumption = state.population_effects.creation.as_ref()
        .is_some_and(|events| transfer.consumed_inputs.iter().any(|checked| {
            matches!(checked.fact.resource(), Resource::Instance(instance)
                if events.recognizes_imported_population(&ResourceDescription::from_instance(instance)))
        }));
    if imported_named_consumption && !checked_named_deaths {
        return Ok((
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                "Requires a checked death for every consumed named member".into(),
            )),
            obligations,
            None,
        ));
    }
    let caller_resources_after_requirements = transfer.caller_resources_after_requirements.clone();
    let output_resource_state = with_contract_argument_views(&state, function, argument_values);
    let entry_resource_state =
        with_contract_argument_views(caller_state, function, argument_values);
    let mut transfer = transfer.clone();
    let ContractReturnResources {
        output_resources,
        return_resources,
        escrow_boundary,
        ensured_views: returned_views,
        produced_borrowing_pieces,
        returned_entry_partition,
    } = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return resource evaluation",
        || {
            evaluate_function_return_resources(
                &caller_resources_after_requirements,
                escrowed_owners(&transfer),
                &transfer.canonical_borrowed_owners,
                &transfer.borrowed_inputs,
                &transfer_entry_clauses(&transfer),
                &entry_resource_state,
                &output_resource_state,
                &state,
                function,
                transfer.allocation_creator.as_ref(),
                &transfer.consumed_cell_returns,
                assumptions,
                budget,
            )
        },
    )? {
        Ok(resources) => resources,
        Err(RuntimeError::TypeMismatch) => {
            return Ok((
                FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                    "could not evaluate {} return resources",
                    function.name()
                ))),
                obligations,
                None,
            ));
        }
        Err(error) => return Ok((FunctionOutcome::RuntimeError(error), obligations, None)),
    };
    // Return construction consumed each output from one persistent body
    // context and installed that constructed group. Do not consume it again.
    transfer.returned_entry_partition = returned_entry_partition;
    transfer.candidate_output_views = returned_views;
    transfer.produced_borrowing_pieces = produced_borrowing_pieces;
    let (return_resources, return_ledger, return_participant, return_view_bindings, loan_evidence) =
        match recover_candidate_stable_view_resources(
            caller_state,
            &state,
            &transfer,
            return_resources,
            escrow_boundary,
            assumptions,
            assumptions,
            &obligations,
        ) {
            Ok(recovered) => recovered,
            Err(error) => return Ok((FunctionOutcome::RuntimeError(error), obligations, None)),
        };

    match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return allocation obligation check",
        || unreturned_allocation_obligation(&state, &return_resources, function, assumptions),
    ) {
        Ok(Some((allocation, resource))) => {
            return Ok((
                FunctionOutcome::RuntimeError(RuntimeError::LiveAllocationLeak {
                    allocation: Box::new(allocation),
                    resource: resource.map(Box::new),
                }),
                obligations,
                None,
            ));
        }
        Err(error) => return Ok((FunctionOutcome::RuntimeError(error), obligations, None)),
        Ok(None) => {}
    }

    let mut return_state = caller_state.clone();
    // The caller resumes with the callee's memory, made by the steps the
    // callee took: continue the callee's path, which began at the call.
    return_state.set_memory_of(&state);
    return_state.resources = return_resources;
    return_state.loan_ledger = return_ledger;
    return_state.loan_participant = return_participant;
    return_state = return_state.with_loan_view_bindings(return_view_bindings);
    return_state.thread_ledger = state.thread_ledger.clone();
    return_state.mutex_ledger = state.mutex_ledger.clone();
    return_state.mutex_input_reservations = state.mutex_input_reservations.clone();
    return_state.opaque_mutex_acquisitions = state.opaque_mutex_acquisitions.clone();
    return_state.named_mutex_authorities = state.named_mutex_authorities.clone();
    return_state.population_access = state.population_access.clone();
    return_state.observed_population_families = state.observed_population_families;
    return_state.restore_population_creation_after_call(
        caller_state.population_effects.creation.as_ref(),
        state.population_effects.creation.as_ref(),
    );
    return_state = match checked_returned_control_wrappers(
        return_state,
        &output_resources,
        function.contract_interface(),
        assumptions,
    ) {
        Ok(state) => state,
        Err(error) => {
            return Ok((
                FunctionOutcome::RuntimeError(error),
                obligations,
                loan_evidence,
            ));
        }
    };
    return_state.next_local_frame = state.next_local_frame;
    return_state.next_local_lifetime = state.next_local_lifetime;
    let outcome = if exceptional {
        FunctionOutcome::Throw {
            value,
            state: Box::new(return_state),
        }
    } else {
        FunctionOutcome::Return {
            value,
            state: Box::new(return_state),
        }
    };
    Ok((outcome, obligations, loan_evidence))
}

fn without_loan_evidence(
    (outcome, obligations): (FunctionOutcome, Vec<ProofObligation>),
) -> (
    FunctionOutcome,
    Vec<ProofObligation>,
    Option<Arc<CheckedLoanCallEvidence>>,
) {
    (outcome, obligations, None)
}

/// The function-exit rule the verification execution applies to a body
/// outcome, so that a completed proof path ends in the same contract-level
/// state an independent execution would: the contract's resource transfer
/// when a composite needs one at the outcome, the declared-population
/// transition when the contract changes counted quantities, and otherwise
/// the plain outcome. A void fallthrough completes as a return first.
#[cfg(test)]
pub(super) fn contract_exit_outcome(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: StatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    purpose: ResourceTransitionPurpose,
) -> ExecutionResult<
    Result<
        (
            FunctionOutcome,
            Vec<ProofObligation>,
            Option<Arc<CheckedLoanCallEvidence>>,
        ),
        RuntimeError,
    >,
> {
    contract_exit_outcome_with_boundary_transfer(
        caller_state,
        function,
        arguments,
        outcome,
        obligations,
        assumptions,
        budget,
        purpose,
        None,
    )
}

/// A helper body that acquires an authority-bearing control changes that
/// population only under the acquired authority. Its contract must declare
/// exactly that change: at most one produced or consumed member of the
/// population, matched by one checked birth or death. The caller applies the
/// declared change to the population held by the mutex, so a declared
/// consumption that was not spent, or an undeclared birth, is refused here.
pub(crate) fn check_acquired_control_member_effects(
    entry: &ExecutionState,
    exit: &ExecutionState,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(), RuntimeError>> {
    let (Some(before), Some(after)) = (
        entry.population_effects.creation.as_ref(),
        exit.population_effects.creation.as_ref(),
    ) else {
        return Ok(Ok(()));
    };
    let acquired = after.opaque_imports_since(before);
    // The caller lends exactly the declared members' populations. Each must be
    // one whose control this body acquired, never an unrelated anchor.
    let declared_members = if authority_mutex_member_helper_contract(interface) {
        locked_helper_member_effects(interface).unwrap_or_default()
    } else {
        Vec::new()
    };
    for (_, member) in declared_members {
        let fact = match evaluate_function_resource_spec_with_entry(
            entry,
            entry,
            member,
            assumptions,
            budget,
        )? {
            Ok(fact) => fact,
            Err(error) => return Ok(Err(error)),
        };
        let governed = match fact.resource() {
            Resource::Composite { name, arguments } => acquired.iter().any(|description| {
                description.family() == name && description.arguments() == arguments.as_ref()
            }),
            _ => false,
        };
        if !governed {
            return Ok(Err(RuntimeError::FunctionContract(
                "a locked helper's member must belong to the population whose control it acquires"
                    .into(),
            )));
        }
    }
    for description in acquired {
        let mut declared = None;
        for (produce, spec) in interface
            .resource_requires()
            .iter()
            .filter(|spec| spec.role() == ResourceTransferRole::Consume)
            .map(|spec| (false, spec))
            .chain(
                interface
                    .resource_ensures()
                    .iter()
                    .filter(|spec| spec.role() == ResourceTransferRole::Produce)
                    .map(|spec| (true, spec)),
            )
        {
            let ResourceTerm::Composite { name, .. } = spec.term() else {
                continue;
            };
            if name != description.family() {
                continue;
            }
            let fact = match evaluate_function_resource_spec_with_entry(
                entry,
                entry,
                spec,
                assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            let Resource::Composite { arguments, .. } = fact.resource() else {
                continue;
            };
            if arguments.as_ref() != description.arguments()
                || fact.owned_quantity_term().and_then(MachineTerm::as_const) != Some(1)
                || declared.replace(produce).is_some()
            {
                return Ok(Err(RuntimeError::FunctionContract(format!(
                    "a helper that acquires the control of {}(...) supports one produced or consumed member",
                    description.family()
                ))));
            }
        }
        // An unreadable change is refused, never read as unchanged.
        let actual = after.acquired_member_delta(&description);
        let matches = match (declared, actual) {
            (None, Some((_, 0))) => true,
            (Some(produce), Some((actual_produce, 1))) => actual_produce == produce,
            _ => false,
        };
        if !matches {
            let family = description.family();
            return Ok(Err(RuntimeError::FunctionContract(match declared {
                Some(true) => format!(
                    "Requires produces {family}(...) to be created under the acquired authority"
                ),
                Some(false) => format!(
                    "Requires consumes {family}(...) to be spent under the acquired authority"
                ),
                None => format!(
                    "a change to {family}(...) under the acquired authority must be declared by produces or consumes"
                ),
            })));
        }
    }
    Ok(Ok(()))
}

fn contract_exit_outcome_with_boundary_transfer(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: StatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    purpose: ResourceTransitionPurpose,
    checked_transfer: Option<&CheckedBoundaryResourceTransfer>,
) -> ExecutionResult<
    Result<
        (
            FunctionOutcome,
            Vec<ProofObligation>,
            Option<Arc<CheckedLoanCallEvidence>>,
        ),
        RuntimeError,
    >,
> {
    if let Some(receipt) = checked_transfer
        && (purpose != ResourceTransitionPurpose::FunctionBoundary
            || !receipt.matches(caller_state, function, arguments))
    {
        return Ok(Err(RuntimeError::FunctionContract(
            "function boundary resource receipt belongs to another entry".into(),
        )));
    }
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(RuntimeError::FunctionContract(
            "contract exit rule requires symbolic value arguments".to_string(),
        )));
    };
    let outcome = complete_void_fallthrough(function, outcome);
    if let StatementOutcome::Return { state, .. } = &outcome {
        let entry = bind_program_function_arguments(caller_state, function, &argument_values)
            .ok_or(RuntimeError::TypeMismatch);
        match entry.and_then(|entry| {
            check_mutex_helper_body_return(
                &entry,
                state,
                function.contract_interface(),
                assumptions,
                budget,
            )
        }) {
            Ok(()) => {}
            Err(error) => return Ok(Err(error)),
        }
    }
    // Execution and proof rewrites construct this partition as they go.
    // Retain its exact resources, projections, quantities and occurrence IDs;
    // completing a path neither re-admits it nor canonicalizes the ambient
    // frame. The binding mirror is a constant-time shared-root invariant.
    if let StatementOutcome::Return { state, .. } | StatementOutcome::Throw { state, .. } = &outcome
        && !state.loan_bindings_are_consistent()
    {
        return Ok(Err(RuntimeError::FunctionContract(
            "stable-view return resources are not a valid bound context".into(),
        )));
    }
    let callee_state = if let Some(receipt) = checked_transfer {
        receipt.callee.clone()
    } else {
        let Some(callee) = bind_contract_proof_arguments(caller_state, function, &argument_values)
        else {
            return Ok(Err(RuntimeError::TypeMismatch));
        };
        callee
    };
    if authority_consumes_member_contract(function.contract_interface())
        || authority_produces_member_contract(function.contract_interface())
        || authority_final_release_contract(function.contract_interface())
        || authority_exchanges_member_contract(function.contract_interface())
    {
        let StatementOutcome::Return { state, .. } = &outcome else {
            return Ok(Err(RuntimeError::FunctionContract(
                "population helper must return after its member transition".into(),
            )));
        };

        let final_release = match authority_release_retires_control(
            &callee_state,
            state,
            function.contract_interface(),
            checked_transfer.and_then(|receipt| {
                checked_consumed_population_control(
                    function.contract_interface(),
                    &receipt.transfer,
                )
            }),
            assumptions,
            budget,
        )? {
            Ok(retires) => retires,
            Err(error) => return Ok(Err(error)),
        };
        if final_release {
            let interface = function.contract_interface();
            let checked_control = checked_transfer.and_then(|receipt| {
                checked_consumed_population_control(interface, &receipt.transfer)
            });
            let selected = if let Some(control) = checked_control {
                control.clone()
            } else {
                let control =
                    authority_consumed_control(interface).expect("checked final-release control");
                match evaluate_function_resource_spec_with_entry(
                    &callee_state,
                    &callee_state,
                    control,
                    assumptions,
                    budget,
                )? {
                    Ok(control) => control,
                    Err(error) => return Ok(Err(error)),
                }
            };
            let Resource::Composite { name, .. } = selected.resource() else {
                return Ok(Err(RuntimeError::FunctionContract(
                    "final release requires a control resource".into(),
                )));
            };
            let definition = interface
                .composite_resource_definition(name)
                .expect("checked final-release control definition");
            let descriptions = match callee_state.authority_wrapper_descriptions(
                &selected,
                definition,
                assumptions,
            ) {
                Ok(descriptions) => descriptions,
                Err(error) => return Ok(Err(RuntimeError::FunctionContract(error))),
            };
            for description in &descriptions {
                if !state
                    .population_effects
                    .creation
                    .as_ref()
                    .is_some_and(|events| events.checked_empty_population(description))
                {
                    return Ok(Err(RuntimeError::FunctionContract(format!(
                        "Requires consumes authority({}(...))",
                        description.family(),
                    ))));
                }
            }
        }
        let quantity_exchange =
            authority_quantity_exchange_effects(function.contract_interface()).is_some();
        if quantity_exchange
            && let Err(error) = check_quantity_exchange_at_return(
                &callee_state,
                state,
                function.contract_interface(),
                assumptions,
                budget,
            )?
        {
            return Ok(Err(error));
        }
        for (produce, member_spec) in
            authority_checked_member_effects(function.contract_interface())
                .into_iter()
                .filter(|_| !quantity_exchange)
        {
            let checked_member = if !produce {
                checked_transfer.and_then(|receipt| {
                    let index = function
                        .resource_requires()
                        .iter()
                        .position(|spec| std::ptr::eq(spec, member_spec))?;
                    receipt
                        .transfer
                        .consumed_inputs
                        .iter()
                        .find(|checked| checked.section_index == Some(index))
                        .map(|checked| checked.fact.clone())
                })
            } else {
                None
            };
            let expected_member = if let Some(member) = checked_member {
                member
            } else {
                match evaluate_function_resource_spec_with_entry(
                    &callee_state,
                    &callee_state,
                    member_spec,
                    assumptions,
                    budget,
                )? {
                    Ok(fact) => fact,
                    Err(error) => return Ok(Err(error)),
                }
            };
            let expected_quantity = expected_member.owned_quantity_term().cloned();
            let expected_description = match expected_member.resource() {
                Resource::Composite { name, arguments } => Some(ResourceDescription::new(
                    name.clone(),
                    arguments.clone(),
                    ResourceFieldSchema::new(vec![]).expect("empty schema"),
                )),
                _ => None,
            };
            let exchanged = callee_state
                .population_effects
                .creation
                .as_ref()
                .zip(state.population_effects.creation.as_ref())
                .is_some_and(|(before, after)| {
                    if final_release {
                        expected_description.as_ref().is_some_and(|description| {
                            let consumed = if expected_quantity.as_ref().and_then(|q| q.as_const())
                                == Some(1)
                            {
                                after.spent_imported_member_since(before, description)
                            } else {
                                expected_quantity.as_ref().is_some_and(|expected| {
                                    after
                                        .imported_member_delta_since_entry(description)
                                        .is_some_and(|(produce, actual)| {
                                            (!produce
                                                || crate::kernel::quantity_condition_holds(
                                                    assumptions,
                                                    ConditionTerm::Compare {
                                                        format: MachineIntegerType::Int32,
                                                        relation: CompareRelation::Equal,
                                                        left: Box::new(actual.clone()),
                                                        right: Box::new(MachineTerm::constant(0)),
                                                    },
                                                ))
                                                && crate::kernel::quantity_condition_holds(
                                                    assumptions,
                                                    ConditionTerm::Compare {
                                                        format: MachineIntegerType::Int32,
                                                        relation: CompareRelation::Equal,
                                                        left: Box::new(actual),
                                                        right: Box::new(expected.clone()),
                                                    },
                                                )
                                        })
                                })
                            };
                            consumed && after.retired_imported_authority_since(before, description)
                        })
                    } else if let (Some(description), Some(expected_quantity)) =
                        (expected_description.as_ref(), expected_quantity.as_ref())
                    {
                        after
                            .imported_member_delta_since_entry(description)
                            .is_some_and(|(actual_produce, actual_quantity)| {
                                (actual_produce == produce
                                    || crate::kernel::quantity_condition_holds(
                                        assumptions,
                                        ConditionTerm::Compare {
                                            format: MachineIntegerType::Int32,
                                            relation: CompareRelation::Equal,
                                            left: Box::new(actual_quantity.clone()),
                                            right: Box::new(MachineTerm::constant(0)),
                                        },
                                    ))
                                    && crate::kernel::quantity_condition_holds(
                                        assumptions,
                                        ConditionTerm::Compare {
                                            format: MachineIntegerType::Int32,
                                            relation: CompareRelation::Equal,
                                            left: Box::new(actual_quantity),
                                            right: Box::new(expected_quantity.clone()),
                                        },
                                    )
                            })
                    } else {
                        false
                    }
                });
            if !exchanged {
                let requirement = population_member_requirement(member_spec);
                return Ok(Err(RuntimeError::FunctionContract(format!(
                    "Requires {} {requirement}",
                    if produce { "produces" } else { "consumes" }
                ))));
            }
        }
    }
    if let StatementOutcome::Return { state, .. } = &outcome
        && let Err(error) = check_acquired_control_member_effects(
            &callee_state,
            state,
            function.contract_interface(),
            assumptions,
            budget,
        )?
    {
        return Ok(Err(error));
    }
    let fallback_transfer;
    let transfer = if let Some(receipt) = checked_transfer {
        &receipt.transfer
    } else {
        fallback_transfer = match prepare_function_resource_transfer(
            caller_state,
            &callee_state,
            function,
            assumptions,
            budget,
            true,
            purpose,
        )? {
            Ok(transfer) => transfer,
            Err(error) => return Ok(Err(error)),
        };
        &fallback_transfer
    };
    // A quantity change that reaches a population
    // crosses the checked resource transfer; any other contract keeps the
    // ordinary exit, which returns the body's own resources.
    if function_needs_outcome_resource_transfer(function)
        || function_changes_declared_resource_quantities(function)
            && contract_reaches_population(function.contract_interface())
    {
        function_outcome_from_body_with_resource_transfer(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            transfer,
            &argument_values,
            true,
            budget,
        )
        .map(Ok)
    } else if function_changes_declared_resource_quantities(function) {
        function_outcome_from_body_changing_quantities(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
        )
        .map(|outcome| Ok(without_loan_evidence(outcome)))
    } else {
        Ok(Ok(without_loan_evidence(function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        ))))
    }
}

pub(crate) fn is_deferred_conditional_resource_effect_error(error: &RuntimeError) -> bool {
    matches!(
        error,
        RuntimeError::FunctionContract(message)
            if message == "could not select a conditional resource effect: its pre-state condition is not proven"
                || message == "function body does not yet establish its joint returned resource units"
    )
}

/// Completes a checked body path at the function boundary. An undecided
/// conditional produced effect is not a successful transition. It produces a
/// body-only path only with the exact boundary error retained alongside an
/// explicit deferred marker; certification must resolve that marker under an
/// exhaustive contract case before using the path post-state.
pub(crate) fn checked_contract_exit_outcome_with_boundary_transfer(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: StatementOutcome,
    body_outcome: FunctionOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    purpose: ResourceTransitionPurpose,
    checked_transfer: Option<&CheckedBoundaryResourceTransfer>,
) -> ExecutionResult<
    Result<
        (
            FunctionOutcome,
            Vec<ProofObligation>,
            Option<Arc<CheckedLoanCallEvidence>>,
            bool,
            Option<RuntimeError>,
        ),
        RuntimeError,
    >,
> {
    let deferred_obligations = obligations.clone();
    match contract_exit_outcome_with_boundary_transfer(
        caller_state,
        function,
        arguments,
        outcome,
        obligations,
        assumptions,
        budget,
        purpose,
        checked_transfer,
    )? {
        Ok((outcome, obligations, loan_evidence)) => {
            if let FunctionOutcome::RuntimeError(error) = &outcome
                && is_deferred_conditional_resource_effect_error(error)
            {
                return Ok(Ok((
                    body_outcome,
                    deferred_obligations,
                    None,
                    true,
                    Some(error.clone()),
                )));
            }
            Ok(Ok((outcome, obligations, loan_evidence, false, None)))
        }
        Err(error) if is_deferred_conditional_resource_effect_error(&error) => Ok(Ok((
            body_outcome,
            deferred_obligations,
            None,
            true,
            Some(error),
        ))),
        Err(error) => Ok(Err(error)),
    }
}

/// Resolves a body-only path with deferred conditional or returned-resource obligations.
/// The caller supplies checked resource evidence and contract-case assumptions; this helper
/// reruns only the boundary transition, never the C body or its proof trace.
pub(crate) fn resolve_deferred_contract_exit(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    body_outcome: &FunctionOutcome,
    checked_transfer: Option<&CheckedBoundaryResourceTransfer>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<FunctionOutcome, RuntimeError>> {
    let statement_outcome = match body_outcome {
        FunctionOutcome::Return { value, state } => StatementOutcome::Return {
            value: value.clone(),
            state: state.clone(),
        },
        FunctionOutcome::Throw { value, state } => StatementOutcome::Throw {
            value: value.clone(),
            state: state.clone(),
        },
        FunctionOutcome::VerificationDiverges => {
            return Ok(Ok(FunctionOutcome::VerificationDiverges));
        }
        FunctionOutcome::UndefinedBehavior(error) => {
            return Ok(Ok(FunctionOutcome::UndefinedBehavior(error.clone())));
        }
        FunctionOutcome::RuntimeError(error) => return Ok(Err(error.clone())),
    };
    match contract_exit_outcome_with_boundary_transfer(
        caller_state,
        function,
        arguments,
        statement_outcome,
        Vec::new(),
        assumptions,
        budget,
        ResourceTransitionPurpose::FunctionBoundary,
        checked_transfer,
    )? {
        Ok((outcome, _, _)) => Ok(Ok(outcome)),
        Err(error) => Ok(Err(error)),
    }
}

pub(super) fn apply_verified_contract_resource_transition(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    outcome: FunctionOutcome,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(FunctionOutcome, Vec<ProofObligation>), RuntimeError>> {
    // As at call sites, the authority helper rules govern only contracts
    // that reach a population; an ordinary contract's exit transition folds
    // its produced composites by their definitions.
    if contract_reaches_population(function.contract_interface())
        && !authority_supports_resource_contract(function.contract_interface())
    {
        return Ok(Err(RuntimeError::FunctionContract(
            "helper contract needs conserved owns resources, a checked consumes/produces effect, or a supported unit exchange".into(),
        )));
    }
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            ProgramExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(RuntimeError::FunctionContract(
            "contract resource transition requires symbolic value arguments".to_string(),
        )));
    };
    let Some(callee_state) =
        bind_contract_proof_arguments(caller_state, function, &argument_values)
    else {
        return Ok(Err(RuntimeError::TypeMismatch));
    };
    let transfer = match prepare_function_resource_transfer(
        caller_state,
        &callee_state,
        function,
        assumptions,
        budget,
        true,
        ResourceTransitionPurpose::FunctionBoundary,
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    let statement_outcome = match outcome {
        FunctionOutcome::Return { value, state } => StatementOutcome::Return { value, state },
        FunctionOutcome::Throw { value, state } => StatementOutcome::Throw { value, state },
        FunctionOutcome::VerificationDiverges => {
            return Ok(Ok((FunctionOutcome::VerificationDiverges, Vec::new())));
        }
        FunctionOutcome::UndefinedBehavior(error) => {
            return Ok(Ok((FunctionOutcome::UndefinedBehavior(error), Vec::new())));
        }
        FunctionOutcome::RuntimeError(error) => return Ok(Err(error)),
    };
    let (outcome, obligations, _loan_evidence) = crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "contract resource outcome reconstruction",
        || {
            function_outcome_from_body_with_resource_transfer(
                caller_state,
                function,
                statement_outcome,
                Vec::new(),
                assumptions,
                &transfer,
                &argument_values,
                false,
                budget,
            )
        },
    )?;
    match outcome {
        FunctionOutcome::RuntimeError(error) => Ok(Err(error)),
        outcome => Ok(Ok((outcome, obligations))),
    }
}

pub(super) fn function_outcome_from_body(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    outcome: StatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    return_resources: Option<&ResourceContext>,
) -> (FunctionOutcome, Vec<ProofObligation>) {
    match outcome {
        StatementOutcome::Return { value, mut state } => {
            if let Some(error) =
                construction_return::complete_parameter(&state, function.contract_interface())
            {
                return (FunctionOutcome::RuntimeError(error), obligations);
            }
            if let Some(undefined_behavior) =
                freed_pointer_return_conversion(&state, function, &value, assumptions)
            {
                return (
                    FunctionOutcome::UndefinedBehavior(undefined_behavior),
                    obligations,
                );
            }
            if let Some(refusal) =
                incompatible_pointer_return(&state, function, &value, assumptions)
            {
                return (FunctionOutcome::RuntimeError(refusal), obligations);
            }
            let Some(value) = coerce_retained_function_return_value(
                value,
                function,
                &mut obligations,
                assumptions,
            ) else {
                return (
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                        "{} {RETURN_TYPE_MISMATCH}",
                        function.name()
                    ))),
                    obligations,
                );
            };
            let value = if function.return_aggregate_layout().is_some() {
                match complete_aggregate_return(&mut state, function, value.into_native()) {
                    Ok(value) => value.into(),
                    Err(AggregateReturnRefusal::UninitializedRead) => {
                        return (
                            FunctionOutcome::UndefinedBehavior(
                                UndefinedBehavior::UninitializedRead,
                            ),
                            obligations,
                        );
                    }
                    Err(AggregateReturnRefusal::InvalidValue) => {
                        return (
                            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                                "{} returned an invalid struct value",
                                function.name()
                            ))),
                            obligations,
                        );
                    }
                }
            } else {
                value
            };

            let original_creation = caller_state.population_effects.creation.clone();
            let mut caller_state = caller_state.clone();
            let retired_memory = if function.has_inline_body() {
                end_inline_frame_automatic_lifetimes(&state)
            } else {
                end_function_body_automatic_lifetimes(
                    &state,
                    function,
                    caller_state.memory(),
                    value.native_payload(),
                )
            };
            let retired_creation_blocks = match retired_memory {
                Ok(memory) => {
                    let blocks = retired_automatistorage_creation_blocks(&state, &memory);
                    caller_state.set_memory_continuing(&state, memory);
                    blocks
                }
                Err(error) => return (FunctionOutcome::RuntimeError(error), obligations),
            };
            let retired_creation =
                match state.retired_population_creation_for_blocks(&retired_creation_blocks) {
                    Ok(creation) => creation,
                    Err(error) => return (FunctionOutcome::RuntimeError(error), obligations),
                };
            if function.has_inline_body() {
                // Inline bodies execute with a parameter-only local
                // environment, so pointer stores into caller locals cannot
                // synchronize their named bindings during body execution.
                // Reconcile those bindings from the shared caller memory
                // before the caller resumes evaluating its next statement.
                let memory = caller_state.memory.clone();
                caller_state.sync_scalar_locals_from_memory(&memory);
            }
            // The body ran on its entry ledger and may have projected viewed
            // composite children into it (or, for an inline body, made calls
            // on the caller's ledger); the return state carries the body's
            // ledger. A modular call's recovery replaces it afterwards.
            caller_state = caller_state
                .with_loan_ledger(state.loan_ledger().cloned())
                .with_loan_participant(state.loan_participant());
            caller_state.thread_ledger = state.thread_ledger.clone();
            caller_state.mutex_ledger = state.mutex_ledger.clone();
            caller_state.mutex_input_reservations = state.mutex_input_reservations.clone();
            caller_state.opaque_mutex_acquisitions = state.opaque_mutex_acquisitions.clone();
            caller_state.named_mutex_authorities = state.named_mutex_authorities.clone();
            if return_resources.is_none() {
                caller_state.instance_field_scope = state.instance_field_scope;
            }
            caller_state = caller_state
                .with_resource_context(return_resources.cloned().unwrap_or(state.resources));
            for block in &retired_creation_blocks {
                let Some(bytes) = state.memory.block_size(block).cloned() else {
                    continue;
                };
                crate::kernel::eval::retire_automatic_storage_owner(
                    &mut caller_state,
                    &MemoryRange::new_with_element_width(
                        Address {
                            base: block.clone(),
                            offset: AddressOffset::Constant(0),
                        },
                        0.into(),
                        bytes,
                        1,
                    ),
                );
            }
            caller_state.population_access = state.population_access.clone();
            caller_state.observed_population_families = state.observed_population_families;

            caller_state.restore_population_creation_after_call(
                original_creation.as_ref(),
                retired_creation.as_ref(),
            );
            caller_state.next_local_frame = state.next_local_frame;
            caller_state.next_local_lifetime = state.next_local_lifetime;
            (
                FunctionOutcome::Return {
                    value,
                    state: Box::new(caller_state),
                },
                obligations,
            )
        }
        StatementOutcome::Throw { value, state } => {
            if !function.exceptional_signature().permits(&value.native()) {
                return (
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                        "{} produced an exceptional outcome not declared by its signature",
                        function.name()
                    ))),
                    obligations,
                );
            }
            let original_creation = caller_state.population_effects.creation.clone();
            let mut caller_state = caller_state.clone();
            let retired_memory = if function.has_inline_body() {
                end_inline_frame_automatic_lifetimes(&state)
            } else {
                end_function_body_automatic_lifetimes(&state, function, caller_state.memory(), None)
            };
            let retired_creation_blocks = match retired_memory {
                Ok(memory) => {
                    let blocks = retired_automatistorage_creation_blocks(&state, &memory);
                    caller_state.set_memory_continuing(&state, memory);
                    blocks
                }
                Err(error) => return (FunctionOutcome::RuntimeError(error), obligations),
            };
            let retired_creation =
                match state.retired_population_creation_for_blocks(&retired_creation_blocks) {
                    Ok(creation) => creation,
                    Err(error) => return (FunctionOutcome::RuntimeError(error), obligations),
                };
            caller_state.thread_ledger = state.thread_ledger.clone();
            caller_state.mutex_ledger = state.mutex_ledger.clone();
            caller_state.mutex_input_reservations = state.mutex_input_reservations.clone();
            caller_state.opaque_mutex_acquisitions = state.opaque_mutex_acquisitions.clone();
            caller_state.named_mutex_authorities = state.named_mutex_authorities.clone();
            if function.has_inline_body() {
                let memory = caller_state.memory.clone();
                caller_state.sync_scalar_locals_from_memory(&memory);
            }
            caller_state = caller_state
                .with_loan_ledger(state.loan_ledger().cloned())
                .with_loan_participant(state.loan_participant());
            if return_resources.is_none() {
                caller_state.instance_field_scope = state.instance_field_scope;
            }
            caller_state = caller_state
                .with_resource_context(return_resources.cloned().unwrap_or(state.resources));
            for block in &retired_creation_blocks {
                let Some(bytes) = state.memory.block_size(block).cloned() else {
                    continue;
                };
                crate::kernel::eval::retire_automatic_storage_owner(
                    &mut caller_state,
                    &MemoryRange::new_with_element_width(
                        Address {
                            base: block.clone(),
                            offset: AddressOffset::Constant(0),
                        },
                        0.into(),
                        bytes,
                        1,
                    ),
                );
            }
            caller_state.population_access = state.population_access.clone();
            caller_state.observed_population_families = state.observed_population_families;

            caller_state.restore_population_creation_after_call(
                original_creation.as_ref(),
                retired_creation.as_ref(),
            );
            caller_state.next_local_frame = state.next_local_frame;
            caller_state.next_local_lifetime = state.next_local_lifetime;
            (
                FunctionOutcome::Throw {
                    value,
                    state: Box::new(caller_state),
                },
                obligations,
            )
        }
        StatementOutcome::Normal(_) => (
            FunctionOutcome::RuntimeError(RuntimeError::MissingReturn),
            obligations,
        ),
        StatementOutcome::LoopTestFalse(_)
        | StatementOutcome::Break(_)
        | StatementOutcome::Continue(_)
        | StatementOutcome::Jump { .. } => (
            FunctionOutcome::RuntimeError(RuntimeError::MissingReturn),
            obligations,
        ),
        StatementOutcome::VerificationDiverges => {
            (FunctionOutcome::VerificationDiverges, obligations)
        }
        StatementOutcome::UndefinedBehavior(undefined_behavior) => (
            FunctionOutcome::UndefinedBehavior(undefined_behavior),
            obligations,
        ),
        StatementOutcome::RuntimeError(error) => {
            (FunctionOutcome::RuntimeError(error), obligations)
        }
    }
}

fn exceptional_outcome_declaration_error(
    function: &ProgramFunction,
    outcome: &StatementOutcome,
) -> Option<RuntimeError> {
    let StatementOutcome::Throw { value, .. } = outcome else {
        return None;
    };
    (!function.exceptional_signature().permits(&value.native())).then(|| {
        RuntimeError::FunctionContract(format!(
            "{} produced an exceptional outcome not declared by its signature",
            function.name()
        ))
    })
}

impl From<u32> for MachineTerm {
    fn from(value: u32) -> Self {
        Self::constant(value)
    }
}

impl From<bool> for ConditionTerm {
    fn from(value: bool) -> Self {
        Self::Constant(value)
    }
}

#[cfg(test)]
mod automatic_frame_loan_tests;

#[cfg(test)]
mod mutex_automatic_frame_tests;

#[cfg(test)]
mod population_creation_frame_tests;

#[cfg(test)]
mod provisional_ensure_obligation_tests;

mod call_initialization;
#[cfg(test)]
mod verified_call_initialization_tests;
pub(crate) use call_initialization::memory_range_is_initialized;

#[cfg(test)]
mod integer_parameter_read_tests;

#[cfg(test)]
mod stable_view_call_tests;

#[cfg(test)]
mod retained_aggregate_resource_values_tests;

#[cfg(test)]
mod resource_reference_tests;

#[cfg(test)]
mod inline_loop_boundary_tests;

#[cfg(test)]
mod composite_pointer_body_fact_tests;

#[cfg(test)]
mod wide_range_reader_tests;

#[cfg(test)]
mod wide_matched_range_reader_tests;

#[cfg(test)]
mod storage_summary_footprint_tests;

#[cfg(test)]
mod iterated_operand_storage_tests;

mod legacy_search;
