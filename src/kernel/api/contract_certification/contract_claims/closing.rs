//! Resource and write-footprint obligations owned by the outcome proof.

use super::*;
use crate::kernel::proof::{
    ContractClosingGoal, ContractClosingGoals, OutcomeClaimGoals, OutcomeIdentity,
    OutcomeProofCore, PureFactStore,
};
use std::sync::{Arc, OnceLock};

/// Shared declaration input of the closing goals, prepared once per proof.
pub(crate) struct ContractClosingContext {
    function: ProgramFunction,
    caller: ExecutionState,
    arguments: Vec<ProgramExpression>,
    entry_assumptions: PureFactContext,
    checked_entry: Option<Arc<crate::kernel::functions::CheckedBoundaryResourceTransfer>>,
    resource_claims: Vec<FunctionContractClaim>,
    resource_keys: Arc<BTreeSet<FunctionContractClaimKey>>,
    complete_boundary: bool,
    completion_keys: Arc<[FunctionContractClaimKey]>,
    effect_claims: Vec<FunctionContractClaim>,
    retained_entry: Option<Arc<PreparedContractEntryCases>>,
    entry: OnceLock<Result<RetainedClosingFootprint, ContractClosingRefusal>>,
    // Both bindings use the exact caller snapshot captured at completion.
    // A retry still checks the current outcome and its current assumptions.
    transition_caller: ExecutionState,
    transition_entry: OnceLock<Option<crate::kernel::functions::ReturnResourceEntry>>,
}

impl ContractClosingContext {
    #[cfg(test)]
    pub(crate) fn new(execution: &CheckedFunctionExecution) -> Arc<Self> {
        Self::for_resource_prefix(
            execution,
            execution.function.resource_ensures().len(),
            execution.allocation_entry_state(),
        )
    }

    /// A clause-specific proof owes its jointly returned prefix, not clauses
    /// whose separate proofs have not run. The final prefix closes the boundary.
    pub(crate) fn for_resource_prefix(
        execution: &CheckedFunctionExecution,
        resource_prefix: usize,
        transition_caller: &ExecutionState,
    ) -> Arc<Self> {
        crate::instrumentation::record_deterministic_work(execution.arguments.len() + 1);
        let complete_boundary = resource_prefix >= execution.function.resource_ensures().len();
        let mut resource_claims = Vec::new();
        let mut resource_keys = BTreeSet::new();
        let mut effect_claims = Vec::new();
        let mut completion_keys = Vec::new();
        // Build the selected closing obligations and their completion outputs
        // together from the explicit contract declaration.
        for claim in execution.function.contract_claims() {
            crate::instrumentation::record_deterministic_work(1);
            match claim.target() {
                FunctionContractClaimTarget::EnsureResource(index) if *index < resource_prefix => {
                    resource_claims.push(claim.clone());
                    resource_keys.insert(claim.key().clone());
                    completion_keys.push(claim.key().clone());
                }
                FunctionContractClaimTarget::Effect => {
                    effect_claims.push(claim.clone());
                    completion_keys.push(claim.key().clone());
                }
                FunctionContractClaimTarget::BodySafety if complete_boundary => {
                    completion_keys.push(claim.key().clone());
                }
                _ => {}
            }
        }
        Arc::new(Self {
            completion_keys: completion_keys.into(),
            function: execution.function.clone(),
            caller: execution.allocation_entry_state().clone(),
            arguments: execution.function_arguments().to_vec(),
            entry_assumptions: execution.assumptions.clone(),
            checked_entry: execution.boundary_transfer.clone(),
            effect_claims,
            resource_claims,
            resource_keys: Arc::new(resource_keys),
            complete_boundary,
            retained_entry: execution
                .entry_authority
                .as_ref()
                .map(|authority| authority.cases().clone()),
            entry: OnceLock::new(),
            transition_caller: transition_caller.clone(),
            transition_entry: OnceLock::new(),
        })
    }

    pub(crate) fn open_claims(
        &self,
        claims: impl IntoIterator<
            Item = (
                FunctionContractClaimKey,
                Option<FunctionContractClaimTarget>,
            ),
        >,
        is_exceptional: bool,
    ) -> OutcomeClaimGoals {
        OutcomeClaimGoals::open_with_borrowed_resources(
            claims,
            is_exceptional,
            self.function.resource_ensures(),
        )
    }

    pub(crate) fn open(
        self: &Arc<Self>,
        path_index: usize,
        outcome: &OutcomeProofCore,
    ) -> ContractExitObligations {
        ContractExitObligations {
            context: self.clone(),
            path_index,
            outcome: outcome.identity.clone(),
            goals: ContractClosingGoals::open(),
            checked_transition: None,
            effects: None,
        }
    }

    fn entry(&self) -> Result<&RetainedClosingFootprint, ContractClosingRefusal> {
        if let Some(entry) = &self.retained_entry {
            return Ok(entry
                .closing_footprint
                .get()
                .expect("opening the entry prepared its footprint"));
        }
        self.entry
            .get_or_init(|| {
                let state = match &self.checked_entry {
                    Some(entry) => entry.callee_entry().clone(),
                    None => {
                        program_function_entry_state(&self.caller, &self.function, &self.arguments)
                            .ok_or_else(|| {
                                ContractClosingRefusal::Internal(
                                    "could not bind the contract entry".into(),
                                )
                            })?
                    }
                };
                let mut budget = ExecutionBudget::beside_live_state();
                let resources = if self.function.resource_derived_mutable_frame() {
                    let checked = if let Some(entry) = &self.checked_entry {
                        entry.checked_entry_clauses()
                    } else {
                        let (_, checked) = evaluate_function_resource_context_with_metadata(
                            &state,
                            self.function.resource_requires(),
                            self.function.composite_resource_definitions(),
                            &self.entry_assumptions.clone().assume_entry_clause_spans(),
                            &mut budget,
                        )
                        .map_err(ContractClosingRefusal::from_stop)?
                        .map_err(ContractClosingRefusal::Runtime)?;
                        checked
                    };
                    Some(checked.into())
                } else {
                    None
                };
                let projection = project_contract_memory_effects(
                    &state,
                    self.function.contract_interface(),
                    resources.as_deref(),
                    &self.entry_assumptions,
                    &mut budget,
                )
                .map_err(ContractClosingRefusal::from_stop)?
                .map_err(ContractClosingRefusal::Incomplete)?;
                Ok(RetainedClosingFootprint {
                    state,
                    resources,
                    entry_assumptions: self.entry_assumptions.clone(),
                    projection: OnceLock::from(Ok(projection)),
                })
            })
            .as_ref()
            .map_err(Clone::clone)
    }
}

/// The contract closer opens these goals before post-execution tactics.
/// Checked resource transitions retain evidence; ordinary proof operations
/// discharge returned resources, allocation lifetime, and write footprints.
#[derive(Clone)]
pub(crate) struct ContractExitObligations {
    context: Arc<ContractClosingContext>,
    path_index: usize,
    outcome: OutcomeIdentity,
    goals: ContractClosingGoals,
    checked_transition: Option<CheckedResourceTransition>,
    effects: Option<Arc<PreparedEffectGoals>>,
}

/// Evidence supplied by the checked resource producer, not a closed goal.
#[derive(Clone, Copy)]
struct CheckedResourceTransition;

struct PreparedEffectGoals {
    base: PureFactStore,
    paths: Vec<CertifiedFunctionClaimPath>,
}

/// Evidence consumed by registration, never a request to check a path again.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ClosedContractExit {
    path_index: usize,
    origin: Theorem,
    resources: Arc<BTreeSet<FunctionContractClaimKey>>,
    complete_boundary: bool,
}

impl ClosedContractExit {
    pub(crate) fn completes_boundary(&self) -> bool {
        self.complete_boundary
    }

    #[cfg(test)]
    pub(in crate::kernel) fn matches_path(&self, path: &SymbolicExecutionPath) -> bool {
        Arc::ptr_eq(&self.origin.proposition, &path.theorem.proposition)
    }
}

#[derive(Clone, Debug)]
pub(crate) enum ContractClosingRefusal {
    /// The verifier supplied inconsistent state for this closing operation.
    Internal(String),
    Incomplete(String),
    InvalidContract(String),
    UndefinedBehavior(crate::kernel::UndefinedBehavior),
    Claim(FunctionContractClaimKey),
    Runtime(RuntimeError),
    Write(Address),
    Range(MemoryRange),
    Storage(Vec<crate::kernel::functions::StorageWriteOutsideFootprint>),
    #[cfg(test)]
    Pending(ContractClosingGoal),
}

impl ContractClosingRefusal {
    pub(in crate::kernel) fn from_stop(stop: ExecutionLimit) -> Self {
        use ExecutionLimit::*;
        match stop {
            Deadline
            | ExpressionSteps
            | StatementSteps
            | FunctionCalls
            | LoopUnrolls
            | KernelVariables { .. }
            | MatchBinderVariables { .. } => {
                Self::Internal(format!("checking the contract return stopped at {stop}"))
            }
            ExecutionIdentityBesideLiveState => Self::Internal(stop.describe()),
            _ => Self::Incomplete(format!("could not check the contract return: {stop}")),
        }
    }
}

impl ContractExitObligations {
    pub(in crate::kernel) fn completed_claim_keys(
        &self,
    ) -> impl Iterator<Item = &FunctionContractClaimKey> {
        self.context.completion_keys.iter()
    }

    pub(in crate::kernel) fn completes_whole_boundary(&self) -> bool {
        self.context.complete_boundary
    }

    #[cfg(test)]
    pub(in crate::kernel) fn fixture_close_goal(&self, kind: ContractClosingGoal) -> Self {
        Self {
            goals: self.goals.close(kind),
            ..self.clone()
        }
    }

    pub(crate) fn first_open_goal(&self) -> Option<ContractClosingGoal> {
        self.goals.first_open()
    }

    pub(crate) fn after_resource_change(&self) -> Self {
        Self {
            goals: self
                .goals
                .reopen(ContractClosingGoal::ReturnedResources)
                .reopen(ContractClosingGoal::AllocationLifetime),
            checked_transition: None,
            effects: None,
            ..self.clone()
        }
    }

    /// Retain the checked producer's resource/lifetime evidence. Ordinary
    /// closing operations still discharge the corresponding goals, including
    /// any retained boundary refusal the resource producer does not cover.
    pub(crate) fn apply_resource_transition(
        &self,
        outcome: FunctionOutcome,
        assumptions: &PureFactContext,
    ) -> Result<(Self, FunctionOutcome), String> {
        let caller_state = &self.context.transition_caller;
        let function = &self.context.function;
        let arguments = &self.context.arguments;
        // The transition replaces the body's resources with the ones the
        // contract returns, so it publishes them, a produced composite included.
        // Publish only what the body establishes by the rule certification
        // applies, which assembles a composite from pieces only when its body
        // facts hold on this path.
        if matches!(outcome, FunctionOutcome::Return { .. })
            && !self
                .context
                .transition_entry
                .get_or_init(|| {
                    crate::kernel::functions::ReturnResourceEntry::bind(
                        caller_state,
                        function,
                        arguments,
                    )
                })
                .as_ref()
                .is_some_and(|entry| {
                    crate::kernel::functions::function_return_resources_definitionally_established(
                        caller_state,
                        function,
                        arguments,
                        &outcome,
                        assumptions,
                        Some(entry),
                    )
                })
        {
            return Err(
                "the body outcome does not establish the contract's returned resources".into(),
            );
        }
        let (outcome, obligations) = apply_program_function_contract_resource_transition(
            caller_state,
            function,
            arguments,
            outcome,
            assumptions,
        )?;
        if let Some(obligation) = obligations.iter().find(|obligation| {
            !crate::kernel::PureFactContext::settles_exactly(assumptions, obligation.proposition())
        }) {
            return Err(format!(
                "unproved contract resource obligation: {}",
                obligation.context().unwrap_or("resource transition"),
            ));
        }
        if let FunctionOutcome::RuntimeError(error) = &outcome {
            return Err(error.kernel_summary());
        }
        Ok((
            Self {
                checked_transition: Some(CheckedResourceTransition),
                ..self.clone()
            },
            outcome,
        ))
    }

    /// The ordinary closer reads its own outcome's producer publication,
    /// without accepting a separately assembled specification.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prove_goal(
        &self,
        kind: ContractClosingGoal,
        execution: &CheckedFunctionExecution,
        path: &SymbolicExecutionPath,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &PureFactStore,
    ) -> Result<Self, ContractClosingRefusal> {
        let publication = outcome
            .publication
            .as_ref()
            .expect("an ordinary checked outcome retains its producer publication");
        self.prove_goal_with_specification(
            kind,
            execution,
            path,
            publication.specification(),
            outcome,
            claims,
            facts,
        )
    }

    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn prove_goal_for_specification(
        &self,
        kind: ContractClosingGoal,
        execution: &CheckedFunctionExecution,
        path: &SymbolicExecutionPath,
        specification: &FunctionSpecification,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &PureFactStore,
    ) -> Result<Self, ContractClosingRefusal> {
        self.prove_goal_with_specification(
            kind,
            execution,
            path,
            specification,
            outcome,
            claims,
            facts,
        )
    }

    /// One primitive proof of the currently selected closing obligation.
    fn prove_goal_with_specification(
        &self,
        kind: ContractClosingGoal,
        execution: &CheckedFunctionExecution,
        path: &SymbolicExecutionPath,
        specification: &FunctionSpecification,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &PureFactStore,
    ) -> Result<Self, ContractClosingRefusal> {
        if !self.outcome.same_as(&outcome.identity) {
            return Err(ContractClosingRefusal::Internal(
                "closing obligations belong to another outcome".into(),
            ));
        }
        if self.first_open_goal() != Some(kind) {
            return Err(ContractClosingRefusal::Internal(
                "the selected closing goal is not open".into(),
            ));
        }
        let input_units = match kind {
            ContractClosingGoal::ReturnedResources => {
                self.context.resource_claims.len() + path.obligations().len() + 1
            }
            ContractClosingGoal::AllocationLifetime => self.context.resource_claims.len() + 1,
            ContractClosingGoal::WriteFootprint => {
                path.effect_facts.len() + self.context.effect_claims.len() + 1
            }
        };
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("contract closing", input_units);
        let mut proved = self.clone();
        match kind {
            ContractClosingGoal::ReturnedResources => {
                if !outcome.is_exceptional
                    && let FunctionOutcome::RuntimeError(error) = specification.outcome()
                    && ((self.context.complete_boundary && self.checked_transition.is_none())
                        || !crate::kernel::functions::is_deferred_conditional_resource_effect_error(
                            error,
                        ))
                {
                    return Err(ContractClosingRefusal::Runtime(error.clone()));
                }
                let receipts_closed = !self.context.complete_boundary
                    || !execution
                        .deferred_contract_exits
                        .get(self.path_index)
                        .copied()
                        .unwrap_or(false);
                let resources_closed = self.checked_transition.is_some()
                    || receipts_closed
                        && matches!(
                            specification.outcome(),
                            FunctionOutcome::Return { .. } | FunctionOutcome::Throw { .. }
                        )
                        && self.resource_receipts_jointly_available(
                            outcome,
                            claims,
                            facts.assumptions(),
                        );
                let paths = self.prove_resource_goals(
                    execution,
                    path,
                    outcome,
                    claims,
                    facts,
                    !resources_closed,
                )?;
                if !self.context.effect_claims.is_empty() {
                    proved.effects = Some(Arc::new(PreparedEffectGoals {
                        base: facts.clone(),
                        paths,
                    }));
                }
            }
            ContractClosingGoal::AllocationLifetime => {
                if !outcome.is_exceptional
                    && self.context.complete_boundary
                    && self.checked_transition.is_none()
                {
                    self.prove_allocation_lifetime(outcome, claims, facts)?;
                }
            }
            ContractClosingGoal::WriteFootprint => {
                if !self.context.effect_claims.is_empty() {
                    let effects = self
                        .effects
                        .as_ref()
                        .ok_or(ContractClosingRefusal::Internal(
                            "the resource goal has not prepared the effect input".into(),
                        ))?;
                    let delta = facts.introduced_since(&effects.base).ok_or(
                        ContractClosingRefusal::Internal(
                            "the effect goal belongs to another proof context".into(),
                        ),
                    )?;
                    for prepared in &effects.paths {
                        let assumptions =
                            assumptions_with_propositions(&prepared.assumptions, &delta);
                        check_effect_on_prepared_path(
                            &self.context.function,
                            prepared,
                            &assumptions,
                        )?;
                    }
                }
                self.prove_footprint(outcome, facts.assumptions())?;
            }
        }
        proved.goals = proved.goals.close(kind);
        Ok(proved)
    }

    /// The ordinary outcome operation has already closed every goal.
    pub(in crate::kernel) fn completed_exit(
        &self,
        path: &SymbolicExecutionPath,
    ) -> ClosedContractExit {
        ClosedContractExit {
            path_index: self.path_index,
            origin: path.theorem.clone(),
            resources: self.context.resource_keys.clone(),
            complete_boundary: self.context.complete_boundary,
        }
    }

    /// Compatibility helper for independent checked-execution fixtures.
    #[cfg(test)]
    pub(crate) fn completion(
        &self,
        path: &SymbolicExecutionPath,
    ) -> Result<ClosedContractExit, ContractClosingRefusal> {
        if let Some(goal) = self.first_open_goal() {
            return Err(ContractClosingRefusal::Pending(goal));
        }
        Ok(ClosedContractExit {
            path_index: self.path_index,
            origin: path.theorem.clone(),
            resources: self.context.resource_keys.clone(),
            complete_boundary: self.context.complete_boundary,
        })
    }

    /// Clause receipts prove individual ownership. Consume their explicit
    /// returned units together: one surviving unit cannot return both a
    /// borrowed input and an additional produced unit.
    fn resource_receipts_jointly_available(
        &self,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        assumptions: &PureFactContext,
    ) -> bool {
        let mut remaining = outcome.state.resources().clone();
        for claim in &self.context.resource_claims {
            let Some(crate::kernel::proof::ClaimGoalEvidence::Resource(receipt)) =
                claims.evidence(claim.key())
            else {
                return false;
            };
            if receipt.defers_resource_transition {
                return false;
            }
            for fact in receipt.returned_resources.facts() {
                let Some(next) = remaining.without_fact_incrementally(fact, assumptions) else {
                    return false;
                };
                remaining = next;
            }
        }
        true
    }

    fn prove_resource_goals(
        &self,
        execution: &CheckedFunctionExecution,
        path: &SymbolicExecutionPath,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &PureFactStore,
        check_resources: bool,
    ) -> Result<Vec<CertifiedFunctionClaimPath>, ContractClosingRefusal> {
        let context = &self.context;
        // A successful checked transition has resolved this boundary. The
        // original execution's deferred marker predates post-return folds;
        // replaying it would discard the transition's established custody.
        let deferred = self.context.complete_boundary
            && self.checked_transition.is_none()
            && execution
                .deferred_contract_exits
                .get(self.path_index)
                .copied()
                .unwrap_or(false);
        if (!check_resources || context.resource_claims.is_empty())
            && context.effect_claims.is_empty()
            && !deferred
        {
            return Ok(Vec::new());
        }
        let retained_entry = execution
            .entry_authority
            .as_ref()
            .map(|authority| authority.cases());
        let check_guards =
            deferred || retained_entry.is_some() && !context.effect_claims.is_empty();
        let independent_guards;
        let guards = if !check_guards {
            &[][..]
        } else if let Some(entry) = retained_entry {
            entry.closing_resource_guards()?
        } else {
            independent_guards = contract_resource_guards(
                &context.caller,
                &context.function,
                &context.arguments,
                &context.entry_assumptions,
            )?;
            independent_guards.as_slice()
        };
        let checked_outcome = if outcome.is_exceptional {
            FunctionOutcome::Throw {
                value: outcome.result.clone(),
                state: Box::new((*outcome.state).clone()),
            }
        } else {
            FunctionOutcome::Return {
                value: outcome.result.clone(),
                state: Box::new((*outcome.state).clone()),
            }
        };
        let checked_claims = context
            .resource_claims
            .iter()
            .filter(|claim| {
                matches!(
                    claims.evidence(claim.key()),
                    Some(crate::kernel::proof::ClaimGoalEvidence::Resource(_))
                )
            })
            .map(|claim| claim.key().clone())
            .collect::<Vec<_>>();
        let mut effect_paths = Vec::new();
        let mut pending = vec![(0, Vec::new())];
        while let Some((start, mut case)) = pending.pop() {
            if crate::kernel::assumptions::reasoning_interrupted() {
                return Err(ContractClosingRefusal::Internal(
                    "checking conditional resources was interrupted".into(),
                ));
            }
            // Decide guards from this checked outcome. Keep the other arm
            // pending only for a guard whose truth this path leaves open.
            let mut post = assumptions_with_propositions(facts.assumptions(), &case);
            for (index, guard) in guards.iter().enumerate().skip(start) {
                crate::instrumentation::record_deterministic_work(1);
                let negated = negate_contract_case_proposition(guard);
                let selected = if post.settles_exactly(guard) {
                    guard.clone()
                } else if post.settles_exactly(&negated) {
                    negated
                } else {
                    let mut alternative = case.clone();
                    alternative.push(negated);
                    pending.push((index + 1, alternative));
                    guard.clone()
                };
                post = post.assume_proposition(selected.clone());
                case.push(selected);
            }
            if post.has_retained_contradiction() {
                continue;
            }
            let mut path = path.clone();
            path.assumptions = assumptions_with_propositions(&path.assumptions, &case);
            path.post_assumptions = Some(post);
            let prepared = if let Some(entry) = retained_entry {
                let case_entry;
                let selected = if case.is_empty() {
                    &entry.closing_entry
                } else {
                    case_entry = entry
                        .closing_entry
                        .for_resource_case(&context.function, &case)?;
                    &case_entry
                };
                prepare_closing_path(
                    &context.function,
                    &path,
                    selected,
                    &checked_outcome,
                    checked_claims.clone(),
                    false,
                    deferred,
                    execution
                        .deferred_contract_exit_errors
                        .get(self.path_index)
                        .cloned()
                        .flatten(),
                    false,
                    execution.boundary_transfer.as_deref(),
                )
            } else {
                prepare_function_claim_path(
                    &context.function,
                    &path,
                    checked_claims.clone(),
                    false,
                    deferred,
                    execution
                        .deferred_contract_exit_errors
                        .get(self.path_index)
                        .cloned()
                        .flatten(),
                    false,
                    execution.boundary_transfer.as_deref(),
                    Some(&checked_outcome),
                )
            }
            .map_err(ContractPathPreparationFailure::into_closing_refusal)?;
            match &prepared.outcome {
                FunctionOutcome::RuntimeError(error) => {
                    return Err(ContractPathPreparationFailure::runtime(
                        error.to_string(),
                        error.clone(),
                    )
                    .into_closing_refusal());
                }
                FunctionOutcome::UndefinedBehavior(error) => {
                    return Err(ContractClosingRefusal::UndefinedBehavior(error.clone()));
                }
                _ => {}
            }
            let no_propositions = CheckedPropositionIndex::default();
            for claim in context.resource_claims.iter().filter(|_| check_resources) {
                if !function_claim_holds_on_prepared_path(
                    &context.function,
                    claim,
                    &prepared,
                    &no_propositions,
                    None,
                    None,
                ) {
                    return Err(ContractClosingRefusal::Claim(claim.key().clone()));
                }
            }
            if !context.effect_claims.is_empty() {
                effect_paths.push(prepared);
            }
        }
        Ok(effect_paths)
    }

    fn prove_allocation_lifetime(
        &self,
        outcome: &OutcomeProofCore,
        claims: &OutcomeClaimGoals,
        facts: &PureFactStore,
    ) -> Result<(), ContractClosingRefusal> {
        let context = &self.context;
        let assumptions = facts.assumptions();
        let mut returned = ResourceContext::new_with_equalities(assumptions);
        let mut all_checked = !context.resource_claims.is_empty();
        let mut contributes = false;
        for claim in &context.resource_claims {
            match claims.evidence(claim.key()) {
                Some(crate::kernel::proof::ClaimGoalEvidence::Resource(receipt)) => {
                    if receipt.defers_resource_transition {
                        return Ok(());
                    }
                    if receipt.contributes_returned_resources {
                        contributes = true;
                        returned = returned.unchecked_with_facts(
                            receipt.returned_resources.facts().iter().cloned(),
                        );
                    }
                }
                _ => all_checked = false,
            }
        }
        let mut budget = ExecutionBudget::beside_live_state();
        let result = if all_checked && contributes {
            crate::kernel::functions::unreturned_allocation_with_checked_returned_resources(
                &context.caller,
                &outcome.state,
                &outcome.result.native(),
                &context.function,
                &context.arguments,
                &returned,
                assumptions,
                &mut budget,
            )
        } else {
            crate::kernel::functions::unreturned_allocation_at_function_exit(
                &context.caller,
                &outcome.state,
                &outcome.result.native(),
                &context.function,
                &context.arguments,
                assumptions,
                &mut budget,
            )
            .map_err(ContractClosingRefusal::from_stop)?
        }
        .map_err(ContractClosingRefusal::Runtime)?;
        if let Some(obligation) = result {
            return Err(ContractClosingRefusal::Runtime(
                RuntimeError::LiveAllocationLeak {
                    allocation: Box::new(obligation.allocation().clone()),
                    resource: obligation.holder().cloned().map(Box::new),
                },
            ));
        }
        Ok(())
    }

    fn prove_footprint(
        &self,
        outcome: &OutcomeProofCore,
        assumptions: &PureFactContext,
    ) -> Result<(), ContractClosingRefusal> {
        let context = &self.context;
        let function = &context.function;
        let empty =
            function.contract_mutable().is_empty() && !function.resource_derived_mutable_frame();
        let framed = !function.contract_mutable().is_empty()
            || !function.resource_requires().is_empty()
            || function.resource_derived_mutable_frame();
        if !empty && !framed {
            return Ok(());
        }
        // What the function wrote is what the memory history records from
        // the caller's point to this exit, argument binding included.
        // A loop's iterations that return to its head are on no exit's
        // path; its exit records their writes.
        let writes = crate::kernel::RecordedWrites::between(
            context.caller.path_link(),
            outcome.state.path_link(),
        )
        .ok_or_else(|| {
            ContractClosingRefusal::Incomplete(
                "the exit is not reached from the function's entry".into(),
            )
        })?;
        if writes.unbounded_loop {
            return Err(ContractClosingRefusal::Incomplete(
                "a loop's iterations do not record what they wrote".into(),
            ));
        }
        if empty {
            check_empty_footprint(&context.caller, &writes, assumptions)?;
        }
        if framed {
            let has_storage_write = writes
                .accesses
                .iter()
                .any(|(pointer, _)| pointer.base.is_static_storage_block())
                || writes
                    .ranges
                    .iter()
                    .any(|(range, _)| range.base().base.is_static_storage_block());
            if has_storage_write {
                let entry = context.entry()?;
                match storage_writes_outside_owned_footprint(
                    function,
                    &entry.state,
                    &writes,
                    assumptions,
                    entry.resources.as_deref(),
                    Some(
                        entry
                            .projection(function)
                            .map_err(ContractClosingRefusal::Incomplete)?,
                    ),
                )
                .map_err(ContractClosingRefusal::from_stop)?
                {
                    Some(outside) if outside.is_empty() => {}
                    Some(outside) => return Err(ContractClosingRefusal::Storage(outside)),
                    None => {
                        return Err(ContractClosingRefusal::Incomplete(
                            "could not determine which storage the contract allows this function to write".into(),
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

/// The empty footprint: no write the history records reaches memory that
/// existed before the call. Storage the function created is its own.
pub(crate) fn check_empty_footprint(
    caller: &ExecutionState,
    writes: &crate::kernel::RecordedWrites,
    assumptions: &PureFactContext,
) -> Result<(), ContractClosingRefusal> {
    for (pointer, _) in &writes.accesses {
        if !writes.created.contains(&pointer.base)
            && preexisting_write(pointer, caller, assumptions)
        {
            return Err(ContractClosingRefusal::Write(pointer.clone()));
        }
    }
    for (range, before) in &writes.ranges {
        if !writes.created.contains(&range.base().base)
            && preexisting_write(range.base(), caller, assumptions)
            && (!memory_holds_live_heap_allocation_at(before, range.base(), assumptions)
                || memory_holds_live_heap_allocation_at(caller.memory(), range.base(), assumptions))
        {
            return Err(ContractClosingRefusal::Range(range.clone()));
        }
    }
    Ok(())
}

fn preexisting_write(
    pointer: &Address,
    caller: &ExecutionState,
    assumptions: &PureFactContext,
) -> bool {
    if pointer.base.is_local_block() || pointer.base.is_havoc_block() {
        return false;
    }
    // A descriptor can retain a loaded spelling of this function's local.
    // Its checked address-class anchor identifies that private storage with
    // one lookup; no external mutable footprint is needed for those bytes.
    if assumptions
        .equality_graph
        .storage_address(pointer)
        .base
        .is_local_block()
    {
        return false;
    }
    if !matches!(
        pointer.base,
        AddressBase::Heap(_) | AddressBase::Symbolic(_)
    ) {
        return true;
    }
    let memory = caller.memory();
    if !memory.has_nonlocal_storage() {
        return false;
    }
    if memory.is_live_heap_address(pointer, assumptions) {
        return true;
    }
    let mut seen = BTreeSet::new();
    let mut pending = vec![pointer.clone()];
    while let Some(candidate) = pending.pop() {
        if !seen.insert(candidate.clone()) {
            continue;
        }
        if !candidate.base.is_local_block()
            && !candidate.base.is_havoc_block()
            && (memory.has_block(&candidate.base)
                || memory.is_live_heap_address(&candidate, assumptions))
        {
            return true;
        }
        pending.extend(assumptions.exact_pointer_aliases(&candidate).cloned());
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn aliased_write_fixture(
        local: bool,
        size: u32,
    ) -> (
        ExecutionState,
        crate::kernel::RecordedWrites,
        PureFactContext,
    ) {
        let anchor = if local {
            SymbolicMemory::local_pointer("private-output")
        } else {
            Address::new("global:public-output".into(), AddressOffset::constant(0))
        };
        let mut memory = SymbolicMemory::new().with_block(anchor.base.clone(), 4);
        let alias = Address::loaded_value(
            &crate::kernel::intern_memory(memory.clone()),
            &Address::symbolic(Variable(988_000)),
        );
        let mut assumptions = PureFactContext::new();
        let mut previous = alias.clone();
        for i in 0..size {
            let next = Address::symbolic(Variable(988_001 + u64::from(i)));
            assumptions = assumptions.assume_condition(
                OldConditionTerm::address_equal(previous, next.clone()),
                true,
            );
            previous = next;
            memory = memory.with_block(format!("unrelated-write-{i}"), 4);
        }
        assumptions =
            assumptions.assume_condition(OldConditionTerm::address_equal(previous, anchor), true);
        let writes = crate::kernel::RecordedWrites {
            ranges: vec![(
                MemoryRange::new_with_element_width(alias, 0u32.into(), 4u32.into(), 1),
                crate::kernel::intern_memory(memory.clone()),
            )],
            ..Default::default()
        };
        (
            ExecutionState::new().with_memory(memory),
            writes,
            assumptions,
        )
    }

    #[test]
    fn private_storage_aliases_need_no_external_write_footprint() {
        let _session = crate::kernel::VerificationSession::enter();
        let (caller, effects, assumptions) = aliased_write_fixture(true, 8);
        assert!(check_empty_footprint(&caller, &effects, &assumptions).is_ok());
        assert!(check_empty_footprint(&caller, &effects, &PureFactContext::new()).is_err());
        let (caller, effects, assumptions) = aliased_write_fixture(false, 8);
        assert!(check_empty_footprint(&caller, &effects, &assumptions).is_err());
    }

    mod scaling_tests {
        use super::*;
        include!(
            "../../../../scaling_tests/kernel/api/contract_certification/contract_claims/closing.rs"
        );
    }
}
