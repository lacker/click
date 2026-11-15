//! Obligation focus, outcome states, and exit queries.

use super::*;

#[cfg(test)]
thread_local! {
    static OUTCOME_FACT_READS: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}
#[cfg(test)]
pub(in crate::surface) fn take_outcome_fact_reads() -> (usize, usize) {
    OUTCOME_FACT_READS.with(|counts| counts.replace((0, 0)))
}

impl<'a> Proof<'a> {
    /// Whether this execution proof has reached the function-exit frontier.
    ///
    /// This is a read-only smart-tactic query: it exposes no execution state and
    /// grants no authority to advance the proof.
    pub(in crate::surface::proof) fn is_at_function_exit(&self) -> bool {
        self.execution()
            .is_some_and(|execution| execution.core.frontier.is_at_function_exit())
    }

    /// The focused branch execution rests at its bounded region's typed boundary:
    /// its own statement tree is exhausted and no code lies beyond it.
    pub(in crate::surface::proof) fn is_at_region_boundary(&self) -> bool {
        self.execution()
            .is_some_and(|execution| execution.core.frontier.is_at_region_boundary())
    }

    /// Every open goal in this proof, in stable id order.
    #[cfg(test)]
    pub(in crate::surface::proof) fn branches(&self) -> impl Iterator<Item = BranchId> + '_ {
        self.state().open_branches().ids()
    }

    /// The line naming the C statement checked path `path_index` ended at,
    /// as [`describe_execution_statement_site`] spells a stepped statement, or
    /// nothing when the path recorded no statement.
    ///
    /// This is diagnostics only. The statement is the one whose state the
    /// path recorded last, read from the presentation data the outcome
    /// already carries.
    ///
    /// [`describe_execution_statement_site`]: crate::surface::diagnostics::describe_execution_statement_site
    pub(in crate::surface::proof) fn describe_outcome_statement_site(
        &self,
        path_index: usize,
    ) -> String {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return String::new();
        };
        self.state()
            .open_branches()
            .iter()
            .find_map(|(_, branch)| match &branch.obligation {
                Obligation::FunctionOutcome(outcome) if outcome.path_index == path_index => {
                    Some(describe_last_statement_site(
                        &context.constants.source_layout,
                        &outcome.data.presentation.recorded_states,
                    ))
                }
                _ => None,
            })
            .unwrap_or_default()
    }

    pub(in crate::surface::proof) fn focused_outcome_state(
        &self,
    ) -> Result<FunctionOutcome, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("an outcome state requires a focused outcome goal"));
        };
        let value = (*goal.data.core.result).clone();
        let state = (*goal.data.core.state).clone();
        Ok(if goal.data.core.is_exceptional {
            FunctionOutcome::Throw {
                value: value.into(),
                state: Box::new(state),
            }
        } else {
            FunctionOutcome::Return {
                value: value.into(),
                state: Box::new(state),
            }
        })
    }

    pub(in crate::surface::proof) fn with_contract_return_counts(
        &self,
        execution: &CheckedFunctionExecution,
    ) -> Result<Self, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("return counts require an outcome goal"));
        };
        let path = execution
            .paths()
            .get(goal.path_index)
            .ok_or_else(|| self.step_error("return counts have no checked path"))?;
        let Proposition::ProgramFunctionVerifies { outcome, .. } =
            implication_body(path.theorem().proposition())
        else {
            return Err(self.step_error("return counts have no checked execution outcome"));
        };
        self.with_outcome_state(&crate::kernel::function_body_with_return_counts(
            &self.focused_outcome_state()?,
            outcome,
        ))
    }

    /// A retained proposition scope may follow checked resource changes on
    /// its owning outcome. Context, branch and result identity must agree.
    pub(in crate::surface::proof) fn refresh_outcome_from(
        &self,
        root: &Self,
    ) -> Result<Self, ClickError> {
        if !Arc::ptr_eq(&self.context, &root.context) {
            return Err(self.step_error("outcome refresh belongs to another proof branch"));
        }
        let data = self
            .focused_outcome_data()
            .ok_or_else(|| self.step_error("outcome refresh requires an outcome-aware goal"))?;
        let current = root
            .focused_outcome_data()
            .ok_or_else(|| self.step_error("outcome refresh lost its owning outcome"))?;
        if !data.core.identity.same_as(&current.core.identity) {
            return Err(self.step_error("outcome refresh belongs to another execution outcome"));
        }
        if data.core.result != current.core.result
            || data.core.is_exceptional != current.core.is_exceptional
        {
            return Err(self.step_error("outcome refresh cannot change the checked result"));
        }
        self.with_outcome_state(&root.focused_outcome_state()?)
    }

    pub(in crate::surface::proof) fn apply_outcome_contract_resources(
        &self,
        pre_state: &ExecutionState,
        _function: &ProgramFunction,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(_) = self.context.as_ref() else {
            return Err(self.step_error("contract resource effects require an execution proof"));
        };
        // The transition reads the outcome through copies of its resources.
        // Advance the retained outcome's memory index to these facts first,
        // as each step does for its execution state, so a transition retried
        // after each later `have` pairs only the facts added since the last
        // attempt rather than every fact since execution ended.
        if let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() {
            goal.data
                .core
                .state
                .resources()
                .synchronize_memory_equalities(self.facts().assumptions());
        }

        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("contract resource effects require an outcome goal"));
        };
        let (closing, outcome) = goal
            .closing
            .as_ref()
            .ok_or_else(|| {
                self.step_error("contract closing has not generated its resource obligations")
            })?
            .apply_resource_transition(
                pre_state,
                self.focused_outcome_state()?,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!(
                    "could not apply checked contract resource effect: {message}"
                ))
            })?;
        let updated = self.with_outcome_state(&outcome)?;
        let Some(Obligation::FunctionOutcome(goal)) = updated.focused_obligation() else {
            unreachable!("the resource transition preserves its outcome obligation")
        };
        let mut goal = goal.clone();
        goal.closing = Some(closing);
        updated.with_focused_outcome_obligation(goal)
    }

    pub(in crate::surface::proof) fn check_outcome_resource_claim<'e>(
        &self,
        checked_execution: &'e CheckedFunctionExecution,
        claim: FunctionClaimRef<'_>,
    ) -> Result<CheckedResourceClaim<'e>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource claim requires an execution proof"));
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("resource claim requires an outcome goal"));
        };
        let Ensure::Resource(resource) = claim.clause().ensure() else {
            return Err(self.step_error("resource production cannot close a proposition claim"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("resource claim lost its execution"))?;
        let (guard_active, guard_deferred) = match claim.key() {
            FunctionContractClaimKey::Ensure(index) => {
                let guard = checked_execution
                    .function()
                    .resource_ensures()
                    .get(index)
                    .and_then(|resource| resource.guard());
                let Some(guard) = guard else {
                    return prove_ensure_resource(
                        checked_execution,
                        claim.key(),
                        context.claim_label,
                        goal.path_index,
                        || (*goal.data.core.effect_facts).clone(),
                        self.facts(),
                        resource,
                        claim.clause().borrowed(),
                        context.parameter_binding(),
                        execution
                            .core
                            .frontier
                            .execution_start_state(&execution.core.state),
                        context
                            .constants
                            .function_entry_state
                            .as_ref()
                            .unwrap_or_else(|| {
                                execution
                                    .core
                                    .frontier
                                    .execution_start_state(&execution.core.state)
                            }),
                        &self.focused_outcome_state()?,
                        None,
                        false,
                    );
                };
                let decision = {
                    let mut budget = ExecutionBudget::beside_live_state();
                    // Outcome construction already imported these checked path
                    // facts. Retain that context instead of folding the same
                    // inherited guard prefix again for each resource claim.
                    let guard_assumptions = self.facts().assumptions().clone();
                    let guard_state = context
                        .constants
                        .function_entry_state
                        .as_ref()
                        .unwrap_or_else(|| {
                            execution
                                .core
                                .frontier
                                .execution_start_state(&execution.core.state)
                        });
                    let guard_post_state = match self.focused_outcome_state() {
                        Ok(FunctionOutcome::Return { state, .. }) => {
                            // Function exits restore caller locals. Rebind the
                            // callee parameters before lowering a guard, whose
                            // old-memory pointer still uses those names.
                            program_function_entry_state(
                                &state,
                                checked_execution.function(),
                                context.arguments,
                            )
                            .ok_or_else(|| {
                                self.step_error(
                                    "could not bind function parameters for the resource guard",
                                )
                            })?
                        }
                        _ => guard_state.clone(),
                    };
                    crate::kernel::evaluate_guarded_contract_condition_with_loop_entry(
                        guard,
                        &guard_post_state,
                        Some(guard_state),
                        &guard_assumptions,
                        &mut budget,
                    )
                };
                (decision, decision.is_none())
            }
            FunctionContractClaimKey::BodySafety
            | FunctionContractClaimKey::ExceptionalEnsure(_)
            | FunctionContractClaimKey::Effect(_) => (None, false),
        };
        prove_ensure_resource(
            checked_execution,
            claim.key(),
            context.claim_label,
            goal.path_index,
            || (*goal.data.core.effect_facts).clone(),
            self.facts(),
            resource,
            claim.clause().borrowed(),
            context.parameter_binding(),
            execution
                .core
                .frontier
                .execution_start_state(&execution.core.state),
            context
                .constants
                .function_entry_state
                .as_ref()
                .unwrap_or_else(|| {
                    execution
                        .core
                        .frontier
                        .execution_start_state(&execution.core.state)
                }),
            &self.focused_outcome_state()?,
            guard_active,
            guard_deferred,
        )
    }

    /// Updates the focused branch outcome goal's immutable result/state state
    /// after a separately checked resource transition.
    fn with_outcome_state(&self, outcome: &FunctionOutcome) -> Result<Self, ClickError> {
        let (value, state) = match outcome {
            FunctionOutcome::Return { value, state } | FunctionOutcome::Throw { value, state } => {
                (value, state)
            }
            _ => {
                return Err(self.step_error("an outcome state requires a completed outcome"));
            }
        };
        let outcome_data = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => goal.data.as_ref(),
            Some(Obligation::Proposition(goal)) => goal.outcome.as_deref().ok_or_else(|| {
                self.step_error("an outcome state requires a result-aware proposition goal")
            })?,
            _ => {
                return Err(self.step_error("an outcome state requires a focused outcome goal"));
            }
        };
        let mut data = outcome_data.clone();
        if data.core.is_exceptional != matches!(outcome, FunctionOutcome::Throw { .. }) {
            return Err(self.step_error("an outcome state cannot change its outcome family"));
        }
        // Resource-producing post-execution tactics can replace the outcome
        // state after this goal was derived. Carry that persistent state
        // root forward; otherwise later
        // checked fixed-state operations lower resource counts against the stale
        // pre-fold state. ExecutionState's components are shared immutable roots, so
        // this update is constant-size rather than a resource/history
        // materialization.
        data.core.result = Arc::new(value.clone().into_native());
        data.core.state = (*state.clone()).into();
        let data = Arc::new(data);
        let obligation = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => {
                let mut updated = goal.clone();
                updated.data = data;
                updated.closing = updated
                    .closing
                    .as_ref()
                    .map(|closing| closing.after_resource_change());
                Obligation::FunctionOutcome(updated)
            }
            Some(Obligation::Proposition(goal)) => {
                let mut updated = goal.clone();
                updated.outcome = Some(data);
                Obligation::Proposition(updated)
            }
            _ => unreachable!("the outcome data was selected above"),
        };
        let state = self
            .state
            .replace_focused_obligation(obligation)
            .map_err(|_| self.step_error("outcome goal is no longer open"))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        })
    }

    /// Opens the contract claims the focused outcome path owes, in contract
    /// order, as that goal's claim goals. A claim about the other kind of
    /// outcome opens closed.
    pub(in crate::surface::proof) fn open_contract_claim_goals(
        &self,
        closing_context: &Arc<crate::kernel::ContractClosingContext>,
        claims: impl IntoIterator<
            Item = (
                FunctionContractClaimKey,
                Option<FunctionContractClaimTarget>,
            ),
        >,
    ) -> Result<Self, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("claim goals require a focused outcome goal"));
        };
        if goal.claims.is_some() {
            return Err(self.step_error("this outcome path's claim goals are already open"));
        }
        let mut goal = goal.clone();
        goal.closing = Some(closing_context.open(goal.path_index, &goal.data.core));
        goal.claims = Some(OutcomeClaimGoals::open(
            claims,
            goal.data.core.is_exceptional,
        ));
        self.with_focused_outcome_obligation(goal)
    }

    /// One ordinary proof operation discharges one selected closing goal.
    pub(in crate::surface::proof) fn prove_contract_closing_goal(
        &self,
        kind: crate::kernel::proof::ContractClosingGoal,
        execution: &CheckedFunctionExecution,
        path: &crate::kernel::SymbolicExecutionPath,
        publication: &Arc<crate::kernel::PublishedFunctionOutcome>,
    ) -> Result<Self, ClickError> {
        let bound = self
            .state
            .bind_outcome_publication(publication.clone())
            .map_err(|reason| self.step_error(reason))?;
        let bound = self.with_kernel_state(bound);
        let this = &bound;
        let Some(Obligation::FunctionOutcome(goal)) = this.focused_obligation() else {
            return Err(self.step_error("contract closing requires an outcome goal"));
        };
        if !matches!(goal.first_open_goal(), Ok(Some(crate::kernel::proof::OutcomeGoal::Closing(selected))) if selected == kind)
        {
            return Err(
                self.step_error("contract closing must follow the pending source obligations")
            );
        }
        let closing = goal
            .closing
            .as_ref()
            .ok_or_else(|| self.step_error("contract closing obligations were not generated"))?;
        let claims = goal
            .claims
            .as_ref()
            .ok_or_else(|| self.step_error("contract claim obligations were not generated"))?;
        let closing = closing
            .prove_goal(kind, execution, path, &goal.data.core, claims, this.facts())
            .map_err(|refusal| self.contract_closing_error(refusal))?;
        let mut goal = goal.clone();
        goal.closing = Some(closing);
        this.with_focused_outcome_obligation(goal)
    }

    pub(in crate::surface::proof) fn published_contract_claim(
        &self,
        key: &FunctionContractClaimKey,
    ) -> Option<crate::kernel::CheckedFunctionProposition> {
        self.state.published_contract_claim(key)
    }

    fn contract_closing_error(&self, refusal: crate::kernel::ContractClosingRefusal) -> ClickError {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return self.step_error("contract closing requires an execution proof");
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return self.step_error("contract closing requires an outcome goal");
        };
        use crate::kernel::ContractClosingRefusal as Refusal;
        let binding = context.parameter_binding();
        let label = context.claim_label;
        let index = goal.path_index;
        let message = match refusal {
            Refusal::Claim(key) => {
                let claim = match key {
                            FunctionContractClaimKey::Ensure(clause_index) => match context.function_block.ensures().get(clause_index) { Some(clause) => FunctionClaimRef::Ensure(clause_index, clause), None => return self.step_error(format!("contract closing for `{label}` path {index}: unproved generated returned-storage obligation")) },
                            _ => return self.step_error(format!("contract closing for `{label}` path {index}: unproved boundary claim {key:?}")),
                        };
                let clause = match claim.clause().ensure() {
                    Ensure::Resource(resource) => {
                        crate::surface::validation::describe_resource_clause(resource)
                    }
                    Ensure::Proposition(proposition) => {
                        crate::surface::diagnostics::describe_click_proposition(proposition)
                    }
                };
                format!(
                    "contract closing for `{label}` path {index}: unproved resource obligation {} `{clause}`",
                    function_claim_label(context.function_block, &claim)
                )
            }
            #[cfg(test)]
            Refusal::Pending(kind) => format!(
                "contract closing for `{label}` path {index}: unproved {} obligation; prove it explicitly with `known()` or supply the facts and resources needed by the implicit solver",
                kind.description()
            ),
            Refusal::Resource(reason) => {
                format!("contract closing for `{label}` path {index}: {reason}")
            }
            Refusal::Runtime(error) => format!(
                "`{label}` path {index}: C operation could not be verified: {}{}",
                describe_runtime_error(&error, binding),
                self.describe_outcome_statement_site(index)
            ),
            Refusal::Write(pointer) => format!(
                "`{}.implicit_effect` failed on path {index}: write to `{}` is outside the mutable footprint",
                context.function_block.signature().name(),
                describe_pointer(&pointer, binding)
            ),
            Refusal::Range(range) => format!(
                "`{}.implicit_effect` failed on path {index}: write range `{}` is outside the mutable footprint",
                context.function_block.signature().name(),
                describe_memory_range(&range, binding)
            ),
            Refusal::Storage(outside) => format!(
                "`{label}` path {index}: write to storage outside the owned footprint: {}; own the written cells",
                crate::surface::diagnostics::describe_storage_writes_outside_footprint(
                    &outside, binding
                )
            ),
        };
        self.step_error(message)
    }

    pub(in crate::surface::proof) fn first_open_outcome_goal(
        &self,
    ) -> Result<Option<crate::kernel::proof::OutcomeGoal>, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("goal selection requires an outcome proof"));
        };
        goal.first_open_goal()
            .map_err(|reason| self.step_error(reason))
    }

    pub(in crate::surface::proof) fn open_contract_execution(
        &self,
        execution: CheckedFunctionExecution,
        whole: Option<&crate::kernel::WholeContractRoot>,
        branches: impl Iterator<Item = BranchId>,
    ) -> Result<crate::kernel::ContractExecutionOwner, ClickError> {
        self.state
            .open_contract_execution(execution, whole, branches)
            .map_err(|reason| self.step_error(reason))
    }

    pub(in crate::surface::proof) fn complete_outcome_in(
        &self,
        owner: &Self,
        execution: &mut crate::kernel::ContractExecutionOwner,
    ) -> Result<Self, ClickError> {
        let state = self
            .state
            .complete_function_outcome_in_execution(&owner.state, execution)
            .map_err(|reason| self.step_error(reason))?;
        Ok(owner.with_kernel_state(state))
    }

    pub(in crate::surface::proof) fn finish_contract_execution(
        &self,
        execution: crate::kernel::ContractExecutionOwner,
    ) -> Result<crate::kernel::CompletedContractExecution, ClickError> {
        self.state
            .finish_contract_execution(execution)
            .map_err(|reason| self.step_error(reason))
    }

    pub(in crate::surface::proof) fn contract_exit_completes_boundary(&self) -> bool {
        match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => goal
                .closing
                .as_ref()
                .is_some_and(|closing| closing.completes_boundary()),
            _ => false,
        }
    }

    /// The focused outcome path's claim goals, once opened.
    pub(in crate::surface::proof) fn claim_goals(&self) -> Option<&OutcomeClaimGoals> {
        match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => goal.claims.as_ref(),
            _ => None,
        }
    }

    /// Closes one claim goal of the focused outcome path with its evidence.
    /// A checked completion must be proved about this outcome and about this
    /// claim.
    pub(in crate::surface::proof) fn close_claim_goal(
        &self,
        key: &FunctionContractClaimKey,
        evidence: ClaimGoalEvidence,
    ) -> Result<Self, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("closing a claim requires a focused outcome goal"));
        };
        let claims = goal
            .claims
            .as_ref()
            .ok_or_else(|| self.step_error("this outcome path's claim goals are not open"))?
            .close(key, evidence, &goal.data.core.identity)
            .map_err(|error| {
                self.step_error(match error {
                    ClaimGoalError::Unknown => "this outcome path owes no such claim",
                    ClaimGoalError::AlreadyClosed => "this claim is already closed on this path",
                    ClaimGoalError::WrongClaim => {
                        "the completion does not prove this contract claim"
                    }
                    ClaimGoalError::WrongOutcome => {
                        "the completion was proved about a different outcome path"
                    }
                })
            })?;
        let mut goal = goal.clone();
        goal.claims = Some(claims);
        self.with_focused_outcome_obligation(goal)
    }

    fn with_focused_outcome_obligation(&self, goal: OutcomeObligation) -> Result<Self, ClickError> {
        let state = self
            .state
            .replace_focused_obligation(Obligation::FunctionOutcome(goal))
            .map_err(|_| self.step_error("outcome goal is no longer open"))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        })
    }

    /// Resource observations are consequences of this outcome's checked
    /// resource state. Publish their persistent fact delta on the same branch.
    pub(in crate::surface::proof) fn project_outcome_resources(&self) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome resource projection requires an execution proof"));
        };
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("outcome resource projection requires an outcome goal"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("outcome lost its execution"))?;
        let pre_state = execution
            .core
            .frontier
            .execution_start_state(&execution.core.state);
        let facts = project_outcome_resource_facts(
            context.resource_environment,
            context.parameter_binding(),
            pre_state,
            &self.focused_outcome_state()?,
            self.facts().clone(),
            context.spec_definitions,
            context.claim_label,
            goal.path_index,
        )?;
        let state = self
            .state
            .replace_focused_obligation_and_facts(Obligation::FunctionOutcome(goal.clone()), facts)
            .map_err(|_| self.step_error("outcome goal is no longer open"))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        })
    }

    /// Route this checked execution path through its retained proof-case
    /// hypotheses. The caller cannot supply a new hypothesis or select facts
    /// from another path.
    pub(in crate::surface::proof) fn prepare_outcome_cases(
        &self,
        owner: &mut Self,
        execution_owner: &mut crate::kernel::ContractExecutionOwner,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome routing requires an execution proof"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("outcome lost its execution"))?;
        let mut facts = self.facts().clone();
        let outcome = self.focused_outcome_state()?;
        for case in &execution.presentation.case_assumptions {
            let FunctionOutcome::Return { value, state } = &outcome else {
                return Err(self.step_error("proof-level `if` requires a return outcome"));
            };
            let fact = if let Some(fact) = &case.fact {
                fact.clone()
            } else {
                let condition = lower_outcome_proposition_with_recorded_states(
                    context.parameter_binding(),
                    execution
                        .core
                        .frontier
                        .execution_start_state(&execution.core.state),
                    state,
                    &value.native(),
                    &facts,
                    &case.condition,
                    context.spec_definitions,
                    &execution.presentation.recorded_states,
                )
                .map_err(|message| self.step_error(message))?;
                if case.value {
                    condition
                } else {
                    Proposition::Not(Box::new(condition))
                }
            };
            let conflicts = facts.directly_conflicts_with(&fact);
            match if conflicts {
                Ok(true)
            } else {
                super::super::claim_proofs::proof_case_fact_conflicts(&fact, facts.assumptions())
            } {
                Ok(true) => {
                    let facts = facts.with_kernel_checked_fact(fact.clone());
                    let state = self
                        .state
                        .replace_focused_obligation_and_facts(
                            self.focused_obligation().expect("outcome exists").clone(),
                            facts,
                        )
                        .map_err(|_| self.step_error("outcome goal is no longer open"))?;
                    let state = state
                        .refute_function_outcome_in_execution(&owner.state, &fact, execution_owner)
                        .map_err(|reason| self.step_error(reason))?;
                    *owner = owner.with_kernel_state(state);
                    return Ok(None);
                }
                Err(()) => return Err(self.step_error(format!(
                    "proof branch routing reached an inconsistent assumption context at tactic {}",
                    case.tactic_index
                ))),
                Ok(false) => {}
            }
            facts = facts.with_kernel_checked_fact(fact);
        }
        let state = self
            .state
            .replace_focused_obligation_and_facts(
                self.focused_obligation().expect("outcome exists").clone(),
                facts,
            )
            .map_err(|_| self.step_error("outcome goal is no longer open"))?;
        Ok(Some(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        }))
    }

    /// Store consequences are derived from this outcome's checked execution
    /// once and retained with it. Later haves share the resulting fact root.
    pub(in crate::surface::proof) fn with_outcome_store_consequences(
        &self,
    ) -> Result<Self, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("store consequences require an outcome goal"));
        };
        if goal.data.core.store_consequences_available {
            return Ok(self.clone());
        }
        let mut facts = self.facts().clone();
        for fact in crate::kernel::certified_store_equations(&*goal.data.core.effect_facts)
            .into_iter()
            .chain(crate::kernel::certified_store_loadability_facts(
                &*goal.data.core.effect_facts,
            ))
        {
            facts = facts.with_kernel_checked_fact(fact);
        }
        let mut data = (*goal.data).clone();
        data.core.store_consequences_available = true;
        let mut goal = goal.clone();
        goal.data = Arc::new(data);
        let state = self
            .state
            .replace_focused_obligation_and_facts(Obligation::FunctionOutcome(goal), facts)
            .map_err(|_| self.step_error("outcome goal is no longer open"))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        })
    }

    /// Open a proof of an already-lowered contract claim. Report missing
    /// definedness obligations through the ordinary obligation channel;
    /// scheduling their proofs belongs to the driver.
    pub(in crate::surface::proof) fn begin_contract_claim(
        &self,
        goal: &crate::kernel::ContractClaimGoal,
        surface: &ClickProposition,
    ) -> Result<Self, ClickError> {
        #[cfg(test)]
        let _operation = crate::kernel::search::FastOperationScope::enter("begin_contract_claim");
        for obligation in goal.unproved_requirements(self.facts().assumptions()) {
            let error = self
                .step_error_with_requirement(
                    "contract claim has an outstanding evaluation requirement",
                    None,
                    Some((
                        "evaluation requirement",
                        Box::new(obligation.proposition().clone()),
                        None,
                    )),
                )
                .with_unresolved_requirement(&obligation);
            super::super::execution_planning::refuse_or_record_open_obligation(error)?;
        }
        self.focus_fixed_state_goal_for_claim(
            goal.proposition().clone(),
            Some(surface.clone()),
            Some(goal),
        )
    }

    pub(in crate::surface::proof) fn with_claim_lowering_facts(
        self,
        origin: &Self,
        lowering_facts: &[Proposition],
    ) -> Result<Self, ClickError> {
        let mut focused = self;
        let facts = lowering_facts
            .iter()
            .fold(focused.facts().clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact.clone())
            });
        focused.state = focused
            .state
            .replace_focused_obligation_and_facts(
                focused
                    .focused_obligation()
                    .expect("claim goal exists")
                    .clone(),
                facts,
            )
            .map_err(|_| origin.step_error("claim goal is no longer open"))?;
        Ok(focused)
    }

    /// Returns a handle addressing another open goal of the same state.
    ///
    /// Focus is a cursor: the returned handle shares this proof's semantic
    /// state and provenance, and checked operations through it advance
    /// exactly the addressed goal.
    /// The single open goal's id, when exactly one goal remains. Split
    /// regressions use it to name the pre-split obligation.
    #[cfg(test)]
    pub(super) fn sole_branch_id(&self) -> Option<BranchId> {
        let mut ids = self.branches();
        let sole = ids.next()?;
        ids.next().is_none().then_some(sole)
    }

    pub(in crate::surface::proof) fn focus_branch(
        &self,
        goal: BranchId,
    ) -> Result<Self, ClickError> {
        let mut focused = self.clone();
        focused.state = focused
            .state
            .focus_open_branch(goal)
            .map_err(|error| match error {
                ProofFocusError::NotOpen => {
                    self.step_error(format!("goal {goal:?} is not open in this proof"))
                }
            })?;
        Ok(focused)
    }

    /// Derives the typed function-outcome goal set from a function-exit
    /// frontier: the successor retires the focused branch frontier goal and opens
    /// one outcome goal per feasible checked return or throw path, in the checked
    /// execution's deterministic path order. Candidate paths whose exact
    /// facts contradict the enclosing proof facts contribute no goal.
    ///
    /// Each outcome goal owns its path's result value, post-outcome C state,
    /// and fact context (the frontier's facts extended by only that path's
    /// own facts), and borrows the frontier's state by identity for
    /// lowering. A path proved non-returning contributes no goal. The
    /// returned handle addresses the first outcome goal; `focus` reaches its
    /// siblings. Result and effect continuations consume these goals
    /// directly rather than converting through a mutable execution-context adapter.
    #[cfg(test)]
    pub(in crate::surface::proof) fn split_function_outcomes(
        &self,
    ) -> Result<(Self, Vec<BranchId>, BTreeMap<usize, BranchId>), ClickError> {
        self.split_published_function_outcomes(None)
    }

    pub(in crate::surface::proof) fn split_checked_function_outcomes(
        &self,
        execution: &CheckedFunctionExecution,
    ) -> Result<(Self, Vec<BranchId>, BTreeMap<usize, BranchId>), ClickError> {
        self.split_published_function_outcomes(Some(execution))
    }

    fn split_published_function_outcomes(
        &self,
        publication: Option<&CheckedFunctionExecution>,
    ) -> Result<(Self, Vec<BranchId>, BTreeMap<usize, BranchId>), ClickError> {
        if !matches!(self.focused_obligation(), Some(Obligation::Frontier(_))) {
            return Err(self.step_error("outcome goals require an open execution frontier"));
        }
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let checked = execution.core.frontier.execution().ok_or_else(|| {
            self.step_error("outcome goals require execution to have reached function exit")
        })?;
        let call_edges = execution
            .presentation
            .call_outcome_edges
            .as_ref()
            .filter(|edges| edges.len() == checked.paths().len());
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let frontier_state = branch_state.execution.clone();
        let frontier_unfolds = branch_state.unfolded_predicates.clone();
        let frontier_anchor = frontier_state
            .as_ref()
            .and_then(|execution| frontier_premise_anchor(execution));
        let requirement_surfaces = match self.context.as_ref() {
            ProofContext::Execution(context) => context
                .constants
                .execution_start_facts
                .iter()
                .zip(context.constants.entry_fact_origins.iter())
                .filter_map(|(fact, origin)| {
                    let EntryFactOrigin::Requirement {
                        source_id,
                        role: RequirementFactRole::Principal { .. },
                    } = origin
                    else {
                        return None;
                    };
                    let surface = context
                        .function_block
                        .requires()
                        .get(source_id.outer_ordinal)?
                        .proposition()?;
                    Some((fact.clone(), surface.clone()))
                })
                .fold(PersistentMap::default(), |index, (fact, surface)| {
                    index.with_inserted(fact, surface)
                }),
            _ => PersistentMap::default(),
        };
        let requirement_surfaces = Arc::new(requirement_surfaces);
        // The frontier contributes only the suffix added after the shared
        // entry root. Each checked leaf already retains that entry prefix.
        let ambient_delta = execution
            .presentation
            .outcome_fact_root
            .as_ref()
            .and_then(|root| self.facts().introduced_since(root));
        let mut goals = Vec::new();
        let mut path_indices = Vec::new();
        for (path_index, path) in checked.paths().iter().enumerate() {
            let provenance = execution.provenance_for_outcome(path_index);
            let retained_leaf = provenance
                .checked_leaf_facts
                .as_deref()
                .filter(|(candidate, _, _)| candidate.shares_record_with(path))
                .map(|(_, facts, holds_effects)| (facts, *holds_effects))
                .filter(|_| {
                    execution
                        .core
                        .pending_loop_return_pure_facts(path_index)
                        .is_none()
                })
                .zip(ambient_delta.as_ref());
            // A returned path of a summarized loop keeps the fact base it was
            // certified under, not the facts the continuing path established
            // after the loop.
            let mut facts = execution
                .core
                .pending_loop_return_pure_facts(path_index)
                .cloned()
                .unwrap_or_else(|| self.facts().clone());
            // One checked statement may produce several candidate outcomes.
            // The enclosing Proof facts select the feasible successors; an
            // exact contradictory path fact cannot become a typed outcome
            // goal merely because the legacy execution container retained
            // every candidate. Preserve the original path index so later
            // finalization addresses the checked candidate without rebuilding
            // or renumbering the path set.
            #[cfg(test)]
            OUTCOME_FACT_READS.with(|counts| {
                let (reused, imported) = counts.get();
                counts.set((reused + usize::from(retained_leaf.is_some()), imported));
            });
            if let Some(((leaf, _), ambient)) = retained_leaf {
                if ambient
                    .iter()
                    .any(|fact| leaf.directly_conflicts_with(fact))
                {
                    continue;
                }
                facts = leaf.clone();
                for fact in ambient {
                    facts = facts.with_kernel_checked_fact(fact.clone());
                }
            } else if path
                .facts()
                .iter()
                .any(|fact| facts.directly_conflicts_with(fact.proposition()))
            {
                continue;
            }
            let (result, state, is_exceptional) = match path.outcome() {
                FunctionOutcome::Return { value, state } => (value.clone(), state.clone(), false),
                FunctionOutcome::Throw { value, state } => (value.clone(), state.clone(), true),
                // A path proved non-returning owes no outcome judgment.
                FunctionOutcome::VerificationDiverges => continue,
                FunctionOutcome::UndefinedBehavior(_) | FunctionOutcome::RuntimeError(_) => {
                    let ProofContext::Execution(context) = self.context.as_ref() else {
                        unreachable!()
                    };
                    return Err(self.step_error(format!(
                        "path {path_index}: {}{}",
                        describe_function_outcome(path.outcome(), context.parameter_binding()),
                        describe_last_statement_site(
                            &context.constants.source_layout,
                            &execution.provenance_for_outcome(path_index).recorded_states,
                        ),
                    )));
                }
            };
            // Import the checked path delta once, including its effect
            // evidence. Haves and resource operations share this persistent
            // context; none reconstructs assumptions from the path history.
            let outcome_core = match publication {
                Some(publication) => publication
                    .open_outcome(path_index)
                    .expect("a returning checked candidate owns its outcome publication"),
                None => OutcomeProofCore {
                    publication: None,
                    identity: crate::kernel::proof::OutcomeIdentity::fresh(),
                    store_consequences_available: false,
                    result: Arc::new(result.into_native()),
                    state: (*state).into(),
                    is_exceptional,
                    effect_facts: crate::kernel::proof::OutcomeExecutionFacts::merging(
                        path.facts().clone(),
                        path.effect_facts().clone(),
                    ),
                },
            };
            let execution_facts = outcome_core.effect_facts.clone();
            // A leaf that holds its path's effects imports nothing more.
            let no_facts = crate::kernel::ExecutionFacts::new();
            let imported_facts = match retained_leaf {
                Some(((_, true), _)) => &no_facts,
                Some(_) => path.effect_facts(),
                None => &*execution_facts,
            };
            for fact in imported_facts {
                #[cfg(test)]
                OUTCOME_FACT_READS.with(|counts| {
                    let (reused, imported) = counts.get();
                    counts.set((reused, imported + 1));
                });
                facts = facts.with_kernel_checked_fact(fact.proposition().clone());
            }
            let outcome_execution = frontier_state.as_ref().map(|retained_state| {
                let mut opened = retained_state.as_ref().clone();
                opened
                    .core
                    .open_return_outcome(path_index, &outcome_core, &facts);
                Arc::new(opened)
            });
            path_indices.push(path_index);
            goals.push(OpenBranch::function_outcome(
                OutcomeObligation::new(
                    path_index,
                    Arc::new(OutcomeProofData::new(
                        outcome_core,
                        OutcomeProofPresentation {
                            surface_propositions: provenance.surface_propositions,
                            recorded_states: provenance.recorded_states,
                            // A returned path of a summarized loop states its
                            // facts over the loop's iteration identities,
                            // which the loop's exit state binds; the
                            // frontier's own anchor is wherever the
                            // continuing path last stepped.
                            premise_anchor: execution
                                .core
                                .pending_loop_return_loop_index(path_index)
                                .map(|loop_index| ProgramPointRef {
                                    region: crate::surface::CodeRegionRef::Loop(loop_index),
                                    kind: ProgramPointKind::Exit,
                                })
                                .or_else(|| frontier_anchor.clone()),
                            requirement_surfaces: requirement_surfaces.clone(),
                            branch_decisions: provenance.branch_decisions,
                            match_arms: provenance.match_arms,
                            case_obligations: provenance.case_obligations,
                            checked_haves: provenance.checked_haves,
                            call_routes: if provenance.call_routes.is_empty() {
                                call_edges
                                    .map(|edges| vec![edges[path_index]])
                                    .unwrap_or_default()
                            } else {
                                provenance.call_routes
                            },
                        },
                    )),
                ),
                BranchState {
                    facts,
                    unfolded_predicates: frontier_unfolds.clone(),
                    execution: outcome_execution,
                },
            ));
        }
        let (state, outcome_ids) = self
            .state
            .replace_focused_with_checked_branches(goals)
            .map_err(|_| self.step_error("outcome goals require an open execution frontier"))?;
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            // A structural marker records the derivation; the certificate
            // step vocabulary for consuming outcome goals arrives with the
            // drain migration.
            node: ProofNode::marker(&self.node, self.focused_branch_id(), Vec::new()),
        };
        let by_path = path_indices
            .into_iter()
            .zip(outcome_ids.iter().copied())
            .collect();
        Ok((successor, outcome_ids, by_path))
    }

    /// Whether the checked execution frontier is a structural C `if`.
    ///
    /// Smart `execute` uses this read-only query to distinguish a structural
    /// frontier from an ordinary statement whose indexed candidate simply did
    /// not apply. It grants no branch authority and performs no transition.
    pub(in crate::surface::proof) fn is_at_execution_branch(&self) -> Result<bool, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its semantic frontier"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Ok(false);
        }
        let Some(context) = self.execution_context() else {
            return Ok(false);
        };
        let statement_index = execution.core.frontier.next_statement_index;
        let source_region = context
            .constants
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                self.step_error(format!("could not resolve region({statement_index})"))
            })?;
        Ok(matches!(source_region.kind, SourceStatementKind::If { .. }))
    }

    /// Whether the frontier `if` is an arm test of a Rust `match`. A step
    /// splits it with a proof `match`, not a proof `if`.
    pub(in crate::surface::proof) fn is_at_enum_match_test(&self) -> Result<bool, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(false);
        };
        let Some(execution) = self.execution() else {
            return Ok(false);
        };
        let Ok((_, _, ProgramStatement::If { condition, .. }, _)) =
            next_top_level_statement_from_frontier_position(
                execution.view(context),
                &execution.core.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "execute",
            )
        else {
            return Ok(false);
        };
        let mut test = &condition;
        while let ProgramExpression::Or(left, _) = test {
            test = left;
        }
        Ok(matches!(test, ProgramExpression::EnumIs { .. }))
    }

    /// Whether this frontier has the source shape handled by the explicit
    /// proof-object returned/threw split. This is intentionally syntax-only:
    /// the split operation performs the one checked evaluation, so merely
    /// asking whether the frontier is eligible must not evaluate the call.
    pub(in crate::surface::proof) fn is_at_call_outcomes_frontier(
        &self,
    ) -> Result<bool, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(false);
        };
        let Some(execution) = self.execution() else {
            return Ok(false);
        };
        let (_, _, mut statement, _) =
            crate::surface::proof::cursor_execution::next_top_level_statement_from_frontier_position(
                execution.view(context),
                &execution.core.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "outcomes",
            )?;
        let mut statement_index = execution.core.frontier.next_statement_index;
        let mut descended_through_try = false;
        loop {
            // A call is a fork when it may throw: inside a `try` the throw
            // enters the handler, and outside any `try` it leaves the
            // function. Either way its two successors are two proof arms,
            // like a C `if`'s. A callee whose contract throws nothing has
            // one successor, as the kernel's call has, even inside a `try`:
            // a destructible local's unwind cleanup wraps every call.
            if let ProgramStatement::Call { function_name, .. }
            | ProgramStatement::CallConstruct { function_name, .. }
            | ProgramStatement::CallResult { function_name, .. } = &statement
            {
                return Ok(context
                    .function_environment
                    .get_function(function_name)
                    .map_or(descended_through_try, |callee| {
                        !callee.exceptional_signature().is_empty()
                    }));
            }
            let ProgramStatement::TryCatchInt32 { try_body, .. } = statement else {
                return Ok(false);
            };
            let SourceStatementKind::Try {
                try_statement_index,
                ..
            } = context
                .constants
                .source_layout
                .statement(statement_index)
                .ok_or_else(|| {
                    self.step_error(format!("could not resolve region({statement_index})"))
                })?
                .kind
            else {
                return Ok(false);
            };
            let (next, _) =
                crate::surface::proof::cursor_execution::split_next_source_operation(&try_body)
                    .map_err(|message| self.step_error(format!("`outcomes` failed: {message}")))?;
            statement = next;
            statement_index = try_statement_index;
            descended_through_try = true;
        }
    }

    /// Resolves a Surface Click statement region against this proof's source
    /// layout without exposing the mutable frontier or check metadata.
    pub(in crate::surface::proof) fn resolve_statement_target(
        &self,
        region: &CodeRegionRef,
    ) -> Result<usize, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step_until` requires an execution proof"));
        };
        if let CodeRegionRef::Assignment { local, occurrence } = region {
            return context
                .constants
                .source_layout
                .assignment_entry(local, *occurrence)
                .map_err(|message| self.step_error(message));
        }
        if let CodeRegionRef::Read(occurrence) = region {
            return context
                .constants
                .source_layout
                .read_entry(*occurrence)
                .map_err(|message| self.step_error(message));
        }
        // A statement region is entered at its first atomic region, its own
        // or a child's: execution stops there, as at that `region(N)`.
        if let CodeRegionRef::Path(steps) = region {
            let layout = &context.constants.source_layout;
            let index = layout
                .source_path_region(steps, ProgramPointKind::Entry)
                .map_err(|message| self.step_error(message))?;
            return layout
                .execution_region_entry(CodeRegion::Statement(index))
                .map_err(|message| self.step_error(message));
        }
        let region = resolve_code_region_ref(
            context.function_block,
            region,
            context.claim_label,
            context.tactic_index,
        )?;
        context
            .constants
            .source_layout
            .execution_region_entry(region)
            .map_err(|message| self.step_error(message))
    }

    /// Returns the current source-statement frontier for a checked execution
    /// proof, or `None` after function exit.
    pub(in crate::surface::proof) fn current_statement_index(
        &self,
    ) -> Result<Option<usize>, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its semantic frontier"))?;
        Ok((!execution.core.frontier.is_at_function_exit())
            .then_some(execution.core.frontier.next_statement_index))
    }

    /// Returns the current source-layout frontier node, including the
    /// function-exit node used to attribute terminal effect tactics.
    pub(in crate::surface::proof) fn execution_frontier_index(&self) -> Result<usize, ClickError> {
        self.execution()
            .map(|execution| execution.core.frontier.next_statement_index)
            .ok_or_else(|| self.step_error("execution proof lost its semantic frontier"))
    }
}

/// The line naming the C statement a path stepped last, in the form
/// `describe_execution_statement_site` gives a stepped statement, or nothing when the
/// path recorded none or the layout has no site for it.
fn describe_last_statement_site(
    layout: &crate::surface::lowering::SourceExecutionLayout,
    retained_states: &RecordedStates,
) -> String {
    retained_states
        .latest_statement()
        .and_then(|statement_index| layout.site(statement_index))
        .map(|site| format!("\n  C statement at {}: `{}`", site.location(), site.text()))
        .unwrap_or_default()
}

/// The premise anchor of an execution frontier: the entry of the last
/// executed statement (or the most recent recorded program point), with an
/// exit marker mapped to the matching recorded entry. Premises established
/// across one statement use its entry state as their stable Surface Click
/// spelling; a retained Proof may carry the equivalent exit state as its most
/// recent provenance marker. Outcomes and mid-execution judgments
/// anchor their premises by this one law.
pub(in crate::surface::proof) fn frontier_premise_anchor(
    execution: &ExecutionProofState,
) -> Option<ProgramPointRef> {
    let anchor = execution
        .presentation
        .surface_record
        .last_step_entry
        .clone()
        .or_else(|| {
            execution
                .presentation
                .recorded_states
                .keys_newest_first()
                .find_map(|selector| match selector {
                    ProgramPointSelector::ProgramPoint(point) => Some(point.clone()),
                    ProgramPointSelector::Mark(_) => None,
                })
        })?;
    // A loop's exit state is the state the loop rule's paths are stated
    // over: the head's fresh identities for everything the body writes. Its
    // entry state predates them, so a premise over a returned path's
    // identities could not be spelled there. A statement's exit, by
    // contrast, is read at its entry as before.
    if anchor.kind != ProgramPointKind::Exit
        || matches!(anchor.region, crate::surface::CodeRegionRef::Loop(_))
    {
        return Some(anchor);
    }
    let entry = ProgramPointRef {
        region: anchor.region.clone(),
        kind: ProgramPointKind::Entry,
    };
    Some(
        if execution.presentation.recorded_states.contains_key(&entry) {
            entry
        } else {
            anchor
        },
    )
}
