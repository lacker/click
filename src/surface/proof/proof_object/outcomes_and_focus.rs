//! Obligation focus, outcome snapshots, and exit queries.

use super::*;

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

    /// The open function-outcome goal derived for one checked path, if this
    /// proof owns it. Path indices are the checked execution's deterministic
    /// path order, recorded on each goal at derivation.
    pub(in crate::surface::proof) fn outcome_branch_for_path(
        &self,
        path_index: usize,
    ) -> Option<BranchId> {
        self.state()
            .open_branches()
            .iter()
            .find_map(|(id, branch)| match &branch.obligation {
                Obligation::FunctionOutcome(outcome) if outcome.path_index == path_index => {
                    Some(id)
                }
                _ => None,
            })
    }

    pub(in crate::surface::proof) fn focused_outcome_snapshot(
        &self,
    ) -> Result<CFunctionOutcome, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("an outcome snapshot requires a focused outcome goal"));
        };
        let value = (*goal.data.core.result).clone();
        let state = (*goal.data.core.state).clone();
        Ok(if goal.data.core.is_exceptional {
            CFunctionOutcome::Throw { value, state }
        } else {
            CFunctionOutcome::Return { value, state }
        })
    }

    /// Read return-count representation from the certified path, retaining
    /// the body ownership until its open scopes have been checked closed.
    pub(in crate::surface::proof) fn with_contract_return_counts(
        &self,
        execution: &CCheckedFunctionExecution,
    ) -> Result<Self, ClickError> {
        let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() else {
            return Err(self.step_error("return counts require an outcome goal"));
        };
        let path = execution
            .paths()
            .get(goal.path_index)
            .ok_or_else(|| self.step_error("return counts have no checked path"))?;
        let Proposition::CFunctionVerifies { outcome, .. } =
            implication_body(path.theorem().proposition())
        else {
            return Err(self.step_error("return counts have no checked execution outcome"));
        };
        self.with_outcome_snapshot(&crate::kernel::function_body_with_return_counts(
            &self.focused_outcome_snapshot()?,
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
        self.with_outcome_snapshot(&root.focused_outcome_snapshot()?)
    }

    pub(in crate::surface::proof) fn apply_outcome_contract_resources(
        &self,
        pre_state: &CState,
        function: &CFunction,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("contract resource effects require an execution proof"));
        };

        let (outcome, _obligations) = crate::kernel::apply_c_function_contract_resource_transition(
            pre_state,
            function,
            context.arguments,
            self.focused_outcome_snapshot()?,
            self.facts().assumptions(),
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not apply checked contract resource effect: {message}"
            ))
        })?;
        self.with_outcome_snapshot(&outcome)
    }

    pub(in crate::surface::proof) fn check_outcome_resource_claim<'e>(
        &self,
        checked_execution: &'e CCheckedFunctionExecution,
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
        prove_ensure_resource(
            checked_execution,
            claim.key(),
            context.claim_label,
            goal.path_index,
            &goal.data.core.effect_facts,
            self.facts(),
            resource,
            claim.clause().borrowed(),
            context.parsed_function.parameters(),
            context.arguments,
            execution
                .core
                .frontier
                .execution_start_state(&execution.core.state),
            &self.focused_outcome_snapshot()?,
        )
    }

    /// Updates the focused branch outcome goal's immutable result/state snapshot
    /// after a separately checked resource transition.
    fn with_outcome_snapshot(&self, outcome: &CFunctionOutcome) -> Result<Self, ClickError> {
        let (value, state) = match outcome {
            CFunctionOutcome::Return { value, state }
            | CFunctionOutcome::Throw { value, state } => (value, state),
            _ => return Err(self.step_error("an outcome snapshot requires a completed outcome")),
        };
        let outcome_data = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => goal.data.as_ref(),
            Some(Obligation::Proposition(goal)) => goal.outcome.as_deref().ok_or_else(|| {
                self.step_error("an outcome snapshot requires a result-aware proposition goal")
            })?,
            _ => {
                return Err(self.step_error("an outcome snapshot requires a focused outcome goal"));
            }
        };
        let mut data = outcome_data.clone();
        if data.core.is_exceptional != matches!(outcome, CFunctionOutcome::Throw { .. }) {
            return Err(self.step_error("an outcome snapshot cannot change its outcome family"));
        }
        // Resource-producing post-execution tactics can replace the outcome
        // state after this goal was derived. Carry that persistent snapshot
        // root forward; otherwise later
        // checked fixed-state operations lower resource counts against the stale
        // pre-fold state. CState's components are shared immutable roots, so
        // this update is constant-size rather than a resource/history
        // materialization.
        data.core.result = Arc::new(value.clone());
        data.core.state = state.clone().into();
        let data = Arc::new(data);
        let obligation = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(goal)) => {
                let mut updated = goal.clone();
                updated.data = data;
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
            context.parsed_function.parameters(),
            context.arguments,
            pre_state,
            &self.focused_outcome_snapshot()?,
            self.facts().clone(),
            context.predicate_environment,
            context.click_function_environment,
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
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome routing requires an execution proof"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("outcome lost its execution"))?;
        let mut facts = self.facts().clone();
        let outcome = self.focused_outcome_snapshot()?;
        for case in &execution.presentation.case_assumptions {
            let CFunctionOutcome::Return { value, state } = &outcome else {
                return Err(self.step_error("proof-level `if` requires a return outcome"));
            };
            let fact = if let Some(fact) = &case.fact {
                fact.clone()
            } else {
                let condition = lower_outcome_proposition_with_recorded_snapshots(
                    context.parsed_function.parameters(),
                    context.arguments,
                    execution
                        .core
                        .frontier
                        .execution_start_state(&execution.core.state),
                    state,
                    value,
                    &facts,
                    &case.condition,
                    context.predicate_environment,
                    context.click_function_environment,
                    &execution.presentation.recorded_snapshots,
                )
                .map_err(|message| self.step_error(message))?;
                if case.value {
                    condition
                } else {
                    Proposition::Not(Box::new(condition))
                }
            };
            if facts.directly_conflicts_with(&fact) {
                return Ok(None);
            }
            match super::super::claim_proofs::proof_case_fact_conflicts(&fact, facts.assumptions())
            {
                Ok(true) => return Ok(None),
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
        for fact in crate::kernel::certified_store_equations(&goal.data.core.effect_facts)
            .into_iter()
            .chain(crate::kernel::certified_store_loadability_facts(
                &goal.data.core.effect_facts,
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

    /// Focus a compiler-lowered contract claim with only the load facts
    /// produced by that lowering. The ambient outcome facts remain shared.
    pub(in crate::surface::proof) fn focus_lowered_outcome_claim(
        &self,
        goal: Proposition,
        lowering_facts: &[Proposition],
        surface: &ClickProposition,
    ) -> Result<Self, ClickError> {
        let mut focused = self.focus_fixed_state_goal_with_surface(goal, Some(surface.clone()))?;
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
            .map_err(|_| self.step_error("claim goal is no longer open"))?;
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
    /// own facts), and borrows the frontier's snapshot by identity for
    /// lowering. A path proved non-returning contributes no goal. The
    /// returned handle addresses the first outcome goal; `focus` reaches its
    /// siblings. Result and effect continuations consume these goals
    /// directly rather than converting through a mutable execution-context adapter.
    pub(in crate::surface::proof) fn split_function_outcomes(
        &self,
    ) -> Result<(Self, Vec<BranchId>), ClickError> {
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
        let frontier_snapshot = branch_state.execution.clone();
        let frontier_unfolds = branch_state.unfolded_predicates.clone();
        let frontier_anchor = frontier_snapshot
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
        let mut goals = Vec::new();
        for (path_index, path) in checked.paths().iter().enumerate() {
            let mut facts = execution
                .core
                .pending_exceptional_pure_facts(path_index)
                .cloned()
                .unwrap_or_else(|| self.facts().clone());
            // One checked statement may produce several candidate outcomes.
            // The enclosing Proof facts select the feasible successors; an
            // exact contradictory path fact cannot become a typed outcome
            // goal merely because the legacy execution container retained
            // every candidate. Preserve the original path index so later
            // finalization addresses the checked candidate without rebuilding
            // or renumbering the path set.
            if path
                .facts()
                .iter()
                .any(|fact| facts.directly_conflicts_with(fact.proposition()))
            {
                continue;
            }
            let (result, state, is_exceptional) = match path.outcome() {
                CFunctionOutcome::Return { value, state } => (value.clone(), state.clone(), false),
                CFunctionOutcome::Throw { value, state } => (value.clone(), state.clone(), true),
                // A path proved non-returning owes no outcome judgment.
                CFunctionOutcome::VerificationDiverges => continue,
                CFunctionOutcome::UndefinedBehavior(_) | CFunctionOutcome::RuntimeError(_) => {
                    let ProofContext::Execution(context) = self.context.as_ref() else {
                        unreachable!()
                    };
                    return Err(self.step_error(format!(
                        "path {path_index}: {}",
                        describe_function_outcome(
                            path.outcome(),
                            context.parsed_function.parameters(),
                            context.arguments
                        )
                    )));
                }
            };
            // Import the checked path delta once, including its effect
            // evidence. Haves and resource operations share this persistent
            // context; none reconstructs assumptions from the path history.
            let execution_facts = path.execution_facts();
            for fact in &execution_facts {
                facts = facts.with_kernel_checked_fact(fact.proposition().clone());
            }
            let provenance = execution.provenance_for_outcome(path_index);
            goals.push(OpenBranch::function_outcome(
                OutcomeObligation::new(
                    path_index,
                    Arc::new(OutcomeProofData::new(
                        OutcomeProofCore {
                            identity: crate::kernel::proof::OutcomeIdentity::fresh(),
                            store_consequences_available: false,
                            result: Arc::new(result),
                            state: state.into(),
                            is_exceptional,
                            effect_facts: Arc::new(execution_facts),
                        },
                        OutcomeProofPresentation {
                            surface_propositions: provenance.surface_propositions,
                            recorded_snapshots: provenance.recorded_snapshots,
                            premise_anchor: frontier_anchor.clone(),
                            requirement_surfaces: requirement_surfaces.clone(),
                            branch_decisions: provenance.branch_decisions,
                            call_returned: call_edges.map(|edges| edges[path_index]),
                        },
                    )),
                ),
                BranchState {
                    facts,
                    unfolded_predicates: frontier_unfolds.clone(),
                    execution: frontier_snapshot.clone(),
                },
            ));
        }
        if goals.is_empty() {
            return Ok((self.clone(), Vec::new()));
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
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
                split_branches: Vec::new(),
            }),
        };
        Ok((successor, outcome_ids))
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
        if execution.core.state.memory().has_pending_heap_allocation() {
            // A pending malloc result is an independent execution split. The
            // current branch container owns one C-condition split, not the
            // Cartesian product of both; compatibility execution retains
            // that frontier from the unchanged Proof root.
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
                self.step_error(format!(
                    "could not resolve source statement({statement_index})"
                ))
            })?;
        Ok(matches!(source_region.kind, SourceStatementKind::If { .. }))
    }

    /// Resolves a Surface Click statement region against this proof's source
    /// layout without exposing the mutable frontier or check metadata.
    pub(in crate::surface::proof) fn resolve_statement_target(
        &self,
        region: &CodeRegionRef,
    ) -> Result<usize, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`execute_until` requires an execution proof"));
        };
        let CodeRegion::Statement(statement_index) = resolve_code_region_ref(
            context.function_block,
            region,
            context.claim_label,
            context.tactic_index,
        )?
        else {
            return Err(self.step_error("`execute_until` expects a statement region"));
        };
        Ok(statement_index)
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

/// The premise anchor of an execution frontier: the entry of the last
/// executed statement (or the most recent recorded program point), with an
/// exit marker mapped to the matching recorded entry. Premises established
/// across one statement use its entry snapshot as their stable Surface Click
/// spelling; a retained Proof may carry the equivalent exit snapshot as its most
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
                .recorded_snapshots
                .keys()
                .rev()
                .find_map(|selector| match selector {
                    SnapshotSelector::ProgramPoint(point) => Some(point.clone()),
                    SnapshotSelector::Mark(_) => None,
                })
        })?;
    if anchor.kind != ProgramPointKind::Exit {
        return Some(anchor);
    }
    let entry = ProgramPointRef {
        region: anchor.region.clone(),
        kind: ProgramPointKind::Entry,
    };
    Some(
        if execution
            .presentation
            .recorded_snapshots
            .contains_key(&entry)
        {
            entry
        } else {
            anchor
        },
    )
}
