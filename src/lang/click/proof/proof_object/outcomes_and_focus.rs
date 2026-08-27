//! Goal focus, outcome snapshots, and exit queries.

use super::*;

impl<'a> Proof<'a> {
    /// Whether this execution proof has reached the function-exit frontier.
    ///
    /// This is a read-only smart-tactic query: it exposes no replay state and
    /// grants no authority to advance the proof.
    pub(in crate::lang::click::proof) fn is_at_function_exit(&self) -> bool {
        self.execution()
            .is_some_and(|execution| execution.frontier.is_at_function_exit())
    }

    /// Whether the focused execution frontier still owns a function effect
    /// goal: an effect-claim site's selected effect, or every effect of a
    /// grouped contract with effect clauses. A frame applied here is a
    /// checked step on that goal; without one, a frame is an ordered
    /// outcome operation for the drain.
    pub(in crate::lang::click::proof) fn frontier_owns_effect_goal(&self) -> bool {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return false;
        };
        let effect_count = context.function_block.effects().len();
        match self.focused_goal() {
            Some(Goal::Frontier(FrontierGoal { selection, .. })) => match selection {
                EffectGoalSelection::None => false,
                EffectGoalSelection::One(index) => *index < effect_count,
                EffectGoalSelection::All => effect_count > 0,
            },
            _ => false,
        }
    }

    /// The focused execution rests at its bounded region's typed boundary:
    /// its own statement tree is exhausted and no code lies beyond it.
    pub(in crate::lang::click::proof) fn is_at_region_boundary(&self) -> bool {
        self.execution()
            .is_some_and(|execution| execution.frontier.is_at_region_boundary())
    }

    /// Whether checked execution retained an infeasible sibling as an empty
    /// logical branch. Direct drivers use this Proof-owned structural fact to
    /// keep unsupported empty-leaf shapes on their compatibility routes.
    pub(in crate::lang::click::proof) fn has_empty_execution_branch_leaf(&self) -> bool {
        self.execution()
            .is_some_and(|execution| execution.has_empty_execution_branch_leaf)
    }

    /// Every open goal in this proof, in stable id order.
    pub(in crate::lang::click::proof) fn goals(&self) -> impl Iterator<Item = GoalId> + '_ {
        self.state.goals.open.keys().copied()
    }

    /// The open function-outcome goal derived for one checked path, if this
    /// proof owns it. Path indices are the checked execution's deterministic
    /// path order, recorded on each goal at derivation.
    pub(in crate::lang::click::proof) fn outcome_goal_for_path(
        &self,
        path_index: usize,
    ) -> Option<GoalId> {
        self.state
            .goals
            .open
            .iter()
            .find_map(|(id, goal)| match goal {
                Goal::FunctionOutcome(outcome) if outcome.path_index == path_index => Some(*id),
                _ => None,
            })
    }

    pub(in crate::lang::click::proof) fn focused_outcome_snapshot(
        &self,
    ) -> Result<CFunctionOutcome, ClickError> {
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("an outcome snapshot requires a focused outcome goal"));
        };
        Ok(CFunctionOutcome::Return {
            value: (*goal.point.result).clone(),
            state: (*goal.point.state).clone(),
        })
    }

    pub(in crate::lang::click::proof) fn checked_outcome_frame_authority(
        &self,
    ) -> Result<CheckedFrameAuthority, ClickError> {
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("frame authority requires a focused outcome goal"));
        };
        if !matches!(goal.selection, EffectGoalSelection::None) || goal.checked_effects.is_empty() {
            return Err(self.step_error("the focused outcome has no checked frame authority"));
        }
        Ok(CheckedFrameAuthority::new((*goal.checked_effects).clone()))
    }

    /// Updates the focused outcome goal's immutable result/state snapshot
    /// after a separately checked resource transition.
    pub(in crate::lang::click::proof) fn with_outcome_snapshot(
        &self,
        outcome: &CFunctionOutcome,
    ) -> Result<Self, ClickError> {
        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(self.step_error("an outcome snapshot requires a return outcome"));
        };
        let point = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => goal.point.as_ref(),
            Some(Goal::Proposition(goal)) => goal.outcome.as_deref().ok_or_else(|| {
                self.step_error("an outcome snapshot requires a result-aware proposition goal")
            })?,
            _ => {
                return Err(self.step_error("an outcome snapshot requires a focused outcome goal"));
            }
        };
        let mut point = point.clone();
        // Resource-producing post-execution tactics can replace the outcome
        // state after this goal was derived. Carry that persistent snapshot
        // root forward; otherwise later
        // checked point operations lower resource counts against the stale
        // pre-fold state. CState's components are shared immutable roots, so
        // this update is constant-size rather than a resource/history
        // materialization.
        point.result = Arc::new(value.clone());
        point.state = state.clone().into();
        let point = Arc::new(point);
        let mut state = (*self.state).clone();
        state.goals = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => {
                let mut updated = goal.clone();
                updated.point = point;
                state
                    .goals
                    .replace_at(self.focused, Goal::FunctionOutcome(updated))
            }
            Some(Goal::Proposition(goal)) => {
                let mut updated = goal.clone();
                updated.outcome = Some(point);
                state
                    .goals
                    .replace_at(self.focused, Goal::Proposition(updated))
            }
            _ => unreachable!("the outcome point was selected above"),
        };
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(state),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Installs an already checked post-execution fact context on the focused
    /// outcome goal while preserving retained Surface provenance for facts
    /// that survive the transition.
    pub(in crate::lang::click::proof) fn with_checked_outcome_facts(
        &self,
        facts: &[Proposition],
    ) -> Result<Self, ClickError> {
        let point = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => goal.point.as_ref(),
            Some(Goal::Proposition(goal)) => goal.outcome.as_deref().ok_or_else(|| {
                self.step_error("outcome facts require a result-aware proposition goal")
            })?,
            _ => return Err(self.step_error("outcome facts require a focused outcome goal")),
        };
        // Path preparation can unfold predicate requirements in place. Keep
        // the point view's requirement prefix aligned with the checked fact
        // context so indexed `choose` sources use that exact form.
        let requires = match self.context.as_ref() {
            ProofContext::Execution(context) => context.function_block.requires().len(),
            _ => 0,
        };
        let mut point = point.clone();
        point.requirement_facts = Arc::new(facts[..requires.min(facts.len())].to_vec());
        let point = Arc::new(point);
        let mut state = (*self.state).clone();
        state.goals = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => {
                let mut updated = goal.clone();
                updated.point = point;
                state
                    .goals
                    .replace_at(self.focused, Goal::FunctionOutcome(updated))
            }
            Some(Goal::Proposition(goal)) => {
                let mut updated = goal.clone();
                updated.outcome = Some(point);
                state
                    .goals
                    .replace_at(self.focused, Goal::Proposition(updated))
            }
            _ => unreachable!("the outcome point was selected above"),
        };
        state.goals = state.goals.with_facts_at(
            self.focused,
            self.facts().resync_ordered_preserving_provenance(facts),
        );
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(state),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Returns a handle addressing another open goal of the same state.
    ///
    /// Focus is a cursor: the returned handle shares this proof's semantic
    /// state and provenance, and checked operations through it advance
    /// exactly the addressed goal.
    /// The single open goal's id, when exactly one goal remains. Split
    /// regressions use it to name the pre-split obligation.
    #[cfg(test)]
    pub(super) fn sole_goal_id(&self) -> Option<GoalId> {
        let mut ids = self.goals();
        let sole = ids.next()?;
        ids.next().is_none().then_some(sole)
    }

    pub(in crate::lang::click::proof) fn focus(&self, goal: GoalId) -> Result<Self, ClickError> {
        if self.state.goals.get(goal).is_none() {
            return Err(self.step_error(format!("goal {goal:?} is not open in this proof")));
        }
        let mut focused = self.clone();
        focused.focused = goal;
        Ok(focused)
    }

    /// Derives the typed function-outcome goal set from a function-exit
    /// frontier: the successor retires the focused frontier goal and opens
    /// one outcome goal per feasible checked returning path, in the checked
    /// execution's deterministic path order. Candidate paths whose exact
    /// facts contradict the enclosing proof facts contribute no goal.
    ///
    /// Each outcome goal owns its path's result value, post-outcome C state,
    /// and fact context (the frontier's facts extended by only that path's
    /// own facts), and borrows the frontier's snapshot by identity for
    /// lowering. A path proved non-returning contributes no goal. The
    /// returned handle addresses the first outcome goal; `focus` reaches its
    /// siblings. Result and effect continuations consume these goals
    /// directly rather than converting through the legacy replay adapter.
    pub(in crate::lang::click::proof) fn focus_function_outcomes(
        &self,
        requirement_facts: Arc<Vec<Proposition>>,
    ) -> Result<(Self, Vec<GoalId>), ClickError> {
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            return Err(self.step_error("outcome goals require an open execution frontier"));
        };
        let effect_selection = frontier.selection;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let checked = execution.frontier.execution().ok_or_else(|| {
            self.step_error("outcome goals require execution to have reached function exit")
        })?;
        let frontier_snapshot = frontier.context.execution.clone();
        let frontier_unfolds = frontier.context.unfolded_predicates.clone();
        let frontier_surface = frontier_snapshot
            .as_ref()
            .map(|execution| execution.surface_propositions.clone())
            .unwrap_or_default();
        let frontier_anchor = frontier_snapshot
            .as_ref()
            .and_then(|execution| frontier_premise_anchor(execution));
        let requirement_surfaces = match self.context.as_ref() {
            ProofContext::Execution(context) => requirement_facts
                .iter()
                .zip(context.function_block.requires())
                .filter_map(|(fact, requirement)| {
                    requirement
                        .proposition()
                        .cloned()
                        .map(|surface| (fact.clone(), surface))
                })
                .fold(PersistentMap::default(), |index, (fact, surface)| {
                    index.with_inserted(fact, surface)
                }),
            _ => PersistentMap::default(),
        };
        let requirement_surfaces = Arc::new(requirement_surfaces);
        let mut goals = self.state.goals.discharge_at(self.focused);
        let mut outcome_ids = Vec::new();
        for (path_index, path) in checked.paths().iter().enumerate() {
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
                .any(|fact| self.facts().directly_conflicts_with(fact.proposition()))
            {
                continue;
            }
            let (result, state) = match path.outcome() {
                CFunctionOutcome::Return { value, state } => (value.clone(), state.clone()),
                // A path proved non-returning owes no outcome judgment.
                CFunctionOutcome::VerificationDiverges => continue,
                CFunctionOutcome::UndefinedBehavior(_) | CFunctionOutcome::RuntimeError(_) => {
                    return Err(self.step_error(format!(
                        "outcome goals require a verifying execution, but path {path_index} failed"
                    )));
                }
            };
            // The goal owns the path-local pure facts. Effect-region facts
            // stay in the execution snapshot and are consumed only by the
            // checked point operations that explicitly cross effects.
            let mut facts = self.facts().clone();
            for fact in path.facts() {
                facts = facts.with_fact(fact.proposition().clone());
            }
            let execution_facts = path.execution_facts();
            let id = GoalId(goals.next_id);
            goals = ProofGoals {
                open: goals.open.with_inserted(
                    id,
                    Goal::FunctionOutcome(OutcomeGoal {
                        path_index,
                        selection: effect_selection,
                        checked_effects: Arc::new(Vec::new()),
                        point: Arc::new(OutcomePointData {
                            result: Arc::new(result),
                            state: state.into(),
                            surface_propositions: frontier_surface.clone(),
                            effect_facts: Arc::new(execution_facts),
                            execution_pure_facts: Arc::new(path.facts().to_vec()),
                            premise_anchor: frontier_anchor.clone(),
                            requirement_facts: requirement_facts.clone(),
                            requirement_surfaces: requirement_surfaces.clone(),
                            branch_decisions: execution
                                .outcome_branch_decisions
                                .get(path_index)
                                .cloned()
                                .unwrap_or_else(|| execution.branch_decisions.clone()),
                        }),
                        context: GoalContext {
                            facts,
                            unfolded_predicates: frontier_unfolds.clone(),
                            execution: frontier_snapshot.clone(),
                        },
                    }),
                ),
                next_id: goals.next_id + 1,
            };
            outcome_ids.push(id);
        }
        if outcome_ids.is_empty() {
            return Err(self.step_error("outcome goals require at least one returning path"));
        }
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),

                goals,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            // A structural marker records the derivation; the certificate
            // step vocabulary for consuming outcome goals arrives with the
            // drain migration.
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: outcome_ids[0],
        };
        Ok((successor, outcome_ids))
    }

    /// Whether the checked execution frontier is a structural C `if`.
    ///
    /// Smart `execute` uses this read-only query to distinguish a structural
    /// frontier from an ordinary statement whose indexed candidate simply did
    /// not apply. It grants no branch authority and performs no transition.
    pub(in crate::lang::click::proof) fn is_at_execution_branch(&self) -> Result<bool, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its semantic frontier"))?;
        if execution.frontier.is_at_function_exit() {
            return Ok(false);
        }
        if execution.state.memory().has_pending_heap_allocation() {
            // A pending malloc result is an independent execution split. The
            // current branch container owns one C-condition split, not the
            // Cartesian product of both; compatibility execution retains
            // that frontier from the unchanged Proof root.
            return Ok(false);
        }
        let Some(context) = self.execution_context() else {
            return Ok(false);
        };
        let statement_index = execution.frontier.next_statement_index;
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
    /// layout without exposing the mutable frontier or replay metadata.
    pub(super) fn resolve_statement_target(
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
    pub(super) fn current_statement_index(&self) -> Result<Option<usize>, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its semantic frontier"))?;
        Ok((!execution.frontier.is_at_function_exit())
            .then_some(execution.frontier.next_statement_index))
    }
}

/// The premise anchor of an execution frontier: the entry of the last
/// executed statement (or the most recent recorded program point), with an
/// exit marker mapped to the matching recorded entry. Premises established
/// across one statement use its entry snapshot as their stable Surface Click
/// spelling; a retained Proof may carry the equivalent exit point as its most
/// recent provenance marker. Outcome points and mid-execution judgments
/// anchor their premises by this one law.
pub(super) fn frontier_premise_anchor(execution: &ExecutionProofState) -> Option<ProgramPointRef> {
    let anchor = execution
        .replay
        .proof_certificate_builder
        .last_step_entry
        .clone()
        .or_else(|| execution.program_point_states.keys().next_back().cloned())?;
    if anchor.kind != ProgramPointKind::Exit {
        return Some(anchor);
    }
    let entry = ProgramPointRef {
        region: anchor.region.clone(),
        kind: ProgramPointKind::Entry,
    };
    Some(
        execution
            .program_point_states
            .contains_key(&entry)
            .then_some(entry)
            .unwrap_or(anchor),
    )
}
