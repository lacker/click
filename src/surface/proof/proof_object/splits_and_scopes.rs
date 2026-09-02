//! Logical/execution/outcome splits, joins, and `have`/`open` scopes.

use super::*;

impl<'a> Proof<'a> {
    /// Splits the focused branch proposition goal into two labeled sibling case
    /// goals inside this same proof state.
    ///
    /// This is the in-`Proof` form of `cases`: the parent obligation's id is
    /// retired by the split, each arm owns the same claim under its exact
    /// disjunct in its own path-local context, and both siblings coexist in
    /// one goal collection — arms are proven by focusing each recorded id in
    /// turn on one lineage. The split marker node records this split
    /// instance; the join accepts only derivations that pass through it.
    pub(in crate::surface::proof) fn split_focused_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let kernel = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        let (state, split, ids) = self
            .state
            .split_proposition_cases(kernel)
            .map_err(|error| match error {
                PropositionSplitError::Completed => {
                    self.step_error("`cases` follows a completed proof")
                }
                PropositionSplitError::NotProposition => {
                    self.step_error("`cases` requires a proposition goal")
                }
                PropositionSplitError::MissingDisjunction(kernel) => self.step_error(format!(
                    "`cases` requires its exact disjunction as an available fact: {kernel:?}"
                )),
                PropositionSplitError::ExpectedDisjunction(kernel) => {
                    self.step_error(format!("`cases` requires a disjunction, got {kernel:?}"))
                }
                PropositionSplitError::NonComplementaryCases => {
                    unreachable!("cases does not supply complementary branch facts")
                }
            })?
            .into_parts();
        Ok((
            Self {
                context: self.context.clone(),
                state,
                // The marker records the split instance in provenance; its
                // identity is what the join verifies (identity rule 3).
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth,
                }),
            },
            split,
            ids,
        ))
    }

    /// Splits the focused branch proposition goal under a condition and its exact
    /// surface negation inside this same proof state: the in-`Proof` form of
    /// proof `if`. Unlike `cases`, the condition need not be an available
    /// fact beforehand.
    pub(in crate::surface::proof) fn split_focused_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let (state, split, ids) = self
            .state
            .split_proposition_if(then_fact, else_fact)
            .map_err(|error| match error {
                PropositionSplitError::Completed => {
                    self.step_error("`if` follows a completed proof")
                }
                PropositionSplitError::NotProposition => {
                    self.step_error("proof `if` requires a proposition goal")
                }
                PropositionSplitError::NonComplementaryCases => self.step_error(
                    "proof `if` condition and negation did not lower to complementary facts",
                ),
                PropositionSplitError::MissingDisjunction(_)
                | PropositionSplitError::ExpectedDisjunction(_) => {
                    unreachable!("proof if does not require a disjunction")
                }
            })?
            .into_parts();
        Ok((
            Self {
                context: self.context.clone(),
                state,
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth,
                }),
            },
            split,
            ids,
        ))
    }

    /// Splits a proof path condition that exactly names the current C `if`
    /// and applies each arm's leading source step as a checked `Step` on
    /// that focused branch Proof, which decides the C `if` from the assumed case. The returned arms remain
    /// proof cases, so their source scopes may continue through the C join;
    /// only the branch-entry transition is selected here.
    pub(in crate::surface::proof) fn try_split_source_successor_if(
        &self,
        condition: &ClickProposition,
        arm_steps: [(usize, usize); 2],
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let statement_index = execution.core.frontier.next_statement_index;
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(context),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "source proof `if`",
        )?;
        let CStatement::If {
            condition: c_condition,
            ..
        } = statement
        else {
            return Ok(None);
        };
        let source_fact = self.lower_surface_proposition(condition, "proof `if` condition")?;
        let c_surface = surface_c_condition(&c_condition);
        let c_fact = self.lower_surface_proposition(&c_surface, "current C `if` condition")?;
        if !path_condition_equivalent(&source_fact, &c_fact) {
            return Ok(None);
        }

        let (split, mut record) = self.split_focused_execution_if(condition.clone())?;
        record.surface_condition = surface_at_snapshot(
            &c_surface,
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let mut advanced = split;
        for (arm_index, take_then) in [(0usize, true), (1usize, false)] {
            let (tactic_index, source_index) = arm_steps[arm_index];
            advanced = advanced
                .focus_execution_if_arm(&record, take_then)?
                .apply_step_at(ProofStep::Step, tactic_index, source_index)?;
        }
        Ok(Some((advanced, record)))
    }

    /// Splits one retained execution frontier under an exhaustive proof-level
    /// condition. Both arms share the already-checked C state and receive only
    /// their respective logical polarity; subsequent statement steps remain
    /// independently checked on each sibling.
    pub(in crate::surface::proof) fn split_focused_execution_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let parent_execution = branch_state
            .execution
            .clone()
            .expect("an execution frontier owns its checked state");
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("an execution frontier has an execution context")
        };
        let at_function_entry = parent_execution.core.frontier.is_at_function_entry();
        let arm_presentation = |surface_fact: ClickProposition, fact: &Proposition, value: bool| {
            let mut presentation = parent_execution.presentation.clone();
            presentation
                .surface_propositions
                .record_lowering(&surface_fact, fact)?;
            presentation.case_assumptions.push(CaseAssumption {
                tactic_index: context.tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(fact.clone()),
                at_function_entry,
            });
            Ok(presentation)
        };
        let presentations = [
            arm_presentation(condition.clone(), &then_fact, true)?,
            arm_presentation(else_surface, &else_fact, false)?,
        ];
        let (state, split, ids, path_facts) = self
            .state
            .split_frontier_if(then_fact, else_fact, presentations)
            .map_err(|error| match error {
                FrontierSplitError::Completed => {
                    self.step_error("proof `if` follows a completed proof")
                }
                FrontierSplitError::NotFrontier => self
                    .step_error("proof `if` cannot advance C execution inside a proposition proof"),
                FrontierSplitError::MissingExecution => {
                    self.step_error("execution-frontier proof lost its semantic state")
                }
                FrontierSplitError::NonComplementaryCases => self.step_error(
                    "proof `if` condition and negation did not lower to complementary facts",
                ),
                FrontierSplitError::MissingDisjunction(_)
                | FrontierSplitError::ExpectedDisjunction(_) => {
                    unreachable!("proof if does not require a disjunction")
                }
            })?
            .into_parts_with_facts();
        let then_branch = state
            .open_branches()
            .get(ids[0])
            .expect("the kernel returned its open then branch");
        let else_branch = state
            .open_branches()
            .get(ids[1])
            .expect("the kernel returned its open else branch");
        let then_facts = then_branch.state.facts.clone();
        let else_facts = else_branch.state.facts.clone();
        let then_execution = then_branch
            .state
            .execution
            .clone()
            .expect("a kernel frontier split retains then execution");
        let else_execution = else_branch
            .state
            .execution
            .clone()
            .expect("a kernel frontier split retains else execution");
        let successor = Self {
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        };
        let record = ExecutionProofCaseSplit {
            marker: successor.checkpoint(),
            split,
            arm_branches: ids,
            surface_condition: condition,
            base_facts: [then_facts, else_facts],
            base_executions: [then_execution, else_execution],
            path_facts,
            common_facts: branch_state.facts.clone(),
            parent_unfolds: branch_state.unfolded_predicates.clone(),
            parent_execution: parent_execution.clone(),
            execution_start_state: parent_execution
                .core
                .frontier
                .execution_start_state(&parent_execution.core.state)
                .clone(),
        };
        Ok((successor, record))
    }

    /// Splits one retained execution frontier under the two exact disjuncts
    /// of an available proposition. The disjunction is checked once at the
    /// split; each sibling receives only its own disjunct in its persistent
    /// fact context, and no semantic state is exported to a construction cursor.
    pub(in crate::surface::proof) fn split_focused_execution_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, ExecutionLogicalCasesSplit<'a>), ClickError> {
        let lowered = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        let (state, split, ids, path_facts) = self
            .state
            .split_frontier_cases(lowered)
            .map_err(|error| match error {
                FrontierSplitError::Completed => {
                    self.step_error("`cases` follows a completed proof")
                }
                FrontierSplitError::NotFrontier => {
                    self.step_error("`cases` cannot advance C execution inside a proposition proof")
                }
                FrontierSplitError::MissingExecution => {
                    self.step_error("execution-frontier proof lost its semantic state")
                }
                FrontierSplitError::MissingDisjunction(lowered) => self.step_error(format!(
                    "`cases` requires its exact disjunction as an available fact: {lowered:?}"
                )),
                FrontierSplitError::ExpectedDisjunction(lowered) => {
                    self.step_error(format!("`cases` requires a disjunction, got {lowered:?}"))
                }
                FrontierSplitError::NonComplementaryCases => {
                    unreachable!("execution cases does not supply complementary branch facts")
                }
            })?
            .into_parts_with_facts();
        let successor = Self {
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        };
        let record = ExecutionLogicalCasesSplit {
            marker: successor.checkpoint(),
            split,
            arm_branches: ids,
            path_facts,
        };
        Ok((successor, record))
    }

    /// Focuses one arm of a logical execution-frontier `cases` split. The
    /// arm's exact disjunct is re-presented only as this focused branch operation's
    /// local fact delta.
    pub(in crate::surface::proof) fn focus_execution_cases_arm(
        &self,
        record: &ExecutionLogicalCasesSplit<'a>,
        take_left: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_left);
        let focused_branch = self.focus_branch(record.arm_branches[arm_index])?;
        let path_facts = record.path_facts[arm_index].clone();
        Ok(focused_branch.with_kernel_state(
            focused_branch
                .state
                .with_fact_deltas(path_facts.clone(), path_facts),
        ))
    }

    /// Applies one recursively driven logical `cases` operation over an
    /// execution frontier. Both callbacks must retire their sibling goals;
    /// the returned node retains one structured `Cases` provenance step.
    pub(in crate::surface::proof) fn apply_execution_cases_with<Left, Right>(
        self,
        disjunction: ClickProposition,
        apply_left: Left,
        apply_right: Right,
    ) -> Result<Self, ClickError>
    where
        Left: FnOnce(Self) -> Result<Self, ClickError>,
        Right: FnOnce(Self) -> Result<Self, ClickError>,
    {
        let (split, record) = self.split_focused_execution_cases(disjunction.clone())?;
        let left_done = apply_left(split.focus_execution_cases_arm(&record, true)?)?;
        let right_done = apply_right(left_done.focus_execution_cases_arm(&record, false)?)?;
        right_done.join_focused_cases(
            &record.marker,
            record.split,
            record.arm_branches,
            disjunction,
        )
    }

    /// Applies one recursively driven proof-level execution `if` as an
    /// audited sibling-goal operation. Each callback must retire exactly its
    /// selected arm, either with terminal checked steps or another invocation
    /// of this operation. The returned node retains the structured `If`
    /// provenance directly on this Proof lineage.
    pub(in crate::surface::proof) fn apply_execution_if_with<Then, Else>(
        self,
        condition: ClickProposition,
        apply_then: Then,
        apply_else: Else,
    ) -> Result<Self, ClickError>
    where
        Then: FnOnce(Self) -> Result<Self, ClickError>,
        Else: FnOnce(Self) -> Result<Self, ClickError>,
    {
        let (split, record) = self.split_focused_execution_if(condition.clone())?;
        let then_done = apply_then(split.focus_execution_if_arm(&record, true)?)?;
        let else_done = apply_else(then_done.focus_execution_if_arm(&record, false)?)?;
        else_done.join_focused_if(&record.marker, record.split, record.arm_branches, condition)
    }

    /// Joins a completed in-`Proof` `if` split with one structured `If`
    /// step, under the same rules as [`Self::join_focused_cases`].
    pub(in crate::surface::proof) fn join_focused_if(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        condition: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| ProofStep::If {
            condition,
            then_proof: Box::new(left),
            else_proof: Box::new(right),
        })
    }

    /// Joins a completed in-`Proof` case split: both recorded sibling goals
    /// must be discharged, the derivation must pass through the split's
    /// exact marker, and the retained certificate embeds each arm's steps
    /// partitioned by the per-step goal attribution recorded when they were
    /// applied — never inferred from final states.
    pub(in crate::surface::proof) fn join_focused_cases(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        disjunction: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| ProofStep::Cases {
            disjunction,
            left_proof: Box::new(left),
            right_proof: Box::new(right),
        })
    }

    /// Splits the steps recorded since `marker` into per-arm certificates by
    /// the goal attribution stamped on each node when it was applied. The
    /// derivation must pass through the split's exact marker (foreign splits
    /// of the same root collide numerically but fail pointer identity), and
    /// every step in the region must be attributed to one of the two
    /// recorded arms.
    pub(super) fn partition_steps_since(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
    ) -> Result<[Vec<ProofStep>; 2], ClickError> {
        let mut left_steps = Vec::new();
        let mut right_steps = Vec::new();
        let mut node = Some(self.node.clone());
        loop {
            let Some(current) = node else {
                return Err(self.step_error(format!(
                    "cannot join: the derivation did not pass through split {split:?}"
                )));
            };
            if Arc::ptr_eq(&current, &marker.node) {
                break;
            }
            if let Some(step) = &current.step {
                if current.focused_branch == ids[0] {
                    left_steps.push(step.as_ref().clone());
                } else if current.focused_branch == ids[1] {
                    right_steps.push(step.as_ref().clone());
                } else {
                    return Err(self.step_error(format!(
                        "cannot join: a step was attributed outside split {split:?}"
                    )));
                }
            }
            node = current.parent.clone();
        }
        left_steps.reverse();
        right_steps.reverse();
        Ok([left_steps, right_steps])
    }

    pub(super) fn join_focused_branch(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        step: impl FnOnce(ProofCertificate, ProofCertificate) -> ProofStep,
    ) -> Result<Self, ClickError> {
        let state = self
            .state
            .join_closed_split(split, ids, marker.node.focused_branch)
            .map_err(|error| match error {
                ProofJoinError::ArmIncomplete(arm) => {
                    let name = ["left", "right"][arm];
                    self.step_error(format!("cannot join `cases`: {name} arm is incomplete"))
                }
                ProofJoinError::InvalidSplit => {
                    self.step_error(format!("cannot join: invalid split identity {split:?}"))
                }
            })?;
        let [left_steps, right_steps] = self.partition_steps_since(marker, split, ids)?;
        let parent = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `cases`: the split marker lost its root")
        })?;
        Ok(Self {
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(parent.clone()),
                step: Some(Arc::new(step(
                    ProofCertificate::from_steps(left_steps),
                    ProofCertificate::from_steps(right_steps),
                ))),
                focused_branch: marker.node.focused_branch,
                depth: parent.depth + 1,
            }),
        })
    }

    /// Partitions an already-checked terminal execution by one proof-level
    /// condition. Every owned outcome must decide exactly one polarity; no
    /// path may be copied into both arms or silently discarded.
    /// Partitions an already-checked terminal execution by one proof-level
    /// condition into two sibling frontier goals inside this proof. Every
    /// owned outcome must decide exactly one polarity; no path may be
    /// copied into both arms or silently discarded. Unlike a proposition
    /// sibling split, the arms retain execution-frontier goals owning
    /// disjoint subsets of the checked execution, so branch-local facts
    /// justify terminal proof steps without being exposed to incompatible
    /// outcomes.
    pub(super) fn split_focused_outcome_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, OutcomeSplit<'a>), ClickError> {
        if self.state().open_branches().is_discharged() {
            return Err(self.step_error("execution outcome `if` follows a completed proof"));
        }
        let ProofContext::Execution(_) = self.context.as_ref() else {
            return Err(self.step_error("execution outcome `if` requires an execution proof"));
        };
        self.require_execution_frontier("execution outcome `if`")?;
        let root_execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution outcome `if` lost its semantic frontier"))?;
        if !root_execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error("execution outcome `if` requires function exit"));
        }
        let checked = root_execution.core.frontier.execution().ok_or_else(|| {
            self.step_error("execution outcome `if` has no checked execution paths")
        })?;
        let then_fact =
            self.lower_surface_proposition(&condition, "execution outcome condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact =
            self.lower_surface_proposition(&else_surface, "execution outcome negation")?;
        let shared_facts = self.facts().to_vec();
        type OutcomePath = (
            CFunctionOutcome,
            Vec<ExecutionPureFact>,
            Vec<ProofObligation>,
        );
        let mut partition_paths: [Vec<OutcomePath>; 2] = [Vec::new(), Vec::new()];
        let mut common_path_facts: [Option<Vec<Proposition>>; 2] = [None, None];

        for (path_index, path) in checked.paths().iter().enumerate() {
            let mut available = shared_facts.clone();
            let path_facts = path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            available.extend(path_facts.iter().cloned());
            let assumptions = assumptions_from_propositions(&available);
            let selects_then =
                exact_fact_is_available(&then_fact, &available) || assumptions.proves(&then_fact);
            let selects_else = exact_fact_is_available(&else_fact, &available)
                || assumptions.proves(&else_fact)
                || fact_conflicts_with_assumptions(&then_fact, &assumptions);
            let arm_index = match (selects_then, selects_else) {
                (true, false) => 0,
                (false, true) => 1,
                (false, false) => {
                    return Err(self.step_error(format!(
                        "execution path {path_index} does not decide outcome branch `{}`",
                        describe_click_proposition(&condition)
                    )));
                }
                (true, true) => {
                    return Err(self.step_error(format!(
                        "execution path {path_index} proves both sides of outcome branch `{}`",
                        describe_click_proposition(&condition)
                    )));
                }
            };
            match &mut common_path_facts[arm_index] {
                Some(common) => common.retain(|fact| path_facts.contains(fact)),
                slot @ None => *slot = Some(path_facts),
            }
            partition_paths[arm_index].push((
                path.outcome().clone(),
                path.execution_facts(),
                path.obligations().to_vec(),
            ));
        }
        if partition_paths.iter().any(Vec::is_empty) {
            return Err(self.step_error(
                "execution outcome `if` requires at least one checked path in each arm",
            ));
        }

        let execution_state = checked.state().clone();
        let function = checked.function().clone();
        let arguments = checked.arguments().to_vec();
        let polarity_facts = [then_fact, else_fact];
        let polarity_surfaces = [condition.clone(), else_surface];
        let Some(Obligation::Frontier(_)) = self.focused_obligation() else {
            unreachable!("the execution frontier requirement was checked above")
        };
        let ProofContext::Execution(execution_context) = self.context.as_ref() else {
            unreachable!("the execution context requirement was checked above")
        };
        let expected_effects = self.selected_effect_indices(execution_context)?;
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let parent_facts = branch_state.facts.clone();
        let parent_unfolds = branch_state.unfolded_predicates.clone();
        let parent_execution = branch_state
            .execution
            .clone()
            .expect("the execution frontier owns its semantic state");
        let mut path_facts: [Vec<Proposition>; 2] = [Vec::new(), Vec::new()];
        let mut arms = [None, None];
        for arm_index in 0..2 {
            let mut execution = root_execution.clone();
            let paths = std::mem::take(&mut partition_paths[arm_index]);
            execution.core.frontier.position = FrontierPosition::FunctionExit {
                execution: c_function_execution_candidates_from_outcomes(
                    execution_state.clone(),
                    function.clone(),
                    arguments.clone(),
                    paths,
                ),
            };
            execution
                .presentation
                .surface_propositions
                .record_lowering(&polarity_surfaces[arm_index], &polarity_facts[arm_index])?;

            let mut facts = parent_facts.clone();
            let mut added_facts = Vec::new();
            for fact in std::iter::once(&polarity_facts[arm_index])
                .chain(common_path_facts[arm_index].as_ref().into_iter().flatten())
            {
                if !facts.contains(fact) {
                    facts = facts.with_fact(fact.clone());
                    added_facts.push(fact.clone());
                }
            }
            path_facts[arm_index] = added_facts;
            arms[arm_index] = Some((facts, execution));
        }
        let [Some(then_arm), Some(else_arm)] = arms else {
            unreachable!("the checked outcome partition has exactly two arms")
        };
        let checked_facts = path_facts[0].clone();
        let published = self
            .state
            .publish_checked_frontier_split([then_arm, else_arm], path_facts.clone(), checked_facts)
            .map_err(|error| self.execution_update_error("outcome `if`", error))?;
        let (state, split, ids, _) = published.into_parts_with_facts();
        let successor = Self {
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        };
        let record = OutcomeSplit {
            marker: successor.checkpoint(),
            split,
            arm_branches: ids,
            condition,
            expected_effects,
            path_facts,
            parent_facts,
            parent_unfolds,
            parent_execution,
            root_post_execution_count: root_execution.presentation.post_execution_tactics.len(),
        };
        Ok((successor, record))
    }

    /// Focuses one recorded outcome-partition arm and installs that arm's
    /// entry fact delta as the proof's delta, as `focus_split_arm` does for
    /// C-branch siblings.
    pub(super) fn focus_outcome_arm(
        &self,
        record: &OutcomeSplit<'a>,
        arm_index: usize,
    ) -> Result<Self, ClickError> {
        let delta = record.path_facts[arm_index].clone();
        let state = self
            .state
            .focus_open_branch_with_fact_deltas(
                record.arm_branches[arm_index],
                delta.clone(),
                delta,
            )
            .map_err(|error| match error {
                ProofFocusError::NotOpen => self.step_error(format!(
                    "goal {:?} is not open in this proof",
                    record.arm_branches[arm_index]
                )),
                ProofFocusError::NotAllocated => {
                    unreachable!("open-branch focus reports only whether the branch is open")
                }
            })?;
        Ok(self.with_kernel_state(state))
    }

    /// Joins two exhaustive terminal outcome partitions after both sibling
    /// arms checked the same effect selection. Each arm may retain
    /// different simple evidence, but ordered finalization receives one
    /// authority and therefore performs the resource transition once per
    /// original path. The parent obligation resumes under its original id
    /// with its effect goal closed.
    pub(super) fn join_focused_outcome_if(
        &self,
        record: &OutcomeSplit<'a>,
    ) -> Result<Self, ClickError> {
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, record.arm_branches)?;
        let arm_certificates = [
            ProofCertificate::from_steps(then_steps),
            ProofCertificate::from_steps(else_steps),
        ];
        let mut checked_deferrals = Vec::with_capacity(2);
        for (name, id) in [
            ("then", record.arm_branches[0]),
            ("else", record.arm_branches[1]),
        ] {
            let Some(branch) = self.state().open_branches().get(id) else {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm is not an open execution frontier"
                )));
            };
            let Obligation::Frontier(frontier) = &branch.obligation else {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm is not an open execution frontier"
                )));
            };
            if !matches!(frontier.selection, EffectGoalSelection::None) {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not close its effect goal"
                )));
            }
            let execution = branch.state.execution.as_deref().ok_or_else(|| {
                self.step_error(format!(
                    "execution outcome {name} arm lost its semantic frontier"
                ))
            })?;
            if !execution.core.frontier.is_at_function_exit() {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not remain at function exit"
                )));
            }
            let mut added = execution
                .presentation
                .post_execution_tactics
                .iter()
                .skip(record.root_post_execution_count);
            let deferred = added.next().ok_or_else(|| {
                self.step_error(format!(
                    "execution outcome {name} arm retained no checked terminal operation"
                ))
            })?;
            if added.next().is_some() {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm retained more than one terminal operation"
                )));
            }
            let PostExecutionTactic::CheckedFrameUsing { authority, .. } = &deferred.tactic else {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not retain checked frame authority"
                )));
            };
            if !authority.matches(&record.expected_effects) {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm closed a different effect selection"
                )));
            }
            checked_deferrals.push(deferred.clone());
        }
        if checked_deferrals[0].tactic_index != checked_deferrals[1].tactic_index
            || checked_deferrals[0].source_index != checked_deferrals[1].source_index
        {
            return Err(self.step_error(
                "execution outcome arms attribute their frame to different source tactics",
            ));
        }

        let mut execution = (*record.parent_execution).clone();
        execution.presentation.defer_checked_post_execution(
            checked_deferrals[0].tactic_index,
            checked_deferrals[0].source_index,
            PostExecutionTactic::CheckedFrameUsing {
                authority: CheckedFrameAuthority::new(record.expected_effects.clone()),
                // The structured node below owns the two exact surface
                // forms. This deferral is semantic authority only.
                region: None,
                premises: Vec::new(),
                surface_tactics: None,
            },
        );
        let parent_goal = record.marker.node.focused_branch;
        let parent_node = record.marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join outcome `if`: the split marker lost its root")
        })?;
        let state = self
            .state
            .publish_checked_frontier_join(
                record.split,
                record.arm_branches,
                parent_goal,
                EffectGoalSelection::None,
                record.parent_facts.clone(),
                record.parent_unfolds.clone(),
                execution,
                Vec::new(),
                Vec::new(),
            )
            .map_err(|_| self.step_error("cannot join outcome `if`: invalid branch lineage"))?;
        let [then_certificate, else_certificate] = arm_certificates;
        Ok(Self {
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(parent_node.clone()),
                step: Some(Arc::new(ProofStep::If {
                    condition: record.condition.clone(),
                    then_proof: Box::new(then_certificate),
                    else_proof: Box::new(else_certificate),
                })),
                focused_branch: parent_goal,
                depth: parent_node.depth + 1,
            }),
        })
    }

    /// Opens a nested proof for one surface proposition. The body has a fresh
    /// provenance root but shares the persistent semantic fact index and
    /// immutable checking context with its enclosing proof.
    ///
    /// A fixed-state proof may open `have` either while refining a proposition or
    /// from its initial result frontier. The latter is the audited way for
    /// grouped contract finalization to prove one obligation, publish it as a
    /// checked fact, and then prove a dependent obligation without rebuilding
    /// or mutating an external fact context.
    pub(in crate::surface::proof) fn begin_have(
        &self,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        if self.state().open_branches().is_discharged() {
            return Err(self.step_error("`have` follows a completed proof"));
        }
        match (self.focused_obligation(), self.context.as_ref()) {
            (Some(Obligation::Proposition(_) | Obligation::FunctionOutcome(_)), _) => {}
            (
                Some(Obligation::Frontier(_)),
                ProofContext::FixedState(_) | ProofContext::Execution(_),
            ) => {}
            _ => {
                return Err(
                    self.step_error("`have` requires a proposition or fixed-state proof context")
                );
            }
        }
        let kernel = self.lower_surface_goal(&proposition, "`have` proposition")?;
        // A post-execution unfold lets a predicate-call `have` prove the
        // predicate through its structural body. Pair that body kernel with
        // the same unfolded Surface view so `intro` retains binder names and
        // subsequent proof steps serialize an independently checkable
        // proof. Joining still publishes the opaque `kernel` named by the
        // enclosing Have step.
        let structural_proposition = if let ClickProposition::PredicateCall { name, .. } =
            &proposition
            && self.focused_branch_unfolds().contains(name)
        {
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::FixedState(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let active_unfolds = self.focused_branch_unfolds().to_vec();
            unfold_structural_invariant_proposition(
                predicate_environment,
                &proposition,
                &active_unfolds,
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `have` goal: {message}"))
            })?
        } else {
            proposition.clone()
        };
        let body_kernel = if structural_proposition == proposition {
            kernel.clone()
        } else {
            self.lower_surface_goal(&structural_proposition, "`have` body")?
        };
        // A `have` stated at an execution frontier proves its goal from the
        // frontier's facts alone; the selected-separation materialization
        // below serves outcome and fixed-state judgments, whose separation goals
        // are read from retained resources rather than derived in the body.
        let at_frontier = matches!(self.focused_obligation(), Some(Obligation::Frontier(_)));
        let mut body_facts = if at_frontier {
            self.facts().clone()
        } else {
            self.facts().with_selected_resource_separation(&body_kernel)
        };
        // A `have` stated at an execution frontier may use the frontier's
        // effect facts exactly as the shared mid-execution law offers them.
        if at_frontier && let Some(execution) = self.execution() {
            for fact in execution.core.effect_facts.iter() {
                if !body_facts.contains(fact.proposition()) {
                    body_facts = body_facts.with_fact(fact.proposition().clone());
                }
            }
        }
        let selected_surface_separation = match &structural_proposition {
            ClickProposition::Separate { .. } => true,
            ClickProposition::At { proposition, .. } => {
                matches!(proposition.as_ref(), ClickProposition::Separate { .. })
            }
            _ => false,
        };
        if !at_frontier
            && selected_surface_separation
            && !body_facts.contains(&body_kernel)
            && body_facts.assumptions().proves(&body_kernel)
        {
            body_facts = body_facts.with_fact(body_kernel.clone());
        }
        for name in self.focused_branch_unfolds().iter() {
            let recorded_bodies = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::FixedState(context) => context
                    .surface_propositions
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => self
                    .outcome_fixed_state_view()
                    .into_iter()
                    .flat_map(|view| view.surface_propositions.kernels_written_by_predicate(name))
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            for recorded in recorded_bodies {
                if matches!(recorded, Proposition::ForAll { .. })
                    && body_facts.contains_top_level(&recorded)
                {
                    body_facts = body_facts.with_predicate_unfold_fact(recorded);
                }
            }
        }
        let body_context = BranchState {
            facts: body_facts,
            unfolded_predicates: self.focused_branch_unfolds().clone(),
            execution: self.branch_execution().cloned(),
        };
        // An execution `have` borrows the current immutable frontier solely
        // as its proposition-lowering/theorem context, shared by identity on
        // the nested goal; a `have` stated at a function outcome borrows that
        // outcome's result-aware outcome proof data the same way. The nested goal
        // cannot publish a changed frontier or outcome: `join` restores the
        // exact root state and exposes only the stated proposition.
        let mut body_goal = match self.focused_outcome_data() {
            Some(outcome_data) => OpenBranch::surface_proposition_at_outcome(
                body_context,
                outcome_data.clone(),
                body_kernel.clone(),
                structural_proposition,
            ),
            None => OpenBranch::surface_proposition_in(
                body_context,
                body_kernel,
                structural_proposition,
            ),
        };
        if let (Some(Obligation::Proposition(parent)), Obligation::Proposition(body)) =
            (self.focused_obligation(), &mut body_goal.obligation)
        {
            body.surface_bindings = parent.surface_bindings.clone();
        }
        let body = Proof {
            context: self.context.clone(),
            state: KernelProofObject::root(self.state().locals().clone(), body_goal),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
        };
        Ok(ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Have {
                proposition,
                kernel,
            }),
            body,
            introduced_facts: Vec::new(),
        })
    }

    /// Opens one composite resource body as an execution scope. Entry is an
    /// audited representation transition, not a separately serialized
    /// `unfold`; the child Proof starts fresh provenance and the eventual join
    /// records the child certificate inside one `Open` step.
    pub(in crate::surface::proof) fn begin_open(
        &self,
        resource: ResourceClause,
        source_index: usize,
    ) -> Result<ProofScope<'a>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`open` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`open`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error("`open` must begin before execution reaches function exit"));
        }
        let before_facts = self.facts().clone();
        let checked = open_composite_resource_for_proof(
            context.resource_environment,
            &resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.core.state).clone(),
            self.facts().clone(),
            &mut execution.presentation.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution
            .core
            .record_resource_rewrite(
                context.function,
                context.arguments,
                &before_facts,
                &checked.selected,
                &checked.state,
                &checked.facts,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "kernel rejected checked resource `open`: {message}"
                ))
            })?;
        execution.core.state = checked.state.into();
        let introduced_facts = checked.added_facts.clone();
        let state = self
            .state
            .publish_checked_frontier_transition(
                checked.facts,
                execution,
                checked.added_facts.clone(),
                checked.added_facts,
                false,
            )
            .map_err(|error| self.execution_update_error("`open`", error))?;
        let body = Proof {
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: 0,
            }),
        };
        Ok(ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Open {
                resource,
                source_index,
                preserve_exposed_body: checked.body_was_already_exposed,
            }),
            body,
            introduced_facts,
        })
    }
}
