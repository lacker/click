//! Checked execution statement steps and loop-invariant bundles.

use super::*;

impl<'a> Proof<'a> {
    pub(super) fn apply_execution_statement_step(
        &self,
        step: SimpleProofStep,
        premises: &[ClickProposition],
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step using` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`step using`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let checked = check_step_using_facts(
            &mut execution.replay,
            &mut execution.state,
            &self.facts(),
            premises,
            context.function_block,
            context.function,
            context.parsed_function,
            context.arguments,
            context.function_environment,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above");
        };
        let parent_execution = Arc::new(execution.clone());
        let execution_start_state = execution
            .replay
            .execution_start_state(&execution.state)
            .clone();
        let initial_continuation_depth = execution.replay.frontier.continuations.len();
        let make_goal = |checked: CheckedStatementStep| {
            let mut successor_execution = execution.clone();
            successor_execution.replay = checked.replay;
            successor_execution.state = checked.state.into();
            (
                Goal::Frontier(FrontierGoal {
                    selection: frontier.selection,
                    context: GoalContext {
                        facts: checked.facts,
                        unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                        execution: Some(Arc::new(successor_execution)),
                    },
                }),
                checked.added_facts,
                checked.path,
            )
        };

        let (goals, focused, added_facts) = match checked.len() {
            1 => {
                let (goal, added, path) = make_goal(
                    checked
                        .into_iter()
                        .next()
                        .expect("one checked successor was required"),
                );
                debug_assert!(path.is_none());
                (
                    self.state.goals.replace_at(self.focused, goal),
                    self.focused,
                    added,
                )
            }
            2 => {
                let mut by_polarity = [None, None];
                let mut condition = None;
                let mut common_added: Option<Vec<Proposition>> = None;
                for successor in checked {
                    let CheckedStatementStep {
                        replay,
                        state,
                        facts,
                        added_facts: added,
                        path,
                    } = successor;
                    let Some((path_condition, value)) = path else {
                        return Err(self
                            .step_error("statement successors omitted their certified partition"));
                    };
                    if let Some(condition) = &condition {
                        if condition != &path_condition {
                            return Err(self.step_error(
                                "statement successors used different partition conditions",
                            ));
                        }
                    } else {
                        condition = Some(path_condition.clone());
                    }
                    let slot = usize::from(!value);
                    let mut successor_execution = execution.clone();
                    successor_execution.replay = replay;
                    successor_execution.state = state.into();
                    let path_fact = Proposition::ConditionIs(path_condition, value);
                    if by_polarity[slot]
                        .replace((facts, Arc::new(successor_execution), vec![path_fact]))
                        .is_some()
                    {
                        return Err(
                            self.step_error("statement successors repeated one partition polarity")
                        );
                    }
                    if let Some(common) = &mut common_added {
                        common.retain(|fact| added.contains(fact));
                    } else {
                        common_added = Some(added);
                    }
                }
                let [Some(then_arm), Some(else_arm)] = by_polarity else {
                    return Err(self.step_error(
                        "statement successors did not cover both partition polarities",
                    ));
                };
                let condition = condition.expect("two successors recorded a condition");
                let common_added = common_added.unwrap_or_default();
                // Both call successors descend from the pre-call facts, but
                // their statement batches are siblings even when those
                // batches contain some equal propositions. Keep the actual
                // shared ancestor here; the terminal merge computes common
                // post-call facts output-sensitively from the two arm deltas.
                let common_facts = self.facts().clone();
                let split = SplitId(self.state.goals.next_id);
                let ids = [
                    GoalId(self.state.goals.next_id + 1),
                    GoalId(self.state.goals.next_id + 2),
                ];
                let partition = Arc::new(StatementSuccessorPartition {
                    split,
                    ids,
                    condition,
                    base_facts: [then_arm.0.clone(), else_arm.0.clone()],
                    base_executions: [then_arm.1.clone(), else_arm.1.clone()],
                    path_facts: [then_arm.2, else_arm.2],
                    common_facts,
                    parent_unfolds: frontier.context.unfolded_predicates.clone(),
                    parent_execution: parent_execution.clone(),
                    execution_start_state: execution_start_state.clone(),
                    initial_continuation_depth,
                });
                let goals = self.state.goals.split_at(
                    self.focused,
                    [
                        Goal::Frontier(FrontierGoal {
                            selection: frontier.selection,
                            context: GoalContext {
                                facts: then_arm.0,
                                unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                                execution: Some(Arc::new({
                                    let mut execution = (*then_arm.1).clone();
                                    execution.last_step_delta.statement_partition =
                                        Some(partition.clone());
                                    execution
                                })),
                            },
                        }),
                        Goal::Frontier(FrontierGoal {
                            selection: frontier.selection,
                            context: GoalContext {
                                facts: else_arm.0,
                                unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                                execution: Some(Arc::new({
                                    let mut execution = (*else_arm.1).clone();
                                    execution.last_step_delta.statement_partition = Some(partition);
                                    execution
                                })),
                            },
                        }),
                    ],
                );
                debug_assert_eq!(goals.0, split);
                debug_assert_eq!(goals.1, ids);
                let goals = goals.2;
                (goals, ids[0], common_added)
            }
            count => {
                return Err(self.step_error(format!(
                    "statement execution produced {count} certified successors; expected one successor or one binary partition"
                )));
            }
        };
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(added_facts.clone()),
                checked_facts: Arc::new(added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused: self.focused,
                depth: self.node.depth + 1,
            }),
            focused,
        })
    }

    pub(super) fn apply_execution_mark(&self, name: &str) -> Result<ProofState, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`mark` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`mark`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let point = ProgramPointRef {
            region: CodeRegionRef::Mark(name.to_string()),
            kind: ProgramPointKind::Entry,
        };
        if execution.replay.program_point_states.contains_key(&point) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        execution
            .replay
            .program_point_states
            .insert(point, (*execution.state).clone());
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_frontier_at(
                self.focused,
                self.facts().clone(),
                execution,
            ),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    pub(super) fn apply_close_invariants(&self) -> Result<ProofState, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`close_invariants` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`close_invariants`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if !execution.replay.loop_invariant_region {
            return Err(
                self.step_error("`close_invariants` is only available in a loop-region proof")
            );
        }
        if execution.replay.region_invariants_closed {
            return Err(
                self.step_error("the invariant bundle was closed more than once on one path")
            );
        }
        execution.replay.region_invariants_closed = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_frontier_at(
                self.focused,
                self.facts().clone(),
                execution,
            ),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    /// Checks the complete loop-invariant bundle at this back edge and
    /// retains `close_invariants` when the source path has not already
    /// supplied it.
    ///
    /// The legacy source driver may arrive with the surface closer already
    /// reflected in cursor metadata. That metadata is not authority for the
    /// invariant judgment: this operation always performs the kernel check
    /// against the Proof-owned state and facts before accepting the path.
    pub(in crate::lang::click::proof) fn certify_loop_invariant_bundle(
        &self,
        loop_entry_state: &CState,
        invariant_checks: &[CLoopInvariantCheck],
    ) -> Result<Self, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("loop invariant closure requires an execution proof"));
        }
        self.require_execution_frontier("loop invariant closure")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop invariant closure lost its execution state"))?;
        if !execution.replay.loop_invariant_region {
            return Err(self.step_error("loop invariant closure requires a loop-region proof"));
        }

        let mut closer_facts = self.facts().to_vec();
        closer_facts.extend(
            execution
                .replay
                .effect_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        closer_facts.extend(crate::kernel::certified_store_equations(
            &execution.replay.effect_facts,
        ));
        c_loop_invariants_hold_at_back_edge_using(
            &execution.state,
            loop_entry_state,
            invariant_checks,
            &assumptions_from_propositions(&closer_facts),
        )
        .map_err(|message| self.step_error(format!("invariant bundle: {message}")))?;

        if execution.replay.region_invariants_closed {
            Ok(self.clone())
        } else {
            self.apply_step(SimpleProofStep::CloseInvariants)
        }
    }
}
