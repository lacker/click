//! Logical/execution/outcome splits, joins, and `have`/`open` scopes.

use super::*;

impl<'a> Proof<'a> {
    /// Splits the focused proposition goal into two labeled sibling case
    /// goals inside this same proof state.
    ///
    /// This is the in-`Proof` form of `cases`: the parent obligation's id is
    /// retired by the split, each arm owns the same claim under its exact
    /// disjunct in its own path-local context, and both siblings coexist in
    /// one goal collection — arms are proven by focusing each recorded id in
    /// turn on one lineage. The split marker node records this split
    /// instance; the join accepts only derivations that pass through it.
    pub(in crate::lang::click::proof) fn split_focused_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, SplitId, [GoalId; 2]), ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`cases` follows a completed proof"));
        }
        let Some(Goal::Proposition(goal)) = self.focused_goal() else {
            return Err(self.step_error("`cases` requires a proposition goal"));
        };
        let kernel = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        if !self.facts().contains(&kernel) {
            return Err(self.step_error(format!(
                "`cases` requires its exact disjunction as an available fact: {kernel:?}"
            )));
        }
        let Proposition::Or(left, right) = kernel else {
            return Err(self.step_error(format!("`cases` requires a disjunction, got {kernel:?}")));
        };
        let arm = |disjunct: Proposition| {
            Goal::Proposition(PropositionGoal {
                kernel: goal.kernel.clone(),
                surface: goal.surface.clone(),
                surface_bindings: goal.surface_bindings.clone(),
                context: GoalContext {
                    facts: goal.context.facts.with_fact(disjunct),
                    unfolded_predicates: goal.context.unfolded_predicates.clone(),
                    execution: goal.context.execution.clone(),
                },
                outcome: goal.outcome.clone(),
            })
        };
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [arm(*left), arm(*right)]);
        Ok((
            Self {
                context: self.context.clone(),
                state: Arc::new(ProofState {
                    locals: self.state.locals.clone(),
                    goals,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                }),
                // The marker records the split instance in provenance; its
                // identity is what the join verifies (identity rule 3).
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused: self.focused,
                    depth: self.node.depth,
                }),
                focused: ids[0],
            },
            split,
            ids,
        ))
    }

    /// Splits the focused proposition goal under a condition and its exact
    /// surface negation inside this same proof state: the in-`Proof` form of
    /// proof `if`. Unlike `cases`, the condition need not be an available
    /// fact beforehand.
    pub(in crate::lang::click::proof) fn split_focused_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, SplitId, [GoalId; 2]), ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`if` follows a completed proof"));
        }
        let Some(Goal::Proposition(goal)) = self.focused_goal() else {
            return Err(self.step_error("proof `if` requires a proposition goal"));
        };
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let arm = |fact: Proposition| {
            Goal::Proposition(PropositionGoal {
                kernel: goal.kernel.clone(),
                surface: goal.surface.clone(),
                surface_bindings: goal.surface_bindings.clone(),
                context: GoalContext {
                    facts: goal.context.facts.with_fact(fact),
                    unfolded_predicates: goal.context.unfolded_predicates.clone(),
                    execution: goal.context.execution.clone(),
                },
                outcome: goal.outcome.clone(),
            })
        };
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [arm(then_fact), arm(else_fact)]);
        Ok((
            Self {
                context: self.context.clone(),
                state: Arc::new(ProofState {
                    locals: self.state.locals.clone(),
                    goals,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                }),
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused: self.focused,
                    depth: self.node.depth,
                }),
                focused: ids[0],
            },
            split,
            ids,
        ))
    }

    /// Enters the exhaustive operational partition produced by the
    /// immediately preceding statement step. The proof `if` introduces no
    /// hypothesis of its own: both Surface polarities must lower to the exact
    /// condition already certified for the two successor frontiers.
    pub(in crate::lang::click::proof) fn enter_statement_successor_if(
        &self,
        condition: &ClickProposition,
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(partition) = self
            .execution()
            .and_then(|execution| execution.last_step_delta.statement_partition.clone())
        else {
            return Ok(None);
        };
        if self.focused != partition.ids[0]
            || !matches!(
                self.node.step.as_deref(),
                Some(SimpleProofStep::Step | SimpleProofStep::StepUsing(_))
            )
        {
            return Err(self
                .step_error("statement-successor `if` must immediately follow its checked step"));
        }
        let then_fact = self.lower_surface_proposition(condition, "proof `if` condition")?;
        let expected_then = Proposition::ConditionIs(partition.condition.clone(), true);
        if !path_condition_equivalent(&then_fact, &expected_then) {
            return Err(self.step_error(format!(
                "proof `if` condition does not name the preceding statement's certified partition: expected {expected_then:?}, got {then_fact:?}"
            )));
        }
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        // Lower both polarities against one semantic snapshot. Independent
        // lowering in the sibling successor can allocate different fresh
        // names for the same snapshot-qualified load, making an exact
        // certified partition appear different across its two arms.
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let expected_else = Proposition::ConditionIs(partition.condition.clone(), false);
        if !path_condition_equivalent(&else_fact, &expected_else) {
            return Err(self.step_error(format!(
                "proof `if` negation does not name the preceding statement's certified partition: expected {expected_else:?}, got {else_fact:?}"
            )));
        }

        let successor = Self {
            context: self.context.clone(),
            state: self.state.clone(),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.node.focused,
                depth: self.node.depth,
            }),
            focused: partition.ids[0],
        };
        let record = ExecutionProofCaseSplit {
            marker: successor.checkpoint(),
            split: partition.split,
            ids: partition.ids,
            surface_condition: condition.clone(),
            base_facts: partition.base_facts.clone(),
            base_executions: partition.base_executions.clone(),
            path_facts: partition.path_facts.clone(),
            common_facts: partition.common_facts.clone(),
            parent_unfolds: partition.parent_unfolds.clone(),
            parent_execution: partition.parent_execution.clone(),
            execution_start_state: partition.execution_start_state.clone(),
        };
        Ok(Some((successor, record)))
    }

    /// Splits a proof path condition that exactly names the current C `if`
    /// and applies each arm's leading source step as a checked `StepUsing`
    /// operation on that focused Proof. Smart entries arrive with the same
    /// explicit premises selected by their caller. The returned arms remain
    /// proof cases, so their source scopes may continue through the C join;
    /// only the branch-entry transition is selected here.
    pub(in crate::lang::click::proof) fn try_split_source_successor_if(
        &self,
        condition: &ClickProposition,
        arm_steps: [(usize, usize, Vec<ClickProposition>); 2],
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        // A preceding call or other multi-successor statement already owns a
        // certified partition. Its bounded product requires explicit source
        // evidence to exclude parent lanes; a fresh proof-case assumption
        // must not bypass that checked adapter merely because the following
        // C statement uses the same condition.
        if execution.last_step_delta.statement_partition.is_some() {
            return Ok(None);
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let statement_index = execution.replay.frontier.next_statement_index;
        let (_, _, statement, _) = next_top_level_statement_from_execution_point(
            &execution.replay,
            &execution.state,
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
        record.surface_condition = surface_with_source_site(
            &c_surface,
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let mut advanced = split;
        for (arm_index, take_then) in [(0usize, true), (1usize, false)] {
            let (tactic_index, source_index, premises) = &arm_steps[arm_index];
            advanced = advanced
                .focus_execution_if_arm(&record, take_then)?
                .apply_step_at(
                    SimpleProofStep::StepUsing(premises.clone()),
                    *tactic_index,
                    *source_index,
                )?;
        }
        Ok(Some((advanced, record)))
    }

    /// Tries the one bounded product needed when a proof-level condition does
    /// not name the immediately preceding statement partition. Each logical
    /// polarity is checked against both certified statement successors while
    /// crossing exactly the following C `if`. The speculative product is
    /// accepted only when each polarity immediately has exactly one survivor;
    /// no multi-frontier family is ever published to the proof state.
    pub(in crate::lang::click::proof) fn try_collapse_statement_successor_if(
        &self,
        condition: &ClickProposition,
        arm_steps: [(usize, Vec<ClickProposition>); 2],
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(partition) = self
            .execution()
            .and_then(|execution| execution.last_step_delta.statement_partition.clone())
        else {
            return Ok(None);
        };
        if self.focused != partition.ids[0]
            || !matches!(
                self.node.step.as_deref(),
                Some(SimpleProofStep::Step | SimpleProofStep::StepUsing(_))
            )
        {
            return Ok(None);
        }

        // The exact-partition adapter is both cheaper and more informative.
        // Leave that case to `enter_statement_successor_if`.
        let first_then = self.lower_surface_proposition(condition, "proof `if` condition")?;
        let expected_then = Proposition::ConditionIs(partition.condition.clone(), true);
        if path_condition_equivalent(&first_then, &expected_then) {
            return Ok(None);
        }

        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            return Ok(None);
        };
        let selection = frontier.selection;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        for execution in &partition.base_executions {
            let statement_index = execution.replay.frontier.next_statement_index;
            let Some(region) = execution.replay.source_layout.statement(statement_index) else {
                return Ok(None);
            };
            if !matches!(region.kind, SourceStatementKind::If { .. }) {
                return Ok(None);
            }
        }

        struct Survivor {
            base_facts: ProofFacts,
            base_execution: Arc<ExecutionProofState>,
            path_fact: Proposition,
            checked: CheckedStatementStep,
        }

        enum LaneDecision {
            Excluded,
            Survives(Proposition),
        }

        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let mut survivors: [Option<Survivor>; 2] = [None, None];
        for logical_arm in 0..2 {
            let take_then = logical_arm == 0;
            let surface_fact = if take_then {
                condition.clone()
            } else {
                else_surface.clone()
            };
            let mut survivor = None;
            for parent_arm in 0..2 {
                let focused = self.focus(partition.ids[parent_arm])?;
                let decision = crate::instrumentation::measure_operation(
                    context.function.name(),
                    context.claim_label,
                    "bounded statement-successor exclusion",
                    || -> Result<Option<LaneDecision>, ClickError> {
                        let fact = focused.lower_surface_proposition(
                            &surface_fact,
                            if take_then {
                                "proof `if` condition"
                            } else {
                                "proof `if` negation"
                            },
                        )?;
                        // Exclusion is intentionally bounded by source
                        // evidence. It asks only whether the arm polarity plus
                        // explicitly named premises refute one of this lane's
                        // exact certified partition facts; it never searches
                        // the ambient context for a global contradiction.
                        let mut evidence = Vec::new();
                        for premise in &arm_steps[logical_arm].1 {
                            let lowered = focused.lower_surface_proposition(
                                premise,
                                "bounded statement-successor premise",
                            )?;
                            if !partition.base_facts[parent_arm].contains(&lowered) {
                                return Ok(None);
                            }
                            if !evidence.contains(&lowered) {
                                evidence.push(lowered);
                            }
                        }
                        let premise_context = assumptions_from_propositions(&evidence);
                        if partition.path_facts[parent_arm].iter().any(|path_fact| {
                            fact_conflicts_with_assumptions(path_fact, &premise_context)
                        }) {
                            return Ok(None);
                        }
                        evidence.push(fact.clone());
                        let arm_context = assumptions_from_propositions(&evidence);
                        let arm_refutes_parent =
                            partition.path_facts[parent_arm].iter().any(|path_fact| {
                                fact_conflicts_with_assumptions(path_fact, &arm_context)
                            });
                        evidence.pop();
                        evidence.extend(partition.path_facts[parent_arm].iter().cloned());
                        let parent_context = assumptions_from_propositions(&evidence);
                        let parent_refutes_arm =
                            fact_conflicts_with_assumptions(&fact, &parent_context);
                        Ok(Some(if arm_refutes_parent || parent_refutes_arm {
                            LaneDecision::Excluded
                        } else {
                            LaneDecision::Survives(fact)
                        }))
                    },
                )?;
                let Some(decision) = decision else {
                    return Ok(None);
                };
                let LaneDecision::Survives(fact) = decision else {
                    continue;
                };
                let facts = partition.base_facts[parent_arm].with_fact(fact.clone());
                let mut execution = (*partition.base_executions[parent_arm]).clone();
                execution.last_step_delta = ExecutionProofStepDelta::default();
                execution
                    .replay
                    .surface_propositions
                    .record_lowering(&surface_fact, &fact)?;
                execution
                    .replay
                    .case_assumptions
                    .push(ReplayCaseAssumption {
                        tactic_index: context.tactic_index,
                        condition: condition.clone(),
                        value: take_then,
                        fact: Some(fact.clone()),
                        at_function_entry: execution.replay.is_at_function_entry(),
                    });
                let base_execution = Arc::new(execution.clone());
                let mut checked = check_step_using_facts(
                    &mut execution.replay,
                    &mut execution.state,
                    &facts,
                    &arm_steps[logical_arm].1,
                    context.function_block,
                    context.function,
                    context.parsed_function,
                    context.arguments,
                    context.function_environment,
                    context.predicate_environment,
                    context.click_function_environment,
                    context.claim_label,
                    arm_steps[logical_arm].0,
                )?;
                match checked.len() {
                    0 => {}
                    1 if survivor.is_none() => {
                        survivor = Some(Survivor {
                            base_facts: facts,
                            base_execution,
                            path_fact: fact,
                            checked: checked.pop().expect("one successor was checked"),
                        });
                    }
                    // More than one surviving parent lane, or a statement
                    // that itself still branches, did not collapse within
                    // the fixed four-check boundary.
                    _ => return Ok(None),
                }
            }
            let Some(survivor) = survivor else {
                return Ok(None);
            };
            survivors[logical_arm] = Some(survivor);
        }

        let [Some(then_survivor), Some(else_survivor)] = survivors else {
            unreachable!("both logical arms were required above")
        };
        let make_goal = |survivor: &Survivor| {
            let mut execution = (*survivor.base_execution).clone();
            execution.replay = survivor.checked.replay.clone();
            execution.state = survivor.checked.state.clone().into();
            Goal::Frontier(FrontierGoal {
                selection,
                context: GoalContext {
                    facts: survivor.checked.facts.clone(),
                    unfolded_predicates: partition.parent_unfolds.clone(),
                    execution: Some(Arc::new(execution)),
                },
            })
        };
        let goals = self
            .state
            .goals
            .replace_at(partition.ids[0], make_goal(&then_survivor))
            .replace_at(partition.ids[1], make_goal(&else_survivor));
        let marker_node = Arc::new(ProofNode {
            parent: Some(self.node.clone()),
            step: None,
            focused: self.focused,
            depth: self.node.depth,
        });
        let then_node = Arc::new(ProofNode {
            parent: Some(marker_node.clone()),
            step: Some(Arc::new(SimpleProofStep::StepUsing(arm_steps[0].1.clone()))),
            focused: partition.ids[0],
            depth: marker_node.depth + 1,
        });
        let else_node = Arc::new(ProofNode {
            parent: Some(then_node),
            step: Some(Arc::new(SimpleProofStep::StepUsing(arm_steps[1].1.clone()))),
            focused: partition.ids[1],
            depth: marker_node.depth + 2,
        });
        let then_path = vec![then_survivor.path_fact.clone()];
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(then_path.clone()),
                checked_facts: Arc::new(then_path.clone()),
            }),
            node: else_node,
            focused: partition.ids[0],
        };
        let record = ExecutionProofCaseSplit {
            marker: ProofCheckpoint {
                context: self.context.clone(),
                node: marker_node,
            },
            split: partition.split,
            ids: partition.ids,
            surface_condition: condition.clone(),
            base_facts: [then_survivor.base_facts, else_survivor.base_facts],
            base_executions: [then_survivor.base_execution, else_survivor.base_execution],
            path_facts: [then_path, vec![else_survivor.path_fact]],
            common_facts: partition.common_facts.clone(),
            parent_unfolds: partition.parent_unfolds.clone(),
            parent_execution: partition.parent_execution.clone(),
            execution_start_state: partition.execution_start_state.clone(),
        };
        Ok(Some((successor, record)))
    }

    /// Splits one retained execution frontier under an exhaustive proof-level
    /// condition. Both arms share the already-checked C state and receive only
    /// their respective logical polarity; subsequent statement steps remain
    /// independently checked on each sibling.
    pub(in crate::lang::click::proof) fn split_focused_execution_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        self.require_execution_frontier("proof `if`")?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above")
        };
        let parent_execution = frontier
            .context
            .execution
            .clone()
            .expect("an execution frontier owns its checked state");
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("an execution frontier has an execution context")
        };
        let at_function_entry = parent_execution.replay.is_at_function_entry();
        let arm = |surface_fact: ClickProposition, fact: Proposition, value: bool| {
            let facts = frontier.context.facts.with_fact(fact.clone());
            let mut execution = (*parent_execution).clone();
            execution
                .replay
                .surface_propositions
                .record_lowering(&surface_fact, &fact)?;
            execution
                .replay
                .case_assumptions
                .push(ReplayCaseAssumption {
                    tactic_index: context.tactic_index,
                    condition: condition.clone(),
                    value,
                    fact: Some(fact.clone()),
                    at_function_entry,
                });
            Ok((
                Goal::Frontier(FrontierGoal {
                    selection: frontier.selection,
                    context: GoalContext {
                        facts: facts.clone(),
                        unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                        execution: Some(Arc::new(execution.clone())),
                    },
                }),
                facts,
                vec![fact],
                Arc::new(execution),
            ))
        };
        let (then_goal, then_facts, then_path, then_execution) =
            arm(condition.clone(), then_fact, true)?;
        let (else_goal, else_facts, else_path, else_execution) =
            arm(else_surface, else_fact, false)?;
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [then_goal, else_goal]);
        let first_path = then_path.clone();
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(first_path.clone()),
                checked_facts: Arc::new(first_path),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: ids[0],
        };
        let record = ExecutionProofCaseSplit {
            marker: successor.checkpoint(),
            split,
            ids,
            surface_condition: condition,
            base_facts: [then_facts, else_facts],
            base_executions: [then_execution, else_execution],
            path_facts: [then_path, else_path],
            common_facts: frontier.context.facts.clone(),
            parent_unfolds: frontier.context.unfolded_predicates.clone(),
            parent_execution: parent_execution.clone(),
            execution_start_state: parent_execution
                .replay
                .execution_start_state(&parent_execution.state)
                .clone(),
        };
        Ok((successor, record))
    }

    /// Splits one retained execution frontier under the two exact disjuncts
    /// of an available proposition. The disjunction is checked once at the
    /// split; each sibling receives only its own disjunct in its persistent
    /// fact context, and no semantic state is exported to a replay cursor.
    pub(in crate::lang::click::proof) fn split_focused_execution_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, ExecutionLogicalCasesSplit<'a>), ClickError> {
        self.require_execution_frontier("`cases`")?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above")
        };
        let parent_execution = frontier
            .context
            .execution
            .clone()
            .expect("an execution frontier owns its checked state");
        let lowered = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        if !frontier.context.facts.contains(&lowered) {
            return Err(self.step_error(format!(
                "`cases` requires its exact disjunction as an available fact: {lowered:?}"
            )));
        }
        let Proposition::Or(left, right) = lowered else {
            return Err(self.step_error(format!("`cases` requires a disjunction, got {lowered:?}")));
        };
        let arm = |disjunct: Proposition| {
            let facts = frontier.context.facts.with_fact(disjunct.clone());
            (
                Goal::Frontier(FrontierGoal {
                    selection: frontier.selection,
                    context: GoalContext {
                        facts,
                        unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                        execution: Some(parent_execution.clone()),
                    },
                }),
                vec![disjunct],
            )
        };
        let (left_goal, left_path) = arm(*left);
        let (right_goal, right_path) = arm(*right);
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [left_goal, right_goal]);
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(left_path.clone()),
                checked_facts: Arc::new(left_path.clone()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: ids[0],
        };
        let record = ExecutionLogicalCasesSplit {
            marker: successor.checkpoint(),
            split,
            ids,
            path_facts: [left_path, right_path],
        };
        Ok((successor, record))
    }

    /// Focuses one arm of a logical execution-frontier `cases` split. The
    /// arm's exact disjunct is re-presented only as this focused operation's
    /// local fact delta.
    pub(in crate::lang::click::proof) fn focus_execution_cases_arm(
        &self,
        record: &ExecutionLogicalCasesSplit<'a>,
        take_left: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_left);
        let mut focused = self.focus(record.ids[arm_index])?;
        let path_facts = record.path_facts[arm_index].clone();
        focused.state = Arc::new(ProofState {
            locals: focused.state.locals.clone(),
            goals: focused.state.goals.clone(),
            added_facts: Arc::new(path_facts.clone()),
            checked_facts: Arc::new(path_facts),
        });
        Ok(focused)
    }

    /// Applies one recursively driven logical `cases` operation over an
    /// execution frontier. Both callbacks must retire their sibling goals;
    /// the returned node retains one structured `Cases` provenance step.
    pub(in crate::lang::click::proof) fn apply_execution_cases_with<Left, Right>(
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
        right_done.join_focused_cases(&record.marker, record.split, record.ids, disjunction)
    }

    /// Applies one recursively driven proof-level execution `if` as an
    /// audited sibling-goal operation. Each callback must retire exactly its
    /// selected arm, either with terminal checked steps or another invocation
    /// of this operation. The returned node retains the structured `If`
    /// provenance directly on this Proof lineage.
    pub(in crate::lang::click::proof) fn apply_execution_if_with<Then, Else>(
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
        else_done.join_focused_if(&record.marker, record.split, record.ids, condition)
    }

    /// Joins a completed in-`Proof` `if` split with one structured `If`
    /// step, under the same rules as [`Self::join_focused_cases`].
    pub(in crate::lang::click::proof) fn join_focused_if(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [GoalId; 2],
        condition: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| SimpleProofStep::If {
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
    pub(in crate::lang::click::proof) fn join_focused_cases(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [GoalId; 2],
        disjunction: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| SimpleProofStep::Cases {
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
        ids: [GoalId; 2],
    ) -> Result<[Vec<SimpleProofStep>; 2], ClickError> {
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
                if current.focused == ids[0] {
                    left_steps.push(step.as_ref().clone());
                } else if current.focused == ids[1] {
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
        ids: [GoalId; 2],
        step: impl FnOnce(ProofCertificate, ProofCertificate) -> SimpleProofStep,
    ) -> Result<Self, ClickError> {
        for (name, id) in [("left", ids[0]), ("right", ids[1])] {
            if self.state.goals.get(id).is_some() {
                return Err(
                    self.step_error(format!("cannot join `cases`: {name} arm is incomplete"))
                );
            }
        }
        let [left_steps, right_steps] = self.partition_steps_since(marker, split, ids)?;
        let parent = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `cases`: the split marker lost its root")
        })?;
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: self.state.goals.clone(),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(parent.clone()),
                step: Some(Arc::new(step(
                    ProofCertificate::from_steps(left_steps),
                    ProofCertificate::from_steps(right_steps),
                ))),
                focused: marker.node.focused,
                depth: parent.depth + 1,
            }),
            focused: marker.node.focused,
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
    /// justify terminal simple steps without being exposed to incompatible
    /// outcomes.
    pub(super) fn split_focused_outcome_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, OutcomeSplit<'a>), ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("execution outcome `if` follows a completed proof"));
        }
        let ProofContext::Execution(_) = self.context.as_ref() else {
            return Err(self.step_error("execution outcome `if` requires an execution proof"));
        };
        self.require_execution_frontier("execution outcome `if`")?;
        let root_execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution outcome `if` lost its semantic frontier"))?;
        if !root_execution.replay.is_at_function_exit() {
            return Err(self.step_error("execution outcome `if` requires function exit"));
        }
        let checked = root_execution.replay.execution().ok_or_else(|| {
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
        let Some(Goal::Frontier(parent)) = self.focused_goal() else {
            unreachable!("the execution frontier requirement was checked above")
        };
        let ProofContext::Execution(execution_context) = self.context.as_ref() else {
            unreachable!("the execution context requirement was checked above")
        };
        let expected_effects = self.selected_effect_indices(execution_context)?;
        let selection = parent.selection;
        let parent_facts = parent.context.facts.clone();
        let parent_unfolds = parent.context.unfolded_predicates.clone();
        let parent_execution = parent
            .context
            .execution
            .clone()
            .expect("the execution frontier owns its semantic state");
        let split = SplitId(self.state.goals.next_id);
        let ids = [
            GoalId(self.state.goals.next_id + 1),
            GoalId(self.state.goals.next_id + 2),
        ];
        let mut open = self.state.goals.open.without_key(&self.focused);
        let mut path_facts: [Vec<Proposition>; 2] = [Vec::new(), Vec::new()];
        for arm_index in 0..2 {
            let mut execution = root_execution.clone();
            let paths = std::mem::take(&mut partition_paths[arm_index]);
            execution.replay.frontier.point = ProofExecutionPoint::FunctionExit {
                execution: c_function_execution_candidates_from_outcomes(
                    execution_state.clone(),
                    function.clone(),
                    arguments.clone(),
                    paths,
                ),
            };
            execution.last_step_delta = ExecutionProofStepDelta::default();
            execution
                .replay
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
            open = open.with_inserted(
                ids[arm_index],
                Goal::Frontier(FrontierGoal {
                    selection,
                    context: GoalContext {
                        facts,
                        unfolded_predicates: parent_unfolds.clone(),
                        execution: Some(Arc::new(execution)),
                    },
                }),
            );
        }
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: ProofGoals {
                    open,
                    next_id: self.state.goals.next_id + 3,
                },
                added_facts: Arc::new(path_facts[0].clone()),
                checked_facts: Arc::new(path_facts[0].clone()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: ids[0],
        };
        let record = OutcomeSplit {
            marker: successor.checkpoint(),
            split,
            ids,
            condition,
            expected_effects,
            path_facts,
            parent_facts,
            parent_unfolds,
            parent_execution,
            root_post_execution_count: root_execution.replay.post_execution_tactics.len(),
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
        let mut focused = self.focus(record.ids[arm_index])?;
        let delta = record.path_facts[arm_index].clone();
        focused.state = Arc::new(ProofState {
            locals: focused.state.locals.clone(),
            goals: focused.state.goals.clone(),
            added_facts: Arc::new(delta.clone()),
            checked_facts: Arc::new(delta),
        });
        Ok(focused)
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
            self.partition_steps_since(&record.marker, record.split, record.ids)?;
        let arm_certificates = [
            ProofCertificate::from_steps(then_steps),
            ProofCertificate::from_steps(else_steps),
        ];
        let mut checked_deferrals = Vec::with_capacity(2);
        for (name, id) in [("then", record.ids[0]), ("else", record.ids[1])] {
            let Some(Goal::Frontier(frontier)) = self.state.goals.get(id) else {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm is not an open execution frontier"
                )));
            };
            if !matches!(frontier.selection, EffectGoalSelection::None) {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not close its effect goal"
                )));
            }
            let execution = frontier.context.execution.as_deref().ok_or_else(|| {
                self.step_error(format!(
                    "execution outcome {name} arm lost its semantic frontier"
                ))
            })?;
            if !execution.replay.is_at_function_exit() {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not remain at function exit"
                )));
            }
            let mut added = execution
                .replay
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
            if authority.effect_indices.as_ref() != &record.expected_effects {
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
        execution.replay.defer_checked_post_execution(
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
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let parent_goal = record.marker.node.focused;
        let parent_node = record.marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join outcome `if`: the split marker lost its root")
        })?;
        let open = self
            .state
            .goals
            .open
            .without_key(&record.ids[0])
            .without_key(&record.ids[1])
            .with_inserted(
                parent_goal,
                Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context: GoalContext {
                        facts: record.parent_facts.clone(),
                        unfolded_predicates: record.parent_unfolds.clone(),
                        execution: Some(Arc::new(execution)),
                    },
                }),
            );
        let [then_certificate, else_certificate] = arm_certificates;
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: ProofGoals {
                    open,
                    next_id: self.state.goals.next_id,
                },
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(parent_node.clone()),
                step: Some(Arc::new(SimpleProofStep::If {
                    condition: record.condition.clone(),
                    then_proof: Box::new(then_certificate),
                    else_proof: Box::new(else_certificate),
                })),
                focused: parent_goal,
                depth: parent_node.depth + 1,
            }),
            focused: parent_goal,
        })
    }

    /// Opens a nested proof for one surface proposition. The body has a fresh
    /// provenance root but shares the persistent semantic fact index and
    /// immutable checking context with its enclosing proof.
    ///
    /// A point proof may open `have` either while refining a proposition or
    /// from its initial result frontier. The latter is the audited way for
    /// grouped contract finalization to prove one obligation, publish it as a
    /// checked fact, and then prove a dependent obligation without rebuilding
    /// or mutating an external fact context.
    pub(in crate::lang::click::proof) fn begin_have(
        &self,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`have` follows a completed proof"));
        }
        match (self.focused_goal(), self.context.as_ref()) {
            (Some(Goal::Proposition(_) | Goal::FunctionOutcome(_)), _) => {}
            (Some(Goal::Frontier(_)), ProofContext::Point(_) | ProofContext::Execution(_)) => {}
            _ => {
                return Err(self.step_error("`have` requires a proposition or point context"));
            }
        }
        let kernel = self.lower_surface_goal(&proposition, "`have` proposition")?;
        // A post-execution unfold lets a predicate-call `have` prove the
        // predicate through its structural body. Pair that body kernel with
        // the same unfolded Surface view so `intro` retains binder names and
        // subsequent simple steps serialize an independently replayable
        // proof. Joining still publishes the opaque `kernel` named by the
        // enclosing Have step.
        let structural_proposition = if let ClickProposition::PredicateCall { name, .. } =
            &proposition
            && self.focused_goal_unfolds().contains(name)
        {
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::Point(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let active_unfolds = self.focused_goal_unfolds().to_vec();
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
        let body_kernel = self.lower_surface_goal(&structural_proposition, "`have` body")?;
        let mut body_facts = self.facts().with_selected_resource_separation(&body_kernel);
        let selected_surface_separation = match &structural_proposition {
            ClickProposition::Separate { .. } => true,
            ClickProposition::At { proposition, .. } => {
                matches!(proposition.as_ref(), ClickProposition::Separate { .. })
            }
            _ => false,
        };
        if selected_surface_separation
            && !body_facts.contains(&body_kernel)
            && body_facts.assumptions().proves(&body_kernel)
        {
            body_facts = body_facts.with_fact(body_kernel.clone());
        }
        for name in self.focused_goal_unfolds().iter() {
            let recorded_bodies = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Point(context) => context
                    .surface_propositions
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => self
                    .outcome_point_view()
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
        let body_context = GoalContext {
            facts: body_facts,
            unfolded_predicates: self.focused_goal_unfolds().clone(),
            execution: self.goal_execution().cloned(),
        };
        // An execution `have` borrows the current immutable frontier solely
        // as its proposition-lowering/theorem context, shared by identity on
        // the nested goal; a `have` stated at a function outcome borrows that
        // outcome's result-aware point data the same way. The nested goal
        // cannot publish a changed frontier or outcome: `join` restores the
        // exact root state and exposes only the stated proposition.
        let mut body_goal = match self.focused_outcome_point() {
            Some(point) => Goal::surface_proposition_at_outcome(
                body_context,
                point.clone(),
                body_kernel.clone(),
                structural_proposition,
            ),
            None => Goal::surface_proposition_in(body_context, body_kernel, structural_proposition),
        };
        if let (Some(Goal::Proposition(parent)), Goal::Proposition(body)) =
            (self.focused_goal(), &mut body_goal)
        {
            body.surface_bindings = parent.surface_bindings.clone();
        }
        let body = Proof {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),

                goals: ProofGoals::root(body_goal),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
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
    pub(in crate::lang::click::proof) fn begin_open(
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
        if execution.replay.is_at_function_exit() {
            return Err(self.step_error("`open` must begin before execution reaches function exit"));
        }
        let checked = open_composite_resource_for_proof(
            context.resource_environment,
            &resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.state).clone(),
            self.facts().clone(),
            &mut execution.replay.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution.state = checked.state.into();
        execution.replay.open_scopes += 1;
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let introduced_facts = checked.added_facts.clone();
        let body = Proof {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),

                goals: self
                    .state
                    .goals
                    .replace_frontier_at(self.focused, checked.facts, execution),
                added_facts: Arc::new(checked.added_facts.clone()),
                checked_facts: Arc::new(checked.added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: self.focused,
                depth: 0,
            }),
            focused: self.focused,
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
