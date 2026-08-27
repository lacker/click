//! Checked execution statement steps and loop-invariant bundles.

use super::*;

impl<'a> Proof<'a> {
    pub(super) fn apply_execution_statement_step(
        &self,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`step`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        // Every statement step executes in the whole proof context.
        let fact_context = Some(self.facts().assumptions());
        let checked = check_statement_step(&mut execution, context, &self.facts(), fact_context)?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above");
        };
        let parent_execution = Arc::new(execution.clone());
        let execution_start_state = execution
            .frontier
            .execution_start_state(&execution.state)
            .clone();
        let make_goal = |mut checked: CheckedStatementStep| {
            // A fact the statement introduces (a callee's `ensures`, a
            // store's value) is recorded under its readable spelling at the
            // successor state, so a later premise can name it without
            // re-lowering it against another memory. Output-sized work: one
            // synthesis per introduced fact.
            for fact in &checked.added_facts {
                if let Some(surface) = synthesize_surface_proposition(
                    fact,
                    context.parsed_function.parameters(),
                    context.arguments,
                    &checked.execution.state,
                ) {
                    let _ = checked
                        .execution
                        .surface_propositions
                        .record_lowering(&surface, fact);
                }
            }
            let successor_execution = checked.execution;
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
                        execution: successor_execution,
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
                    let path_fact = Proposition::ConditionIs(path_condition, value);
                    if by_polarity[slot]
                        .replace((
                            facts,
                            Arc::new(successor_execution),
                            vec![path_fact],
                            added.clone(),
                        ))
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
                    introduced_facts: [then_arm.3, else_arm.3],
                    common_facts,
                    parent_unfolds: frontier.context.unfolded_predicates.clone(),
                    parent_execution: parent_execution.clone(),
                    execution_start_state: execution_start_state.clone(),
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
        if execution.program_point_states.contains_key(&point) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        execution
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
        if execution.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(
                self.step_error("`close_invariants` is only available in a loop-region proof")
            );
        }
        if execution.region_invariants_closed {
            return Err(
                self.step_error("the invariant bundle was closed more than once on one path")
            );
        }
        execution.region_invariants_closed = true;
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
        if execution.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("loop invariant closure requires a loop-region proof"));
        }

        let mut closer_facts = self.facts().to_vec();
        closer_facts.extend(
            execution
                .effect_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        closer_facts.extend(crate::kernel::certified_store_equations(
            &execution.effect_facts,
        ));
        c_loop_invariants_hold_at_back_edge_using(
            &execution.state,
            loop_entry_state,
            invariant_checks,
            &assumptions_from_propositions(&closer_facts),
        )
        .map_err(|message| self.step_error(format!("invariant bundle: {message}")))?;

        if execution.region_invariants_closed {
            Ok(self.clone())
        } else {
            self.apply_step(SimpleProofStep::CloseInvariants)
        }
    }

    /// Splits the focused preservation frontier under a proof-level `if`,
    /// introducing each arm's case assumption through the one shared
    /// case-assumption law, so lowered spellings, recorded surface
    /// propositions, and feasibility match the replayed form exactly.
    /// Infeasible arms are omitted; the returned slots align `[then, else]`.
    /// Sibling arms stay separate — a preservation path never rejoins across
    /// the back edge — so no join consumes this split.
    pub(in crate::lang::click::proof) fn split_preservation_case(
        &self,
        condition: &ClickProposition,
        tactic_index: usize,
    ) -> Result<(Self, [Option<GoalId>; 2]), ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a preservation `if` requires an execution proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("proof `if`")?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above")
        };
        let mut base_execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // A mid-execution case condition may name the current statement's
        // entry snapshot before any step has crossed it; record it so the
        // form lowers, exactly as the replayed `if` did.
        record_current_statement_entry(
            &base_execution.frontier,
            &mut base_execution.program_point_states,
            &base_execution.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            tactic_index,
            "if",
        )?;
        let mut arms: [Option<(Goal, Vec<Proposition>)>; 2] = [None, None];
        for value in [true, false] {
            let mut arm_execution = base_execution.clone();
            arm_execution.last_step_delta = ExecutionProofStepDelta::default();
            let mut arm_facts = self.facts().to_vec();
            let base_facts = arm_facts.len();
            let feasible = introduce_proof_case_assumption(
                &mut arm_execution,
                &tactic_context,
                &mut arm_facts,
                base_execution.has_structured_branch_history,
                condition,
                value,
            )?;
            if !feasible {
                continue;
            }
            // Record where this proof-level case split sits in the path's
            // surface record, exactly as the replayed form recorded it.
            if arm_execution
                .replay
                .proof_certificate_builder
                .blocker
                .is_none()
            {
                let tactic_offset = arm_execution.replay.proof_certificate_builder.steps.len();
                arm_execution
                    .replay
                    .proof_certificate_builder
                    .path_choices
                    .push(SurfacePathChoice {
                        occurrence: tactic_index,
                        condition: condition.clone(),
                        value,
                        tactic_offset,
                    });
            }
            let added = arm_facts[base_facts..].to_vec();
            let mut facts = frontier.context.facts.clone();
            for fact in &added {
                facts = facts.with_fact(fact.clone());
            }
            let execution = arm_execution;
            arms[usize::from(!value)] = Some((
                Goal::Frontier(FrontierGoal {
                    selection: frontier.selection,
                    context: GoalContext {
                        facts,
                        unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                        execution: Some(Arc::new(execution)),
                    },
                }),
                added,
            ));
        }
        match arms {
            [Some((then_goal, added)), Some((else_goal, _))] => {
                let (_, ids, goals) = self
                    .state
                    .goals
                    .split_at(self.focused, [then_goal, else_goal]);
                let successor = Self {
                    context: self.context.clone(),
                    state: Arc::new(ProofState {
                        locals: self.state.locals.clone(),
                        goals,
                        added_facts: Arc::new(added),
                        checked_facts: Arc::new(Vec::new()),
                    }),
                    node: Arc::new(ProofNode {
                        parent: Some(self.node.clone()),
                        step: None,
                        focused: self.focused,
                        depth: self.node.depth,
                    }),
                    focused: ids[0],
                };
                Ok((successor, [Some(ids[0]), Some(ids[1])]))
            }
            [then_arm, else_arm] => {
                let (value, (goal, added)) = if let Some(arm) = then_arm {
                    (true, arm)
                } else if let Some(arm) = else_arm {
                    (false, arm)
                } else {
                    return Err(self.step_error(
                        "no feasible arm exists for this preservation `if` condition",
                    ));
                };
                let successor = Self {
                    context: self.context.clone(),
                    state: Arc::new(ProofState {
                        locals: self.state.locals.clone(),
                        goals: self.state.goals.replace_at(self.focused, goal),
                        added_facts: Arc::new(added),
                        checked_facts: Arc::new(Vec::new()),
                    }),
                    node: self.node.clone(),
                    focused: self.focused,
                };
                let mut ids = [None, None];
                ids[usize::from(!value)] = Some(successor.focused);
                Ok((successor, ids))
            }
        }
    }

    /// The planner fallback for a preservation smart `step`: a scratch
    /// planning pass constructs the explicit checked operations for the
    /// current statement, and this Proof applies exactly those operations.
    /// Mirrors the replayed smart-step law, including its failure wording.
    pub(in crate::lang::click::proof) fn apply_planned_smart_step(
        &self,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("smart `step` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`step`")?;
        let execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let claim_label = context.claim_label;
        let mut planning = execution.clone();
        planning.planned_statement_transitions.clear();
        let facts_vec = self.facts().to_vec();
        planning.replay.proof_certificate_builder = ProofCertificateBuilder {
            last_step_entry: execution
                .replay
                .proof_certificate_builder
                .last_step_entry
                .clone(),
            certificate_facts: ProofFactStore::from_ordered(facts_vec.clone()),
            ..ProofCertificateBuilder::default()
        }
        .into();
        let mut planning_facts = facts_vec;
        let assumptions = assumptions_from_propositions(&planning_facts);
        execute_step_from_execution_point(
            &mut planning,
            &tactic_context,
            &mut planning_facts,
            &assumptions,
            "step",
            StatementPrerequisitePolicy::Planning,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::EnterBody,
            Some(ConstructionEnvironments {
                predicate_environment: context.predicate_environment,
                click_function_environment: context.click_function_environment,
            }),
        )?;
        let construction =
            std::mem::take(&mut planning.replay.proof_certificate_builder).into_value();
        if construction.blocker.is_none()
            && !construction.steps.is_empty()
            && construction.steps.iter().all(|step| {
                matches!(
                    step,
                    SimpleProofStep::Have { .. }
                        | SimpleProofStep::UnfoldPredicate(_)
                        | SimpleProofStep::TransportUsing { .. }
                        | SimpleProofStep::Step
                )
            })
            && construction
                .steps
                .iter()
                .any(|step| matches!(step, SimpleProofStep::Step))
        {
            let mut proof = self.clone();
            for step in &construction.steps {
                proof = proof.apply_step(step.clone())?;
            }
            let mut successor_execution = proof
                .execution()
                .cloned()
                .ok_or_else(|| proof.step_error("smart `step` lost its semantic state"))?;
            successor_execution
                .replay
                .proof_certificate_builder
                .last_step_entry = construction.last_step_entry;
            return Ok(Self {
                context: proof.context.clone(),
                state: Arc::new(ProofState {
                    locals: proof.state.locals.clone(),
                    goals: proof.state.goals.replace_frontier_at(
                        proof.focused,
                        proof.facts().clone(),
                        successor_execution,
                    ),
                    added_facts: proof.state.added_facts.clone(),
                    checked_facts: proof.state.checked_facts.clone(),
                }),
                node: proof.node.clone(),
                focused: proof.focused,
            });
        }
        if let Some(blocker) = construction.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart `step` could not construct checked Proof operations: {blocker}"
            )));
        }
        Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: smart `step` found no checked Proof candidate"
        )))
    }

    /// Pushes checked surface steps into this path's transitional surface
    /// record, which the preservation certificate serializes per leaf.
    /// Cursor metadata only: the steps were already checked on this Proof.
    pub(in crate::lang::click::proof) fn record_surface_steps(
        &self,
        steps: &[SimpleProofStep],
    ) -> Result<Self, ClickError> {
        if steps.is_empty() {
            return Ok(self.clone());
        }
        self.require_execution_frontier("surface recording")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        for step in steps {
            execution
                .replay
                .proof_certificate_builder
                .push_step(step.clone());
        }
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: self.state.goals.replace_frontier_at(
                    self.focused,
                    self.facts().clone(),
                    execution,
                ),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// The planner fallback for a smart `execute`: a scratch planning pass
    /// constructs the explicit checked operations for the remaining
    /// execution (a linear sequence, or a planned `if` tree for
    /// whole-function branches), and this Proof applies exactly those
    /// operations. This is the one smart-execute planner law: the source
    /// interpreter reports its errors directly, while the direct driver
    /// treats any error as a decline.
    /// The one mid-execution `transport` premise law, shared by the drivers:
    /// the source and target are lowered at the frontier, the premise
    /// planner names the premises, and this Proof applies the explicit
    /// `transport using` transition. The planner's failure is the answer,
    /// with its diagnostic.
    pub(in crate::lang::click::proof) fn apply_planned_fact_transport(
        &self,
        surface_source: &ClickProposition,
        surface_target: &ClickProposition,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`transport` requires an execution-frontier proof"));
        };
        let claim_label = context.claim_label;
        let premises = {
            let view = self.finalization_view()?;
            let (state, frontier, facts) = (view.state, view.frontier, &view.facts);
            if frontier.is_at_function_entry() || frontier.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one completed execution step"
                )));
            }
            let assumptions = assumptions_from_propositions(facts);
            let pre_state = view.context.old_reference_state(frontier, state);
            let source = lower_point_proposition(
                surface_source,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                state,
                None,
                &view.execution.program_point_states,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
                ))
            })?;
            if assumptions.derive_proposition(&source).is_none() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a source derivable from its ambient facts: {}",
                    describe_missing_pure_fact(
                        &source,
                        facts,
                        state.resources().facts(),
                        context.parsed_function.parameters(),
                        context.arguments,
                        &view.execution.effect_facts,
                    )
                )));
            }
            let target = lower_point_proposition(
                surface_target,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                state,
                None,
                &view.execution.program_point_states,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts = super::super::cursor_execution::fact_transport_transition_facts(
                &view.execution.effect_facts,
                &source,
            );
            plan_explicit_fact_transport(
                surface_source,
                &source,
                &target,
                facts,
                &transition_facts,
                context.parsed_function.parameters(),
                context.arguments,
                view.execution.view(view.context),
                state,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: {}",
                    fact_transport_planning_failure(
                        surface_source,
                        surface_target,
                        &view.unfolded_predicates,
                        &error,
                    )
                ))
            })?
        };
        self.apply_step(SimpleProofStep::TransportUsing {
            source: surface_source.clone(),
            target: surface_target.clone(),
            premises,
        })
    }

    /// The one `execute_until` planner law, shared by the drivers: the
    /// planner constructs the explicit checked operations from a scratch
    /// copy of the frontier, and this Proof applies exactly those operations,
    /// recording them as the tactic's surface. The planner's failure is the
    /// answer.
    pub(in crate::lang::click::proof) fn apply_planned_execute_until(
        &self,
        region_ref: &CodeRegionRef,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`execute_until` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        let claim_label = context.claim_label;
        let checkpoint = self.checkpoint();
        let code_region = super::super::structural::resolve_code_region_ref(
            context.function_block,
            region_ref,
            claim_label,
            tactic_index,
        )?;
        let CodeRegion::Statement(target_statement_index) = code_region else {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until` expects a statement region"
            )));
        };
        let (mut planning, mut planning_facts) = {
            let view = self.finalization_view()?;
            let mut planning = self.execution().cloned().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
            planning.planned_statement_transitions.clear();
            planning.replay.proof_certificate_builder = ProofCertificateBuilder {
                last_step_entry: view
                    .replay
                    .proof_certificate_builder
                    .last_step_entry
                    .clone(),
                certificate_facts: ProofFactStore::from_ordered(view.facts.clone()),
                ..ProofCertificateBuilder::default()
            }
            .into();
            (planning, view.facts)
        };
        super::super::cursor_execution::execute_until_statement(
            &mut planning,
            &tactic_context,
            &mut planning_facts,
            target_statement_index,
            StatementPrerequisitePolicy::Planning,
            Some(ConstructionEnvironments {
                predicate_environment: context.predicate_environment,
                click_function_environment: context.click_function_environment,
            }),
        )?;
        let construction =
            std::mem::take(&mut planning.replay.proof_certificate_builder).into_value();
        if construction.blocker.is_none()
            && !construction.steps.is_empty()
            && construction.steps.iter().all(|step| {
                matches!(
                    step,
                    SimpleProofStep::Have { .. }
                        | SimpleProofStep::UnfoldPredicate(_)
                        | SimpleProofStep::TransportUsing { .. }
                        | SimpleProofStep::Step
                )
            })
            && construction
                .steps
                .iter()
                .any(|step| matches!(step, SimpleProofStep::Step))
        {
            let mut executed = self.clone();
            for step in &construction.steps {
                executed = executed.apply_step(step.clone())?;
            }
            let certificate = executed.certificate_since(&checkpoint)?;
            let (recorded, ()) = executed.edit_replay_cursor(|replay, _, _| {
                for step in certificate.steps() {
                    replay.proof_certificate_builder.push_step(step.clone());
                }
                replay.proof_certificate_builder.last_step_entry = construction.last_step_entry;
            })?;
            Ok(recorded)
        } else if let Some(blocker) = construction.blocker {
            Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until` could not construct checked Proof operations: {blocker}"
            )))
        } else {
            Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `execute_until` found no checked Proof candidate"
            )))
        }
    }

    pub(in crate::lang::click::proof) fn apply_planned_smart_execute(
        &self,
        force_all_paths: bool,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("smart `execute` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        let claim_label = context.claim_label;
        self.require_execution_frontier("`execute`")?;
        let execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let facts_vec = self.facts().to_vec();
        let planning_builder = |certificate_facts: &[Proposition]| ProofCertificateBuilder {
            last_step_entry: execution
                .replay
                .proof_certificate_builder
                .last_step_entry
                .clone(),
            certificate_facts: ProofFactStore::from_ordered(certificate_facts.to_vec()),
            ..ProofCertificateBuilder::default()
        };
        let construction_environments = Some(ConstructionEnvironments {
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
        });
        let mut planning = execution.clone();
        planning.planned_statement_transitions.clear();
        planning.replay.proof_certificate_builder = planning_builder(&facts_vec).into();
        let mut planning_facts = facts_vec.clone();
        let direct_result = (!force_all_paths).then(|| {
            execute_rest_from_execution_point(
                &mut planning,
                &tactic_context,
                &mut planning_facts,
                construction_environments,
            )
        });
        if direct_result.is_none_or(|result| result.is_err()) {
            planning = execution.clone();
            planning.planned_statement_transitions.clear();
            planning.replay.proof_certificate_builder = planning_builder(&facts_vec).into();
            planning_facts = facts_vec.clone();
            bounded_execute_from_execution_point(
                &mut planning,
                &tactic_context,
                &mut planning_facts,
                StatementPrerequisitePolicy::Planning,
                construction_environments,
            )?;
        }
        let construction =
            std::mem::take(&mut planning.replay.proof_certificate_builder).into_value();
        if let Some(blocker) = &construction.blocker {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart `execute` could not construct checked Proof operations: {blocker}"
            )));
        }
        let no_candidate = || {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: smart `execute` found no checked Proof candidate"
            ))
        };
        if construction.steps.is_empty() {
            return Err(no_candidate());
        }
        let linear_supported = construction.steps.iter().all(|step| {
            matches!(
                step,
                SimpleProofStep::Have { .. }
                    | SimpleProofStep::UnfoldPredicate(_)
                    | SimpleProofStep::TransportUsing { .. }
                    | SimpleProofStep::Step
            )
        }) && construction
            .steps
            .iter()
            .any(|step| matches!(step, SimpleProofStep::Step));
        let applied = if linear_supported {
            let mut proof = self.clone();
            for step in &construction.steps {
                proof = proof.apply_step(step.clone())?;
            }
            Some(proof)
        } else if construction
            .steps
            .iter()
            .any(|step| matches!(step, SimpleProofStep::If { .. }))
        {
            self.try_planned_execution_steps(&construction.steps)?
        } else {
            None
        };
        let Some(proof) = applied else {
            return Err(no_candidate());
        };
        let mut successor_execution = proof
            .execution()
            .cloned()
            .ok_or_else(|| proof.step_error("smart `execute` lost its semantic state"))?;
        successor_execution
            .replay
            .proof_certificate_builder
            .last_step_entry = construction.last_step_entry;
        Ok(Self {
            context: proof.context.clone(),
            state: Arc::new(ProofState {
                locals: proof.state.locals.clone(),
                goals: proof.state.goals.replace_frontier_at(
                    proof.focused,
                    proof.facts().clone(),
                    successor_execution,
                ),
                added_facts: proof.state.added_facts.clone(),
                checked_facts: proof.state.checked_facts.clone(),
            }),
            node: proof.node.clone(),
            focused: proof.focused,
        })
    }

    /// The mid-execution `have` for a bounded region path, applied through
    /// the one shared have law when the Proof-native nested scope declines.
    /// The law records its own surface certificate and lowerings.
    pub(in crate::lang::click::proof) fn apply_mid_execution_have(
        &self,
        expansion_capture: Option<&mut ExpansionCapture>,
        have: &ProofHave,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let mut expansion_capture = expansion_capture;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`have` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`have`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let mut facts = self.facts().to_vec();
        let base_facts = facts.len();
        let mut scope = Some(begin_tactic_surface_scope(&mut execution.replay));
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.replay,
            context.constants.proof_site.as_ref(),
        );
        let smart_certificate =
            check_mid_execution_have(have, &mut execution, &tactic_context, &mut facts)?;
        let slice = end_tactic_surface_scope(
            &mut execution.replay,
            scope.take().expect("tactic scope is open"),
        );
        if capture_this_tactic {
            finish_tactic_expansion_capture(expansion_capture.as_deref_mut(), &slice, false);
        }
        let added = facts[base_facts..].to_vec();
        let mut proof_facts = self.facts().clone();
        for fact in &added {
            proof_facts = proof_facts.with_fact(fact.clone());
        }
        // Retain the checked `have` as provenance: a smart body keeps the
        // law's selected surface operations; an explicit body keeps its own
        // script. Expansion serializes this node, never the aftermath.
        let have_step = match (smart_certificate, &have.proof) {
            // The law's surface certificate is already the complete checked
            // form, including the `have` wrapper when it selected one.
            (Some(certificate), _) => match certificate.steps() {
                [step @ SimpleProofStep::Have { .. }] => step.clone(),
                _ => SimpleProofStep::Have {
                    proposition: have.proposition.clone(),
                    proof: Box::new(certificate),
                },
            },
            (None, SourceProof::Script(tactics)) => SimpleProofStep::Have {
                proposition: have.proposition.clone(),
                proof: Box::new(ProofCertificate::from_proof_tactics(tactics).map_err(
                    |error| {
                        self.step_error(format!(
                            "`have` body is not surface-expressible: {error:?}"
                        ))
                    },
                )?),
            },
            (None, _) => SimpleProofStep::Have {
                proposition: have.proposition.clone(),
                proof: Box::new(
                    ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption])
                        .expect("assumption is a simple proof"),
                ),
            },
        };
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: self
                    .state
                    .goals
                    .replace_frontier_at(self.focused, proof_facts, execution),
                added_facts: Arc::new(added),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(have_step)),
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: self.focused,
        })
    }

    /// Records where the replayed `close_invariants` tactic sat, so the
    /// kernel re-derivation its caller performs at the bundle check can be
    /// timed against that tactic's identity. Cursor metadata only.
    pub(in crate::lang::click::proof) fn record_invariant_closer(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`close_invariants`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.invariant_closer_step = Some(InvariantCloserStep {
            tactic_index,
            source_index,
            statement_index: execution.frontier.next_statement_index,
        });
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: self.state.goals.replace_frontier_at(
                    self.focused,
                    self.facts().clone(),
                    execution,
                ),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Records a region-level `simp` for the loop-invariant bundle. The
    /// tactic's semantic content is the bundle closer certified at the
    /// typed boundary, so only its identity is recorded here — cursor
    /// metadata for expansion capture and timing attribution, never a
    /// semantic transition.
    pub(in crate::lang::click::proof) fn defer_region_simp(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`simp`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("a region `simp` is only available in a loop-region proof"));
        }
        execution.region_simp = Some((tactic_index, source_index));
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: self.state.goals.replace_frontier_at(
                    self.focused,
                    self.facts().clone(),
                    execution,
                ),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Applies a frontier-local `loop` tactic as one checked operation on
    /// the focused execution frontier: the loop's phases verify through the
    /// shared loop-planning machinery, the certified loop rule replaces the
    /// `while` statement in the frontier's own statement tree, and the
    /// derived exit facts join this goal's context. The surface record and
    /// expansion capture ride the transitional cursor exactly as the
    /// replayed form recorded them.
    pub(in crate::lang::click::proof) fn apply_frontier_local_loop(
        &self,
        mut expansion_capture: Option<&mut ExpansionCapture>,
        loop_clause: &StructuralClause,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`loop` requires an execution-frontier proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`loop`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let mut facts = self.facts().to_vec();
        let base_facts = facts.len();
        let mut scope = Some(begin_tactic_surface_scope(&mut execution.replay));
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.replay,
            context.constants.proof_site.as_ref(),
        );
        let _timing = TacticTiming::new(
            context.claim_label,
            tactic_index,
            source_index,
            &ProofTactic::Loop(loop_clause.clone()),
            execution.frontier.next_statement_index,
        );
        let expanded_loop = execute_frontier_local_loop(
            expansion_capture.as_deref_mut(),
            loop_clause,
            &mut execution,
            &tactic_context,
            &mut facts,
            source_index,
        )?;
        let slice = end_tactic_surface_scope(
            &mut execution.replay,
            scope.take().expect("tactic scope is open"),
        );
        if capture_this_tactic {
            finish_tactic_expansion_capture(expansion_capture, &slice, false);
        }
        debug_assert!(facts.len() >= base_facts);
        let added = facts[base_facts..].to_vec();
        let mut proof_facts = self.facts().clone();
        for fact in &added {
            proof_facts = proof_facts.with_fact(fact.clone());
        }
        // Retain the expanded loop clause as checked provenance so
        // whole-claim expansion serializes it without consulting the
        // transitional builder record.
        let loop_step = ProofCertificate::from_proof_tactics(std::slice::from_ref(
            &ProofTactic::Loop(expanded_loop),
        ))
        .map_err(|error| {
            self.step_error(format!(
                "`loop` produced an invalid expanded clause: {error:?}"
            ))
        })?
        .steps()[0]
            .clone();
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: self
                    .state
                    .goals
                    .replace_frontier_at(self.focused, proof_facts, execution),
                added_facts: Arc::new(added),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(loop_step)),
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: self.focused,
        })
    }
}
