//! Checked execution statement steps and loop-invariant bundles.

use super::*;

impl<'a> Proof<'a> {
    pub(super) fn apply_execution_statement_step(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`step`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // Every statement step executes in the whole proof context.
        let fact_context = Some(self.facts().assumptions());
        let checked = check_statement_step(&mut execution, context, &self.facts(), fact_context)?;
        let Some(Obligation::Frontier(frontier)) = self.focused_obligation() else {
            unreachable!("the frontier requirement was checked above");
        };
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let mut checked = checked;
        // A fact the statement introduces (a callee's `ensures`, a store's
        // value) is recorded under its readable spelling at the successor
        // state, so a later premise can name it without re-lowering it against
        // another memory. Output-sized work: one synthesis per introduced
        // fact.
        for fact in &checked.added_facts {
            if let Some(surface) = synthesize_surface_proposition(
                fact,
                context.parsed_function.parameters(),
                context.arguments,
                &checked.execution.core.state,
            ) {
                // At a call successor, a synthesized `old(...)` names the
                // callee's entry snapshot, while the same surface syntax in
                // the caller names the caller's function entry. Do not cache
                // that ambiguous spelling as caller provenance. Explicit
                // Snapshot-qualified forms (including proof marks) retain the exact
                // call-frontier identity needed to name such a fact later.
                if proposition_contains_old_expression(&surface) {
                    continue;
                }
                let _ = checked
                    .execution
                    .presentation
                    .surface_propositions
                    .record_lowering(&surface, fact);
            }
        }
        let added_facts = checked.added_facts;
        let goal = OpenBranch::frontier(
            frontier.selection,
            BranchState {
                facts: checked.facts,
                unfolded_predicates: branch_state.unfolded_predicates.clone(),
                execution: Some(Arc::new(checked.execution)),
            },
        );
        let open_branches = self
            .state
            .open_branches
            .replace_at(self.focused_branch_id(), goal);
        Ok(Self {
            context: self.context.clone(),
            state: KernelProofObject::new(
                ProofState {
                    locals: self.state().locals.clone(),
                    open_branches,
                    added_facts: Arc::new(added_facts.clone()),
                    checked_facts: Arc::new(added_facts),
                },
                self.focused_branch_id(),
            ),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth + 1,
            }),
        })
    }

    pub(super) fn apply_execution_mark(&self, name: &str) -> Result<KernelProofHandle, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`mark` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`mark`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let mut presentation = execution.presentation.clone();
        let selector = SnapshotSelector::Mark(name.to_string());
        if presentation.recorded_snapshots.contains_key(&selector) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        presentation
            .recorded_snapshots
            .insert(selector, (*execution.core.state).clone());
        self.state
            .replace_frontier_presentation(presentation)
            .map_err(|error| self.execution_update_error("`mark`", error))
    }

    pub(super) fn apply_close_invariants(&self) -> Result<KernelProofHandle, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`close_invariants` requires an execution-frontier proof"));
        }
        self.state
            .close_frontier_invariants()
            .map_err(|error| self.execution_update_error("`close_invariants`", error))
    }

    fn execution_update_error(&self, operation: &str, error: ExecutionUpdateError) -> ClickError {
        match error {
            ExecutionUpdateError::NotFrontier | ExecutionUpdateError::ClosedLoopEffect => self
                .step_error(format!(
                    "{operation} cannot advance C execution inside a proposition proof"
                )),
            ExecutionUpdateError::MissingExecution => {
                self.step_error("execution-frontier proof lost its semantic state")
            }
            ExecutionUpdateError::NotLoopBody => {
                self.step_error("`close_invariants` is only available in a loop-region proof")
            }
            ExecutionUpdateError::InvariantsAlreadyClosed => {
                self.step_error("the invariant bundle was closed more than once on one path")
            }
        }
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
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("loop invariant closure requires a loop-region proof"));
        }

        let mut closer_facts = self.facts().to_vec();
        closer_facts.extend(
            execution
                .core
                .effect_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        closer_facts.extend(crate::kernel::certified_store_equations(
            &execution.core.effect_facts,
        ));
        c_loop_invariants_hold_at_back_edge_using(
            &execution.core.state,
            loop_entry_state,
            invariant_checks,
            &assumptions_from_propositions(&closer_facts),
        )
        .map_err(|message| self.step_error(format!("invariant bundle: {message}")))?;

        if execution.core.region_invariants_closed {
            Ok(self.clone())
        } else {
            self.apply_step(ProofStep::CloseInvariants)
        }
    }

    /// Splits the focused branch preservation frontier under a proof-level `if`,
    /// introducing each arm's case assumption through the one shared
    /// case-assumption law, so lowered spellings, recorded surface
    /// propositions, and feasibility match the checked form exactly.
    /// Infeasible arms are omitted; the returned slots align `[then, else]`.
    /// Sibling arms stay separate — a preservation path never rejoins across
    /// the back edge — so no join consumes this split.
    pub(in crate::lang::click::proof) fn split_preservation_case(
        &self,
        condition: &ClickProposition,
        tactic_index: usize,
    ) -> Result<(Self, [Option<BranchId>; 2]), ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a preservation `if` requires an execution proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("proof `if`")?;
        let Some(Obligation::Frontier(frontier)) = self.focused_obligation() else {
            unreachable!("the frontier requirement was checked above")
        };
        let mut base_execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // A mid-execution case condition may name the current statement's
        // entry snapshot before any step has crossed it; record it so the
        // form lowers, exactly as the checked `if` did.
        record_current_statement_entry(
            &base_execution.core.frontier,
            &mut base_execution.presentation.recorded_snapshots,
            &base_execution.core.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            tactic_index,
            "if",
        )?;
        let mut arms: [Option<(OpenBranch, Vec<Proposition>)>; 2] = [None, None];
        for value in [true, false] {
            let mut arm_execution = base_execution.clone();
            let mut arm_facts = self.facts().to_vec();
            let base_facts = arm_facts.len();
            let feasible = introduce_proof_case_assumption(
                &mut arm_execution,
                &tactic_context,
                &mut arm_facts,
                base_execution.core.has_structured_branch_history,
                condition,
                value,
            )?;
            if !feasible {
                continue;
            }
            // Record where this proof-level case split sits in the path's
            // surface record, exactly as the checked form recorded it.
            if arm_execution.presentation.surface_record.blocker.is_none() {
                // The split sits after the Proof's own top-level steps: surface
                // synthesis splits sibling paths at this offset, so it is
                // measured on the checked derivation, not a mirrored record.
                let tactic_offset = self.certificate().steps().len();
                arm_execution
                    .presentation
                    .surface_record
                    .path_choices
                    .push(SurfacePathChoice {
                        occurrence: tactic_index,
                        condition: condition.clone(),
                        value,
                        tactic_offset,
                    });
            }
            let added = arm_facts[base_facts..].to_vec();
            let branch_state = &self.focused_branch().expect("focused branch exists").state;
            let mut facts = branch_state.facts.clone();
            for fact in &added {
                facts = facts.with_fact(fact.clone());
            }
            let execution = arm_execution;
            arms[usize::from(!value)] = Some((
                OpenBranch::frontier(
                    frontier.selection,
                    BranchState {
                        facts,
                        unfolded_predicates: branch_state.unfolded_predicates.clone(),
                        execution: Some(Arc::new(execution)),
                    },
                ),
                added,
            ));
        }
        match arms {
            [Some((then_goal, added)), Some((else_goal, _))] => {
                let (_, ids, open_branches) = self
                    .state
                    .open_branches
                    .split_at(self.focused_branch_id(), [then_goal, else_goal]);
                let successor = Self {
                    context: self.context.clone(),
                    state: KernelProofObject::new(
                        ProofState {
                            locals: self.state().locals.clone(),
                            open_branches,
                            added_facts: Arc::new(added),
                            checked_facts: Arc::new(Vec::new()),
                        },
                        ids[0],
                    ),
                    node: Arc::new(ProofNode {
                        parent: Some(self.node.clone()),
                        step: None,
                        focused_branch: self.focused_branch_id(),
                        depth: self.node.depth,
                    }),
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
                    state: KernelProofObject::new(
                        ProofState {
                            locals: self.state().locals.clone(),
                            open_branches: self
                                .state
                                .open_branches
                                .replace_at(self.focused_branch_id(), goal),
                            added_facts: Arc::new(added),
                            checked_facts: Arc::new(Vec::new()),
                        },
                        self.focused_branch_id(),
                    ),
                    node: self.node.clone(),
                };
                let mut ids = [None, None];
                ids[usize::from(!value)] = Some(successor.focused_branch_id());
                Ok((successor, ids))
            }
        }
    }

    /// The planner fallback for a preservation smart `step`: a scratch
    /// planning pass constructs the explicit checked operations for the
    /// current statement, and this Proof applies exactly those operations.
    /// Mirrors the checked smart-step law, including its failure wording.
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
        planning.surface_record.certificate_facts = ProofFactStore::from_ordered(facts_vec.clone());
        let mut sink = ProofCertificateBuilder {
            last_step_entry: execution
                .presentation
                .surface_record
                .last_step_entry
                .clone(),
            ..ProofCertificateBuilder::default()
        };
        let mut planning_facts = facts_vec;
        let assumptions = assumptions_from_propositions(&planning_facts);
        execute_step_from_frontier_position(
            &mut planning,
            &tactic_context,
            &mut planning_facts,
            &assumptions,
            "step",
            StatementPrerequisitePolicy::Planning,
            StatementFactTransportPolicy::Automatic,
            LoopStepPolicy::EnterBody,
            Some(Construction {
                environments: ConstructionEnvironments {
                    predicate_environment: context.predicate_environment,
                    click_function_environment: context.click_function_environment,
                },
                sink: &mut sink,
            }),
        )?;
        let construction = sink;
        if construction.blocker.is_none()
            && !construction.steps.is_empty()
            && construction.steps.iter().all(|step| {
                matches!(
                    step,
                    ProofStep::Have { .. }
                        | ProofStep::UnfoldPredicate(_)
                        | ProofStep::TransportUsing { .. }
                        | ProofStep::Step
                )
            })
            && construction
                .steps
                .iter()
                .any(|step| matches!(step, ProofStep::Step))
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
                .presentation
                .surface_record
                .last_step_entry = construction.last_step_entry;
            return Ok(Self {
                context: proof.context.clone(),
                state: KernelProofObject::new(
                    ProofState {
                        locals: proof.state.locals.clone(),
                        open_branches: proof.state.open_branches.replace_frontier_at(
                            proof.focused_branch_id(),
                            proof.facts().clone(),
                            successor_execution,
                        ),
                        added_facts: proof.state.added_facts.clone(),
                        checked_facts: proof.state.checked_facts.clone(),
                    },
                    proof.focused_branch_id(),
                ),
                node: proof.node.clone(),
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
            let view = self.execution_view()?;
            let (state, frontier, facts) = (view.state, view.frontier, &view.facts);
            if frontier.is_at_function_entry() || frontier.is_at_function_exit() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `transport` requires a current statement frontier after at least one completed execution step"
                )));
            }
            let assumptions = assumptions_from_propositions(facts);
            let pre_state = view.context.old_reference_state(frontier, state);
            let source = lower_fixed_state_proposition(
                surface_source,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                state,
                None,
                &view.execution.presentation.recorded_snapshots,
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
                        &view.execution.core.effect_facts,
                    )
                )));
            }
            let target = lower_fixed_state_proposition(
                surface_target,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                state,
                None,
                &view.execution.presentation.recorded_snapshots,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
                ))
            })?;
            let transition_facts = super::super::cursor_execution::fact_transport_transition_facts(
                &view.execution.core.effect_facts,
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
        self.apply_step(ProofStep::TransportUsing {
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
        let (mut planning, mut planning_facts, mut sink) = {
            let view = self.execution_view()?;
            let mut planning = self.execution().cloned().ok_or_else(|| {
                self.step_error("execution-frontier proof lost its semantic state")
            })?;
            planning.planned_statement_transitions.clear();
            planning.surface_record.certificate_facts =
                ProofFactStore::from_ordered(view.facts.clone());
            let sink = ProofCertificateBuilder {
                last_step_entry: view
                    .execution
                    .presentation
                    .surface_record
                    .last_step_entry
                    .clone(),
                ..ProofCertificateBuilder::default()
            };
            (planning, view.facts, sink)
        };
        super::super::cursor_execution::execute_until_statement(
            &mut planning,
            &tactic_context,
            &mut planning_facts,
            target_statement_index,
            StatementPrerequisitePolicy::Planning,
            Some(Construction {
                environments: ConstructionEnvironments {
                    predicate_environment: context.predicate_environment,
                    click_function_environment: context.click_function_environment,
                },
                sink: &mut sink,
            }),
        )?;
        let construction = sink;
        if construction.blocker.is_none()
            && !construction.steps.is_empty()
            && construction.steps.iter().all(|step| {
                matches!(
                    step,
                    ProofStep::Have { .. }
                        | ProofStep::UnfoldPredicate(_)
                        | ProofStep::TransportUsing { .. }
                        | ProofStep::Step
                )
            })
            && construction
                .steps
                .iter()
                .any(|step| matches!(step, ProofStep::Step))
        {
            let mut executed = self.clone();
            for step in &construction.steps {
                executed = executed.apply_step(step.clone())?;
            }
            let (recorded, ()) = executed.edit_execution_presentation(|presentation| {
                presentation.surface_record.last_step_entry = construction.last_step_entry;
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
        let planning_sink = || ProofCertificateBuilder {
            last_step_entry: execution
                .presentation
                .surface_record
                .last_step_entry
                .clone(),
            ..ProofCertificateBuilder::default()
        };
        let construction_environments = ConstructionEnvironments {
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
        };
        let mut planning = execution.clone();
        planning.planned_statement_transitions.clear();
        planning.surface_record.certificate_facts = ProofFactStore::from_ordered(facts_vec.clone());
        let mut sink = planning_sink();
        let mut planning_facts = facts_vec.clone();
        let direct_result = (!force_all_paths).then(|| {
            execute_rest_from_frontier_position(
                &mut planning,
                &tactic_context,
                &mut planning_facts,
                Some(Construction {
                    environments: construction_environments,
                    sink: &mut sink,
                }),
            )
        });
        if direct_result.is_none_or(|result| result.is_err()) {
            planning = execution.clone();
            planning.planned_statement_transitions.clear();
            planning.surface_record.certificate_facts =
                ProofFactStore::from_ordered(facts_vec.clone());
            sink = planning_sink();
            planning_facts = facts_vec.clone();
            bounded_execute_from_frontier_position(
                &mut planning,
                &tactic_context,
                &mut planning_facts,
                StatementPrerequisitePolicy::Planning,
                Some(Construction {
                    environments: construction_environments,
                    sink: &mut sink,
                }),
            )?;
        }
        let construction = sink;
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
                ProofStep::Have { .. }
                    | ProofStep::UnfoldPredicate(_)
                    | ProofStep::TransportUsing { .. }
                    | ProofStep::Step
            )
        }) && construction
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Step));
        let applied = if linear_supported {
            let mut proof = self.clone();
            for step in &construction.steps {
                proof = proof.apply_step(step.clone())?;
            }
            Some(proof)
        } else if construction
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::If { .. }))
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
            .presentation
            .surface_record
            .last_step_entry = construction.last_step_entry;
        Ok(Self {
            context: proof.context.clone(),
            state: KernelProofObject::new(
                ProofState {
                    locals: proof.state.locals.clone(),
                    open_branches: proof.state.open_branches.replace_frontier_at(
                        proof.focused_branch_id(),
                        proof.facts().clone(),
                        successor_execution,
                    ),
                    added_facts: proof.state.added_facts.clone(),
                    checked_facts: proof.state.checked_facts.clone(),
                },
                proof.focused_branch_id(),
            ),
            node: proof.node.clone(),
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
        let mut facts = self.facts().to_vec();
        let base_facts = facts.len();
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.presentation.expansion,
            context.constants.proof_site.as_ref(),
        );
        let smart_certificate =
            check_mid_execution_have(have, &mut execution, &tactic_context, &mut facts)?;
        if capture_this_tactic {
            // The tactic's expansion is the law's own surface certificate.
            let expansion = ProofCertificateBuilder {
                steps: smart_certificate
                    .as_ref()
                    .map(|certificate| certificate.steps().to_vec())
                    .unwrap_or_default(),
                ..ProofCertificateBuilder::default()
            };
            finish_tactic_expansion_capture(expansion_capture.as_deref_mut(), &expansion, false);
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
                [step @ ProofStep::Have { .. }] => step.clone(),
                _ => ProofStep::Have {
                    proposition: have.proposition.clone(),
                    proof: Box::new(certificate),
                },
            },
            (None, SourceProof::Script(tactics)) => ProofStep::Have {
                proposition: have.proposition.clone(),
                proof: Box::new(ProofCertificate::from_proof_tactics(tactics).map_err(
                    |error| {
                        self.step_error(format!(
                            "`have` body is not surface-expressible: {error:?}"
                        ))
                    },
                )?),
            },
            (None, _) => ProofStep::Have {
                proposition: have.proposition.clone(),
                proof: Box::new(
                    ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption])
                        .expect("assumption is a simple proof"),
                ),
            },
        };
        Ok(Self {
            context: self.context.clone(),
            state: KernelProofObject::new(
                ProofState {
                    locals: self.state().locals.clone(),
                    open_branches: self.state().open_branches.replace_frontier_at(
                        self.focused_branch_id(),
                        proof_facts,
                        execution,
                    ),
                    added_facts: Arc::new(added),
                    checked_facts: Arc::new(Vec::new()),
                },
                self.focused_branch_id(),
            ),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(have_step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        })
    }

    /// Records where the checked `close_invariants` tactic sat, so the
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
        execution.presentation.invariant_closer_step = Some(InvariantCloserStep {
            tactic_index,
            source_index,
            statement_index: execution.core.frontier.next_statement_index,
        });
        Ok(Self {
            context: self.context.clone(),
            state: KernelProofObject::new(
                ProofState {
                    locals: self.state().locals.clone(),
                    open_branches: self.state().open_branches.replace_frontier_at(
                        self.focused_branch_id(),
                        self.facts().clone(),
                        execution,
                    ),
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                },
                self.focused_branch_id(),
            ),
            node: self.node.clone(),
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
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("a region `simp` is only available in a loop-region proof"));
        }
        execution.core.region_simp = Some((tactic_index, source_index));
        Ok(Self {
            context: self.context.clone(),
            state: KernelProofObject::new(
                ProofState {
                    locals: self.state().locals.clone(),
                    open_branches: self.state().open_branches.replace_frontier_at(
                        self.focused_branch_id(),
                        self.facts().clone(),
                        execution,
                    ),
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                },
                self.focused_branch_id(),
            ),
            node: self.node.clone(),
        })
    }

    /// Applies a frontier-local `loop` tactic as one checked operation on
    /// the focused branch execution frontier: the loop's phases verify through the
    /// shared loop-planning machinery, the certified loop rule replaces the
    /// `while` statement in the frontier's own statement tree, and the
    /// derived exit facts join this goal's context. The surface record and
    /// expansion capture ride the transitional cursor exactly as the
    /// checked form recorded them.
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
        let mut facts = self.facts().to_vec();
        let base_facts = facts.len();
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.presentation.expansion,
            context.constants.proof_site.as_ref(),
        );
        let _timing = TacticTiming::new(
            context.claim_label,
            tactic_index,
            source_index,
            &ProofTactic::Loop(loop_clause.clone()),
            execution.core.frontier.next_statement_index,
        );
        let expanded_loop = execute_frontier_local_loop(
            expansion_capture.as_deref_mut(),
            loop_clause,
            &mut execution,
            &tactic_context,
            &mut facts,
            source_index,
        )?;
        if capture_this_tactic {
            // The tactic's expansion is the expanded loop itself.
            let expansion = ProofCertificateBuilder {
                steps: ProofCertificate::from_proof_tactics(std::slice::from_ref(
                    &ProofTactic::Loop(expanded_loop.clone()),
                ))
                .expect("an expanded loop is one proof step")
                .steps()
                .to_vec(),
                ..ProofCertificateBuilder::default()
            };
            finish_tactic_expansion_capture(expansion_capture, &expansion, false);
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
            state: KernelProofObject::new(
                ProofState {
                    locals: self.state().locals.clone(),
                    open_branches: self.state().open_branches.replace_frontier_at(
                        self.focused_branch_id(),
                        proof_facts,
                        execution,
                    ),
                    added_facts: Arc::new(added),
                    checked_facts: Arc::new(Vec::new()),
                },
                self.focused_branch_id(),
            ),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(loop_step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        })
    }
}
