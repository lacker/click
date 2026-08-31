//! Execution branch preparation, sibling arms, and join merging.

use super::*;

impl<'a> Proof<'a> {
    /// Opens the C `if` at an execution frontier into its kernel-feasible
    /// checked arms.
    ///
    /// This is a structural operation rather than a surface `Step`: branch
    /// entry owns condition certification, path-fact admission, and movement
    /// to each selected arm. The enclosing `Branch` certificate is recorded
    /// only when those descendants join.
    /// Performs the audited C-branch entry work shared by the container
    /// and the in-`Proof` sibling split: guards, source resolution, the
    /// kernel condition transitions, and each feasible arm's checked facts,
    /// snapshot, path-fact delta, and condition theorem. There is exactly
    /// one implementation of this branch-entry law.
    /// Whether the execution frontier is a C `if` whose condition, spelled
    /// at the statement entry, is `surface_condition`. A proof `if` whose
    /// arms begin with statement steps has the same shape whether it enters
    /// a C branch or splits the proof logically; only the frontier decides.
    /// The C condition anchored at a different statement entry is a checked
    /// branch spelling that names the wrong statement; that is an error, not
    /// a logical split.
    pub(in crate::surface::proof) fn frontier_is_execution_branch(
        &self,
        surface_condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(false);
        };
        let Some(execution) = self.execution() else {
            return Ok(false);
        };
        if self.state().open_branches().is_discharged()
            || !matches!(self.focused_obligation(), Some(Obligation::Frontier(_)))
        {
            return Ok(false);
        }
        let statement_index = execution.core.frontier.next_statement_index;
        if !context
            .constants
            .source_layout
            .statement(statement_index)
            .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }))
        {
            return Ok(false);
        }
        let Ok((_, _, CStatement::If { condition, .. }, _)) =
            next_top_level_statement_from_frontier_position(
                execution.view(context),
                &execution.core.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "branch",
            )
        else {
            return Ok(false);
        };
        let entry_point = ProgramPointRef {
            region: CodeRegionRef::Statement(statement_index),
            kind: ProgramPointKind::Entry,
        };
        let checked = surface_at_snapshot(&surface_c_condition(&condition), &entry_point)?;
        if checked == *surface_condition {
            return Ok(true);
        }
        if proposition_contains_at_expression(surface_condition)
            && surface_at_snapshot(surface_condition, &entry_point)
                .is_ok_and(|reanchored| reanchored == checked)
        {
            return Err(self.step_error(
                "expanded execution branch condition does not match the checked C branch",
            ));
        }
        Ok(false)
    }

    pub(super) fn prepare_execution_branch(&self) -> Result<PreparedExecutionBranch, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`branch` requires an execution-frontier proof"));
        };
        if self.state().open_branches().is_discharged()
            || !matches!(self.focused_obligation(), Some(Obligation::Frontier(_)))
        {
            return Err(self.step_error("`branch` requires an open execution frontier"));
        }
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let statement_index = execution.core.frontier.next_statement_index;
        let source_region = context
            .constants
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`branch` could not resolve source statement({statement_index})"
                ))
            })?;
        let SourceStatementKind::If {
            then_statement_index,
            else_statement_index,
        } = source_region.kind
        else {
            return Err(self.step_error(format!(
                "`branch` requires a C `if` at the execution frontier, but statement({statement_index}) is not an `if`"
            )));
        };
        let (execution_start_state, current_state, statement, remaining) =
            next_top_level_statement_from_frontier_position(
                execution.view(context),
                &execution.core.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "branch",
            )?;
        let CStatement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        else {
            return Err(self.step_error("`branch` source region did not contain a C `if`"));
        };
        let surface_condition = surface_at_snapshot(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let (checked_condition_split, transitions) = certified_proof_condition_split(
            &current_state,
            &self.facts(),
            &condition,
            &format!(
                "`{}` tactic {}: `branch`",
                context.claim_label, context.tactic_index
            ),
        )?;
        let mut arms: [Option<PreparedExecutionArm>; 2] = [None, None];
        for transition in transitions {
            let take_then = transition.is_true;
            let selected_branch = if take_then {
                then_branch.as_ref()
            } else {
                else_branch.as_ref()
            };
            let mut arm_execution = execution.clone();
            record_statement_program_snapshot_state(
                &mut arm_execution.presentation.recorded_snapshots,
                context.function_block,
                statement_index,
                ProgramPointKind::Entry,
                current_state.clone(),
            );
            let resolved_state = crate::kernel::resolve_pending_heap_allocations(
                &current_state,
                transition.pure_facts.assumptions(),
            );
            if resolved_state.memory().has_pending_heap_allocation() {
                return Err(self.step_error(
                    "checked `branch` cannot yet own an unresolved heap-allocation outcome split",
                ));
            }
            arm_execution.core.frontier.next_statement_index = if take_then {
                then_statement_index
            } else {
                else_statement_index
            };
            arm_execution.core.frontier.execution_start_state = Some(execution_start_state.clone());
            arm_execution.core.state = resolved_state.into();
            // The arm frontier owns exactly the arm's own statement tree:
            // exhausting it reaches the typed region boundary, and the join
            // restores the parent frontier. Enclosing continuations belong
            // to the parent, never to a bounded arm.
            arm_execution.core.frontier.continuations = PersistentSequence::default();
            arm_execution.core.frontier.region = ExecutionRegionKind::BranchArm;
            if matches!(selected_branch, CStatement::Skip) {
                record_statement_program_snapshot_state(
                    &mut arm_execution.presentation.recorded_snapshots,
                    context.function_block,
                    statement_index,
                    ProgramPointKind::Exit,
                    (*arm_execution.core.state).clone(),
                );
                arm_execution.core.frontier.position = FrontierPosition::RegionBoundary;
            } else {
                arm_execution.core.frontier.position = FrontierPosition::StatementEntry {
                    remaining: Arc::new(selected_branch.clone()),
                };
            }
            record_current_statement_entry(
                &arm_execution.core.frontier,
                &mut arm_execution.presentation.recorded_snapshots,
                &arm_execution.core.state,
                context.function_block,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "branch",
            )?;
            let surface_path_fact = if take_then {
                surface_condition.clone()
            } else {
                negate_click_proposition(&surface_condition)
            };
            let pre_state = context
                .old_reference_state(&arm_execution.core.frontier, &arm_execution.core.state);
            let kernel_path_fact = lower_fixed_state_proposition_with_assumptions(
                &surface_path_fact,
                transition.pure_facts.assumptions(),
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                &arm_execution.core.state,
                None,
                &arm_execution.presentation.recorded_snapshots,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "could not retain the checked C branch condition form: {message}"
                ))
            })?;
            arm_execution
                .presentation
                .surface_propositions
                .record_lowering(&surface_path_fact, &kernel_path_fact)?;
            arm_execution
                .presentation
                .branch_surface_facts
                .insert(kernel_path_fact.clone());
            arm_execution
                .presentation
                .branch_decisions
                .push(ExecutionBranchDecision {
                    condition: surface_condition.clone(),
                    value: take_then,
                    proof_case: false,
                });
            arm_execution.core.has_structured_branch_history = true;
            arm_execution.presentation.branch_path.push(format!(
                "{} arm of C `if` at statement({statement_index})",
                if take_then { "then" } else { "else" }
            ));
            arm_execution
                .core
                .record_condition_transition(transition.theorem.clone());
            arms[usize::from(!take_then)] = Some(PreparedExecutionArm {
                facts: transition.pure_facts,
                execution: arm_execution,
                path_facts: transition.path_facts,
                condition_theorem: transition.theorem,
            });
        }
        if arms.iter().all(Option::is_none) {
            return Err(self.step_error("`branch` found no feasible C `if` arm"));
        }
        Ok(PreparedExecutionBranch {
            statement_index,
            continuation_index: source_region.continuation_node,
            continuation_remaining: remaining.map(Arc::new),
            execution_start_state,
            checked_condition_split,
            arms,
        })
    }

    /// Splits the focused branch execution frontier at a C `if` into sibling
    /// frontier goals inside this same proof state: the in-`Proof` form of
    /// the execution branch. Each kernel-feasible arm becomes one sibling
    /// goal owning its checked arm facts and snapshot; the returned record
    /// carries the split identity, per-arm condition theorems, split-time
    /// fact bases for `introduced_since`, and the shared continuation data
    /// its joins verify — bookkeeping, never semantic authority.
    /// The delta checks both execution join variants share: the arm kept
    /// its recorded condition polarity, and every check store the join
    /// migrates changed by exactly the arm's claimed introduction delta,
    /// while the unmigrated stores did not change at all.
    pub(super) fn validate_execution_join_arm_deltas(
        &self,
        variant: &str,
        name: &str,
        expected: bool,
        arm: &CheckedExecutionJoinArm<'_>,
        parent_execution: &ExecutionProofState,
    ) -> Result<(), ClickError> {
        if let Some(condition_theorem) = arm.condition_theorem
            && !matches!(
                implication_body(condition_theorem.proposition()),
                Proposition::CConditionEvaluates {
                    outcome: CConditionOutcome::Value(actual),
                    ..
                } if *actual == expected
            )
        {
            return Err(self.step_error(format!("{name} arm retained the wrong condition theorem")));
        }
        if arm
            .execution
            .core
            .function_entry_execution_prerequisites
            .len()
            != parent_execution
                .core
                .function_entry_execution_prerequisites
                .len()
                + arm.introduced_prerequisites.len()
            || arm.execution.core.function_entry_derivations.len()
                != parent_execution.core.function_entry_derivations.len()
                    + arm.introduced_derivations.len()
            || arm.execution.presentation.frontier_loop_clauses.len()
                != parent_execution.presentation.frontier_loop_clauses.len()
                    + arm.introduced_loop_clauses.len()
            || arm.execution.core.frontier_loop_rules.len()
                != parent_execution.core.frontier_loop_rules.len() + arm.introduced_loop_rules.len()
            || arm.execution.core.unfolded_predicates.len()
                != parent_execution.core.unfolded_predicates.len() + arm.introduced_unfolds.len()
            || arm
                .execution
                .presentation
                .planned_statement_transitions
                .len()
                != parent_execution
                    .presentation
                    .planned_statement_transitions
                    .len()
        {
            return Err(self.step_error(format!(
                "{name} execution arm changed check metadata that the checked {variant} has not migrated"
            )));
        }
        Ok(())
    }

    /// The retention law for a decided `branch ensuring`: the explicit
    /// interface is validated on the sole kernel-feasible arm with no
    /// abstraction or resource merge — the surviving checked state remains
    /// the successor, so ownership assertions are safe here even though
    /// two-arm ownership normalization has not migrated. Produces the arm's
    /// post-interface context and the structured `Branch { ensuring, .. }`
    /// with an empty impossible arm.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn merge_decided_interface_execution_path(
        &self,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        continuation_index: usize,
        take_then: bool,
        assertions: Vec<ProofAssertion>,
        arm: &CheckedExecutionJoinArm<'_>,
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        if !arm.execution.core.frontier.is_at_region_boundary()
            && !arm.execution.core.frontier.is_at_function_exit()
        {
            return Err(self.step_error(format!(
                "the sole feasible {} `branch ensuring` arm has not reached its region boundary or function exit",
                if take_then { "then" } else { "else" }
            )));
        }
        self.validate_execution_join_arm_deltas(
            "path operation",
            "the decided interface",
            take_then,
            arm,
            parent_execution,
        )?;

        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let target = ProgramPointRef {
            region: CodeRegionRef::Statement(continuation_index),
            kind: ProgramPointKind::Entry,
        };
        let mut execution = arm.execution.clone();
        let mut facts = arm.facts.clone();
        let facts_before_interface = facts.clone();
        apply_branch_interface_with_proof_facts(
            &target,
            &assertions,
            &mut execution,
            context,
            &mut facts,
            &BTreeMap::new(),
            None,
            false,
        )
        .map_err(|error| add_proof_branch_path(error, &execution.presentation.branch_path))?;
        execution.presentation.branch_path = parent_execution.presentation.branch_path.clone();
        execution.presentation.case_assumptions =
            parent_execution.presentation.case_assumptions.clone();

        let mut added_facts = arm.introduced_facts.clone();
        for assertion in &assertions {
            let ProofAssertion::Fact(surface) = assertion else {
                continue;
            };
            if let Some(fact) = execution
                .presentation
                .surface_propositions
                .unique_kernel(surface)
                && !facts_before_interface.contains_top_level(fact)
                && !added_facts.contains(fact)
            {
                added_facts.push(fact.clone());
            }
        }
        let selected = arm.certificate.clone();
        let empty = ProofCertificate::from_steps(Vec::new());
        let (then_proof, else_proof) = if take_then {
            (selected, empty)
        } else {
            (empty, selected)
        };
        let unfolded_predicates =
            arm.introduced_unfolds
                .iter()
                .fold(parent_unfolds.clone(), |mut unfolds, name| {
                    unfolds.insert(name.clone());
                    unfolds
                });
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts: added_facts,
            unfolded_predicates,
            step: ProofStep::Branch {
                ensuring: Some(assertions),
                then_proof: Box::new(then_proof),
                else_proof: Box::new(else_proof),
            },
        })
    }

    /// The retention law for a decided execution branch: the kernel
    /// certified exactly one feasible arm, so the surviving descendant's
    /// context becomes the successor while a logical `If` records the
    /// checked source condition and an empty contradictory arm. Verifies
    /// arrival at the shared continuation or function exit, condition
    /// polarity, and the migrated check deltas, and produces the `If`
    /// step. Callers assemble the successor around the arm's own context.
    pub(super) fn merge_decided_execution_path(
        &self,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        take_then: bool,
        arm: &CheckedExecutionJoinArm<'_>,
    ) -> Result<ProofStep, ClickError> {
        if !arm.execution.core.frontier.is_at_region_boundary()
            && !arm.execution.core.frontier.is_at_function_exit()
        {
            return Err(self.step_error(format!(
                "the sole feasible {} execution arm has not reached its region boundary or function exit",
                if take_then { "then" } else { "else" }
            )));
        }
        self.validate_execution_join_arm_deltas(
            "path operation",
            "the decided",
            take_then,
            arm,
            parent_execution,
        )?;

        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            parent_execution.view(context),
            &parent_execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "decided branch",
        )?;
        let CStatement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        else {
            return Err(
                self.step_error("decided execution branch root no longer points at a C `if`")
            );
        };
        let surface_condition = surface_at_snapshot(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let source_arm = if take_then {
            then_branch.as_ref()
        } else {
            else_branch.as_ref()
        };
        let entry_steps = 1 + usize::from(matches!(source_arm, CStatement::Skip));
        let mut selected_steps = Vec::with_capacity(entry_steps + arm.certificate.steps().len());
        selected_steps.push(ProofStep::Step);
        selected_steps.resize_with(entry_steps, || ProofStep::Step);
        selected_steps.extend_from_slice(arm.certificate.steps());
        let selected = ProofCertificate::from_steps(selected_steps);
        let empty = ProofCertificate::from_steps(Vec::new());
        let (then_proof, else_proof) = if take_then {
            (selected, empty)
        } else {
            (empty, selected)
        };
        Ok(ProofStep::If {
            condition: surface_condition,
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        })
    }

    pub(super) fn common_resources_after_interface_consumption(
        &self,
        parent_execution: &ExecutionProofState,
        arms: &[CheckedExecutionJoinArm<'_>; 2],
        assertions: &[ProofAssertion],
    ) -> Result<ResourceContext, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource interface requires an execution proof"));
        };
        let mut then_residual = arms[0].execution.core.state.resources().clone();
        let mut else_residual = arms[1].execution.core.state.resources().clone();
        for assertion in assertions {
            let ProofAssertion::Resource(resource) = assertion else {
                continue;
            };
            let then_expected = lower_resource_clause_at_state(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &arms[0].execution.core.state,
            )?;
            if !then_expected.is_own() {
                continue;
            }
            let else_expected = lower_resource_clause_at_state(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &arms[1].execution.core.state,
            )?;
            then_residual = then_residual
                .without_fact_incrementally(&then_expected, arms[0].facts.assumptions())
                .ok_or_else(|| {
                    self.step_error(
                        "then arm could not consume its established `branch ensuring` ownership representation",
                    )
                })?;
            else_residual = else_residual
                .without_fact_incrementally(&else_expected, arms[1].facts.assumptions())
                .ok_or_else(|| {
                    self.step_error(
                        "else arm could not consume its established `branch ensuring` ownership representation",
                    )
                })?;
        }
        ResourceContext::common_exact_descendant(
            &then_residual,
            &else_residual,
            parent_execution.core.state.resources(),
        )
        .ok_or_else(|| {
            self.step_error(
                "checked `branch ensuring` resource snapshots do not descend from the branch root",
            )
        })
    }

    /// The merge law for a checked two-arm interface join: each arm is
    /// independently abstracted through the explicit `branch ensuring`
    /// interface before any result is selected, the join is accepted only
    /// when the abstract states and exported facts agree exactly, and the
    /// owned resource interface is consumed from both concrete arms before
    /// intersecting their residuals. Produces the abstract continuation
    /// context and the `Branch { ensuring, .. }` step.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn merge_interface_execution_join(
        &self,
        parent_facts: &ProofFacts,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        continuation_index: usize,
        continuation_remaining: &Option<Arc<CStatement>>,
        execution_start_state: CState,
        assertions: Vec<ProofAssertion>,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        let join_continuation = derive_execution_join_continuation(
            parent_execution,
            continuation_remaining,
            continuation_index,
        );
        for (name, expected, arm) in [("then", true, &arms[0]), ("else", false, &arms[1])] {
            if !arm.execution.core.frontier.is_at_region_boundary() {
                return Err(self.step_error(format!(
                    "{name} `branch ensuring` arm has not reached its region boundary"
                )));
            }
            self.validate_execution_join_arm_deltas(
                "interface join",
                name,
                expected,
                arm,
                parent_execution,
            )?;
        }
        let common_snapshots = arms[0]
            .execution
            .presentation
            .recorded_snapshots
            .common_descendant(
                &arms[1].execution.presentation.recorded_snapshots,
                &parent_execution.presentation.recorded_snapshots,
            )
            .ok_or_else(|| {
                self.step_error(
                    "`branch ensuring` arms do not descend from the root recorded snapshots",
                )
            })?;

        let mut stable_join_locals = arms[0]
            .execution
            .core
            .state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect::<BTreeMap<_, _>>();
        stable_join_locals
            .retain(|name, value| arms[1].execution.core.state.locals().get(name) == Some(value));
        // The interface anchors at its continuation's entry. A `branch
        // ensuring` that ends its region has no live parent continuation,
        // but the patched source layout supplies the same statically known
        // continuation statement the arms recorded at their boundaries.
        let target = ProgramPointRef {
            region: CodeRegionRef::Statement(match &join_continuation {
                Some(join) => join.next_statement_index,
                None => continuation_index,
            }),
            kind: ProgramPointKind::Entry,
        };
        let sibling_join_states: [&CState; 2] =
            [&arms[0].execution.core.state, &arms[1].execution.core.state];

        let abstract_arm = |arm: &CheckedExecutionJoinArm<'_>| -> Result<
            (ExecutionProofState, ProofFacts),
            ClickError,
        > {
            let mut execution = arm.execution.clone();
            let mut facts = arm.facts.clone();
            let ProofContext::Execution(context) = self.context.as_ref() else {
                unreachable!("execution branch retained a non-execution context")
            };
            apply_branch_interface_with_proof_facts(
                &target,
                &assertions,
                &mut execution,
                context,
                &mut facts,
                &stable_join_locals,
                Some(&sibling_join_states),
                true)
            .map_err(|error| add_proof_branch_path(error, &execution.presentation.branch_path))?;
            Ok((execution, facts))
        };
        let (mut then_abstract, then_interface_facts) = abstract_arm(&arms[0])?;
        let (else_abstract, else_interface_facts) = abstract_arm(&arms[1])?;

        let then_interface_vec = then_interface_facts.to_vec();
        let else_interface_vec = else_interface_facts.to_vec();
        if then_interface_vec != else_interface_vec
            || *then_abstract.core.state != *else_abstract.core.state
        {
            return Err(self.step_error(
                "`branch ensuring` arms produced different abstract successor states",
            ));
        }

        // Consume owned exports from both concrete arms before intersecting
        // their exact residuals. Re-adding the normalized interface below
        // therefore neither duplicates a common representation nor loses the
        // portion of ownership selected by the interface.
        let common_resources = self.common_resources_after_interface_consumption(
            parent_execution,
            &arms,
            &assertions,
        )?;

        // Owned interface facts were consumed above and must be restored once.
        // Duplicable views are added only when the residual common context
        // does not already establish them.
        let mut resources = common_resources;
        let additions = then_abstract
            .core
            .state
            .resources()
            .facts()
            .iter()
            .filter(|fact| {
                fact.is_own() || !resources.satisfies_fact(fact, then_interface_facts.assumptions())
            })
            .cloned()
            .collect::<Vec<_>>();
        resources = resources
            .try_compose_into_valid_context_delaying_normalization(
                additions.iter().cloned(),
                then_interface_facts.assumptions(),
            )
            .map_err(|error| {
                self.step_error(format!(
                    "invalid automatic common `branch ensuring` resource interface: {error:?}"
                ))
            })?
            .normalized_around_facts(&additions, then_interface_facts.assumptions());
        let state = (*then_abstract.core.state)
            .clone()
            .with_resource_context(resources);
        then_abstract.core.state = state.into();

        let abstract_state = (*then_abstract.core.state).clone();
        let mut execution = parent_execution.clone();
        execution.core.has_empty_execution_branch_leaf |=
            then_abstract.core.has_empty_execution_branch_leaf
                || else_abstract.core.has_empty_execution_branch_leaf;
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [&then_abstract, &else_abstract],
        )?;
        execution.core.state = abstract_state.clone().into();
        execution.presentation.recorded_snapshots = common_snapshots;
        execution
            .presentation
            .recorded_snapshots
            .insert(target, abstract_state.clone());
        execution.presentation.recorded_snapshots.insert(
            ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Exit,
            },
            abstract_state.clone(),
        );
        execution.core.frontier.execution_start_state = Some(execution_start_state);
        match join_continuation {
            Some(join) => {
                execution.core.frontier.next_statement_index = join.next_statement_index;
                execution.core.frontier.continuations = join.continuations;
                execution.core.frontier.position = FrontierPosition::StatementEntry {
                    remaining: join.remaining,
                };
            }
            None => {
                // The joined `branch ensuring` ends its enclosing region:
                // the parent rests at its own typed boundary.
                execution.core.frontier.continuations = PersistentSequence::default();
                if !finish_exhausted_region(&mut execution.core.frontier) {
                    return Err(self.step_error(
                        "execution `branch` reached the end of the function without a return",
                    ));
                }
            }
        }
        execution.core.has_structured_branch_history = true;
        execution.core.execution_abstraction = true;
        execution.core.unfolded_predicates.clear();
        execution.presentation.case_assumptions.clear();
        execution.core.next_opaque_call = then_abstract
            .core
            .next_opaque_call
            .max(else_abstract.core.next_opaque_call);
        execution.core.next_kernel_variable = then_abstract
            .core
            .next_kernel_variable
            .max(else_abstract.core.next_kernel_variable);
        for effect in arms[0]
            .introduced_effect_facts
            .iter()
            .chain(&arms[1].introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.core.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in arms[0]
            .introduced_prerequisites
            .iter()
            .chain(&arms[1].introduced_prerequisites)
        {
            execution
                .core
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in arms[0]
            .introduced_derivations
            .iter()
            .chain(&arms[1].introduced_derivations)
        {
            execution
                .core
                .function_entry_derivations
                .insert(theorem.clone());
        }
        migrate_arm_loop_proofs(&mut execution, &arms);
        execution.presentation.branch_path.clear();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        record_statement_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            context.function_block,
            statement_index,
            ProgramPointKind::Exit,
            abstract_state,
        );
        record_current_statement_entry(
            &execution.core.frontier,
            &mut execution.presentation.recorded_snapshots,
            &execution.core.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "branch ensuring",
        )?;

        let mut facts = parent_facts.clone();
        let mut added_facts = Vec::new();
        let mut retain_fact = |fact: &Proposition| -> Result<(), ClickError> {
            if !facts.contains_top_level(fact) {
                facts = facts.with_fact(fact.clone());
                added_facts.push(fact.clone());
            }
            for surface in then_abstract.surface_propositions.surfaces(fact) {
                if else_abstract
                    .surface_propositions
                    .surfaces(fact)
                    .any(|candidate| candidate == surface)
                {
                    execution
                        .presentation
                        .surface_propositions
                        .record_lowering(surface, fact)?;
                }
            }
            Ok(())
        };
        for fact in &then_interface_vec {
            retain_fact(fact)?;
        }
        let else_introduced: std::collections::BTreeSet<&Proposition> =
            arms[1].introduced_facts.iter().collect();
        for fact in &arms[0].introduced_facts {
            if else_introduced.contains(fact)
                && arms[0].facts.contains(fact)
                && arms[1].facts.contains(fact)
            {
                retain_fact(fact)?;
            }
        }

        #[cfg(test)]
        CHECKED_EXECUTION_INTERFACE_JOINS.with(|count| count.set(count.get() + 1));

        let [then_view, else_view] = arms;
        let step = ProofStep::Branch {
            ensuring: Some(assertions),
            then_proof: Box::new(then_view.certificate),
            else_proof: Box::new(else_view.certificate),
        };
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts: added_facts,
            unfolded_predicates: parent_unfolds.clone(),
            step,
        })
    }

    /// Joins the two sibling execution frontier goals created by
    /// [`Proof::split_focused_execution_branch`] through one explicit
    /// common frontier interface, resuming the parent obligation under its
    /// original id with the abstract continuation context. A one-arm split
    /// is a decided path: the interface is validated on the sole sibling
    /// with no abstraction or resource merge, as in the container form.
    pub(in crate::surface::proof) fn join_focused_execution_interface(
        &self,
        record: &ExecutionSplit<'a>,
        assertions: Vec<ProofAssertion>,
    ) -> Result<Self, ClickError> {
        let sole_arm = match record.arm_branches {
            [Some(id), None] => Some((true, 0usize, id)),
            [None, Some(id)] => Some((false, 1, id)),
            _ => None,
        };
        if let Some((take_then, arm_index, id)) = sole_arm {
            let [mut steps, trailing] =
                self.partition_steps_since(&record.marker, record.split, [id, id])?;
            steps.extend(trailing);
            let name = if take_then { "then" } else { "else" };
            let (selection, view) =
                self.sibling_execution_arm_view(record, name, arm_index, id, steps)?;
            let mut parts = self.merge_decided_interface_execution_path(
                &record.parent_unfolds,
                &record.parent_execution,
                record.continuation_index,
                take_then,
                assertions,
                &view,
            )?;
            self.install_parent_frontier_after_decided(&mut parts.execution, record)?;
            return self.resume_parent_after_sibling_join(record, [id, id], selection, parts);
        }
        let (ids, selection, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_interface_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.continuation_index,
            &record.continuation_remaining,
            record.execution_start_state.clone(),
            assertions,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, selection, parts)
    }

    /// Carries only checked C-branch anchor spellings across a structural
    /// join. The persistent fact set is owned by `Proof`; it retains exact
    /// historical premises and extraction spellings without publishing
    /// unrelated arm-local predicate or resource provenance.
    pub(super) fn merge_branch_surface_facts(
        &self,
        execution: &mut ExecutionProofState,
        parent: &ExecutionProofState,
        arms: [&ExecutionProofState; 2],
    ) -> Result<(), ClickError> {
        for arm in arms {
            let introduced = arm
                .branch_surface_facts
                .introduced_since(&parent.branch_surface_facts)
                .ok_or_else(|| {
                    self.step_error(
                        "execution branch surface facts do not descend from the split root",
                    )
                })?;
            for fact in introduced {
                for surface in arm.surface_propositions.surfaces(&fact) {
                    execution
                        .presentation
                        .surface_propositions
                        .record_lowering(surface, &fact)?;
                }
                execution.presentation.branch_surface_facts.insert(fact);
            }
        }
        Ok(())
    }

    /// The merge law for a terminal two-arm execution join: both arms
    /// completed at function exit, so distinct return outcomes remain as
    /// separate paths instead of requiring one equal C state. Produces the
    /// function-exit continuation context and the structured logical `If`
    /// step, wrapping each arm's body certificate with its explicit entry
    /// steps. Callers assemble the successor proof.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn merge_terminal_execution_join(
        &self,
        parent_facts: &ProofFacts,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        execution_start_state: CState,
        proof_case_condition: Option<ClickProposition>,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        // Both arms completed at function exit. Their outcomes remain
        // separate paths, each with its own state and resources, and kernel
        // certification runs once per recorded case, so the arms' resource
        // contexts need not agree.
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("terminal execution join retained a non-execution context")
        };
        let proof_case_split = proof_case_condition.is_some();
        let (surface_condition, empty_source_arms) = if let Some(condition) = proof_case_condition {
            (condition, [false, false])
        } else {
            let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
                parent_execution.view(context),
                &parent_execution.core.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "terminal branch join",
            )?;
            let CStatement::If {
                condition,
                then_branch,
                else_branch,
            } = statement
            else {
                return Err(
                    self.step_error("terminal execution branch root no longer points at a C `if`")
                );
            };
            (
                surface_at_snapshot(
                    &surface_c_condition(&condition),
                    &ProgramPointRef {
                        region: CodeRegionRef::Statement(statement_index),
                        kind: ProgramPointKind::Entry,
                    },
                )?,
                [
                    matches!(then_branch.as_ref(), CStatement::Skip),
                    matches!(else_branch.as_ref(), CStatement::Skip),
                ],
            )
        };
        for (name, expected, arm) in [("then", true, &arms[0]), ("else", false, &arms[1])] {
            if !arm.execution.core.frontier.is_at_function_exit() {
                return Err(self.step_error(format!(
                    "{name} branch arm has not completed at function exit"
                )));
            }
            self.validate_execution_join_arm_deltas(
                "terminal join",
                name,
                expected,
                arm,
                parent_execution,
            )?;
        }

        let terminal_certificate = |body: &ProofCertificate, empty_source_arm: bool| {
            let entry_steps = 1 + usize::from(empty_source_arm);
            let mut steps = Vec::with_capacity(entry_steps + body.steps().len());
            steps.push(ProofStep::Step);
            steps.resize_with(entry_steps, || ProofStep::Step);
            steps.extend_from_slice(body.steps());
            ProofCertificate::from_steps(steps)
        };
        let then_proof = if proof_case_split {
            arms[0].certificate.clone()
        } else {
            terminal_certificate(&arms[0].certificate, empty_source_arms[0])
        };
        let else_proof = if proof_case_split {
            arms[1].certificate.clone()
        } else {
            terminal_certificate(&arms[1].certificate, empty_source_arms[1])
        };
        let then_expansion = &arms[0].execution.presentation.expansion;
        let else_expansion = &arms[1].execution.presentation.expansion;
        let common_snapshots = arms[0]
            .execution
            .presentation.recorded_snapshots
            .common_descendant(
                &arms[1].execution.presentation.recorded_snapshots,
                &parent_execution.presentation.recorded_snapshots,
            )
            .ok_or_else(|| {
                self.step_error(
                    "terminal execution arms do not descend from the branch root's recorded snapshots",
                )
            })?;

        // Root facts remain shared in `ProofState`. Only facts introduced in
        // one arm need to be copied into that arm's returned execution paths;
        // doing so avoids duplicating the complete ambient proof context per
        // outcome.
        let mut paths = Vec::new();
        let mut execution_evidence = Vec::new();
        let mut outcome_provenance = Vec::new();
        for (arm_index, arm) in arms.iter().enumerate() {
            let completed = arm
                .execution
                .core
                .frontier
                .execution()
                .expect("validated terminal arm is at function exit");
            if completed.paths().len() != arm.execution.core.execution_evidence.len() {
                return Err(self.step_error(format!(
                    "{} terminal branch arm lost its checked execution evidence",
                    if arm_index == 0 { "then" } else { "else" }
                )));
            }
            for (arm_path_index, path) in completed.paths().iter().enumerate() {
                let mut path_facts = path.execution_facts();
                for proposition in &arm.introduced_facts {
                    let fact = ExecutionPureFact::new(proposition.clone());
                    if !path_facts.contains(&fact) {
                        path_facts.push(fact);
                    }
                }
                let obligations = path.obligations().to_vec();
                if !paths
                    .iter()
                    .any(|(existing_outcome, existing_facts, existing_obligations)| {
                        existing_outcome == path.outcome()
                            && existing_facts == &path_facts
                            && existing_obligations == &obligations
                    })
                {
                    paths.push((path.outcome().clone(), path_facts, obligations));
                    execution_evidence
                        .push(arm.execution.core.execution_evidence[arm_path_index].clone());
                    let mut provenance = arm.execution.provenance_for_outcome(arm_path_index);
                    if proof_case_split {
                        provenance.branch_decisions.push(ExecutionBranchDecision {
                            condition: surface_condition.clone(),
                            value: arm_index == 0,
                            proof_case: true,
                        });
                    }
                    outcome_provenance.push(provenance);
                }
            }
        }

        let outcomes = c_function_execution_candidates_from_outcomes(
            execution_start_state.clone(),
            context.function.clone(),
            context.arguments.to_vec(),
            paths,
        );
        let mut execution = parent_execution.clone();
        execution.core.has_empty_execution_branch_leaf |= arms
            .iter()
            .any(|arm| arm.execution.core.has_empty_execution_branch_leaf);
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [arms[0].execution, arms[1].execution],
        )?;
        execution.core.state = execution_start_state.clone().into();
        execution.presentation.recorded_snapshots = common_snapshots;
        execution.core.frontier.continuations.clear();
        execution.core.frontier.execution_start_state = Some(execution_start_state);
        execution.core.frontier.position = FrontierPosition::FunctionExit {
            execution: outcomes,
        };
        execution.core.execution_evidence = execution_evidence.into();
        execution.presentation.branch_decisions =
            parent_execution.presentation.branch_decisions.clone();
        execution.presentation.outcome_provenance = Arc::new(outcome_provenance);
        execution.core.has_structured_branch_history = true;
        execution.core.next_opaque_call = arms[0]
            .execution
            .core
            .next_opaque_call
            .max(arms[1].execution.core.next_opaque_call);
        execution.core.next_kernel_variable = arms[0]
            .execution
            .core
            .next_kernel_variable
            .max(arms[1].execution.core.next_kernel_variable);
        for effect in arms[0]
            .introduced_effect_facts
            .iter()
            .chain(&arms[1].introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.core.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in arms[0]
            .introduced_prerequisites
            .iter()
            .chain(&arms[1].introduced_prerequisites)
        {
            execution
                .core
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in arms[0]
            .introduced_derivations
            .iter()
            .chain(&arms[1].introduced_derivations)
        {
            execution
                .core
                .function_entry_derivations
                .insert(theorem.clone());
        }
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            if !execution.core.unfolded_predicates.contains(name) {
                execution.core.unfolded_predicates.push(name.clone());
            }
        }
        migrate_arm_loop_proofs(&mut execution, &arms);
        execution.presentation.branch_path = parent_execution.presentation.branch_path.clone();
        execution.presentation.case_assumptions =
            parent_execution.presentation.case_assumptions.clone();

        // A selected-site capture is attribution metadata for one source
        // occurrence. It may be inherited unchanged by both arms, or begin
        // in exactly one arm. Retain that cursor across the audited join, but
        // reject two different captures rather than guessing which source
        // occurrence owns the eventual expansion.
        let parent_capture = parent_execution
            .presentation
            .expansion
            .deferred_tactic_capture
            .as_ref();
        let then_capture = then_expansion.deferred_tactic_capture.as_ref();
        let else_capture = else_expansion.deferred_tactic_capture.as_ref();
        if parent_capture.is_some()
            && (then_capture != parent_capture || else_capture != parent_capture)
        {
            return Err(
                self.step_error("terminal execution arm lost its inherited selected-tactic cursor")
            );
        }
        execution.presentation.expansion.deferred_tactic_capture =
            match (then_capture, else_capture) {
                (Some(then_capture), Some(else_capture)) if then_capture == else_capture => {
                    Some(then_capture.clone())
                }
                (Some(capture), None) if parent_capture.is_none() => {
                    let mut capture = capture.clone();
                    capture.branch_skeleton = vec![ProofTactic::If(ProofIf {
                        condition: surface_condition.clone(),
                        then_tactics: capture.branch_skeleton,
                        else_tactics: Vec::new(),
                    })];
                    Some(capture)
                }
                (None, Some(capture)) if parent_capture.is_none() => {
                    let mut capture = capture.clone();
                    capture.branch_skeleton = vec![ProofTactic::If(ProofIf {
                        condition: surface_condition.clone(),
                        then_tactics: Vec::new(),
                        else_tactics: capture.branch_skeleton,
                    })];
                    Some(capture)
                }
                (None, None) => None,
                _ => {
                    return Err(self.step_error(
                        "terminal execution arms retained different selected-tactic cursors",
                    ));
                }
            };

        // Terminal arm tactics are source-order cursors, not semantic state.
        // Preserve only the append-only suffix each checked arm added after
        // the split root, nested under the exact condition this audited join
        // retained in its `If` provenance. Ordered finalization later asks
        // each focused branch outcome Proof to select one arm and apply those
        // ordinary operations; the joined execution frontier gains no facts,
        // C state, resources, or successor authority from this tree.
        let then_post_execution = arms[0]
            .execution
            .presentation
            .post_execution_tactics
            .suffix_since(&parent_execution.presentation.post_execution_tactics)
            .ok_or_else(|| {
                self.step_error(
                    "terminal then-arm finalization cursor does not descend from the split root",
                )
            })?;
        let else_post_execution = arms[1]
            .execution
            .presentation
            .post_execution_tactics
            .suffix_since(&parent_execution.presentation.post_execution_tactics)
            .ok_or_else(|| {
                self.step_error(
                    "terminal else-arm finalization cursor does not descend from the split root",
                )
            })?;
        if !then_post_execution.is_empty() || !else_post_execution.is_empty() {
            let attribution = then_post_execution
                .first()
                .or_else(|| else_post_execution.first())
                .expect("a nonempty terminal cursor has one attributed operation");
            execution.presentation.defer_post_execution(
                attribution.tactic_index,
                attribution.source_index,
                PostExecutionTactic::If {
                    condition: surface_condition.clone(),
                    then_tactics: then_post_execution,
                    else_tactics: else_post_execution,
                },
            );
        }

        let mut facts = parent_facts.clone();
        let mut common_added_facts = Vec::new();
        let else_introduced: std::collections::BTreeSet<&Proposition> =
            arms[1].introduced_facts.iter().collect();
        for fact in &arms[0].introduced_facts {
            if else_introduced.contains(fact)
                && arms[0].facts.contains(fact)
                && arms[1].facts.contains(fact)
                && !facts.contains(fact)
            {
                facts = facts.with_fact(fact.clone());
                common_added_facts.push(fact.clone());
                for surface in arms[0]
                    .execution
                    .presentation
                    .surface_propositions
                    .surfaces(fact)
                {
                    if arms[1]
                        .execution
                        .presentation
                        .surface_propositions
                        .surfaces(fact)
                        .any(|candidate| candidate == surface)
                    {
                        execution
                            .presentation
                            .surface_propositions
                            .record_lowering(surface, fact)?;
                    }
                }
            }
        }
        let mut unfolded_predicates = parent_unfolds.clone();
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            unfolded_predicates.insert(name.clone());
        }
        let step = ProofStep::If {
            condition: surface_condition,
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        };
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts,
            unfolded_predicates,
            step,
        })
    }

    /// The merge law for a checked two-arm execution join: verifies both
    /// arms reached the shared continuation with identical C states and
    /// matching condition polarity, re-applies each arm's introduction
    /// deltas on the parent context, and produces the continuation context
    /// plus the structured `Branch` step. Callers assemble the successor.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn merge_checked_execution_join(
        &self,
        parent_facts: &ProofFacts,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        continuation_index: usize,
        continuation_remaining: Option<Arc<CStatement>>,
        execution_start_state: CState,
        require_empty: bool,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        for (name, expected, arm) in [("then", true, &arms[0]), ("else", false, &arms[1])] {
            if require_empty && !arm.certificate.steps().is_empty() {
                return Err(self.step_error(format!(
                    "cannot use the empty execution join for a nonempty {name} arm"
                )));
            }
            if !arm.execution.core.frontier.is_at_region_boundary() {
                return Err(self.step_error(format!(
                    "{name} branch arm has not reached its shared continuation"
                )));
            }
            self.validate_execution_join_arm_deltas("join", name, expected, arm, parent_execution)?;
        }
        let then_state = &arms[0].execution.core.state;
        let else_state = &arms[1].execution.core.state;
        if **then_state != **else_state {
            return Err(self.step_error("execution `branch` arms reached different C states"));
        }
        let mut execution = parent_execution.clone();
        execution.core.has_empty_execution_branch_leaf |= arms
            .iter()
            .any(|arm| arm.execution.core.has_empty_execution_branch_leaf);
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [arms[0].execution, arms[1].execution],
        )?;
        execution.core.state = (**then_state).clone().into();
        execution.presentation.recorded_snapshots.insert(
            ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Exit,
            },
            (**then_state).clone(),
        );
        execution.core.frontier.execution_start_state = Some(execution_start_state);
        // The parent frontier continues around the joined state: its own
        // tail when it has one; otherwise control returns through the
        // parent's enclosing loop-iteration continuations, and an exhausted
        // bounded region rests at its typed boundary.
        match continuation_remaining {
            Some(remaining) => {
                execution.core.frontier.next_statement_index = continuation_index;
                execution.core.frontier.position = FrontierPosition::StatementEntry { remaining };
            }
            None => match resume_after_completed_region(&mut execution.core.frontier) {
                Some(remaining) => {
                    execution.core.frontier.position = FrontierPosition::StatementEntry {
                        remaining: remaining.into(),
                    };
                }
                None => {
                    if !finish_exhausted_region(&mut execution.core.frontier) {
                        return Err(self.step_error(
                            "execution `branch` reached the end of the function without a return",
                        ));
                    }
                }
            },
        }
        execution.core.has_structured_branch_history = true;
        execution.core.next_opaque_call = arms[0]
            .execution
            .core
            .next_opaque_call
            .max(arms[1].execution.core.next_opaque_call);
        execution.core.next_kernel_variable = arms[0]
            .execution
            .core
            .next_kernel_variable
            .max(arms[1].execution.core.next_kernel_variable);
        for effect in arms[0]
            .introduced_effect_facts
            .iter()
            .chain(&arms[1].introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.core.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in arms[0]
            .introduced_prerequisites
            .iter()
            .chain(&arms[1].introduced_prerequisites)
        {
            execution
                .core
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in arms[0]
            .introduced_derivations
            .iter()
            .chain(&arms[1].introduced_derivations)
        {
            execution
                .core
                .function_entry_derivations
                .insert(theorem.clone());
        }
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            if !execution.core.unfolded_predicates.contains(name) {
                execution.core.unfolded_predicates.push(name.clone());
            }
        }
        migrate_arm_loop_proofs(&mut execution, &arms);
        migrate_arm_loop_proofs(&mut execution, &arms);
        execution.presentation.branch_path.clear();
        execution.presentation.case_assumptions.clear();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        record_statement_program_snapshot_state(
            &mut execution.presentation.recorded_snapshots,
            context.function_block,
            statement_index,
            ProgramPointKind::Exit,
            (**then_state).clone(),
        );
        record_current_statement_entry(
            &execution.core.frontier,
            &mut execution.presentation.recorded_snapshots,
            &execution.core.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "branch",
        )?;

        let mut facts = parent_facts.clone();
        let mut common_added_facts = Vec::new();
        let else_introduced: std::collections::BTreeSet<&Proposition> =
            arms[1].introduced_facts.iter().collect();
        for fact in &arms[0].introduced_facts {
            if else_introduced.contains(fact)
                && arms[0].facts.contains(fact)
                && arms[1].facts.contains(fact)
                && !facts.contains(fact)
            {
                facts = facts.with_fact(fact.clone());
                common_added_facts.push(fact.clone());
                for surface in arms[0]
                    .execution
                    .presentation
                    .surface_propositions
                    .surfaces(fact)
                {
                    if arms[1]
                        .execution
                        .presentation
                        .surface_propositions
                        .surfaces(fact)
                        .any(|candidate| candidate == surface)
                    {
                        execution
                            .presentation
                            .surface_propositions
                            .record_lowering(surface, fact)?;
                    }
                }
            }
        }
        let mut unfolded_predicates = parent_unfolds.clone();
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            unfolded_predicates.insert(name.clone());
        }
        let [then_arm, else_arm] = arms;
        let step = ProofStep::Branch {
            ensuring: None,
            then_proof: Box::new(then_arm.certificate),
            else_proof: Box::new(else_arm.certificate),
        };
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts,
            unfolded_predicates,
            step,
        })
    }

    /// Joins the two sibling execution frontier goals created by
    /// [`Proof::split_focused_execution_branch`] at their shared
    /// continuation. Both recorded arms must be open frontier goals that
    /// reached the continuation; the interleaved steps since the split
    /// marker are partitioned into per-arm certificates by recorded
    /// attribution, each arm's introduction deltas are recovered by suffix
    /// walks against the split-time bases, and the parent obligation
    /// resumes under its original id with the merged continuation context.
    pub(in crate::surface::proof) fn join_focused_execution_branch(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        self.join_focused_execution_checked(record, false)
    }

    pub(super) fn join_focused_execution_checked(
        &self,
        record: &ExecutionSplit<'a>,
        require_empty: bool,
    ) -> Result<Self, ClickError> {
        let (ids, selection, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_checked_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.continuation_index,
            record.continuation_remaining.clone(),
            record.execution_start_state.clone(),
            require_empty,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, selection, parts)
    }

    /// Joins the two sibling execution frontier goals created by
    /// [`Proof::split_focused_execution_branch`] when both arms completed
    /// at function exit: distinct return outcomes remain as separate paths
    /// under a logical `If`, and the parent obligation resumes at function
    /// exit under its original id.
    pub(in crate::surface::proof) fn join_focused_execution_terminal(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        let (ids, selection, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_terminal_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.execution_start_state.clone(),
            None,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, selection, parts)
    }

    /// Joins the two terminal arms of a proof-level execution `if`. Both arms
    /// retain the same checked C root; the join adds only the proof `if` and
    /// its arm bodies.
    pub(in crate::surface::proof) fn join_focused_execution_if_terminal(
        &self,
        record: &ExecutionProofCaseSplit<'a>,
    ) -> Result<Self, ClickError> {
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, record.arm_branches)?;
        let (selection, then_view) = self.sibling_execution_arm_view_from_bases(
            "then",
            record.split,
            record.arm_branches[0],
            then_steps,
            &record.base_facts[0],
            &record.common_facts,
            &record.base_executions[0],
            None,
        )?;
        let (_, else_view) = self.sibling_execution_arm_view_from_bases(
            "else",
            record.split,
            record.arm_branches[1],
            else_steps,
            &record.base_facts[1],
            &record.common_facts,
            &record.base_executions[1],
            None,
        )?;
        let parts = self.merge_terminal_execution_join(
            &record.common_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.parent_execution.core.frontier.next_statement_index,
            record.execution_start_state.clone(),
            Some(record.surface_condition.clone()),
            [then_view, else_view],
        )?;
        self.resume_parent_after_sibling_join_from_marker(
            &record.marker,
            record.arm_branches,
            selection,
            parts,
        )
    }

    /// Reduces the two sibling arms of an in-`Proof` execution split to the
    /// shared per-arm join view: both recorded goals must be open execution
    /// frontiers, the steps since the split marker partition by recorded
    /// attribution into per-arm body certificates, and each arm's
    /// introduction deltas are recovered by suffix walks against the
    /// recorded split-time bases.
    #[allow(clippy::type_complexity)]
    pub(super) fn sibling_execution_arm_views<'v>(
        &'v self,
        record: &'v ExecutionSplit<'a>,
    ) -> Result<
        (
            [BranchId; 2],
            EffectGoalSelection,
            [CheckedExecutionJoinArm<'v>; 2],
        ),
        ClickError,
    > {
        let [Some(then_id), Some(else_id)] = record.arm_branches else {
            return Err(self.step_error(
                "an execution `branch` with one feasible arm is a decided path, not a join",
            ));
        };
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, [then_id, else_id])?;
        let (selection, then_view) =
            self.sibling_execution_arm_view(record, "then", 0, then_id, then_steps)?;
        let (_, else_view) =
            self.sibling_execution_arm_view(record, "else", 1, else_id, else_steps)?;
        Ok(([then_id, else_id], selection, [then_view, else_view]))
    }

    /// Reduces one sibling arm of an in-`Proof` execution split to the
    /// shared per-arm join view: the recorded goal must be an open
    /// execution frontier, the partitioned steps become its body
    /// certificate, and its introduction deltas are recovered by suffix
    /// walks against the recorded split-time bases.
    pub(super) fn sibling_execution_arm_view<'v>(
        &'v self,
        record: &'v ExecutionSplit<'a>,
        name: &str,
        arm_index: usize,
        id: BranchId,
        steps: Vec<ProofStep>,
    ) -> Result<(EffectGoalSelection, CheckedExecutionJoinArm<'v>), ClickError> {
        self.validate_checked_execution_split(record)?;
        let base_facts = record.base_facts[arm_index]
            .as_ref()
            .expect("a recorded arm id has a recorded fact base");
        let base_execution = record.base_executions[arm_index]
            .as_ref()
            .expect("a recorded arm id has a recorded execution base");
        let condition_theorem = record.condition_theorems[arm_index]
            .as_ref()
            .expect("a recorded arm id has a recorded condition theorem");
        self.sibling_execution_arm_view_from_bases(
            name,
            record.split,
            id,
            steps,
            base_facts,
            &record.parent_facts,
            base_execution,
            Some(condition_theorem),
        )
    }

    fn validate_checked_execution_split(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<(), ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("checked C branch split lost its execution context"));
        };
        let (_, current_state, statement, _) = next_top_level_statement_from_frontier_position(
            record.parent_execution.view(context),
            &record.parent_execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "branch join",
        )?;
        let CStatement::If { condition, .. } = statement else {
            return Err(self.step_error("checked C branch split no longer names a C `if`"));
        };
        let arm_theorems = [
            record.condition_theorems[0].as_ref(),
            record.condition_theorems[1].as_ref(),
        ];
        let arm_facts = [record.base_facts[0].as_ref(), record.base_facts[1].as_ref()];
        if !record.checked_condition_split.validates_exhaustive_join(
            &current_state,
            &condition,
            &record.parent_facts,
            arm_theorems,
            arm_facts,
        ) {
            return Err(self.step_error(
                "checked C branch split does not exhaust its recorded condition paths",
            ));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn sibling_execution_arm_view_from_bases<'v>(
        &'v self,
        name: &str,
        split: SplitId,
        id: BranchId,
        steps: Vec<ProofStep>,
        ancestry_facts: &'v ProofFacts,
        delta_facts: &'v ProofFacts,
        delta_execution: &'v ExecutionProofState,
        condition_theorem: Option<&'v Theorem>,
    ) -> Result<(EffectGoalSelection, CheckedExecutionJoinArm<'v>), ClickError> {
        let Some(branch) = self.state().open_branches().get(id) else {
            return Err(self.step_error(format!(
                "cannot join `branch`: the {name} arm is not an open execution frontier"
            )));
        };
        let Obligation::Frontier(frontier) = &branch.obligation else {
            return Err(self.step_error(format!(
                "cannot join `branch`: the {name} arm is not an open execution frontier"
            )));
        };
        let execution = branch.state.execution.as_deref().ok_or_else(|| {
            self.step_error(format!("{name} branch arm lost its execution state"))
        })?;
        let not_descended = || {
            self.step_error(format!(
                "cannot join `branch`: the {name} arm does not descend from split {:?}",
                split
            ))
        };
        // Fact introductions are measured against the PARENT facts, not the
        // arm's split-time base: the container seeded each arm's record with
        // the prepared introduction set, so an arm's path facts count as
        // introduced and flow into its retained outcome paths. The check
        // stores below instead diff against the arm base, matching the
        // container's empty per-arm records. The base ancestry check keeps
        // the arm honest about deriving from this exact split.
        if branch
            .state
            .facts
            .introduced_since(ancestry_facts)
            .is_none()
        {
            return Err(not_descended());
        }
        let introduced_facts = branch
            .state
            .facts
            .introduced_since(delta_facts)
            .ok_or_else(not_descended)?;
        let introduced_effect_facts = execution
            .core
            .effect_facts
            .suffix_since(&delta_execution.core.effect_facts)
            .ok_or_else(not_descended)?
            .to_vec();
        let introduced_prerequisites = execution
            .core
            .function_entry_execution_prerequisites
            .introduced_since(&delta_execution.core.function_entry_execution_prerequisites)
            .ok_or_else(not_descended)?;
        let introduced_derivations = execution
            .core
            .function_entry_derivations
            .introduced_since(&delta_execution.core.function_entry_derivations)
            .ok_or_else(not_descended)?;
        let introduced_unfolds = execution
            .core
            .unfolded_predicates
            .suffix_since(&delta_execution.core.unfolded_predicates)
            .ok_or_else(not_descended)?
            .to_vec();
        let introduced_loop_clauses = execution
            .presentation
            .frontier_loop_clauses
            .suffix_since(&delta_execution.presentation.frontier_loop_clauses)
            .ok_or_else(not_descended)?
            .to_vec();
        let introduced_loop_rules = execution
            .core
            .frontier_loop_rules
            .suffix_since(&delta_execution.core.frontier_loop_rules)
            .ok_or_else(not_descended)?
            .to_vec();
        Ok((
            frontier.selection,
            CheckedExecutionJoinArm {
                certificate: ProofCertificate::from_steps(steps),
                facts: &branch.state.facts,
                execution,
                condition_theorem,
                introduced_facts,
                introduced_effect_facts,
                introduced_prerequisites,
                introduced_derivations,
                introduced_unfolds,
                introduced_loop_clauses,
                introduced_loop_rules,
            },
        ))
    }

    /// Finishes an in-`Proof` execution split for which the kernel
    /// certified exactly one feasible arm. This is path retention, not a
    /// join: the sole sibling's evolved context becomes the continuation
    /// while a logical `If` records the checked source condition and an
    /// empty contradictory arm. The parent obligation resumes under its
    /// original id — unlike the container form, which keeps the arm's id —
    /// because the sibling form splices over the split region and enclosing
    /// attribution must keep addressing the parent.
    pub(in crate::surface::proof) fn finish_focused_execution_decided(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        let (take_then, arm_index, id) = match record.arm_branches {
            [Some(id), None] => (true, 0usize, id),
            [None, Some(id)] => (false, 1, id),
            _ => {
                return Err(self.step_error(
                    "a decided execution branch requires exactly one kernel-feasible arm",
                ));
            }
        };
        // Both partition slots name the sole arm: every step recorded since
        // the marker must be attributed to it.
        let [mut steps, trailing] =
            self.partition_steps_since(&record.marker, record.split, [id, id])?;
        steps.extend(trailing);
        let name = if take_then { "then" } else { "else" };
        let (selection, view) =
            self.sibling_execution_arm_view(record, name, arm_index, id, steps)?;
        let step = self.merge_decided_execution_path(
            &record.parent_execution,
            record.statement_index,
            take_then,
            &view,
        )?;
        let mut execution = view.execution.clone();
        self.install_parent_frontier_after_decided(&mut execution, record)?;
        execution.presentation.branch_path =
            record.parent_execution.presentation.branch_path.clone();
        execution.core.has_empty_execution_branch_leaf = true;
        let parts = CheckedExecutionJoinParts {
            execution,
            facts: view.facts.clone(),
            common_added_facts: view.introduced_facts.clone(),
            unfolded_predicates: view.introduced_unfolds.iter().fold(
                record.parent_unfolds.clone(),
                |mut unfolds, name| {
                    unfolds.insert(name.clone());
                    unfolds
                },
            ),
            step,
        };
        self.resume_parent_after_sibling_join(record, [id, id], selection, parts)
    }

    /// Consumes both sibling arm goals and resumes the parent obligation
    /// under its original id with the merged continuation context, splicing
    /// the structured join step over the split region so step attribution
    /// stays correct for enclosing splits.
    pub(super) fn resume_parent_after_sibling_join(
        &self,
        record: &ExecutionSplit<'a>,
        ids: [BranchId; 2],
        selection: EffectGoalSelection,
        parts: CheckedExecutionJoinParts,
    ) -> Result<Self, ClickError> {
        self.resume_parent_after_sibling_join_from_marker(&record.marker, ids, selection, parts)
    }

    pub(super) fn resume_parent_after_sibling_join_from_marker(
        &self,
        marker: &ProofCheckpoint<'a>,
        ids: [BranchId; 2],
        selection: EffectGoalSelection,
        parts: CheckedExecutionJoinParts,
    ) -> Result<Self, ClickError> {
        let parent_goal = marker.node.focused_branch;
        let parent_node = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `branch`: the split marker lost its root")
        })?;
        let state = self
            .state
            .publish_reserved_checked_frontier_join(
                ids,
                parent_goal,
                selection,
                parts.facts,
                parts.unfolded_predicates,
                parts.execution,
                parts.common_added_facts.clone(),
                parts.common_added_facts,
            )
            .map_err(|_| self.step_error("cannot join `branch`: invalid branch lineage"))?;
        Ok(Self {
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(parent_node.clone()),
                step: Some(Arc::new(parts.step)),
                focused_branch: parent_goal,
                depth: parent_node.depth + 1,
            }),
        })
    }

    /// Focuses one recorded sibling arm and installs that arm's split-time
    /// path facts as the proof's delta. The container gave each arm proof
    /// its own `added_facts`; with siblings sharing one proof, the cursor
    /// move re-presents the delta that created the now-focused branch obligation
    /// so smart premise selection sees the same candidates.
    pub(in crate::surface::proof) fn focus_split_arm(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_then);
        let Some(id) = record.arm_branches[arm_index] else {
            return Err(self.step_error(format!(
                "cannot focus the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            )));
        };
        let path_facts = record.path_facts[arm_index]
            .clone()
            .expect("a recorded arm id has recorded path facts");
        let state = self
            .state
            .focus_open_branch_with_fact_deltas(id, path_facts.clone(), path_facts)
            .map_err(|error| match error {
                ProofFocusError::NotOpen => {
                    self.step_error(format!("goal {id:?} is not open in this proof"))
                }
                ProofFocusError::NotAllocated => {
                    unreachable!("open-branch focus reports only whether the branch is open")
                }
            })?;
        Ok(self.with_kernel_state(state))
    }

    /// Focuses one proof-level execution case. No C transition is repeated;
    /// the recorded polarity is re-presented only as the focused branch operation's
    /// local delta.
    pub(in crate::surface::proof) fn focus_execution_if_arm(
        &self,
        record: &ExecutionProofCaseSplit<'a>,
        take_then: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_then);
        let focused_branch = self.focus_branch(record.arm_branches[arm_index])?;
        let path_facts = record.path_facts[arm_index].clone();
        Ok(focused_branch.with_kernel_state(
            focused_branch
                .state
                .with_fact_deltas(path_facts.clone(), path_facts),
        ))
    }

    /// Runs the narrow statement selector on this focused branch frontier until it
    /// reaches function exit. A nested C `if` recurses through an in-`Proof`
    /// split whose arms are focused branch runs of this same search; any other
    /// structural frontier is a search miss.
    pub(in crate::surface::proof) fn try_focused_execute_to_exit(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_focused_execute_to_exit_within(Vec::new())
    }

    /// The nested-branch execute-to-exit recursion. `enclosing` is the chain
    /// of bounded-arm split records this execution runs inside, innermost
    /// last: reaching a bounded arm's typed boundary consumes one record to
    /// continue privately into that arm's parent continuation, so a terminal
    /// path escapes exactly as many regions as it is nested inside.
    fn try_focused_execute_to_exit_within(
        &self,
        enclosing: Vec<&ExecutionSplit<'a>>,
    ) -> Result<Option<Self>, ClickError> {
        let mut proof = self.clone();
        let mut enclosing = enclosing;
        loop {
            while proof.is_at_region_boundary() {
                let Some(record) = enclosing.pop() else {
                    return Ok(None);
                };
                proof = proof.continue_arm_into_parent_frontier(record)?;
            }
            if proof.is_at_function_exit() {
                return Ok(Some(proof));
            }
            if let Some(next) = proof.try_statement_step()? {
                proof = next;
                continue;
            }
            if !proof.is_at_execution_branch()? {
                return Ok(None);
            }
            let (split, record) = proof.split_focused_execution_branch()?;
            let mut advanced = split;
            for take_then in [true, false] {
                if record.arm_id(take_then).is_none() {
                    continue;
                }
                let mut arm_enclosing = enclosing.clone();
                arm_enclosing.push(&record);
                let Some(next) = advanced
                    .focus_split_arm(&record, take_then)?
                    .try_focused_execute_to_exit_within(arm_enclosing)?
                else {
                    return Ok(None);
                };
                advanced = next;
            }
            proof = if record.sole_feasible_arm().is_some() {
                advanced.finish_focused_execution_decided(&record)?
            } else {
                advanced.join_focused_execution_terminal(&record)?
            };
        }
    }

    /// Validates and applies one already-expanded logical execution arm.
    ///
    /// Terminal and decided branches render one structural branch-entry
    /// `step()` (two for an empty C arm). The split already performed
    /// those transitions, so this checks the exact Surface operations against
    /// the C branch and applies only the remaining body steps to the focused branch
    /// sibling. No certificate is constructed or interpreted.
    pub(super) fn checked_expanded_execution_arm_entry_steps(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
        surface_condition: Option<&ClickProposition>,
    ) -> Result<Vec<ProofStep>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            record.parent_execution.view(context),
            &record.parent_execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "expanded execution branch",
        )?;
        let CStatement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        else {
            return Err(self.step_error("expanded execution branch root is not a C `if`"));
        };
        let checked_condition = surface_at_snapshot(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(record.statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        if surface_condition
            .is_some_and(|surface_condition| surface_condition != &checked_condition)
        {
            return Err(self.step_error(
                "expanded execution branch condition does not match the checked C branch",
            ));
        }
        let source_arm = if take_then {
            then_branch.as_ref()
        } else {
            else_branch.as_ref()
        };
        let entry_steps = 1 + usize::from(matches!(source_arm, CStatement::Skip));
        let mut expected = vec![ProofStep::Step];
        expected.resize_with(entry_steps, || ProofStep::Step);
        Ok(expected)
    }

    pub(in crate::surface::proof) fn focus_expanded_execution_arm_entry(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
        surface_condition: &ClickProposition,
        steps: &[ProofStep],
    ) -> Result<Option<(Self, usize)>, ClickError> {
        let expected = self.checked_expanded_execution_arm_entry_steps(
            record,
            take_then,
            Some(surface_condition),
        )?;
        let entry_steps = expected.len();
        if record.arm_id(take_then).is_none() {
            // A common extracted surface tree may retain the checked entry
            // prefix for an arm that earlier path facts make unreachable on
            // this particular outcome. Validate that prefix exactly before
            // declining to apply the remaining, structurally classified
            // syntax: there is no successor Proof on which it could act.
            if !steps.is_empty() && !arm_entry_steps_match(steps, &expected) {
                return Err(self.step_error(format!(
                    "expanded execution infeasible {} arm does not begin with its {entry_steps} checked branch-entry step(s)",
                    if take_then { "then" } else { "else" },
                )));
            }
            return Ok(None);
        }
        if !arm_entry_steps_match(steps, &expected) {
            return Err(self.step_error(format!(
                "expanded execution {} arm does not begin with its {entry_steps} checked branch-entry step(s)",
                if take_then { "then" } else { "else" },
            )));
        }
        Ok(Some((
            self.focus_split_arm(record, take_then)?,
            entry_steps,
        )))
    }

    pub(super) fn apply_focused_expanded_execution_arm(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
        surface_condition: &ClickProposition,
        steps: &[ProofStep],
    ) -> Result<Self, ClickError> {
        let Some((proof, entry_steps)) =
            self.focus_expanded_execution_arm_entry(record, take_then, surface_condition, steps)?
        else {
            return Err(self.step_error("cannot advance an infeasible expanded execution arm"));
        };
        proof.apply_execution_steps_in_arm(record, &steps[entry_steps..], true)
    }

    pub(super) fn planned_execution_step_is_supported(step: &ProofStep) -> bool {
        match step {
            ProofStep::Have { .. }
            | ProofStep::UnfoldPredicate(_)
            | ProofStep::UnfoldFunction(_)
            | ProofStep::TransportUsing { .. }
            | ProofStep::Step => true,
            ProofStep::If {
                then_proof,
                else_proof,
                ..
            } => {
                !then_proof.steps().is_empty()
                    && !else_proof.steps().is_empty()
                    && then_proof
                        .steps()
                        .iter()
                        .all(Self::planned_execution_step_is_supported)
                    && else_proof
                        .steps()
                        .iter()
                        .all(Self::planned_execution_step_is_supported)
            }
            _ => false,
        }
    }

    pub(super) fn planned_execution_steps_contain_transition(steps: &[ProofStep]) -> bool {
        steps.iter().any(|step| match step {
            ProofStep::Step => true,
            ProofStep::If {
                then_proof,
                else_proof,
                ..
            } => {
                Self::planned_execution_steps_contain_transition(then_proof.steps())
                    || Self::planned_execution_steps_contain_transition(else_proof.steps())
            }
            _ => false,
        })
    }

    /// Applies one bounded arm's step sequence. An execution-advancing step
    /// at the arm's typed boundary continues privately into the parent
    /// continuation, once, through the split record — the terminal-arm form
    /// the container allowed. Logical steps run at the boundary unchanged.
    fn apply_execution_steps_in_arm(
        &self,
        record: &ExecutionSplit<'a>,
        steps: &[ProofStep],
        expanded: bool,
    ) -> Result<Self, ClickError> {
        let mut proof = self.clone();
        let mut escaped = false;
        for step in steps {
            if !escaped
                && matches!(step, ProofStep::Step | ProofStep::If { .. })
                && proof.is_at_region_boundary()
            {
                proof = proof.continue_arm_into_parent_frontier(record)?;
                escaped = true;
            }
            proof = match step {
                ProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                } if expanded => proof.apply_expanded_execution_if(
                    condition,
                    then_proof.steps(),
                    else_proof.steps(),
                )?,
                ProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                } => proof.apply_planned_execution_if(
                    condition,
                    then_proof.steps(),
                    else_proof.steps(),
                )?,
                _ => proof.apply_step(step.clone())?,
            };
        }
        Ok(proof)
    }

    pub(super) fn apply_planned_execution_steps_inner(
        &self,
        steps: &[ProofStep],
    ) -> Result<Self, ClickError> {
        let mut proof = self.clone();
        for step in steps {
            proof = match step {
                ProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                } => proof.apply_planned_execution_if(
                    condition,
                    then_proof.steps(),
                    else_proof.steps(),
                )?,
                _ => proof.apply_step(step.clone())?,
            };
        }
        Ok(proof)
    }

    /// Applies one planner-selected whole-execution tree directly to this
    /// Proof. The generated tree is only structured Surface input: Proof
    /// validates each operation, owns every C split and join, and accepts the
    /// result only when the checked execution has reached function exit.
    pub(in crate::surface::proof) fn try_planned_execution_steps(
        &self,
        steps: &[ProofStep],
    ) -> Result<Option<Self>, ClickError> {
        if steps.is_empty()
            || !steps.iter().all(Self::planned_execution_step_is_supported)
            || !Self::planned_execution_steps_contain_transition(steps)
        {
            return Ok(None);
        }
        let proof = self.apply_planned_execution_steps_inner(steps)?;
        Ok(proof.is_at_function_exit().then_some(proof))
    }

    pub(super) fn apply_planned_execution_if(
        &self,
        _condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
    ) -> Result<Self, ClickError> {
        let (split, record) = self.split_focused_execution_branch()?;
        let mut advanced = split;
        for (take_then, steps) in [(true, then_steps), (false, else_steps)] {
            if record.arm_id(take_then).is_none() {
                continue;
            }
            let entry_steps = advanced
                .checked_expanded_execution_arm_entry_steps(&record, take_then, None)?
                .len();
            if steps.len() < entry_steps
                || !steps[..entry_steps]
                    .iter()
                    .all(|step| matches!(step, ProofStep::Step))
            {
                return Err(self.step_error(format!(
                    "planned execution {} arm does not begin with its {entry_steps} C branch-entry step(s)",
                    if take_then { "then" } else { "else" },
                )));
            }
            advanced = advanced
                .focus_split_arm(&record, take_then)?
                .apply_execution_steps_in_arm(&record, &steps[entry_steps..], false)?;
        }
        advanced.join_focused_execution_split(&record, false, None)
    }

    /// Applies an already-expanded logical C branch as one audited structural
    /// Proof transition. Source syntax supplies only its condition and simple
    /// arm operations; the split, entry validation, focused branch successors, and
    /// join remain owned by this Proof lineage.
    pub(in crate::surface::proof) fn apply_expanded_execution_if(
        &self,
        condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
    ) -> Result<Self, ClickError> {
        let (split, record) = self.split_focused_execution_branch()?;
        let mut advanced = split;
        for (take_then, steps) in [(true, then_steps), (false, else_steps)] {
            if record.arm_id(take_then).is_none() {
                if !steps.is_empty() {
                    return Err(self.step_error(format!(
                        "expanded execution {} arm is nonempty, but the checked C branch is infeasible",
                        if take_then { "then" } else { "else" },
                    )));
                }
                continue;
            }
            if !matches!(steps.last(), Some(ProofStep::Step | ProofStep::If { .. })) {
                return Err(self.step_error(format!(
                    "expanded execution {} arm does not end in a checked C step",
                    if take_then { "then" } else { "else" },
                )));
            }
            advanced = advanced
                .apply_focused_expanded_execution_arm(&record, take_then, condition, steps)?;
        }
        advanced.join_focused_execution_split(&record, false, None)
    }

    /// Restores the parent frontier around a decided arm that rests at its
    /// typed region boundary. The parent's own remaining tail continues it;
    /// with no tail, control returns through the parent's loop-iteration
    /// continuations, and an exhausted bounded parent rests at its own
    /// boundary. A terminal decided arm keeps its function exit.
    fn install_parent_frontier_after_decided(
        &self,
        execution: &mut ExecutionProofState,
        record: &ExecutionSplit<'a>,
    ) -> Result<(), ClickError> {
        // The decided path is the parent's frontier from here on, whether the
        // sole arm ended at its typed boundary or returned: a function-exit
        // frontier reached inside an arm belongs to the enclosing region, so
        // source-ordered outcome tactics see it as the function's exit.
        execution.core.frontier.region = record.parent_execution.core.frontier.region;
        if !execution.core.frontier.is_at_region_boundary() {
            return Ok(());
        }
        execution.core.frontier.continuations =
            record.parent_execution.core.frontier.continuations.clone();
        execution.core.frontier.next_statement_index = record.continuation_index;
        match record.continuation_remaining.clone() {
            Some(remaining) => {
                execution.core.frontier.position = FrontierPosition::StatementEntry { remaining };
            }
            None => match resume_after_completed_region(&mut execution.core.frontier) {
                Some(remaining) => {
                    execution.core.frontier.position = FrontierPosition::StatementEntry {
                        remaining: remaining.into(),
                    };
                }
                None => {
                    if !finish_exhausted_region(&mut execution.core.frontier) {
                        return Err(self.step_error(
                            "decided `branch` reached the end of the function without a return",
                        ));
                    }
                }
            },
        }
        Ok(())
    }

    /// The terminal-execution escape from a bounded arm: a smart or
    /// execute-to-exit operation at the arm's typed boundary continues
    /// privately into the parent's continuation, exactly as the container
    /// form allowed, using only the split record's checked continuation
    /// data. Checked statement transitions stay refused at the boundary,
    /// so only terminal execution can pass it.
    pub(in crate::surface::proof) fn continue_arm_into_parent_frontier(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(self.clone());
        };
        if !execution.core.frontier.is_at_region_boundary() {
            return Ok(self.clone());
        }
        let mut execution = execution.clone();
        self.install_parent_frontier_after_decided(&mut execution, record)?;
        let state = self
            .state
            .publish_checked_frontier_transition(
                self.facts().clone(),
                execution,
                Vec::new(),
                Vec::new(),
                false,
            )
            .map_err(|error| self.execution_update_error("continue branch arm", error))?;
        Ok(Self {
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        })
    }

    /// Preserves the original empty-arm entry point for callers that require
    /// the sibling branch region to contain no body steps.
    pub(in crate::surface::proof) fn join_focused_execution_empty(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        self.join_focused_execution_checked(record, true)
    }

    /// True when the split recorded two feasible arms and both sibling
    /// goals completed at function exit.
    /// Checks a `branch ensuring` interface on this arm's frontier: every
    /// fact is lowered here and must be available or proved by the context.
    /// A resource item is not checked this way (`Ok(false)`).
    pub(in crate::surface::proof) fn interface_facts_established(
        &self,
        assertions: &[ProofAssertion],
    ) -> Result<bool, ClickError> {
        for assertion in assertions {
            let ProofAssertion::Fact(surface) = assertion else {
                return Ok(false);
            };
            let fact = self.lower_surface_proposition(surface, "`branch ensuring` fact")?;
            if !self.facts().contains(&fact) && !self.facts().assumptions().proves(&fact) {
                return Err(self.step_error(format!(
                    "`branch ensuring` did not establish fact `{}`",
                    describe_click_proposition(surface)
                )));
            }
        }
        Ok(true)
    }

    /// Whether one arm of the split reached function exit.
    pub(in crate::surface::proof) fn arm_at_function_exit(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
    ) -> bool {
        record.arm_id(take_then).is_some_and(|id| {
            self.state()
                .open_branches()
                .get(id)
                .and_then(|branch| branch.state.execution.as_deref())
                .is_some_and(|execution| execution.core.frontier.is_at_function_exit())
        })
    }

    pub(in crate::surface::proof) fn split_arms_at_function_exit(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> bool {
        record.sole_feasible_arm().is_none()
            && record.arm_branches.iter().flatten().all(|id| {
                self.state()
                    .open_branches()
                    .get(*id)
                    .and_then(|branch| branch.state.execution.as_deref())
                    .is_some_and(|execution| execution.core.frontier.is_at_function_exit())
            })
    }

    /// Selects the structural join for an advanced in-`Proof` execution
    /// split, mirroring the container's join dispatch: an explicit
    /// interface joins (or decides) through it, a sole feasible arm is
    /// decided path retention, two returned arms join terminally, and a
    /// nonterminal region joins at the shared continuation.
    pub(in crate::surface::proof) fn join_focused_execution_split(
        &self,
        record: &ExecutionSplit<'a>,
        empty: bool,
        ensuring: Option<Vec<ProofAssertion>>,
    ) -> Result<Self, ClickError> {
        if let Some(assertions) = ensuring {
            self.join_focused_execution_interface(record, assertions)
        } else if record.sole_feasible_arm().is_some() {
            self.finish_focused_execution_decided(record)
        } else if self.split_arms_at_function_exit(record) {
            self.join_focused_execution_terminal(record)
        } else if empty {
            self.join_focused_execution_empty(record)
        } else {
            self.join_focused_execution_branch(record)
        }
    }

    pub(in crate::surface::proof) fn split_focused_execution_branch(
        &self,
    ) -> Result<(Self, ExecutionSplit<'a>), ClickError> {
        let prepared = self.prepare_execution_branch()?;
        let Some(Obligation::Frontier(_)) = self.focused_obligation() else {
            return Err(self.step_error("`branch` requires an open execution frontier"));
        };
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let unfolds = branch_state.unfolded_predicates.clone();
        let parent_facts = branch_state.facts.clone();
        let parent_execution = branch_state
            .execution
            .clone()
            .expect("the preparation requires an execution frontier");
        let mut condition_theorems: [Option<Theorem>; 2] = [None, None];
        let mut base_facts: [Option<ProofFacts>; 2] = [None, None];
        let mut base_executions: [Option<Arc<ExecutionProofState>>; 2] = [None, None];
        let mut path_facts: [Option<Vec<Proposition>>; 2] = [None, None];
        let mut arms = [None, None];
        for (arm_index, prepared_arm) in prepared.arms.into_iter().enumerate() {
            let Some(prepared_arm) = prepared_arm else {
                continue;
            };
            condition_theorems[arm_index] = Some(prepared_arm.condition_theorem);
            base_facts[arm_index] = Some(prepared_arm.facts.clone());
            path_facts[arm_index] = Some(prepared_arm.path_facts);
            let execution = Arc::new(prepared_arm.execution);
            base_executions[arm_index] = Some(execution.clone());
            arms[arm_index] = Some((prepared_arm.facts, execution));
        }
        let (state, split, arm_ids) = self
            .state
            .publish_checked_partial_frontier_split(arms, path_facts.clone())
            .map_err(|error| self.execution_update_error("`branch`", error))?;
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
        let record = ExecutionSplit {
            marker: successor.checkpoint(),
            split,
            arm_branches: arm_ids,
            condition_theorems,
            checked_condition_split: prepared.checked_condition_split,
            base_facts,
            base_executions,
            path_facts,
            parent_facts,
            parent_unfolds: unfolds,
            parent_execution,
            statement_index: prepared.statement_index,
            continuation_index: prepared.continuation_index,
            continuation_remaining: prepared.continuation_remaining,
            execution_start_state: prepared.execution_start_state,
        };
        Ok((successor, record))
    }
}

/// Whether an arm's leading steps are its checked branch-entry steps.
fn arm_entry_steps_match(steps: &[ProofStep], expected: &[ProofStep]) -> bool {
    steps.len() >= expected.len()
        && steps
            .iter()
            .zip(expected)
            .all(|(actual, expected)| actual == expected)
}

/// Carries the frontier-local loop proofs both arms established into the
/// joined check. A loop is keyed by its code region: the same C loop proved
/// in both arms is one bound clause and one verified rule.
fn migrate_arm_loop_proofs(
    execution: &mut ExecutionProofState,
    arms: &[CheckedExecutionJoinArm<'_>; 2],
) {
    for arm in arms {
        for (clause, rule) in arm
            .introduced_loop_clauses
            .iter()
            .zip(&arm.introduced_loop_rules)
        {
            if execution
                .presentation
                .frontier_loop_clauses
                .iter()
                .any(|existing: &StructuralClause| existing.region() == clause.region())
            {
                continue;
            }
            execution
                .presentation
                .frontier_loop_clauses
                .push(clause.clone());
            execution.core.frontier_loop_rules.push(rule.clone());
        }
    }
}
