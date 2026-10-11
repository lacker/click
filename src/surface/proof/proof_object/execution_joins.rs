//! Execution branch preparation, sibling arms, and join merging.

use super::*;

fn join_arm_loan_evidence(
    parent: &ExecutionProofState,
    arms: [&ExecutionProofState; 2],
    label: &str,
) -> Result<crate::kernel::CheckedLoanCallEvidenceSequence, ClickError> {
    let parent_evidence = parent.core.loan_evidence();
    let then_suffix = arms[0]
        .core
        .loan_evidence()
        .suffix_since(parent_evidence)
        .ok_or_else(|| {
            ClickError::new(format!(
                "{label} then arm loan evidence does not descend from the branch root"
            ))
        })?;
    let else_suffix = arms[1]
        .core
        .loan_evidence()
        .suffix_since(parent_evidence)
        .ok_or_else(|| {
            ClickError::new(format!(
                "{label} else arm loan evidence does not descend from the branch root"
            ))
        })?;
    let joined = crate::kernel::concat_checked_loan_evidence(parent_evidence, &then_suffix);
    Ok(crate::kernel::concat_checked_loan_evidence(
        &joined,
        &else_suffix,
    ))
}
use crate::kernel::proof::PropositionIdentityKey;
use std::collections::{BTreeMap, BTreeSet};

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
        let branch_statement = CStatement::If {
            condition: condition.clone(),
            then_branch: then_branch.clone(),
            else_branch: else_branch.clone(),
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
            self.facts(),
            &branch_statement,
            remaining.as_ref(),
            &format!(
                "`{}` tactic {}: `branch`",
                context.claim_label, context.tactic_index
            ),
            Some(context.parsed_function),
        )?;
        // A `branch` has one arm per truth value. A condition that reaches one
        // value along several checked paths -- a short-circuit, or a load
        // that may read a cell an earlier store wrote -- has more cases than
        // arms, and one arm cannot stand for two paths with different facts.
        // Refuse here, naming the cases, rather than join an arm that covers
        // only one of them.
        let repeated_value = [true, false].into_iter().find(|value| {
            transitions
                .iter()
                .filter(|transition| transition.is_true == *value)
                .count()
                > 1
        });
        let source_condition = surface_c_condition(&condition);
        let mut operand_condition = &source_condition;
        while let ClickProposition::Not(inner) = operand_condition {
            operand_condition = inner;
        }
        let short_circuit = matches!(
            operand_condition,
            ClickProposition::And(..) | ClickProposition::Or(..)
        );
        let selector = (repeated_value.is_some() || short_circuit)
            .then(|| {
                let path_facts = transitions
                    .iter()
                    .map(|transition| transition.path_facts.as_slice())
                    .collect::<Vec<_>>();
                super::super::cursor_execution::condition_path_case_split_condition(
                    &path_facts,
                    &|fact| self.facts().contains(fact),
                    &current_state,
                    context,
                )
                .and_then(|(kernel_condition, surface)| {
                    let expected = Proposition::ConditionIs(kernel_condition, true);
                    self.lower_surface_proposition(&surface, "execution path selector")
                        .ok()
                        .filter(|actual| actual == &expected)
                        .map(|_| (expected, surface))
                })
            })
            .flatten();
        // A short-circuit selector must remain explicit even when only one
        // path reaches each truth value. Assuming the negated whole condition
        // does not supply the individual false operand to a simple `step`.
        let operand_selector = short_circuit
            && transitions.len() > 1
            && selector.as_ref().is_none_or(|(expected, _)| {
                self.lower_surface_proposition(&surface_condition, "C branch condition")
                    .is_ok_and(|actual| actual != *expected)
            });
        if repeated_value.is_some() || operand_selector {
            let path_facts = transitions
                .iter()
                .map(|transition| transition.path_facts.as_slice())
                .collect::<Vec<_>>();
            let parameters = context.parsed_function.parameters();
            let cases = transitions
                .iter()
                .enumerate()
                .map(|(index, transition)| {
                    let selecting = transition
                        .path_facts
                        .iter()
                        .filter(|fact| !path_facts.iter().all(|other| other.contains(fact)))
                        .cloned()
                        .collect::<Vec<_>>();
                    format!(
                        "\n  path {}: {} {}",
                        index + 1,
                        if transition.is_true {
                            "true when"
                        } else {
                            "false when"
                        },
                        crate::surface::diagnostics::describe_pure_facts_for_diagnostic(
                            &selecting,
                            parameters,
                            context.arguments,
                        )
                    )
                })
                .collect::<String>();
            let split_condition = selector.map(|(_, surface)| surface);
            let reason = match repeated_value {
                Some(value) => format!(
                    "its condition `{}` is {value} along {} checked paths, and `branch` has one arm per truth value",
                    crate::surface::diagnostics::describe_c_expression(&condition),
                    transitions
                        .iter()
                        .filter(|transition| transition.is_true == value)
                        .count(),
                ),
                None => "its short-circuit paths need an explicit operand selector".to_string(),
            };
            let error = self.step_error(format!(
                "`branch` cannot split the C `if` at statement({statement_index}): {reason}{cases}\nSplit the proof on the facts that tell these paths apart with a proof `if` first; `execute()` makes this split itself.",
            ));
            return Err(match split_condition {
                Some(condition) => error.with_path_case_condition(condition),
                None => error.with_path_case_split(),
            });
        }
        let mut arms: [Option<PreparedExecutionArm>; 2] = [None, None];
        for transition in transitions {
            let take_then = transition.is_true;
            let selected_branch = if take_then {
                then_branch.as_ref()
            } else {
                else_branch.as_ref()
            };
            let mut arm_execution = execution.clone();
            // The arm's condition theorem is recorded while the arm still
            // stands at the parent's `if`, where the proof object checks
            // it; the arm frontier then moves into the selected branch.
            arm_execution
                .core
                .record_condition_transition(
                    context.function,
                    context.arguments,
                    transition.theorem.clone(),
                    transition.pure_facts.assumptions().clone(),
                    &transition.path_facts,
                    &[],
                )
                .map_err(|refusal| {
                    self.step_error(format!(
                        "`branch` recorded condition evidence the proof object rejected: {}",
                        crate::surface::proof::cursor_execution::describe_evidence_refusal(
                            &refusal,
                            context.parsed_function.parameters(),
                            context.arguments,
                        )
                    ))
                })?;
            record_statement_program_snapshot_state(
                &mut arm_execution.presentation.recorded_snapshots,
                context.function_block,
                statement_index,
                ProgramPointKind::Entry,
                current_state.clone(),
            );
            // Condition certification already resolved pending allocation
            // outcomes and retained that exact successor. Recomputing it
            // here creates an equal resource context with different mutation
            // ancestry, so a later checked resource exchange rejects it.
            let resolved_state = arm_execution.core.reached_state().clone();
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
                context.spec_definitions,
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
            // `surface_path_fact` already reads the `if` statement's entry
            // snapshot, so it survives the body's later stores and a bundle
            // closer on this arm may name it.
            arm_execution
                .presentation
                .path_branch_premises
                .push(surface_path_fact.clone());
            arm_execution
                .presentation
                .branch_decisions
                .push(ExecutionBranchDecision {
                    fingerprint: std::sync::OnceLock::new(),
                    condition: surface_condition.clone(),
                    value: take_then,
                });
            arm_execution.core.has_structured_branch_history = true;
            arm_execution.presentation.branch_path.push(format!(
                "{} arm of C `if` at statement({statement_index})",
                if take_then { "then" } else { "else" }
            ));
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
        if arm.execution.core.function_entry_derivations.len()
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
        let join_next_kernel_variable = execution.core.kernel_variable_mark();
        apply_branch_interface_with_proof_facts(
            &target,
            &assertions,
            &assertions,
            &mut execution,
            context,
            &mut facts,
            &BTreeMap::new(),
            None,
            join_next_kernel_variable,
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
        let empty = ProofCertificate::pruned_execution_arm();
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
        let selected = ProofCertificate::from_steps(selected_steps)?;
        let empty = ProofCertificate::pruned_execution_arm();
        let (then_proof, else_proof) = if take_then {
            (selected, empty)
        } else {
            (empty, selected)
        };
        Ok(ProofStep::If {
            condition: surface_condition,
            ensuring: None,
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
            let then_expected = lower_interface_resource_clause(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &arms[0].execution.core.state,
                arms[0].facts.assumptions(),
            )?;
            if !then_expected.is_own() {
                continue;
            }
            let else_expected = lower_interface_resource_clause(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &arms[1].execution.core.state,
                arms[1].facts.assumptions(),
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
        // The ancestor is the state the retained evidence reached, which is
        // the one the kernel's check of the join intersects against.
        ResourceContext::common_exact_descendant(
            &then_residual,
            &else_residual,
            parent_execution.core.reached_state().resources(),
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
        // The C branch the arms came from, or `None` with
        // `proof_case_condition` when they are the cases of a proof `if`.
        checked_condition_split: Option<CheckedBranchSplit>,
        proof_case_condition: Option<ClickProposition>,
        assertions: Vec<ProofAssertion>,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        // A named interface resource is a binder declared inside a proof
        // script, so it gets its field schema here, where the interface is
        // lowered, as a loop binder does. The certificate keeps the
        // assertions as written.
        let written_assertions = assertions;
        // The interface is written inside this frontier's proof scope: a
        // proof `match` arm's fields, `let` names, call-result binders. Its
        // entries name them as a `have` goal here would, so they are
        // resolved before anything is lowered.
        let proof_locals = self.proof_local_values();
        let assertions = written_assertions
            .iter()
            .map(|assertion| match assertion {
                ProofAssertion::Fact(fact) => substitute_click_proposition(fact, &proof_locals)
                    .map(ProofAssertion::Fact)
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not resolve the names in an `ensuring` fact: {message}"
                        ))
                    }),
                ProofAssertion::Resource(resource) => {
                    crate::surface::verification::substitute_resource_clause_for_summary(
                        resource,
                        &proof_locals,
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not resolve the names in an `ensuring` resource: {message}"
                        ))
                    })
                    .and_then(|resource| {
                        crate::surface::lowering::loop_resource_with_field_schema(
                            &resource,
                            context.resource_environment,
                        )
                    })
                    .map(ProofAssertion::Resource)
                }
            })
            .collect::<Result<Vec<_>, ClickError>>()?;
        // The cases of a proof `if` rejoin where they stand: at the program
        // point both arms reached, not after a C statement.
        let rejoins_cases = proof_case_condition.is_some();
        if rejoins_cases
            && !arms[0]
                .execution
                .core
                .frontier
                .at_same_program_point(&arms[1].execution.core.frontier)
        {
            return Err(self.step_error(
                "the arms of this proof `if` end at different program points, so they cannot rejoin",
            ));
        }
        // `old(...)` in an interface fact means what it means everywhere
        // else in this proof: the function's entry, also inside a loop body.
        let interface_reference_state = context
            .old_reference_state(
                &parent_execution.core.frontier,
                &parent_execution.core.state,
            )
            .clone();
        let join_continuation = derive_execution_join_continuation(
            parent_execution,
            continuation_remaining,
            continuation_index,
        );
        // The interface anchors at its continuation's entry. A `branch
        // ensuring` that ends its region has no live parent continuation,
        // but the patched source layout supplies the same statically known
        // continuation statement the arms recorded at their boundaries.
        let target = ProgramPointRef {
            region: CodeRegionRef::Statement(match &join_continuation {
                _ if rejoins_cases => arms[0].execution.core.frontier.next_statement_index,
                Some(join) => join.next_statement_index,
                None => continuation_index,
            }),
            kind: ProgramPointKind::Entry,
        };
        let interface_resource_specs = assertions
            .iter()
            .filter_map(|assertion| match assertion {
                ProofAssertion::Fact(_) => None,
                ProofAssertion::Resource(resource) => {
                    Some(crate::surface::verification::resource_clause_to_resource_spec(resource))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (name, expected, arm) in [("then", true, &arms[0]), ("else", false, &arms[1])] {
            if !rejoins_cases && !arm.execution.core.frontier.is_at_region_boundary() {
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
        // A mark freezes only the expressions inside `at(...)`. Mixed facts
        // still read the current arm/successor and need the same checked
        // interface lowering as unmarked facts. Resolve frozen expressions
        // from snapshots shared by both arms, never an arm-private mark.
        let interface_specs = assertions
            .iter()
            .filter_map(|assertion| match assertion {
                ProofAssertion::Fact(fact) => Some(lower_branch_interface_fact(
                    fact,
                    context.parsed_function,
                    &interface_reference_state,
                    &parent_execution.core.state,
                    &target,
                    &common_snapshots,
                    context.arguments,
                    context.spec_definitions,
                )),
                ProofAssertion::Resource(_) => None,
            })
            .collect::<Result<Vec<_>, _>>()?;
        let joined_loan_evidence = join_arm_loan_evidence(
            parent_execution,
            [arms[0].execution, arms[1].execution],
            "interface execution join",
        )?;

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
        let sibling_join_states: [&CState; 2] =
            [&arms[0].execution.core.state, &arms[1].execution.core.state];
        // Both arms abstract from the higher of their two counters: their
        // abstractions are compared for equality below, so one shared lower
        // bound is what makes them agree, and taking the maximum is what
        // keeps the join off an identity either arm has already spent.
        let join_next_kernel_variable = arms[0]
            .execution
            .core
            .kernel_variable_mark()
            .max(arms[1].execution.core.kernel_variable_mark());

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
                &written_assertions,
                &mut execution,
                context,
                &mut facts,
                &stable_join_locals,
                Some(&sibling_join_states),
                join_next_kernel_variable,
                true)
            .map_err(|error| add_proof_branch_path(error, &execution.presentation.branch_path))?;
            Ok((execution, facts))
        };
        let (mut then_abstract, then_interface_facts) = abstract_arm(&arms[0])?;
        let (else_abstract, else_interface_facts) = abstract_arm(&arms[1])?;

        let then_interface_vec = then_interface_facts.to_vec();
        let else_interface_vec = else_interface_facts.to_vec();
        if then_interface_vec != else_interface_vec
            || !then_abstract.core.state.eq_with_memories_from(
                &else_abstract.core.state,
                parent_execution.core.state.memory(),
            )
        {
            // Say which part of the two abstractions disagrees: the arms
            // must agree on everything the interface does not abstract.
            let (then_state, else_state) = (&then_abstract.core.state, &else_abstract.core.state);
            let mut differing = Vec::new();
            if then_interface_vec != else_interface_vec {
                differing.push("the facts the interface exports");
            }
            if then_state.locals() != else_state.locals() {
                differing.push("the local variables");
            }
            let memory_parts = then_state.memory().differing_parts(else_state.memory());
            let memory_difference = format!("the memory ({})", memory_parts.join(", "));
            if then_state.memory() != else_state.memory() {
                differing.push(memory_difference.as_str());
            }
            if then_state.resources() != else_state.resources() {
                differing.push("the interface resources");
            }
            if differing.is_empty() {
                differing.push("state outside locals, memory, and resources");
            }
            return Err(self.step_error(format!(
                "`branch ensuring` arms produced different abstract successor states: they differ in {}",
                differing.join(", ")
            )));
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

        // The facts the joined proof holds: the interface's, and what both
        // arms established anyway. They are settled before the resources
        // are composed, because the kernel's check of the join normalizes
        // the successor's resources under these facts, and the same
        // resources normalized under fewer facts can be written differently.
        let mut facts = parent_facts.clone();
        let mut added_facts = Vec::new();
        let else_introduced: std::collections::BTreeSet<&Proposition> =
            arms[1].introduced_facts.iter().collect();
        let retained_facts = then_interface_vec
            .iter()
            .chain(arms[0].introduced_facts.iter().filter(|fact| {
                else_introduced.contains(fact)
                    && arms[0].facts.contains(fact)
                    && arms[1].facts.contains(fact)
            }))
            .collect::<Vec<_>>();
        for fact in &retained_facts {
            if !facts.contains_top_level(fact) {
                facts = facts.with_kernel_checked_fact((*fact).clone());
                added_facts.push((*fact).clone());
            }
        }

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
            .filter(|fact| fact.is_own() || !resources.satisfies_fact(fact, facts.assumptions()))
            .cloned()
            .collect::<Vec<_>>();
        resources = resources
            .try_compose_into_valid_context_delaying_normalization(
                additions.iter().cloned(),
                facts.assumptions(),
            )
            .map_err(|error| {
                self.step_error(format!(
                    "invalid automatic common `branch ensuring` resource interface: {error:?}"
                ))
            })?
            .normalized_around_facts(&additions, facts.assumptions());
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
            true,
        )?;
        execution.core.state = abstract_state.clone().into();
        execution.core.loan_evidence = joined_loan_evidence;
        execution.presentation.recorded_snapshots = common_snapshots;
        execution
            .presentation
            .recorded_snapshots
            .insert(target, abstract_state.clone());
        if !rejoins_cases {
            execution.presentation.recorded_snapshots.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Statement(statement_index),
                    kind: ProgramPointKind::Exit,
                },
                abstract_state.clone(),
            );
        }
        execution.core.frontier.execution_start_state = Some(execution_start_state);
        match join_continuation {
            _ if rejoins_cases => {
                execution.core.frontier = arms[0].execution.core.frontier.clone();
            }
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
        // The joined path is still on the cases the proof took before this
        // split. Its own two cases are the ones that end here.
        execution.presentation.case_assumptions =
            parent_execution.presentation.case_assumptions.clone();
        execution.core.next_opaque_call = then_abstract
            .core
            .next_opaque_call
            .max(else_abstract.core.next_opaque_call);
        // The fresh-variable counter is not carried across from the arms here.
        // This join invents identities, so the kernel recomputes the
        // abstraction below and installs the mark that abstraction reached
        // (`record_interface_branch_join`). A counter the surface chose is
        // exactly what was not being checked.
        migrate_arm_metadata(&mut execution, &arms, false);
        execution.presentation.branch_path.clear();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        if !rejoins_cases {
            record_statement_program_snapshot_state(
                &mut execution.presentation.recorded_snapshots,
                context.function_block,
                statement_index,
                ProgramPointKind::Exit,
                abstract_state,
            );
        }
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

        for fact in retained_facts {
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
        }

        let joined_state = (*execution.core.state).clone();
        let arm_effect_facts: [&ExecutionFacts; 2] = [
            &arms[0].introduced_effect_facts,
            &arms[1].introduced_effect_facts,
        ];
        let joined_effect = match checked_condition_split {
            Some(checked_condition_split) => {
                let [Some(then_theorem), Some(else_theorem)] =
                    [arms[0].condition_theorem, arms[1].condition_theorem]
                else {
                    return Err(self
                        .step_error("checked interface join lost one of its condition theorems"));
                };
                execution.core.record_interface_branch_join(
                    checked_condition_split,
                    parent_facts,
                    [then_theorem, else_theorem],
                    [arms[0].facts, arms[1].facts],
                    &parent_execution.core,
                    [&arms[0].execution.core, &arms[1].execution.core],
                    context.function,
                    context.arguments,
                    &stable_join_locals,
                    &interface_specs,
                    &interface_resource_specs,
                    arm_effect_facts,
                    &joined_state,
                    &facts,
                    Some(&interface_reference_state),
                )
            }
            None => execution.core.record_interface_proof_case_join(
                &parent_execution.core,
                parent_facts,
                [
                    (&arms[0].execution.core, arms[0].facts),
                    (&arms[1].execution.core, arms[1].facts),
                ],
                context.function,
                context.arguments,
                &stable_join_locals,
                &interface_specs,
                &interface_resource_specs,
                arm_effect_facts,
                &joined_state,
                &facts,
                Some(&interface_reference_state),
            ),
        }
        .map_err(|message| {
            // The kernel proves each interface fact in each arm from facts
            // that are already there, the fact's side conditions included.
            // The arm's own check above does not ask for those, so a fact
            // an arm proved can still be refused here. Say which fact, in
            // which arm, and what that arm does not hold.
            let missing = (message
                == "an interface fact is not established by both concrete arms")
                .then(crate::kernel::proof::take_unestablished_interface_goal)
                .flatten()
                .map(|missing| {
                    let fact = assertions
                        .iter()
                        .filter_map(|assertion| match assertion {
                            ProofAssertion::Fact(fact) => Some(fact),
                            ProofAssertion::Resource(_) => None,
                        })
                        .nth(missing.fact)
                        .map_or_else(String::new, |fact| {
                            format!(
                                " `{}`",
                                crate::surface::diagnostics::describe_click_proposition(fact)
                            )
                        });
                    let arm = match (rejoins_cases, missing.arm) {
                        (true, 0) => "first",
                        (true, _) => "second",
                        (false, 0) => "then",
                        (false, _) => "else",
                    };
                    let goal = crate::surface::diagnostics::describe_required_pure_fact(
                        &missing.goal,
                        context.parsed_function.parameters(),
                        context.arguments,
                    );
                    if missing.side_condition {
                        format!(
                            ": the {arm} arm holds the interface fact{fact} but not what its terms need to denote a value, `{goal}`. Prove that in each arm as well, for example `have defined(j + 1) by {{ ... }}` for a fact that mentions `j + 1`"
                        )
                    } else {
                        format!(": the {arm} arm does not hold the interface fact{fact}")
                    }
                })
                .unwrap_or_default();
            self.step_error(format!(
                "kernel rejected the checked `ensuring` interface: {message}{missing}"
            ))
        })?;
        append_execution_effect_facts(&mut execution.core.effect_facts, &joined_effect);

        #[cfg(test)]
        CHECKED_EXECUTION_INTERFACE_JOINS.with(|count| count.set(count.get() + 1));

        // An interface that states nothing is the join a bare split makes,
        // and is written as one.
        let written_ensuring = (!written_assertions.is_empty()).then_some(written_assertions);
        let [then_view, else_view] = arms;
        let step = match proof_case_condition {
            Some(condition) => ProofStep::If {
                condition,
                ensuring: written_ensuring.clone(),
                then_proof: Box::new(then_view.certificate),
                else_proof: Box::new(else_view.certificate),
            },
            None => ProofStep::Branch {
                ensuring: written_ensuring.clone(),
                then_proof: Box::new(then_view.certificate),
                else_proof: Box::new(else_view.certificate),
            },
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
            let view = self.sibling_execution_arm_view(record, name, arm_index, id, steps)?;
            let mut parts = self.merge_decided_interface_execution_path(
                &record.parent_unfolds,
                &record.parent_execution,
                record.continuation_index,
                take_then,
                assertions,
                &view,
            )?;
            self.install_parent_frontier_after_decided(&mut parts.execution, record)?;
            return self.resume_parent_after_sibling_join(record, [id, id], parts);
        }
        let (ids, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_interface_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.continuation_index,
            &record.continuation_remaining,
            record.execution_start_state.clone(),
            match &record.checked_split {
                CheckedExecutionSplit::Branch(split) => Some(split.clone()),
                CheckedExecutionSplit::CallOutcomes(_) => {
                    return Err(
                        self.step_error("`branch ensuring` cannot apply to a call-outcome split")
                    );
                }
            },
            None,
            assertions,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, parts)
    }

    /// Rejoins the two arms of a proof-level execution `if` through an
    /// explicit interface: the arms end at one program point in different
    /// states, and the proof continues once from the abstraction of both
    /// that keeps what the interface names.
    pub(in crate::surface::proof) fn join_focused_execution_if_interface(
        &self,
        record: &ExecutionProofCaseSplit<'a>,
        assertions: Vec<ProofAssertion>,
    ) -> Result<Self, ClickError> {
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, record.arm_branches)?;
        let then_view = self.sibling_execution_arm_view_from_bases(
            "then",
            record.split,
            record.arm_branches[0],
            then_steps,
            &record.base_facts[0],
            &record.common_facts,
            &record.base_executions[0],
            None,
        )?;
        let else_view = self.sibling_execution_arm_view_from_bases(
            "else",
            record.split,
            record.arm_branches[1],
            else_steps,
            &record.base_facts[1],
            &record.common_facts,
            &record.base_executions[1],
            None,
        )?;
        let statement_index = record.parent_execution.core.frontier.next_statement_index;
        let parts = self.merge_interface_execution_join(
            &record.common_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            statement_index,
            statement_index,
            &None,
            record.execution_start_state.clone(),
            None,
            Some(record.surface_condition.clone()),
            assertions,
            [then_view, else_view],
        )?;
        self.resume_parent_after_sibling_join_from_marker(
            &record.marker,
            record.split,
            record.arm_branches,
            parts,
        )
    }

    /// Carries only checked C-branch anchor spellings across a structural
    /// join, when `carry_condition_spellings` is set. A terminal join does
    /// not set it: carrying them there re-recorded every enclosing arm's
    /// condition at each nested join, quadratic work in a function's early
    /// returns, for a frontier that has no successor to read them.
    /// The persistent fact set is owned by `Proof`; it retains exact
    /// historical premises and extraction spellings without publishing
    /// unrelated arm-local predicate or resource provenance.
    pub(super) fn merge_branch_surface_facts(
        &self,
        execution: &mut ExecutionProofState,
        parent: &ExecutionProofState,
        arms: [&ExecutionProofState; 2],
        carry_condition_spellings: bool,
    ) -> Result<(), ClickError> {
        self.merge_branch_generated_load_bindings(execution, parent, arms)?;
        self.merge_branch_generated_load_source_events(execution, parent, arms)?;
        // A chosen existential projection is usable only when both sibling
        // paths retained the same checked source record.  Otherwise it is
        // branch-local presentation and must not leak through the join.
        execution.presentation.chosen_projection = (arms[0].presentation.chosen_projection
            == arms[1].presentation.chosen_projection)
            .then(|| arms[0].presentation.chosen_projection.clone())
            .flatten();
        if !carry_condition_spellings {
            return Ok(());
        }
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

    /// Propagates only producer observations appended by each arm after the
    /// split root. The presentation map is persistent, while the event
    /// sequence supplies an identity-checked, output-sized arm delta. A
    /// conflicting exact observation is reduced to the existing variable
    /// tombstone by `record_generated_load_bindings`.
    fn merge_branch_generated_load_bindings(
        &self,
        execution: &mut ExecutionProofState,
        parent: &ExecutionProofState,
        arms: [&ExecutionProofState; 2],
    ) -> Result<(), ClickError> {
        for (name, arm) in [("then", arms[0]), ("else", arms[1])] {
            let introduced = arm
                .presentation
                .generated_load_binding_events
                .suffix_since(&parent.presentation.generated_load_binding_events)
                .ok_or_else(|| {
                    self.step_error(format!(
                        "{name} execution load bindings do not descend from the split root"
                    ))
                })?;
            execution
                .presentation
                .record_generated_load_bindings(&introduced);
        }
        Ok(())
    }

    /// Propagates source identities appended by each arm after the split
    /// root. The persistent event sequence keeps this merge output-sized and
    /// rejects a non-descending arm rather than scanning ambient facts.
    fn merge_branch_generated_load_source_events(
        &self,
        execution: &mut ExecutionProofState,
        parent: &ExecutionProofState,
        arms: [&ExecutionProofState; 2],
    ) -> Result<(), ClickError> {
        for (name, arm) in [("then", arms[0]), ("else", arms[1])] {
            let introduced = arm
                .presentation
                .generated_load_source_events
                .suffix_since(&parent.presentation.generated_load_source_events)
                .ok_or_else(|| {
                    self.step_error(format!(
                        "{name} execution load source events do not descend from the split root"
                    ))
                })?;
            execution
                .presentation
                .record_generated_load_source_events(&introduced);
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
        call_outcomes: bool,
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
        let has_terminal_cursor = arms.iter().any(|arm| {
            arm.execution.presentation.post_execution_tactics.len()
                > parent_execution.presentation.post_execution_tactics.len()
        });
        let terminal_route = if !call_outcomes && has_terminal_cursor {
            Some(new_terminal_execution_route()?)
        } else {
            None
        };
        let (surface_condition, empty_source_arms) = if call_outcomes {
            (
                ClickProposition::Comparison {
                    left: ContractExpression::CFragment(CExpression::Value(
                        crate::kernel::api::int32(0),
                    )),
                    operator: ComparisonOperator::Equal,
                    right: ContractExpression::CFragment(CExpression::Value(
                        crate::kernel::api::int32(0),
                    )),
                },
                [false, false],
            )
        } else if let Some(condition) = proof_case_condition {
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
            if !call_outcomes {
                self.validate_execution_join_arm_deltas(
                    "terminal join",
                    name,
                    expected,
                    arm,
                    parent_execution,
                )?;
            }
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
            terminal_certificate(&arms[0].certificate, empty_source_arms[0])?
        };
        let else_proof = if proof_case_split {
            arms[1].certificate.clone()
        } else {
            terminal_certificate(&arms[1].certificate, empty_source_arms[1])?
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
        let completed_arms = [&arms[0], &arms[1]].map(|arm| {
            arm.execution
                .core
                .frontier
                .execution()
                .expect("validated terminal arm")
        });
        let can_share_publication = !call_outcomes
            && terminal_route.is_none()
            && arms.iter().zip(completed_arms).all(|(arm, completed)| {
                arm.execution.core.frontier_loop_rules.is_empty()
                    && arm.execution.presentation.loop_return_proofs.is_empty()
                    && completed.path_count() == arm.execution.core.execution_evidence.len()
                    && arm.introduced_facts.iter().all(|fact| {
                        completed.common_facts_contain(&ExecutionPureFact::new(fact.clone()))
                    })
                    && (!arm.execution.presentation.outcome_provenance.is_empty()
                        || completed.path_count() == 1)
            });
        #[cfg(test)]
        TERMINAL_PUBLICATION_VISITS.with(|counts| {
            let (shared, read) = counts.get();
            counts.set((
                shared + usize::from(can_share_publication),
                read + if can_share_publication {
                    0
                } else {
                    completed_arms
                        .iter()
                        .map(|paths| paths.path_count())
                        .sum::<usize>()
                },
            ));
        });
        let (outcomes, execution_evidence, outcome_provenance) = if can_share_publication {
            let outcomes = crate::kernel::concat_retained_function_candidates(
                execution_start_state.clone(),
                completed_arms,
                parent_execution.core.publication_case_prefix(),
            );
            let mut evidence = arms[0].execution.core.execution_evidence.clone();
            evidence.append_shared(&arms[1].execution.core.execution_evidence);
            let arm_provenance = |arm: &CheckedExecutionJoinArm<'_>| {
                if arm.execution.presentation.outcome_provenance.is_empty() {
                    vec![arm.execution.provenance_for_outcome(0)].into()
                } else {
                    arm.execution.presentation.outcome_provenance.clone()
                }
            };
            let mut provenance: crate::kernel::proof::PersistentVector<OutcomeProvenance> =
                arm_provenance(&arms[0]);
            provenance.append_shared(&arm_provenance(&arms[1]));
            (outcomes, evidence, provenance)
        } else {
            let mut paths = Vec::new();
            let mut retained_path_keys: BTreeMap<
                _,
                Vec<(crate::kernel::CheckedLoanCallEvidenceSequence, usize)>,
            > = BTreeMap::new();
            let mut execution_evidence = Vec::new();
            let mut outcome_provenance: Vec<OutcomeProvenance> = Vec::new();
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
                // A call the arm stepped together with its `return` labels the
                // arm's own paths; it is the innermost edge on each of them.
                let arm_call_edges = arm
                    .execution
                    .presentation
                    .call_outcome_edges
                    .as_ref()
                    .filter(|edges| edges.len() == completed.paths().len());
                let route_decision = terminal_route.map(|_| {
                    Arc::new(ExecutionBranchDecision {
                        fingerprint: std::sync::OnceLock::new(),
                        condition: surface_condition.clone(),
                        value: arm_index == 0,
                    })
                });
                for (arm_path_index, path) in completed.paths().iter().enumerate() {
                    let mut provenance = arm.execution.provenance_for_outcome(arm_path_index);
                    if provenance
                        .checked_leaf_facts
                        .as_deref()
                        .is_some_and(|(candidate, _)| !candidate.shares_record_with(path))
                    {
                        provenance.checked_leaf_facts = None;
                    }

                    if provenance.call_routes.is_empty()
                        && let Some(edges) = arm_call_edges
                    {
                        provenance.call_routes.push(edges[arm_path_index]);
                    }
                    if call_outcomes {
                        // An `outcomes` nested in this arm was joined first, so
                        // its edge follows this one.
                        provenance.call_routes.insert(0, arm_index == 0);
                    }
                    let mut path_facts = path.execution_facts();
                    // A returned path of a summarized loop carries what the arm
                    // had established when its loop was summarized, not what the
                    // arm went on to establish on the continuing path.
                    let introduced = match arm
                    .execution
                    .core
                    .pending_loop_return_pure_facts(arm_path_index)
                {
                    Some(returned_facts) => {
                        returned_facts.introduced_since(parent_facts).ok_or_else(|| {
                            self.step_error(
                                "a loop's returned path does not descend from the branch root's facts",
                            )
                        })?
                    }
                    None => arm.introduced_facts.clone(),
                };
                    // The arm's checked introduction delta is true on every
                    // descendant leaf. Preserve its checked context through
                    // publication; summarized loop returns keep their own base.
                    if provenance.loop_return.is_some() {
                        provenance.checked_leaf_facts = None;
                    } else if let Some(cache) = &mut provenance.checked_leaf_facts {
                        let (_, facts) = Arc::make_mut(cache);
                        for proposition in &introduced {
                            *facts = facts.with_kernel_checked_fact(proposition.clone());
                        }
                    }
                    let mut additional_facts = crate::kernel::ExecutionFacts::new();
                    for proposition in &introduced {
                        let fact = ExecutionPureFact::new(proposition.clone());
                        if !path_facts.contains(&fact) {
                            additional_facts.push(fact.clone());
                            path_facts.push(fact);
                        }
                    }
                    let path_key = (
                        path.outcome(),
                        path_facts.clone(),
                        path.obligations(),
                        provenance.call_routes.clone(),
                    );
                    let path_loan_evidence = path.loan_evidence().clone();
                    let retained_index = retained_path_keys.get(&path_key).and_then(|entries| {
                        entries
                            .iter()
                            .find(|(evidence, index)| {
                                evidence == &path_loan_evidence
                                    && match (
                                        &provenance.loop_return,
                                        &outcome_provenance[*index].loop_return,
                                    ) {
                                        (None, None) => true,
                                        (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                                        _ => false,
                                    }
                            })
                            .map(|(_, index)| *index)
                    });
                    if let Some(retained_index) = retained_index {
                        if !outcome_provenance[retained_index]
                            .merge_generated_load_source_events_since(
                                &provenance,
                                &parent_execution.presentation.generated_load_source_events,
                            )
                        {
                            return Err(self.step_error(
                            "terminal outcome load source events do not descend from the branch root",
                        ));
                        }
                    } else {
                        retained_path_keys
                            .entry(path_key)
                            .or_default()
                            .push((path_loan_evidence.clone(), paths.len()));
                        let published =
                            crate::kernel::c_function_execution_candidate_with_additional_facts(
                                path,
                                &additional_facts,
                            );
                        if let Some(cache) = &mut provenance.checked_leaf_facts {
                            let (candidate, _) = Arc::make_mut(cache);
                            // Reclassification preserves the checked facts;
                            // this join admitted the new arm suffix above.
                            *candidate = published.clone();
                        }
                        paths.push(published);
                        execution_evidence
                            .push(arm.execution.core.execution_evidence[arm_path_index].clone());
                        // Proof cases retain their decision when the checked arm
                        // opens, so this path already shares the complete ordered
                        // case history. A join must not rebuild its nested suffix.
                        if let Some(route) = terminal_route {
                            provenance.branch_decisions.record_route(
                                route,
                                Arc::clone(
                                    route_decision
                                        .as_ref()
                                        .expect("terminal route owns its decision"),
                                ),
                            );
                        }
                        outcome_provenance.push(provenance);
                    }
                }
            }

            let outcomes = crate::kernel::c_function_execution_candidates_from_retained_paths(
                execution_start_state.clone(),
                context.function.clone(),
                context.arguments.to_vec(),
                paths,
            );
            (
                outcomes,
                execution_evidence.into(),
                outcome_provenance.into(),
            )
        };
        let mut execution = parent_execution.clone();
        execution.core.has_empty_execution_branch_leaf |= arms
            .iter()
            .any(|arm| arm.execution.core.has_empty_execution_branch_leaf);
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [arms[0].execution, arms[1].execution],
            // Both arms ended at function exit: nothing runs after this
            // join to cite an arm's condition, and each terminal path keeps
            // its own spellings in its outcome provenance.
            false,
        )?;
        execution.core.state = execution_start_state.clone().into();
        execution.presentation.recorded_snapshots = common_snapshots;
        execution.core.frontier.continuations.clear();
        execution.core.frontier.execution_start_state = Some(execution_start_state);
        execution.core.frontier.position = FrontierPosition::FunctionExit {
            execution: outcomes,
        };
        execution.core.execution_evidence = execution_evidence;
        // Each arm's completed paths, the returned loop paths it retained
        // among them, are in the joined set above.
        execution.core.clear_pending_loop_returns();
        execution.core.loan_evidence = crate::kernel::empty_checked_loan_evidence_sequence();
        execution.core.evidence_completed = true;
        execution.core.evidence_state = None;
        execution.core.evidence_source = None;
        execution.presentation.branch_decisions =
            parent_execution.presentation.branch_decisions.clone();
        execution.presentation.outcome_provenance = outcome_provenance;
        if call_outcomes {
            execution.presentation.call_outcome_edges = execution
                .presentation
                .outcome_provenance
                .iter()
                .map(|path| path.call_routes.first().copied())
                .collect();
        }
        execution.core.has_structured_branch_history = true;
        execution.core.next_opaque_call = arms[0]
            .execution
            .core
            .next_opaque_call
            .max(arms[1].execution.core.next_opaque_call);
        // A structural join invents no identity: it keeps the arms' own
        // states, so the successor only has to stay clear of what either arm
        // spent. The checked setter is what makes that a forward move rather
        // than a surface-chosen counter.
        advance_joined_kernel_variable_mark(&mut execution, &arms)
            .map_err(|message| self.step_error(message))?;
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
        migrate_arm_metadata(&mut execution, &arms, true);
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
                    capture.branch_skeleton = Arc::new(if call_outcomes {
                        vec![ProofTactic::CallOutcomes(ProofCallOutcomes {
                            returned_tactics: capture.branch_skeleton.as_ref().clone(),
                            threw_tactics: Vec::new(),
                        })]
                    } else {
                        vec![ProofTactic::If(ProofIf {
                            condition: surface_condition.clone(),
                            ensuring: None,
                            then_tactics: capture.branch_skeleton.as_ref().clone(),
                            else_tactics: Vec::new(),
                        })]
                    });
                    Some(capture)
                }
                (None, Some(capture)) if parent_capture.is_none() => {
                    let mut capture = capture.clone();
                    capture.branch_skeleton = Arc::new(if call_outcomes {
                        vec![ProofTactic::CallOutcomes(ProofCallOutcomes {
                            returned_tactics: Vec::new(),
                            threw_tactics: capture.branch_skeleton.as_ref().clone(),
                        })]
                    } else {
                        vec![ProofTactic::If(ProofIf {
                            condition: surface_condition.clone(),
                            ensuring: None,
                            then_tactics: Vec::new(),
                            else_tactics: capture.branch_skeleton.as_ref().clone(),
                        })]
                    });
                    Some(capture)
                }
                (None, None) => None,
                _ => {
                    return Err(self.step_error(
                        "terminal execution arms retained different selected-tactic cursors",
                    ));
                }
            };

        let parent_batch = &parent_execution
            .presentation
            .expansion
            .batch_deferred_captures;
        let mut batch = parent_batch.clone();
        for (arm_index, arm_expansion) in [then_expansion, else_expansion].into_iter().enumerate() {
            for (index, arm_capture) in &arm_expansion.batch_deferred_captures {
                if let Some(parent) = parent_batch.get(index) {
                    if parent != arm_capture {
                        return Err(
                            self.step_error("terminal arm changed an inherited batch cursor")
                        );
                    }
                    continue;
                }
                if let Some(existing) = batch.get(index) {
                    if existing.source_index != arm_capture.source_index {
                        return Err(self
                            .step_error("terminal arms disagree about a selected source cursor"));
                    }
                    let mut combined = existing.clone();
                    let mut skeleton = combined.branch_skeleton.as_ref().clone();
                    match skeleton.as_mut_slice() {
                        [ProofTactic::If(branch)] if !call_outcomes && arm_index == 1 => {
                            branch.else_tactics = arm_capture.branch_skeleton.as_ref().clone();
                        }
                        [ProofTactic::CallOutcomes(branch)] if call_outcomes && arm_index == 1 => {
                            branch.threw_tactics = arm_capture.branch_skeleton.as_ref().clone();
                        }
                        _ => {
                            return Err(self.step_error(
                                "selected batch cursor lost its terminal branch owner",
                            ));
                        }
                    }
                    combined.branch_skeleton = Arc::new(skeleton);
                    batch.insert(*index, combined);
                    continue;
                }
                let mut captured = arm_capture.clone();
                let (first, second) = if arm_index == 0 {
                    (captured.branch_skeleton.as_ref().clone(), Vec::new())
                } else {
                    (Vec::new(), captured.branch_skeleton.as_ref().clone())
                };
                captured.branch_skeleton = Arc::new(if call_outcomes {
                    vec![ProofTactic::CallOutcomes(ProofCallOutcomes {
                        returned_tactics: first,
                        threw_tactics: second,
                    })]
                } else {
                    vec![ProofTactic::If(ProofIf {
                        condition: surface_condition.clone(),
                        ensuring: None,
                        then_tactics: first,
                        else_tactics: second,
                    })]
                });
                batch.insert(*index, captured);
            }
        }
        execution.presentation.expansion.batch_deferred_captures = batch;
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
                if call_outcomes {
                    PostExecutionTactic::CallOutcomes {
                        returned_tactics: then_post_execution,
                        threw_tactics: else_post_execution,
                    }
                } else {
                    PostExecutionTactic::If {
                        condition: surface_condition.clone(),
                        execution_route: terminal_route,
                        then_tactics: then_post_execution,
                        else_tactics: else_post_execution,
                    }
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
                facts = facts.with_kernel_checked_fact(fact.clone());
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
        for name in &arms[0].introduced_unfolds {
            if !arms[1].introduced_unfolds.contains(name) {
                continue;
            }
            unfolded_predicates.insert(name.clone());
        }
        let step = if call_outcomes {
            ProofStep::CallOutcomes {
                returned_proof: Box::new(then_proof),
                threw_proof: Box::new(else_proof),
            }
        } else {
            ProofStep::If {
                condition: surface_condition,
                ensuring: None,
                then_proof: Box::new(then_proof),
                else_proof: Box::new(else_proof),
            }
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
        checked_condition_split: CheckedBranchSplit,
        require_empty: bool,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
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
        let joined_loan_evidence = join_arm_loan_evidence(
            parent_execution,
            [arms[0].execution, arms[1].execution],
            "checked execution join",
        )?;
        let [Some(then_theorem), Some(else_theorem)] =
            [arms[0].condition_theorem, arms[1].condition_theorem]
        else {
            return Err(self.step_error("checked C branch join lost one of its condition theorems"));
        };
        let joined_effect = execution
            .core
            .record_exhaustive_branch_join(
                checked_condition_split,
                parent_facts,
                [then_theorem, else_theorem],
                [arms[0].facts, arms[1].facts],
                &parent_execution.core,
                [&arms[0].execution.core, &arms[1].execution.core],
                context.function,
                context.arguments,
                [
                    &arms[0].introduced_effect_facts,
                    &arms[1].introduced_effect_facts,
                ],
            )
            .map_err(|message| {
                self.step_error(format!("checked C branch join rejected: {message}"))
            })?;
        execution.core.has_empty_execution_branch_leaf |= arms
            .iter()
            .any(|arm| arm.execution.core.has_empty_execution_branch_leaf);
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [arms[0].execution, arms[1].execution],
            true,
        )?;
        execution.core.state = (**then_state).clone().into();
        execution.core.loan_evidence = joined_loan_evidence;
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
        // As above: a structural join keeps an arm's state and invents
        // nothing, so the successor continues from the higher arm counter
        // through the kernel's checked forward-only setter.
        advance_joined_kernel_variable_mark(&mut execution, &arms)
            .map_err(|message| self.step_error(message))?;
        append_execution_effect_facts(&mut execution.core.effect_facts, &joined_effect);
        migrate_arm_metadata(&mut execution, &arms, true);
        // The joined C arms discharge only their own split. Execution was
        // cloned from the parent, so retain its enclosing proof cases and
        // branch path for certificate reconstruction and diagnostics.
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
                facts = facts.with_kernel_checked_fact(fact.clone());
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
        for name in &arms[0].introduced_unfolds {
            if !arms[1].introduced_unfolds.contains(name) {
                continue;
            }
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
        let (ids, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_checked_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.continuation_index,
            record.continuation_remaining.clone(),
            record.execution_start_state.clone(),
            match &record.checked_split {
                CheckedExecutionSplit::Branch(split) => split.clone(),
                CheckedExecutionSplit::CallOutcomes(_) => {
                    return Err(self.step_error("checked C branch join lost its branch witness"));
                }
            },
            require_empty,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, parts)
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
        let (ids, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_terminal_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.execution_start_state.clone(),
            None,
            false,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, parts)
    }

    /// Joins the returned and caught-throw descendants of one live call.
    /// The call has already been executed in each sibling, so the resulting
    /// certificate retains one leading `step()` per arm.
    pub(in crate::surface::proof) fn join_focused_call_outcomes_terminal(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        let [Some(returned_id), Some(threw_id)] = record.arm_branches else {
            return Err(self.step_error("call outcomes require returned and thrown arms"));
        };
        let [returned_steps, threw_steps] =
            self.partition_steps_since(&record.marker, record.split, [returned_id, threw_id])?;
        self.validate_checked_execution_split(record)?;
        let returned_view = self.sibling_execution_arm_view_from_bases(
            "returned",
            record.split,
            returned_id,
            returned_steps,
            record.base_facts[0].as_ref().expect("returned base facts"),
            &record.parent_facts,
            record.base_executions[0]
                .as_ref()
                .expect("returned base execution"),
            record.condition_theorems[0].as_ref(),
        )?;
        let threw_view = self.sibling_execution_arm_view_from_bases(
            "threw",
            record.split,
            threw_id,
            threw_steps,
            record.base_facts[1].as_ref().expect("threw base facts"),
            &record.parent_facts,
            record.base_executions[1]
                .as_ref()
                .expect("threw base execution"),
            record.condition_theorems[1].as_ref(),
        )?;
        let parts = self.merge_terminal_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.execution_start_state.clone(),
            None,
            true,
            [returned_view, threw_view],
        )?;
        self.resume_parent_after_sibling_join(record, [returned_id, threw_id], parts)
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
        let then_view = self.sibling_execution_arm_view_from_bases(
            "then",
            record.split,
            record.arm_branches[0],
            then_steps,
            &record.base_facts[0],
            &record.common_facts,
            &record.base_executions[0],
            None,
        )?;
        let else_view = self.sibling_execution_arm_view_from_bases(
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
            false,
            [then_view, else_view],
        )?;
        self.resume_parent_after_sibling_join_from_marker(
            &record.marker,
            record.split,
            record.arm_branches,
            parts,
        )
    }

    /// Rejoins the two arms of a proof-level execution `if` so the proof
    /// continues once, from one state, with the facts both arms established.
    ///
    /// `None` when the arms cannot be rejoined here: one of them reached
    /// function exit, they ended at different program points or in different
    /// states, or one proved a loop. The caller then keeps the cases separate.
    pub(in crate::surface::proof) fn try_join_focused_execution_if(
        &self,
        record: &ExecutionProofCaseSplit<'a>,
    ) -> Result<Option<Self>, ClickError> {
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, record.arm_branches)?;
        let then_view = self.sibling_execution_arm_view_from_bases(
            "then",
            record.split,
            record.arm_branches[0],
            then_steps,
            &record.base_facts[0],
            &record.common_facts,
            &record.base_executions[0],
            None,
        )?;
        let else_view = self.sibling_execution_arm_view_from_bases(
            "else",
            record.split,
            record.arm_branches[1],
            else_steps,
            &record.base_facts[1],
            &record.common_facts,
            &record.base_executions[1],
            None,
        )?;
        let Some(parts) = self.merge_case_execution_join(
            &record.common_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.surface_condition.clone(),
            [then_view, else_view],
        )?
        else {
            return Ok(None);
        };
        self.resume_parent_after_sibling_join_from_marker(
            &record.marker,
            record.split,
            record.arm_branches,
            parts,
        )
        .map(Some)
    }

    /// The merge law for a logical two-arm join. The kernel checks the arms
    /// against the partition they entered, that they end at one program
    /// point in one state, and decides which facts survive. Arms that ran C
    /// ran the same statements from the same state, so the frontier, the
    /// state, and the effect facts are either arm's.
    fn merge_case_execution_join(
        &self,
        parent_facts: &ProofFacts,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        surface_condition: ClickProposition,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<Option<CheckedExecutionJoinParts>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("an execution `if` retained a non-execution context")
        };
        if arms.iter().any(|arm| {
            arm.execution.core.frontier.is_at_function_exit()
                || !arm.introduced_derivations.is_empty()
                || !arm.introduced_loop_clauses.is_empty()
                || !arm.introduced_loop_rules.is_empty()
                || arm
                    .execution
                    .presentation
                    .planned_statement_transitions
                    .len()
                    != parent_execution
                        .presentation
                        .planned_statement_transitions
                        .len()
        }) {
            return Ok(None);
        }
        if !arms[0]
            .execution
            .core
            .frontier
            .at_same_program_point(&arms[1].execution.core.frontier)
            || *arms[0].execution.core.state != *arms[1].execution.core.state
            || arms[0].introduced_effect_facts != arms[1].introduced_effect_facts
        {
            return Ok(None);
        }
        let mut execution = parent_execution.clone();
        // What every arm established holds after the join. The kernel checks
        // exactly that of the facts it is handed.
        let mut facts = parent_facts.clone();
        let mut common_added_facts = Vec::new();
        for fact in &arms[0].introduced_facts {
            if !arms[1].facts.contains(fact) || facts.contains(fact) {
                continue;
            }
            facts = facts.with_kernel_checked_fact(fact.clone());
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
        let Ok(changed_execution) = execution.core.record_proof_case_join(
            &parent_execution.core,
            &[
                (&arms[0].execution.core, arms[0].facts),
                (&arms[1].execution.core, arms[1].facts),
            ],
            context.function,
            context.arguments,
            &facts,
        ) else {
            return Ok(None);
        };
        if changed_execution {
            // The arms ran the same statements, so the points they recorded
            // on the way are common to both; a point only one arm named is
            // not carried.
            let Some(snapshots) = arms[0]
                .execution
                .presentation
                .recorded_snapshots
                .common_descendant(
                    &arms[1].execution.presentation.recorded_snapshots,
                    &parent_execution.presentation.recorded_snapshots,
                )
            else {
                return Ok(None);
            };
            let Ok(loan_evidence) = join_arm_loan_evidence(
                parent_execution,
                [arms[0].execution, arms[1].execution],
                "proof `if` join",
            ) else {
                return Ok(None);
            };
            execution.presentation.recorded_snapshots = snapshots;
            execution.core.loan_evidence = loan_evidence;
            execution.core.state = arms[0].execution.core.state.clone();
            execution.core.frontier = arms[0].execution.core.frontier.clone();
            execution.core.has_empty_execution_branch_leaf |= arms
                .iter()
                .any(|arm| arm.execution.core.has_empty_execution_branch_leaf);
            execution.core.has_structured_branch_history |= arms
                .iter()
                .any(|arm| arm.execution.core.has_structured_branch_history);
            append_execution_effect_facts(
                &mut execution.core.effect_facts,
                &arms[0].introduced_effect_facts,
            );
            execution.presentation.resource_unfolded =
                arms[0].execution.presentation.resource_unfolded
                    && arms[1].execution.presentation.resource_unfolded;
        }
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [arms[0].execution, arms[1].execution],
            false,
        )?;
        execution.core.next_opaque_call = arms[0]
            .execution
            .core
            .next_opaque_call
            .max(arms[1].execution.core.next_opaque_call);
        advance_joined_kernel_variable_mark(&mut execution, &arms)
            .map_err(|message| self.step_error(message))?;
        migrate_arm_metadata(&mut execution, &arms, true);

        let mut unfolded_predicates = parent_unfolds.clone();
        for name in &arms[0].introduced_unfolds {
            if arms[1].introduced_unfolds.contains(name) {
                unfolded_predicates.insert(name.clone());
            }
        }
        let [then_arm, else_arm] = arms;
        Ok(Some(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts,
            unfolded_predicates,
            step: ProofStep::If {
                condition: surface_condition,
                ensuring: None,
                then_proof: Box::new(then_arm.certificate),
                else_proof: Box::new(else_arm.certificate),
            },
        }))
    }

    /// Reduces the two sibling arms of an in-`Proof` execution split to the
    /// shared per-arm join view: both recorded goals must be open execution
    /// frontiers, the steps since the split marker partition by recorded
    /// attribution into per-arm body certificates, and each arm's
    /// introduction deltas are recovered by suffix walks against the
    /// recorded split-time bases.
    pub(super) fn sibling_execution_arm_views<'v>(
        &'v self,
        record: &'v ExecutionSplit<'a>,
    ) -> Result<([BranchId; 2], [CheckedExecutionJoinArm<'v>; 2]), ClickError> {
        let [Some(then_id), Some(else_id)] = record.arm_branches else {
            return Err(self.step_error(
                "an execution `branch` with one feasible arm is a decided path, not a join",
            ));
        };
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, [then_id, else_id])?;
        let then_view = self.sibling_execution_arm_view(record, "then", 0, then_id, then_steps)?;
        let else_view = self.sibling_execution_arm_view(record, "else", 1, else_id, else_steps)?;
        Ok(([then_id, else_id], [then_view, else_view]))
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
    ) -> Result<CheckedExecutionJoinArm<'v>, ClickError> {
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
        let arm_theorems = [
            record.condition_theorems[0].as_ref(),
            record.condition_theorems[1].as_ref(),
        ];
        let arm_facts = [record.base_facts[0].as_ref(), record.base_facts[1].as_ref()];
        match &record.checked_split {
            CheckedExecutionSplit::Branch(split) => {
                let (_, current_state, statement, _) =
                    next_top_level_statement_from_frontier_position(
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
                if !split.validates_exhaustive_join(
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
            }
            CheckedExecutionSplit::CallOutcomes(split) => {
                if !split.validates(
                    &record.split_state,
                    &record.split_statement,
                    &record.parent_facts,
                    arm_theorems[0].ok_or_else(|| {
                        self.step_error("call-outcome split lost its returned theorem")
                    })?,
                    arm_theorems[1].ok_or_else(|| {
                        self.step_error("call-outcome split lost its thrown theorem")
                    })?,
                ) {
                    return Err(self.step_error(
                        "checked call-outcome split no longer matches its call frontier",
                    ));
                }
            }
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
    ) -> Result<CheckedExecutionJoinArm<'v>, ClickError> {
        let Some(branch) = self.state().open_branches().get(id) else {
            return Err(self.step_error(format!(
                "cannot join `branch`: the {name} arm is not an open execution frontier"
            )));
        };
        if !matches!(branch.obligation, Obligation::Frontier(_)) {
            return Err(self.step_error(format!(
                "cannot join `branch`: the {name} arm is not an open execution frontier"
            )));
        }
        let execution = branch.state.execution.as_deref().ok_or_else(|| {
            self.step_error(format!("{name} branch arm lost its execution state"))
        })?;
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
            return Err(self.step_error(format!(
                "cannot join `branch`: the {name} arm facts do not descend from split {:?}",
                split
            )));
        }
        let introduced_facts = branch
            .state
            .facts
            .introduced_since(delta_facts)
            .ok_or_else(|| self.step_error(format!(
                "cannot join `branch`: the {name} arm fact delta does not descend from split {:?}", split
            )))?;
        let introduced_effect_facts = execution
            .core
            .effect_facts
            .suffix_since(&delta_execution.core.effect_facts)
            .ok_or_else(|| self.step_error(format!(
                "cannot join `branch`: the {name} arm effect facts do not descend from split {:?}", split
            )))?
            .to_vec();
        let introduced_derivations = execution
            .core
            .function_entry_derivations
            .introduced_since(&delta_execution.core.function_entry_derivations)
            .ok_or_else(|| self.step_error(format!(
                "cannot join `branch`: the {name} arm derivations do not descend from split {:?}", split
            )))?;
        let introduced_unfolds = execution
            .core
            .unfolded_predicates
            .suffix_since(&delta_execution.core.unfolded_predicates)
            .ok_or_else(|| {
                self.step_error(format!(
                    "cannot join `branch`: the {name} arm unfolds do not descend from split {:?}",
                    split
                ))
            })?
            .to_vec();
        let introduced_loop_clauses = execution
            .presentation
            .frontier_loop_clauses
            .suffix_since(&delta_execution.presentation.frontier_loop_clauses)
            .ok_or_else(|| self.step_error(format!(
                "cannot join `branch`: the {name} arm loop clauses do not descend from split {:?}", split
            )))?
            .to_vec();
        let introduced_loop_rules = execution
            .core
            .frontier_loop_rules
            .suffix_since(&delta_execution.core.frontier_loop_rules)
            .ok_or_else(|| self.step_error(format!(
                "cannot join `branch`: the {name} arm loop rules do not descend from split {:?}", split
            )))?
            .to_vec();
        Ok(CheckedExecutionJoinArm {
            certificate: ProofCertificate::from_steps(steps)?,
            facts: &branch.state.facts,
            execution,
            condition_theorem,
            introduced_facts,
            introduced_effect_facts: introduced_effect_facts.into(),
            introduced_derivations,
            introduced_unfolds,
            introduced_loop_clauses,
            introduced_loop_rules,
        })
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
        let view = self.sibling_execution_arm_view(record, name, arm_index, id, steps)?;
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
        self.resume_parent_after_sibling_join(record, [id, id], parts)
    }

    /// Consumes both sibling arm goals and resumes the parent obligation
    /// under its original id with the merged continuation context, splicing
    /// the structured join step over the split region so step attribution
    /// stays correct for enclosing splits.
    pub(super) fn resume_parent_after_sibling_join(
        &self,
        record: &ExecutionSplit<'a>,
        ids: [BranchId; 2],
        parts: CheckedExecutionJoinParts,
    ) -> Result<Self, ClickError> {
        self.resume_parent_after_sibling_join_from_marker(&record.marker, record.split, ids, parts)
    }

    pub(super) fn resume_parent_after_sibling_join_from_marker(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        parts: CheckedExecutionJoinParts,
    ) -> Result<Self, ClickError> {
        let parent_goal = marker.node.focused_branch;
        let parent_node = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `branch`: the split marker lost its root")
        })?;
        let trace_added_facts =
            crate::surface::proof_trace::enabled_for(self.claim_label()).then(|| {
                (
                    parts
                        .common_added_facts
                        .iter()
                        .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact))
                        .take(8)
                        .cloned()
                        .collect::<Vec<_>>(),
                    parts
                        .common_added_facts
                        .iter()
                        .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact))
                        .count()
                        .saturating_sub(8),
                )
            });
        let state = self
            .state
            .publish_reserved_checked_frontier_join(
                split,
                ids,
                parent_goal,
                parts.facts,
                parts.unfolded_predicates,
                parts.execution,
                parts.common_added_facts.clone(),
                parts.common_added_facts,
            )
            .map_err(|_| self.step_error("cannot join `branch`: invalid branch lineage"))?;
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: Some(parent_node.clone()),
                step: Some(Arc::new(parts.step)),
                focused_branch: parent_goal,
                depth: parent_node.depth + 1,
                split_branches: Vec::new(),
            }),
        };
        if crate::surface::proof_trace::enabled_for(self.claim_label()) {
            let (trace_added_facts, more_facts) =
                trace_added_facts.expect("trace facts retained when enabled");
            let facts = trace_added_facts
                .into_iter()
                .map(|fact| successor.checked_trace_fact(fact))
                .collect();
            crate::surface::proof_trace::record_join(
                Arc::as_ptr(&successor.node) as usize,
                crate::surface::proof_trace::TraceJoin {
                    marker: Arc::as_ptr(&marker.node) as usize,
                    arms: [
                        trace_arm_lineage(&self.node, &marker.node, ids[0]),
                        trace_arm_lineage(&self.node, &marker.node, ids[1]),
                    ],
                    facts,
                    more_facts,
                    continuation_arm: None,
                    _retained: Box::new(self.node.clone()),
                },
            );
        }
        Ok(successor)
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
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_focused_execute_to_exit(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_focused_execute_to_exit_within(
            Vec::new(),
            &mut BTreeSet::new(),
            &mut 0,
            None,
            None,
        )
    }

    /// Charges one statement step of a smart `execute()` against its fixed
    /// step budget. A loop the context decides is walked one iteration at a
    /// time, so a loop that never exits must stop here, naming the statement
    /// it stands at, rather than run until the work limit.
    pub(in crate::surface::proof) fn charge_execute_step(
        &self,
        steps: &mut usize,
    ) -> Result<(), ClickError> {
        let limit = super::super::cursor_execution::BOUNDED_EXECUTE_STEP_LIMIT;
        if *steps == limit {
            let statement = self
                .current_statement_index()?
                .map_or_else(String::new, |index| format!(" at statement({index})"));
            return Err(self.step_error(format!(
                "`execute` exhausted its {limit}-step budget{statement}"
            )));
        }
        *steps += 1;
        Ok(())
    }

    /// The nested-branch execute-to-exit recursion. `enclosing` is the chain
    /// of bounded-arm split records this execution runs inside, innermost
    /// last: reaching a bounded arm's typed boundary consumes one record to
    /// continue privately into that arm's parent continuation, so a terminal
    /// path escapes exactly as many regions as it is nested inside.
    ///
    /// `steps` counts the statement steps the owning `execute()` has taken,
    /// across every nested arm: [`Self::charge_execute_step`] refuses the
    /// search at its fixed budget. `introduced`, given only at the top level,
    /// collects the facts each advance there adds, for a scope that retains
    /// what its body introduced. `until` stops the run before that source
    /// statement instead of at function exit; such a run follows one path
    /// and refuses where it would have to split.
    pub(in crate::surface::proof) fn try_focused_execute_to_exit_within(
        &self,
        enclosing: Vec<&ExecutionSplit<'a>>,
        retried_requirements: &mut BTreeSet<PropositionIdentityKey>,
        steps: &mut usize,
        mut introduced: Option<&mut Vec<Proposition>>,
        until: Option<usize>,
    ) -> Result<Option<Self>, ClickError> {
        let mut record_added = |proof: &Self| {
            if let Some(introduced) = introduced.as_deref_mut() {
                for fact in proof.added_facts() {
                    if !introduced.contains(fact) {
                        introduced.push(fact.clone());
                    }
                }
            }
        };
        let mut proof = self.clone();
        let mut enclosing = enclosing;
        loop {
            while proof.is_at_region_boundary() {
                let Some(record) = enclosing.pop() else {
                    return Ok(None);
                };
                proof = proof.continue_arm_into_parent_frontier(record)?;
            }
            if let Some(target) = until {
                match proof.current_statement_index()? {
                    Some(current) if current == target => return Ok(Some(proof)),
                    Some(current) if current < target => {}
                    Some(current) => {
                        return Err(proof.step_error(format!(
                            "`execute_until(statement({target}))` target is not reachable from the current execution path; execution moved the frontier to statement({current})"
                        )));
                    }
                    None => {
                        return Err(proof.step_error(format!(
                            "`execute_until(statement({target}))` reached function exit before its target"
                        )));
                    }
                }
            } else if proof.is_at_function_exit() {
                return Ok(Some(proof));
            }
            proof.charge_execute_step(steps)?;
            if let Some(next) =
                proof.try_smart_statement_step(ProofStep::Step, retried_requirements)?
            {
                record_added(&next);
                proof = next;
                retried_requirements.clear();
                continue;
            }
            if let Some(target) = until {
                // `execute_until` runs one path and does not split it: a
                // frontier the bare step cannot take (an undecided C `if`, a
                // maybe-throwing call) is refused with that step's own
                // diagnostic.
                return match proof.apply_step(ProofStep::Step) {
                    Err(error) => Err(error),
                    Ok(_) => Err(proof.step_error(format!(
                        "`execute_until(statement({target}))` could not advance this statement"
                    ))),
                };
            }
            let Some((split, record, call_outcomes)) = (if proof.is_at_call_outcomes_frontier()? {
                proof
                    .split_focused_call_outcomes()?
                    .map(|(split, record)| (split, record, true))
            } else if proof.is_at_execution_branch()? {
                // A condition with path cases needs a case split on their
                // facts before a C `branch` applies: split the proof on the
                // condition that tells them apart, and each case meets the
                // same `if` again with one path per arm.
                let (split, record) = match proof.split_focused_execution_branch() {
                    Ok(split) => split,
                    Err(error) if error.is_path_case_split() => {
                        let Some(condition) = error.path_case_condition() else {
                            return Ok(None);
                        };
                        let cases = proof.try_focused_execute_cases_to_exit(
                            condition.clone(),
                            &enclosing,
                            retried_requirements,
                            steps,
                        )?;
                        if let Some(cases) = &cases {
                            record_added(cases);
                        }
                        return Ok(cases);
                    }
                    Err(error) => return Err(error),
                };
                Some((split, record, false))
            } else {
                None
            }) else {
                // A statement whose successors are path cases (a load's
                // may-alias cases, a symbolic `switch`) splits the proof on
                // the condition that tells them apart; each case runs to exit
                // under its side of the condition.
                return match proof.apply_step(ProofStep::Step) {
                    Err(error) if error.is_path_case_split() => {
                        let Some(condition) = error.path_case_condition() else {
                            return Ok(None);
                        };
                        let cases = proof.try_focused_execute_cases_to_exit(
                            condition.clone(),
                            &enclosing,
                            retried_requirements,
                            steps,
                        )?;
                        if let Some(cases) = &cases {
                            record_added(cases);
                        }
                        Ok(cases)
                    }
                    // The statement cannot run here in the whole proof
                    // context; its refusal is the answer.
                    Err(error) => Err(error),
                    Ok(_) => Ok(None),
                };
            };
            let mut advanced = split;
            for take_then in [true, false] {
                if record.arm_id(take_then).is_none() {
                    continue;
                }
                let mut arm_enclosing = enclosing.clone();
                arm_enclosing.push(&record);
                let Some(next) = advanced
                    .focus_split_arm(&record, take_then)?
                    .try_focused_execute_to_exit_within(
                        arm_enclosing,
                        retried_requirements,
                        steps,
                        None,
                        None,
                    )?
                else {
                    return Ok(None);
                };
                advanced = next;
            }
            proof = if call_outcomes {
                advanced.join_focused_call_outcomes_terminal(&record)?
            } else if record.sole_feasible_arm().is_some() {
                advanced.finish_focused_execution_decided(&record)?
            } else {
                advanced.join_focused_execution_terminal(&record)?
            };
            record_added(&proof);
            retried_requirements.clear();
        }
    }

    /// Splits the proof on `condition` and runs each case to function exit,
    /// then joins the two terminal cases. `enclosing` is the chain of bounded
    /// arms the split runs inside; each case escapes all of them.
    fn try_focused_execute_cases_to_exit(
        &self,
        condition: ClickProposition,
        enclosing: &[&ExecutionSplit<'a>],
        retried_requirements: &mut BTreeSet<PropositionIdentityKey>,
        steps: &mut usize,
    ) -> Result<Option<Self>, ClickError> {
        // This selector will also surround deferred path-dependent closers
        // after return. Read it where the case was checked, rather than from
        // a compiler temporary or a parameter's later value at function exit.
        let mut proof = self.clone();
        let execution = proof.execution().expect("execute cases retain a frontier");
        let ProofContext::Execution(context) = proof.context.as_ref() else {
            unreachable!("execute cases retain an execution context")
        };
        let point = ProgramPointRef {
            region: CodeRegionRef::Statement(execution.core.frontier.next_statement_index),
            kind: ProgramPointKind::Entry,
        };
        let frontier = execution.core.frontier.clone();
        let state = execution.core.state.clone();
        let (recorded, result) = proof.clone().edit_execution_presentation(|presentation| {
            record_current_statement_entry(
                &frontier,
                &mut presentation.recorded_snapshots,
                &state,
                context.function_block,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "execute cases",
            )
        })?;
        result?;
        proof = recorded;
        let anchored =
            super::super::cursor_execution::surface_frozen_at_snapshot(&condition, &point)?;
        let original = proof.lower_surface_proposition(&condition, "execute case condition")?;
        let frozen =
            proof.lower_surface_proposition(&anchored, "anchored execute case condition")?;
        // A synthesized source selector can lower to a condition the case
        // already knows without selecting the kernel statement's successors.
        // Splitting that condition again makes no progress and can exhaust
        // the native stack before the execution work budget is reached.
        let opposite = proof.lower_surface_proposition(
            &ClickProposition::Not(Box::new(condition.clone())),
            "execute case negation",
        )?;
        if proof.facts().contains(&original) || proof.facts().contains(&opposite) {
            return Err(proof.step_error(
                "`execute` cannot advance after selecting this path condition; use explicit cases and `step()` to expose the remaining obligation",
            ));
        }
        if original != frozen {
            return Err(
                proof.step_error("anchored execute case condition changed its checked meaning")
            );
        }
        let (mut advanced, record) = proof.split_focused_execution_if(anchored)?;
        for take_then in [true, false] {
            let Some(next) = advanced
                .focus_execution_if_arm(&record, take_then)?
                .try_focused_execute_to_exit_within(
                    enclosing.to_vec(),
                    retried_requirements,
                    steps,
                    None,
                    None,
                )?
            else {
                return Ok(None);
            };
            advanced = next;
        }
        retried_requirements.clear();
        advanced
            .join_focused_execution_if_terminal(&record)
            .map(Some)
    }

    /// Validates and applies one already-expanded logical execution arm.
    ///
    /// Terminal and decided branches render one structural branch-entry
    /// `step()` (two for an empty C arm). The split already performed
    /// those transitions, so this checks the exact Surface operations against
    /// the C branch and applies only the remaining body steps to the focused branch
    /// sibling. No certificate is constructed or interpreted.
    pub(in crate::surface::proof) fn checked_expanded_execution_arm_entry_steps(
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

    /// Applies one expanded arm of the split `arm_enclosing` ends with,
    /// inside the bounded arms before it.
    fn apply_focused_expanded_execution_arm(
        &self,
        arm_enclosing: &[&ExecutionSplit<'a>],
        take_then: bool,
        surface_condition: &ClickProposition,
        steps: &[ProofStep],
    ) -> Result<Self, ClickError> {
        let record = arm_enclosing
            .last()
            .expect("an expanded arm runs inside its own split");
        let Some((proof, entry_steps)) =
            self.focus_expanded_execution_arm_entry(record, take_then, surface_condition, steps)?
        else {
            return Err(self.step_error("cannot advance an infeasible expanded execution arm"));
        };
        proof.apply_execution_steps_within(arm_enclosing, &steps[entry_steps..], true)
    }

    /// Applies planner (or, with `expanded`, already-expanded) execution
    /// steps inside the bounded C `if` arms `enclosing` names, innermost
    /// last. A path runs to function exit, so an execution-advancing step
    /// that finds the frontier at an arm's typed boundary continues
    /// privately into that arm's parent continuation through its split
    /// record, and again through the next record while the parent's own
    /// region is exhausted: a path escapes exactly as many arms as it is
    /// nested inside, as [`Self::try_focused_execute_to_exit_within`] does.
    /// Logical steps run at a boundary unchanged. A case split inside an arm
    /// (a load or condition with path cases) runs each case under the same
    /// chain, so a case that finishes the arm continues past it instead of
    /// failing as running off the arm.
    fn apply_execution_steps_within(
        &self,
        enclosing: &[&ExecutionSplit<'a>],
        steps: &[ProofStep],
        expanded: bool,
    ) -> Result<Self, ClickError> {
        let mut proof = self.clone();
        let mut enclosing = enclosing.to_vec();
        for step in steps {
            if matches!(step, ProofStep::Step | ProofStep::If { .. }) {
                while proof.is_at_region_boundary() {
                    let Some(record) = enclosing.pop() else {
                        break;
                    };
                    proof = proof.continue_arm_into_parent_frontier(record)?;
                }
            }
            proof = match step {
                ProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                    ..
                } => proof.apply_execution_if_within(
                    &enclosing,
                    condition,
                    then_proof.steps(),
                    else_proof.steps(),
                    expanded,
                )?,
                _ => proof.apply_step(step.clone())?,
            };
        }
        Ok(proof)
    }

    /// Applies one planner (or, with `expanded`, already-expanded) `if`
    /// inside the bounded arms `enclosing` names (see
    /// [`Self::apply_execution_steps_within`]).
    fn apply_execution_if_within(
        &self,
        enclosing: &[&ExecutionSplit<'a>],
        condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
        expanded: bool,
    ) -> Result<Self, ClickError> {
        // A planner `if` at a C `if` whose condition has one path per truth
        // value enters an actual C `if` arm, including its branch-entry
        // statement steps. Every other planner `if` is a proof-level case
        // split: a native C `switch` is one checked statement whose symbolic
        // dispatch needs each generated arm to supply its selected case fact;
        // a statement or condition with path cases (a load that may read an
        // earlier store's cell, a short-circuit condition) needs each case's
        // facts before its one successor exists. The planner splits such an
        // operation one condition at a time and re-runs it on each side, so
        // the same question decides every nested planner `if` here as well.
        // An expanded `if` is the C branch exactly when it spells the C
        // condition, as at the top level; otherwise it is a case split.
        let case_split = if expanded {
            !self.frontier_is_execution_branch(condition)?
        } else {
            self.execution_frontier_is_switch()? || self.execution_frontier_has_path_cases()?
        };
        if case_split {
            return self.clone().apply_execution_if_with(
                condition.clone(),
                |proof| proof.apply_execution_steps_within(enclosing, then_steps, expanded),
                |proof| proof.apply_execution_steps_within(enclosing, else_steps, expanded),
            );
        }
        self.apply_execution_branch_within(enclosing, condition, then_steps, else_steps, expanded)
    }

    /// Splits the C `if` at the frontier and applies each arm's steps inside
    /// `enclosing` and the new split, then joins.
    fn apply_execution_branch_within(
        &self,
        enclosing: &[&ExecutionSplit<'a>],
        condition: &ClickProposition,
        then_steps: &[ProofStep],
        else_steps: &[ProofStep],
        expanded: bool,
    ) -> Result<Self, ClickError> {
        let (split, record) = self.split_focused_execution_branch()?;
        let mut arm_enclosing: Vec<&ExecutionSplit<'a>> = enclosing.to_vec();
        arm_enclosing.push(&record);
        let mut advanced = split;
        for (take_then, steps) in [(true, then_steps), (false, else_steps)] {
            if record.arm_id(take_then).is_none() {
                if expanded && !steps.is_empty() {
                    return Err(self.step_error(format!(
                        "expanded execution {} arm is nonempty, but the checked C branch is infeasible",
                        if take_then { "then" } else { "else" },
                    )));
                }
                continue;
            }
            if expanded {
                // Proof operations may follow the last C step. Entry validation
                // and the checked join enforce the arm's execution boundary.
                advanced = advanced.apply_focused_expanded_execution_arm(
                    &arm_enclosing,
                    take_then,
                    condition,
                    steps,
                )?;
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
                .apply_execution_steps_within(&arm_enclosing, &steps[entry_steps..], false)?;
        }
        advanced.join_focused_execution_split(&record, false, None)
    }

    /// Whether the next C operation at the focused frontier has path cases a
    /// C `branch` cannot represent: a plain statement (whose cases a planner
    /// `if` can only select by their facts), or a C `if` whose condition
    /// reaches one truth value along several checked paths.
    fn execution_frontier_has_path_cases(&self) -> Result<bool, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(false);
        };
        let Some(execution) = self.execution() else {
            return Ok(false);
        };
        if matches!(
            execution.core.frontier.position,
            FrontierPosition::FunctionExit { .. } | FrontierPosition::RegionBoundary
        ) {
            return Ok(false);
        }
        let Ok((_, current_state, statement, remaining)) =
            next_top_level_statement_from_frontier_position(
                execution.view(context),
                &execution.core.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "planned case split",
            )
        else {
            return Ok(false);
        };
        let CStatement::If { .. } = &statement else {
            return Ok(true);
        };
        let (_, transitions) = certified_proof_condition_split(
            &current_state,
            self.facts(),
            &statement,
            remaining.as_ref(),
            &format!(
                "`{}` tactic {}: planned case split",
                context.claim_label, context.tactic_index
            ),
            Some(context.parsed_function),
        )?;
        Ok([true, false].into_iter().any(|value| {
            transitions
                .iter()
                .filter(|transition| transition.is_true == value)
                .count()
                > 1
        }))
    }

    fn execution_frontier_is_switch(&self) -> Result<bool, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(false);
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let statement = match &execution.core.frontier.position {
            FrontierPosition::FunctionEntry => context.function.body().clone(),
            FrontierPosition::StatementEntry { remaining } => remaining.as_ref().clone(),
            FrontierPosition::FunctionExit { .. } | FrontierPosition::RegionBoundary => {
                return Ok(false);
            }
        };
        Ok(
            super::super::cursor_execution::split_next_source_operation(&statement)
                .is_ok_and(|(statement, _)| matches!(statement, CStatement::Switch { .. })),
        )
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
        self.apply_execution_branch_within(&[], condition, then_steps, else_steps, true)
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
        // The continuation's first statement is entered here, as a step
        // onto it would enter it, so its entry point is recorded the same
        // way. An expanded branch that follows names that point in its
        // condition.
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
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
            )
            .map_err(|error| self.execution_update_error("continue branch arm", error))?;
        Ok(Self {
            site: self.site.clone(),
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
            if !crate::kernel::proof::checked_branch_fact_is_available(self.facts(), &fact) {
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

    /// How one arm of this split left a loop body, if it did.
    ///
    /// A `branch` joins its arms at the `if`'s continuation. An arm that
    /// left the loop through `break`, or reached the back edge through
    /// `continue`, never arrives there, so there is nothing to join and the
    /// caller refuses instead of merging two paths that go to different
    /// places.
    pub(in crate::surface::proof) fn arm_loop_control(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
    ) -> LoopControlExit {
        record
            .arm_id(take_then)
            .and_then(|id| {
                self.state()
                    .open_branches()
                    .get(id)
                    .and_then(|branch| branch.state.execution.as_deref())
                    .map(|execution| execution.core.frontier.loop_control)
            })
            .unwrap_or_default()
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
        } else if self.split_arms_end_apart(record)? {
            // Arms that end in different states join keeping what both
            // agree on: the join an interface makes, with nothing stated.
            // `ensuring { ... }` is what a proof adds to say more.
            self.join_focused_execution_interface(record, Vec::new())
        } else {
            self.join_focused_execution_branch(record)
        }
    }

    /// Whether both arms of a C branch reached its continuation in
    /// different states, where a join that can abstract them is available.
    /// Costs the arms' own steps, which the join then partitions again.
    pub(in crate::surface::proof) fn split_arms_end_apart(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<bool, ClickError> {
        if record.sole_feasible_arm().is_some()
            || self.split_arms_at_function_exit(record)
            || !record.supports_interface_branch()
        {
            return Ok(false);
        }
        let (_, arms) = self.sibling_execution_arm_views(record)?;
        Ok(*arms[0].execution.core.state != *arms[1].execution.core.state)
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
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
                split_branches: arm_ids.iter().flatten().copied().collect(),
            }),
        };
        successor.record_trace_c_branch(&successor.node, arm_ids, &path_facts);
        let record = ExecutionSplit {
            marker: successor.checkpoint(),
            split,
            arm_branches: arm_ids,
            condition_theorems,
            checked_split: CheckedExecutionSplit::Branch(prepared.checked_condition_split),
            base_facts,
            base_executions,
            path_facts,
            parent_facts,
            parent_unfolds: unfolds,
            parent_execution: parent_execution.clone(),
            statement_index: prepared.statement_index,
            continuation_index: prepared.continuation_index,
            continuation_remaining: prepared.continuation_remaining,
            execution_start_state: prepared.execution_start_state,
            split_state: (*parent_execution.core.state).clone(),
            split_statement: CStatement::Skip,
        };
        Ok((successor, record))
    }

    /// Opens a live caught-throw call into returned and handler-entry proof
    /// siblings. The call is evaluated once. Each descendant records one of
    /// those already-certified transitions; no descendant re-evaluates the
    /// call.
    pub(in crate::surface::proof) fn split_focused_call_outcomes(
        &self,
    ) -> Result<Option<(Self, ExecutionSplit<'a>)>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(parent_execution) = self.execution().cloned() else {
            return Ok(None);
        };
        let available_facts = PureFactList::from(self.facts().to_vec());
        let Some(prepared) = crate::surface::proof::cursor_execution::prepare_call_outcome_split(
            &parent_execution,
            context,
            &available_facts,
            "outcomes",
        )?
        else {
            return Ok(None);
        };
        let root_facts = self.facts().clone();
        let normal_index = prepared
            .transitions
            .iter()
            .position(|transition| matches!(transition.outcome, CStatementOutcome::Normal(_)))
            .expect("prepared call split has a normal transition");
        let throw_index = prepared
            .transitions
            .iter()
            .position(|transition| matches!(transition.outcome, CStatementOutcome::Throw { .. }))
            .expect("prepared call split has a throw transition");
        let normal = &prepared.transitions[normal_index];
        let thrown = &prepared.transitions[throw_index];
        let mut returned_execution = prepared.execution.clone();
        let mut returned_available_facts = available_facts.clone();
        let mut returned_introduced_facts = Vec::new();
        crate::surface::proof::cursor_execution::apply_prepared_call_outcome_transition(
            &mut returned_execution,
            context,
            &mut returned_available_facts,
            &mut returned_introduced_facts,
            &prepared,
            normal,
        )?;
        let mut threw_execution = prepared.execution.clone();
        let mut threw_available_facts = available_facts.clone();
        let mut threw_introduced_facts = Vec::new();
        crate::surface::proof::cursor_execution::apply_prepared_call_outcome_transition(
            &mut threw_execution,
            context,
            &mut threw_available_facts,
            &mut threw_introduced_facts,
            &prepared,
            thrown,
        )?;
        let facts_descending_from_root = |facts: &[Proposition]| {
            facts.iter().fold(root_facts.clone(), |current, fact| {
                if current.contains(fact) {
                    current
                } else {
                    current.with_kernel_checked_fact(fact.clone())
                }
            })
        };
        let returned_facts = facts_descending_from_root(&returned_available_facts);
        let threw_facts = facts_descending_from_root(&threw_available_facts);
        let returned_execution = Arc::new(returned_execution);
        let threw_execution = Arc::new(threw_execution);
        let arms = [
            Some((returned_facts.clone(), returned_execution.clone())),
            Some((threw_facts.clone(), threw_execution.clone())),
        ];
        let path_facts = [
            Some(normal.path_facts.clone()),
            Some(thrown.path_facts.clone()),
        ];
        let (state, split, arm_ids) = self
            .state
            .publish_checked_partial_frontier_split(arms, path_facts.clone())
            .map_err(|error| self.execution_update_error("`outcomes`", error))?;
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
                split_branches: arm_ids.iter().flatten().copied().collect(),
            }),
        };
        let checked_split = CheckedCallOutcomeSplit::from_certified_transitions(
            prepared.current_state.clone(),
            prepared.statement.clone(),
            &root_facts,
            &normal.theorem,
            &normal.outcome,
            &normal.path_facts,
            &normal.obligations,
            &thrown.theorem,
            &thrown.outcome,
            &thrown.path_facts,
            &thrown.obligations,
        )
        .map_err(|_| {
            self.step_error("`outcomes` could not certify the returned/threw call split")
        })?;
        let record = ExecutionSplit {
            marker: successor.checkpoint(),
            split,
            arm_branches: arm_ids,
            condition_theorems: [Some(normal.theorem.clone()), Some(thrown.theorem.clone())],
            checked_split: CheckedExecutionSplit::CallOutcomes(checked_split),
            base_facts: [Some(returned_facts), Some(threw_facts)],
            base_executions: [Some(returned_execution), Some(threw_execution)],
            path_facts,
            parent_facts: root_facts,
            parent_unfolds: self.focused_branch_unfolds().clone(),
            parent_execution: Arc::new(parent_execution),
            statement_index: prepared.statement_index,
            continuation_index: prepared.statement_index,
            continuation_remaining: None,
            execution_start_state: prepared.execution_start_state,
            split_state: prepared.current_state,
            split_statement: prepared.statement,
        };
        Ok(Some((successor, record)))
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

/// Continues a joined execution from the higher of its arms' fresh-variable
/// counters, through the kernel's forward-only setter.
///
/// Both arms forked from this execution, so neither counter is below the
/// successor's and the move always succeeds; the setter is what says so
/// rather than a comment. A join that invents identities of its own does not
/// use this -- the kernel installs the abstraction's own mark there.
fn advance_joined_kernel_variable_mark(
    execution: &mut ExecutionProofState,
    arms: &[CheckedExecutionJoinArm<'_>; 2],
) -> Result<(), String> {
    let mark = arms[0]
        .execution
        .core
        .kernel_variable_mark()
        .max(arms[1].execution.core.kernel_variable_mark());
    execution
        .core
        .advance_kernel_variable_mark(mark)
        .map_err(|message| format!("branch join: {message}"))
}

/// Applies the shared metadata policy for a two-arm join. Entry
/// prerequisites and derivation theorems are self-contained checked
/// obligations, so either arm may contribute them. An unfold marker is a
/// frontier-local planning hint and becomes common only when both arms
/// introduced it. Presentation clauses are deduplicated by code region;
/// every checked loop rule is retained so a ranked branch cannot mask an
/// unranked sibling's termination obligation.
fn migrate_arm_metadata(
    execution: &mut ExecutionProofState,
    arms: &[CheckedExecutionJoinArm<'_>; 2],
    retain_common_unfolds: bool,
) {
    for arm in arms {
        for theorem in &arm.introduced_derivations {
            execution
                .core
                .function_entry_derivations
                .insert(theorem.clone());
        }
    }
    if retain_common_unfolds {
        for name in &arms[0].introduced_unfolds {
            if arms[1].introduced_unfolds.contains(name)
                && !execution.core.unfolded_predicates.contains(name)
            {
                execution.core.unfolded_predicates.push(name.clone());
            }
        }
    }
    for arm in arms {
        // Clauses describe source presentation and may share a C loop across
        // proof branches. Rules are checked path evidence: retain every rule,
        // including unranked siblings and nested rules with no separate clause.
        for rule in &arm.introduced_loop_rules {
            execution.core.frontier_loop_rules.push(rule.clone());
        }
        for clause in &arm.introduced_loop_clauses {
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
        }
    }
}

#[cfg(test)]
mod progress_tests {
    use super::*;
    fn indexed_fact(index: u32) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(Bitvector32Term::Variable(Variable(0))),
                Box::new(Bitvector32Term::Constant(index)),
            ),
            true,
        )
    }

    #[test]
    fn execute_refuses_to_split_an_already_selected_path_condition() {
        let click_file = crate::surface::parse(
            r#"
            int32 identity(int32 x) {
                ensures result == x;
            } by {
                assumption();
            }
        "#,
        )
        .expect("test contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let parsed_function = syntax::parse_function(
            "int32 identity(int32 x) { int32 copied; copied = x; return copied; }",
        )
        .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(71_000)),
        ))];
        let function_environment = CExecutionEnvironment::new();
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::GreaterEqual,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };

        for size in [8_u32, 32, 128] {
            let root = Proof::for_execution_frontier(
                "execution proof if scaling",
                0,
                ExecutionProofState::at_entry(
                    CState::new(),
                    ExecutionFrontier::default(),
                    RecordedSnapshots::new(),
                    SurfacePropositionMap::default(),
                    PersistentSequence::default(),
                ),
                (0..size).map(indexed_fact).collect::<Vec<_>>(),
                ExecutionProofConstants {
                    source_layout: SourceExecutionLayout::new(parsed_function.body()),
                    ..ExecutionProofConstants::default()
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                SpecDefinitions::new(&predicate_environment, &click_function_environment),
                &theorem_environment,
            )
            .apply_step(ProofStep::Step)
            .expect("the declaration prefix should execute before the proof split");

            let (split, record) = root.split_focused_execution_if(condition.clone()).unwrap();
            for take_then in [true, false] {
                let focused = split.focus_execution_if_arm(&record, take_then).unwrap();
                let mut steps = 0;
                let error = focused
                    .try_focused_execute_cases_to_exit(
                        condition.clone(),
                        &[],
                        &mut BTreeSet::new(),
                        &mut steps,
                    )
                    .err()
                    .expect("a selected condition must not recurse into another identical split");
                assert!(
                    error
                        .message()
                        .contains("cannot advance after selecting this path condition"),
                    "{error:?}"
                );
                assert_eq!(steps, 0, "refusal must precede recursive execution");
            }
            let mut steps = 0;
            assert!(
                root.try_focused_execute_cases_to_exit(
                    condition.clone(),
                    &[],
                    &mut BTreeSet::new(),
                    &mut steps,
                )
                .unwrap()
                .is_some(),
                "an undecided condition must still execute both cases"
            );
        }
    }
}
