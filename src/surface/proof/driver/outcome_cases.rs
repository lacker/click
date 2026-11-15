//! Drives ordinary proposition obligations before deferred outcome splits.
use super::*;
use crate::surface::proof::driver::{OutcomeSplitFailure, ProofDriver};

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    pub(in crate::surface::proof) fn split_outcome_paths(
        &self,
        split: &DeferredPostExecutionTactic,
    ) -> Result<Proof<'a>, OutcomeSplitFailure> {
        let driver_proof = self.proof;
        driver_proof.require_execution_frontier("post-execution case split")?;
        let ProofContext::Execution(context) = driver_proof.context.as_ref() else {
            return Err(driver_proof
                .step_error("post-execution case split requires an execution proof")
                .into());
        };
        let mut execution = driver_proof.execution().cloned().ok_or_else(|| {
            driver_proof.step_error("post-execution case split lost its execution frontier")
        })?;
        if !execution.core.frontier.is_at_function_exit() {
            return Err(driver_proof
                .step_error("post-execution case split requires function exit")
                .into());
        }
        let checked = execution
            .core
            .frontier
            .execution()
            .cloned()
            .ok_or_else(|| {
                driver_proof.step_error("post-execution case split has no checked execution paths")
            })?;
        let pre_state = execution
            .core
            .frontier
            .execution_start_state(&execution.core.state)
            .clone();
        let mut paths = Vec::with_capacity(checked.paths().len() * 2);
        let mut outcome_provenance = Vec::with_capacity(checked.paths().len() * 2);
        // The retained evidence traces fork with the candidates so they
        // stay zipped for completion; each forked copy records its arm.
        let mut evidence_plan = Vec::with_capacity(checked.paths().len());
        let mut nodes = Vec::new();
        let pending = execution
            .presentation
            .post_execution_tactics
            .suffix_since(&execution.presentation.partitioned_post_execution_tactics)
            .ok_or_else(|| driver_proof.step_error("deferred case proof lost its source prefix"))?;
        let split_root = outcome_case_region(std::slice::from_ref(split), None, &mut nodes)
            .ok_or_else(|| {
                driver_proof.step_error("post-execution case split is not a case split")
            })?;
        let root = outcome_case_region(&pending, Some(split_root), &mut nodes)
            .expect("the new case follows the deferred prefix");
        // Every path partitions its deferred matches with witnesses past
        // those of the paths before it.
        let next_variable = std::cell::Cell::new(driver_proof.state.locals().next_choice_variable);
        let ambient_delta = execution
            .presentation
            .outcome_fact_root
            .as_ref()
            .and_then(|root| driver_proof.facts().introduced_since(root));
        for (path_index, path) in checked.paths().iter().enumerate() {
            check_verification_deadline()?;
            let mut provenance = execution.provenance_for_outcome(path_index);
            let retained = provenance
                .checked_leaf_facts
                .as_deref()
                .filter(|(candidate, _, _)| candidate.shares_record_with(path))
                .filter(|_| {
                    execution
                        .core
                        .pending_loop_return_pure_facts(path_index)
                        .is_none()
                })
                .zip(ambient_delta.as_ref())
                .map(|((_, facts, holds_effects), delta)| {
                    (
                        delta.iter().fold(facts.clone(), |facts, fact| {
                            facts.with_kernel_checked_fact(fact.clone())
                        }),
                        *holds_effects,
                    )
                });
            if retained.is_none() {
                provenance.checked_leaf_facts = None;
            }
            let FunctionOutcome::Return { value, state } = path.outcome() else {
                paths.push(path.clone());
                outcome_provenance.push(provenance);
                evidence_plan.push(OutcomeEvidenceFork::Keep);
                continue;
            };
            // A checked leaf retains its query root. Only new case facts
            // enter the push/pop buffer; legacy paths keep their full input.
            let mut path_facts = if retained.is_some() {
                Vec::new()
            } else {
                path.facts()
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect::<Vec<_>>()
            };
            let base_len = path_facts.len();
            let query = retained.clone().map(|(facts, _)| facts).unwrap_or_else(|| {
                path_facts
                    .iter()
                    .fold(driver_proof.facts().clone(), |facts, fact| {
                        facts.with_kernel_checked_fact(fact.clone())
                    })
            });
            let retained_states = provenance.recorded_states.clone();
            let match_cases = |source: &ProofMatch,
                               query: &ProofFacts,
                               authority: &ProofFacts,
                               bindings: Option<&OutcomeBindings>| {
                let scoped = driver_proof.with_surface_local_scope(
                    bindings.unwrap_or(&driver_proof.state.locals().values),
                );
                let value =
                    scoped.outcome_match_scrutinee(source, state, query, &retained_states)?;
                let cases =
                    scoped.outcome_match_cases(source, &value, authority, next_variable.get())?;
                next_variable.set(cases.next_variable);
                Ok(cases)
            };
            let obligation_failed = std::cell::Cell::new(false);
            let fork = partition_outcome_cases(
                &nodes,
                Some(root),
                driver_proof.facts(),
                &query,
                &mut path_facts,
                provenance,
                &|condition, facts, bindings| {
                    let scoped = driver_proof.with_surface_local_scope(
                        bindings.unwrap_or(&driver_proof.state.locals().values),
                    );
                    let condition =
                        scoped.substitute_fixed_state_locals_in_proposition(condition)?;
                    let condition = &condition;
                    let lowered = if retained.is_some() {
                        let retained_query = facts.iter().fold(query.clone(), |query, fact| {
                            query.with_kernel_checked_fact(fact.clone())
                        });
                        lower_outcome_proposition_with_recorded_states(
                            context.parameter_binding(),
                            &pre_state,
                            state,
                            &value.native(),
                            &retained_query,
                            condition,
                            context.spec_definitions,
                            &retained_states,
                        )
                    } else {
                        lower_outcome_proposition_with_recorded_states(
                            context.parameter_binding(),
                            &pre_state,
                            state,
                            &value.native(),
                            facts,
                            condition,
                            context.spec_definitions,
                            &retained_states,
                        )
                    };
                    lowered.map_err(|message| {
                        driver_proof.step_error(format!(
                            "post-execution case split could not lower its condition: {message}"
                        ))
                    })
                },
                &match_cases,
                &|surface, written, facts, provenance, bindings| {
                    let result = (|| {
                        let native_value = value.native();
                        let fixed = Proof::for_fixed_state(
                            context.claim_label,
                            written.map_or(context.tactic_index, |source| source.tactic_index),
                            FixedStateFacts::Slice(&[]),
                            OpenBranch::frontier,
                            context.parameter_binding(),
                            FixedStateFrame::new(
                                &pre_state,
                                state,
                                Some(&native_value),
                                &provenance.recorded_states,
                            ),
                            frontier_premise_anchor(&execution),
                            &provenance.surface_propositions,
                            context.spec_definitions,
                            context.theorem_environment,
                            &[],
                            &execution.core.effect_facts,
                            context.function_block.requires(),
                            Some(facts.clone()),
                        )
                        .with_surface_local_scope(
                            written
                                .and_then(|source| source.lexical_bindings.as_ref())
                                .or(bindings)
                                .unwrap_or(&driver_proof.state.locals().values),
                        );
                        let kernel =
                            fixed.lower_surface_proposition(surface, "`cases` obligation")?;
                        let proved = if let Some(source) = written {
                            let PostExecutionTactic::Have(have) = &source.tactic else {
                                unreachable!("the obligation retains its source have")
                            };
                            let nested = fixed.driver().open_source_have(have)?;
                            let goal = nested.goal().cloned();
                            let mut failure = None;
                            let closed = crate::surface::proof::checked_drivers::solve_nested_have(
                                nested,
                                have,
                                &mut failure,
                            )?
                            .ok_or_else(|| {
                                crate::surface::proof::checked_drivers::source_have_error(
                                    &fixed,
                                    have,
                                    source.tactic_index,
                                    goal.as_ref(),
                                    failure,
                                    true,
                                )
                            })?;
                            closed.join()?
                        } else {
                            fixed.driver().prove_cases_disjunction(surface)?
                        };
                        Ok((kernel, proved.certificate()))
                    })();
                    if result.is_err() {
                        obligation_failed.set(true);
                    }
                    result
                },
                &mut |facts, mut provenance| {
                    let additional = facts[base_len..]
                        .iter()
                        .cloned()
                        .map(ExecutionPureFact::new)
                        .collect::<ExecutionFacts>();
                    let published =
                        crate::kernel::program_function_execution_candidate_with_additional_facts(
                            path,
                            &additional,
                        );
                    if let Some((retained, holds_effects)) = &retained {
                        let facts = facts[base_len..]
                            .iter()
                            .fold(retained.clone(), |facts, fact| {
                                facts.with_kernel_checked_fact(fact.clone())
                            });
                        provenance.checked_leaf_facts =
                            Some(Arc::new((published.clone(), facts, *holds_effects)));
                    }
                    paths.push(published);
                    outcome_provenance.push(provenance);
                },
            )
            .map_err(|error| {
                if obligation_failed.get() {
                    OutcomeSplitFailure::Obligation(error)
                } else {
                    OutcomeSplitFailure::Partition(error)
                }
            })?;
            evidence_plan.push(fork);
        }
        let candidates = crate::kernel::program_function_execution_candidates_from_retained_paths(
            checked.state().clone(),
            checked.function().clone(),
            checked.arguments().to_vec(),
            paths,
        );
        execution
            .core
            .fork_outcome_evidence(&evidence_plan)
            .map_err(|message| {
                driver_proof.step_error(format!("post-execution case split: {message}"))
            })?;
        execution.core.frontier.position = FrontierPosition::FunctionExit {
            execution: candidates,
        };
        execution.presentation.outcome_provenance = outcome_provenance.into();
        execution.presentation.partitioned_post_execution_tactics =
            execution.presentation.post_execution_tactics.clone();
        let transition = driver_proof.checked_execution_transition(
            driver_proof.facts().clone(),
            false,
            execution,
            Vec::new(),
            Vec::new(),
        );
        let mut state = driver_proof.publish_checked_transition(transition)?;
        if next_variable.get() > state.locals().next_choice_variable {
            let mut locals = state.locals().clone();
            locals.next_choice_variable = next_variable.get();
            state = state.with_locals(locals);
        }
        Ok(Proof {
            site: driver_proof.site.clone(),
            context: driver_proof.context.clone(),
            state,
            node: driver_proof.node.clone(),
        })
    }
}
