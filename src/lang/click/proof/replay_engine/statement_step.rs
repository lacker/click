use super::*;

pub(in crate::lang::click::proof) struct CheckedStatementStep {
    pub(in crate::lang::click::proof) facts: ProofFacts,
    pub(in crate::lang::click::proof) added_facts: Vec<Proposition>,
}

/// Checks one explicit statement transition from exactly the named surface
/// premises and atomically advances the caller-selected execution successor.
///
/// This is the audited semantic operation shared by explicit source replay
/// and the checked proof-object frontier. It performs no premise search: the
/// selected surface premises are lowered, checked, and used as the only facts
/// transported across the statement boundary before ambient facts are
/// restored at their original snapshots.
#[allow(clippy::too_many_arguments)]
pub(in crate::lang::click::proof) fn check_step_using_facts(
    replay: &mut TacticReplayState,
    state: &mut CState,
    requirement_pure_facts: &ProofFacts,
    premises: &[ClickProposition],
    function_block: &FunctionBlock,
    function: &CFunction,
    parsed_function: &syntax::C0Function,
    arguments: &[CExpression],
    function_environment: &CExecutionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CheckedStatementStep, ClickError> {
    let assumptions = requirement_pure_facts.assumptions();
    let tactic_name = "step() using";
    let prerequisite_policy = StatementPrerequisitePolicy::Explicit;
    let loop_step_policy = LoopStepPolicy::EnterBody;
    // Resuming from a completed branch region reaches this
    // statement without recording its entry snapshot; a premise
    // written `at(statement(N).entry, ...)` for the statement this
    // step crosses must still lower.
    record_current_statement_entry(
        replay,
        state,
        function_block,
        function,
        arguments,
        claim_label,
        tactic_index,
        tactic_name,
    )?;
    let pre_state = replay.old_reference_state(state).clone();
    let mut explicit_premises = Vec::new();
    for surface_premise in premises {
        let recorded = replay
            .surface_propositions
            .available_kernel_matching(surface_premise, |kernel| {
                requirement_pure_facts.contains(kernel)
            });
        let recorded_is_constant_truth = recorded.is_some_and(|premise| match premise {
            Proposition::ConditionIs(ConditionTerm::Constant(true), true) => true,
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(left, right)
                | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector32Equal(left, right),
                true,
            ) => matches!(
                (left.as_ref(), right.as_ref()),
                (Bitvector32Term::Constant(_), Bitvector32Term::Constant(_))
            ),
            _ => false,
        });
        let lower_at_current = || {
            lower_point_proposition_with_assumptions(
                surface_premise,
                assumptions,
                parsed_function.parameters(),
                arguments,
                &pre_state,
                state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
        };
        let current_indexed = proposition_contains_at_expression(surface_premise)
            .then(|| lower_at_current().ok())
            .flatten()
            .filter(|current| {
                requirement_pure_facts
                    .replay_available_across_effects(current, &replay.effect_facts)
            });
        let parameter_names = parsed_function
            .parameters()
            .iter()
            .map(syntax::C0Parameter::name)
            .collect::<BTreeSet<_>>();
        let stable_recorded_definedness = matches!(
            surface_premise,
            ClickProposition::Defined { expression }
                if !super::super::surface_certificates::contract_expression_mentions_c_local(
                    expression,
                    &parameter_names,
                )
        );
        // Prefer an explicit program-point lowering when it names
        // an exact available fact. Fall back to the checked cache
        // when a partial expansion has not replayed that point, or
        // when the cache records an equivalent polarity form
        // such as `not (a < b)` versus `a >= b`.
        let premise = if let Some(current) = current_indexed {
            current
        } else if recorded_is_constant_truth {
            match lower_at_current() {
                Ok(current)
                    if !PureFactContext::new().proves(&current)
                        && requirement_pure_facts
                            .replay_available_across_effects(&current, &replay.effect_facts) =>
                {
                    current
                }
                _ => recorded.expect("checked recorded truth").clone(),
            }
        } else if (proposition_contains_at_expression(surface_premise)
            || proposition_contains_old_expression(surface_premise)
            || stable_recorded_definedness)
            && let Some(recorded) = recorded
        {
            recorded.clone()
        } else {
            lower_at_current().map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `{tactic_name}` premise `{}`: {message}",
                    super::super::super::printing::source_click_proposition(surface_premise)
                ))
            })?
        };
        replay
            .surface_propositions
            .record_lowering(surface_premise, &premise)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise: {}",
                    error.message()
                ))
            })?;
        // Anchor the premise at this statement's entry only when its
        // surface form actually denotes the recorded fact here: a premise
        // taken from the recorded cache may have been established at an
        // earlier point, and a cell it reads may have changed since. With
        // terms canonical at creation the recorded fact is
        // snapshot-independent, so a stale anchor would silently bind the
        // old value to this point's surface form.
        let anchored_form_is_current = proposition_contains_at_expression(surface_premise)
            || proposition_contains_old_expression(surface_premise)
            || lower_at_current().is_ok_and(|fresh| {
                fresh == premise
                    || crate::kernel::canonical_condition_fact(&fresh)
                        == crate::kernel::canonical_condition_fact(&premise)
            });
        if anchored_form_is_current {
            let entry_point = ProgramPointRef {
                region: CodeRegionRef::Statement(replay.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            };
            let source_surface = surface_anchored_where_unanchored(surface_premise, &entry_point)?;
            replay
                .surface_propositions
                .record_lowering(&source_surface, &premise)
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not record `{tactic_name}` premise source site: {}",
                        error.message()
                    ))
                })?;
        }
        // Loadability premises additionally transport across
        // snapshot terms and recorded effects: the recorded
        // fact and the premise print identically but embed
        // different memory snapshots.
        let premise_is_available = requirement_pure_facts
                .replay_available_across_effects(&premise, &replay.effect_facts)
                || crate::kernel::loadable_covered_by_fact(assumptions, &premise)
                // A premise written for a sibling execution path
                // can lower to a context-free truth on this path
                // (a shared post-branch step's premise after a
                // constant assignment); it demands no evidence.
                || PureFactContext::new().proves(&premise)
                // A premise whose load atoms carry the abstract
                // spec form ("the current value") cannot be
                // related to live-written facts by history — the
                // pristine memory is not a snapshot. Rewrite
                // those atoms over the current point's memory
                // and decide the live pair by framing across
                // the recorded effects.
                || {
                    let concretized = concretize_pristine_loads(
                        &premise,
                        state.memory(),
                    );
                    concretized != premise
                        && requirement_pure_facts.replay_available_across_effects(
                            &concretized,
                            &replay.effect_facts,
                        )
                }
                // Canonical load variables are kernel-internal names; two
                // recorded equalities chained through one are the same
                // user-level fact, so availability closes over them rather
                // than demanding the certificate write the chain.
                || premise_bridged_by_canonical_names(&premise, requirement_pure_facts);
        if !premise_is_available {
            let all_pure_facts = requirement_pure_facts.to_vec();
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{tactic_name}` requires an exact premise: {}",
                describe_missing_pure_fact(
                    &premise,
                    &all_pure_facts,
                    state.resources().facts(),
                    parsed_function.parameters(),
                    arguments,
                    &replay.effect_facts,
                )
            )));
        }
        if !explicit_premises.contains(&premise) {
            explicit_premises.push(premise);
        }
    }
    for case in &replay.case_assumptions {
        let branch_fact = if let Some(fact) = &case.fact {
            fact.clone()
        } else {
            let proposition = lower_point_proposition_with_assumptions(
                &case.condition,
                assumptions,
                parsed_function.parameters(),
                arguments,
                &pre_state,
                state,
                None,
                &replay.program_point_states,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower enclosing proof-branch condition: {message}"
                ))
            })?;
            if case.value {
                proposition
            } else {
                match proposition {
                    Proposition::ConditionIs(condition, value) => {
                        Proposition::ConditionIs(condition, !value)
                    }
                    Proposition::Not(body) => *body,
                    proposition => Proposition::Not(Box::new(proposition)),
                }
            }
        };
        if requirement_pure_facts
            .replay_available_across_effects(&branch_fact, &replay.effect_facts)
            && !explicit_premises.contains(&branch_fact)
        {
            explicit_premises.push(branch_fact);
        }
    }
    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
    for resource_fact in state
        .resources()
        .observable_facts_assuming_valid(&explicit_assumptions)
    {
        if !explicit_premises.contains(&resource_fact) {
            explicit_premises.push(resource_fact);
        }
    }
    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
    let introduced_facts = execute_step_from_execution_point(
        replay,
        state,
        &mut explicit_premises,
        function_block,
        function,
        parsed_function.parameters(),
        arguments,
        &explicit_assumptions,
        function_environment,
        claim_label,
        tactic_index,
        tactic_name,
        prerequisite_policy,
        // `using` deliberately selects the exact context that may
        // cross this statement boundary. Transport only those
        // listed facts through the certified statement effect;
        // ambient facts are restored below at their original
        // snapshots.
        StatementFactTransportPolicy::Selected,
        loop_step_policy,
        None,
    )?;
    let facts = requirement_pure_facts.with_statement_facts(explicit_premises);
    Ok(CheckedStatementStep {
        facts,
        added_facts: introduced_facts,
    })
}

/// Frame-lean adapter for the shared canonical-name closure. Fact-vector
/// materialization is local work and must not enlarge every statement replay
/// frame; the expansion small-stack regression pins that boundary.
#[inline(never)]
fn premise_bridged_by_canonical_names(premise: &Proposition, facts: &ProofFacts) -> bool {
    super::super::fact_reasoning::premise_bridged_by_canonical_name_chain(premise, &facts.to_vec())
}
