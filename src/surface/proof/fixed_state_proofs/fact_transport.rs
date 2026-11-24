use super::*;
use crate::kernel::ExecutionFactSource;
#[cfg(test)]
use crate::kernel::OverflowOperation;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::surface::proof_diagnostics::render;

/// The premises a bare `transport` writes: its source, when that is an
/// available fact and carries the target, or none when the target already
/// follows without it. No other available fact is a candidate: a frame that
/// needs more premises is written as `transport(P, Q) using { ... }`, and the
/// bare form's miss says so. The final `TransportUsing` step checks all the
/// ordinary frame routes.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn plan_explicit_fact_transport(
    surface_source: &ClickProposition,
    source: &Proposition,
    target: &Proposition,
    available_facts: &PureFactStore,
    effect_facts: &(impl ExecutionFactSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Result<Vec<ClickProposition>, ClickError> {
    let available = available_facts.to_vec();
    let mut selected = Vec::new();
    if exact_fact_is_available(source, &available) {
        selected.push((source.clone(), surface_source.clone()));
    }
    let check_premises = |selected: &[(Proposition, ClickProposition)]| {
        let explicit = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let explicit_assumptions = assumptions_from_propositions(&explicit);
        let resource_facts = state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        let selected_assumptions = available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        if crate::kernel::search::ProofSearch::derive_proposition(&(selected_assumptions), source)
            .is_none()
        {
            return false;
        }
        if crate::kernel::search::ProofSearch::derive_proposition(&(selected_assumptions), target)
            .is_some()
        {
            return true;
        }
        let transport_assumptions = effect_facts
            .fact_iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        let chain_facts = available
            .iter()
            .cloned()
            .chain(std::iter::once(source.clone()))
            .collect::<Vec<_>>();
        let chain_assumptions = chain_facts
            .iter()
            .flat_map(|fact| {
                // A separation's bounds travel with it as a conjunction.
                // Frame evidence may use its leaves, but never facts under
                // an implication or a quantifier.
                let mut parts = Vec::new();
                atomic_conjuncts(fact, &mut parts);
                parts
            })
            .filter(|fact| {
                // Separations are frame justification too: crossing a call's
                // havoc edge for a load outside the callee's footprint is
                // decided by exactly these facts, checked in this context.
                matches!(
                    fact,
                    Proposition::ConditionIs(_, _)
                        | Proposition::MemoryMutatesOnly { .. }
                        | Proposition::MemoryEffectSummary { .. }
                        | Proposition::HeapAllocationFreed { .. }
                        | Proposition::ResourceSeparate { .. }
                        | Proposition::ResourceComposition(_)
                )
            })
            .fold(transport_assumptions.clone(), |assumptions, fact| {
                assumptions.assume_proposition(fact.clone())
            });
        if super::super::fact_reasoning::premise_bridged_by_load_variable_chain_with_origins(
            target,
            &chain_facts,
            &chain_assumptions,
        ) {
            return true;
        }
        certified_fact_transport_reaches(
            source,
            target,
            Some(state.memory()),
            &transport_assumptions,
        )
    };

    let checks = |selected: &[(Proposition, ClickProposition)]| {
        crate::instrumentation::measure_operation(
            "surface",
            "fact transport",
            "explicit fact transport: premise check",
            || check_premises(selected),
        )
    };
    // The candidate is the source alone. Search over the other available
    // facts is gone: a premise the frame needs beyond the source is written
    // in the `using` form, which this planner never scans for.
    if !checks(&selected) {
        let _render_timing = crate::instrumentation::OperationTiming::new(
            "surface",
            "fact transport",
            "explicit fact transport: planning refusal",
        );
        let _exact = render::TypedNotationScope::enter();
        let mut labels = render::MemoryStateLabels::with_state(parameter_binding, state);
        let checked_source = render::render_proposition_labeled(source, &mut labels);
        let checked_target = render::render_proposition_labeled(target, &mut labels);
        return Err(ClickError::new(format!(
            "the source alone does not carry the certified fact transport\n  checked source (holds): {checked_source}\n  checked target (wanted): {checked_target}{}",
            labels.trace_legend(),
        )));
    }
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if checks(&reduced) {
            selected = reduced;
        } else {
            index += 1;
        }
    }
    Ok(selected.into_iter().map(|(_, surface)| surface).collect())
}

pub(in crate::surface::proof) struct CheckedFixedStateFactTransport {
    pub(in crate::surface::proof) source: Proposition,
    pub(in crate::surface::proof) target: Proposition,
}

/// Audited semantic operation for one explicit mid-execution
/// `transport(source, target) using { premises }`.
///
/// Both explicit source check and `Proof::apply_step` call this operation.
/// It does not mutate surface bookkeeping or proof lineage; it returns the
/// exact checked source and target for those owners to record atomically.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn check_fixed_state_fact_transport_using_facts(
    surface_source: &ClickProposition,
    surface_target: &ClickProposition,
    surface_premises: &[ClickProposition],
    claim_label: &str,
    tactic_index: usize,
    available: &PureFactStore,
    effect_facts: &(impl ExecutionFactSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    surface_propositions: &SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<CheckedFixedStateFactTransport, ClickError> {
    // One explicit transport can ask the same failed alias/frame question
    // through several proof routes. Share their existing, fully keyed failure
    // memo within this check, just as the smart closure does.
    crate::kernel::with_transport_cell_walk_diagnostics(|| {
        crate::kernel::with_closure_failure_memo(|| {
            let mut checked_target = None;
            let result = check_fixed_state_fact_transport_using_facts_inner(
                surface_source,
                surface_target,
                surface_premises,
                claim_label,
                tactic_index,
                available,
                effect_facts,
                parameter_binding,
                fixed_state,
                surface_propositions,
                spec_definitions,
                &mut checked_target,
            );
            // A check may finish after consuming its allowance. Report the
            // goal it actually lowered, never re-evaluate it after the stop.
            result
                .and_then(|checked| {
                    check_verification_deadline()?;
                    Ok(checked)
                })
                .map_err(|error| {
                    if crate::instrumentation::deadline_exceeded()
                        && let Some(target) = checked_target
                    {
                        error.with_spelled_requirement(
                            target,
                            surface_target.clone(),
                            "checked transport target".into(),
                        )
                    } else {
                        error
                    }
                })
        })
    })
}

#[allow(clippy::too_many_arguments)]
fn check_fixed_state_fact_transport_using_facts_inner(
    surface_source: &ClickProposition,
    surface_target: &ClickProposition,
    surface_premises: &[ClickProposition],
    claim_label: &str,
    tactic_index: usize,
    available: &PureFactStore,
    effect_facts: &(impl ExecutionFactSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    surface_propositions: &SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    checked_target: &mut Option<Proposition>,
) -> Result<CheckedFixedStateFactTransport, ClickError> {
    // Resource compositions keep separation compact. Materialize only a
    // listed separation premise on the local checked state so explicit
    // `transport using` retains its exact-premise contract without publishing
    // every unrelated member pair.
    let mut available = available.clone();
    let mut explicit_premises = Vec::new();
    for surface_premise in surface_premises {
        let premise = if let Some(recorded) = surface_propositions
            .available_kernel_matching(surface_premise, |kernel| available.contains(kernel))
        {
            recorded.clone()
        } else {
            lower_fixed_state_proposition_with_assumptions(
                surface_premise,
                available.assumptions(),
                parameter_binding,
                fixed_state,
                spec_definitions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `transport using` premise: {message}"
                ))
            })?
        };
        available = available.with_selected_resource_separation(&premise);
        // A premise that lowers to a syntactically reflexive equality (two
        // state reads canonicalized to one term) needs no fact: the exact
        // check accepts every proposition that holds without facts
        // (`proposition_holds_without_facts`), and a transport also accepts
        // one that holds that way under binders and guards: the reflexive
        // source a quantified frame transports from.
        // A quantified premise is accepted up to its binder's name, as
        // `apply using` accepts it: a call's postcondition is held with the
        // binder its lowering chose, and the written premise names its own.
        // A premise the context's equality graph proves is available too: a
        // read written through one alias of a cell whose fact was stated
        // through another is the same premise, and lowering does not rename
        // it to match (lowering is fact-stable, `docs/internals/raise-lower-principle.md`).
        if !available.listed_premise_available(&premise, &[], true)
            && !holds_without_facts_under_binders(&premise)
            && !available.assumptions().contains_known(&premise)
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `transport using` requires an exact premise"
            ))
            .with_spelled_requirement(
                premise,
                surface_premise.clone(),
                "`transport using` premise".into(),
            ));
        }
        // Citing a stated range cites both of its halves; see
        // `cite_range_span_guards`.
        crate::surface::proof::theorem_application::cite_range_span_guards(
            &premise,
            &mut explicit_premises,
            |guard| available.exact_available_across_effects(guard, &[]),
        );
        if !explicit_premises.contains(&premise) {
            explicit_premises.push(premise);
        }
    }

    // Lowering memory expressions may use the validated ambient context, but
    // the proof itself remains restricted to explicit premises, resource
    // observations, and certified frame/effect facts.
    let recorded_source = surface_propositions
        .available_kernel_matching(surface_source, |kernel| available.contains(kernel))
        .cloned();
    let ordinary_source = if let Some(recorded) = &recorded_source {
        recorded.clone()
    } else {
        lower_fixed_state_proposition_with_assumptions(
            surface_source,
            available.assumptions(),
            parameter_binding,
            fixed_state,
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower `transport` source: {message}"
            ))
            })?
    };
    let concrete_source_is_true = matches!(
        normalize_proposition(&ordinary_source),
        NormalizedProposition::True
    );
    let explicit_assumptions = assumptions_from_propositions(&explicit_premises);
    // The target form is paired with an already-lowered focused goal, so
    // the validated ambient context may justify only its expression
    // definedness (not the transport conclusion). This includes bounds such
    // as `n >= 1` needed to read one cell from `loadable(p[0..n])`; the
    // restricted assumptions below still exclusively decide whether the
    // explicit source and certified effects reach the lowered target.
    let target_lowering_assumptions = explicit_premises
        .iter()
        .cloned()
        .fold(available.assumptions().clone(), |assumptions, premise| {
            assumptions.assume_proposition(premise)
        });
    // Never resolve the target through the recorded surface map: the same
    // surface form may deliberately name an older source state.
    let target = lower_fixed_state_proposition_with_assumptions(
        surface_target,
        &target_lowering_assumptions,
        parameter_binding,
        fixed_state,
        spec_definitions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower `transport` target: {message}"
        ))
    })?;
    if crate::surface::proof_trace::enabled_for(claim_label) {
        *checked_target = Some(target.clone());
    }
    // A source that evaluated to true needs no symbolic frame when the
    // target is already held. Re-lowering it symbolically first can replace
    // a checked store equality by a joined read that its cited, evaluated
    // premise no longer names.
    let target_is_available =
        concrete_source_is_true.then(|| available.available_across_effects(&target, effect_facts));
    if target_is_available == Some(true) {
        return Ok(CheckedFixedStateFactTransport {
            source: ordinary_source,
            target,
        });
    }
    let source = if concrete_source_is_true
        && (proposition_contains_at_expression(surface_source)
            || proposition_contains_old_expression(surface_source))
    {
        let symbolic_assumptions = available
            .assumptions()
            .clone()
            .allow_symbolic_contract_loads()
            .force_symbolic_external_loads();
        lower_fixed_state_proposition_with_assumptions(
            surface_source,
            &symbolic_assumptions,
            parameter_binding,
            fixed_state,
            spec_definitions,
        )
        .unwrap_or(ordinary_source)
    } else {
        ordinary_source
    };
    // An explicit alias transport needs only its cited source and equality.
    // Check that selected operation before introducing the live resource
    // composition or consulting the ambient state/effect context.
    if matches!(
        (&source, &target),
        (
            Proposition::ResourceSeparate { .. },
            Proposition::ResourceSeparate { .. }
        )
    ) && exact_fact_is_available(&source, &explicit_premises)
        && certified_fact_transport_reaches(
            &source,
            &target,
            None,
            &explicit_assumptions
                .clone()
                .assume_proposition(source.clone()),
        )
    {
        return Ok(CheckedFixedStateFactTransport { source, target });
    }
    let resource_facts = fixed_state
        .state
        .resources()
        .observable_facts_assuming_valid(&explicit_assumptions);
    let selected_assumptions = explicit_premises
        .iter()
        .cloned()
        .chain(resource_facts)
        .fold(
            available.implicit_transport_assumptions().clone(),
            |assumptions, fact| assumptions.assume_proposition(fact),
        );
    // At a completed return outcome, the source is its own checked slot in
    // `transport(source, target)`: it may name an exact result-path fact
    // without being duplicated in `using`. A quantified source names it up
    // to its binder's name, as a listed premise does: a call's postcondition
    // is held with the binder its lowering chose. Both are indexed lookups.
    // Mid-execution transport retains the stricter rule that `using` must
    // establish its logical source. A selected outcome state that
    // materializes to true likewise checks the equivalent symbolic source
    // used for frame transport.
    let source_is_available =
        || available.contains(&source) || available.quantified_fact_available(&source);
    if !(fixed_state.result.is_some() && (concrete_source_is_true || source_is_available()))
        && !holds_without_facts_under_binders(&source)
        && !exact_fact_is_available(&source, &explicit_premises)
        && !separation_bridged_fact_is_available(
            &source,
            &explicit_premises,
            &selected_assumptions,
            effect_facts,
        )
        && crate::kernel::search::ProofSearch::derive_atomic_proposition(
            &(selected_assumptions),
            &source,
        )
        .is_none()
    {
        // Mid-execution, an available source that `using` does not list is
        // refused only for not being listed. Say so, naming it as written,
        // rather than print it as missing beside the facts that hold it.
        if source_is_available() {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `transport using` requires a source derivable from its explicit facts: its source `{}` is an available fact, but this check reads only the facts listed in `using`; list the source there",
                crate::surface::printing::source_click_proposition(surface_source),
            )));
        }
        let available = available.to_vec();
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `transport using` requires a source derivable from its explicit facts: {}",
            describe_missing_pure_fact(
                &source,
                &available,
                fixed_state.state.resources().facts(),
                parameter_binding,
                effect_facts,
            )
        )));
    }

    if !target_is_available
        .unwrap_or_else(|| available.available_across_effects(&target, effect_facts))
    {
        let transition_facts = fact_transport_transition_facts(effect_facts, &source);
        // Uncharged, a known violation: the path's effect facts and the
        // listed premises below are assumed afresh at each explicit
        // transport, so a transport is linear in the path; charging these
        // two builds grows `expanded_roundtrip_work_per_source_byte_is_logarithmic`
        // faster than its bound (docs/internals/verification-efficiency.md).
        crate::kernel::reasoning::path_facts::count_uncharged_context_entries(
            transition_facts.len() + 1,
        );
        let source_is_true = crate::kernel::proposition_holds_without_facts(&source);
        let transport_assumptions =
            transition_facts
                .iter()
                .fold(selected_assumptions, |assumptions, fact| {
                    assumptions.assume_proposition_uncharged(fact.proposition().clone())
                });
        // A tautology is already justified without an assumption. Keeping
        // its incidental load names in the query context makes otherwise
        // identical failed frame questions have different context identities.
        let transport_assumptions = if source_is_true {
            transport_assumptions
        } else {
            transport_assumptions.assume_proposition_uncharged(source.clone())
        };
        // Load-variable bridges decide search-free before the reachability
        // walk: a target equating two internal names for one unchanged cell
        // needs only the bounded origins proof, and the walk's general
        // equality legs would re-enter state comparison on exactly these
        // targets.
        let chain_facts: Vec<Proposition> = {
            let mut chain_facts = explicit_premises.clone();
            if !source_is_true {
                chain_facts.push(source.clone());
            }
            // The frontier's certified effect facts (call postconditions and
            // effect summaries) may relate a load at one state to the same
            // cell at another: load names are not preserved across call-havoc
            // and store edges by path assumptions (see `MemoryDerivation`).
            // They are certified facts, not user premises.
            chain_facts.extend(
                effect_facts
                    .fact_iter()
                    .map(|fact| fact.proposition().clone())
                    .filter(|fact| matches!(fact, Proposition::ConditionIs(_, _))),
            );
            chain_facts
        };
        // The origins-unchanged frame evidence reads the listed premises, the
        // certified effect facts, and the implicit frame facts (loadability,
        // store permission, separation) the selected assumptions carry; it
        // never searches the rest of the proof context. It only decides whether two
        // load variables denote one unchanged cell.
        let chain_assumptions = chain_facts
            .iter()
            .flat_map(|fact| {
                // A separation's bounds travel with it as a conjunction.
                // Frame evidence may use its leaves, but never facts under
                // an implication or a quantifier.
                let mut parts = Vec::new();
                atomic_conjuncts(fact, &mut parts);
                parts
            })
            .filter(|fact| {
                // Separations are frame justification too: crossing a call's
                // havoc edge for a load outside the callee's footprint is
                // decided by exactly these facts, checked in this context.
                matches!(
                    fact,
                    Proposition::ConditionIs(_, _)
                        | Proposition::MemoryMutatesOnly { .. }
                        | Proposition::MemoryEffectSummary { .. }
                        | Proposition::HeapAllocationFreed { .. }
                        | Proposition::ResourceSeparate { .. }
                        | Proposition::ResourceComposition(_)
                )
            })
            .fold(transport_assumptions.clone(), |assumptions, fact| {
                crate::kernel::reasoning::path_facts::count_uncharged_context_entries(1);
                assumptions.assume_proposition_uncharged(fact.clone())
            });
        let bridge_propositions = std::iter::once(&target)
            .chain(chain_facts.iter())
            .collect::<Vec<_>>();
        if crate::kernel::closure_memoized_fact_check(
            crate::kernel::ClosureFactCheck::LoadVariableBridge,
            &bridge_propositions,
            None,
            &chain_assumptions,
            &[],
            || {
                super::super::fact_reasoning::premise_bridged_by_load_variable_chain_with_origins(
                    &target,
                    &chain_facts,
                    &chain_assumptions,
                )
            },
        ) {
            return Ok(CheckedFixedStateFactTransport { source, target });
        }
        // A fact about a checked range-fold application crosses a step that
        // provably misses every cell the fold reads. The kernel decides it
        // from the function's checked read summary, each recorded step's own
        // write set, and exact order and separation facts of this context;
        // the answer is this query's derivation and is recorded nowhere else.
        //
        // The rule is a checked simple step and answers the same for every
        // caller: an explicit `transport ... using`, a planned transport, and
        // `solve`'s state transport closure all ask it the same question.
        let fold_frame = crate::instrumentation::measure_operation(
            "surface",
            "fact transport",
            "explicit fact transport: fold read frame",
            || {
                crate::kernel::frame_fold_application_transport(
                    &source,
                    &target,
                    available.assumptions(),
                )
            },
        );
        let fold_refusal = match fold_frame {
            Ok(_) => return Ok(CheckedFixedStateFactTransport { source, target }),
            Err(refusal) => refusal,
        };
        // A quantified fact crosses the same steps leaf by leaf: each universal
        // binder is renamed fresh, each guard is assumed on the proving side,
        // and each differing condition leaf is carried by its reads' checked
        // load history, read in this context's own facts, or by the
        // single-fact transport below, read in its own premises. Like the
        // fold frame, the answer is this query's derivation and nothing else.
        let quantified_frame = || {
            crate::instrumentation::measure_operation(
                "surface",
                "fact transport",
                "explicit fact transport: quantified frame",
                || {
                    let with_resources = |assumptions: PureFactContext| {
                        fixed_state
                            .state
                            .resources()
                            .observable_facts_assuming_valid(&assumptions)
                            .into_iter()
                            .fold(assumptions, PureFactContext::assume_proposition)
                    };
                    let resource_facts = fixed_state
                        .state
                        .resources()
                        .observable_facts_assuming_valid(available.assumptions());
                    let mut context_variables = std::collections::BTreeSet::new();
                    for fact in effect_facts
                        .fact_iter()
                        .map(ExecutionPureFact::proposition)
                        .chain(resource_facts.iter())
                    {
                        context_variables.extend(crate::kernel::proposition_variables(fact));
                    }
                    let context = effect_facts
                        .fact_iter()
                        .map(|fact| fact.proposition().clone())
                        .chain(resource_facts)
                        .fold(
                            available.assumptions().clone(),
                            PureFactContext::assume_proposition,
                        );
                    let leaf = |from: &Proposition,
                                to: &Proposition,
                                assumptions: &PureFactContext| {
                        let assumptions = if crate::kernel::proposition_holds_without_facts(from) {
                            assumptions.clone()
                        } else {
                            assumptions.clone().assume_proposition(from.clone())
                        };
                        certified_fact_transport_reaches_through(
                            from,
                            to,
                            fixed_state.state.memory(),
                            &assumptions,
                            &transition_facts,
                        )
                    };
                    crate::kernel::frame_quantified_transport(
                        &source,
                        &target,
                        &available,
                        &context,
                        &transport_assumptions,
                        &leaf,
                        &with_resources,
                        &context_variables,
                    )
                },
            )
        };
        if !certified_fact_transport_reaches_through(
            &source,
            &target,
            fixed_state.state.memory(),
            &transport_assumptions,
            &transition_facts,
        ) {
            // Only where the single-fact route refused, so every transport it
            // already carried costs exactly what it did.
            // A smart closure asks the same failing frame once per state
            // and strategy; it answers a repeat from its failure memo, as it
            // does for the reachability walk.
            let mut frame_refusal = None;
            let framed = crate::kernel::closure_memoized_fact_check(
                crate::kernel::ClosureFactCheck::QuantifiedFrame,
                &[&source, &target],
                Some(fixed_state.state.memory()),
                available.assumptions(),
                effect_facts,
                || match quantified_frame() {
                    Ok(()) => true,
                    Err(refusal) => {
                        frame_refusal = Some(refusal);
                        false
                    }
                },
            );
            if framed {
                // The frame's reads consult the proof context only through
                // the kernel's checked load equality, a bounded walk over
                // recorded history that looks up separation and order facts:
                // the fast path's kind of decision, not a search.
                return Ok(CheckedFixedStateFactTransport { source, target });
            }
            // A repeat answered from the failure memo never ran the frame, so
            // this refusal names the leaf only if the frame runs once more:
            // the report must not depend on whether a planner asked first.
            let read_refusal = frame_refusal
                .or_else(|| quantified_frame().err())
                .unwrap_or(crate::kernel::QuantifiedFrameRefusal::NothingToFrame);
            let mut labels =
                render::MemoryStateLabels::with_state(parameter_binding, fixed_state.state);
            labels.source_state(fixed_state.pre_state, "function.entry".into());
            for (selector, retained_state) in fixed_state.recorded_states.recent(16) {
                labels.source_state(retained_state, describe_program_point_selector(selector));
            }
            let mut rendered = describe_unreachable_fact_transport(
                claim_label,
                tactic_index,
                surface_source,
                surface_target,
                &source,
                &target,
                &transition_facts,
                &mut labels,
            );
            if !matches!(
                fold_refusal,
                crate::kernel::FoldFrameRefusal::ShapeMismatch
                    | crate::kernel::FoldFrameRefusal::NothingToFrame
            ) {
                rendered.push_str(&format!("\n  fold read frame: {fold_refusal}"));
            }
            // The leaf pair says something the lines above do not only when a
            // binder stood between the two propositions and their leaves.
            let quantified = matches!(source, Proposition::ForAll { .. })
                && matches!(target, Proposition::ForAll { .. });
            match &read_refusal {
                crate::kernel::QuantifiedFrameRefusal::LeafNotCarried { from, to }
                    if quantified =>
                {
                    // One label set for both leaves, so a read they share is
                    // spelled once and two different reads never share a name.
                    // It knows the recorded states the report above names, and
                    // its `where` list says what produced every other state.
                    let mut labels =
                        render::MemoryStateLabels::with_state(parameter_binding, fixed_state.state);
                    labels.source_state(fixed_state.pre_state, "function.entry".into());
                    for (selector, retained_state) in fixed_state.recorded_states.recent(16) {
                        labels.source_state(
                            retained_state,
                            describe_program_point_selector(selector),
                        );
                    }
                    // A leaf reads at its binder, which the source names.
                    for (kernel, surface) in [(&source, surface_source), (&target, surface_target)]
                    {
                        if let Proposition::ForAll { var, .. } = kernel
                            && let Some(name) = quantifier_binder_name(surface)
                        {
                            labels.source_name(**var, name);
                        }
                    }
                    let had = render::render_proposition_labeled(from, &mut labels);
                    let wanted = render::render_proposition_labeled(to, &mut labels);
                    rendered.push_str(&format!(
                        "\n  quantified frame: {read_refusal}\n  leaf it had: {had}\n  leaf it wanted: {wanted}{}",
                        labels.trace_legend(),
                    ));
                }
                crate::kernel::QuantifiedFrameRefusal::BinderExhausted => {
                    rendered.push_str(&format!("\n  quantified frame: {read_refusal}"));
                }
                _ => {}
            }
            return Err(ClickError::new(rendered).with_report_labels(labels));
        }
    }
    Ok(CheckedFixedStateFactTransport { source, target })
}

/// The refusal of a checked `transport using` whose source and premises
/// lowered and held, but whose frame could not carry the source to the
/// target. A bare `transport` reports it when its planner selects nothing
/// better (`fact_transport_planning_failure`).
const NO_FRAME_EVIDENCE: &str =
    "found no frame evidence carrying its source fact to the target's state";

/// Show the written and checked propositions with one shared state legend.
/// Include every frontier effect: a truncated list can hide the missing frame.
/// The name a quantified proposition's source gives its binder: the written
/// spelling when hygiene renamed it, through any `at(...)` around it.
fn quantifier_binder_name(surface: &ClickProposition) -> Option<String> {
    match surface {
        ClickProposition::At { proposition, .. } => quantifier_binder_name(proposition),
        ClickProposition::ForAll {
            name, written_name, ..
        } => Some(
            written_name
                .clone()
                .or_else(|| name.written().map(str::to_owned))
                .unwrap_or_else(|| "value".into()),
        ),
        ClickProposition::RangeAll {
            item, written_item, ..
        } => Some(
            written_item
                .clone()
                .or_else(|| item.written().map(str::to_owned))
                .unwrap_or_else(|| "item".into()),
        ),
        _ => None,
    }
}

fn describe_unreachable_fact_transport(
    claim_label: &str,
    tactic_index: usize,
    surface_source: &ClickProposition,
    surface_target: &ClickProposition,
    source: &Proposition,
    target: &Proposition,
    transition_facts: &(impl ExecutionFactSource + ?Sized),
    labels: &mut render::MemoryStateLabels,
) -> String {
    // Refusals must expose checked identities even outside --trace-proof.
    let _exact = render::TypedNotationScope::enter();
    let mut rendered = format!(
        "`{claim_label}` tactic {tactic_index}: `transport using` {NO_FRAME_EVIDENCE}\
         \n  source (holds): {}\
         \n  target (wanted): {}",
        crate::surface::printing::source_click_proposition(surface_source),
        crate::surface::printing::source_click_proposition(surface_target),
    );
    let checked_source = render::render_proposition_labeled(source, labels);
    let checked_target = render::render_proposition_labeled(target, labels);
    rendered.push_str(&format!(
        "\n  checked source (holds): {checked_source}\n  checked target (wanted): {checked_target}"
    ));
    let walks = crate::kernel::take_transport_cell_walk_diagnostics();
    if !walks.is_empty() {
        rendered.push_str("\n  cell walks performed while checking transport (identical observations shown once):");
        for walk in &walks {
            rendered.push_str("\n    ");
            rendered.push_str(&render::render_transport_cell_walk(walk, labels));
        }
    }

    if transition_facts.is_empty() {
        rendered.push_str(&labels.trace_legend());
        rendered.push_str(
            "\n  no effect fact at this frontier relates the two states, so the target must \
             follow from the source and the listed premises alone, and it does not: check that \
             they cover the target (for a range, that its index is inside the range); if the two \
             sides read the same memory, the target is not a transport but an ordinary goal — \
             prove it with the rule that decides it, such as `close()` or a theorem application",
        );
        return rendered;
    }
    let total = transition_facts.len();
    rendered.push_str(&format!(
        "\n  effect facts relating states at this frontier ({total}):"
    ));
    for fact in transition_facts.fact_iter() {
        rendered.push_str("\n    ");
        rendered.push_str(&render::render_proposition_labeled(
            fact.proposition(),
            labels,
        ));
        if let Proposition::MemoryMutatesOnly { writes, .. } = fact.proposition() {
            for (pointer, bytes) in writes.iter() {
                if let Some((names, values)) = labels.naming_tables()
                    && let Some(cell) = crate::surface::diagnostics::diagnostic_source_cell(
                        pointer,
                        ParameterBinding::new(names, values),
                    )
                {
                    rendered.push_str(&format!(
                        "\n    memory change: store to {cell} ({bytes} bytes)"
                    ));
                }
            }
        }
    }

    rendered.push_str(&labels.trace_legend().replace(
        "label definitions (recorded constructions, not additional facts):",
        "transport label definitions (shared by checked source, target, and effects):",
    ));
    rendered
        .push_str("\n  no checked route established the target from these premises and effects");
    rendered
}

fn surface_predicate_call_name(proposition: &ClickProposition) -> Option<&str> {
    match proposition {
        ClickProposition::Value(_) => None,
        ClickProposition::PredicateCall { name, .. } => Some(name),
        ClickProposition::At { proposition, .. }
        | ClickProposition::Not(proposition)
        | ClickProposition::ForAll {
            body: proposition, ..
        }
        | ClickProposition::Exists {
            body: proposition, ..
        }
        | ClickProposition::RangeAll {
            body: proposition, ..
        }
        | ClickProposition::RangeAny {
            body: proposition, ..
        } => surface_predicate_call_name(proposition),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            surface_predicate_call_name(left).or_else(|| surface_predicate_call_name(right))
        }
        ClickProposition::Comparison { .. }
        | ClickProposition::FloatClassification { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::ResourceViewable { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. }
        | ClickProposition::IsA { .. } => None,
    }
}

/// The refusal a bare `transport` reports when its premise planner fails.
///
/// `source_refusal` is the refusal of the bare form's own first attempt,
/// the checked `transport using` with its source as the only premise. When
/// that check got as far as the frame, its refusal already names the leaf
/// the frame could not carry, the cell walks that stopped it and the effects
/// between the two states, so it is the answer: the planner's own failure
/// says only that no premise selection helped.
pub(in crate::surface::proof) fn fact_transport_planning_failure(
    source: &ClickProposition,
    target: &ClickProposition,
    error: &ClickError,
    source_refusal: Option<&ClickError>,
) -> String {
    let opaque_name = [source, target]
        .into_iter()
        .filter_map(surface_predicate_call_name)
        .next();
    if let Some(name) = opaque_name {
        return format!(
            "`transport` cannot frame opaque predicate `{name}` across C execution because its memory footprint is hidden; unfold the selected application, such as `unfold({name}(args));`, before execution and transport its unfolded definition"
        );
    }
    if let Some(frame_refusal) = source_refusal.and_then(|refusal| {
        let summary = refusal.raw_summary();
        summary
            .find(NO_FRAME_EVIDENCE)
            .map(|start| &summary[start..])
    }) {
        return format!(
            "`transport` {frame_refusal}\n  this is the refusal with the source as the only premise, which is all a bare `transport` cites{TRANSPORT_SEARCH_MISS}"
        );
    }
    format!(
        "could not make fact transport premises explicit: {}{TRANSPORT_SEARCH_MISS}",
        error.raw_summary()
    )
}

/// The line a bare `transport` adds when its premise planner finds no frame
/// evidence. The planner is a search, so finding nothing is a search miss:
/// the fix is the evidence written in the explicit form, which searches
/// nothing and whose refusal is the frame check's own.
const TRANSPORT_SEARCH_MISS: &str = "\n  this is a search miss, not a refusal; if the target holds, list the facts that carry the source in `transport(P, Q) using { ... }`, stating any that is not available with `have` first";

/// Erases every embedded memory state from a comparison proposition so
/// two forms of the same comparison at different states compare
/// equal; used as a cheap prefilter before attempting a transport proof.
pub(in crate::surface::proof) fn memory_erased_comparison(
    proposition: &Proposition,
) -> Option<Proposition> {
    fn erase_term(term: &MachineTerm) -> MachineTerm {
        match term {
            MachineTerm::MemoryLoad(_, pointer, kind) => crate::kernel::MachineTerm::read_named(
                crate::kernel::ProgramPoint::at(
                    &(crate::kernel::intern_memory(SymbolicMemory::default())),
                ),
                Address {
                    base: pointer.base.clone(),
                    offset: erase_offset(&pointer.offset),
                },
                *kind,
            ),
            binary_term!(Bits32 @ format32, Add, left, right) => {
                binary_node!(
                @ *format32,
                Add,
                    Box::new(erase_term(left)),
                    Box::new(erase_term(right))
                )
            }
            binary_term!(Bits32 @ format32, Subtract, left, right) => {
                binary_node!(
                @ *format32,
                Subtract,
                    Box::new(erase_term(left)),
                    Box::new(erase_term(right))
                )
            }
            binary_term!(Bits32 @ format32, Multiply, left, right) => {
                binary_node!(
                @ *format32,
                Multiply,
                    Box::new(erase_term(left)),
                    Box::new(erase_term(right))
                )
            }
            other => other.clone(),
        }
    }
    fn erase_offset(offset: &AddressOffset) -> AddressOffset {
        match offset {
            AddressOffset::Add(left, right) => {
                AddressOffset::Add(Box::new(erase_offset(left)), Box::new(erase_offset(right)))
            }
            AddressOffset::Int32Scaled { value, byte_width } => {
                AddressOffset::scaled_int32_node(erase_term(value.structural_value()), *byte_width)
            }
            other => other.clone(),
        }
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    let erased = match condition.native_compat() {
        // A 32-bit comparison, signed or `uint32` (equality is filed at
        // `int32`).
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation,
            left,
            right,
        } => ConditionTerm::Compare {
            format: *format,
            relation: *relation,
            left: Box::new(erase_term(left)),
            right: Box::new(erase_term(right)),
        },
        _ => return None,
    };
    Some(Proposition::condition_is(erased, *value))
}

/// Compares branch facts after erasing the memory state captured at the
/// branch split. In addition to the kernel's canonical forms, accept the
/// ordinary complementary and operand-reversed forms of 32-bit order
/// comparisons, signed or `uint32` (for example, `!(a < b)` and `a >= b`).
pub(in crate::surface::proof) fn path_condition_equivalent(
    left: &Proposition,
    right: &Proposition,
) -> bool {
    fn signed_order_equivalent(left: &Proposition, right: &Proposition) -> bool {
        let (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) = (left, right)
        else {
            return false;
        };
        use CompareRelation::{
            GreaterEqual as Ge, GreaterThan as Gt, LessEqual as Le, LessThan as Lt,
        };
        let (
            ConditionTerm::Compare {
                format: left_format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                relation: left_relation,
                left,
                right,
            },
            ConditionTerm::Compare {
                format: right_format,
                relation: right_relation,
                left: other_left,
                right: other_right,
            },
        ) = (
            left_condition.native_compat(),
            right_condition.native_compat(),
        )
        else {
            return false;
        };
        // An order compares in one signedness: a `uint32` order is never a
        // signed one.
        if left_format != right_format {
            return false;
        }
        match (left_relation, right_relation) {
            (Lt, Ge) | (Ge, Lt) | (Le, Gt) | (Gt, Le) => {
                left == other_left && right == other_right && left_value != right_value
            }
            (Lt, Gt) | (Gt, Lt) | (Le, Ge) | (Ge, Le) => {
                left == other_right && right == other_left && left_value == right_value
            }
            _ => false,
        }
    }

    fn symmetric_equality_equivalent(left: &Proposition, right: &Proposition) -> bool {
        let (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) = (left, right)
        else {
            return false;
        };
        if left_value != right_value {
            return false;
        }
        match (
            left_condition.native_compat(),
            right_condition.native_compat(),
        ) {
            (
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left: other_left,
                    right: other_right,
                },
            ) => left == other_right && right == other_left,
            (
                ConditionTerm::AddressOffsetEqual(left, right),
                ConditionTerm::AddressOffsetEqual(other_left, other_right),
            ) => left == other_right && right == other_left,
            (
                ConditionTerm::AddressEqual(left, right),
                ConditionTerm::AddressEqual(other_left, other_right),
            ) => left == other_right && right == other_left,
            _ => false,
        }
    }

    if condition_polarity_equivalent(left, right)
        || signed_order_equivalent(left, right)
        || symmetric_equality_equivalent(left, right)
    {
        return true;
    }
    let (Some(left), Some(right)) = (
        memory_erased_comparison(left),
        memory_erased_comparison(right),
    ) else {
        return false;
    };
    condition_polarity_equivalent(&left, &right)
        || signed_order_equivalent(&left, &right)
        || symmetric_equality_equivalent(&left, &right)
}

/// Like [`certified_fact_transport_reaches`], but first rewrites the source
/// through the transition facts' certified stores, so a fact written in
/// pre-store terms can reach a post-store form.
pub(in crate::surface::proof) fn certified_fact_transport_reaches_through(
    source: &Proposition,
    target: &Proposition,
    after: &SymbolicMemory,
    assumptions: &PureFactContext,
    transitions: &(impl ExecutionFactSource + ?Sized),
) -> bool {
    crate::kernel::closure_memoized_fact_check(
        crate::kernel::ClosureFactCheck::Reachability,
        &[source, target],
        Some(after),
        assumptions,
        transitions,
        || {
            certified_fact_transport_reaches_through_unmemoized(
                source,
                target,
                after,
                assumptions,
                transitions,
            )
        },
    )
}

fn certified_fact_transport_reaches_through_unmemoized(
    source: &Proposition,
    target: &Proposition,
    after: &SymbolicMemory,
    assumptions: &PureFactContext,
    transitions: &(impl ExecutionFactSource + ?Sized),
) -> bool {
    if certified_fact_transport_reaches(source, target, Some(after), assumptions) {
        return true;
    }
    let rewritten = crate::kernel::rewrite_condition_through_certified_stores(source, transitions);
    if &rewritten == source {
        return false;
    }

    rewritten.clone() == target.clone()
        || crate::kernel::program_condition_facts_equivalent_for_memory_resolution(
            &rewritten,
            target,
            assumptions,
        )
        || certified_fact_transport_reaches(&rewritten, target, Some(after), assumptions)
}

/// Whether the checked `transport` conclusion `target` follows from the exact
/// source fact under `assumptions`.
///
/// `after` is the state the transport lands in, and is `None` in a pure
/// theorem, which has no C state. Only the final store-rewrite route needs it;
/// every other route — the structural recursion, the resource rules, the
/// memory-loadability decision, and the condition-fact matching — reads facts
/// and terms alone. A pure theorem and a fixed-state proof therefore accept
/// the same conclusions from the same facts, through this one function.
pub(in crate::surface::proof) fn certified_fact_transport_reaches(
    source: &Proposition,
    target: &Proposition,
    after: Option<&SymbolicMemory>,
    assumptions: &PureFactContext,
) -> bool {
    // A checked read at a computed address includes its address-definedness
    // obligations. Prove every target leaf from the same selected facts;
    // those obligations must not prevent transport of the read itself.
    if matches!(target, Proposition::And(_, _)) {
        let mut pending = vec![target];
        while let Some(leaf) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let Proposition::And(left, right) = leaf {
                pending.push(right);
                pending.push(left);
            } else if !assumptions.proves_exact(leaf)
                && !crate::kernel::proposition_holds_without_facts(leaf)
                && !certified_fact_transport_reaches(source, leaf, after, assumptions)
            {
                return false;
            }
        }
        return true;
    }
    let equivalent = |left: &Proposition, right: &Proposition| {
        left == right
            || crate::kernel::program_condition_facts_equivalent_for_memory_resolution(
                left,
                right,
                assumptions,
            )
    };
    match (source, target) {
        (
            Proposition::ForAll {
                var: source_var,
                sort: source_sort,
                body: source_body,
                ..
            },
            Proposition::ForAll {
                var: target_var,
                sort: target_sort,
                body: target_body,
                ..
            },
        ) if source_var == target_var && source_sort == target_sort => {
            // Open both bodies at one fresh variable: the binder means nothing
            // outside its quantifier, and the antecedents below are assumed.
            let Some((witness, source_body)) =
                crate::kernel::quantifiers::open_quantifier(*source_var, source_sort, source_body)
            else {
                return false;
            };
            let Some(target_body) = crate::kernel::quantifiers::rename_quantified_variable(
                target_body,
                **target_var,
                witness,
                target_sort,
            ) else {
                return false;
            };
            return certified_fact_transport_reaches(
                &source_body,
                &target_body,
                after,
                assumptions,
            );
        }
        (
            Proposition::Implies(source_antecedent, source_consequent),
            Proposition::Implies(target_antecedent, target_consequent),
        ) if equivalent(source_antecedent, target_antecedent) => {
            let consequent_assumptions = assumptions
                .clone()
                .assume_proposition(target_antecedent.as_ref().clone());
            return certified_fact_transport_reaches(
                source_consequent,
                target_consequent,
                after,
                &consequent_assumptions,
            );
        }
        (
            Proposition::And(source_left, source_right),
            Proposition::And(target_left, target_right),
        )
        | (
            Proposition::Or(source_left, source_right),
            Proposition::Or(target_left, target_right),
        ) => {
            return certified_fact_transport_reaches(source_left, target_left, after, assumptions)
                && certified_fact_transport_reaches(
                    source_right,
                    target_right,
                    after,
                    assumptions,
                );
        }
        (Proposition::Not(source_body), Proposition::Not(target_body)) => {
            return equivalent(source_body, target_body);
        }
        (
            Proposition::ResourceSeparate {
                left: source_left,
                right: source_right,
            },
            Proposition::ResourceSeparate {
                left: target_left,
                right: target_right,
            },
        ) => {
            return crate::instrumentation::measure_operation(
                "kernel",
                "fact transport",
                "resource separation transport: direct orientation",
                || {
                    crate::instrumentation::measure_operation(
                        "kernel",
                        "fact transport",
                        "resource separation transport: direct left",
                        || resources_directly_match(source_left, target_left, assumptions),
                    ) && crate::instrumentation::measure_operation(
                        "kernel",
                        "fact transport",
                        "resource separation transport: direct right",
                        || resources_directly_match(source_right, target_right, assumptions),
                    )
                },
            ) || crate::instrumentation::measure_operation(
                "kernel",
                "fact transport",
                "resource separation transport: swapped orientation",
                || {
                    resources_directly_match(source_left, target_right, assumptions)
                        && resources_directly_match(source_right, target_left, assumptions)
                },
            );
        }
        (
            Proposition::ResourceContains {
                parent: source_parent,
                child: source_child,
            },
            Proposition::ResourceContains {
                parent: target_parent,
                child: target_child,
            },
        ) => {
            return resources_directly_match(source_parent, target_parent, assumptions)
                && resources_directly_match(source_child, target_child, assumptions);
        }
        _ => {}
    }
    if let Proposition::MemoryReadDefined {
        memory,
        pointer,
        value_type,
        ..
    } = target
    {
        return assumptions.proves_memory_read_defined(memory, pointer, *value_type);
    }
    if matches!(target, Proposition::MemoryLoadable { .. }) {
        return crate::kernel::search::ProofSearch::derive_atomic_proposition(assumptions, target)
            .is_some();
    }
    // A reflexive source adds no information. Match the target directly in
    // this context rather than comparing both copies of the source's load
    // with both target operands, then transporting the same tautology.
    if matches!(&(source, target), (
            condition_source_0 @ Proposition::ConditionIs(_, true),
            condition_source_1 @ Proposition::ConditionIs(_, true)
        ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left, right }, _)) if matches!(condition_source_1.condition_native(), Some((ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, .. }, _)) if (left == right))))
    {
        return crate::kernel::api::program_condition_fact_target_reaches_in_context(
            source,
            target,
            assumptions,
        );
    }
    // Two forms of the same condition fact — for example an element load
    // whose symbolic index the listed order facts pin to a constant — match
    // by the same bounded rule the atomic prover uses on context facts.
    if crate::kernel::program_condition_facts_match_for_transport(source, target, assumptions) {
        return true;
    }
    // This operation retains its live context. The context-bound rule
    // decides it directly; exporting a standalone theorem first repeats
    // the decision and constructs premises that this operation never exports.
    if crate::kernel::api::program_condition_fact_target_reaches_in_context(
        source,
        target,
        assumptions,
    ) {
        return true;
    }
    let Some(after) = after else {
        return false;
    };
    let Some(theorem) = prove_program_condition_fact_transport(source, after, assumptions) else {
        return false;
    };
    crate::kernel::program_condition_fact_transport_target_in_context(&theorem, source, assumptions)
        == Some(target)
}

/// A proposition that holds without facts once its universal binders, guards
/// and conjunctions are read through: `forall (k: int32) { G implies x == x }`
/// holds for every `k` whatever `G` says. Only a transport's source and its
/// `using` list read this; the shared rule
/// (`proposition_holds_without_facts`) stays the leaf.
fn holds_without_facts_under_binders(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::ForAll { body, .. } => holds_without_facts_under_binders(body),
        Proposition::Implies(_, consequent) => holds_without_facts_under_binders(consequent),
        Proposition::And(left, right) => {
            holds_without_facts_under_binders(left) && holds_without_facts_under_binders(right)
        }
        _ => crate::kernel::proposition_holds_without_facts(proposition),
    }
}

#[cfg(test)]
mod path_condition_tests {
    use super::*;

    #[test]
    fn compound_read_transport_requires_every_address_guard_and_range() {
        let memory = SymbolicMemory::new();
        let base = Address {
            base: "bytes".into(),
            offset: AddressOffset::Constant(0),
        };
        let source = Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: (MachineTerm::constant(1)).into(),
            wide: false,
        };
        let guard = Proposition::condition_is(
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Subtract,
                left: Box::new(MachineTerm::Variable(Variable(7))),
                right: Box::new(MachineTerm::constant(1)),
            },
            false,
        );
        let target = Proposition::And(Box::new(guard.clone()), Box::new(source.clone()));
        let facts = PureFactContext::new().assume_proposition(source.clone());
        assert!(!certified_fact_transport_reaches(
            &source, &target, None, &facts
        ));
        let facts = facts.assume_proposition(guard.clone());
        assert!(certified_fact_transport_reaches(
            &source, &target, None, &facts
        ));
        let wider = Proposition::MemoryLoadable {
            memory,
            base,
            bytes: (MachineTerm::constant(2)).into(),
            wide: false,
        };
        let invalid = Proposition::And(Box::new(guard), Box::new(wider));
        assert!(!certified_fact_transport_reaches(
            &source, &invalid, None, &facts
        ));
    }

    #[test]
    fn pointer_offset_path_equality_accepts_reversed_operands() {
        let left = AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(41)), 4);
        let right = AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(42)), 4);
        let forward = Proposition::condition_is(
            ConditionTerm::AddressOffsetEqual(Box::new(left.clone()), Box::new(right.clone())),
            true,
        );
        let reversed = Proposition::condition_is(
            ConditionTerm::AddressOffsetEqual(Box::new(right), Box::new(left)),
            true,
        );

        assert!(path_condition_equivalent(&forward, &reversed));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../../scaling_tests/surface/proof/fixed_state_proofs/fact_transport/path_condition_tests.rs"
        );
    }
}
