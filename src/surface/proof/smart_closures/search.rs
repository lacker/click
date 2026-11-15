//! Discovery over Surface proof presentations; semantic state remains in ProofObject.
use super::*;

/// Premise citations must already be evaluable; a proposed `have` may
/// carry evaluation requirements that its ordinary driver still must prove.
#[derive(Clone, Copy)]
enum SurfaceSpellingPurpose {
    AvailablePremise,
    ProposedGoal,
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Retain computational `known` or a genuinely selected normalization.
    /// A goal outside those rules must continue to explicit derivation search.
    pub(in crate::surface::proof) fn apply_normalization_closure(
        search_input: &Proof<'a>,
        premises: Option<Vec<ClickProposition>>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_normalization_closure");
        let step = if search_input
            .goal()
            .is_some_and(crate::surface::planning::solve::computes_with_known)
        {
            ProofStep::Known
        } else {
            match premises {
                Some(premises) => ProofStep::NormalizeUsing(premises),
                None => {
                    return Err(search_input
                        .step_error("this goal requires an explicit checked derivation"));
                }
            }
        };
        search_input.driver().apply_step(step)
    }

    /// Strategy dispatch for the smart arithmetic step. Keep the same selected
    /// premise order, explicit certificates, and refusal precedence as solve.
    pub(in crate::surface::proof) fn apply_arithmetic_using(
        search_input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_arithmetic_using");
        if let Some(proof) = Self::try_integer_add_le_using(search_input, premises)? {
            return Ok(proof);
        }
        if let Some(proof) = Self::try_unsigned_order_step_using(search_input, premises) {
            return Ok(proof);
        }
        let ordinary = search_input
            .driver()
            .apply_step_without_outcome_wrapping_after_wide(ProofStep::ArithmeticUsing(
                premises.to_vec(),
            ));
        if ordinary.is_ok() {
            return ordinary;
        }
        if let Some(refuted) = Self::disequality_by_refutation(search_input, premises) {
            return refuted;
        }
        match Self::try_wide_arithmetic_using(search_input, premises) {
            Ok(proof) => Ok(proof),
            Err(Some(reason)) => Err(search_input.step_error(format!(
                "arithmetic read the current goal as a 64-bit comparison: {reason}"
            ))),
            Err(None) => ordinary,
        }
    }

    /// Stage one of ordinary arithmetic expansion: one addition of two
    /// explicitly selected Integer bounds becomes a named law application.
    /// Other arithmetic remains on the existing planner routes.
    fn try_integer_add_le_using(
        search_input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_integer_add_le_using");
        let [first, second] = premises else {
            return Ok(None);
        };
        if !matches!(
            search_input.goal(),
            Some(Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(_, _),
                true
            ))
        ) || !matches!(
            search_input.surface_goal(),
            Some(ClickProposition::Comparison {
                left: ContractExpression::Add(_, _),
                operator: ComparisonOperator::LessEqual,
                ..
            })
        ) {
            return Ok(None);
        }
        let Some((a, ComparisonOperator::LessEqual, b)) = integer_surface_ordered_parts(first)
        else {
            return Ok(None);
        };
        let Some((c, ComparisonOperator::LessEqual, d)) = integer_surface_ordered_parts(second)
        else {
            return Ok(None);
        };
        let candidate = search_input
            .driver()
            .apply_step(ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "click::integer::add_le".into(),
                    arguments: vec![a, b, c, d],
                },
                premises: premises.to_vec(),
            });
        Ok(attempt::candidate_outcome(candidate)?.filter(|proof| proof.is_complete()))
    }

    /// The fact `lower <u upper` as a proof that has it in that spelling,
    /// with the fact's surface and its two operands. The fact may be held
    /// as `upper >u lower`; it is then first restated the other way round by
    /// Integer arithmetic. Both lookups are exact: no fact is scanned.
    fn try_unsigned_strict_fact(
        search_input: &Proof<'a>,
        lower: &MachineTerm,
        upper: &MachineTerm,
        surface_fact: &dyn Fn(&Proposition) -> Option<ClickProposition>,
    ) -> Option<(
        Proof<'a>,
        ClickProposition,
        ContractExpression,
        ContractExpression,
    )> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_strict_fact");
        let less = Proposition::ConditionIs(
            ConditionTerm::unsigned_less_than(lower.clone(), upper.clone()),
            true,
        );
        if let Some(surface) = surface_fact(&less) {
            let (lower, upper) = surface_strict_parts(&surface)?;
            return Some((search_input.clone(), surface, lower, upper));
        }
        let greater = Proposition::ConditionIs(
            ConditionTerm::unsigned_greater_than(upper.clone(), lower.clone()),
            true,
        );
        let surface = surface_fact(&greater)?;
        let (lower, upper) = surface_strict_parts(&surface)?;
        let reversed = ClickProposition::Comparison {
            left: lower.clone(),
            operator: ComparisonOperator::LessThan,
            right: upper.clone(),
        };
        let proof = search_input
            .driver()
            .have_by_integer_arithmetic(reversed.clone(), vec![surface])
            .ok()?;
        Some((proof, reversed, lower, upper))
    }

    /// A small shared search combinator for structural proposition closure.
    /// Every candidate is accepted only through `apply_step`; `intro` is the
    /// binder move; disjunctions open a `have` for a smaller disjunct.
    ///
    /// A miss is `Ok(None)` and leaves `self` the unchanged authority. An
    /// error is a tooling failure such as an exceeded deadline; it must abort
    /// the enclosing search rather than read as one more rejection.
    pub(in crate::surface::proof) fn try_direct_logical_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_logical_closure");
        let mut scope = attempt::search_scope("direct logical closure");
        let mut budget = attempt::AttemptBudget::unbounded();
        let mut proof = search_input.clone();
        loop {
            if let Some(closed) =
                attempt::try_steps(&proof, &mut budget, direct_logical_candidates(proof.goal()))?
            {
                scope.succeed();
                return Ok(Some(closed));
            }
            // A disjunct that closes directly needs no search through the
            // other side's connected facts. Retain its ordinary `have` proof
            // and inject it with `known`, just as the general structural
            // search does. Recursion only visits smaller goal disjuncts; a
            // miss never invokes general solve.
            if matches!(proof.goal(), Some(Proposition::Or(_, _)))
                && let Some((left, right)) = proof
                    .surface_goal()
                    .and_then(|goal| surface_logical_children(goal, false))
            {
                for disjunct in [left, right] {
                    let Some(disjunct_scope) =
                        attempt::candidate_outcome(proof.driver().open_have(disjunct))?
                    else {
                        continue;
                    };
                    let Some(closed) = disjunct_scope.driver().try_direct_logical_closure()? else {
                        continue;
                    };
                    let Some(joined) = attempt::candidate_outcome(closed.join())? else {
                        continue;
                    };
                    if let Some(closed) =
                        attempt::candidate_outcome(joined.driver().apply_step(ProofStep::Known))?
                    {
                        scope.succeed();
                        return Ok(Some(closed));
                    }
                }
            }
            // A literal false premise needs no source search or arithmetic
            // derivation. Fixed-state goals can use the same explicit
            // contradiction as pure goals. Both spellings of the literal
            // are read: `false` holds, and `true` does not, as the infeasible
            // arm of a case split on a decided condition states it.
            if proof.goal().is_some()
                && proof
                    .facts()
                    .holds_contradiction_fact(&Proposition::ConditionIs(
                        ConditionTerm::Constant(false),
                        true,
                    ))
                && let Some(closed) = attempt::candidate_outcome(proof.driver().apply_step(
                    ProofStep::Contradiction(ClickProposition::Comparison {
                        // Machine literals cannot be shadowed by C parameters
                        // named `false` or `true` when the certificate is read.
                        left: ContractExpression::ProgramExpression(ProgramExpression::Value(
                            ProgramValue::UInt32(0u32.into()),
                        )),
                        operator: ComparisonOperator::Equal,
                        right: ContractExpression::ProgramExpression(ProgramExpression::Value(
                            ProgramValue::UInt32(1u32.into()),
                        )),
                    }),
                ))?
            {
                scope.succeed();
                return Ok(Some(closed));
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_discharged_consequent_closure(&(proof))?
            {
                scope.succeed();
                return Ok(Some(closed));
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_quantified_conjunct_projection_closure(
                    &(proof),
                )?
            {
                scope.succeed();
                return Ok(Some(closed));
            }
            // The kernel introduces only these outer connectives. An
            // atomic goal cannot take this step; constructing its rejection
            // would also capture an unused memory-history diagnostic.
            if !matches!(
                proof.goal(),
                Some(Proposition::Implies(..) | Proposition::ForAll { .. } | Proposition::Not(_))
            ) {
                return Ok(None);
            }
            // An antecedent that context-free normalization refutes, such as
            // `to_integer(i) == to_integer(i) + 1`, closes the implication
            // once introduced: `intro(); contradiction(A);`. Only the goal
            // is read.
            let refuted = match (proof.goal(), proof.surface_goal()) {
                (
                    Some(Proposition::Implies(antecedent, _)),
                    Some(ClickProposition::Implies(surface, _)),
                ) if normalization_refutes(antecedent) => Some(surface.as_ref().clone()),
                _ => None,
            };
            match attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Intro))? {
                Some(introduced) => proof = introduced,
                None => return Ok(None),
            }
            if let Some(antecedent) = refuted
                && let Some(closed) = attempt::candidate_outcome(
                    proof
                        .driver()
                        .apply_step(ProofStep::Contradiction(antecedent)),
                )?
            {
                scope.succeed();
                return Ok(Some(closed));
            }
        }
    }

    /// Modus ponens as a direct logical step: the goal is the consequent of
    /// an available implication (or chain) whose antecedents are exactly
    /// available, such as a call guarantee `left_result == 0 implies X`
    /// inside the branch whose path condition is `left_result == 0`. The
    /// indexed consequent lookup that the checked `extract` rule performs
    /// decides it. For an order comparison, search also tries its mirrored
    /// spelling with one additional probe. Expansion prints the selected
    /// `extract` and, if needed, `known`.
    pub(in crate::surface::proof) fn try_discharged_consequent_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_discharged_consequent_closure");
        let (Some(goal), Some(surface)) = (search_input.goal(), search_input.surface_goal()) else {
            return Ok(None);
        };
        if !search_input
            .facts()
            .contains_discharged_implication_consequent(goal)
        {
            // Implication extraction deliberately requires the consequent as
            // written. Select its mirrored order spelling in search, then
            // let the checked extraction and ordinary `known` close it.
            if let ClickProposition::Comparison {
                left,
                operator,
                right,
            } = surface
            {
                let mirrored_operator = match operator {
                    ComparisonOperator::LessThan => Some(ComparisonOperator::GreaterThan),
                    ComparisonOperator::LessEqual => Some(ComparisonOperator::GreaterEqual),
                    ComparisonOperator::GreaterThan => Some(ComparisonOperator::LessThan),
                    ComparisonOperator::GreaterEqual => Some(ComparisonOperator::LessEqual),
                    _ => None,
                };
                if let Some(operator) = mirrored_operator
                    && let Some(kernel) = mirrored_order_goal(goal)
                {
                    let mirrored = ClickProposition::Comparison {
                        left: right.clone(),
                        operator,
                        right: left.clone(),
                    };
                    if search_input
                        .facts()
                        .contains_discharged_implication_consequent(&kernel)
                        && let Some(extracted) = attempt::candidate_outcome(
                            search_input
                                .driver()
                                .apply_step(ProofStep::Extract(mirrored)),
                        )?
                    {
                        if extracted.focused_discharged() {
                            return Ok(Some(extracted));
                        }
                        return Ok(attempt::candidate_outcome(
                            extracted.driver().apply_step(ProofStep::Known),
                        )?
                        .filter(Proof::focused_discharged));
                    }
                }
            }
            return crate::kernel::search::ProofSearch::try_discharged_consequent_conjunct_closure(
                search_input,
                goal,
                surface,
            );
        }
        Ok(attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::Extract(surface.clone())),
        )?
        .filter(Proof::focused_discharged))
    }

    /// A goal that is one conjunct of a discharged implication's
    /// consequent, `c` from `a` and `a implies (b and c)`: `extract` the
    /// whole consequent, spelled as the implication fact is written, and
    /// then the goal, now a proper conjunct of an available fact. The
    /// implication is selected by one probe of the conjunct index
    /// (`ProofFacts::discharged_implication_containing`); both steps are
    /// checked as written, and expansion prints them.
    pub(in crate::surface::proof) fn try_discharged_consequent_conjunct_closure(
        search_input: &Proof<'a>,
        goal: &Proposition,
        surface: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_discharged_consequent_conjunct_closure");
        let Some((fact, whole)) = search_input.facts().discharged_implication_containing(goal)
        else {
            return Ok(None);
        };
        let Some(mut spelled) = search_input.spelled_goal_for_search(&fact) else {
            return Ok(None);
        };
        // A fact recorded at a state is spelled `at(selector, ...)`; its
        // consequent is read at the same state.
        let selector = match spelled {
            ClickProposition::At {
                selector,
                proposition,
            } => {
                spelled = *proposition;
                Some(selector)
            }
            _ => None,
        };
        let mut kernel = &fact;
        while let Proposition::Implies(_, consequent) = kernel {
            let ClickProposition::Implies(_, rest) = spelled else {
                return Ok(None);
            };
            spelled = *rest;
            kernel = consequent;
            if kernel == &whole {
                break;
            }
        }
        let spelled = match selector {
            Some(selector) => ClickProposition::At {
                selector,
                proposition: Box::new(spelled),
            },
            None => spelled,
        };
        let Some(extracted) = attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::Extract(spelled)),
        )?
        else {
            return Ok(None);
        };
        if extracted.is_complete() || extracted.focused_discharged() {
            return Ok(Some(extracted));
        }
        Ok(attempt::candidate_outcome(
            extracted
                .driver()
                .apply_step(ProofStep::Extract(surface.clone())),
        )?
        .filter(Proof::focused_discharged))
    }

    /// Weakening a guarded universal by dropping conjuncts of its conclusion:
    /// the goal `forall k { G implies A }` follows from an available
    /// `forall k { G implies A and B }` with the same binder and guards.
    /// The source is selected by one probe of the indexed conjunct
    /// projections (`ProofFacts::quantified_conjunct_projection_source`), so
    /// a universal goal no such fact concludes costs one lookup and no
    /// unrelated fact is visited. The proof is the explicit sequence
    /// `intro()` for the binder and each guard, `instantiate(F, k)` at the
    /// introduced binder, and `known()`; each step is checked as written
    /// and expansion prints it.
    pub(in crate::surface::proof) fn try_quantified_conjunct_projection_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_quantified_conjunct_projection_closure");
        let Some(goal @ Proposition::ForAll { body, .. }) = search_input.goal() else {
            return Ok(None);
        };
        let Some(source) = search_input
            .facts()
            .quantified_conjunct_projection_source(goal)
        else {
            return Ok(None);
        };
        let binder = match search_input.surface_goal() {
            Some(ClickProposition::ForAll { name, .. }) => name.clone(),
            Some(ClickProposition::RangeAll { item, .. }) => item.clone(),
            _ => return Ok(None),
        };
        let source = source.clone();
        let mut guards = 0usize;
        let mut conclusion = body.as_ref();
        while let Proposition::Implies(_, consequent) = conclusion {
            guards += 1;
            conclusion = consequent;
        }
        let Some(quantified) = crate::kernel::search::ProofSearch::resolve_solve_premises(
            search_input,
            std::slice::from_ref(&source),
            &[],
        )
        .and_then(|pairs| pairs.into_iter().next())
        .map(|(_, surface)| surface) else {
            return Ok(None);
        };
        let mut scope = attempt::search_scope("quantified conjunct projection");
        let steps = std::iter::repeat_n(ProofStep::Intro, guards + 1).chain([
            ProofStep::InstantiateUsing {
                quantified,
                argument: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    binder,
                )),
                premises: None,
            },
        ]);
        let mut proof = search_input.clone();
        for step in steps {
            let Some(next) = attempt::candidate_outcome(proof.driver().apply_step(step))? else {
                return Ok(None);
            };
            proof = next;
        }
        if !proof.focused_discharged() {
            let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
            else {
                return Ok(None);
            };
            proof = closed;
        }
        if !proof.focused_discharged() {
            return Ok(None);
        }
        scope.succeed();
        Ok(Some(proof))
    }

    /// Extends [`Self::try_direct_logical_closure`] through the goal's
    /// logical structure: a conjunction the direct candidates miss is split
    /// with the checked `both` operation and each conjunct is closed by this
    /// same closer, and `intro` may expose a conjunction to split. Only
    /// direct logical candidates close a leaf, so the search never selects
    /// premises, rewrites the goal, or instantiates ambient facts.
    ///
    /// Every move strictly removes one outer connective of the focused goal
    /// (`both` splits one conjunction, `intro` removes one binder), so the
    /// number of attempted candidates is linear in the goal's size. A miss
    /// anywhere declines the whole candidate and leaves `self` unchanged; a
    /// success is the explicit `both`/`intro`/direct-step sequence that
    /// expansion prints.
    pub(in crate::surface::proof) fn try_direct_structural_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure");
        let mut scope = attempt::search_scope("direct structural closure");
        let result = crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
            search_input,
            &mut |_| Ok(None),
        )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// A conjunction under implications or universals, every leaf of which
    /// the direct candidates close, is closed before any premise-selecting,
    /// rewriting, or instantiating strategy runs over the whole goal. Those
    /// strategies scale with the ambient facts rather than with the goal,
    /// and the implication closure that would eventually introduce the
    /// binders first searches for a refutation of each antecedent. A bare
    /// conjunction needs no such pass: it is split before those strategies
    /// run, and each conjunct is offered to the direct candidates first.
    pub(in crate::surface::proof) fn try_direct_structural_closure_under_binders(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_under_binders");
        if !conjunction_under_binders(search_input.goal()) {
            return Ok(None);
        }
        crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: direct structural",
            || crate::kernel::search::ProofSearch::try_direct_structural_closure(search_input),
        )
    }

    /// [`Self::try_direct_structural_closure`] with one more closer at a
    /// universal node the direct candidates miss: `quantified` is offered
    /// the universal whole before `intro` descends into it. The walk is
    /// otherwise the same goal-sized descent, so the extra work is one
    /// `quantified` attempt per universal node of the goal.
    pub(in crate::surface::proof) fn try_direct_structural_closure_with_quantified(
        search_input: &Proof<'a>,
        quantified: &mut dyn FnMut(&Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_with_quantified");
        let mut scope = attempt::search_scope("direct structural closure");
        let result = crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
            search_input,
            quantified,
        )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    pub(in crate::surface::proof) fn try_direct_structural_closure_inner(
        search_input: &Proof<'a>,
        quantified: &mut dyn FnMut(&Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_inner");
        crate::kernel::search::ProofSearch::try_direct_structural_closure_inner_impl(
            search_input,
            quantified,
        )
        .map_err(|error| search_input.attach_step_diagnostic(error))
    }

    pub(in crate::surface::proof) fn try_direct_structural_closure_inner_impl(
        search_input: &Proof<'a>,
        quantified: &mut dyn FnMut(&Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_inner_impl");
        check_verification_deadline()?;
        let mut budget = attempt::AttemptBudget::unbounded();
        if let Some(closed) = attempt::try_steps(
            search_input,
            &mut budget,
            direct_logical_candidates(search_input.goal()),
        )? {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_discharged_consequent_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(surfaces) = search_input.wide_conjunction_surfaces() {
            let mut proof = search_input.clone();
            for surface in surfaces {
                let scope = proof.driver().open_have(surface)?;
                let Some(closed) = (scope)
                    .driver()
                    .try_direct_structural_closure_with_quantified(quantified)?
                else {
                    return Ok(None);
                };
                proof = closed.join()?;
            }
            return attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known));
        }
        if matches!(search_input.goal(), Some(Proposition::And(_, _))) {
            let Some((split_proof, split, ids)) =
                attempt::candidate_outcome(search_input.split_focused_both())?
            else {
                return Ok(None);
            };
            let marker = split_proof.checkpoint();
            let Some(left) =
                crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
                    &(split_proof.focus_branch(ids[0])?),
                    quantified,
                )?
            else {
                return Ok(None);
            };
            let Some(right) =
                crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
                    &(left.focus_branch(ids[1])?),
                    quantified,
                )?
            else {
                return Ok(None);
            };
            return attempt::candidate_outcome(right.join_focused_both(&marker, split, ids));
        }
        if matches!(search_input.goal(), Some(Proposition::ForAll { .. }))
            && let Some(closed) = quantified(search_input)?
        {
            return Ok(Some(closed));
        }
        if matches!(search_input.goal(), Some(Proposition::Implies(_, _))) {
            let mut introduced = search_input.clone();
            while matches!(introduced.goal(), Some(Proposition::Implies(_, _))) {
                let Some(next) =
                    attempt::candidate_outcome(introduced.driver().apply_step(ProofStep::Intro))?
                else {
                    return Ok(None);
                };
                introduced = next;
            }
            return crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
                &(introduced),
                quantified,
            );
        }
        match attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Intro))? {
            Some(introduced) => {
                crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
                    &(introduced),
                    quantified,
                )
            }
            None => Ok(None),
        }
    }

    /// Searches the currently migrated `solve` vocabulary against this proof.
    ///
    /// Direct logical closers remain the cheap first choice. For a pure or
    /// fixed-state signed-order/equality derivation, the kernel-selected edge path
    /// is translated into a candidate made only of checked theorem
    /// applications, rewrites, and nested `have` scopes. The candidate
    /// advances this same `Proof`; no semantic result is produced before
    /// those proof steps have been accepted.
    pub(in crate::surface::proof) fn try_solve_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure");
        // solve reaches the same failing frame question through several of
        // its strategies and candidates; one closure attempt answers each
        // exact failed question once (`with_closure_failure_memo`).
        crate::kernel::search::proposition_search::with_solve_atomic_reduction_cache(|| {
            crate::kernel::with_closure_failure_memo(|| {
                crate::kernel::search::ProofSearch::try_solve_closure_strategies(search_input)
            })
        })
        .map_err(|error| search_input.attach_step_diagnostic(error))
    }

    /// Close a mathematical `Integer` bound goal with selected-premise arithmetic behind
    /// `solve`: refute the goal's negation from the facts connected to it and
    /// apply the resulting certificate as one ordinary checked step. Any
    /// miss leaves the proof unchanged.
    /// `solve` on an arithmetic goal: `arithmetic` from premises it selects
    /// itself, the facts connected to the goal and the type ranges of the
    /// machine values they observe, then the same with a machine order or
    /// equality carried to `Integer`, an equality proved from its two
    /// bounds, and `defined(a + b)` proved from the bounds of the exact
    /// result. Each returns at once on a goal it does not apply to.
    /// A subgoal of the arithmetic below, such as one bound of an equality
    /// or the definedness of an operand: a direct logical closure, else
    /// the same arithmetic, else the rest of `solve` with no arithmetic of
    /// its own, so a subgoal does not open subgoals again.
    pub(in crate::surface::proof) fn try_arithmetic_fact_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_arithmetic_fact_closure");
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_arithmetic_with_selected_premises(search_input)?
        {
            return Ok(Some(closed));
        }
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ArithmeticSubgoal) else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_solve_closure(search_input)
    }

    /// Arithmetic subgoals do not recursively select the same premises.
    /// Connected rewrites only retry arithmetic when the original comparison
    /// has a scalar match operand: selecting its arm exposes new arithmetic.
    pub(in crate::surface::proof) fn try_arithmetic_with_selected_premises(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_arithmetic_with_selected_premises");
        if (SolveFallbackScope::active(SolveFallback::ConnectedFacts)
            && !SolveFallbackScope::active(SolveFallback::MatchArithmetic))
            || SolveFallbackScope::active(SolveFallback::ArithmeticSubgoal)
        {
            return Ok(None);
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_selected_arithmetic(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_bridged_selected_arithmetic(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_machine_goal_through_integer(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_equality_by_bounds_early(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_disequality_by_selected_refutation(
                search_input,
            )?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_definedness_by_bounds(search_input)
    }

    /// The arithmetic `solve` tries last, once every other strategy has
    /// missed: a 64-bit equality through its `Integer` reading, whose type
    /// is known only after the reading is proved, and a native comparison
    /// through its `Integer` reading.
    pub(in crate::surface::proof) fn try_late_arithmetic_with_selected_premises(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_late_arithmetic_with_selected_premises");
        if (SolveFallbackScope::active(SolveFallback::ConnectedFacts)
            && !SolveFallbackScope::active(SolveFallback::MatchArithmetic))
            || SolveFallbackScope::active(SolveFallback::ArithmeticSubgoal)
        {
            return Ok(None);
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_wide_equality_through_integer(search_input)?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_native_goal_by_integer_reading(search_input)
    }

    /// A known different scalar value or a nonzero mathematical offset
    /// cannot satisfy this equality. Avoid spelling historical equalities
    /// and unfolding functions for that miss. An inconsistent context stays
    /// eligible for ordinary contradiction closure; this is not proof evidence.
    pub(in crate::surface::proof) fn scalar_offset_goal_is_refuted(
        search_input: &Proof<'a>,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("scalar_offset_goal_is_refuted");
        let Some(Proposition::ConditionIs(condition, wanted)) = search_input.goal() else {
            return false;
        };
        let assumptions = search_input.facts().assumptions();
        if let ConditionTerm::IntegerEqual(left, right) = condition {
            if !*wanted {
                return false;
            }
            fn offset_base(
                term: &crate::kernel::SharedIntegerTerm,
            ) -> Option<&crate::kernel::SharedIntegerTerm> {
                use crate::kernel::IntegerTerm;
                match term.as_ref() {
                    IntegerTerm::Add(base, delta) | IntegerTerm::Subtract(base, delta) if matches!(delta.as_ref(), IntegerTerm::Constant(value) if !value.is_zero()) => {
                        Some(base)
                    }
                    IntegerTerm::Add(delta, base) if matches!(delta.as_ref(), IntegerTerm::Constant(value) if !value.is_zero()) => {
                        Some(base)
                    }
                    _ => None,
                }
            }
            let same_value =
                |left: &crate::kernel::SharedIntegerTerm,
                 right: &crate::kernel::SharedIntegerTerm| {
                    left == right
                        || search_input.facts().contains(&Proposition::ConditionIs(
                            ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                            true,
                        ))
                        || search_input.facts().contains(&Proposition::ConditionIs(
                            ConditionTerm::IntegerEqual(right.clone(), left.clone()),
                            true,
                        ))
                };
            // Cancel ordinary Integer terms before asking about a single
            // remaining machine observation. A contract parameter pinned to
            // two cannot satisfy `to_integer(x) + 3 == to_integer(x) + to_integer(parameter)`.
            let affine_refuted = integer_affine_claim(
                search_input.goal().expect("an equality goal"),
            )
            .is_some_and(|claim| {
                if claim.terms.is_empty() {
                    return !claim.constant.is_zero();
                }
                let mut terms = claim.terms.iter();
                let Some((
                    crate::kernel::proof::integer_arithmetic::IntegerAffineAtom::Machine(machine),
                    coefficient,
                )) = terms.next()
                else {
                    return false;
                };
                if terms.next().is_some() || coefficient.abs() != BigInt::one() {
                    return false;
                }
                let required = -claim.constant / coefficient;
                let Some(constant) =
                    crate::kernel::machine_integer::range::constant_word(machine.ty(), &required)
                else {
                    return true;
                };
                assumptions.decide(&ConditionTerm::machine_compare(
                    machine.ty(),
                    CompareRelation::Equal,
                    machine.value().clone(),
                    constant,
                )) == Some(false)
            });
            let refuted = affine_refuted
                || incompatible_machine_offsets(left, right)
                || offset_base(right).is_some_and(|base| same_value(left, base))
                || offset_base(left).is_some_and(|base| same_value(right, base));
            if !refuted {
                return false;
            }
            let _scope = crate::kernel::assumptions::PureFactContextIdScope::enter(assumptions);
            return !assumptions.is_inconsistent();
        }
        let (left, right) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } => (left, right),
            _ => return false,
        };
        if *wanted
            && matches!(
                condition,
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                }
            )
        {
            // Adding or subtracting a nonzero word has no fixed point,
            // including at unsigned wraparound. A retained equality names
            // the same base without spelling unrelated historical premises.
            fn offset_base(term: &MachineTerm) -> Option<&MachineTerm> {
                match term {
                    binary_term!(Int32, Add, base, delta)
                    | binary_term!(Int32, Subtract, base, delta)
                        if matches!(delta.as_ref(), bits32_constant!(value) if constant_u32(*value) != 0) =>
                    {
                        Some(base)
                    }
                    _ => None,
                }
            }
            let same_value = |left: &MachineTerm, right: &MachineTerm| {
                left == right
                    || search_input.facts().contains(&Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(left.clone()),
                            right: Box::new(right.clone()),
                        },
                        true,
                    ))
                    || search_input.facts().contains(&Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(right.clone()),
                            right: Box::new(left.clone()),
                        },
                        true,
                    ))
            };
            if offset_base(right).is_some_and(|base| same_value(left, base))
                || offset_base(left).is_some_and(|base| same_value(right, base))
            {
                return !assumptions.is_inconsistent();
            }
        }
        false
    }

    pub(in crate::surface::proof) fn scalar_equality_goal_is_refuted(
        search_input: &Proof<'a>,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("scalar_equality_goal_is_refuted");
        if crate::kernel::search::ProofSearch::scalar_offset_goal_is_refuted(search_input) {
            return true;
        }
        let Some(Proposition::ConditionIs(condition, wanted)) = search_input.goal() else {
            return false;
        };
        let (left, right) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } => (left, right),
            _ => return false,
        };
        let assumptions = search_input.facts().assumptions();
        let literal = |term: &MachineTerm| matches!(term, bits32_constant!(_) | int64_constant!(_));
        if !literal(left) && !literal(right) {
            return false;
        }
        !assumptions.is_inconsistent()
            && assumptions
                .decide(condition)
                .is_some_and(|known| known != *wanted)
    }

    pub(in crate::surface::proof) fn try_selected_arithmetic(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_arithmetic");
        crate::kernel::search::ProofSearch::selected_arithmetic(search_input, true, &[])
    }

    /// Close a native comparison of exact observations, such as `a < 100`
    /// for an `int`, by proving its Integer reading `to_integer(a) < 100`
    /// with selected-premise arithmetic. The Integer fact files its native comparison, so
    /// the goal is then an available fact.
    pub(in crate::surface::proof) fn try_native_goal_by_integer_reading(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_native_goal_by_integer_reading");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        // A plain 32-bit equality reads as an Integer equality, which
        // simplex proves only from its two bounds; its Integer spelling would
        // be filed as the same native goal.
        if matches!(
            goal,
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                },
                true
            )
        ) {
            return crate::kernel::search::ProofSearch::equality_by_bounds(search_input, true);
        }
        let readings =
            crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
                goal,
            );
        if readings.is_empty() {
            return Ok(None);
        }
        let written = written_integer_observations(std::iter::once(surface_goal));
        for reading in readings {
            let Some(spelled) = search_input.spell_integer_comparison(&reading, &written) else {
                continue;
            };
            let Ok(scope) = search_input.driver().open_have(spelled) else {
                continue;
            };
            let Some(closed) = (scope).driver().try_selected_arithmetic()? else {
                continue;
            };
            let Ok(proof) = closed.join() else {
                continue;
            };
            if let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// An operation identity has a direct certificate from its ordinary
    /// domain. Try it in the written read names before exploring a stored-
    /// value comparison form, whose inner operations may have older names.
    pub(in crate::surface::proof) fn try_direct_operation_identity(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_operation_identity");
        let (
            Some(goal @ Proposition::ConditionIs(ConditionTerm::IntegerEqual(..), true)),
            Some(surface),
        ) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        let direct = operation_identities(machine_observations(goal, &[]));
        if !direct.iter().any(|(_, _, identity)| identity == goal) {
            return Ok(None);
        }
        let written = written_integer_observations(std::iter::once(surface));
        let identities = direct.iter().collect::<Vec<_>>();
        if let Ok((proof, _)) = crate::kernel::search::ProofSearch::prove_operation_identities(
            search_input,
            &identities,
            &written,
            None,
        )? {
            return attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known));
        }
        Ok(None)
    }

    /// Refute the goal's negation from the connected facts, then from them
    /// and the type ranges of their machine observations, then, when
    /// `identities`, also from in-range machine `+` and `-` identities.
    ///
    /// `spelled` gives the source spelling of facts the caller just
    /// established, which a cited premise uses before its resolved one.
    pub(in crate::surface::proof) fn selected_arithmetic(
        search_input: &Proof<'a>,
        identities: bool,
        spelled: &[(Proposition, ClickProposition)],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_arithmetic");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        // A native goal is refuted as its Integer reading, so the certificate
        // spells it observed: `r <= 5` as `to_integer(r) <= 5`.
        let observed_goal = observed_native_surface_comparison(goal, surface_goal);
        let surface_goal = &observed_goal;
        if identities
            && let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_operation_identity(search_input)?
        {
            return Ok(Some(closed));
        }
        if crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let Some(candidates) =
            crate::kernel::search::proposition_search::arithmetic_connected_premises(
                search_input.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        check_verification_deadline()?;
        let plan = |premises: &[Proposition], ranges: &[crate::kernel::IntegerTerm]| {
            crate::instrumentation::measure_operation(
                "surface",
                "solve arithmetic",
                "solve arithmetic: integer refutation",
                || refute_integer_goal(goal, premises, ranges),
            )
        };
        // Native comparisons read as Integer comparisons, and machine type
        // ranges, are added only when the Integer facts alone leave a
        // counterexample, so a proof that needs neither keeps its
        // certificate.
        // A native candidate reads as an Integer fact, so the first plan may
        // cite one with no source spelling (a derived low-word bound); the
        // extended search below then drops it and plans again.
        // The planner reads a native comparison as an Integer one, but it
        // cites native facts only through their Integer readings,
        // which it spells by the native fact's own written operands; the
        // native candidates themselves stay out.
        let native = |premise: &Proposition| {
            !crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
                premise,
            )
            .is_empty()
        };
        // The first plan reads only the native facts that observe a value
        // the goal does; the extended search below reads the rest.
        let goal_values =
            crate::kernel::proof::integer_arithmetic::integer_affine_machine_values(goal)
                .into_iter()
                .map(|value| value.id())
                .collect::<std::collections::HashSet<_>>();
        let observes_goal = |premise: &Proposition| {
            crate::kernel::proof::integer_arithmetic::integer_affine_machine_values(premise)
                .iter()
                .any(|value| goal_values.contains(&value.id()))
        };
        let near = candidates
            .iter()
            .filter(|premise| !native(premise) || observes_goal(premise))
            .cloned()
            .collect::<Vec<_>>();
        let mut integer_candidates = with_native_comparisons_as_integer(&near);
        integer_candidates.retain(|premise| !native(premise));

        let spellings = SpellingCache::default();
        let first = match plan(&integer_candidates, &[]) {
            IntegerRefutation::Proved {
                certificate,
                premises,
            } => match search_input.spell_refutation(
                &certificate,
                &premises,
                &candidates,
                spelled,
                surface_goal,
                &spellings,
            ) {
                Spelling::Spelled(pairs, ranges) => Some((certificate, pairs, ranges)),
                Spelling::UnspelledReading(_) => None,
                _ => return Ok(None),
            },
            IntegerRefutation::Counterexample(_) => None,
            _ => return Ok(None),
        };
        let (certificate, pairs, ranges) = match first {
            Some(spelled) => spelled,
            None => {
                let mut extended = with_native_comparisons_as_integer(&candidates);
                extended.retain(|premise| !native(premise));
                let mut ranges = machine_observations(goal, &extended);
                // A reading or a range with no source spelling cannot be
                // cited; drop it and plan again, a bounded number of times.
                let mut attempts = 0;
                loop {
                    match plan(&extended, &ranges) {
                        IntegerRefutation::Proved {
                            certificate,
                            premises,
                        } if !ranges.is_empty() || extended.len() > integer_candidates.len() => {
                            let outcome = search_input.spell_refutation(
                                &certificate,
                                &premises,
                                &candidates,
                                spelled,
                                surface_goal,
                                &spellings,
                            );
                            match outcome {
                                Spelling::Spelled(pairs, spelled_ranges) => {
                                    break (certificate, pairs, spelled_ranges);
                                }
                                Spelling::UnspelledReading(reading) if attempts < 8 => {
                                    extended.retain(|premise| premise != &reading);
                                }
                                Spelling::UnspelledRange(value) if attempts < 8 => {
                                    ranges.retain(|range| range != &value);
                                }
                                Spelling::UnspelledBound => return Ok(None),
                                _ => return Ok(None),
                            }
                            attempts += 1;
                        }
                        IntegerRefutation::Counterexample(_) if identities => {
                            return crate::kernel::search::ProofSearch::try_operation_identity_closure(search_input,
                                goal,
                                surface_goal,
                                &extended,
                                &candidates,
                            );
                        }
                        _ => return Ok(None),
                    }
                }
            }
        };
        let Some(surface) = integer_plan_to_surface_certificate_with_ranges(
            &certificate,
            &pairs,
            surface_goal,
            &ranges,
        ) else {
            return Ok(None);
        };
        attempt::candidate_outcome(search_input.driver().apply_step(
            ProofStep::ArithmeticCertificate(ArithmeticCertificate::integer(surface)),
        ))
    }

    /// Close the goal with in-range machine `+` and `-` identities. A
    /// refutation that may assume `to_integer(a op b) == to_integer(a) op
    /// to_integer(b)` for the operations among the facts' and goal's
    /// machine observations selects the identities it needs. Each is then
    /// proved: its two type-range bounds by selected-premise arithmetic, the identity by
    /// `integer_operation_identity`, and the goal by selected-premise arithmetic from the
    /// facts and identities. An operand's identity is proved before its
    /// operation's, so the bounds of `a + b + c` read the established
    /// `to_integer(a + b) == to_integer(a) + to_integer(b)`.
    pub(in crate::surface::proof) fn try_operation_identity_closure(
        search_input: &Proof<'a>,
        goal: &Proposition,
        surface_goal: &ClickProposition,
        candidates: &[Proposition],
        written_facts: &[Proposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_operation_identity_closure");
        let mut identities = operation_identities(machine_observations(goal, candidates));
        // A refutation may cite an identity that nothing written spells, or
        // one whose spelling proves a different identity, such as the signed
        // reading of an unsigned narrowing's word, which spells as the
        // unsigned cast. That identity is dropped and the refutation planned
        // again, so each identity costs at most one more plan.
        loop {
            if identities.is_empty() {
                return Ok(None);
            }
            check_verification_deadline()?;
            let mut assumed = candidates.to_vec();
            assumed.extend(identities.iter().map(|(_, _, identity)| identity.clone()));
            let ranges = machine_observations(goal, &assumed);
            let IntegerRefutation::Proved { premises, .. } =
                crate::instrumentation::measure_operation(
                    "surface",
                    "solve arithmetic",
                    "solve arithmetic: integer refutation with operation identities",
                    || refute_integer_goal(goal, &assumed, &ranges),
                )
            else {
                return Ok(None);
            };
            let used: Vec<_> = identities
                .iter()
                .filter(|(_, _, identity)| premises.contains(identity))
                .collect();
            if used.is_empty() {
                return Ok(None);
            }
            // Spell each identity from the goal and the facts the refutation
            // cited.
            let mut surfaces = vec![surface_goal.clone()];
            for premise in &premises {
                if identities
                    .iter()
                    .any(|(_, _, identity)| identity == premise)
                {
                    continue;
                }
                // A native comparison read as an Integer one has no spelling
                // of its own; the goal and the other facts spell the
                // identities.
                if let Some((_, surface)) =
                    crate::kernel::search::ProofSearch::resolve_solve_premises(
                        search_input,
                        std::slice::from_ref(premise),
                        &[],
                    )
                    .and_then(|mut spelled| spelled.pop())
                {
                    surfaces.push(surface);
                }
            }
            let mut written = written_integer_observations(surfaces.iter());
            // An operand the cited facts do not spell, such as a capacity the
            // refutation bounds only through a native comparison, may still
            // be spelled by another connected fact as written, such as the
            // native `capacity == used + available` behind a cited Integer
            // reading. Look there only on a miss.
            let spells = |written: &[ContractExpression],
                          (observed, value, _): &OperationIdentity| {
                let Some(operands) = identity_operands(value) else {
                    return false;
                };
                std::iter::once(observed).chain(operands).all(|term| {
                    search_input
                        .spell_integer_observation(term, written)
                        .is_some()
                })
            };
            if !used.iter().all(|identity| spells(&written, identity)) {
                for premise in written_facts.iter().take(MAX_SOLVER_SPELLING_FACTS) {
                    if let Some((_, surface)) =
                        crate::kernel::search::ProofSearch::resolve_solve_premises(
                            search_input,
                            std::slice::from_ref(premise),
                            &[],
                        )
                        .and_then(|mut spelled| spelled.pop())
                    {
                        surfaces.push(surface);
                    }
                }
                written = written_integer_observations(surfaces.iter());
            }
            if let Some(unspelled) = used.iter().find(|identity| !spells(&written, identity)) {
                let unspelled = unspelled.2.clone();
                identities.retain(|(_, _, identity)| identity != &unspelled);
                continue;
            }
            match crate::kernel::search::ProofSearch::prove_operation_identities(
                search_input,
                &used,
                &written,
                None,
            )? {
                Ok((proof, established)) => {
                    // A cited product whose bounds missed is left out; plan
                    // again without it, as for any identity that missed.
                    if let Some((_, _, skipped)) = used.iter().find(|(_, _, identity)| {
                        !established.iter().any(|(fact, _)| fact == identity)
                    }) {
                        let skipped = skipped.clone();
                        identities.retain(|(_, _, identity)| identity != &skipped);
                        continue;
                    }
                    return crate::kernel::search::ProofSearch::selected_arithmetic(
                        &(proof),
                        false,
                        &established,
                    );
                }
                Err(failed) => identities.retain(|(_, _, identity)| identity != &failed),
            }
        }
    }

    /// Prove each of `identities`, `to_integer(a op b) == to_integer(a) op
    /// to_integer(b)` or `to_integer((T)x) == to_integer(x)`, spelled from
    /// `written`: its two type-range bounds by selected-premise arithmetic, then the identity
    /// by `integer_operation_identity` or `integer_cast_identity`. Each
    /// operand was found after its operation, so the reverse order proves
    /// the innermost identity first. Returns the proof with the identities
    /// established and their spellings, or the identity that missed.
    pub(in crate::surface::proof) fn prove_operation_identities(
        search_input: &Proof<'a>,
        identities: &[&OperationIdentity],
        written: &[ContractExpression],
        listed: Option<&[ClickProposition]>,
    ) -> Result<Result<(Proof<'a>, Vec<(Proposition, ClickProposition)>), Proposition>, ClickError>
    {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prove_operation_identities");
        use crate::kernel::IntegerTerm;
        let mut proof = search_input.clone();
        let mut established: Vec<(Proposition, ClickProposition)> = Vec::new();
        'identities: for (observed, value, failed) in identities.iter().rev().copied() {
            let IntegerTerm::Machine(machine) = observed else {
                return Ok(Err(failed.clone()));
            };
            // A product whose bounds miss is left out rather than failing the
            // others: before products were planned its identity was never
            // proved, and an identity over it still needs its own bounds.
            // A caller that cited it sees it missing from `established`.
            let product = matches!(value, IntegerTerm::Multiply(left, right)
                if left.as_const().is_none() && right.as_const().is_none());
            let before_product = proof.clone();
            let Some(spelled_observed) = search_input.spell_integer_observation(observed, written)
            else {
                return Ok(Err(failed.clone()));
            };
            let conversion =
                crate::kernel::machine_integer::conversion::integer_conversion(observed).is_some();
            let cast = conversion || matches!(value, IntegerTerm::Machine(_));
            let spelled_value = match value {
                // The conversion's operand as the observation itself writes
                // it, `E` of `to_integer(to_T(E))`: lowering is fact-stable,
                // so `E` lowers to the operand `z`, and the kernel checks it.
                _ if conversion => {
                    let ContractExpression::Call { name, arguments } = &spelled_observed else {
                        return Ok(Err(failed.clone()));
                    };
                    let [
                        ContractExpression::Call {
                            arguments: converted,
                            ..
                        },
                    ] = arguments.as_slice()
                    else {
                        return Ok(Err(failed.clone()));
                    };
                    let [operand] = converted.as_slice() else {
                        return Ok(Err(failed.clone()));
                    };
                    if name != "to_integer" {
                        return Ok(Err(failed.clone()));
                    }
                    operand.clone()
                }
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right) => {
                    let (Some(spelled_left), Some(spelled_right)) = (
                        search_input.spell_integer_observation(left, written),
                        search_input.spell_integer_observation(right, written),
                    ) else {
                        return Ok(Err(failed.clone()));
                    };
                    let (left, right) = (Box::new(spelled_left), Box::new(spelled_right));
                    match value {
                        IntegerTerm::Subtract(..) => ContractExpression::Subtract(left, right),
                        IntegerTerm::Multiply(..) => ContractExpression::Multiply(left, right),
                        _ => ContractExpression::Add(left, right),
                    }
                }
                IntegerTerm::Machine(_) => {
                    let Some(spelled) = search_input.spell_integer_observation(value, written)
                    else {
                        return Ok(Err(failed.clone()));
                    };
                    spelled
                }
                _ => return Ok(Err(failed.clone())),
            };
            // The identity is checked at the format of the observation's
            // value reading (rule W).
            let (min, max) = match observed.value_read() {
                IntegerTerm::Machine(read) => read.ty().format().bounds(),
                _ => machine.ty().format().bounds(),
            };
            let (lower, upper) = (
                ClickProposition::Comparison {
                    left: surface_signed_integer_literal(&min),
                    operator: ComparisonOperator::LessEqual,
                    right: spelled_value.clone(),
                },
                ClickProposition::Comparison {
                    left: spelled_value.clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: surface_signed_integer_literal(&max),
                },
            );
            for bound in [&lower, &upper] {
                let scope = proof.driver().open_have(bound.clone())?;
                let closed = if let Some(listed) = listed {
                    let mut premises = listed.to_vec();
                    premises.extend(established.iter().map(|(_, surface)| surface.clone()));
                    scope
                        .driver()
                        .apply_step(ProofStep::ArithmeticUsing(premises))
                        .ok()
                } else if let Some(closed) = (scope).driver().try_direct_logical_closure()? {
                    // A complete arithmetic domain already contains these
                    // ordinary bounds. Use the available fact before a
                    // refutation search, which excludes the exact goal.
                    Some(closed)
                } else {
                    scope
                        .driver()
                        .try_selected_arithmetic_without_identities()?
                };
                let closed = match closed {
                    Some(closed) => Some(closed.join()?),
                    None if product => {
                        let IntegerTerm::Multiply(left, right) = value else {
                            unreachable!("a product identity's value is a product")
                        };
                        let ContractExpression::Multiply(spelled_left, spelled_right) =
                            &spelled_value
                        else {
                            unreachable!("a product is spelled as one")
                        };
                        let (target, lower) = if std::ptr::eq(bound, &lower) {
                            (&min, true)
                        } else {
                            (&max, false)
                        };
                        crate::kernel::search::ProofSearch::prove_product_bound_from_ranges(
                            &proof,
                            [(left, spelled_left), (right, spelled_right)],
                            bound,
                            target,
                            lower,
                        )?
                    }
                    None => None,
                };
                let Some(closed) = closed else {
                    if product {
                        proof = before_product;
                        continue 'identities;
                    }
                    return Ok(Err(failed.clone()));
                };
                proof = closed;
                established.extend(
                    proof
                        .added_facts()
                        .iter()
                        .map(|fact| (fact.clone(), bound.clone())),
                );
            }
            let identity = ClickProposition::Comparison {
                left: spelled_observed,
                operator: ComparisonOperator::Equal,
                right: spelled_value,
            };
            let identity_surface = identity.clone();
            let scope = proof.driver().open_have(identity.clone())?;
            let step = ProofStep::ArithmeticCertificate(ArithmeticCertificate::special(
                SpecialArithmeticCertificate {
                    premises: vec![lower, upper],
                    nodes: vec![if cast {
                        SpecialArithmeticNode::IntegerCastIdentity {
                            bounds: vec![0, 1],
                            result: identity,
                        }
                    } else {
                        SpecialArithmeticNode::IntegerOperationIdentity {
                            bounds: vec![0, 1],
                            result: identity,
                        }
                    }],
                    conclusion: 0,
                },
            ));
            let Ok(closed) = scope.driver().apply_step(step) else {
                return Ok(Err(failed.clone()));
            };
            proof = closed.join()?;
            established.extend(
                proof
                    .added_facts()
                    .iter()
                    .map(|fact| (fact.clone(), identity_surface.clone())),
            );
        }
        Ok(Ok((proof, established)))
    }

    /// A bound `target <= a * b` (`lower`) or `a * b <= target` on a product
    /// of two machine observations, from the operands' type ranges by
    /// `integer_product_bounds`: each operand's two range bounds as a
    /// `have`, then the bound by the certificate over those four premises,
    /// the shape `click expand` writes. The four corner products of the
    /// ranges are compared with `target` first, so a range that cannot give
    /// the bound costs no step. Reads no fact and no other premise: the work
    /// is the two operands' formats and four constant products.
    pub(in crate::surface::proof) fn prove_product_bound_from_ranges(
        search_input: &Proof<'a>,
        operands: [(&crate::kernel::SharedIntegerTerm, &Box<ContractExpression>); 2],
        bound: &ClickProposition,
        target: &num_bigint::BigInt,
        lower: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prove_product_bound_from_ranges");
        use crate::kernel::IntegerTerm;
        let mut ranges = Vec::with_capacity(2);
        for (operand, _) in &operands {
            let IntegerTerm::Machine(read) = operand.value_read() else {
                return Ok(None);
            };
            ranges.push(read.ty().format().bounds());
        }
        let follows = [&ranges[0].0, &ranges[0].1].into_iter().all(|left| {
            [&ranges[1].0, &ranges[1].1].into_iter().all(|right| {
                let corner = left * right;
                if lower {
                    target <= &corner
                } else {
                    &corner <= target
                }
            })
        });
        if !follows {
            return Ok(None);
        }
        let mut proof = search_input.clone();
        let mut premises = Vec::with_capacity(4);
        for ((_, spelled), (min, max)) in operands.iter().zip(&ranges) {
            for range_bound in [
                ClickProposition::Comparison {
                    left: surface_signed_integer_literal(min),
                    operator: ComparisonOperator::LessEqual,
                    right: spelled.as_ref().clone(),
                },
                ClickProposition::Comparison {
                    left: spelled.as_ref().clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: surface_signed_integer_literal(max),
                },
            ] {
                let scope = proof.driver().open_have(range_bound.clone())?;
                let closed = match scope.driver().try_direct_logical_closure()? {
                    Some(closed) => Some(closed),
                    None => scope
                        .driver()
                        .try_selected_arithmetic_without_identities()?,
                };
                let Some(closed) = closed else {
                    return Ok(None);
                };
                proof = closed.join()?;
                premises.push(range_bound);
            }
        }
        let scope = proof.driver().open_have(bound.clone())?;
        let step = ProofStep::ArithmeticCertificate(ArithmeticCertificate::special(
            SpecialArithmeticCertificate {
                premises,
                nodes: vec![SpecialArithmeticNode::IntegerProductBounds {
                    bounds: vec![0, 1, 2, 3],
                    result: bound.clone(),
                }],
                conclusion: 0,
            },
        ));
        let Ok(closed) = scope.driver().apply_step(step) else {
            return Ok(None);
        };
        Ok(Some(closed.join()?))
    }

    /// Establish the in-range machine `+` and `-` identities of the
    /// operations this goal observes, and those of their operands, before
    /// an equality is split into its two bounds, so both bounds read them
    /// rather than each proving them inside its own `have`. Only the goal's
    /// own spelling is read; an identity it cannot spell, or a bound the
    /// arithmetic misses, leaves the proof unchanged.
    pub(in crate::surface::proof) fn with_goal_operation_identities(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("with_goal_operation_identities");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let identities = operation_identities(machine_observations(goal, &[]))
            .into_iter()
            .filter(|(_, _, identity)| !search_input.facts().contains(identity))
            .collect::<Vec<_>>();
        if identities.is_empty() {
            return Ok(None);
        }
        check_verification_deadline()?;
        let written = written_integer_observations(std::iter::once(surface_goal));
        let identities = identities.iter().collect::<Vec<_>>();
        Ok(
            crate::kernel::search::ProofSearch::prove_operation_identities(
                search_input,
                &identities,
                &written,
                None,
            )?
            .ok()
            .map(|(proof, _)| proof),
        )
    }

    pub(in crate::surface::proof) fn try_flat_solve_conjunction(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_flat_solve_conjunction");
        let Some(surfaces) = search_input.wide_conjunction_surfaces() else {
            return Ok(None);
        };
        let mut proof = search_input.clone();
        for surface in surfaces {
            let scope = proof.driver().open_have(surface)?;
            let Some(closed) = (scope)
                .driver()
                .try_solve_closure_with_surfaces(introduced_surfaces)?
            else {
                return Ok(None);
            };
            proof = closed.join()?;
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// Try the explicit zero witness for a machine-integer existential.
    /// The recursive solve sees its instantiated body, not the existential.
    pub(in crate::surface::proof) fn try_zero_witness_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_zero_witness_closure");
        let Some(ClickProposition::Exists {
            click_type: ClickType::Program(crate::languages::interface::InterfaceType::Int32),
            name,
            written_name,
            ..
        }) = search_input.surface_goal()
        else {
            return Ok(None);
        };
        let Some(witnessed) = attempt::candidate_outcome(search_input.driver().apply_step(
            ProofStep::Witness(ProofWitness::single(
                written_name.as_ref().unwrap_or(name).clone(),
                ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(MachineTerm::constant(0)),
                )),
            )),
        ))?
        else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_solve_closure(&witnessed)
    }

    /// Reuse a witness from a function-entry existential, then transport its
    /// leaves through the effect-free prefix. This is an ordinary solve
    /// strategy; it receives no call-site obligation or private premise list.
    pub(in crate::surface::proof) fn try_entry_existential_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_entry_existential_closure");
        if !matches!(
            search_input.surface_goal(),
            Some(ClickProposition::Exists { .. })
        ) {
            return Ok(None);
        }
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = search_input.execution() else {
            return Ok(None);
        };
        if !execution.core.effect_facts.is_empty() {
            return Ok(None);
        }
        let Some(owner) = &context.constants.caller_source_owner else {
            return Ok(None);
        };
        for outer_ordinal in 0..context.function_block.requires().len() {
            check_verification_deadline()?;
            let source_id = RequirementSourceId {
                owner: owner.clone(),
                outer_ordinal,
            };
            let Some(selection) = context
                .constants
                .caller_requirement_index
                .lookup_source_requirement(&source_id)
            else {
                continue;
            };
            let ClickProposition::PredicateCall { name, .. } = &selection.source_proposition else {
                continue;
            };
            let proof = if search_input.active_unfolded_predicates().contains(name) {
                search_input.clone()
            } else {
                let Some(unfolded) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_step(ProofStep::UnfoldPredicate(name.clone())),
                )?
                else {
                    continue;
                };
                unfolded
            };
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_selected_entry_existential_closure(
                    &proof, &selection,
                )?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    pub(in crate::surface::proof) fn try_selected_entry_existential_closure(
        search_input: &Proof<'a>,
        selection: &CallerRequirementSelection,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_entry_existential_closure");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let unfolded = unfold_structural_invariant_proposition(
            context.spec_definitions.predicates,
            &selection.source_proposition,
            &search_input.active_unfolded_predicates(),
        )
        .map_err(|message| search_input.step_error(message))?;
        let ClickProposition::Exists {
            click_type,
            name: source_name,
            body,
            ..
        } = unfolded
        else {
            return Ok(None);
        };
        let candidate_names = std::iter::once(source_name.clone()).chain((0..4096).map(|suffix| {
            format!(
                "{}_witness_{}_{suffix}",
                source_name, selection.source_id.outer_ordinal
            )
        }));
        let Some(choice_name) = candidate_names.into_iter().find(|candidate| {
            search_input.local_binding(candidate).is_none()
                && !context
                    .parsed_function
                    .parameters()
                    .iter()
                    .any(|parameter| parameter.name() == candidate)
                && search_input
                    .execution()
                    .is_none_or(|execution| !execution.core.state.locals().contains_name(candidate))
        }) else {
            return Ok(None);
        };
        let replacement = match &click_type {
            ClickType::Resource => return Ok(None),
            ClickType::Integer | ClickType::Algebraic(_) => {
                ContractExpression::Binding(choice_name.clone())
            }
            ClickType::Program(_) | ClickType::CObjectPointer { .. } => {
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    choice_name.clone(),
                ))
            }
            ClickType::Parameter(_) => return Ok(None),
        };
        let body =
            substitute_click_proposition(&body, &BTreeMap::from([(source_name, replacement)]))
                .map_err(|message| search_input.step_error(message))?;
        let source = ClickProposition::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(ClickProposition::Exists {
                click_type: click_type.clone(),
                name: choice_name.clone(),
                written_name: None,
                body: Box::new(body),
            }),
        };
        let Some(chosen) = attempt::candidate_outcome(search_input.driver().apply_step(
            ProofStep::LetSatisfy(ProofLetSatisfy {
                bindings: vec![(choice_name.clone(), click_type)],
                proposition: source,
            }),
        ))?
        else {
            return Ok(None);
        };
        let Some(projection) = chosen
            .execution()
            .and_then(|execution| execution.presentation.existential_projection.as_ref())
        else {
            return Ok(None);
        };
        if chosen.focused_discharged() {
            return Ok(Some(chosen));
        }
        let source_leaves = projection
            .leaves
            .iter()
            .map(|leaf| leaf.surface.clone())
            .collect::<Vec<_>>();
        let Some(ClickProposition::Exists {
            name, written_name, ..
        }) = chosen.surface_goal()
        else {
            return Ok(None);
        };
        let witness_name = written_name.as_ref().unwrap_or(name).clone();
        let Some(witnessed) = attempt::candidate_outcome(chosen.driver().apply_step(
            ProofStep::Witness(ProofWitness::single(
                witness_name,
                ContractExpression::ProgramExpression(ProgramExpression::Variable(choice_name)),
            )),
        ))?
        else {
            return Ok(None);
        };
        let mut proof = witnessed;
        for source in &source_leaves {
            // At the entry state the leaves already close the goal.
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
            let Some(extracted) = attempt::candidate_outcome(
                proof
                    .driver()
                    .apply_step(ProofStep::Extract(source.clone())),
            )?
            else {
                return Ok(None);
            };
            proof = extracted;
        }
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        // The leaves hold at function entry. A conjunct this frontier does
        // not state exactly, such as a wide range or a universal over reads,
        // is carried here by one explicit transport of its entry form.
        let Some(goal) = proof.surface_goal().cloned() else {
            return Ok(None);
        };
        let mut conjuncts = Vec::new();
        let mut pending = vec![goal];
        while let Some(proposition) = pending.pop() {
            match proposition {
                ClickProposition::And(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
                conjunct => conjuncts.push(conjunct),
            }
        }
        for conjunct in conjuncts {
            check_verification_deadline()?;
            let Ok(lowered) =
                proof.lower_surface_proposition(&conjunct, "caller requirement conjunct")
            else {
                return Ok(None);
            };
            if proof.facts().pure_known_available(&lowered) {
                continue;
            }
            let Some(carried) =
                crate::kernel::search::ProofSearch::try_carry_entry_conjunct(&(proof), &conjunct)?
            else {
                return Ok(None);
            };
            proof = carried;
        }
        crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(proof),
            &source_leaves,
        )
    }

    /// Proves `conjunct` at this frontier from its function-entry form: a
    /// plain fact by one `transport`, and a guarded universal by introducing
    /// its binder and guard, instantiating the entry universal there, and
    /// transporting that one conclusion. Every step is the checked operation.
    pub(in crate::surface::proof) fn try_carry_entry_conjunct(
        search_input: &Proof<'a>,
        conjunct: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_carry_entry_conjunct");
        let entry = |proposition: &ClickProposition| ClickProposition::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(proposition.clone()),
        };
        let transport = |proposition: &ClickProposition| ProofStep::TransportUsing {
            source: entry(proposition),
            target: proposition.clone(),
            premises: vec![entry(proposition)],
        };
        let steps = match conjunct {
            ClickProposition::ForAll { name, body, .. } => {
                let ClickProposition::Implies(guard, consequent) = body.as_ref() else {
                    return Ok(None);
                };
                vec![
                    ProofStep::IntroAs(name.clone()),
                    ProofStep::Intro,
                    ProofStep::InstantiateUsing {
                        quantified: entry(conjunct),
                        argument: ContractExpression::ProgramExpression(
                            ProgramExpression::Variable(name.clone()),
                        ),
                        premises: Some(vec![guard.as_ref().clone()]),
                    },
                    transport(consequent),
                ]
            }
            _ => vec![transport(conjunct)],
        };
        let Some(mut scope) =
            attempt::candidate_outcome(search_input.driver().open_have(conjunct.clone()))?
        else {
            return Ok(None);
        };
        for step in steps {
            let Some(next) = attempt::candidate_outcome(scope.driver().apply_step(step))? else {
                return Ok(None);
            };
            scope = next;
        }
        attempt::candidate_outcome(scope.join())
    }

    pub(in crate::surface::proof) fn try_solve_closure_strategies(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_strategies");
        let mut scope = attempt::search_scope("solve closure");
        // Prefer the whole `known` closure, including computation, before
        // decomposing the goal or searching for another derivation.
        if let Some(proof) =
            attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Known))?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_flat_solve_conjunction(search_input, &[])?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_zero_witness_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_entry_existential_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if crate::kernel::search::ProofSearch::scalar_equality_goal_is_refuted(search_input) {
            // The facts decide the goal false, so only an undetected
            // contradiction proves it; a rewrite chain may expose one.
            let result =
                crate::kernel::search::ProofSearch::try_connected_fact_closure(search_input)?;
            if result.is_some() {
                scope.succeed();
            }
            return Ok(result);
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_structural_closure_under_binders(
                search_input,
            )?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if matches!(search_input.context.as_ref(), ProofContext::Pure(_))
            && let Some(surface) = search_input.surface_goal()
            && let Ok(proof) = search_input
                .driver()
                .apply_step(ProofStep::Extract(surface.clone()))
            && proof.focused_discharged()
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(execution) = search_input.execution()
            && let Some(anchor) = frontier_premise_anchor(execution)
            && let Some(surface_goal) = search_input.surface_goal()
            && let Ok(source) =
                surface_at_program_point(surface_goal, &ProgramPointSelector::ProgramPoint(anchor))
            && let Ok(proof) = search_input.driver().apply_step(ProofStep::Extract(source))
            && proof.is_complete()
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_operation_identity(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        let result = match crate::kernel::search::ProofSearch::try_solve_closure_after_direct(search_input, false)? {
            Some(proof) => Some(proof),
            None => match crate::kernel::search::ProofSearch::try_restated_constant_upper_bound(search_input)? {
                Some(proof) => Some(proof),
                None => match crate::kernel::search::ProofSearch::try_connected_fact_closure(search_input)? {
                    Some(proof) => Some(proof),
                    None => match crate::kernel::search::ProofSearch::try_late_arithmetic_with_selected_premises(search_input)? {
                        Some(proof) => Some(proof),
                        None => match crate::kernel::search::ProofSearch::try_disequality_by_refuted_equality(search_input)? {
                            Some(proof) => Some(proof),
                            None => crate::kernel::search::ProofSearch::try_element_address_disequality(search_input)?,
                        },
                    },
                },
            },
        };
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// Proves a disequality `a != b` from an available disequality `p != q`
    /// that `a == b` contradicts, such as the `int32` word fact
    /// `((m - 1) as int32) != 0` from the Integer fact `m - 1 != 0` where the
    /// facts keep `m - 1` in range, or the converse. Arithmetic reads no
    /// disequality premise, so the proof is by cases on `a == b`: that arm
    /// states `p == q`, which `solve` proves from `a == b`, and `known`
    /// closes it on the contradictory pair; the other arm holds the goal. The
    /// certificate is an ordinary proof `if`.
    ///
    /// It runs only after every other strategy has missed, on a disequality
    /// goal, over at most [`MAX_REFUTED_EQUALITY_PREMISES`] disequalities
    /// connected to the goal. The goals it states are equalities, and the
    /// strategy does not nest inside itself.
    pub(in crate::surface::proof) fn try_disequality_by_refuted_equality(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_disequality_by_refuted_equality");
        /// The equality a kernel disequality denies.
        fn denied(proposition: &Proposition) -> Option<Proposition> {
            match proposition {
                Proposition::ConditionIs(ConditionTerm::IntegerNotEqual(left, right), true) => {
                    Some(Proposition::ConditionIs(
                        ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                        true,
                    ))
                }
                Proposition::ConditionIs(
                    condition @ (ConditionTerm::IntegerEqual(..)
                    | ConditionTerm::Compare {
                        relation: CompareRelation::Equal,
                        ..
                    }),
                    false,
                ) => Some(Proposition::ConditionIs(condition.clone(), true)),
                _ => None,
            }
        }
        /// The equality a written disequality denies, under its state.
        fn denied_surface(surface: &ClickProposition) -> Option<ClickProposition> {
            match surface {
                ClickProposition::At {
                    selector,
                    proposition,
                } => Some(ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(denied_surface(proposition)?),
                }),
                ClickProposition::Comparison {
                    operator: ComparisonOperator::NotEqual,
                    ..
                } => Some(negate_click_proposition(surface)),
                ClickProposition::Not(body)
                    if matches!(
                        body.as_ref(),
                        ClickProposition::Comparison {
                            operator: ComparisonOperator::Equal,
                            ..
                        }
                    ) =>
                {
                    Some(body.as_ref().clone())
                }
                _ => None,
            }
        }
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        if denied(goal).is_none() {
            return Ok(None);
        }
        let Some(equal) = denied_surface(surface_goal) else {
            return Ok(None);
        };
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::RefutedEquality) else {
            return Ok(None);
        };
        let Some(connected) =
            crate::kernel::search::proposition_search::arithmetic_connected_premises(
                search_input.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        check_verification_deadline()?;
        let premises = connected
            .into_iter()
            .filter(|fact| fact != goal)
            .filter_map(|fact| denied(&fact))
            .take(MAX_REFUTED_EQUALITY_PREMISES)
            .collect::<Vec<_>>();
        if premises.is_empty() {
            return Ok(None);
        }
        let Some((split_proof, split, ids)) =
            attempt::candidate_outcome(search_input.split_focused_if(equal.clone()))?
        else {
            return Ok(None);
        };
        let marker = split_proof.checkpoint();
        let equal_arm = split_proof.focus_branch(ids[0])?;
        let introduced = [equal.clone()];
        for contradicted in premises {
            // The denied equality is spelled by construction at this state,
            // as a requirement is; a missing spelling is the candidate's miss.
            let requirement = UnresolvedRequirement {
                proposition: contradicted,
                context: None,
                introductions: Default::default(),
                call_site: None,
                assertion_condition: None,
                surface: None,
            };
            let Some(Some(spelling)) = attempt::candidate_outcome(
                equal_arm.requirement_surface(&requirement, &ProofStep::Step),
            )?
            else {
                continue;
            };
            let Some(scope) =
                attempt::candidate_outcome(equal_arm.driver().open_have(spelling.surface))?
            else {
                continue;
            };
            let Some(stated) = scope
                .driver()
                .try_solve_closure_with_surfaces(&introduced)?
            else {
                continue;
            };
            let Some(refuted) = attempt::candidate_outcome(stated.join())? else {
                continue;
            };
            let Some(equal_done) =
                attempt::candidate_outcome(refuted.driver().apply_step(ProofStep::Known))?
            else {
                continue;
            };
            let other_arm = equal_done.focus_branch(ids[1])?;
            let Some(other_done) =
                attempt::candidate_outcome(other_arm.driver().apply_step(ProofStep::Known))?
            else {
                return Ok(None);
            };
            return other_done
                .join_focused_if(&marker, split, ids, equal)
                .map(Some);
        }
        Ok(None)
    }

    /// Proves `&p[i] != &p[j]` from `i != j`: states the index disequality
    /// with `have i != j`, proved by `solve`, then closes the goal with
    /// `apply(click::separation::distinct_elements(p, i, j)) using { i != j; }`.
    /// `p` is the written goal's base; `i` and `j` are spelled from the
    /// kernel's two index words as the store search spells its index
    /// disequality (`((m - 1) as int32)`, `n - 1u64`, `0u64`), so the steps
    /// are spelled by construction and expansion writes them; the expanded
    /// proof searches nothing. It runs after every other strategy has missed, on a
    /// goal the kernel reads as two element addresses of one common base
    /// with indices of one width and format (`int32`, or 64-bit of one
    /// signedness), once (it does not nest inside itself), and its one
    /// search is the nested `solve` of the index disequality.
    pub(in crate::surface::proof) fn try_element_address_disequality(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_element_address_disequality");
        /// The base of a written element address `&p[i]`.
        fn element_address_base(expression: &ContractExpression) -> Option<&ProgramExpression> {
            let ContractExpression::ProgramExpression(ProgramExpression::AddressOf(target)) =
                expression
            else {
                return None;
            };
            let ProgramExpression::Index(base, _) = target.as_ref() else {
                return None;
            };
            Some(base)
        }
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        let Some((left, right, format)) =
            crate::kernel::search::store_separation::element_address_disequality_indices(goal)
        else {
            return Ok(None);
        };
        let ClickProposition::Comparison {
            left: left_address,
            operator: ComparisonOperator::NotEqual,
            right: right_address,
        } = surface_goal
        else {
            return Ok(None);
        };
        let (Some(base), Some(other_base)) = (
            element_address_base(left_address),
            element_address_base(right_address),
        ) else {
            return Ok(None);
        };
        if base != other_base {
            return Ok(None);
        }
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ElementAddress) else {
            return Ok(None);
        };
        check_verification_deadline()?;
        // The two indices are spelled from the kernel's index words, as the
        // store search spells its disequality, and are the law's arguments.
        let Some(indices_differ) = search_input.index_disequality_surface(&left, &right, format)
        else {
            return Ok(None);
        };
        let ClickProposition::Comparison {
            left: i, right: j, ..
        } = &indices_differ
        else {
            return Ok(None);
        };
        let arguments = vec![
            ContractExpression::ProgramExpression(base.clone()),
            i.clone(),
            j.clone(),
        ];
        let Some(scope) =
            attempt::candidate_outcome(search_input.driver().open_have(indices_differ.clone()))?
        else {
            return Ok(None);
        };
        let Some(closed) = scope.driver().try_solve_closure()? else {
            return Ok(None);
        };
        let Some(proof) = attempt::candidate_outcome(closed.join())? else {
            return Ok(None);
        };
        Ok(proof.driver().close_with_unsigned_lemma(
            "click::separation::distinct_elements",
            arguments,
            indices_differ,
        ))
    }

    /// A goal that reads stored cells, proved over the values stored there:
    /// `have` the goal's read-over-write form (`kernel::comparison_form`)
    /// by `solve`, then close the goal by `known`, which matches a read
    /// through the value its cell holds. The stored-value form is the goal
    /// `solve` would have seen had the reads been folded, so this recovers
    /// what its rules prove about the stored values. One level: the inner
    /// `solve` does not take this route again.
    pub(in crate::surface::proof) fn try_stored_value_goal(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_stored_value_goal");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let Some(resolved) = crate::kernel::comparison_form(goal) else {
            return Ok(None);
        };
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::StoredValue) else {
            return Ok(None);
        };
        let surface = search_input.premise_surface_facts().and_then(|recorded| {
            Self::proposed_surface_goal(search_input, recorded, &resolved).or_else(|| {
                Self::proposed_surface_goal(
                    search_input,
                    search_input.local_surface_facts(),
                    &resolved,
                )
            })
        });
        let Some(surface) = surface else {
            return Ok(None);
        };
        let Some(scope) = attempt::candidate_outcome(search_input.driver().open_have(surface))?
        else {
            return Ok(None);
        };
        let Some(closed) = (scope).driver().try_solve_closure()? else {
            return Ok(None);
        };
        let Some(proof) = attempt::candidate_outcome(closed.join())? else {
            return Ok(None);
        };
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// `solve`'s strategy over the facts connected to the goal: read
    /// the goal out of a function fact's definition; rewrite the goal by a
    /// connected equality once and then `known`, then as a bounded
    /// chain whose rewritten goals the cheap closers and a nested `solve`
    /// try; and join two constructor equations of one value. A nested
    /// `solve` inside these does not start them again.
    pub(in crate::surface::proof) fn try_connected_fact_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_connected_fact_closure");
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ConnectedFacts) else {
            return Ok(None);
        };
        // A scalar match was opaque to arithmetic before its constructor
        // rewrite. Only that shape permits arithmetic to restart inside the
        // connected search; general equality chains must not repeat all its
        // failed planners at every rewritten goal.
        let scalar_match = match search_input.goal() {
            Some(Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), _)) => {
                matches!(
                    left.as_ref(),
                    crate::kernel::IntegerTerm::AlgebraicMatch { .. }
                ) || matches!(
                    right.as_ref(),
                    crate::kernel::IntegerTerm::AlgebraicMatch { .. }
                )
            }
            _ => false,
        };
        let _match_arithmetic = scalar_match
            .then(|| SolveFallbackScope::enter(SolveFallback::MatchArithmetic))
            .flatten();
        // First: it costs little when it does not apply.
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_definition_condition_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_single_rewrite_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_connected_equality_chain_closure(
                search_input,
                RewriteClosers::Ambient,
            )?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_constructor_join_closure(search_input)
    }

    /// Closes `value <= c` over a constant by proving the same bound
    /// written `value < c + 1`. The two are one claim, but an order chain
    /// that ends at `c + 1` concludes the strict form, and the derivation
    /// asked for the non-strict form finds no chain ending at `c`.
    ///
    /// It runs only after every other strategy has missed, on a goal of
    /// exactly this shape, and the restated goal is strict, so it does not
    /// recur.
    pub(in crate::surface::proof) fn try_restated_constant_upper_bound(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restated_constant_upper_bound");
        let Some(Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                relation: CompareRelation::LessEqual,
                left: _,
                right: bound,
            },
            true,
        )) = search_input.goal()
        else {
            return Ok(None);
        };
        let unsigned = *format == MachineIntegerType::UInt32;
        // `c + 1` must not wrap in the order the comparison is made in.
        let Some(bound) = bound.as_const().filter(|bound| {
            if unsigned {
                *bound != u32::MAX
            } else {
                *bound as i32 != i32::MAX
            }
        }) else {
            return Ok(None);
        };
        let Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        }) = search_input.surface_goal().cloned()
        else {
            return Ok(None);
        };
        // The source bound is the kernel bound; the successor is spelled in
        // the operand's own type.
        let successor = match &right {
            ContractExpression::ProgramExpression(ProgramExpression::Value(
                ProgramValue::UInt32(bits32_constant!(value)),
            )) if unsigned && constant_u32(*value) == bound => {
                ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::UInt32(MachineTerm::uint32_constant(constant_u32(*value) + 1)),
                ))
            }
            ContractExpression::IntegerLiteral(literal)
                if !unsigned && literal.parse::<i32>().ok() == Some(bound as i32) =>
            {
                ContractExpression::IntegerLiteral((i64::from(bound as i32) + 1).to_string())
            }
            _ => return Ok(None),
        };
        let strict = ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right: successor,
        };
        let Ok(scope) = search_input.driver().open_have(strict.clone()) else {
            return Ok(None);
        };
        let Some(proved) = (scope).driver().try_solve_closure()? else {
            return Ok(None);
        };
        let Ok(joined) = proved.join() else {
            return Ok(None);
        };
        Ok(joined
            .driver()
            .apply_step(ProofStep::ArithmeticUsing(vec![strict]))
            .ok()
            .filter(|proof| proof.is_complete() || proof.goal() != search_input.goal()))
    }

    /// Continues smart closure after direct logical candidates have either
    /// missed or been deliberately rejected as non-checkable. When
    /// `exclude_exact_goal` is true, the atomic derivation query may not cite
    /// the goal's own ambient fact; every selected theorem step is still
    /// checked against this unchanged Proof.
    pub(in crate::surface::proof) fn try_solve_closure_after_direct(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_after_direct");
        let mut scope = attempt::search_scope("solve closure after direct candidates");
        let result =
            crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces(
                search_input,
                exclude_exact_goal,
                &[],
            )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    pub(in crate::surface::proof) fn try_solve_closure_with_surfaces(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_with_surfaces");
        let mut scope = attempt::search_scope("solve closure with surfaces");
        // Prefer the whole `known` closure, including computation, before
        // decomposing the goal or searching for another derivation.
        if let Some(proof) =
            attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Known))?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_structural_closure_under_binders(
                search_input,
            )?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        let result =
            crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces(
                search_input,
                false,
                introduced_surfaces,
            )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    pub(in crate::surface::proof) fn try_solve_closure_after_direct_with_surfaces(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_after_direct_with_surfaces");
        crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces_and_function_unfold(search_input,
            exclude_exact_goal,
            introduced_surfaces,
            true,
        )
    }

    pub(in crate::surface::proof) fn try_solve_closure_after_direct_with_surfaces_and_function_unfold(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
        allow_function_unfold: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery(
            "try_solve_closure_after_direct_with_surfaces_and_function_unfold",
        );
        // A separating conjunction already states its structural proof tree.
        // Decompose it before selecting ambient arithmetic/history candidates;
        // each child still runs ordinary solve and emits ordinary library steps.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(proof) = Self::try_resource_star_separation_closure(
                search_input,
                surface_goal,
                introduced_surfaces,
            )?
        {
            return Ok(Some(proof));
        }
        // Prefer ordinary equalities between resource descriptors to a
        // historical transport of the whole separation proposition.
        if let Some(proof) = Self::try_resource_descriptor_rewrite_closure(search_input)? {
            return Ok(Some(proof));
        }
        if let Some(proof) = Self::try_ordinary_viewability_restriction_closure(search_input, None)
        {
            return Ok(Some(proof));
        }
        // Plain solve and recursive logical closure share the same memory
        // strategies. A structural child must not lose read-over-write or
        // explicit frame transport merely because it was reached by `both`.
        if let Some(surface) = search_input.surface_goal()
            && let Some(proof) =
                crate::kernel::search::ProofSearch::try_cell_frame_transport_closure(
                    search_input,
                    surface,
                )?
        {
            return Ok(Some(proof));
        }
        // A goal that reads stored cells is first tried over the stored
        // values, the goal the search saw before reads kept their version
        // names; the full search over the reads follows only when that
        // misses.
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_stored_value_goal(search_input)?
        {
            return Ok(Some(proof));
        }
        // The uint32 lemmas state the wrapping steps of a `uint32` order, so
        // a goal of one of their shapes is closed by naming the lemma, from
        // the exact premise it requires.
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_unsigned_order_step(search_input)
        {
            return Ok(Some(proof));
        }
        // Population bounds are arithmetic on the authority's count, even
        // when that count shares a carrier with a C field. Try its indexed
        // bounds before searching memory equalities and recorded states.
        // Compound signed orders likewise select indexed bounds before
        // spelling historical aliases, including terminal outcomes with
        // many earlier clauses. Simple terminal comparisons retain their
        // result-aware rewrites and named-rule routes first.
        let population_count_comparison = matches!(
            search_input.surface_goal(),
            Some(
                ClickProposition::Comparison {
                    left: ContractExpression::ResourceCount(_),
                    ..
                } | ClickProposition::Comparison {
                    right: ContractExpression::ResourceCount(_),
                    ..
                }
            )
        );
        let compound_signed_order = matches!(
            search_input.goal(),
            Some(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::LessThan,
                    ..
                } | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::LessEqual,
                    ..
                } | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::GreaterThan,
                    ..
                } | ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::GreaterEqual,
                    ..
                },
                _
            ))
        ) && matches!(
            search_input.surface_goal(),
            Some(ClickProposition::Comparison { left, right, .. })
                if [left, right].into_iter().any(|term| matches!(
                    term,
                    ContractExpression::Add(..)
                        | ContractExpression::Subtract(..)
                        | ContractExpression::Multiply(..)
                ))
        );
        let indexed_arithmetic_tried = population_count_comparison
            || compound_signed_order
            || (search_input.focused_outcome_data().is_none()
                && matches!(
                    search_input.goal(),
                    Some(Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::LessThan,
                            ..
                        } | ConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::LessEqual,
                            ..
                        } | ConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::GreaterThan,
                            ..
                        } | ConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::GreaterEqual,
                            ..
                        },
                        _
                    ))
                ));
        if indexed_arithmetic_tried
            && let Some(proof) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: indexed bounds",
                || {
                    crate::kernel::search::ProofSearch::try_execution_signed_arithmetic(
                        search_input,
                    )
                },
            )
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_equality_from_opposite_bounds(search_input)
        {
            return Ok(Some(proof));
        }
        // Integer arithmetic has its own compact, locally checked evidence
        // path. Keep it ahead of the legacy signed arithmetic derivation so
        // a mathematical Integer goal cannot accidentally enter the machine
        // overflow checker.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(goal) = search_input.goal()
            && let Some(plan) = plan_arithmetic(ArithmeticEngine::IntegerAffine, goal, &[])
                .and_then(ArithmeticPlan::integer_affine)
            && plan.nodes.len() == 1
            && matches!(
                plan.nodes.first(),
                Some(IntegerArithmeticNode::Trivial { .. })
            )
        {
            let certificate = IntegerCertificate {
                nodes: vec![IntegerCertificateNode::Trivial {
                    result: surface_goal.clone(),
                }],
                conclusion: 0,
            };
            if let Ok(proof) = search_input
                .driver()
                .apply_step(ProofStep::ArithmeticCertificate(
                    ArithmeticCertificate::integer(certificate),
                ))
            {
                return Ok(Some(proof));
            }
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_goal_conditional_normalization(search_input)
        {
            return Ok(Some(proof));
        }
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(proof) =
                crate::kernel::search::ProofSearch::try_selected_unchanged_load_forall_goal(
                    search_input,
                    surface_goal,
                    &[],
                )
        {
            return Ok(Some(proof));
        }
        // A written conjunction is split before any whole-goal derivation,
        // rewrite, transport, or instantiation strategy below runs over it.
        // Each of those costs work in the ambient facts per attempt, and on
        // a conjunction chain the structural recursion would otherwise
        // repeat them on every suffix of the chain before reaching its
        // leaves, which is quadratic in the chain. Each conjunct still gets
        // the complete closure, including these strategies, and the
        // whole-goal strategies still run, unchanged, when the split misses.
        if let Some(flat) = crate::kernel::search::ProofSearch::try_flat_solve_conjunction(
            search_input,
            introduced_surfaces,
        )? {
            return Ok(Some(flat));
        }
        let structural_conjunction_tried = if let Some(surface_goal) = search_input.surface_goal()
            && matches!(search_input.goal(), Some(Proposition::And(_, _)))
            && surface_logical_children(surface_goal, true).is_some()
        {
            if let Some(structural) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: structural",
                || {
                    crate::kernel::search::ProofSearch::try_structural_solve_closure_with_surfaces(
                        search_input,
                        surface_goal,
                        introduced_surfaces,
                    )
                },
            )? {
                return Ok(Some(structural));
            }
            true
        } else {
            false
        };
        // A constructor-disjoint guard needs only its indexed model equation.
        // Refute it before the whole implication's connected memory facts are
        // selected and given historical source spellings.
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_constructor_guard_refutation(search_input)?
        {
            return Ok(Some(closed));
        }
        // Retain the selected premises for the anchored fallbacks. The proof
        // is unchanged by a declined candidate, so repeating derivation
        // discovery here would perform the same search a second time.
        let mut anchored_pairs = Vec::new();
        let atomic = (|| {
            let (goal, derivation) =
                crate::kernel::search::ProofSearch::selected_solve_derivation_plan(
                    search_input,
                    exclude_exact_goal,
                )?;
            // A derivation that records the exact path it used names its
            // own premises. Spell only those first: the selection it ran in
            // holds every fact connected to the goal's variables, and
            // spelling them all costs work in the path's length for a
            // closer that cites one or two.
            let cited_pairs = derivation.recorded_path_premises().and_then(|cited| {
                crate::kernel::search::ProofSearch::resolve_solve_premises(
                    search_input,
                    &cited,
                    introduced_surfaces,
                )
                .filter(|pairs| pairs.len() == cited.len())
            });
            if let Some(pairs) = &cited_pairs
                && let Some(closed) =
                    crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                        search_input,
                        &goal,
                        &derivation,
                        pairs,
                    )
            {
                return Some(closed);
            }
            // A derivation that only selects a disjunct proves nothing the
            // atomic closers below can check: its premises belong to that
            // disjunct, which the structural closure proves on its own goal.
            if derivation.disjunction_choice().is_some() {
                return None;
            }
            anchored_pairs = crate::kernel::search::ProofSearch::resolve_solve_premises(
                search_input,
                &derivation.context_premises(),
                introduced_surfaces,
            )?;
            let premise_pairs = &anchored_pairs;
            // This rule constructs its checked nonnegative scope directly.
            // Avoid a speculative generic candidate for this same predecessor
            // goal before constructing that scope.
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_selected_predecessor_upper_bound(
                    search_input,
                    &goal,
                    premise_pairs,
                )
            {
                return Some(closed);
            }
            // The same derivation already failed to check over the premises
            // it cites; the wider context does not translate it either.
            let typed_atomic =
                match crate::kernel::search::ProofSearch::extract_special_conjunct_premises(
                    search_input,
                    &derivation,
                    premise_pairs,
                ) {
                    Ok(Some(extracted)) if extracted.is_complete() => Some(extracted),
                    _ if cited_pairs.is_some() => None,
                    Ok(Some(extracted)) => {
                        crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                            &(extracted),
                            &goal,
                            &derivation,
                            premise_pairs,
                        )
                    }
                    Ok(None) | Err(()) => {
                        crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                            search_input,
                            &goal,
                            &derivation,
                            premise_pairs,
                        )
                    }
                };
            typed_atomic
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_pointer_inequality_rewrite(
                        search_input,
                        &goal,
                        premise_pairs,
                    )
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_premise_equality_chain_closure(
                        search_input,
                        premise_pairs,
                        RewriteClosers::Selected,
                    )
                    .ok()
                    .flatten()
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_constant_bound_weakening(
                        search_input,
                        &goal,
                        &derivation,
                    )
                })
                .or_else(|| {
                    search_input.surface_goal().and_then(|surface_goal| {
                        crate::kernel::search::ProofSearch::try_selected_unchanged_load_forall_goal(
                            search_input,
                            surface_goal,
                            premise_pairs,
                        )
                        .or_else(|| {
                            crate::kernel::search::ProofSearch::try_selected_forall_goal(
                                search_input,
                                &goal,
                                surface_goal,
                                premise_pairs,
                            )
                        })
                    })
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_forall_instantiation(
                        search_input,
                        &goal,
                        premise_pairs,
                    )
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_disjunction_cases(
                        search_input,
                        premise_pairs,
                    )
                })
        })();
        check_verification_deadline()?;
        if let Some(atomic) = atomic {
            return Ok(Some(atomic));
        }
        if matches!(search_input.context.as_ref(), ProofContext::Pure(_)) {
            for (_, surface) in &anchored_pairs {
                if let Some(contradiction) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_step(ProofStep::Contradiction(surface.clone())),
                )? {
                    return Ok(Some(contradiction));
                }
            }
        }
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(goal) = search_input.goal()
            && !anchored_pairs.is_empty()
        {
            let kernels = anchored_pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            // The bounded affine planner first, then simplex for a bound
            // that needs more of the selected premises than it combines.
            for engine in [
                ArithmeticEngine::IntegerAffine,
                ArithmeticEngine::IntegerRefutation,
            ] {
                if let Some(plan) =
                    plan_arithmetic(engine, goal, &kernels).and_then(ArithmeticPlan::integer_affine)
                    && let Some(certificate) =
                        integer_plan_to_surface_certificate(&plan, &anchored_pairs, surface_goal)
                    && let Ok(proof) =
                        search_input
                            .driver()
                            .apply_step(ProofStep::ArithmeticCertificate(
                                ArithmeticCertificate::integer(certificate),
                            ))
                {
                    return Ok(Some(proof));
                }
            }
            check_verification_deadline()?;
        }
        if let Some(anchored) =
            crate::kernel::search::ProofSearch::try_outcome_anchored_order_transitivity(
                search_input,
                &anchored_pairs,
            )
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_outcome_anchored_increment_order(
                    search_input,
                    &anchored_pairs,
                )
            })
        {
            return Ok(Some(anchored));
        }
        // One indexed rewrite can close the goal at once. The search over
        // chains of connected equalities costs a closure attempt per
        // rewritten goal, each over the goal's whole connected component, so
        // it waits until arithmetic from selected premises has had the goal:
        // a linear claim that one stated fact decides is not searched for
        // through every equality that mentions its atoms.
        let direct_rewrite = crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: goal equality rewrite",
            || {
                Ok::<_, ClickError>(
                    crate::kernel::search::ProofSearch::try_indexed_direct_equality_rewrite(
                        search_input,
                        exclude_exact_goal,
                    ),
                )
            },
        )?;
        let chain_rewrites = match direct_rewrite {
            std::ops::ControlFlow::Break(Some(rewritten)) => return Ok(Some(rewritten)),
            std::ops::ControlFlow::Break(None) => false,
            std::ops::ControlFlow::Continue(()) => true,
        };
        // An arithmetic goal the cheap derivations above missed goes to
        // `arithmetic` from premises it selects, before the rewrite, unfold
        // and transport strategies below spend their work in the context's
        // facts.
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_arithmetic_with_selected_premises(search_input)?
        {
            return Ok(Some(proof));
        }
        if chain_rewrites
            && let Some(rewritten) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: goal equality rewrite",
                || {
                    crate::kernel::search::ProofSearch::try_connected_goal_equality_chain_closure(
                        search_input,
                        allow_function_unfold,
                    )
                },
            )?
        {
            return Ok(Some(rewritten));
        }
        // Indexed rewrite planning uses Option for an ordinary candidate
        // miss; preserve an exhausted budget before trying another closer.
        check_verification_deadline()?;
        if allow_function_unfold
            && let Some(rewritten) =
                crate::kernel::search::ProofSearch::try_introduced_equality_then_function_unfold_closure(search_input, introduced_surfaces)?
        {
            return Ok(Some(rewritten));
        }
        // A goal over a value a fact equates to a constructor, as a proof
        // `match` arm's case states it: evaluate from a rewrite.
        if allow_function_unfold
            && search_input
                .facts()
                .assumptions()
                .has_algebraic_constructor_facts()
            && let Some(rewritten) =
                crate::kernel::search::ProofSearch::try_constructor_evaluation_closure(
                    search_input,
                    introduced_surfaces,
                )?
        {
            return Ok(Some(rewritten));
        }
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(proof) = crate::kernel::search::ProofSearch::try_state_transport_closure(
                search_input,
                surface_goal,
            )?
        {
            return Ok(Some(proof));
        }
        if let Some(instantiated) =
            crate::kernel::search::ProofSearch::try_indexed_forall_instantiation_with_surfaces(
                search_input,
                introduced_surfaces,
            )
        {
            return Ok(Some(instantiated));
        }
        if let Some(defined) =
            crate::kernel::search::ProofSearch::try_signed_definedness_closure(search_input)?
        {
            return Ok(Some(defined));
        }
        if let Some(eliminated) =
            crate::kernel::search::ProofSearch::try_disjunctive_syllogism_closure(search_input)
        {
            return Ok(Some(eliminated));
        }
        if let Some(guarded) =
            crate::kernel::search::ProofSearch::try_guarded_consequent_closure(search_input)?
        {
            return Ok(Some(guarded));
        }
        // The atomic helpers still classify their internal candidate misses
        // as `Option`; surface a deadline that fired inside them here rather
        // than continuing into structural search with it exceeded.
        check_verification_deadline()?;
        if search_input.surface_goal().is_none()
            && matches!(search_input.goal(), Some(Proposition::And(_, _)))
        {
            return crate::kernel::search::ProofSearch::try_structural_and_solve_closure(
                search_input,
                introduced_surfaces,
            );
        }
        let Some(surface_goal) = search_input.surface_goal().cloned() else {
            return Ok(None);
        };
        if let Some(enumerated) = crate::kernel::search::ProofSearch::try_finite_forall_enumeration(
            search_input,
            &surface_goal,
        )? {
            return Ok(Some(enumerated));
        }
        // A pure goal that its own signed bounds already decide gets the one
        // checked arithmetic certificate, not a case split over those same
        // bounds. The certificate reads the goal's own bound buckets and
        // emits a single leaf, while the split searches for a pivot and then
        // owes a proof on each arm — including a dead arm closed only by a
        // contradiction between the pivot and a premise. Keep this ahead of
        // the split so the cheaper, smaller expansion wins whenever it
        // applies; the split still runs for everything the certificate
        // declines.
        if let Some(arithmetic) =
            crate::kernel::search::ProofSearch::try_pure_signed_arithmetic(search_input)
        {
            return Ok(Some(arithmetic));
        }
        if let Some(split) = crate::kernel::search::ProofSearch::try_upper_bound_split_closure(
            search_input,
            introduced_surfaces,
        )? {
            return Ok(Some(split));
        }
        // Enter logical binders before looking for function applications.
        // An application below `forall (x)` cannot be checked until `intro`
        // has associated the surface name `x` with its fresh kernel variable.
        // The recursive structural call retains that checked `Intro` step and
        // then discovers applications in the now-focused body goal.
        // A conjunction already missed the same structural closure above;
        // no proof step has been applied since, so it would miss again.
        if !structural_conjunction_tried
            && let Some(structural) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: structural",
                || {
                    crate::kernel::search::ProofSearch::try_structural_solve_closure_with_surfaces(
                        search_input,
                        &surface_goal,
                        introduced_surfaces,
                    )
                },
            )?
        {
            return Ok(Some(structural));
        }
        if allow_function_unfold
            && let Some(unfolded) =
                crate::kernel::search::ProofSearch::try_function_unfold_solve_closure(
                    search_input,
                    introduced_surfaces,
                )?
        {
            return Ok(Some(unfolded));
        }
        // A Special fact such as `aligned(p + i, 8)` is not generally a
        // solve-derivation: the kernel's pointer rule consumes a matching
        // alignment/relation fact directly. Use the selected pairs when
        // `solve() using` supplied them; otherwise recover only typed Special
        // candidates from the recorded Surface map for generic `solve()`.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(goal) = search_input.goal()
        {
            let special_pairs = if !anchored_pairs.is_empty() {
                anchored_pairs.clone()
            } else {
                let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
                    ProofContext::Pure(context) => {
                        (&context.theorem_context.surface_requirements, None)
                    }
                    ProofContext::FixedState(context) => (
                        context.surface_propositions,
                        context.premise_anchor.as_ref(),
                    ),
                    ProofContext::Execution(_) => {
                        if let Some(data) = search_input.focused_outcome_data() {
                            (&data.surface_propositions, data.premise_anchor.as_ref())
                        } else {
                            let Some(execution) = search_input.execution() else {
                                return Ok(None);
                            };
                            (&execution.presentation.surface_propositions, None)
                        }
                    }
                };
                search_input
                    .facts()
                    .special_candidates_mentioning(goal)
                    .into_iter()
                    .filter(|premise| {
                        matches!(
                            premise,
                            Proposition::ConditionIs(
                                ConditionTerm::Compare {
                                    format: MachineIntegerType::Int64,
                                    relation: CompareRelation::Equal,
                                    ..
                                } | ConditionTerm::PointerValueEqual(..)
                                    | ConditionTerm::PointerEqual(..)
                                    | ConditionTerm::PointerOffsetEqual(..)
                                    | ConditionTerm::Float32(FloatCondition::Classification { .. })
                                    | ConditionTerm::Float64(FloatCondition::Classification { .. }),
                                true
                            )
                        )
                    })
                    .filter_map(|premise| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            search_input,
                            surface_facts,
                            premise_anchor,
                            &premise,
                        )
                        .map(|surface| (premise.clone(), surface))
                    })
                    .collect::<Vec<_>>()
            };
            let kernels = special_pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            let surfaces = special_pairs
                .iter()
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>();
            if let Some(plan) = plan_arithmetic(ArithmeticEngine::Special, goal, &kernels)
                .and_then(ArithmeticPlan::special)
            {
                let certificate =
                    special_plan_to_surface_certificate(&plan, &surfaces, surface_goal);
                if let Ok(proof) = search_input
                    .driver()
                    .apply_step(ProofStep::ArithmeticCertificate(certificate))
                {
                    return Ok(Some(proof));
                }
            }
        }
        // Signed arithmetic over the selected premises is the final
        // fallback. All established equality, transport, quantifier,
        // structural, and function-unfold routes must get first choice so
        // their selected proof steps remain visible in expansion. Population
        // comparisons already tried indexed bounds before memory rewriting;
        // pure arithmetic ran ahead of the case split it would hide behind.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(goal) = search_input.goal()
            && !anchored_pairs.is_empty()
            && let Some(plan) = plan_arithmetic(
                ArithmeticEngine::SignedInt32,
                goal,
                &anchored_pairs
                    .iter()
                    .map(|(kernel, _)| kernel.clone())
                    .collect::<Vec<_>>(),
            )
            .and_then(ArithmeticPlan::signed_int32)
            && let Some(certificate) = search_input.signed_plan_to_surface_certificate(
                &plan,
                &anchored_pairs,
                surface_goal,
            )
            && let Ok(proof) = search_input
                .driver()
                .apply_step(ProofStep::ArithmeticCertificate(ArithmeticCertificate {
                    family: ArithmeticCertificateFamily::SignedInt32(certificate),
                }))
        {
            return Ok(Some(proof));
        }
        if !indexed_arithmetic_tried
            && let Some(arithmetic) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: indexed bounds",
                || {
                    crate::kernel::search::ProofSearch::try_execution_signed_arithmetic(
                        search_input,
                    )
                },
            )
        {
            return Ok(Some(arithmetic));
        }
        // The pure signed certificate already ran above on this same proof
        // state; repeating it here would redo identical work for an
        // identical answer.
        check_verification_deadline()?;
        Ok(None)
    }

    /// Select signed bounds only from the goal variables' persistent buckets.
    /// This is a smart query; the resulting certificate checks every premise.
    pub(in crate::surface::proof) fn try_pure_signed_arithmetic(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_pure_signed_arithmetic");
        let ProofContext::Pure(context) = search_input.context.as_ref() else {
            return None;
        };
        crate::kernel::search::ProofSearch::try_indexed_signed_arithmetic(
            search_input,
            &context.theorem_context.surface_requirements,
            None,
        )
    }

    /// The same indexed bound selection on an execution proof: at function
    /// exit, at a statement frontier, or inside a loop phase, so solve reads a
    /// variable's bounds the same way wherever it runs. A bound can also be
    /// the negation of a branch condition. A goal that is itself an available
    /// fact is left to `known`. Pre-return signed orders and population
    /// bounds run before broad premise spelling, preferring named rules on
    /// the selected premises; other goals retain the final fallback.
    pub(in crate::surface::proof) fn try_execution_signed_arithmetic(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execution_signed_arithmetic");
        let goal = search_input.goal()?;
        if std::iter::once(goal.clone())
            .chain(condition_polarity_forms(goal))
            .any(|form| search_input.facts().contains(&form))
        {
            return None;
        }
        let (surfaces, anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(_) => return None,
            ProofContext::FixedState(context) => {
                (context.surface_propositions, context.premise_anchor.clone())
            }
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.clone()),
                None => (
                    &search_input.execution()?.surface_propositions,
                    search_input.execution().and_then(frontier_premise_anchor),
                ),
            },
        };
        crate::kernel::search::ProofSearch::try_indexed_signed_arithmetic(
            search_input,
            surfaces,
            anchor.as_ref(),
        )
    }

    /// An equality of two machine integers from the two opposite order facts
    /// on them, `l <= r` and `r <= l` in any spelling: an `arithmetic()
    /// using` step citing just those two facts. The signed `int32` order has
    /// its own named rules; this covers `uint32` and both 64-bit orders, which
    /// the atomic derivation does not combine into an equality. Each
    /// candidate fact is one exact index lookup per spelling, so the route
    /// costs a fixed number of lookups per goal.
    pub(in crate::surface::proof) fn try_equality_from_opposite_bounds(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_equality_from_opposite_bounds");
        // Each candidate is the two opposite orders, each with whether it
        // holds of every value: `0 <= x` in an unsigned order, which no
        // fact states and the step's own range reasoning supplies.
        let zero =
            |term: &MachineTerm| term.as_const() == Some(0) || term.uint64_as_const() == Some(0);
        let pairs = match search_input.goal()? {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => {
                let (left, right) = (left.as_ref().clone(), right.as_ref().clone());
                vec![(
                    (
                        ConditionTerm::unsigned_less_equal(left.clone(), right.clone()),
                        zero(&left),
                    ),
                    (
                        ConditionTerm::unsigned_less_equal(right.clone(), left.clone()),
                        zero(&right),
                    ),
                )]
            }
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => {
                let (left, right) = (left.as_ref().clone(), right.as_ref().clone());
                vec![
                    (
                        (
                            ConditionTerm::int64_signed_less_equal(left.clone(), right.clone()),
                            false,
                        ),
                        (
                            ConditionTerm::int64_signed_less_equal(right.clone(), left.clone()),
                            false,
                        ),
                    ),
                    (
                        (
                            ConditionTerm::uint64_less_equal(left.clone(), right.clone()),
                            zero(&left),
                        ),
                        (
                            ConditionTerm::uint64_less_equal(right.clone(), left.clone()),
                            zero(&right),
                        ),
                    ),
                ]
            }
            _ => return None,
        };
        let available = |condition: ConditionTerm| {
            let fact = Proposition::ConditionIs(condition, true);
            std::iter::once(fact.clone())
                .chain(crate::surface::proof::order_claim_forms(&fact))
                .find(|form| search_input.facts().contains(form))
        };
        let (surfaces, anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(_) => (None, None),
            ProofContext::FixedState(context) => (
                Some(context.surface_propositions),
                context.premise_anchor.clone(),
            ),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (
                    Some(&data.surface_propositions),
                    data.premise_anchor.clone(),
                ),
                None => (
                    Some(&search_input.execution()?.surface_propositions),
                    search_input.execution().and_then(frontier_premise_anchor),
                ),
            },
        };
        for ((lower, lower_total), (upper, upper_total)) in pairs {
            let mut facts = Vec::new();
            let mut missing = false;
            for (condition, total) in [(lower, lower_total), (upper, upper_total)] {
                match available(condition) {
                    Some(fact) => facts.push(fact),
                    None if total => {}
                    None => missing = true,
                }
            }
            if missing || facts.is_empty() {
                continue;
            }
            let spelled = facts
                .iter()
                .map(|fact| match surfaces {
                    Some(surfaces) => crate::kernel::search::ProofSearch::available_surface_fact(
                        search_input,
                        surfaces,
                        anchor.as_ref(),
                        fact,
                    )
                    .or_else(|| search_input.spelled_comparison_surface(fact)),
                    None => search_input.spelled_comparison_surface(fact),
                })
                .collect::<Option<Vec<_>>>();
            if let Some(spelled) = spelled
                && let Ok(proof) = search_input
                    .driver()
                    .apply_step(ProofStep::ArithmeticUsing(spelled))
            {
                return Some(proof);
            }
        }
        None
    }

    /// The facts the indexed signed arithmetic route plans over: the bounds
    /// reachable from the goal's variables, and with `with_equalities` the
    /// equalities naming them too, followed to their own variables. Each
    /// visited variable costs its indexed bound entries and, with
    /// equalities, one indexed lookup of the facts that mention it.
    pub(in crate::surface::proof) fn indexed_arithmetic_premises(
        search_input: &Proof<'a>,
        goal: &Proposition,
        with_equalities: bool,
    ) -> (Vec<Proposition>, bool) {
        #[cfg(test)]
        crate::kernel::search::record_discovery("indexed_arithmetic_premises");
        let mut available = BTreeSet::new();
        let mut has_equalities = false;
        let mut visited = BTreeSet::new();
        let unsigned_goal = crate::surface::checking::is_unsigned_order_goal(goal);
        // Count lowering can leave a read expression where the bounds index
        // names its registered load variable. Seed from that canonical value,
        // not from variables in the read's address or memory state.
        let canonical_goal = crate::kernel::canonical_condition_fact(goal);
        let mut pending = crate::kernel::proposition_variables(&canonical_goal)
            .into_iter()
            .collect::<std::collections::VecDeque<_>>();
        while let Some(variable) = pending.pop_front() {
            if visited.len() == MAX_BOUND_VARIABLES {
                break;
            }
            if !visited.insert(variable) {
                continue;
            }
            let assumptions = search_input.facts().assumptions();
            let term = MachineTerm::Variable(variable);
            // A `uint32` goal's bounds are `uint32` orders, filed in their
            // own index.
            let entries = assumptions
                .signed_order_bound_entries(&term)
                .map(|entry| (MachineIntegerType::Int32, entry))
                .chain(
                    unsigned_goal
                        .then(|| assumptions.uint32_order_bound_entries(&term))
                        .into_iter()
                        .flatten()
                        .map(|entry| (MachineIntegerType::UInt32, entry)),
                )
                .collect::<Vec<_>>();
            for (format, (endpoint, other, strict, forward)) in entries {
                let (left, right) = if forward {
                    (endpoint, other)
                } else {
                    (other, endpoint)
                };
                let condition = ConditionTerm::Compare {
                    format,
                    relation: if strict {
                        CompareRelation::LessThan
                    } else {
                        CompareRelation::LessEqual
                    },
                    left: Box::new(left),
                    right: Box::new(right),
                };
                let fact = Proposition::ConditionIs(condition, true);
                let mut found = false;
                for form in std::iter::once(fact.clone()).chain(condition_polarity_forms(&fact)) {
                    if search_input.facts().contains(&form) {
                        available.insert(form);
                        found = true;
                    }
                }
                if found {
                    pending.extend(
                        crate::kernel::proposition_variables(
                            &crate::kernel::canonical_condition_fact(&fact),
                        )
                        .into_iter()
                        .filter(|next| !visited.contains(next)),
                    );
                }
            }
            // An equality names the variable through another: a call's
            // `o.size == old(o.size) + 1` relates the goal's field to the
            // entry value its bounds name.
            if !with_equalities {
                continue;
            }
            let equalities = search_input
                .facts()
                .assumptions()
                .condition_facts_mentioning_variable(variable)
                .into_iter()
                .flatten()
                .filter(|(condition, value)| {
                    *value
                        && matches!(
                            condition,
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                                relation: CompareRelation::Equal,
                                ..
                            }
                        )
                })
                .map(|(condition, _)| Proposition::ConditionIs(condition.clone(), true))
                // A load's defining equation only names that same value.
                // It adds no arithmetic relation, and following its memory
                // term would pull unrelated address variables into the search.
                .filter(|fact| !crate::kernel::is_load_variable_defining_fact(fact))
                .collect::<Vec<_>>();
            for fact in equalities {
                if !search_input.facts().contains(&fact) {
                    continue;
                }
                has_equalities = true;
                pending.extend(
                    crate::kernel::proposition_variables(&crate::kernel::canonical_condition_fact(
                        &fact,
                    ))
                    .into_iter()
                    .filter(|next| !visited.contains(next)),
                );
                available.insert(fact);
            }
        }
        (available.into_iter().collect(), has_equalities)
    }

    /// Selects the bounds reachable from the goal's variables: each goal
    /// variable's bounds, then the bounds on the variables those bounds
    /// name (`i < n` leads to `n`'s bounds), breadth-first in variable order,
    /// visiting at most [`MAX_BOUND_VARIABLES`] variables. Each visited
    /// variable costs one O(log n) bucket lookup and one indexed membership
    /// test per bound it lists; a leaf conjunct of a fact is itself an
    /// indexed fact, so a bound written inside a conjunction needs no
    /// `extract`. Literal bounds on the goal variables are tried first, so
    /// unrelated relational claims do not crowd out those operands' ranges.
    /// The certificate is planned over the kernel facts before any
    /// of them is spelled, so a goal the bounds do not decide is declined
    /// without surface work.
    pub(in crate::surface::proof) fn try_indexed_signed_arithmetic(
        search_input: &Proof<'a>,
        surfaces: &SurfacePropositionMap,
        anchor: Option<&ProgramPointRef>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_signed_arithmetic");
        let goal = search_input.goal()?;
        let surface_goal = search_input.surface_goal()?;
        let is_pure = matches!(search_input.context.as_ref(), ProofContext::Pure(_));
        // A `uint32` order chain is an atomic derivation over the goal
        // variables' `uint32` bounds (`x <u n`, `n <=u 4`): its recorded
        // order path is closed by Integer arithmetic over the path's
        // premises, the bounds selected here and nothing else.
        if !is_pure
            && crate::surface::checking::is_unsigned_order_goal(goal)
            && let Some(closed) =
                crate::kernel::search::ProofSearch::try_indexed_unsigned_order_chain(
                    search_input,
                    surfaces,
                    anchor,
                    goal,
                )
        {
            return Some(closed);
        }
        // A variable's literal bounds can settle the goal without admitting
        // every earlier relational claim on that variable to the planner's
        // bounded premise slice. Keep that slice local even in a contract
        // with hundreds of independently checked outcomes.
        let mut available =
            indexed_constant_arithmetic_premises(search_input.facts().assumptions(), goal);
        let compact_plan = plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &available)
            .and_then(ArithmeticPlan::signed_int32);
        // If the literal bounds miss, retain the existing relational-bound
        // and equality routes.
        if compact_plan.is_none() {
            available = crate::kernel::search::ProofSearch::indexed_arithmetic_premises(
                search_input,
                goal,
                false,
            )
            .0;
        }
        let plan = if let Some(plan) = compact_plan.or_else(|| {
            plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &available)
                .and_then(ArithmeticPlan::signed_int32)
        }) {
            plan
        } else {
            let (expanded, has_equalities) =
                crate::kernel::search::ProofSearch::indexed_arithmetic_premises(
                    search_input,
                    goal,
                    true,
                );
            // Without a selected equality, the second traversal follows the
            // same bounds graph and cannot change the first planning miss.
            if !has_equalities {
                return None;
            }
            available = expanded;
            plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &available)
                .and_then(ArithmeticPlan::signed_int32)?
        };
        let planned_premises = available.len();
        let mut pairs = Vec::new();
        for fact in available {
            let source = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surfaces,
                anchor,
                &fact,
            )
            .or_else(|| (!is_pure).then(|| search_input.spelled_comparison_surface(&fact))?);
            if let Some(source) = source {
                pairs.push((fact, source));
            }
        }
        let kernels = pairs
            .iter()
            .map(|(fact, _)| fact.clone())
            .collect::<Vec<_>>();
        // Preserve the existing named-rule expansion when these selected
        // bounds support it. Searching this compact context avoids spelling
        // the entire ambient atomic component merely to recover that rule.
        if !is_pure
            && let Some(SolveEvidence::Derivation(derivation)) =
                plan_solve_certificate(goal, &assumptions_from_propositions(&kernels))
            && let Some(closed) =
                crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                    search_input,
                    goal,
                    &derivation,
                    &pairs,
                )
        {
            return Some(closed);
        }
        let plan = if kernels.len() == planned_premises {
            plan
        } else {
            plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &kernels)
                .and_then(ArithmeticPlan::signed_int32)?
        };
        let certificate =
            search_input.signed_plan_to_surface_certificate(&plan, &pairs, surface_goal)?;
        search_input
            .driver()
            .apply_step(ProofStep::ArithmeticCertificate(ArithmeticCertificate {
                family: ArithmeticCertificateFamily::SignedInt32(certificate),
            }))
            .ok()
    }

    /// [`Self::try_indexed_signed_arithmetic`]'s route for a `uint32` order
    /// goal: the goal variables' `uint32` bounds, spelled, and the named
    /// rule or recorded order path a derivation over exactly those selects.
    pub(in crate::surface::proof) fn try_indexed_unsigned_order_chain(
        search_input: &Proof<'a>,
        surfaces: &SurfacePropositionMap,
        anchor: Option<&ProgramPointRef>,
        goal: &Proposition,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_unsigned_order_chain");
        let available = crate::kernel::search::ProofSearch::indexed_arithmetic_premises(
            search_input,
            goal,
            false,
        )
        .0;
        let mut pairs = Vec::new();
        for fact in available {
            let source = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surfaces,
                anchor,
                &fact,
            )
            .or_else(|| search_input.spelled_comparison_surface(&fact));
            if let Some(source) = source {
                pairs.push((fact, source));
            }
        }
        let kernels = pairs
            .iter()
            .map(|(fact, _)| fact.clone())
            .collect::<Vec<_>>();
        let Some(SolveEvidence::Derivation(derivation)) =
            plan_solve_certificate(goal, &assumptions_from_propositions(&kernels))
        else {
            return None;
        };
        crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
            search_input,
            goal,
            &derivation,
            &pairs,
        )
    }

    /// Select only guards actually occurring in the goal, through indexed
    /// fact/source lookups. The emitted simple step checks every selection.
    pub(in crate::surface::proof) fn try_goal_conditional_normalization(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_conditional_normalization");
        // The trusted ambient graph may close an equality without any
        // explicit condition premise. Emit the existing simple checker with
        // an empty input list; no fact search or extra theorem premise is
        // needed, and expansion preserves this exact check.
        if matches!(
            search_input.goal(),
            Some(Proposition::ConditionIs(
                ConditionTerm::PointerEqual(..) | ConditionTerm::PointerValueEqual(..),
                true
            ))
        ) && let Ok(proof) = crate::kernel::search::ProofSearch::apply_normalization_closure(
            search_input,
            Some(Vec::new()),
        ) && proof.is_complete()
        {
            return Some(proof);
        }
        let guards = crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(
            search_input.goal()?,
        );
        let frontier_anchor = match search_input.context.as_ref() {
            ProofContext::Execution(_) if search_input.focused_outcome_data().is_none() => {
                search_input.execution().and_then(frontier_premise_anchor)
            }
            _ => None,
        };
        let (surfaces, anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &search_input.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        // The written goal retains nominal field places that the imported
        // scalar execution expression can spell only as a lowered index.
        // Cite its own conditional guards before reconstructing a premise
        // from execution syntax, so printing preserves that field's type.
        let written_guards = match search_input.surface_goal() {
            Some(ClickProposition::Comparison { left, right, .. }) => [left, right]
                .into_iter()
                .filter_map(|expression| match expression {
                    ContractExpression::If { condition, .. } => Some(condition.as_ref().clone()),
                    _ => None,
                })
                .flat_map(|condition| {
                    [
                        condition.clone(),
                        ClickProposition::Not(Box::new(condition)),
                    ]
                })
                .filter_map(|surface| {
                    let lowered = search_input
                        .lower_surface_proposition_direct(&surface, "conditional goal guard")
                        .ok()?;
                    Some((lowered, surface))
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        };
        let mut premises = Vec::new();
        let mut selected = BTreeSet::new();
        for condition in guards {
            for value in [true, false] {
                let fact = Proposition::ConditionIs(condition.clone(), value);
                if !search_input.facts().contains(&fact)
                    && !condition_polarity_forms(&fact)
                        .iter()
                        .any(|form| search_input.facts().contains(form))
                {
                    continue;
                }
                let surface = written_guards
                    .iter()
                    .find(|(lowered, _)| {
                        *lowered == fact || condition_polarity_equivalent(lowered, &fact)
                    })
                    .map(|(_, surface)| surface.clone())
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            search_input,
                            surfaces,
                            anchor,
                            &fact,
                        )
                    })
                    .or_else(|| {
                        condition_polarity_forms(&fact).iter().find_map(|form| {
                            crate::kernel::search::ProofSearch::available_surface_fact(
                                search_input,
                                surfaces,
                                anchor,
                                form,
                            )
                        })
                    });
                if let Some(surface) = surface
                    && selected.insert(fact)
                {
                    premises.push(surface);
                }
            }
        }
        if premises.is_empty() {
            return None;
        }
        crate::kernel::search::ProofSearch::apply_normalization_closure(
            search_input,
            Some(premises),
        )
        .ok()
        .filter(Proof::is_complete)
    }

    /// Uses one explicitly supplied equality before unfolding applications in
    /// the rewritten goal. Loop preservation supplies its entry invariants in
    /// this list: rewriting through that checked premise first changes a
    /// function-entry comparison into the smaller loop-entry frame that the
    /// defining equation can expose.
    pub(in crate::surface::proof) fn try_introduced_equality_then_function_unfold_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery(
            "try_introduced_equality_then_function_unfold_closure",
        );
        for surface in introduced_surfaces {
            for oriented in
                std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
            {
                let Some(rewritten) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_step(ProofStep::Rewrite(oriented)),
                )?
                else {
                    continue;
                };
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_direct_logical_closure(&(rewritten))?
                {
                    return Ok(Some(closed));
                }
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_function_unfold_solve_closure(
                        &(rewritten),
                        introduced_surfaces,
                    )?
                {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Tries the finite set of function applications already present in the
    /// current surface goal. Each accepted candidate is a normal checked
    /// `unfold` step. The recursive simplification attempt disables further
    /// function unfolding, so recursive definitions cannot turn this smart
    /// tactic into unbounded evaluation.
    pub(in crate::surface::proof) fn try_function_unfold_solve_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_function_unfold_solve_closure");
        // The structural closer introduces these binders and searches their
        // bodies with the guard or fresh variable available. Unfolding the
        // whole binder would repeat that same search for every candidate.
        if matches!(
            search_input.goal(),
            Some(Proposition::Implies(..) | Proposition::ForAll { .. })
        ) {
            return Ok(None);
        }
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::FunctionUnfold) else {
            return Ok(None);
        };
        let Some(surface_goal) = search_input.surface_goal() else {
            return Ok(None);
        };
        let applications =
            pure_theorems::click_function_applications(surface_goal, introduced_surfaces);
        if applications.is_empty() {
            return Ok(None);
        }
        let mut unfolded_any = false;
        let mut proof = search_input.clone();
        for application in applications {
            let attempted = proof
                .driver()
                .apply_step(ProofStep::UnfoldFunction(application));
            let Some(unfolded) = attempt::candidate_outcome(attempted)? else {
                continue;
            };
            proof = unfolded;
            unfolded_any = true;
            // The unfold can close the goal itself: the refreshed goal may
            // already be an available fact, which leaves no goal to search.
            if proof.is_complete() {
                return Ok(Some(proof));
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))?
            {
                return Ok(Some(closed));
            }
            // A recursive definition over a known constructor exposes its
            // recursive call on a smaller argument. Evaluate those calls to a
            // fixed fuel before searching.
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_constructor_evaluation_closure(
                    &(proof),
                    introduced_surfaces,
                )?
            {
                return Ok(Some(closed));
            }
            if let Some(closed) = crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces_and_function_unfold(&(proof),
                    false,
                    introduced_surfaces,
                    false,
                )?
            {
                return Ok(Some(closed));
            }
        }
        // No application unfolds as it stands, as when its argument is a
        // variable a fact equates to a constructor: evaluate from a rewrite.
        if !unfolded_any {
            return crate::kernel::search::ProofSearch::try_constructor_evaluation_closure(
                search_input,
                introduced_surfaces,
            );
        }
        Ok(None)
    }

    /// Evaluate a goal's recursive applications over known constructors, at
    /// most `CONSTRUCTOR_EVALUATION_FUEL` checked steps. Each step is the
    /// first that applies of: an `unfold` of an application in the goal
    /// (which the kernel accepts only when its argument selects one
    /// definition arm), or a `rewrite` by a supplied equation whose right
    /// side is a constructor, exposing one for the next unfold. There is no
    /// branching: one candidate per step, and the goal is checked for
    /// closure after each. Nothing is kept unless the goal closes.
    pub(in crate::surface::proof) fn try_constructor_evaluation_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_constructor_evaluation_closure");
        // A fact recorded at a program point keeps its anchor, `at(p, s) ==
        // at(p, Shape::Circle(r))`; the anchored constructor is still one.
        let is_constructor_equation = |surface: &ClickProposition| {
            let ClickProposition::Comparison {
                operator: ComparisonOperator::Equal,
                right,
                ..
            } = surface
            else {
                return false;
            };
            let mut right = right;
            while let ContractExpression::At { expression, .. } = right {
                right = expression;
            }
            matches!(right, ContractExpression::AlgebraicConstructor { .. })
        };
        let mut constructor_equations: Vec<ClickProposition> = introduced_surfaces
            .iter()
            .filter(|surface| is_constructor_equation(surface))
            .cloned()
            .collect();
        let mut fact_equations_gathered = false;
        let mut proof = search_input.clone();
        for _ in 0..CONSTRUCTOR_EVALUATION_FUEL {
            check_verification_deadline()?;
            let Some(surface_goal) = proof.surface_goal() else {
                return Ok(None);
            };
            let mut next = None;
            for application in pure_theorems::click_function_applications(surface_goal, &[]) {
                if let Some(unfolded) = attempt::candidate_outcome(
                    proof
                        .driver()
                        .apply_step(ProofStep::UnfoldFunction(application)),
                )? {
                    next = Some(unfolded);
                    break;
                }
            }
            if next.is_none() && !fact_equations_gathered {
                // A constructor equation among the facts connected to the
                // goal, such as a requirement `u == Tree::Node(..)`, read
                // once and only when nothing supplied applies.
                fact_equations_gathered = true;
                if let Some(goal) = proof.goal()
                    && let Some(equalities) =
                        crate::kernel::search::proposition_search::connected_equalities(
                            proof.facts().assumptions(),
                            goal,
                        )
                {
                    for equality in equalities.iter().take(CONSTRUCTOR_EVALUATION_FACTS) {
                        if let Some((_, surface)) =
                            crate::kernel::search::ProofSearch::resolve_solve_premises(
                                &(proof),
                                std::slice::from_ref(equality),
                                &[],
                            )
                            .and_then(|mut spelled| spelled.pop())
                            && is_constructor_equation(&surface)
                            && !constructor_equations.contains(&surface)
                        {
                            constructor_equations.push(surface);
                        }
                    }
                }
            }
            if next.is_none() {
                for equation in &constructor_equations {
                    if let Some(rewritten) = attempt::candidate_outcome(
                        proof
                            .driver()
                            .apply_step(ProofStep::Rewrite(equation.clone())),
                    )? && rewritten.surface_goal() != proof.surface_goal()
                    {
                        next = Some(rewritten);
                        break;
                    }
                }
            }
            let Some(next) = next else {
                return Ok(None);
            };
            proof = next;
            if proof.is_complete() {
                return Ok(Some(proof));
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Splits one atomic goal at the final index licensed by an available
    /// upper bound. Selection happens over recorded Surface facts, and the
    /// result is an ordinary checked proof `if`: the then arm learns
    /// `variable < pivot`, while the else arm derives equality from the same
    /// bound and the exact negated branch fact through normal theorem search.
    ///
    /// Once either polarity of the proposed condition is available, the
    /// candidate is no longer a split. That structural fact is what makes
    /// recursive closure terminate inside both arms; no search-depth guard or
    /// hidden kernel recursion participates.
    pub(in crate::surface::proof) fn try_upper_bound_split_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_upper_bound_split_closure");
        // Each arm of a split runs the whole closure, which reaches this
        // split again on the next bound. Along a chain `x0 <= x1 <= ...`
        // that recursion followed every bound, so a goal no split decides
        // cost closure runs linear in the chain. Nest a fixed number.
        let Some(_scope) = UpperBoundSplitScope::enter() else {
            return Ok(None);
        };
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        if matches!(
            goal,
            Proposition::And(_, _)
                | Proposition::Or(_, _)
                | Proposition::Implies(_, _)
                | Proposition::ForAll { .. }
                | Proposition::Exists { .. }
        ) {
            return Ok(None);
        }
        let mut goal_variables = crate::kernel::proposition_variables(goal);
        if let Some(surface_goal) = search_input.surface_goal() {
            let mut surface_names = BTreeSet::new();
            collect_current_proposition_variables(surface_goal, &mut surface_names);
            for name in surface_names {
                let expression =
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(name));
                let probe = ClickProposition::Comparison {
                    left: expression.clone(),
                    operator: ComparisonOperator::Equal,
                    right: expression,
                };
                if let Ok(kernel) =
                    search_input.lower_surface_proposition(&probe, "upper-bound goal variable")
                {
                    goal_variables.extend(crate::kernel::proposition_variables(&kernel));
                }
            }
        }
        if goal_variables.is_empty() {
            return Ok(None);
        }

        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => {
                if let Some(data) = search_input.focused_outcome_data() {
                    (&data.surface_propositions, data.premise_anchor.as_ref())
                } else {
                    let Some(execution) = search_input.execution() else {
                        return Ok(None);
                    };
                    frontier_anchor = frontier_premise_anchor(execution);
                    (
                        &execution.presentation.surface_propositions,
                        frontier_anchor.as_ref(),
                    )
                }
            }
        };

        // An introduced implication guard is the nearest and smallest source
        // of the bound in the quantified-extension shape. Prefer those named
        // facts so ordinary closure does not clone and probe the ambient fact
        // set at every atomic leaf. Fall back to ambient facts only when no
        // introduced bound can concern this goal.
        let mut bound_sources = introduced_surfaces
            .iter()
            .filter_map(|surface| {
                let bound = search_input
                    .lower_surface_proposition(surface, "introduced upper bound")
                    .ok()?;
                let (variable, _) = kernel_upper_bound_split_candidate(&bound)?;
                goal_variables
                    .contains(&variable)
                    .then(|| (bound, Some(surface.clone())))
            })
            .collect::<Vec<_>>();
        if bound_sources.is_empty() {
            // Read each goal variable's bounds from its indexed bucket; a
            // scan of every fact for the few that bound these variables
            // costs work in the whole context at each atomic leaf.
            let mut seen = BTreeSet::new();
            for variable in &goal_variables {
                for (endpoint, other, strict, forward) in search_input
                    .facts()
                    .assumptions()
                    .signed_order_bound_entries(&MachineTerm::Variable(*variable))
                {
                    let (left, right) = if forward {
                        (endpoint, other)
                    } else {
                        (other, endpoint)
                    };
                    let condition = if strict {
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessThan,
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    } else {
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessEqual,
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    };
                    let fact = Proposition::ConditionIs(condition, true);
                    for bound in
                        std::iter::once(fact.clone()).chain(condition_polarity_forms(&fact))
                    {
                        if search_input.facts().contains(&bound)
                            && kernel_upper_bound_split_candidate(&bound)
                                .is_some_and(|(bounded, _)| goal_variables.contains(&bounded))
                            && seen.insert(bound.clone())
                        {
                            bound_sources.push((bound, None));
                        }
                    }
                }
            }
        }
        let candidates = bound_sources
            .into_iter()
            .filter_map(|(bound, introduced_surface)| {
                let (variable, pivot) = kernel_upper_bound_split_candidate(&bound)?;
                let pivot_probe = Proposition::Equal(
                    Term::Integer(crate::kernel::IntegerTerm::Machine(pivot.clone())),
                    Term::Integer(crate::kernel::IntegerTerm::Machine(pivot.clone())),
                );
                if crate::kernel::proposition_variables(&pivot_probe).contains(&variable) {
                    return None;
                }
                let bound_surface = introduced_surface.or_else(|| {
                    crate::kernel::search::ProofSearch::available_surface_fact(
                        search_input,
                        surface_facts,
                        premise_anchor,
                        &bound,
                    )
                })?;
                let split_kernel = Proposition::ConditionIs(
                    crate::kernel::machine_integer::comparison::condition_for_operand_views(
                        MachineIntegerType::Int32,
                        CompareRelation::LessThan,
                        [
                            crate::kernel::MachineOperandView::Legacy(&MachineTerm::Variable(
                                variable,
                            )),
                            pivot.operand_view(),
                        ],
                    ),
                    true,
                );
                let direct = surface_upper_bound_direct_condition(&bound_surface)?;
                let direct_surface = std::iter::once(direct.clone())
                    .chain(
                        search_input
                            .premise_fixed_state_view()
                            .into_iter()
                            .flat_map(|view| {
                                view.fixed_state
                                    .recorded_states
                                    .recent(MAX_TRANSPORT_SOURCE_POINTS)
                                    .into_iter()
                                    .filter_map(|(selector, _)| {
                                        surface_at_program_point(&direct, selector).ok()
                                    })
                                    .collect::<Vec<_>>()
                            }),
                    )
                    .find(|surface| {
                        search_input
                            .lower_surface_proposition(surface, "upper-bound premise")
                            .is_ok_and(|lowered| {
                                crate::kernel::proof::fact_reasoning::order_claim_equivalent(
                                    &lowered, &bound,
                                )
                            })
                    })?;
                let mut surface_candidates = vec![
                    surface_upper_bound_split_condition(&bound_surface)?,
                    direct.clone(),
                ];
                if let Some(view) = search_input.premise_fixed_state_view() {
                    surface_candidates.extend(
                        view.fixed_state
                            .recorded_states
                            .recent(MAX_TRANSPORT_SOURCE_POINTS)
                            .into_iter()
                            .filter_map(|(selector, _)| {
                                surface_at_program_point(&direct, selector).ok()
                            }),
                    );
                }
                let split_surface = surface_candidates.into_iter().find(|surface| {
                    search_input
                        .lower_surface_proposition(surface, "upper-bound split condition")
                        .is_ok_and(|lowered| {
                            crate::kernel::proof::fact_reasoning::order_claim_equivalent(
                                &lowered,
                                &split_kernel,
                            )
                        })
                })?;
                let split_negation = ClickProposition::Not(Box::new(split_surface.clone()));
                if introduced_surfaces
                    .iter()
                    .any(|surface| surface == &split_surface || surface == &split_negation)
                    || condition_polarity_forms(&split_kernel)
                        .iter()
                        .any(|form| search_input.facts().contains(form))
                {
                    return None;
                }
                Some((split_surface, direct_surface, pivot))
            })
            .collect::<Vec<_>>();
        for (condition, direct_bound, pivot) in candidates {
            let (split_proof, split, ids) = search_input.split_focused_if(condition.clone())?;
            let marker = split_proof.checkpoint();
            let mut then_surfaces = introduced_surfaces.to_vec();
            then_surfaces.push(condition.clone());
            let then_branch = split_proof.focus_branch(ids[0])?;
            let disequality = surface_split_disequality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let disequality_scope = then_branch.driver().open_have(disequality.clone())?;
            let disequality_done = (disequality_scope)
                .driver()
                .try_solve_closure_with_surfaces(&then_surfaces)?;
            let Some(disequality_done) = disequality_done else {
                continue;
            };
            let then_branch = disequality_done.join()?;
            then_surfaces.push(disequality);
            let Some(then_done) =
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &(then_branch),
                    &then_surfaces,
                )?
            else {
                continue;
            };
            let negated = ClickProposition::Not(Box::new(condition.clone()));
            let mut else_surfaces = introduced_surfaces.to_vec();
            else_surfaces.push(negated.clone());
            let equality = surface_split_equality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let nonstrict = surface_split_nonstrict_bound(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let else_branch = then_done.focus_branch(ids[1])?;
            let equality_scope = else_branch.driver().open_have(equality.clone())?;
            let nonstrict_scope = equality_scope.driver().open_have(nonstrict.clone())?;
            let nonstrict_done = nonstrict_scope
                .driver()
                .try_solve_closure_with_surfaces(&else_surfaces)?
                .or_else(|| {
                    // `x < pivot + 1` gives `x <= pivot` by arithmetic once
                    // `pivot + 1` is known not to wrap; a direct bound of
                    // the form `x <= pivot` needs nothing more.
                    std::iter::once(None)
                        .chain(
                            crate::kernel::search::ProofSearch::increment_headroom_premises(
                                search_input,
                                pivot.structural_value(),
                                surface_facts,
                                premise_anchor,
                            )
                            .into_iter()
                            .map(Some),
                        )
                        .find_map(|headroom| {
                            let premises = std::iter::once(direct_bound.clone())
                                .chain(headroom)
                                .collect();
                            nonstrict_scope
                                .driver()
                                .apply_step(ProofStep::ArithmeticUsing(premises))
                                .ok()
                        })
                });
            let Some(nonstrict_done) = nonstrict_done else {
                continue;
            };
            let equality_scope = equality_scope.join_nested(nonstrict_done)?;
            else_surfaces.push(nonstrict);
            let Some(equality_done) = (equality_scope)
                .driver()
                .try_solve_closure_with_surfaces(&else_surfaces)?
            else {
                continue;
            };
            let else_branch = equality_done.join()?;
            else_surfaces.push(equality.clone());
            let rewritten_surface_goal =
                surface_strict_parts(&condition).and_then(|(left, right)| {
                    let ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) =
                        left
                    else {
                        return None;
                    };
                    substitute_click_proposition(
                        else_branch.surface_goal()?,
                        &std::iter::once((name, right)).collect(),
                    )
                    .ok()
                });
            let transported_else = else_branch
                .surface_goal()
                .and_then(old_reflexive_transport_source)
                .and_then(|source| {
                    crate::kernel::search::ProofSearch::try_planned_execution_proposition_fact_transport(&(else_branch),
                            &source,
                            else_branch.surface_goal()?,
                        )
                        .ok()
                        .flatten()
                })
                .filter(Proof::focused_discharged);
            let rewritten_else = match else_branch
                .driver()
                .apply_step(ProofStep::Rewrite(equality.clone()))
            {
                Ok(rewritten) if rewritten.focused_discharged() => Some(rewritten),
                Ok(rewritten) => {
                    let transported = rewritten_surface_goal
                        .as_ref()
                        .and_then(old_reflexive_transport_source)
                        .and_then(|source| {
                            crate::kernel::search::ProofSearch::try_planned_execution_proposition_fact_transport(&(rewritten),
                                    &source,
                                    rewritten_surface_goal.as_ref()?,
                                )
                                .ok()
                                .flatten()
                        })
                        .filter(Proof::focused_discharged);
                    if transported.is_some() {
                        transported
                    } else {
                        crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                            &(rewritten),
                            &else_surfaces,
                        )?
                    }
                }
                Err(_) => None,
            };
            let else_done = if transported_else.is_some() {
                transported_else
            } else if rewritten_else.is_some() {
                rewritten_else
            } else {
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &(else_branch),
                    &else_surfaces,
                )?
            };
            let Some(else_done) = else_done else {
                continue;
            };
            return else_done
                .join_focused_if(&marker, split, ids, condition)
                .map(Some);
        }
        Ok(None)
    }

    /// Proves a two-edge non-strict outcome bound at the return entry or its
    /// immediate predecessor. Outcome lowering deliberately keeps selected
    /// premises in their source form; anchoring those exact premises at
    /// the execution boundary lets the ordinary theorem checker connect a
    /// returned local to its result without consulting the retired planner.
    pub(in crate::surface::proof) fn try_outcome_anchored_order_transitivity(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_outcome_anchored_order_transitivity");
        let data = search_input.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Region(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Region(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let ordered = premise_pairs
                .iter()
                .filter_map(|(_, surface)| {
                    let anchored = surface_at_program_point(surface, anchor).ok()?;
                    let parts = surface_nonstrict_parts(&anchored)?;
                    Some((anchored, parts))
                })
                .collect::<Vec<_>>();
            for (first_surface, (first, middle)) in &ordered {
                for (second_surface, (second_middle, last)) in &ordered {
                    if middle != second_middle {
                        continue;
                    }
                    // `last >= first`, the composed order at the anchor.
                    let composed = ClickProposition::Comparison {
                        left: last.clone(),
                        operator: ComparisonOperator::GreaterEqual,
                        right: first.clone(),
                    };
                    let Ok(applied) = search_input.driver().have_by_integer_arithmetic(
                        composed,
                        vec![second_surface.clone(), first_surface.clone()],
                    ) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    if let Some(closed) =
                        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                            .ok()
                            .flatten()
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Proves an outcome increment bound at the return entry or its immediate
    /// predecessor. The latter is the assignment boundary that can connect a
    /// named return local to the increment expression. The two propositions
    /// come only from the atomic derivation's selected requirements; the
    /// ordinary theorem, nested-`have`, and `known` checkers decide whether
    /// either constant-size historical application establishes the current
    /// result-aware goal.
    pub(in crate::surface::proof) fn try_outcome_anchored_increment_order(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_outcome_anchored_increment_order");
        let data = search_input.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Region(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Region(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        let surface_goal = search_input.surface_goal()?.clone();
        surface_nonstrict_parts(&surface_goal)?;
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let mut lower_bounds = Vec::new();
            let mut upper_bounds = Vec::new();
            for (kernel, surface) in premise_pairs {
                let anchored = surface_at_program_point(surface, anchor).ok()?;
                if let Some(parts) = surface_nonstrict_parts(&anchored) {
                    lower_bounds.push((
                        anchored.clone(),
                        parts,
                        signed_nonstrict_parts(kernel).map(|(_, value)| value),
                    ));
                }
                if let Some(parts) = surface_strict_parts(&anchored) {
                    upper_bounds.push((
                        anchored,
                        parts,
                        signed_strict_parts(kernel).map(|(value, _)| value),
                    ));
                }
            }
            for (lower_surface, (surface_lower, lower_value), lower_kernel) in &lower_bounds {
                for (upper_surface, (upper_value, _), upper_kernel) in &upper_bounds {
                    // Entry requirements and resource observations can spell
                    // the same checked value at different states. Select
                    // by the kernel endpoint as well as identical syntax;
                    // ApplyTheoremUsing still validates both named premises
                    // and the result at the chosen historical boundary.
                    if lower_value != upper_value
                        && !(lower_kernel.is_some() && lower_kernel == upper_kernel)
                    {
                        continue;
                    }
                    // `lower + 1 <= value + 1`, the order of the two machine
                    // sums, written as the comparison of their exact
                    // observations: outside `to_integer`, a written `+` is
                    // Integer addition.
                    let one =
                        ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1)));
                    let observed_sum = |base: &ContractExpression| ContractExpression::Call {
                        name: "to_integer".to_string(),
                        arguments: vec![ContractExpression::Add(
                            Box::new(base.clone()),
                            Box::new(one.clone()),
                        )],
                    };
                    let theorem_conclusion = ClickProposition::Comparison {
                        left: observed_sum(surface_lower),
                        operator: ComparisonOperator::LessEqual,
                        right: observed_sum(lower_value),
                    };
                    let Ok(applied) = search_input.driver().have_by_integer_arithmetic(
                        theorem_conclusion.clone(),
                        vec![lower_surface.clone(), upper_surface.clone()],
                    ) else {
                        continue;
                    };
                    if let Some(closed) = applied
                        .driver()
                        .apply_step(ProofStep::TransportUsing {
                            source: theorem_conclusion,
                            target: surface_goal.clone(),
                            premises: Vec::new(),
                        })
                        .ok()
                        .or_else(|| {
                            crate::kernel::search::ProofSearch::try_direct_logical_closure(
                                &(applied),
                            )
                            .ok()
                            .flatten()
                        })
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Tries the focused branch goal itself as one explicit fact transport from a
    /// recorded program point. This also applies to proposition scopes opened
    /// mid-execution, such as loop-invariant initialization and preservation.
    /// The candidate space is the execution's
    /// recorded-state index, not the ambient fact set; every accepted source
    /// and target is checked by `TransportUsing` on this immutable Proof.
    pub(in crate::surface::proof) fn try_state_transport_closure(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_state_transport_closure");
        if super::selected_arithmetic::machine_equality_bridge_active() {
            return Ok(None);
        }
        // Every candidate below lowers the same goal, so a failing question
        // about the goal's own loads repeats per candidate; remember those
        // failures for this closure (`with_closure_failure_memo`).
        crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: state transport",
            || {
                crate::kernel::with_closure_failure_memo(|| {
                    crate::kernel::search::ProofSearch::try_state_transport_closure_candidates(
                        search_input,
                        surface_goal,
                    )
                })
            },
        )
    }

    pub(in crate::surface::proof) fn try_state_transport_closure_candidates(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_state_transport_closure_candidates");
        if let Some(proof) = crate::kernel::search::ProofSearch::try_cell_frame_transport_closure(
            search_input,
            surface_goal,
        )? {
            return Ok(Some(proof));
        }
        // Outcome transport is a general closure. Extending it to fixed-state
        // and mid-execution proposition scopes is needed for opaque Click
        // applications, whose state arguments cannot be refreshed by
        // ordinary field rewrites, and for goals that read memory: a read
        // written through one alias of a cell whose fact was stated through
        // another, before a store the alias shows separate, is carried here
        // rather than renamed by lowering (lowering is fact-stable,
        // `docs/internals/spellability.md`). Other goals keep their more
        // local rewrite plans.
        if search_input.outcome_fixed_state_view().is_none() {
            let mut calls = BTreeSet::new();
            crate::surface::validation::collect_click_function_calls_in_proposition(
                surface_goal,
                &mut calls,
            );
            let reads_memory = search_input.goal().is_some_and(|goal| {
                crate::kernel::proposition_mentions_load_variable(goal)
                    || crate::kernel::proof::term_rewrite::proposition_pointer_terms(goal)
                        .iter()
                        .any(|pointer| matches!(pointer.block, PointerBlock::LoadedPointer(_)))
            });
            if calls.is_empty() && !reads_memory {
                return Ok(None);
            }
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        if let Some(source) = old_reflexive_transport_source(surface_goal) {
            if search_input.execution_proposition_fixed_state_view().is_some()
                && let Some(proof) =
                    crate::kernel::search::ProofSearch::try_planned_execution_proposition_fact_transport(search_input, &source, surface_goal)?
                && proof.is_complete()
            {
                return Ok(Some(proof));
            }
            match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                search_input,
                &source,
                surface_goal,
                std::iter::empty(),
            ) {
                Ok(Some(proof)) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        // A goal about `result` exists only once the function has returned,
        // so its first source is function exit rather than entry, and no
        // recorded point before the return is offered.
        let names_result = crate::surface::proposition_names_result(surface_goal);
        let first = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: if names_result {
                ProgramPointKind::Exit
            } else {
                ProgramPointKind::Entry
            },
        };
        // The source points are that function point and the most recently
        // recorded ones, newest first. A path records a point per statement
        // it ran, so offering every one made this search linear in the
        // path's length for each goal, and quadratic over a function's
        // early-return paths. An older point is still reachable by an
        // explicit `transport`.
        let selectors = std::iter::once(ProgramPointSelector::ProgramPoint(first)).chain(
            view.fixed_state
                .recorded_states
                .recent(MAX_TRANSPORT_SOURCE_POINTS)
                .into_iter()
                .map(|(selector, _)| selector.clone()),
        );
        let mut tried = BTreeSet::new();
        for selector in selectors {
            if (names_result && !crate::surface::program_point_can_name_result(Some(&selector)))
                || !tried.insert(selector.clone())
            {
                continue;
            }
            let source = ClickProposition::At {
                selector,
                proposition: Box::new(surface_goal.clone()),
            };
            match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                search_input,
                &source,
                surface_goal,
                std::iter::once(source.clone()),
            ) {
                Ok(Some(proof)) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
            if let Some(proof) = crate::kernel::search::ProofSearch::try_projected_state_transport(
                search_input,
                &source,
                surface_goal,
            )? {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    /// A guarded universal goal whose recorded-point form is held only as
    /// the conjunct of a larger guarded universal there, such as
    /// `forall k { k < n implies p[k] == v }` from a call's
    /// `forall k { k < n implies defined(p[k]) and p[k] == v }`. The larger
    /// fact is selected by one probe of the indexed conjunct projections
    /// (`ProofFacts::quantified_conjunct_projection_source`) with the goal
    /// lowered at that point, so a point holding no such fact costs one
    /// lowering and one lookup. The proof is one explicit transport from
    /// the larger fact to the goal, which the checked quantified frame
    /// decides by conjunction elimination; expansion prints it.
    pub(in crate::surface::proof) fn try_projected_state_transport(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_projected_state_transport");
        let Ok(lowered) = search_input
            .lower_surface_proposition_direct(source, "smart projected transport source")
        else {
            check_verification_deadline()?;
            return Ok(None);
        };
        let Some(full) = search_input
            .facts()
            .quantified_conjunct_projection_source(&lowered)
        else {
            return Ok(None);
        };
        let full = full.clone();
        let Some(full_surface) = crate::kernel::search::ProofSearch::resolve_solve_premises(
            search_input,
            std::slice::from_ref(&full),
            &[],
        )
        .and_then(|pairs| pairs.into_iter().next())
        .map(|(_, surface)| surface) else {
            return Ok(None);
        };
        match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
            search_input,
            &full_surface,
            surface_goal,
            std::iter::once(full_surface.clone()),
        ) {
            Ok(Some(proof)) if proof.is_complete() => Ok(Some(proof)),
            Ok(_) => Ok(None),
            Err(_) => {
                check_verification_deadline()?;
                Ok(None)
            }
        }
    }

    /// A goal that reads one cell at two states, such as
    /// `owner->cell[0] == owner->phase` right after a store wrote the first
    /// side from the second, holds when nothing in between wrote that cell.
    /// That is a frame fact: carry the cell's reflexive equality from a
    /// recorded point to the goal by `transport`, whose checker takes the
    /// frame evidence (an exact `separate`, say) as its listed premises.
    pub(in crate::surface::proof) fn try_cell_frame_transport_closure(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_cell_frame_transport_closure");
        let Some(Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = search_input.goal()
        else {
            return Ok(None);
        };
        let load = |term: &MachineTerm| match term {
            MachineTerm::Variable(variable) => {
                crate::kernel::registered_load_term_for_variable(variable)
            }
            MachineTerm::MemoryLoad(..) => Some(term.clone()),
            _ => None,
        };
        let (
            Some(MachineTerm::MemoryLoad(left_memory, left_pointer, left_kind)),
            Some(MachineTerm::MemoryLoad(right_memory, right_pointer, right_kind)),
        ) = (load(left), load(right))
        else {
            return Ok(None);
        };
        if left_pointer != right_pointer || left_kind != right_kind || left_memory == right_memory {
            return Ok(None);
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        // The cell as the current state reads it.
        let current = crate::kernel::intern_memory_ref(view.fixed_state.state.memory());
        let current_side = if right_memory == current {
            right
        } else if left_memory == current {
            left
        } else {
            return Ok(None);
        };
        let Some(cell) = super::surface_synthesis::synthesize_surface_machine_expression(
            current_side,
            view.parameter_binding,
            view.fixed_state.state,
        ) else {
            return Ok(None);
        };
        let reflexive = ClickProposition::Comparison {
            left: cell.clone(),
            operator: ComparisonOperator::Equal,
            right: cell,
        };
        let selectors = view
            .fixed_state
            .recorded_states
            .recent(MAX_TRANSPORT_SOURCE_POINTS)
            .into_iter()
            .map(|(selector, _)| selector.clone())
            .collect::<Vec<_>>();
        for selector in selectors {
            let source = ClickProposition::At {
                selector,
                proposition: Box::new(reflexive.clone()),
            };
            match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                search_input,
                &source,
                surface_goal,
                std::iter::empty(),
            ) {
                Ok(Some(proof)) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => check_verification_deadline()?,
            }
        }
        Ok(None)
    }

    /// Close an implication whose algebraic guard is refuted by a checked
    /// rewrite and direct normalization. A miss does not run general solve on
    /// the guard or select the implication's connected fact component.
    pub(in crate::surface::proof) fn try_constructor_guard_refutation(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_constructor_guard_refutation");
        let Some(Proposition::Implies(guard, _)) = search_input.goal() else {
            return Ok(None);
        };
        let comparison = match guard.as_ref() {
            Proposition::Not(body) => body.as_ref(),
            guard => guard,
        };
        if !matches!(
            comparison,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        ) {
            return Ok(None);
        }
        let Some(antecedent) = search_input
            .surface_goal()
            .and_then(surface_implication_antecedent)
        else {
            return Ok(None);
        };
        let opposite = negate_click_proposition(&antecedent);
        let Some(scope) =
            attempt::candidate_outcome(search_input.driver().open_have(opposite.clone()))?
        else {
            return Ok(None);
        };
        let Some(proved) = (scope).driver().try_direct_model_equality_rewrite_closure() else {
            check_verification_deadline()?;
            return Ok(None);
        };
        let Some(joined) = attempt::candidate_outcome(proved.join())? else {
            return Ok(None);
        };
        let Some(introduced) =
            attempt::candidate_outcome(joined.driver().apply_step(ProofStep::Intro))?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(
            introduced
                .driver()
                .apply_step(ProofStep::Contradiction(opposite)),
        )
    }

    // Walk consecutive implication guards without retaining a dispatcher
    // frame for each. Each guard keeps its checked introduction, contradiction
    // probes, and named-premise extraction before the body is simplified.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_implication_solve_closure(
        search_input: &Proof<'a>,
        surface_antecedent: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_implication_solve_closure");
        let mut base = search_input.clone();
        let mut antecedent = surface_antecedent.clone();
        let mut available_surfaces = introduced_surfaces.to_vec();
        loop {
            let Some(mut introduced) =
                attempt::candidate_outcome(base.driver().apply_step(ProofStep::Intro))?
            else {
                return Ok(None);
            };
            // The introduced antecedent itself is the uniquely selected
            // contradiction candidate. This is a constant-size probe:
            // `Contradiction` checks that exact fact and its indexed
            // opposite, without scanning ambient path facts.
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_introduced_antecedent_contradiction(
                    &(introduced),
                    &antecedent,
                )?
            {
                return Ok(Some(closed));
            }
            // A selected execution path can make the antecedent false through a
            // short derivation rather than an already-indexed exact opposite.
            // Prove and retain that opposite first; after `intro`, ordinary
            // contradiction checks the two explicit facts.
            let negated_antecedent = negate_click_proposition(&antecedent);
            if let Some(scope) =
                attempt::candidate_outcome(base.driver().open_have(negated_antecedent.clone()))?
                && let Some(proved) = (scope).driver().try_solve_closure()?
                && let Some(with_opposite) = attempt::candidate_outcome(proved.join())?
                && let Some(with_antecedent) =
                    attempt::candidate_outcome(with_opposite.driver().apply_step(ProofStep::Intro))?
                && let Some(closed) = attempt::candidate_outcome(
                    with_antecedent
                        .driver()
                        .apply_step(ProofStep::Contradiction(negated_antecedent)),
                )?
            {
                return Ok(Some(closed));
            }
            let mut conjuncts = Vec::new();
            if matches!(&antecedent, ClickProposition::And(_, _)) {
                collect_surface_conjunct_leaves(&antecedent, &mut conjuncts);
            }
            for conjunct in &conjuncts {
                let Some(extracted) = attempt::candidate_outcome(
                    introduced
                        .driver()
                        .apply_step(ProofStep::Extract(conjunct.clone())),
                )?
                else {
                    return Ok(None);
                };
                introduced = extracted;
                if introduced.is_complete() {
                    return Ok(Some(introduced));
                }
                // Each conjunct is probed as a curried antecedent would be:
                // `a and b implies c` closes where `a implies b implies c`
                // does, when the facts hold a conjunct's exact opposite.
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_introduced_antecedent_contradiction(
                        &(introduced),
                        conjunct,
                    )?
                {
                    return Ok(Some(closed));
                }
            }
            available_surfaces.push(antecedent.clone());
            available_surfaces.extend(conjuncts.iter().cloned());
            // Introducing this guard can make a previously introduced
            // conditional premise usable. Select its written consequent
            // and let the ordinary checked `extract` rule discharge the
            // guard; do not branch over possible guard values.
            for premise in available_surfaces.clone() {
                let mut current = &premise;
                while let ClickProposition::Implies(_, consequent) = current {
                    let Some(extracted) = attempt::candidate_outcome(
                        introduced
                            .driver()
                            .apply_step(ProofStep::Extract(consequent.as_ref().clone())),
                    )?
                    else {
                        break;
                    };
                    introduced = extracted;
                    available_surfaces.push(consequent.as_ref().clone());
                    if introduced.is_complete() {
                        return Ok(Some(introduced));
                    }
                    current = consequent;
                }
            }
            if !conjuncts.is_empty()
                && let Some(surface_goal) = introduced.surface_goal()
                && let Some(source) = old_reflexive_transport_source(surface_goal)
            {
                match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                    &(introduced),
                    &source,
                    surface_goal,
                    conjuncts.iter().cloned(),
                ) {
                    Ok(Some(transported)) if transported.is_complete() => {
                        return Ok(Some(transported));
                    }
                    Ok(_) => {}
                    Err(_) => check_verification_deadline()?,
                }
            }
            if let Some(split) = crate::kernel::search::ProofSearch::try_upper_bound_split_closure(
                &(introduced),
                &available_surfaces,
            )? {
                return Ok(Some(split));
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(introduced))?
            {
                return Ok(Some(closed));
            }
            if matches!(introduced.goal(), Some(Proposition::Implies(_, _)))
                && let Some(next) = introduced
                    .surface_goal()
                    .and_then(surface_implication_antecedent)
            {
                base = introduced;
                antecedent = next;
                continue;
            }
            return crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                &(introduced),
                &available_surfaces,
            );
        }
    }

    /// Compare the written descriptors with recorded separation facts. Each
    /// proposed equality is applied by ordinary rewrite; there is no call to
    /// solve or transport inside the candidate proof. The tactic work budget
    /// bounds selection, and at most sixteen separation facts are attempted.
    pub(in crate::surface::proof) fn try_resource_descriptor_rewrite_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_resource_descriptor_rewrite_closure");
        let Some(target @ ClickProposition::Separate { .. }) = search_input.surface_goal() else {
            return Ok(None);
        };
        let Some(surfaces) = search_input.premise_surface_facts() else {
            return Ok(None);
        };
        let mut attempts = 0;
        for kernel in surfaces.requirement_kernel_atoms_for_search() {
            check_verification_deadline()?;
            if !matches!(kernel, Proposition::ResourceSeparate { .. }) {
                continue;
            }
            if attempts == 16 {
                break;
            }
            attempts += 1;
            let mut source = surfaces
                .recorded_requirement_surface(kernel)
                .expect("requirement atoms retain their enclosing source clause");
            while let ClickProposition::At { proposition, .. } = source {
                source = proposition;
            }
            let Some(steps) = resource_descriptor_rewrite_steps(target, source) else {
                continue;
            };
            let mut candidate = Some(search_input.clone());
            for step in steps {
                let Some(proof) = candidate.take() else {
                    break;
                };
                candidate = attempt::candidate_outcome(proof.driver().apply_step(step))?;
            }
            if let Some(proof) = candidate
                && (proof.focused_discharged() || proof.is_complete())
            {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    /// Search chooses enclosing separated regions; replay cites containment
    /// and the ordinary restriction law. No store invokes this planner.
    pub(in crate::surface::proof) fn try_resource_separation_restriction_closure(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_resource_separation_restriction_closure");
        let ClickProposition::Separate { left, right } = surface_goal else {
            return Ok(None);
        };
        let Some(mut kernel_goal) = search_input.goal() else {
            return Ok(None);
        };
        // Resource lowering appends formation conditions to the stated fact.
        // Planning retains and proves the complete Surface goal below.
        while let Proposition::And(stated, _) = kernel_goal {
            kernel_goal = stated;
        }
        let Proposition::ResourceSeparate {
            left: goal_left,
            right: goal_right,
        } = kernel_goal
        else {
            return Ok(None);
        };
        if !matches!(
            (goal_left.as_ref(), goal_right.as_ref()),
            (Resource::Memory(_), Resource::Memory(_))
        ) {
            return Ok(None);
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let mut candidates = search_input
            .facts()
            .assumptions()
            .resource_separation_candidates(goal_left, goal_right)
            .unwrap_or_default()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        for fact in view.fixed_state.state.resources().facts() {
            if fact.is_own() && matches!(fact.resource(), Resource::Memory(_)) {
                candidates.push(Proposition::ResourceSeparate {
                    left: Box::new(fact.resource().clone()),
                    right: goal_right.clone(),
                });
            }
        }
        for candidate in candidates {
            check_verification_deadline()?;
            let Proposition::ResourceSeparate { left: a, right: b } = &candidate else {
                continue;
            };
            if !matches!(
                (a.as_ref(), b.as_ref()),
                (Resource::Memory(_), Resource::Memory(_))
            ) {
                continue;
            }
            if a == goal_left && b == goal_right {
                continue;
            }
            // The goal already owns exact spellings for these resources,
            // including reads at its selected historical points. Keep those
            // names instead of reconstructing them from the current state.
            let source = |resource: &Resource| {
                if resource == goal_left.as_ref() {
                    return Ok(left.clone());
                }
                if resource == goal_right.as_ref() {
                    return Ok(right.clone());
                }
                super::surface_synthesis::synthesize_surface_resource_subject(
                    resource,
                    view.parameter_binding,
                    view.fixed_state.state,
                    &BTreeMap::new(),
                )
                .ok_or_else(|| {
                    search_input
                        .step_error("a separation restriction source has no Surface spelling")
                })
            };
            let (a, b) = (source(a)?, source(b)?);
            for (a, b) in [(a.clone(), b.clone()), (b, a)] {
                let separate = ClickProposition::Separate {
                    left: a.clone(),
                    right: b.clone(),
                };
                let premises = vec![
                    separate,
                    ClickProposition::Contains {
                        parent: a.clone(),
                        child: left.clone(),
                    },
                    ClickProposition::Contains {
                        parent: b.clone(),
                        child: right.clone(),
                    },
                ];
                let mut proof = search_input.clone();
                let mut proved = true;
                for (index, premise) in premises.iter().enumerate() {
                    let Some(scope) =
                        attempt::candidate_outcome(proof.driver().open_have(premise.clone()))?
                    else {
                        proved = false;
                        break;
                    };
                    // Never recursively search for a larger separation here.
                    let closed = if index == 0 {
                        scope.driver().try_direct_logical_closure()?
                    } else {
                        scope
                            .driver()
                            .try_solve_closure_with_surfaces(introduced_surfaces)?
                    };
                    let Some(closed) = closed else {
                        proved = false;
                        break;
                    };
                    proof = closed.join()?;
                }
                if !proved {
                    continue;
                }
                let resource_arg = |r: &crate::surface::ResourceSubject| {
                    ContractExpression::Resource(Box::new(r.clone()))
                };
                proof = proof.driver().apply_step(ProofStep::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "click::separation::separate_restrict".into(),
                        arguments: vec![
                            resource_arg(&a),
                            resource_arg(&b),
                            resource_arg(left),
                            resource_arg(right),
                        ],
                    },
                    premises,
                })?;
                if proof.is_complete() || proof.goal() != search_input.goal() {
                    return Ok(Some(proof));
                }
                if let Some(closed) = Self::try_direct_logical_closure(&proof)? {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Expand separation from a conjunction through the existing library laws.
    /// Only search recurses over the descriptor; replay applies each law once.
    pub(in crate::surface::proof) fn try_resource_star_separation_closure(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_resource_star_separation_closure");
        let ClickProposition::Separate { left, right } = surface_goal else {
            return Ok(None);
        };
        let (a, b, other, reversed) = match (left, right) {
            (crate::surface::ResourceSubject::Star(a, b), other) => (a, b, other, false),
            (other, crate::surface::ResourceSubject::Star(a, b)) => (a, b, other, true),
            _ => return Ok(None),
        };
        let resource_arg = |resource: &crate::surface::ResourceSubject| {
            ContractExpression::Resource(Box::new(resource.clone()))
        };
        let separate = |left: &crate::surface::ResourceSubject,
                        right: &crate::surface::ResourceSubject| {
            ClickProposition::Separate {
                left: left.clone(),
                right: right.clone(),
            }
        };
        let mut proof = search_input.clone();
        let mut premises = Vec::new();
        for child in [a.as_ref(), b.as_ref()] {
            check_verification_deadline()?;
            let premise = if reversed {
                separate(other, child)
            } else {
                separate(child, other)
            };
            let scope = proof.driver().open_have(premise.clone())?;
            let Some(closed) = scope
                .driver()
                .try_solve_closure_with_surfaces(introduced_surfaces)?
            else {
                return Ok(None);
            };
            proof = closed.join()?;
            if reversed {
                proof = proof.driver().apply_step(ProofStep::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "click::separation::separate_symm".into(),
                        arguments: vec![resource_arg(other), resource_arg(child)],
                    },
                    premises: vec![premise],
                })?;
            }
            premises.push(separate(child, other));
        }
        proof = proof.driver().apply_step(ProofStep::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "click::separation::separate_star".into(),
                arguments: vec![resource_arg(a), resource_arg(b), resource_arg(other)],
            },
            premises,
        })?;
        if reversed {
            proof = proof.driver().apply_step(ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "click::separation::separate_symm".into(),
                    arguments: vec![resource_arg(right), resource_arg(left)],
                },
                premises: vec![separate(right, left)],
            })?;
        }
        if proof.is_complete() || proof.goal() != search_input.goal() {
            Ok(Some(proof))
        } else {
            Self::try_direct_logical_closure(&proof)
        }
    }

    /// Refines the Proof-owned Surface goal through audited scopes and steps.
    /// The caller cannot supply a second description of the judgment: this
    /// syntax is the view paired with the kernel goal in `PropositionObligation`.
    /// Keep branch-local proof/syntax temporaries out of this recursive frame.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_solve_closure_with_surfaces(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_solve_closure_with_surfaces");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        if let Some(proof) = Self::try_resource_separation_restriction_closure(
            search_input,
            surface_goal,
            introduced_surfaces,
        )? {
            return Ok(Some(proof));
        }
        if matches!(goal, Proposition::And(_, _)) {
            // The split owns the checked Surface-to-kernel correspondence.
            // In particular, a lowered existential body may be a conjunction
            // whose written Surface spelling is only the body; do not gate
            // this on a shape heuristic.
            // A smart closure candidate may encounter a kernel conjunction
            // whose written presentation is not recoverable.  Decline this
            // candidate so the caller can report its ordinary bounded proof
            // failure; the explicit `both` operation still rejects the same
            // mismatch transactionally through the checked split.
            match search_input.checked_both_surface_children() {
                Ok(_) => {}
                Err(_) => {
                    // Preserve the bounded-operation contract: a
                    // presentation mismatch declines this candidate, but a
                    // deadline raised while checking its lowering must still
                    // escape.
                    check_verification_deadline()?;
                    return Ok(None);
                }
            }
            return crate::kernel::search::ProofSearch::try_structural_and_solve_closure(
                search_input,
                introduced_surfaces,
            );
        }
        if matches!(goal, Proposition::Or(_, _))
            && let Some((surface_left, surface_right)) =
                surface_logical_children(surface_goal, false)
        {
            return crate::kernel::search::ProofSearch::try_structural_or_solve_closure(
                search_input,
                &surface_left,
                &surface_right,
                introduced_surfaces,
            );
        }
        if matches!(goal, Proposition::Implies(_, _))
            && let Some(surface_antecedent) = surface_implication_antecedent(surface_goal)
        {
            return crate::kernel::search::ProofSearch::try_implication_solve_closure(
                search_input,
                &surface_antecedent,
                introduced_surfaces,
            );
        }
        if let (ClickProposition::Exists { name, .. }, Proposition::Exists { var, body, .. }) =
            (surface_goal, goal)
            && let Some(closed) =
                crate::kernel::search::ProofSearch::try_constructor_witness_exists_closure(
                    search_input,
                    name,
                    *var,
                    body,
                    introduced_surfaces,
                )?
        {
            return Ok(Some(closed));
        }
        match (surface_goal, goal) {
            (ClickProposition::Exists { name, .. }, goal @ Proposition::Exists { .. })
                if quantified_external_range_goal(goal) =>
            {
                crate::kernel::search::ProofSearch::try_structural_exists_solve_closure(
                    search_input,
                    name,
                    introduced_surfaces,
                )
            }
            (ClickProposition::ForAll { .. }, Proposition::ForAll { .. }) => {
                crate::kernel::search::ProofSearch::try_structural_forall_solve_closure(
                    search_input,
                    surface_goal,
                    introduced_surfaces,
                )
            }
            // A predicate-call goal unfolds to its body, which the
            // structural arms and logical closers then work over. Repeat
            // unfolds are refused so recursive predicate bodies cannot loop
            // the search.
            (ClickProposition::PredicateCall { name, .. }, _)
                if !search_input.focused_branch_unfolds().contains(name) =>
            {
                crate::kernel::search::ProofSearch::try_structural_predicate_solve_closure(
                    search_input,
                    name,
                    introduced_surfaces,
                )
            }
            _ => Ok(None),
        }
    }

    /// `exists v { x == C(.., v, ..) }` where the facts already give `x` a
    /// constructor `C(.., t, ..)` of the same variant: the witness is `t`,
    /// read off that constructor, as a proof would name it with `witness`.
    /// One lookup in the constructor index; the checked `witness` step and
    /// an ordinary closure of the instance decide it.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_constructor_witness_exists_closure(
        search_input: &Proof<'a>,
        name: &str,
        var: Variable,
        body: &Proposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_constructor_witness_exists_closure");
        use crate::kernel::{AlgebraicTermNode, AlgebraicValue};
        let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = body else {
            return Ok(None);
        };
        let is_bound = |field: &AlgebraicValue| match field {
            AlgebraicValue::Program(
                ProgramValue::Int32(term)
                | ProgramValue::UInt32(term)
                | ProgramValue::Int8(term)
                | ProgramValue::Int16(term)
                | ProgramValue::UInt8(term)
                | ProgramValue::UInt16(term)
                | ProgramValue::Int64(term)
                | ProgramValue::UInt64(term)
                | ProgramValue::Bool(term),
            ) => *term == MachineTerm::Variable(var),
            _ => false,
        };
        // The written pattern and the value it describes, in either order.
        let split = |pattern: &crate::kernel::AlgebraicTerm| match &pattern.node {
            AlgebraicTermNode::Constructor { variant, fields } => fields
                .iter()
                .position(is_bound)
                .map(|index| (variant.clone(), index)),
            _ => None,
        };
        let Some((value, (variant, index))) = split(right)
            .map(|found| (left, found))
            .or_else(|| split(left).map(|found| (right, found)))
        else {
            return Ok(None);
        };
        let Some(known) = search_input
            .facts()
            .assumptions()
            .known_algebraic_constructor(value)
        else {
            return Ok(None);
        };
        let AlgebraicTermNode::Constructor {
            variant: known_variant,
            fields,
        } = &known.node
        else {
            return Ok(None);
        };
        let Some(AlgebraicValue::Program(field)) =
            fields.get(index).filter(|_| *known_variant == variant)
        else {
            return Ok(None);
        };
        // A constant is written as itself; any other value by the local,
        // parameter or binder that holds it.
        let constant = matches!(
            field,
            ProgramValue::Int32(term)
                | ProgramValue::UInt32(term)
                | ProgramValue::Int8(term)
                | ProgramValue::Int16(term)
                | ProgramValue::UInt8(term)
                | ProgramValue::UInt16(term)
                | ProgramValue::Int64(term)
                | ProgramValue::UInt64(term)
                | ProgramValue::Bool(term)
                if matches!(
                    term,
                    bits32_constant!(_)
                        | int64_constant!(_)
                        | uint64_constant!(_)
                )
        );
        let variable = match field {
            ProgramValue::Int32(term)
            | ProgramValue::UInt32(term)
            | ProgramValue::Int8(term)
            | ProgramValue::Int16(term)
            | ProgramValue::UInt8(term)
            | ProgramValue::UInt16(term)
            | ProgramValue::Int64(term)
            | ProgramValue::UInt64(term)
            | ProgramValue::Bool(term) => match term {
                MachineTerm::Variable(variable) => Some(*variable),
                _ => None,
            },
            _ => None,
        };
        let spelled = if constant {
            Some(ContractExpression::ProgramExpression(
                ProgramExpression::Value(field.clone()),
            ))
        } else if let ProofContext::Pure(context) = search_input.context.as_ref() {
            // A theorem's values are its parameters and binders, by name.
            let (intro_names, local_names) = search_input.binder_variable_names();
            context
                .theorem_context
                .values
                .iter()
                .find(|(_, value)| *value == field)
                .map(|(name, _)| name.clone())
                .or_else(|| {
                    variable.and_then(|variable| {
                        context
                            .source_names
                            .get(&variable)
                            .cloned()
                            .or_else(|| local_names.get(&variable).cloned())
                            .or_else(|| intro_names.get(&variable).cloned())
                    })
                })
                .map(|name| {
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(name))
                })
        } else {
            search_input.premise_fixed_state_view().and_then(|view| {
                super::surface_synthesis::synthesize_surface_value(
                    field,
                    view.parameter_binding,
                    view.fixed_state.state,
                )
            })
        };
        let Some(spelled) = spelled else {
            return Ok(None);
        };
        check_verification_deadline()?;
        let witness = ProofWitness::single(name.to_string(), spelled);
        let Some(introduced) = attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::Witness(witness)),
        )?
        else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(introduced),
            introduced_surfaces,
        )
    }

    // These helpers preserve the dispatcher's search order and checked steps;
    // their stack storage is needed only for the selected connective.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_exists_solve_closure(
        search_input: &Proof<'a>,
        name: &str,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_exists_solve_closure");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let mut candidates = Vec::new();
        for argument in context.arguments {
            if matches!(argument, ProgramExpression::Value(ProgramValue::Int32(_))) {
                candidates.push(ContractExpression::ProgramExpression(argument.clone()));
            }
        }
        // The range-loadability source slice has no witness in its call
        // arguments, so zero is the deterministic fallback.  It is tried
        // after call arguments to keep this operation useful for other
        // source-backed existential requirements without searching ambient
        // facts.
        candidates.push(ContractExpression::ProgramExpression(
            ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
        ));
        for value in candidates {
            check_verification_deadline()?;
            let witness = ProofWitness::single(name.to_string(), value);
            let Some(introduced) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_step(ProofStep::Witness(witness)),
            )?
            else {
                continue;
            };
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &(introduced),
                    introduced_surfaces,
                )?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_forall_solve_closure(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_forall_solve_closure");
        if let Some(enumerated) = crate::kernel::search::ProofSearch::try_finite_forall_enumeration(
            search_input,
            surface_goal,
        )? {
            return Ok(Some(enumerated));
        }
        match attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Intro))? {
            Some(introduced) => {
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &(introduced),
                    introduced_surfaces,
                )
            }
            None => Ok(None),
        }
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_and_solve_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_and_solve_closure");
        let (split_proof, split, ids) = search_input.split_focused_both()?;
        let marker = split_proof.checkpoint();
        let Some(left) = crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(split_proof.focus_branch(ids[0])?),
            introduced_surfaces,
        )?
        else {
            return Ok(None);
        };
        let Some(right) = crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(left.focus_branch(ids[1])?),
            introduced_surfaces,
        )?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(right.join_focused_both(&marker, split, ids))
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_predicate_solve_closure(
        search_input: &Proof<'a>,
        name: &str,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_predicate_solve_closure");
        match attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::UnfoldPredicate(name.to_string())),
        )? {
            Some(unfolded) => crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                &(unfolded),
                introduced_surfaces,
            ),
            None => Ok(None),
        }
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_or_solve_closure(
        search_input: &Proof<'a>,
        surface_left: &ClickProposition,
        surface_right: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_or_solve_closure");
        for surface in [surface_left, surface_right] {
            let selected = (|| {
                let Some(scope) =
                    attempt::candidate_outcome(search_input.driver().open_have(surface.clone()))?
                else {
                    return Ok(None);
                };
                let Some(scope) = (scope)
                    .driver()
                    .try_solve_closure_with_surfaces(introduced_surfaces)?
                else {
                    return Ok(None);
                };
                let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                    return Ok(None);
                };
                attempt::candidate_outcome(joined.driver().apply_step(ProofStep::Known))
            })();
            if let Some(selected) = selected? {
                return Ok(Some(selected));
            }
        }
        Ok(None)
    }

    /// Proves the kernel's deterministic constant-bounded universal table as
    /// checked nested `have` scopes, then closes with the ordinary
    /// `Enumerate` rule. Candidate discovery is output-sensitive in the
    /// explicit instance table; each non-vacuous instance recursively uses
    /// the same retained Proof search and no ambient universal scan.
    pub(in crate::surface::proof) fn try_finite_forall_enumeration(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_finite_forall_enumeration");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal, true) else {
            return Ok(None);
        };
        // A goal stated as a predicate call binds through the predicate's
        // body; unfold it at the surface to name the binders.
        let predicate_environment = match search_input.context.as_ref() {
            ProofContext::Pure(context) => context.spec_definitions.predicates,
            ProofContext::FixedState(context) => context.spec_definitions.predicates,
            ProofContext::Execution(context) => context.spec_definitions.predicates,
        };
        let all_predicates = predicate_environment
            .definitions
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        let unfolded = unfold_click_predicates_in_proposition_with_active(
            predicate_environment,
            &all_predicates,
            surface_goal,
            &mut BTreeSet::new(),
        )
        .unwrap_or_else(|_| surface_goal.clone());
        let mut binder_names = Vec::new();
        let mut surface_body = &unfolded;
        while let ClickProposition::ForAll { name, body, .. } = surface_body {
            binder_names.push(name.clone());
            surface_body = body;
        }
        if binder_names.is_empty() {
            return Ok(None);
        }

        let mut proof = search_input.clone();
        for (values, instance) in instances {
            check_verification_deadline()?;
            if values.len() != binder_names.len() {
                return Ok(None);
            }
            if matches!(
                normalize_proposition(&instance),
                NormalizedProposition::True
            ) {
                continue;
            }
            let Some(value_expressions) = values
                .iter()
                .map(|value| {
                    u32::try_from(*value).ok().map(|bits| {
                        ContractExpression::ProgramExpression(ProgramExpression::Value(int32(bits)))
                    })
                })
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
            let substitutions = binder_names
                .iter()
                .cloned()
                .zip(value_expressions)
                .collect::<BTreeMap<_, _>>();
            let Ok(surface_instance) = substitute_click_proposition(surface_body, &substitutions)
            else {
                return Ok(None);
            };
            // An instance whose guard is constant true is stated as its
            // conclusion: that is the fact a later instance's proof cites, and
            // `enumerate()` reads the table through the same normalization.
            let surface_instance = match (&instance, &surface_instance) {
                (Proposition::Implies(guard, _), ClickProposition::Implies(_, conclusion))
                    if matches!(normalize_proposition(guard), NormalizedProposition::True) =>
                {
                    conclusion.as_ref().clone()
                }
                _ => surface_instance,
            };
            let Some(scope) =
                attempt::candidate_outcome(proof.driver().open_have(surface_instance))?
            else {
                return Ok(None);
            };
            let Some(scope) = (scope).driver().try_solve_closure()? else {
                return Ok(None);
            };
            let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Enumerate))
    }

    /// Closes from the just-introduced antecedent and one exact indexed
    /// opposite. The antecedent fixes the kernel pair; Surface lookup visits
    /// only forms recorded for those two facts, never the ambient set.
    pub(in crate::surface::proof) fn try_introduced_antecedent_contradiction(
        search_input: &Proof<'a>,
        surface_antecedent: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_introduced_antecedent_contradiction");
        let Some(introduced) = search_input.checked_facts().first() else {
            return Ok(None);
        };
        let opposite = match introduced {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => body.as_ref().clone(),
            proposition => Proposition::Not(Box::new(proposition.clone())),
        };
        // The facts may hold the opposite in another of its spellings,
        // `x > 100` for `x <= 100` false.
        let Some(opposite) = std::iter::once(opposite.clone())
            .chain(crate::kernel::proof::fact_reasoning::condition_polarity_forms(&opposite))
            .find(|form| search_input.facts().contains(form))
        else {
            return Ok(None);
        };
        if let Some(closed) = attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::Contradiction(surface_antecedent.clone())),
        )? {
            return Ok(Some(closed));
        }
        let surfaces = match search_input.context.as_ref() {
            ProofContext::Pure(context) => context
                .theorem_context
                .surface_requirements
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::FixedState(context) => context
                .surface_propositions
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::Execution(_) => search_input
                .outcome_fixed_state_view()
                .into_iter()
                .flat_map(|view| view.surface_propositions.surfaces(&opposite))
                .cloned()
                .collect::<Vec<_>>(),
        };
        for surface in surfaces {
            if let Some(closed) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_step(ProofStep::Contradiction(surface)),
            )? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Retains the kernel decision and every exact checkable surface form
    /// among its context premises. A typed evidence translator selects and
    /// requires its own exact premises from this subset; unrelated transitive
    /// search context need not be Surface-synthesizable. This is a read-only smart
    /// query: only the later `apply_step` calls may advance the proof.
    pub(in crate::surface::proof) fn selected_solve_derivation(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
    )> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_solve_derivation");
        crate::kernel::search::ProofSearch::selected_solve_derivation_with_surfaces(
            search_input,
            exclude_exact_goal,
            &[],
        )
    }

    pub(in crate::surface::proof) fn selected_solve_derivation_with_surfaces(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
    )> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_solve_derivation_with_surfaces");
        let (goal, derivation) =
            crate::kernel::search::ProofSearch::selected_solve_derivation_plan(
                search_input,
                exclude_exact_goal,
            )?;
        let premise_pairs = crate::kernel::search::ProofSearch::resolve_solve_premises(
            search_input,
            &derivation.context_premises(),
            introduced_surfaces,
        )?;
        Some((goal, derivation, premise_pairs))
    }

    /// The derivation solve selected for the focused goal, before any of its
    /// premises is spelled.
    pub(in crate::surface::proof) fn selected_solve_derivation_plan(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
    ) -> Option<(Proposition, PropositionDerivation)> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_solve_derivation_plan");
        // An execution goal is either a focused outcome or a frontier one.
        if matches!(search_input.context.as_ref(), ProofContext::Execution(_))
            && search_input.focused_outcome_data().is_none()
        {
            search_input.execution()?;
        }
        let goal = search_input.goal()?.clone();
        let derivation = if exclude_exact_goal {
            crate::kernel::search::ProofSearch::derive_solve_proposition_without_exact_goal(
                search_input.facts().assumptions(),
                &goal,
            )
        } else {
            match plan_solve_certificate(&goal, search_input.facts().assumptions()) {
                Some(SolveEvidence::Derivation(derivation)) => Some(derivation),
                _ => crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    search_input.facts().assumptions(),
                    &goal,
                ),
            }
        };
        let Some(derivation) = derivation else {
            if matches!(goal, Proposition::MemoryLoadable { .. }) {
                attempt::record_search_note(
                    "solve view derivation selection",
                    "no retained-premise derivation was produced for the requested view",
                );
            }
            return None;
        };
        Some((goal, derivation))
    }

    /// Spells each of `premises` in this context's recorded source forms,
    /// leaving out one that has none.
    pub(in crate::surface::proof) fn resolve_solve_premises(
        search_input: &Proof<'a>,
        premises: &[Proposition],
        introduced_surfaces: &[ClickProposition],
    ) -> Option<Vec<(Proposition, ClickProposition)>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("resolve_solve_premises");
        // Broad atomic derivations may retain a whole connected fact
        // component even when no checkable source spelling exists. Do not
        // render an unbounded component speculatively. The recorded-path
        // candidate is tried first, and explicit `using` lists have their
        // own presentation/checking path.
        if premises.len() > MAX_SOLVE_SOURCE_PREMISES {
            if matches!(
                search_input.goal(),
                Some(Proposition::MemoryLoadable { .. })
            ) {
                attempt::record_search_note(
                    "solve view premise spelling",
                    format!(
                        "budget exhausted: the selected view derivation contains {} premises; source spelling permits at most {MAX_SOLVE_SOURCE_PREMISES}",
                        premises.len()
                    ),
                );
            }
            return None;
        }
        crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: premise spelling",
            || {
                crate::kernel::search::ProofSearch::resolve_solve_premises_unmeasured(
                    search_input,
                    premises,
                    introduced_surfaces,
                )
            },
        )
    }

    pub(in crate::surface::proof) fn resolve_solve_premises_unmeasured(
        search_input: &Proof<'a>,
        premises: &[Proposition],
        introduced_surfaces: &[ClickProposition],
    ) -> Option<Vec<(Proposition, ClickProposition)>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("resolve_solve_premises_unmeasured");
        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, _, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => {
                (&context.theorem_context.surface_requirements, true, None)
            }
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                true,
                context.premise_anchor.as_ref(),
            ),
            // A judgment stated at a function outcome supplies the
            // outcome's recorded lowerings and statement-entry anchor.
            ProofContext::Execution(_) => {
                if let Some(data) = search_input.focused_outcome_data() {
                    (
                        &data.surface_propositions,
                        // Entry-anchored premises can add a check-equivalent
                        // outcome fact without discharging the exact goal
                        // form. Keep the ordinary trailing `known` so
                        // the checked successor decides whether it is needed.
                        false,
                        data.premise_anchor.as_ref(),
                    )
                } else {
                    // A judgment stated mid-execution (a `have` before
                    // function exit) supplies the frontier's recorded
                    // lowerings and the entry of the last executed
                    // statement, exactly as an outcome data does.
                    let execution = search_input.execution()?;
                    frontier_anchor = frontier_premise_anchor(execution);
                    (
                        &execution.presentation.surface_propositions,
                        false,
                        frontier_anchor.as_ref(),
                    )
                }
            }
        };
        let resolve_premise = |premise: &Proposition, anchor: Option<&ProgramPointRef>| {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            if let Some(surface) = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surface_facts,
                anchor,
                premise,
            ) {
                return Some((premise.clone(), surface));
            }
            if let Some(surface) = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                search_input.local_surface_facts(),
                anchor,
                premise,
            ) {
                return Some((premise.clone(), surface));
            }
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                search_input
                    .lower_surface_proposition(surface, "introduced solve premise")
                    .is_ok_and(|lowered| {
                        lowered == *premise || condition_polarity_equivalent(&lowered, premise)
                    })
            }) {
                return Some((premise.clone(), surface.clone()));
            }
            condition_polarity_forms(premise)
                .into_iter()
                .find_map(|form| {
                    let surface = crate::kernel::search::ProofSearch::available_surface_fact(
                        search_input,
                        surface_facts,
                        anchor,
                        &form,
                    );
                    surface.map(|surface| (form, surface))
                })
                .or_else(|| {
                    // A conjunct of one source fact's lowering — a contract
                    // clause beside its well-formedness conditions, a
                    // comparison beside the range facts its conversion
                    // adds — is spelled by that whole source fact. The
                    // containing kernel is spelled and re-lowered exactly as
                    // any premise is; citing it supplies this conjunct.
                    surface_facts
                        .kernels_containing_conjunct(premise)
                        .chain(
                            search_input
                                .local_surface_facts()
                                .kernels_containing_conjunct(premise),
                        )
                        .find_map(|whole| {
                            if crate::instrumentation::deadline_exceeded() {
                                return None;
                            }
                            crate::kernel::search::ProofSearch::available_surface_fact(
                                search_input,
                                surface_facts,
                                anchor,
                                whole,
                            )
                            .or_else(|| {
                                crate::kernel::search::ProofSearch::available_surface_fact(
                                    search_input,
                                    search_input.local_surface_facts(),
                                    anchor,
                                    whole,
                                )
                            })
                            .map(|surface| (premise.clone(), surface))
                        })
                })
        };
        let mut premise_pairs = premises
            .iter()
            .filter_map(|premise| resolve_premise(premise, premise_anchor))
            .collect::<Vec<_>>();
        // A structured branch continuation can clear `last_step_entry`, or a
        // later common statement can move it past the point where the
        // selected premises were established. If the initially resolved
        // subset already carries one common explicit `at(...)` form,
        // retry this same finite premise list at that successor. No ambient fact
        // or program-point scan participates.
        let anchors = premise_pairs
            .iter()
            .filter_map(
                |(_, surface)| match surface_program_point_selector(surface) {
                    Some(ProgramPointSelector::ProgramPoint(point)) => Some(point),
                    Some(ProgramPointSelector::Mark(_)) | None => None,
                },
            )
            .collect::<BTreeSet<_>>();
        if anchors.len() == 1 {
            let inferred = anchors.first().expect("one inferred anchor");
            let anchored_pairs = premises
                .iter()
                .filter_map(|premise| resolve_premise(premise, Some(inferred)))
                .collect::<Vec<_>>();
            if anchored_pairs.len() >= premise_pairs.len() {
                premise_pairs = anchored_pairs;
            }
        }
        // Name what has no spelling: a derivation found but not written
        // back is refused for that reason, not for the memory history a
        // supplemental explanation may show. Kernel authority is checked
        // context, never a citable premise, so it owes no spelling.
        let unspelled = premises
            .iter()
            .filter(|premise| {
                !premise.is_kernel_authority()
                    && !premise_pairs.iter().any(|(spelled, _)| spelled == *premise)
            })
            .collect::<Vec<_>>();
        if !crate::instrumentation::deadline_exceeded() && !unspelled.is_empty() {
            let strategy = if matches!(
                search_input.goal(),
                Some(Proposition::MemoryLoadable { .. })
            ) {
                "solve view premise spelling"
            } else {
                "solve premise spelling"
            };
            attempt::record_search_premise_note(
                strategy,
                format!(
                    "{} of {} selected derivation premises have checked source spellings; {} were omitted: ",
                    premise_pairs.len(),
                    premise_pairs.len() + unspelled.len(),
                    unspelled.len(),
                ),
                &unspelled,
            );
        }
        (!crate::instrumentation::deadline_exceeded()).then_some(premise_pairs)
    }

    /// Available source facts that keep `pivot + 1` from wrapping: a strict
    /// upper bound on `pivot`, or a nonstrict one by a constant below the
    /// `int32` maximum. Read from `pivot`'s indexed order bounds, at most
    /// [`MAX_INCREMENT_HEADROOM_PREMISES`] of them.
    pub(in crate::surface::proof) fn increment_headroom_premises(
        search_input: &Proof<'a>,
        pivot: &MachineTerm,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
    ) -> Vec<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("increment_headroom_premises");
        let mut premises = Vec::new();
        for (endpoint, other, strict, forward) in search_input
            .facts()
            .assumptions()
            .signed_order_bound_entries(pivot)
        {
            if premises.len() == MAX_INCREMENT_HEADROOM_PREMISES {
                break;
            }
            // Only `pivot < other` or `pivot <= other` bounds `pivot` above.
            if !forward {
                continue;
            }
            if !strict
                && !matches!(other, bits32_constant!(constant)
                    if (constant_u32(constant) as i32) < i32::MAX)
            {
                continue;
            }
            let (left, right) = (Box::new(endpoint), Box::new(other));
            let fact = Proposition::ConditionIs(
                if strict {
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left,
                        right,
                    }
                } else {
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left,
                        right,
                    }
                },
                true,
            );
            if !search_input.facts().contains(&fact) {
                continue;
            }
            if let Some(surface) = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surface_facts,
                premise_anchor,
                &fact,
            ) {
                premises.push(surface);
            }
        }
        premises
    }

    pub(in crate::surface::proof) fn available_surface_fact(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("available_surface_fact");
        let surface = crate::kernel::search::ProofSearch::available_surface_fact_raw(
            search_input,
            surface_facts,
            premise_anchor,
            kernel,
        )?;
        crate::kernel::search::ProofSearch::named_returned_pointer_surface_fact(
            search_input,
            &surface,
            kernel,
        )
        .or(Some(surface))
    }

    pub(in crate::surface::proof) fn named_returned_pointer_surface_fact(
        search_input: &Proof<'a>,
        surface: &ClickProposition,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("named_returned_pointer_surface_fact");
        let view = search_input.premise_fixed_state_view()?;
        let Some(result @ ProgramValue::Pointer(_)) = view.fixed_state.result else {
            return None;
        };
        // Resource witnesses may have no written name but coincide with the
        // checked return value. Name that exact value, then re-lower the
        // candidate so presentation cannot change the cited premise.
        let equality = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(result.clone())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Binding("result".to_string()),
        };
        let named =
            crate::surface::rewrite_click_proposition_by_surface_equality(surface, &equality)?;
        search_input
            .lower_surface_proposition_direct(&named, "returned pointer premise form")
            .is_ok_and(|lowered| {
                lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)
            })
            .then_some(named)
    }

    pub(in crate::surface::proof) fn available_surface_fact_raw(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("available_surface_fact_raw");
        Self::surface_fact_raw_for_purpose(
            search_input,
            surface_facts,
            premise_anchor,
            kernel,
            SurfaceSpellingPurpose::AvailablePremise,
        )
    }

    pub(in crate::surface::proof) fn proposed_surface_goal(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("proposed_surface_goal");
        Self::surface_fact_raw_for_purpose(
            search_input,
            surface_facts,
            None,
            kernel,
            SurfaceSpellingPurpose::ProposedGoal,
        )
    }

    fn surface_fact_raw_for_purpose(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
        purpose: SurfaceSpellingPurpose,
    ) -> Option<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("surface_fact_raw_for_purpose");
        // Option-based presentation misses must not restart work after a
        // candidate exhausted the verifier's sticky budget/deadline.
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        // Store records and reflexive pointer equalities are internal
        // metadata, with no useful source rewrite. Keep their retained source
        // forms when present; do not invent spellings by searching history.
        if (is_reflexive_pointer_equality(kernel)
            || matches!(kernel, Proposition::ConditionIs(condition, value)
                if crate::kernel::is_store_fact(condition, *value)))
            && surface_facts.surfaces(kernel).next().is_none()
            && search_input
                .local_surface_facts()
                .surfaces(kernel)
                .next()
                .is_none()
            && surface_facts
                .kernels_containing_conjunct(kernel)
                .next()
                .is_none()
            && search_input
                .local_surface_facts()
                .kernels_containing_conjunct(kernel)
                .next()
                .is_none()
        {
            return None;
        }
        let _qualified_sources =
            super::surface_synthesis::QualifiedSynthesisScope::enter(surface_facts);
        // A refold moves a constructor equation: a proof `match` arm's case
        // fact states the scrutinee's constructor at unchanged function entry,
        // and once the arm has refolded its instance, `c.model == C(..)` reads
        // the refolded field. Like a program point selector recorded again in a
        // loop, that spelling may stop denoting its old checked fact.
        // Re-lower those movable forms below; other live recorded pairs keep
        // their indexed lookup without repeating proposition lowering.
        let constructor_equation = matches!(
            kernel,
            Proposition::Equal(
                Term::Algebraic(_),
                Term::Algebraic(crate::kernel::AlgebraicTerm {
                    node: crate::kernel::AlgebraicTermNode::Constructor { .. },
                    ..
                })
            )
        );
        let retained_branch_equality = match kernel {
            Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(left, right)
                | ConditionTerm::IntegerNotEqual(left, right),
                _,
            ) => [left, right].iter().any(|term| match term.as_ref() {
                crate::kernel::IntegerTerm::Machine(value) => {
                    value.shared_operand().is_some_and(|term| {
                        term.has_machine_conditionals() || term.has_machine_matches()
                    })
                }
                _ => false,
            }),
            _ => false,
        };
        let matches_kernel = |candidate: &ClickProposition, allow_recorded_pair: bool| {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            // `result` exists only once the function returns: a state
            // before the return that reads it lowers, but does not parse.
            if reads_result_before_return(candidate) {
                return None;
            }
            // Synthesized kernel literals can lower back to this fact yet
            // print as diagnostic-only pointer placeholders. Such a form
            // cannot be cited in an expandable proof; try another spelling.
            let named = crate::kernel::search::ProofSearch::named_returned_pointer_surface_fact(
                search_input,
                candidate,
                kernel,
            );
            if !crate::surface::parser::has_valid_source_tokens(
                &crate::surface::printing::source_click_proposition(
                    named.as_ref().unwrap_or(candidate),
                ),
            ) {
                return None;
            }
            let lower = |candidate: &ClickProposition| {
                let operation = || {
                    search_input
                        .lower_surface_proposition_direct(candidate, "typed solve premise form")
                };
                match purpose {
                    SurfaceSpellingPurpose::AvailablePremise => {
                        super::super::execution_planning::without_open_obligation_probe(operation)
                            .ok()
                    }
                    SurfaceSpellingPurpose::ProposedGoal => {
                        // This private probe checks only the candidate's term identity.
                        // It publishes no proof/facts and cannot add debts to an outer
                        // operation. The selected Surface form must be lowered again by
                        // open_have, which proves and retains all its prerequisites.
                        let (lowered, _requirements) =
                            super::super::execution_planning::probe_open_obligations(operation);
                        lowered.ok()
                    }
                }
            };
            if matches!(purpose, SurfaceSpellingPurpose::AvailablePremise)
                && allow_recorded_pair
                && search_input.focused_outcome_data().is_some()
                && surface_facts
                    .available_kernel_matching(candidate, |fact| {
                        search_input.facts().contains(fact)
                    })
                    .is_some_and(|lowered| {
                        lowered == kernel || condition_polarity_equivalent(lowered, kernel)
                    })
            {
                // A terminal path can retain a fact spelled through an
                // automatic local that has since left scope. Its recorded
                // pair remains a valid kernel fact, but the unanchored
                // spelling cannot be used as a source `rewrite`.
                // Only names in this candidate are queried. An outcome's
                // recorded pair cannot make an out-of-scope temporary legal
                // source, even when no call-outcome route was selected.
                let names_a_dead_local =
                    search_input.premise_fixed_state_view().is_some_and(|view| {
                        let mut current_names = BTreeSet::new();
                        crate::surface::collect_current_proposition_variables(
                            candidate,
                            &mut current_names,
                        );
                        current_names.iter().any(|name| {
                            !(name == "result" && view.fixed_state.result.is_some())
                                && !view.fixed_state.state.locals().contains_name(name)
                                && !view.fixed_state.pre_state.locals().contains_name(name)
                                && !premise_anchor
                                    .and_then(|anchor| view.fixed_state.recorded_states.get(anchor))
                                    .is_some_and(|retained_state| {
                                        retained_state.locals().contains_name(name)
                                    })
                                && search_input.local_binding(name).is_none()
                                && search_input.local_integer_values().get(name).is_none()
                                && search_input.local_algebraic_values().get(name).is_none()
                        })
                    });
                // A statement selector can be recorded again on a later
                // loop iteration. Its old pair remains a checked fact, but
                // an explicit state spelling must still denote it now.
                let state_spelling = proposition_contains_at_expression(candidate);
                if !constructor_equation && !names_a_dead_local && !state_spelling {
                    // The recorded pair is authoritative for this shape.
                    return Some(());
                }
                // A constructor equation's written spelling can have stopped
                // lowering at all: the arm's instance was consumed and
                // unfolded and never refolded under its name, so `t.model`
                // names nothing here and the rechecked certificate would
                // fail on it. Only the entry-anchored form below still
                // denotes the fact.
                let lowered = lower(candidate)?;
                // The spelling lowers to some other fact, so it has stopped
                // denoting this one: citing it would hand the rechecked proof
                // the fact it now names instead.
                return (lowered == *kernel || condition_polarity_equivalent(&lowered, kernel))
                    .then_some(());
            }
            let lowered = lower(candidate)?;
            (lowered == *kernel
                || condition_polarity_equivalent(&lowered, kernel)
                // This candidate spells one already-selected premise. Admit
                // its native/shared equality reading at the same explicit
                // boundary used when the generated certificate cites it.
                || (retained_branch_equality
                    && crate::kernel::proof::fact_reasoning::listed_equality_fact_is_available(
                        kernel, std::slice::from_ref(&lowered),
                    ))
                || quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                    .is_some())
            .then_some(())
        };
        if let Some(surface) = surface_facts.surfaces(kernel).find(|surface| {
            (proposition_contains_at_expression(surface)
                || proposition_contains_old_expression(surface))
                && matches_kernel(surface, true).is_some()
        }) {
            return Some(surface.clone());
        }
        // A selected fact can instead name a fresh loop-head value in the
        // current state. Recover it there before searching older states
        // which cannot name that value at all.
        let pointer_goal = matches!(
            search_input.goal(),
            Some(Proposition::ConditionIs(ConditionTerm::PointerEqual(..), _))
        );
        if pointer_goal
            && let Some(surface) = surface_facts
                .surfaces(kernel)
                .find(|surface| matches_kernel(surface, true).is_some())
        {
            return Some(surface.clone());
        }
        if pointer_goal
            && let Some(view) = search_input.premise_fixed_state_view()
            && let Some(surface) = synthesize_surface_proposition(
                kernel,
                view.parameter_binding,
                view.fixed_state.state,
            )
            && matches_kernel(&surface, true).is_some()
        {
            return Some(surface);
        }
        // Function requirements retain their original unanchored Surface
        // form while their kernel fact is entry-relative. Probe that one
        // canonical source form before the moving statement-entry anchor;
        // the direct lowering check below rejects non-entry facts, and the
        // lookup visits only forms indexed under this selected premise.
        let function_entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        let requirement_surface = if let Some(data) = search_input.focused_outcome_data() {
            data.requirement_surfaces.get(kernel).cloned()
        } else {
            // A judgment stated mid-execution selects its requirement
            // spellings from the frontier's own contract, as an outcome
            // outcome does from its recorded ones.
            search_input
                .execution_proposition_fixed_state_view()
                .and_then(|view| {
                    view.requirement_facts
                        .as_slice()
                        .iter()
                        .zip(view.original_requirements)
                        .find(|(fact, _)| *fact == kernel)
                        .and_then(|(_, requirement)| requirement.proposition().cloned())
                })
        };
        if let Some(surface) = requirement_surface {
            let anchored = ClickProposition::At {
                selector: ProgramPointSelector::ProgramPoint(function_entry.clone()),
                proposition: Box::new(surface.clone()),
            };
            if matches_kernel(&anchored, true).is_some() {
                return Some(anchored);
            }
        }
        if search_input.premise_fixed_state_view().is_some() {
            if let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_program_point(surface, &function_entry).ok()?;
                matches_kernel(&anchored, true).map(|()| anchored)
            }) {
                return Some(anchored);
            }
            if let Some(view) = search_input.premise_fixed_state_view()
                && let Some(surface) = synthesize_surface_proposition(
                    kernel,
                    view.parameter_binding,
                    view.fixed_state.pre_state,
                )
                && let Ok(anchored) = surface_at_program_point(&surface, &function_entry)
                && matches_kernel(&anchored, true).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(anchor) = premise_anchor
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_program_point(surface, anchor).ok()?;
                matches_kernel(&anchored, true).map(|()| anchored)
            })
        {
            return Some(anchored);
        }
        // A selected scalar fact may combine a current value with an entry
        // read, which no single earlier state can spell. Try these named
        // states before walking history. New scalar candidates lower directly: a
        // recorded unanchored form may name an earlier value of the same local.
        // The structural speller: values the current state and the proof's
        // binders name, entry reads as `old(..)`, and a read of any other
        // recorded memory at the point that recorded it, found by its memory
        // in one lookup.
        let _recorded_points = search_input.premise_fixed_state_view().map(|view| {
            super::surface_synthesis::SynthesisRecordedPointsScope::enter(
                view.fixed_state.recorded_states,
            )
        });
        if let Some(view) = search_input.premise_fixed_state_view() {
            let (bound_variable_names, binder_names) = search_input.binder_variable_names();
            let surface = super::surface_synthesis::with_proof_binder_names(
                std::sync::Arc::new(binder_names),
                || {
                    super::surface_synthesis::synthesize_surface_proposition_at_entry_post_with_bound_variable_names(
                        kernel,
                        view.parameter_binding,
                        view.fixed_state.pre_state,
                        view.fixed_state.state,
                        &bound_variable_names,
                    )
                },
            );
            let matched = surface
                .as_ref()
                .is_some_and(|surface| matches_kernel(surface, false).is_some());
            if matched {
                return surface;
            }
        }
        // Before accepting an unanchored recorded form, which may have been
        // stated at an earlier value of a variable that later changed,
        // spell the fact against the recorded state where it was read.
        if let Some(anchor) = premise_anchor
            && let Some((parameters, arguments, recorded_states)) = match search_input
                .context
                .as_ref()
            {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => Some((
                    context.parameter_binding.parameters,
                    context.parameter_binding.arguments,
                    context.fixed_state.recorded_states,
                )),
                ProofContext::Execution(_) => search_input.premise_fixed_state_view().map(|view| {
                    (
                        view.parameter_binding.parameters,
                        view.parameter_binding.arguments,
                        view.fixed_state.recorded_states,
                    )
                }),
            }
            && let Some(anchored) = crate::instrumentation::measure_operation(
                "surface",
                "solve premise",
                "solve premise surface at recorded states",
                || {
                    synthesize_surface_at_recorded_states(
                        kernel,
                        ParameterBinding::new(parameters, arguments),
                        recorded_states,
                        anchor,
                    )
                    .find(|surface| matches_kernel(surface, true).is_some())
                },
            )
        {
            return Some(anchored);
        }
        // A fact can mix states: a call's `ensures` that names its own
        // `old(..)` value holds a value only that call's entry state reads,
        // beside values the current state names. Spell it at the current
        // state with one recorded statement entry as the further state.
        if let Some(anchor) = premise_anchor
            && let Some(view) = search_input.premise_fixed_state_view()
            && let Some(mixed) = crate::instrumentation::measure_operation(
                "surface",
                "solve premise",
                "solve premise surface across recorded states",
                || {
                    synthesize_surface_with_recorded_state(
                        kernel,
                        view.parameter_binding,
                        view.fixed_state.pre_state,
                        view.fixed_state.state,
                        view.fixed_state.recorded_states,
                        anchor,
                    )
                    .find(|surface| matches_kernel(surface, true).is_some())
                },
            )
        {
            return Some(mixed);
        }
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        if let Some(surface) = surface_facts
            .surfaces(kernel)
            .find(|surface| matches_kernel(surface, true).is_some())
            .cloned()
        {
            return Some(surface);
        }
        // A proof `match` arm's case fact states the scrutinee's constructor at
        // unchanged function entry, and the spelling recorded for it is the
        // written, unanchored `c.model == C(..)`. Once the arm refolds its
        // instance, that spelling denotes the fold's own equation, so the
        // direct check above rejects it. The entry-anchored
        // `old(c.model) == C(..)` still lowers to this exact fact. Offer it
        // exactly where the recorded pair alone used to be taken as proof that
        // the written form named this premise -- that acceptance is what let a
        // certificate cite a spelling that is rechecked as a different fact --
        // and nowhere else, so a lookup that found no spelling at all still
        // finds none.
        if constructor_equation
            && search_input.focused_outcome_data().is_some()
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                surface_facts
                    .available_kernel_matching(surface, |fact| search_input.facts().contains(fact))
                    .is_some_and(|recorded| {
                        recorded == kernel || condition_polarity_equivalent(recorded, kernel)
                    })
                    .then(|| entry_anchored_constructor_equality(search_input, surface, kernel))
                    .flatten()
            })
        {
            return Some(anchored);
        }
        // Quantified execution facts may be retained in the canonical memory
        // form used by the kernel while their recorded Surface form lowers to
        // a term carrying a check-equivalent memory state. Probe only the
        // persistent alpha/canonical-form bucket for this selected premise;
        // `InstantiateUsing` validates the same equivalence on check.
        if matches!(kernel, Proposition::ForAll { .. }) {
            for candidate in search_input.facts().matching_quantified_facts(kernel) {
                for surface in surface_facts.surfaces(&candidate) {
                    let lowered = search_input
                        .lower_surface_proposition_direct(
                            surface,
                            "typed quantified solve premise form",
                        )
                        .ok()?;
                    if quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                        .is_some()
                    {
                        return Some(surface.clone());
                    }
                }
            }
        }
        // Pure unfolding and induction can add a selected fact without a
        // written requirement entry. Synthesize its presentation from retained
        // binder names, then independently lower it back to this exact fact.
        // This is candidate presentation only; it neither adds facts nor
        // reconstructs a proof context.
        if let ProofContext::Pure(context) = search_input.context.as_ref() {
            // Include arguments of opaque applications: their variables still
            // need names even though the bitvector collector treats the call
            // as an atom.
            let mut selected = BTreeSet::new();
            crate::kernel::planning_api::collect_proposition_connection_variables(
                kernel,
                &mut selected,
            );
            let mut bindings = selected
                .iter()
                .filter_map(|variable| {
                    context
                        .source_names
                        .get(variable)
                        .map(|name| (*variable, name.clone()))
                })
                .collect::<BTreeMap<_, _>>();
            let (intro_names, local_names) = search_input.binder_variable_names();
            for (variable, name) in local_names.into_iter().chain(intro_names) {
                if selected.contains(&variable) {
                    bindings.insert(variable, name);
                }
            }
            let synthesized = synthesize_surface_proposition_with_bound_variable_names(
                kernel,
                ParameterBinding::default(),
                &context.source_state,
                &bindings,
            );
            if let Some(surface) = synthesized
                && matches_kernel(&surface, true).is_some()
            {
                return Some(surface);
            }
        }
        // Branch-condition facts are checked execution outputs, but their
        // arm-local Surface map entry need not survive at the shared outcome.
        // Reconstruct only this derivation-selected premise at the current
        // symbolic state and accept it only when ordinary lowering recovers
        // the exact kernel fact. This is constant work per typed proof edge,
        // not an ambient form search.
        let synthesis_context = match search_input.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => Some((
                context.parameter_binding.parameters,
                context.parameter_binding.arguments,
                context.fixed_state.state,
            )),
            ProofContext::Execution(_) => search_input.premise_fixed_state_view().map(|view| {
                (
                    view.parameter_binding.parameters,
                    view.parameter_binding.arguments,
                    view.fixed_state.state,
                )
            }),
        };
        let (parameters, arguments, state) = synthesis_context?;
        let (bound_variable_names, binder_names) = search_input.binder_variable_names();
        if let Some(surface) = super::surface_synthesis::with_proof_binder_names(
            std::sync::Arc::new(binder_names),
            || {
                synthesize_surface_proposition_with_bound_variable_names(
                    kernel,
                    ParameterBinding::new(parameters, arguments),
                    state,
                    &bound_variable_names,
                )
            },
        ) && matches_kernel(&surface, true).is_some()
        {
            return Some(surface);
        }
        // The same recorded states and matcher already completed their
        // search above. The intervening presentation candidates do not change
        // this proof's state, so repeating that miss cannot find a new source.
        None
    }

    /// A cheap indexed rewrite can close a goal without exploring its
    /// connected component. Every longer chain uses the shared search,
    /// also when this entry point is reached after a split or an unfold.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_goal_equality_rewrite_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_equality_rewrite_closure");
        crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure_excluding(
            search_input,
            false,
            true,
        )
        .ok()
        .flatten()
    }

    #[cfg(test)]
    pub(in crate::surface::proof) fn try_goal_equality_rewrite_closure_excluding(
        search_input: &Proof<'a>,
        exclude_goal_fact: bool,
        allow_function_unfold: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_equality_rewrite_closure_excluding");
        match crate::kernel::search::ProofSearch::try_indexed_direct_equality_rewrite(
            search_input,
            exclude_goal_fact,
        ) {
            std::ops::ControlFlow::Break(closed) => Ok(closed),
            std::ops::ControlFlow::Continue(()) => {
                let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ConnectedFacts) else {
                    return Ok(None);
                };
                crate::kernel::search::ProofSearch::try_connected_equality_chain_closure(
                    search_input,
                    RewriteClosers::GoalLocal {
                        allow_function_unfold,
                    },
                )
            }
        }
    }

    /// The chain half of [`Self::try_goal_equality_rewrite_closure_excluding`]:
    /// the search over rewrites by the equalities connected to the goal.
    pub(in crate::surface::proof) fn try_connected_goal_equality_chain_closure(
        search_input: &Proof<'a>,
        allow_function_unfold: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_connected_goal_equality_chain_closure");
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ConnectedFacts) else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_connected_equality_chain_closure(
            search_input,
            RewriteClosers::GoalLocal {
                allow_function_unfold,
            },
        )
    }

    /// One indexed rewrite followed by direct closure of an algebraic
    /// comparison, without general solve or connected-premise discovery.
    pub(in crate::surface::proof) fn try_direct_model_equality_rewrite_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_model_equality_rewrite_closure");
        let goal = match search_input.goal()? {
            Proposition::Not(body) => body.as_ref(),
            goal => goal,
        };
        if !matches!(
            goal,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        ) {
            return None;
        }
        crate::kernel::search::ProofSearch::try_indexed_direct_equality_rewrite(search_input, false)
            .break_value()
            .flatten()
    }

    /// Spell a rewrite at the execution frontier that owns its goal. The
    /// last executed statement can name a different loop iteration state;
    /// rewriting must retain the recorded entry name of the selected fact.
    pub(in crate::surface::proof) fn available_rewrite_equality(
        search_input: &Proof<'a>,
        equality: &Proposition,
    ) -> Option<ClickProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("available_rewrite_equality");
        let frontier_anchor;
        let anchor = match search_input.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => context.premise_anchor.as_ref(),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => data.premise_anchor.as_ref(),
                None => {
                    frontier_anchor = ProgramPointRef {
                        region: CodeRegionRef::Region(
                            search_input.execution()?.core.frontier.next_statement_index,
                        ),
                        kind: ProgramPointKind::Entry,
                    };
                    Some(&frontier_anchor)
                }
            },
        };
        crate::kernel::search::ProofSearch::available_surface_fact(
            search_input,
            (search_input).premise_surface_facts()?,
            anchor,
            equality,
        )
        .or_else(|| {
            crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                search_input.local_surface_facts(),
                anchor,
                equality,
            )
        })
    }

    /// A derived call equality need not have a recorded source spelling.
    /// Use only an operand already written in this goal, and check the
    /// resulting equality in an ordinary nested proof before citing it.
    pub(in crate::surface::proof) fn try_goal_operand_constant_equality(
        search_input: &Proof<'a>,
        equality: &Proposition,
    ) -> Option<(ClickProposition, Proof<'a>)> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_operand_constant_equality");
        let ClickProposition::Comparison {
            left: source_left,
            right: source_right,
            ..
        } = search_input.surface_goal()?
        else {
            return None;
        };
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            }
            | ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            true,
        ) = search_input.goal()?
        else {
            return None;
        };
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            },
            true,
        ) = equality
        else {
            return None;
        };
        for (operand, source) in [(left.as_ref(), source_left), (right.as_ref(), source_right)] {
            let literal = if a.as_ref() == operand {
                b.as_ref()
            } else if b.as_ref() == operand {
                a.as_ref()
            } else {
                continue;
            };
            let bits32_constant!(value) = literal else {
                continue;
            };
            if matches!(operand, bits32_constant!(_)) {
                continue;
            }
            let surface = ClickProposition::Comparison {
                left: source.clone(),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(MachineTerm::constant(constant_u32(*value))),
                )),
            };
            let scope = search_input.driver().open_have(surface.clone()).ok()?;
            let closed = (scope).driver().try_direct_logical_closure().ok()??;
            return Some((surface, closed.join().ok()?));
        }
        None
    }

    /// Try one indexed equality and a direct closer. This shortcut never
    /// refines or branches into its own rewrite chain. `Break(None)` stops
    /// when an equivalent scalar goal is refuted or no source candidate can
    /// start a chain. `Continue` leaves the shared search to try.
    pub(in crate::surface::proof) fn try_indexed_direct_equality_rewrite(
        search_input: &Proof<'a>,
        exclude_goal_fact: bool,
    ) -> std::ops::ControlFlow<Option<Proof<'a>>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_direct_equality_rewrite");
        use std::ops::ControlFlow::{Break, Continue};
        if matches!(
            search_input.goal(),
            Some(Proposition::Implies(..) | Proposition::ForAll { .. })
        ) {
            return Continue(());
        }
        if crate::kernel::search::ProofSearch::scalar_offset_goal_is_refuted(search_input) {
            return Break(if exclude_goal_fact {
                None
            } else {
                crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)
                    .ok()
                    .flatten()
            });
        }
        let proof = search_input;
        let (Some(goal), Some(surface_facts)) =
            (proof.goal(), (search_input).premise_surface_facts())
        else {
            return Continue(());
        };
        let goal = goal.clone();
        let attempted_closures = std::cell::RefCell::new(BTreeSet::new());
        // Pointer equalities between scaled offsets are candidates too:
        // `rewrite` carries one through the address of a load, so a
        // goal over `p->q->x` reaches `r->x` under `p->q == r`.
        // Once both pointers have the same base, only their offsets
        // need rewriting. Selecting on the shared base also nominates
        // every historical pointer fact about that object, even when
        // none mentions an offset operand of this comparison.
        let equality_candidates = match &goal {
            Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), value)
                if left.block == right.block =>
            {
                // External arguments share a block and carry the
                // actual base as an offset prefix: `(base + i) == base`
                // needs facts about `i`, not old reads through `base`.
                let zero = crate::kernel::PointerOffsetTerm::Constant(0);
                let (left, right) = match (&left.offset, &right.offset) {
                    (crate::kernel::PointerOffsetTerm::Add(base, index), right)
                        if base.as_ref() == right =>
                    {
                        (index.as_ref(), &zero)
                    }
                    (left, crate::kernel::PointerOffsetTerm::Add(base, index))
                        if left == base.as_ref() =>
                    {
                        (&zero, index.as_ref())
                    }
                    (
                        crate::kernel::PointerOffsetTerm::Add(left_base, left_index),
                        crate::kernel::PointerOffsetTerm::Add(right_base, right_index),
                    ) if left_base == right_base => (left_index.as_ref(), right_index.as_ref()),
                    (left, right) => (left, right),
                };
                proof
                    .facts()
                    .load_equalities_mentioning(&Proposition::ConditionIs(
                        ConditionTerm::PointerOffsetEqual(
                            Box::new(left.clone()),
                            Box::new(right.clone()),
                        ),
                        *value,
                    ))
            }
            _ => proof.facts().load_equalities_mentioning(&goal),
        };
        let equalities = equality_candidates
            .into_iter()
            .chain(proof.facts().algebraic_equalities_mentioning(&goal));
        let mut has_source_candidate = false;
        for equality in equalities {
            // A reflexive equality cannot change the checked goal.
            // Avoid reconstructing source spellings for these pointer
            // metadata facts before the rewrite.
            if is_reflexive_pointer_equality(&equality) {
                continue;
            }
            // A registered read definition remains available to the
            // kernel, but cannot supply a source rewrite. Do not search
            // recorded states for a spelling of this metadata.
            if crate::kernel::is_verified_load_variable_defining_fact(&equality) {
                continue;
            }
            let equality_has_literal_endpoint = rewrite_equality_sides(&equality)
                .is_some_and(|(left, right)| is_rewrite_literal(left) || is_rewrite_literal(right))
                || matches!(
                    &equality,
                    Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)
                        if matches!(&**left, crate::kernel::IntegerTerm::Constant(_))
                            || matches!(&**right, crate::kernel::IntegerTerm::Constant(_))
                );
            if exclude_goal_fact
                && (equality == goal
                    || swapped_bitvector_equality(&equality).is_some_and(|swapped| swapped == goal))
            {
                continue;
            }
            let (surface, candidate_proof) =
                match crate::kernel::search::ProofSearch::available_rewrite_equality(
                    proof, &equality,
                ) {
                    Some(surface) => (surface, proof.clone()),
                    None => {
                        match crate::kernel::search::ProofSearch::try_goal_operand_constant_equality(
                            proof, &equality,
                        ) {
                            Some(candidate) => candidate,
                            None => continue,
                        }
                    }
                };
            has_source_candidate = true;
            let proof = &candidate_proof;
            // `available_surface_fact` has already resolved the spelling
            // that still lowers to this fact, anchoring a stale constructor
            // equality at function entry when the written form stopped
            // denoting it, so only the orientation is open here.
            let reverse = reverse_surface_equality(&surface);
            for oriented in std::iter::once(surface).chain(reverse) {
                // Automatic refinement reduces symbolic operands to known
                // literals. Expanding a literal into an alias creates
                // irrelevant branches, especially after a folded cast or
                // unsigned-order bias. An explicit `rewrite` still permits
                // that checked direction.
                if equality_has_literal_endpoint {
                    let literal_endpoint = |kernel: &Proposition, source: bool| {
                        rewrite_equality_sides(kernel).is_some_and(|(left, right)| {
                            is_rewrite_literal(if source { left } else { right })
                        }) || matches!(kernel, Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)
                            if matches!(if source { &**left } else { &**right }, crate::kernel::IntegerTerm::Constant(_)))
                    };
                    // A retained source spelling may be a proxy for a
                    // symbolic operand. Trust its recorded lowering, not
                    // the spelling's apparent literal syntax.
                    let source_is_literal = surface_facts
                    .available_kernel_matching(&oriented, |fact| proof.facts().contains(fact))
                    .map(|kernel| literal_endpoint(kernel, true))
                    .or_else(|| {
                        let reverse = reverse_surface_equality(&oriented)?;
                        surface_facts.available_kernel_matching(&reverse, |fact| proof.facts().contains(fact))
                            .map(|kernel| literal_endpoint(kernel, false))
                    })
                    .unwrap_or_else(|| matches!(&oriented, ClickProposition::Comparison { left, .. } if surface_expression_is_constant(left)));
                    if source_is_literal {
                        continue;
                    }
                }
                // Each candidate is one checked rewrite and a direct closer.
                // Observe the tactic's deadline and work budget between
                // candidates, including when none can close.
                if crate::instrumentation::deadline_exceeded() {
                    return Continue(());
                }
                let rewrite = proof.driver().apply_step(ProofStep::Rewrite(oriented));
                let Ok(rewritten) = rewrite else {
                    continue;
                };
                if rewritten.goal() == proof.goal() {
                    continue;
                }
                // Checked rewrites preserve this obligation. Once one
                // reaches a refuted scalar equality, more equivalent
                // rewrites or function expansions cannot help the search.
                if crate::kernel::search::ProofSearch::scalar_offset_goal_is_refuted(&(rewritten)) {
                    if !exclude_goal_fact
                        && let Some(closed) =
                            crate::kernel::search::ProofSearch::try_direct_logical_closure(
                                &(rewritten),
                            )
                            .ok()
                            .flatten()
                    {
                        return Break(Some(closed));
                    }
                    return Break(None);
                }
                let closure_key = rewritten
                    .goal()
                    .and_then(proposition_identity_key)
                    .map(|goal| {
                        (
                            crate::kernel::assumptions::unsalted_assumptions_memo_id(
                                rewritten.facts().assumptions(),
                            ),
                            goal,
                        )
                    });
                let fresh_closure =
                    closure_key.is_none_or(|key| attempted_closures.borrow_mut().insert(key));
                if fresh_closure
                    && let Some(closed) =
                        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(rewritten))
                            .ok()
                            .flatten()
                {
                    return Break(Some(closed));
                }
            }
        }
        if has_source_candidate {
            Continue(())
        } else {
            // No indexed source equality can start a chain at this goal.
            // In particular, internal store records must not trigger a
            // connected-component walk merely because they mention it.
            Break(None)
        }
    }

    pub(in crate::surface::proof) fn try_typed_atomic_solve_from_selected_premises(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_typed_atomic_solve_from_selected_premises");
        let goal = search_input.goal()?.clone();
        if premise_pairs
            .iter()
            .any(|(kernel, _)| selected_premise_contains_goal(kernel, &goal))
        {
            return search_input
                .driver()
                .apply_step(ProofStep::Known)
                .ok()
                .filter(Proof::is_complete);
        }
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        match plan_solve_certificate(&goal, &assumptions_from_propositions(&restricted))? {
            SolveEvidence::Known => {
                crate::kernel::search::ProofSearch::apply_normalization_closure(search_input, None)
                    .ok()
                    .filter(Proof::is_complete)
            }
            SolveEvidence::Derivation(derivation) => {
                crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                    search_input,
                    &goal,
                    &derivation,
                    premise_pairs,
                )
            }
        }
    }

    /// Weakens a constant bound. A goal `value >= c` (or `value <= c`)
    /// closes from a stronger context bound `value >= C` with `C >= c`
    /// (`value <= C` with `C <= c`), the shape a loop's negated guard leaves
    /// on its counter. The proof cites only facts it establishes itself, two
    /// nested `have`s closed by the direct logical closer, so the context
    /// bound needs no Surface spelling; the transitivity theorem then closes
    /// the goal.
    pub(in crate::surface::proof) fn try_selected_constant_bound_weakening(
        search_input: &Proof<'a>,
        goal: &Proposition,
        derivation: &PropositionDerivation,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_constant_bound_weakening");
        let surface_goal = search_input.surface_goal()?.clone();
        let (goal_value, goal_bound, lower_bound) = match goal {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: value,
                    right: bound,
                },
                true,
            ) => (value, bound, true),
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: value,
                    right: bound,
                },
                true,
            ) => (value, bound, false),
            _ => return None,
        };
        let bits32_constant!(goal_bits) = goal_bound.as_ref() else {
            return None;
        };
        let goal_constant = constant_u32(*goal_bits) as i32;
        let (surface_lower, surface_upper) = surface_nonstrict_parts(&surface_goal)?;
        let (surface_value, surface_goal_constant) = if lower_bound {
            (surface_upper, surface_lower)
        } else {
            (surface_lower, surface_upper)
        };
        let mut candidates = Vec::new();
        for premise in derivation.context_premises().iter() {
            let Proposition::ConditionIs(term, polarity) = premise else {
                continue;
            };
            let bound = match (term, polarity, lower_bound) {
                (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: value,
                        right: bound,
                    },
                    true,
                    true,
                )
                | (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: value,
                        right: bound,
                    },
                    false,
                    true,
                )
                | (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: value,
                        right: bound,
                    },
                    true,
                    false,
                )
                | (
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: value,
                        right: bound,
                    },
                    false,
                    false,
                ) if value == goal_value => bound,
                _ => continue,
            };
            let bits32_constant!(bits) = bound.as_ref() else {
                continue;
            };
            let constant = constant_u32(*bits) as i32;
            let stronger = if lower_bound {
                constant > goal_constant
            } else {
                constant < goal_constant
            };
            if stronger && !candidates.contains(&constant) {
                candidates.push(constant);
            }
        }
        let operator = if lower_bound {
            ComparisonOperator::GreaterEqual
        } else {
            ComparisonOperator::LessEqual
        };
        for constant in candidates {
            let surface_constant = ContractExpression::ProgramExpression(ProgramExpression::Value(
                int32(constant as u32),
            ));
            let bound_surface = ClickProposition::Comparison {
                left: surface_value.clone(),
                operator,
                right: surface_constant.clone(),
            };
            let link_surface = ClickProposition::Comparison {
                left: surface_constant.clone(),
                operator,
                right: surface_goal_constant.clone(),
            };
            let Ok(scope) = search_input.driver().open_have(bound_surface.clone()) else {
                continue;
            };
            let Some(scope) = (scope).driver().try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let Ok(scope) = proof.driver().open_have(link_surface.clone()) else {
                continue;
            };
            let Some(scope) = scope.driver().try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let composed = ClickProposition::Comparison {
                left: surface_value.clone(),
                operator,
                right: surface_goal_constant.clone(),
            };
            let Ok(applied) = proof
                .driver()
                .have_by_integer_arithmetic(composed, vec![bound_surface, link_surface])
            else {
                continue;
            };
            if applied.is_complete() {
                return Some(applied);
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                    .ok()
                    .flatten()
            {
                return Some(closed);
            }
        }
        None
    }

    /// Closes an unsigned order goal that is one step of uint32 arithmetic
    /// from an exact fact: a predecessor, a successor under a strict bound,
    /// or the descent of a difference, by the uint32 lemma that states that
    /// wrapping step, or one comparison read the other way round, by Integer
    /// arithmetic.
    ///
    /// The goal's shape names the step and the one premise it needs, which
    /// is looked up exactly, so the work is a fixed number of lookups
    /// whatever the context holds.
    pub(in crate::surface::proof) fn try_unsigned_order_step(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_order_step");
        crate::kernel::search::ProofSearch::try_unsigned_order_step_from(
            search_input,
            &|kernel| search_input.unsigned_surface_fact(kernel),
            true,
        )
    }

    /// [`Self::try_unsigned_order_step`] with the premise taken from the
    /// surface premises a tactic lists, and from nowhere else: the step
    /// `arithmetic() using { ... }` promises to use exactly those.
    pub(in crate::surface::proof) fn try_unsigned_order_step_using(
        search_input: &Proof<'a>,
        surface_premises: &[ClickProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_order_step_using");
        // Only an unsigned order goal has a lemma, so only then are the
        // listed premises lowered.
        unsigned_order_parts(search_input.goal()?)?;
        let listed = surface_premises
            .iter()
            .filter_map(|surface| {
                let kernel = search_input
                    .lower_cited_surface_proposition(surface, "`solve() using` premise")
                    .ok()?;
                search_input
                    .facts()
                    .listed_premise_available(&kernel, &[], false)
                    .then(|| (kernel, surface.clone()))
            })
            .collect::<Vec<_>>();
        crate::kernel::search::ProofSearch::try_unsigned_order_step_from(
            search_input,
            &|kernel| {
                listed
                    .iter()
                    .find(|(listed, _)| listed == kernel)
                    .map(|(_, surface)| surface.clone())
            },
            false,
        )
    }

    pub(in crate::surface::proof) fn try_unsigned_order_step_from(
        search_input: &Proof<'a>,
        surface_fact: &dyn Fn(&Proposition) -> Option<ClickProposition>,
        reversals: bool,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_order_step_from");
        let (order, left, right) = unsigned_order_parts(search_input.goal()?)?;
        let zero = MachineTerm::constant(0);
        // The goal from one comparison read the other way round, by
        // Integer arithmetic: the premise's operands, compared the goal's
        // way. `arithmetic() using` reads such a premise itself.
        let reversed_fact = |condition: ConditionTerm, operator: ComparisonOperator| {
            if !reversals {
                return None;
            }
            let surface = surface_fact(&Proposition::ConditionIs(condition, true))?;
            let (lower, upper) = match operator {
                ComparisonOperator::LessThan | ComparisonOperator::GreaterThan => {
                    surface_strict_parts(&surface)?
                }
                _ => surface_nonstrict_parts(&surface)?,
            };
            let (left, right) = match operator {
                ComparisonOperator::LessThan | ComparisonOperator::LessEqual => (lower, upper),
                _ => (upper, lower),
            };
            let conclusion = ClickProposition::Comparison {
                left,
                operator,
                right,
            };
            let applied = search_input
                .driver()
                .have_by_integer_arithmetic(conclusion, vec![surface])
                .ok()?;
            crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                .ok()
                .flatten()
        };
        match order {
            UnsignedOrder::Less => {
                // `value - 1 <u value` from `0 <u value`.
                // A `uint32` operator is its own node, its constants
                // `uint32` ones; a word operator of the same bits reads alike.
                if let binary_term!(Bits32, Subtract, decremented, amount) = &left
                    && decremented.as_ref() == &right
                    && amount.constant32() == Some(1)
                {
                    if let Some((proof, premise, _, value)) =
                        Self::try_unsigned_strict_fact(search_input, &zero, &right, surface_fact)
                    {
                        return proof.driver().close_with_unsigned_lemma(
                            "click::integer::uint32_positive_predecessor_strictly_decreases",
                            vec![value],
                            premise,
                        );
                    }
                    // The value is a difference `upper - lower`, nonzero
                    // because `lower <u upper`.
                    if let binary_term!(Bits32, Subtract, upper, lower) = &right
                        && let Some((proof, premise, lower, upper)) =
                            Self::try_unsigned_strict_fact(search_input, lower, upper, surface_fact)
                    {
                        // Keep this wrapping difference native when expansion
                        // reads it back in Integer specification arithmetic.
                        let difference = ContractExpression::CUnary {
                            operand: Box::new(ContractExpression::Subtract(
                                Box::new(upper.clone()),
                                Box::new(lower.clone()),
                            )),
                            lowered: ProgramExpression::Cast {
                                expression: Box::new(ProgramExpression::Value(int32(0))),
                                target_type: ProgramType::UInt32,
                                integer_mode: crate::kernel::IntegerCastMode::CConversion,
                                pointee_struct: None,
                                pointee_volatile: false,
                                pointee_constant: false,
                                explicit_qualification: false,
                            },
                        };
                        let positive = ClickProposition::Comparison {
                            left: ContractExpression::ProgramExpression(ProgramExpression::Value(
                                ProgramValue::UInt32(MachineTerm::uint32_constant(0)),
                            )),
                            operator: ComparisonOperator::LessThan,
                            right: difference.clone(),
                        };
                        let proof = proof.driver().apply_step(ProofStep::ApplyTheoremUsing {
                                application: TheoremApplication {
                                    name: "click::integer::uint32_less_than_implies_positive_difference"
                                        .to_string(),
                                    arguments: vec![lower, upper],
                                },
                                premises: vec![premise],
                            })
                            .ok()?;
                        return proof.driver().close_with_unsigned_lemma(
                            "click::integer::uint32_positive_predecessor_strictly_decreases",
                            vec![difference],
                            positive,
                        );
                    }
                    return None;
                }
                // `(0 - value) + (bound - 1) <u (0 - value) + bound` from
                // `value <u bound`: the affine forms a measure `bound -
                // value` over a constant evaluates to.
                if let (
                    binary_term!(Bits32, Add, left_base, left_offset),
                    binary_term!(Bits32, Add, right_base, right_offset),
                ) = (&left, &right)
                    && left_base == right_base
                    && let binary_term!(Bits32, Subtract, negated_zero, value) = left_base.as_ref()
                    && negated_zero.constant32() == Some(0)
                    && let (Some(lower), Some(bound)) =
                        (left_offset.as_const(), right_offset.as_const())
                    && bound != 0
                    && lower == bound - 1
                    && let Some((proof, premise, value, bound)) = Self::try_unsigned_strict_fact(
                        search_input,
                        value,
                        right_offset,
                        surface_fact,
                    )
                {
                    return proof.driver().close_with_unsigned_lemma(
                        "click::integer::uint32_difference_decreases_after_increment",
                        vec![value, bound],
                        premise,
                    );
                }
                reversed_fact(
                    ConditionTerm::unsigned_greater_than(right, left),
                    ComparisonOperator::LessThan,
                )
            }
            UnsignedOrder::LessEqual => {
                // `value + 1 <=u upper` from `value <u upper`.
                if let binary_term!(Bits32, Add, value, amount) = &left
                    && amount.constant32() == Some(1)
                    && let Some((proof, premise, value, upper)) =
                        Self::try_unsigned_strict_fact(search_input, value, &right, surface_fact)
                {
                    return proof.driver().close_with_unsigned_lemma(
                        "click::integer::uint32_increment_upper_bound",
                        vec![value, upper],
                        premise,
                    );
                }
                reversed_fact(
                    ConditionTerm::unsigned_greater_equal(right, left),
                    ComparisonOperator::LessEqual,
                )
            }
            UnsignedOrder::Greater => reversed_fact(
                ConditionTerm::unsigned_less_than(right, left),
                ComparisonOperator::GreaterThan,
            ),
            UnsignedOrder::GreaterEqual => reversed_fact(
                ConditionTerm::unsigned_less_equal(right, left),
                ComparisonOperator::GreaterEqual,
            ),
        }
    }

    pub(in crate::surface::proof) fn try_selected_predecessor_upper_bound(
        search_input: &Proof<'a>,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_predecessor_upper_bound");
        if !matches!(search_input.context.as_ref(), ProofContext::FixedState(_)) {
            return None;
        }
        let Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: predecessor,
                right: goal_upper,
            },
            true,
        ) = goal
        else {
            return None;
        };
        let binary_term!(Int32, Subtract, value, amount) = predecessor.as_ref() else {
            return None;
        };
        if amount.as_ref() != &MachineTerm::constant(1) {
            return None;
        }
        let upper_kernel = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: value.clone(),
                right: goal_upper.clone(),
            },
            true,
        );
        let (_, upper_surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == &upper_kernel)?;
        let (surface_value, _) = surface_nonstrict_parts(upper_surface)?;
        let nonnegative_surface = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: surface_value.clone(),
        };
        for (kernel, surface) in premise_pairs {
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) = kernel
            else {
                continue;
            };
            let selected_constant = if left.as_ref() == value.as_ref() {
                right.as_ref()
            } else if right.as_ref() == value.as_ref() {
                left.as_ref()
            } else {
                continue;
            };
            let bits32_constant!(bits) = selected_constant else {
                continue;
            };
            if (constant_u32(*bits) as i32) < 0 {
                continue;
            }
            let mut orientations = vec![surface.clone()];
            if let Some(reverse) = reverse_surface_equality(surface)
                && reverse != *surface
            {
                orientations.push(reverse);
            }
            for equality in orientations {
                let scope = search_input
                    .driver()
                    .open_have(nonnegative_surface.clone())
                    .ok()?;
                let Ok(scope) = scope.driver().apply_step(ProofStep::Rewrite(equality)) else {
                    continue;
                };
                let Some(scope) = (scope).driver().try_direct_logical_closure().ok().flatten()
                else {
                    continue;
                };
                let joined = scope.join().ok()?;
                // `arithmetic() using` the two premises would need the goal's
                // source form, which a fixed-state goal may lack; the
                // certificate it expands to is planned from the premises'
                // kernel forms and spells the goal from their operands.
                let nonnegative_kernel = joined
                    .lower_surface_proposition_direct(
                        &nonnegative_surface,
                        "nonnegative predecessor premise",
                    )
                    .ok()?;
                let listed = [nonnegative_surface.clone(), upper_surface.clone()];
                let pairs = [
                    (nonnegative_kernel, nonnegative_surface.clone()),
                    (upper_kernel.clone(), upper_surface.clone()),
                ];
                let Some(ProofTactic::ArithmeticCertificate(certificate)) =
                    joined.arithmetic_certificate_from_recorded(goal, &listed, &pairs)
                else {
                    continue;
                };
                let Ok(applied) = joined
                    .driver()
                    .apply_step(ProofStep::ArithmeticCertificate(certificate))
                else {
                    continue;
                };
                if applied.is_complete() {
                    return Some(applied);
                }
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                        .ok()
                        .flatten()
                {
                    return Some(closed);
                }
            }
        }
        None
    }

    /// Disjunctive syllogism: the goal is one disjunct of an available
    /// disjunction whose every other disjunct the context refutes exactly,
    /// as `x <= MAX / rhs` is from `rhs == 0 or x <= MAX / rhs` under
    /// `rhs != 0`. The disjunction is eliminated by `cases`, the refuted arms
    /// closing by `contradiction`. Candidates are the context's disjunction
    /// facts, each refutation one exact lookup.
    pub(in crate::surface::proof) fn try_disjunctive_syllogism_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_disjunctive_syllogism_closure");
        let goal = search_input.goal()?.clone();
        if !matches!(goal, Proposition::ConditionIs(_, _)) {
            return None;
        }
        let assumptions = search_input.facts().assumptions();
        let refuted = |disjunct: &Proposition| {
            let negated = match disjunct {
                Proposition::ConditionIs(condition, value) => {
                    Proposition::ConditionIs(condition.clone(), !value)
                }
                other => Proposition::Not(Box::new(other.clone())),
            };
            assumptions.states_required_goal(&negated)
        };
        let candidates = crate::kernel::search::disjunction_candidates(assumptions)
            .filter(|disjunction| {
                let disjuncts = flattened_disjuncts(disjunction);
                disjuncts.iter().any(|disjunct| **disjunct == goal)
                    && disjuncts
                        .iter()
                        .filter(|disjunct| ***disjunct != goal)
                        .all(|disjunct| refuted(disjunct))
            })
            .cloned()
            .collect::<Vec<_>>();
        let frontier_anchor = match search_input.context.as_ref() {
            ProofContext::Execution(_) if search_input.focused_outcome_data().is_none() => {
                search_input.execution().map(|execution| ProgramPointRef {
                    region: CodeRegionRef::Region(execution.core.frontier.next_statement_index),
                    kind: ProgramPointKind::Entry,
                })
            }
            _ => None,
        };
        let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &search_input.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        candidates.into_iter().find_map(|disjunction| {
            let surface = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surface_facts,
                premise_anchor,
                &disjunction,
            )?;
            crate::kernel::search::ProofSearch::try_selected_disjunction_cases(
                search_input,
                &[(disjunction, surface)],
            )
        })
    }

    /// Eliminates one disjunction selected by the kernel derivation and
    /// proves both arms on their branch-local `Proof`s. The disjunction is
    /// never reopened once either disjunct is already available, which makes
    /// recursive branch search descend through distinct case assumptions.
    pub(in crate::surface::proof) fn try_selected_disjunction_cases(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_disjunction_cases");
        for (kernel, surface) in premise_pairs {
            let Proposition::Or(left, right) = kernel else {
                continue;
            };
            if search_input.facts().contains(left) || search_input.facts().contains(right) {
                continue;
            }
            let (surface_left, surface_right) = match surface {
                ClickProposition::Or(left, right) => {
                    (left.as_ref().clone(), right.as_ref().clone())
                }
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    let ClickProposition::Or(left, right) = proposition.as_ref() else {
                        continue;
                    };
                    (
                        ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(left.as_ref().clone()),
                        },
                        ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(right.as_ref().clone()),
                        },
                    )
                }
                _ => continue,
            };
            // The in-`Proof` split: both case goals coexist in one state,
            // each arm is proven by focusing its recorded id on this one
            // lineage, and the join partitions the retained steps by the
            // per-step goal attribution recorded when they were applied.
            let Ok((split_proof, split, ids)) = search_input.split_focused_cases(surface.clone())
            else {
                continue;
            };
            let marker = split_proof.checkpoint();
            let branch_surfaces = [&surface_left, &surface_right];
            let mut proof = split_proof;
            let mut complete = true;
            for (index, (id, assumed_surface)) in ids.into_iter().zip(branch_surfaces).enumerate() {
                let Ok(focused_branch) = proof.focus_branch(id) else {
                    complete = false;
                    break;
                };
                let selected = focused_branch
                    .driver()
                    .apply_step(ProofStep::Contradiction(assumed_surface.clone()))
                    .ok()
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::try_solve_closure(&(focused_branch))
                            .ok()
                            .flatten()
                    })
                    .or_else(|| {
                        let (goal_left, goal_right) =
                            surface_logical_children(focused_branch.surface_goal()?, false)?;
                        let selected_goal = if index == 0 { goal_left } else { goal_right };
                        let scope = focused_branch.driver().open_have(selected_goal).ok()?;
                        let rewritten = scope
                            .driver()
                            .apply_step(ProofStep::Rewrite(assumed_surface.clone()))
                            .ok()?;
                        let closed = (rewritten)
                            .driver()
                            .try_direct_logical_closure()
                            .ok()
                            .flatten()?;
                        let joined = closed.join().ok()?;
                        joined.driver().apply_step(ProofStep::Known).ok()
                    });
                let Some(selected) = selected else {
                    complete = false;
                    break;
                };
                proof = selected;
            }
            if complete
                && let Ok(joined) = proof.join_focused_cases(&marker, split, ids, surface.clone())
            {
                return Some(joined);
            }
        }
        None
    }

    /// Specializes one checkable universal premise selected by the atomic
    /// decision at the current goal. Planning only chooses the explicit
    /// quantified fact, argument, and guards; each selected operation advances
    /// this `Proof` directly.
    pub(in crate::surface::proof) fn try_selected_forall_instantiation(
        search_input: &Proof<'a>,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_forall_instantiation");
        let tactics = plan_explicit_forall_instantiation(goal, premise_pairs).or_else(|| {
            let surface_goal = search_input.surface_goal()?;
            let extra_arguments = search_input
                .proposition_obligation()
                .into_iter()
                .flat_map(|goal| goal.surface_bindings.iter())
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::ProgramExpression(ProgramExpression::Value(
                        ProgramValue::Int32(value),
                    )) => Some((
                        value.clone(),
                        ContractExpression::ProgramExpression(ProgramExpression::Variable(
                            name.clone(),
                        )),
                    )),
                    _ => None,
                })
                .collect::<Vec<_>>();
            plan_explicit_forall_instantiation_transport(
                goal,
                surface_goal,
                premise_pairs,
                &extra_arguments,
                &|conclusion| {
                    crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
                        &(search_input
                            .facts()
                            .assumptions()
                            .clone()
                            .assume_proposition(conclusion.clone())),
                        goal,
                    )
                    .is_some()
                },
            )
        })?;
        Self::try_universal_steps_with_arithmetic(search_input, &tactics)
    }

    /// Specialization can expose an arithmetic consequence without changing
    /// any read. Keep that consequence as ordinary arithmetic certificates,
    /// rather than asking legacy transport to rediscover it. This runs only
    /// in search; checking the emitted steps never enters arithmetic planning.
    fn try_universal_steps_with_arithmetic(
        search_input: &Proof<'a>,
        tactics: &[ProofTactic],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_universal_steps_with_arithmetic");
        let mut proof = search_input.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if index + 1 == tactics.len() && matches!(tactic, ProofTactic::Known) {
                    continue;
                }
                return None;
            }
            if let ProofTactic::TransportUsing { source, .. } = tactic {
                // Instantiation may already close the goal through ordinary
                // equality reasoning. Do not plan arithmetic for that case.
                if let Ok(closed) = proof.driver().apply_step(ProofStep::Known) {
                    proof = closed;
                    continue;
                }
                // This route handles arithmetic consequences of a current
                // fact. Historical reads must first be preserved; attempting
                // every arithmetic strategy before that can exhaust the
                // closer's budget on an unrelated derivation.
                let current_source = match source {
                    ClickProposition::At { proposition, .. } => proposition.as_ref(),
                    other => other,
                };
                if let Ok(scope) = proof.driver().open_have(current_source.clone())
                    && let Ok(scope) = scope.driver().apply_step(ProofStep::Known)
                    && let Ok(current) = scope.join()
                    && let Ok(Some(closed)) = Self::try_arithmetic_with_selected_premises(&current)
                {
                    proof = closed;
                    continue;
                }
            }
            let step = SourceContext::PureGoal.leaf_step(tactic)?;
            proof = proof.driver().apply_step(step).ok()?;
        }
        proof.focused_discharged().then_some(proof)
    }

    /// Tries available universal facts when the atomic decision cannot name
    /// an instantiated premise. Candidate
    /// discovery is read-only; a specialization is retained only after the
    /// ordinary `InstantiateUsing` operation advances and closes this Proof.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_indexed_forall_instantiation(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_forall_instantiation");
        crate::kernel::search::ProofSearch::try_indexed_forall_instantiation_with_surfaces(
            search_input,
            &[],
        )
    }

    pub(in crate::surface::proof) fn try_indexed_forall_instantiation_with_surfaces(
        search_input: &Proof<'a>,
        introduced_surfaces: &[ClickProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_forall_instantiation_with_surfaces");
        let goal = search_input.goal()?;
        let execution_view = matches!(search_input.context.as_ref(), ProofContext::Execution(_))
            .then(|| search_input.premise_fixed_state_view())
            .flatten();
        let surface_facts = match search_input.context.as_ref() {
            ProofContext::Pure(context) => &context.theorem_context.surface_requirements,
            ProofContext::FixedState(context) => context.surface_propositions,
            ProofContext::Execution(_) => execution_view.as_ref()?.surface_propositions,
        };
        let bound_variable_names = match search_input.proposition_obligation() {
            Some(goal) => goal
                .surface_bindings
                .iter()
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::ProgramExpression(ProgramExpression::Value(
                        ProgramValue::Int32(MachineTerm::Variable(variable)),
                    )) => Some((*variable, name.clone())),
                    _ => None,
                })
                .collect::<BTreeMap<_, _>>(),
            _ => BTreeMap::new(),
        };
        let surface_form = |fact: &Proposition| {
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                search_input
                    .lower_surface_proposition(surface, "introduced forall premise")
                    .is_ok_and(|lowered| {
                        lowered == *fact
                            || condition_polarity_equivalent(&lowered, fact)
                            || quantified_equivalent_available_fact(
                                fact,
                                std::slice::from_ref(&lowered),
                            )
                            .is_some()
                    })
            }) {
                return Some(surface.clone());
            }
            let recorded = match search_input.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(fact)
                    .next()
                    .cloned(),
                ProofContext::FixedState(context) => {
                    context.surface_propositions.surfaces(fact).next().cloned()
                }
                ProofContext::Execution(_) => execution_view
                    .as_ref()?
                    .surface_propositions
                    .surfaces(fact)
                    .next()
                    .cloned(),
            };
            let synthesized = match search_input.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => {
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        context.parameter_binding,
                        context.fixed_state.state,
                        &bound_variable_names,
                    )
                }
                ProofContext::Execution(_) => {
                    let view = execution_view.as_ref()?;
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        view.parameter_binding,
                        view.fixed_state.state,
                        &bound_variable_names,
                    )
                }
            };
            recorded.or(synthesized)
        };
        let introduced_candidates = introduced_surfaces
            .iter()
            .filter_map(|surface| {
                let quantified = surface_facts.available_kernel_matching(surface, |kernel| {
                    matches!(kernel, Proposition::ForAll { .. })
                        && search_input.facts().quantified_fact_available(kernel)
                })?;
                Some((quantified.clone(), Some(surface.clone())))
            })
            .collect::<Vec<_>>();
        let ordinary_candidates = crate::kernel::search::universal_candidates(search_input.facts())
            .take_while(|_| !crate::instrumentation::deadline_exceeded_with_work(1))
            .filter(|quantified| {
                !introduced_candidates
                    .iter()
                    .any(|(candidate, _)| candidate == *quantified)
            })
            .map(|quantified| (quantified.clone(), None));
        let quantified_candidates = introduced_candidates
            .iter()
            .cloned()
            .chain(ordinary_candidates);
        for (quantified, introduced_surface) in quantified_candidates {
            // Reject shape-incompatible universals before Surface lookup or
            // synthesis. Candidate extraction is structural and bounded by
            // this one indexed fact and the focused branch goal; the expensive
            // form work is reserved for a specialization that can
            // actually mention the goal's concrete argument.
            let candidate_values =
                crate::kernel::forall_guided_instantiation_candidate_values(&quantified, goal);
            let Proposition::ForAll { var, body, .. } = &quantified else {
                unreachable!("the universal candidate filter admits only universals")
            };
            if candidate_values.is_empty() {
                continue;
            }
            let recorded_surfaces = match search_input.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::FixedState(context) => context
                    .surface_propositions
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => execution_view?
                    .surface_propositions
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            let predicate_environment = match search_input.context.as_ref() {
                ProofContext::Pure(context) => context.spec_definitions.predicates,
                ProofContext::FixedState(context) => context.spec_definitions.predicates,
                ProofContext::Execution(context) => context.spec_definitions.predicates,
            };
            let mut surfaces = introduced_surface.into_iter().collect::<Vec<_>>();
            for recorded in recorded_surfaces {
                let candidate = match recorded {
                    ClickProposition::PredicateCall {
                        ref name,
                        ref arguments,
                    } => predicate_environment.get(name).and_then(|definition| {
                        instantiate_click_predicate_definition(definition, arguments).ok()
                    }),
                    other => Some(other),
                };
                if let Some(candidate) = candidate
                    && !surfaces.contains(&candidate)
                {
                    surfaces.push(candidate);
                }
            }
            let synthesized = match search_input.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => synthesize_surface_proposition(
                    &quantified,
                    context.parameter_binding,
                    context.fixed_state.state,
                ),
                ProofContext::Execution(_) => {
                    let view = execution_view?;
                    synthesize_surface_proposition(
                        &quantified,
                        view.parameter_binding,
                        view.fixed_state.state,
                    )
                }
            };
            if let Some(synthesized) = synthesized
                && !surfaces.contains(&synthesized)
            {
                surfaces.push(synthesized);
            }
            // Unfolding retains the opaque predicate fact alongside its
            // checked body. Reconstruct that body's exact surface form
            // from only the active predicate indexes when generic synthesis
            // cannot express it (notably byte-indexed loads).
            if surfaces.is_empty() {
                let click_function_environment = match search_input.context.as_ref() {
                    ProofContext::Pure(context) => context.spec_definitions.functions,
                    ProofContext::FixedState(context) => context.spec_definitions.functions,
                    ProofContext::Execution(context) => context.spec_definitions.functions,
                };
                for name in search_input.focused_branch_unfolds().iter() {
                    for opaque in search_input.facts().mentioning_predicate(name) {
                        let opaque_surfaces = match search_input.context.as_ref() {
                            ProofContext::Pure(context) => context
                                .theorem_context
                                .surface_requirements
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::FixedState(context) => context
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::Execution(_) => execution_view?
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                        };
                        for opaque_surface in opaque_surfaces {
                            let ClickProposition::PredicateCall {
                                name: surface_name,
                                arguments,
                            } = opaque_surface
                            else {
                                continue;
                            };
                            let Some(definition) = predicate_environment.get(&surface_name) else {
                                continue;
                            };
                            let Ok(body_surface) =
                                instantiate_click_predicate_definition(definition, &arguments)
                            else {
                                continue;
                            };
                            if unfold_predicates_in_proposition(
                                SpecDefinitions::new(
                                    predicate_environment,
                                    click_function_environment,
                                ),
                                std::slice::from_ref(name),
                                opaque,
                                search_input.facts().assumptions(),
                            )
                            .is_ok_and(|kernel| kernel == quantified)
                                && !surfaces.contains(&body_surface)
                            {
                                surfaces.push(body_surface);
                            }
                        }
                    }
                }
            }
            for surface in surfaces {
                for value in candidate_values.iter() {
                    let argument = match value {
                        bits32_constant!(bits) => Some(ContractExpression::ProgramExpression(
                            ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(
                                constant_u32(*bits),
                            ))),
                        )),
                        uint64_constant!(_) => Some(ContractExpression::ProgramExpression(
                            ProgramExpression::Value(ProgramValue::UInt64(value.clone())),
                        )),
                        int64_constant!(_) => Some(ContractExpression::ProgramExpression(
                            ProgramExpression::Value(ProgramValue::Int64(value.clone())),
                        )),
                        MachineTerm::Variable(variable) => {
                            let Some(goal) = search_input.proposition_obligation() else {
                                continue;
                            };
                            goal.surface_bindings.iter().find_map(|(name, binding)| {
                                matches!(
                                    binding,
                                    ContractExpression::ProgramExpression(ProgramExpression::Value(
                                        ProgramValue::Int32(MachineTerm::Variable(bound))
                                    )) if bound == variable
                                )
                                .then(|| {
                                    ContractExpression::ProgramExpression(
                                        ProgramExpression::Variable(name.clone()),
                                    )
                                })
                            })
                        }
                        _ => None,
                    };
                    let Some(argument) = argument else {
                        continue;
                    };
                    let instantiated =
                        substitute_int32_variable_in_proposition(body, *var, value.clone());
                    let mut guard_facts = Vec::new();
                    let mut current = &instantiated;
                    let mut guards_available = true;
                    while let Proposition::Implies(guard, consequent) = current {
                        let mut conjuncts = Vec::new();
                        atomic_conjuncts(guard, &mut conjuncts);
                        for conjunct in conjuncts {
                            if matches!(
                                normalize_proposition(conjunct),
                                NormalizedProposition::True
                            ) {
                                continue;
                            }
                            let exact = std::iter::once(conjunct.clone())
                                .chain(condition_polarity_forms(conjunct))
                                .find(|candidate| search_input.facts().contains(candidate));
                            let selected = exact.map(|fact| vec![fact]).or_else(|| {
                                crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
                                    search_input.facts().assumptions(),
                                    conjunct,
                                )
                                .map(|derivation| derivation.context_premises())
                            });
                            let Some(selected) = selected else {
                                guards_available = false;
                                break;
                            };
                            for actual in selected {
                                let Some(form) = surface_form(&actual) else {
                                    guards_available = false;
                                    break;
                                };
                                if !guard_facts
                                    .iter()
                                    .any(|(candidate, _)| candidate == &actual)
                                {
                                    guard_facts.push((actual, form));
                                }
                            }
                            if !guards_available {
                                break;
                            }
                        }
                        if !guards_available {
                            break;
                        }
                        current = consequent;
                    }
                    if !guards_available {
                        continue;
                    }
                    let instantiated_proof =
                        match search_input
                            .driver()
                            .apply_step(ProofStep::InstantiateUsing {
                                quantified: surface.clone(),
                                argument: argument.clone(),
                                premises: Some(
                                    guard_facts
                                        .iter()
                                        .map(|(_, surface)| surface.clone())
                                        .collect(),
                                ),
                            }) {
                            Ok(proof) => proof,
                            Err(_) => continue,
                        };
                    let conclusion = current.clone();
                    if &conclusion == goal || conclusion.clone() == goal.clone() {
                        // The instantiation added the goal, so it closed it.
                        if instantiated_proof.is_complete() {
                            return Some(instantiated_proof);
                        }
                        continue;
                    }

                    let transport_assumptions = search_input
                        .facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone());
                    let Some(transport_derivation) =
                        crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
                            &(transport_assumptions),
                            goal,
                        )
                    else {
                        continue;
                    };
                    let mut transport_surfaces = Vec::new();
                    let mut transport_written = true;
                    for premise in transport_derivation.context_premises() {
                        if premise == conclusion {
                            continue;
                        }
                        if matches!(premise, Proposition::ForAll { .. })
                            && quantified_equivalent_available_fact(
                                &premise,
                                std::slice::from_ref(&quantified),
                            )
                            .is_some()
                        {
                            // `InstantiateUsing` has already checked this
                            // universal and published its selected conclusion.
                            // Do not feed the quantified source back into the
                            // following transport as an unrelated premise.
                            continue;
                        }
                        let Some(form) = surface_form(&premise) else {
                            transport_written = false;
                            break;
                        };
                        if !transport_surfaces.contains(&form) {
                            transport_surfaces.push(form);
                        }
                    }
                    if !transport_written {
                        continue;
                    }
                    let (selector, quantified_surface) = match &surface {
                        ClickProposition::At {
                            selector,
                            proposition,
                        } => (Some(selector.clone()), proposition.as_ref()),
                        other => (None, other),
                    };
                    let ClickProposition::ForAll {
                        name,
                        body: surface_body,
                        ..
                    } = quantified_surface
                    else {
                        continue;
                    };
                    let substitutions = std::iter::once((name.clone(), argument.clone()))
                        .collect::<BTreeMap<_, _>>();
                    let Ok(mut source) = substitute_click_proposition(surface_body, &substitutions)
                    else {
                        continue;
                    };
                    while let ClickProposition::Implies(_, body) = source {
                        source = *body;
                    }
                    if let Some(selector) = selector {
                        source = ClickProposition::At {
                            selector,
                            proposition: Box::new(source),
                        };
                    }
                    transport_surfaces.insert(0, source.clone());
                    let target = search_input.surface_goal()?.clone();
                    match crate::kernel::search::ProofSearch::try_fact_transport_from_candidates(
                        &(instantiated_proof),
                        &source,
                        &target,
                        transport_surfaces,
                    ) {
                        Ok(Some(transported)) if transported.focused_discharged() => {
                            return Some(transported);
                        }
                        Ok(_) | Err(_) => {}
                    }
                }
            }
        }
        None
    }

    /// Builds the binder-introduction chain from only the universal premises
    /// selected by the atomic decision. The planner never scans the ambient
    /// fact set; every resulting refinement applies directly to this `Proof`.
    pub(in crate::surface::proof) fn try_selected_forall_goal(
        search_input: &Proof<'a>,
        goal: &Proposition,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_forall_goal");
        let tactics = plan_explicit_forall_goal_from_premises(goal, surface_goal, premise_pairs)?;
        if tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Have(_)))
        {
            search_input
                .driver()
                .try_generated_linear_script(&tactics)
                .ok()
                .flatten()
        } else {
            Self::try_universal_steps_with_arithmetic(search_input, &tactics)
        }
    }

    /// Retains the pointwise unchanged-load certificate for a guarded
    /// universal outcome. The kernel derivation has already selected the
    /// finite context premises relevant to this goal; after introducing the
    /// binder and guard, transport searches only those forms plus the
    /// freshly extracted guard leaves.
    pub(in crate::surface::proof) fn try_selected_unchanged_load_forall_goal(
        search_input: &Proof<'a>,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_unchanged_load_forall_goal");
        search_input.focused_outcome_data()?;
        let mut cursor = surface_goal;
        let mut proof = search_input.clone();
        let mut introduced_forall = false;
        while let ClickProposition::ForAll { body, .. } = cursor {
            proof = proof.driver().apply_step(ProofStep::Intro).ok()?;
            cursor = body;
            introduced_forall = true;
        }
        if !introduced_forall {
            return None;
        }
        let ClickProposition::Implies(antecedent, _) = cursor else {
            return None;
        };
        proof = proof.driver().apply_step(ProofStep::Intro).ok()?;
        let mut guard_surfaces = Vec::new();
        collect_surface_conjunct_leaves(antecedent, &mut guard_surfaces);
        for guard in &guard_surfaces {
            proof = proof
                .driver()
                .apply_step(ProofStep::Extract(guard.clone()))
                .ok()?;
        }
        let target = proof.surface_goal()?.clone();
        let source = old_reflexive_transport_source(&target)?;
        let source_pairs = proof
            .lower_surface_proposition(&source, "unchanged-load transport source")
            .ok()
            .and_then(|kernel| {
                crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    proof.facts().assumptions(),
                    &kernel,
                )
            })
            .and_then(|derivation| {
                let data = proof.focused_outcome_data()?;
                let pairs = derivation
                    .context_premises()
                    .into_iter()
                    .filter_map(|premise| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            &(proof),
                            &data.surface_propositions,
                            data.premise_anchor.as_ref(),
                            &premise,
                        )
                        .map(|surface| (premise, surface))
                    })
                    .collect::<Vec<_>>();
                Some(pairs)
            })
            .unwrap_or_default();
        let data = proof.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let view = proof.outcome_fixed_state_view()?;
        let anchor_state = view.fixed_state.recorded_states.get(anchor)?;
        let mut anchored_candidates = Vec::new();
        for (kernel, _) in premise_pairs.iter().chain(&source_pairs) {
            let Some(surface) =
                synthesize_surface_proposition(kernel, view.parameter_binding, anchor_state)
            else {
                continue;
            };
            let Ok(surface) = surface_at_program_point(&surface, anchor) else {
                continue;
            };
            let Some((left, right)) = surface_nonstrict_parts(&surface) else {
                continue;
            };
            let left_is_atomic_variable = match &left {
                ContractExpression::ProgramExpression(ProgramExpression::Variable(_)) => true,
                ContractExpression::At { expression, .. } => matches!(
                    expression.as_ref(),
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(_))
                ),
                _ => false,
            };
            if left == right || !left_is_atomic_variable || anchored_candidates.contains(&surface) {
                continue;
            }
            let Ok(lowered) =
                proof.lower_surface_proposition(&surface, "unchanged-load transport premise")
            else {
                continue;
            };
            if lowered == *kernel || condition_polarity_equivalent(&lowered, kernel) {
                anchored_candidates.push(surface);
            }
        }
        // The source derivation must identify one exact non-strict bound at
        // the outcome anchor. Ambiguity is a prompt miss, never permission to
        // probe combinations of historical facts.
        let [anchored_candidate] = anchored_candidates.as_slice() else {
            return None;
        };
        let candidates = std::iter::once(anchored_candidate.clone()).chain(guard_surfaces);
        let transported = match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
            &(proof),
            &source,
            &target,
            candidates,
        ) {
            Ok(Some(transported)) => transported,
            Ok(None) | Err(_) => return None,
        };
        if transported.is_complete() {
            return Some(transported);
        }
        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(transported))
            .ok()
            .flatten()
    }

    pub(in crate::surface::proof) fn try_typed_atomic_solve_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_typed_atomic_solve_closure");
        let (goal, derivation, premise_pairs) =
            crate::kernel::search::ProofSearch::selected_solve_derivation(search_input, false)?;
        // Resource unfolding records the body conjunction as one checked
        // fact.  Special derivations cite the exact relation leaf, so expose
        // that leaf through the ordinary checked `extract` transition before
        // constructing a certificate.  This keeps certificate premises
        // top-level and preserves the source spelling/state that produced
        // the resource fact.
        match crate::kernel::search::ProofSearch::extract_special_conjunct_premises(
            search_input,
            &derivation,
            &premise_pairs,
        ) {
            Ok(Some(extracted)) if extracted.is_complete() => Some(extracted),
            Ok(Some(extracted)) => {
                crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                    &(extracted),
                    &goal,
                    &derivation,
                    &premise_pairs,
                )
            }
            Ok(None) => crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                search_input,
                &goal,
                &derivation,
                &premise_pairs,
            ),
            Err(()) => crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                search_input,
                &goal,
                &derivation,
                &premise_pairs,
            ),
        }
    }

    pub(in crate::surface::proof) fn extract_special_conjunct_premises(
        search_input: &Proof<'a>,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Result<Option<Proof<'a>>, ()> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("extract_special_conjunct_premises");
        let exact_sources = premise_pairs
            .iter()
            .map(|(kernel, surface)| (kernel, surface))
            .collect::<BTreeMap<_, _>>();
        let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => {
                (context.surface_propositions, context.premise_anchor.clone())
            }
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.clone()),
                None => {
                    let execution = search_input.execution().ok_or(())?;
                    (
                        &execution.presentation.surface_propositions,
                        frontier_premise_anchor(execution),
                    )
                }
            },
        };
        let mut proof = search_input.clone();
        let mut extracted = false;
        for premise in derivation.context_premises().iter() {
            check_verification_deadline().map_err(|_| ())?;
            if proof.facts().contains_top_level(premise)
                || !proof.facts().contains_proper_conjunct(premise)
            {
                continue;
            }
            // The selected derivation and its exact Surface correspondence
            // are one candidate. Do not resolve the spelling again after a
            // checked transition: at an execution outcome the same written
            // load may then denote a different memory state.
            let source = exact_sources
                .get(premise)
                .copied()
                .cloned()
                .or_else(|| {
                    crate::kernel::search::ProofSearch::available_surface_fact(
                        &(proof),
                        surface_facts,
                        premise_anchor.as_ref(),
                        premise,
                    )
                })
                .or_else(|| {
                    premise_anchor.as_ref().and_then(|_| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            &(proof),
                            surface_facts,
                            None,
                            premise,
                        )
                    })
                })
                .ok_or(())?;
            let successor = proof
                .driver()
                .apply_step(ProofStep::Extract(source))
                .map_err(|_| ())?;
            // `extract(source)` proves only the proposition to which `source`
            // lowers in this successor's context. A stale presentation record
            // can therefore make the step succeed without publishing the
            // exact premise selected above. Exact top-level membership is the
            // progress measure; polarity or state conversion requires its
            // own checked proof step rather than being assumed here.
            if !successor.checked_facts().contains(premise) {
                return Err(());
            }
            // Extracting a premise can also discharge the goal. Its checked
            // completion is sufficient; later premises require an open goal.
            if successor.is_complete() {
                return Ok(Some(successor));
            }
            proof = successor;
            extracted = true;
        }
        Ok(extracted.then_some(proof))
    }

    /// Searches from exactly the Surface premises named by `solve() using`.
    /// This query cannot add facts or close the goal: it returns only the
    /// descendant obtained by checking the typed atomic decision through the
    /// ordinary Proof transitions.
    pub(in crate::surface::proof) fn try_restricted_solve_closure(
        search_input: &Proof<'a>,
        surfaces: &[ClickProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restricted_solve_closure");
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_restricted_solve_closure_before_arithmetic(
                search_input,
                surfaces,
            )
        {
            return Some(closed);
        }
        // What the closers above miss goes to the arithmetic engine, as
        // `arithmetic() using` sends it: a bound from the goal's own terms,
        // a sum or chain over the premises, or a refutation of
        // contradictory ones. It comes last so a goal they close keeps its
        // expansion.
        search_input
            .driver()
            .apply_step(ProofStep::ArithmeticUsing(surfaces.to_vec()))
            .ok()
            .filter(|closed| closed.is_complete() || closed.focused_discharged())
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_listed_operation_identities(
                    search_input,
                    surfaces,
                )
                .ok()
                .flatten()
            })
    }

    /// Establish the goal's machine-operation identities from only the
    /// listed bounds and type ranges, then retry arithmetic with those
    /// explicit identities. Each bound and identity remains in expansion.
    pub(in crate::surface::proof) fn try_listed_operation_identities(
        search_input: &Proof<'a>,
        surfaces: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_listed_operation_identities");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        if integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let premises = surfaces
            .iter()
            .map(|surface| {
                search_input.lower_cited_surface_proposition(surface, "operation identity premise")
            })
            .collect::<Result<Vec<_>, _>>()?;
        let identities = operation_identities(machine_observations(goal, &premises));
        if identities.is_empty() {
            return Ok(None);
        }
        let written =
            written_integer_observations(std::iter::once(surface_goal).chain(surfaces.iter()));
        let identities = identities.iter().collect::<Vec<_>>();
        let Ok((proof, established)) =
            crate::kernel::search::ProofSearch::prove_operation_identities(
                search_input,
                &identities,
                &written,
                Some(surfaces),
            )?
        else {
            return Ok(None);
        };
        let mut premises = surfaces.to_vec();
        premises.extend(established.into_iter().map(|(_, surface)| surface));
        Ok(proof
            .driver()
            .apply_step(ProofStep::ArithmeticUsing(premises))
            .ok()
            .filter(|closed| closed.is_complete() || closed.focused_discharged()))
    }

    /// Both forms of solve select the same explicit endpoint proof. Ambient
    /// source enumeration belongs only to the unrestricted smart tactic.
    pub(in crate::surface::proof) fn try_ordinary_viewability_restriction_closure(
        search_input: &Proof<'a>,
        selected: Option<&[ClickProposition]>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_ordinary_viewability_restriction_closure");
        let Some(Proposition::MemoryLoadable { wide, .. }) = search_input.goal() else {
            return None;
        };
        let target = search_input.surface_goal()?;
        // Reject other goal shapes before selecting any ambient premises.
        let ClickProposition::Loadable { segment } = target else {
            return None;
        };
        let ContractSegmentSurface::Range { .. } = &segment.surface else {
            return None;
        };
        let recorded;
        let surfaces = match selected {
            Some(selected) => selected,
            None => {
                let map = search_input.premise_surface_facts()?;
                recorded = map
                    .requirement_kernel_atoms_for_search()
                    .filter(|atom| {
                        matches!(
                            atom,
                            Proposition::MemoryLoadable { .. } | Proposition::ConditionIs(..)
                        )
                    })
                    .map(|atom| {
                        map.recorded_requirement_surface(atom)
                            .expect("requirement atoms retain their enclosing source clause")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                &recorded
            }
        };
        for recorded_source in surfaces {
            let mut source = recorded_source;
            while let ClickProposition::At { proposition, .. } = source {
                source = proposition;
            }
            let ClickProposition::Loadable { segment } = source else {
                continue;
            };
            // A past view suggests a descriptor to try, not evidence that it
            // is still live. The ordinary observation selects an exact held
            // permission in the current state; it never follows history.
            let mut segment = segment.clone();
            segment.state = ContractSegmentState::Current;
            let source = ClickProposition::Loadable {
                segment: segment.clone(),
            };
            let prepared = (|| {
                let scope = search_input.driver().open_have(source.clone())?;
                let scope = scope.driver().apply_step(ProofStep::Known).or_else(|_| {
                    scope.driver().apply_step(ProofStep::ObserveResource(
                        ResourceClause::ViewMemory(segment),
                    ))
                })?;
                scope.join()
            })();
            let Ok(prepared) = prepared else {
                continue;
            };
            if prepared.is_complete() || prepared.focused_discharged() {
                return Some(prepared);
            }
            let mut premises = surfaces.to_vec();
            premises.push(source.clone());
            let goals = if *wide {
                rebased_viewability_restriction_steps(&source, target, &premises)
                    .or_else(|| native_viewability_restriction_steps(&source, target, &premises))
            } else {
                computed_viewability_restriction_steps(&source, target, &premises)
                    .or_else(|| native_viewability_restriction_steps(&source, target, &premises))
            };
            let Some(goals) = goals else {
                continue;
            };
            let candidate = goals
                .into_iter()
                .try_fold(prepared, |proof, (proposition, steps)| {
                    let candidate = (|| {
                        let mut scope = proof
                            .driver()
                            .open_have_with_goal_observations(proposition, true)?;
                        for step in steps {
                            scope = scope.driver().apply_step(step)?;
                        }
                        scope.join()
                    })();
                    candidate.ok()
                })
                .and_then(|proof| proof.driver().apply_step(ProofStep::Known).ok());
            if let Some(proof) = candidate
                && (proof.is_complete() || proof.focused_discharged())
            {
                return Some(proof);
            }
        }
        None
    }

    pub(in crate::surface::proof) fn try_restricted_solve_closure_before_arithmetic(
        search_input: &Proof<'a>,
        surfaces: &[ClickProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restricted_solve_closure_before_arithmetic");
        if let Some(proof) =
            Self::try_ordinary_viewability_restriction_closure(search_input, Some(surfaces))
        {
            return Some(proof);
        }
        if matches!(
            search_input.goal(),
            Some(Proposition::MemoryLoadable { .. } | Proposition::MemoryReadDefined { .. })
        ) && let Some(surface_goal) = search_input.surface_goal()
        {
            for source in surfaces
                .iter()
                .filter(|surface| matches!(surface, ClickProposition::Loadable { .. }))
            {
                let candidate = (|| {
                    let mut prepared = search_input.clone();
                    let mut premises = surfaces.to_vec();
                    if !matches!(
                        search_input.goal(),
                        Some(Proposition::MemoryLoadable { wide: true, .. })
                    ) && let Some(requirements) =
                        viewability_restriction_requirements(source, surface_goal)
                    {
                        for requirement in requirements {
                            if premises.contains(&requirement) {
                                continue;
                            }
                            let step = if matches!(
                                &requirement,
                                ClickProposition::Comparison {
                                    operator: ComparisonOperator::Equal,
                                    ..
                                }
                            ) {
                                ProofStep::Known
                            } else {
                                ProofStep::ArithmeticUsing(premises.clone())
                            };
                            prepared = prepared
                                .driver()
                                .apply_have_step(
                                    &requirement,
                                    &ProofCertificate::from_steps(vec![step]).ok()?,
                                )
                                .ok()?;
                            premises.push(requirement);
                        }
                    }
                    prepared
                        .driver()
                        .apply_step(ProofStep::TransportUsing {
                            source: source.clone(),
                            target: surface_goal.clone(),
                            premises,
                        })
                        .ok()
                        .filter(|closed| closed.is_complete())
                })();
                if candidate.is_some() {
                    return candidate;
                }
            }
        }
        if matches!(search_input.goal(), Some(Proposition::And(..)))
            && !matches!(search_input.surface_goal(), Some(ClickProposition::And(..)))
            && !search_input.goal().is_some_and(|goal| {
                crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(goal)
                    .is_some()
            })
        {
            let split = (|| {
                let (proof, split, ids) = search_input.split_focused_both().ok()?;
                let marker = proof.checkpoint();
                let left = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                    &(proof.focus_branch(ids[0]).ok()?),
                    surfaces,
                )?;
                let right = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                    &(left.focus_branch(ids[1]).ok()?),
                    surfaces,
                )?;
                right.join_focused_both(&marker, split, ids).ok()
            })();
            if split.is_some() {
                return split;
            }
        }
        // A conjunction is proved one conjunct at a time, each as a checked
        // `have` from the same listed premises, and then closed from the
        // conjuncts it added.
        if let (Some(Proposition::And(_, _)), Some(ClickProposition::And(left, right))) =
            (search_input.goal(), search_input.surface_goal())
        {
            let mut proof = search_input.clone();
            for conjunct in [left, right] {
                let scope = proof.driver().open_have(conjunct.as_ref().clone()).ok()?;
                proof = (scope)
                    .driver()
                    .try_restricted_solve_closure(surfaces)?
                    .join()
                    .ok()?;
            }
            return proof
                .driver()
                .apply_step(ProofStep::Known)
                .ok()
                .filter(Proof::is_complete);
        }
        // A named restricted premise may be a leaf of one exact available
        // conjunction (commonly after `unfold(predicate)`). Materialize that
        // leaf through the checked `extract` transition before
        // asking the restricted planner to use it. The returned descendant
        // therefore owns both the semantic fact and the Surface provenance;
        // expansion does not need to reconstruct and check a certificate to
        // justify the premise later.
        let mut proof = search_input.clone();
        for surface in surfaces {
            let kernel = proof
                .lower_surface_proposition(surface, "restricted solve premise")
                .ok()?;
            proof = proof.materialize_selected_resource_separation(&kernel)?;
            if !proof.facts().contains_top_level(&kernel)
                && !normalizes_context_free(&kernel)
                && proof.facts().contains_proper_conjunct(&kernel)
            {
                proof = proof
                    .driver()
                    .apply_step(ProofStep::Extract(surface.clone()))
                    .ok()?;
                if proof.is_complete() {
                    return Some(proof);
                }
            }
        }
        let goal = proof.goal()?;
        let premise_pairs = surfaces
            .iter()
            .map(|surface| {
                let kernel = proof
                    .lower_surface_proposition(surface, "restricted solve premise")
                    .ok()?;
                // A listed premise that lowers to a context-free truth needs
                // no ambient fact authority. Retaining it lets the restricted
                // derivation erase reflexive field equalities after the
                // outcome state has evaluated their loads. Resource
                // separation may instead be supplied by the compact
                // composition authority, so use the same checked availability
                // query without publishing unrelated member pairs.
                (proof.facts().available_across_effects(&kernel, &[])
                    || normalizes_context_free(&kernel))
                .then_some((kernel, surface.clone()))
            })
            .collect::<Option<Vec<_>>>()?;
        if crate::surface::planning::solve::computes_with_known(goal) {
            return proof
                .driver()
                .apply_step(ProofStep::Known)
                .ok()
                .filter(|closed| closed.is_complete() || closed.focused_discharged());
        }
        // A listed equality under a definedness guard the list does not
        // state: prove the guard from the other listed premises, extract the
        // consequent, and continue from the list with the consequent in the
        // implication's place.
        if let Some(closed) = crate::kernel::search::ProofSearch::try_restricted_guarded_consequent(
            &(proof),
            surfaces,
            &premise_pairs,
        ) {
            return Some(closed);
        }
        // A listed implication and its listed antecedent justify extracting
        // the consequent. Keep this route explicitly tied to `using`, rather
        // than allowing an unrelated ambient implication to discharge it.
        if premise_pairs.iter().any(|(premise, _)| {
            matches!(premise, Proposition::Implies(antecedent, consequent)
                if consequent.as_ref() == goal
                    && premise_pairs.iter().any(|(selected, _)| selected == antecedent.as_ref()))
        }) && let Some(surface_goal) = proof.surface_goal()
            && let Ok(extracted) = proof
                .driver()
                .apply_step(ProofStep::Extract(surface_goal.clone()))
        {
            if extracted.is_complete() {
                return Some(extracted);
            }
            if let Ok(closed) = extracted.driver().apply_step(ProofStep::Known)
                && closed.is_complete()
            {
                return Some(closed);
            }
        }
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        // Signed-order and definedness rules have checked named theorem
        // certificates. Try those before allocating speculative normalization
        // contexts, including for predecessor and negated-bound rules without
        // an explicit `+ 1`.
        let signed_order = signed_nonstrict_parts(goal)
            .or_else(|| signed_strict_parts(goal))
            .is_some();
        let try_typed_derivation = || {
            let SolveEvidence::Derivation(derivation) =
                plan_solve_certificate(goal, &assumptions_from_propositions(&restricted))?
            else {
                return None;
            };
            crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                &(proof),
                goal,
                &derivation,
                &premise_pairs,
            )
        };
        let arithmetic_domain = signed_definedness_operands(goal).is_some()
            || crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(goal)
                .is_some();
        let typed_first = signed_order || arithmetic_domain;
        if typed_first && let Some(closed) = try_typed_derivation() {
            return Some(closed);
        }
        if crate::kernel::proof::fact_reasoning::is_single_normalization_condition(goal)
            || !crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(goal).is_empty()
        {
            let conditions = premise_pairs
                .iter()
                .filter(|&(kernel, _surface)| !condition_polarity_forms(kernel).is_empty())
                .map(|(_kernel, surface)| surface.clone())
                .collect::<Vec<_>>();
            let condition_kernels = premise_pairs
                .iter()
                .filter(|(kernel, _)| !condition_polarity_forms(kernel).is_empty())
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            // NormalizeUsing can query its ambient graph. Restricted search
            // must first establish that this candidate works in the selected
            // context, just as its other planners use `restricted` below.
            // Build only from the explicit input; never scan ambient facts.
            if !conditions.is_empty()
                && crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                    goal,
                    &condition_kernels,
                    &crate::kernel::proof::ProofFacts::from_ordered(&restricted),
                )
                .is_ok()
                && let Ok(closed) = crate::kernel::search::ProofSearch::apply_normalization_closure(
                    &proof,
                    Some(conditions),
                )
                && closed.is_complete()
            {
                return Some(closed);
            }
        }
        if let Ok(Some(closed)) = Self::try_integer_add_le_using(&proof, surfaces) {
            return Some(closed);
        }
        // A definedness goal is left to the typed candidates and the
        // `int32_defined` / `int64_defined` closer below, so an
        // operand-specific theorem application keeps its priority.
        if let Some(surface_goal) = proof.surface_goal()
            && !arithmetic_domain
            && let Some(plan) = plan_arithmetic(ArithmeticEngine::Special, goal, &restricted)
                .and_then(ArithmeticPlan::special)
        {
            let certificate = special_plan_to_surface_certificate(
                &plan,
                &premise_pairs
                    .iter()
                    .map(|(_, surface)| surface.clone())
                    .collect::<Vec<_>>(),
                surface_goal,
            );
            if let Ok(closed) = proof
                .driver()
                .apply_step(ProofStep::ArithmeticCertificate(certificate))
                && closed.is_complete()
            {
                return Some(closed);
            }
        }
        if let Some(surface_goal) = proof.surface_goal()
            // The kernel lowering has already established the exact carrier
            // and checked terms for this goal.  Use that fact as the routing
            // predicate so fixed-state and execution proofs receive the same
            // certificate path; source-side guesses would miss converted C
            // values and could route a machine comparison incorrectly.
            && integer_affine_claim(goal).is_some()
            && restricted
                .iter()
                .all(|premise| integer_affine_claim(premise).is_some())
            && let Some(plan) = plan_arithmetic(ArithmeticEngine::IntegerAffine, goal, &restricted)
.and_then(ArithmeticPlan::integer_affine)
            && let Some(certificate) =
                integer_plan_to_surface_certificate(&plan, &premise_pairs, surface_goal)
            && let Ok(closed) = proof.driver().apply_step(ProofStep::ArithmeticCertificate(
                ArithmeticCertificate::integer(certificate),
            ))
            && closed.is_complete()
        {
            return Some(closed);
        }
        // The selected context has not changed, so the ordinary derivation
        // slot need not repeat the early attempt.
        let typed = if typed_first {
            None
        } else {
            try_typed_derivation()
        };
        typed
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_premise_equality_chain_closure(
                    &(proof),
                    &premise_pairs,
                    RewriteClosers::Listed(&premise_pairs),
                )
                .ok()
                .flatten()
            })
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_outcome_anchored_order_transitivity(
                    &(proof),
                    &premise_pairs,
                )
            })
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_outcome_anchored_increment_order(
                    &(proof),
                    &premise_pairs,
                )
            })
            // An exact selected premise or context-free normalization may
            // close directly. An arbitrary ambient `known` must remain
            // invisible through this explicitly restricted boundary.
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_typed_atomic_solve_from_selected_premises(
                    &(proof),
                    &premise_pairs,
                )
            })
            // An `int32` or `int64` definedness goal: the listed premises that
            // bound an operand by a constant, checked by the `int32_defined` /
            // `int64_defined` rule. It runs after the operand-specific `int32`
            // theorem applications above, which keep their checked form.
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_restricted_signed_definedness_closure(
                    &(proof),
                    &premise_pairs,
                )
                .ok()
                .flatten()
            })
    }

    pub(in crate::surface::proof) fn try_selected_pointer_inequality_rewrite(
        search_input: &Proof<'a>,
        goal: &Proposition,
        premises: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_pointer_inequality_rewrite");
        if !matches!(
            goal,
            Proposition::ConditionIs(ConditionTerm::PointerEqual(_, _), false)
        ) {
            return None;
        }
        for (kernel, source) in premises {
            if !matches!(
                kernel,
                Proposition::ConditionIs(ConditionTerm::PointerEqual(_, _), true)
            ) {
                continue;
            }
            let deanchored = match source {
                ClickProposition::Comparison {
                    left:
                        ContractExpression::At {
                            selector: left_selector,
                            expression: left,
                        },
                    operator: ComparisonOperator::Equal,
                    right:
                        ContractExpression::At {
                            selector: right_selector,
                            expression: right,
                        },
                } if left_selector == right_selector => Some(ClickProposition::Comparison {
                    left: left.as_ref().clone(),
                    operator: ComparisonOperator::Equal,
                    right: right.as_ref().clone(),
                }),
                _ => None,
            };
            for spelling in std::iter::once(source.clone()).chain(deanchored) {
                for oriented in
                    std::iter::once(spelling.clone()).chain(reverse_surface_equality(&spelling))
                {
                    let Ok(rewritten) = search_input
                        .driver()
                        .apply_step(ProofStep::Rewrite(oriented))
                    else {
                        continue;
                    };
                    if let Ok(Some(closed)) =
                        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(rewritten))
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    pub(in crate::surface::proof) fn check_typed_atomic_solve_candidate(
        search_input: &Proof<'a>,
        goal: &Proposition,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("check_typed_atomic_solve_candidate");
        // A direct loadability derivation already selected its source range.
        // Expand that selection through ordinary observation and containment
        // before the legacy transport planner can consume the derivation.
        if matches!(goal, Proposition::MemoryLoadable { .. }) {
            let selected = premise_pairs
                .iter()
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>();
            if let Some(proof) =
                Self::try_ordinary_viewability_restriction_closure(search_input, Some(&selected))
            {
                return Some(proof);
            }
        }
        let surface_goal = search_input.surface_goal();
        let tactics = recorded_signed_order_pairs(derivation, premise_pairs)
            .and_then(|ordered| plan_recorded_signed_order_path(goal, &ordered))
            .or_else(|| {
                let ordered = recorded_wide_order_pairs(derivation, premise_pairs)?;
                plan_recorded_wide_order_path(&ordered)
            })
            .or_else(|| plan_recorded_bitvector_equality_path(goal, derivation, premise_pairs))
            .or_else(|| {
                if !derivation.is_int32_pinned_constant_equality() {
                    return None;
                }
                let kernels = premise_pairs
                    .iter()
                    .map(|(premise, _)| premise.clone())
                    .collect::<Vec<_>>();
                let plan = plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &kernels)
                    .and_then(ArithmeticPlan::signed_int32)?;
                let certificate = search_input.signed_plan_to_surface_certificate(
                    &plan,
                    premise_pairs,
                    surface_goal?,
                )?;
                Some(vec![ProofTactic::ArithmeticCertificate(
                    ArithmeticCertificate {
                        family: ArithmeticCertificateFamily::SignedInt32(certificate),
                    },
                )])
            })
            .or_else(|| {
                plan_recorded_pointer_alignment(goal, derivation, premise_pairs, surface_goal?)
            })
            .or_else(|| plan_recorded_pointer_word(goal, derivation, premise_pairs, surface_goal?))
            .or_else(|| {
                let recorded =
                    recorded_load_address_congruence_path_pairs(derivation, premise_pairs)?;
                plan_recorded_load_address_congruence(goal, derivation, &recorded)
            })
            .or_else(|| {
                plan_explicit_loadability_transport(
                    goal,
                    search_input.surface_goal()?,
                    premise_pairs,
                )
            })
            .or_else(|| plan_pointer_advanced_load_equality(goal, premise_pairs))
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_increment_upper_bound_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_upper_bound(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_increment_constant_upper_bound_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_constant_upper_bound(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_increment_strictly_increases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_strictly_increases(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_one_plus_strictly_increases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_one_plus_strictly_increases(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_increment_below_max_is_defined_premise()?],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_below_max_is_defined(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_one_plus_below_max_is_defined_premise()?],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_one_plus_below_max_is_defined(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_nonnegative_add_within_max_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, false)?;
                let mut tactics =
                    plan_explicit_nonnegative_add_within_max_is_defined(goal, &recorded)?;
                // Outside an execution the theorem's conclusion is the exact
                // goal and closes it; its trailing `known` is dropped.
                if !matches!(search_input.context.as_ref(), ProofContext::Execution(_)) {
                    tactics.pop();
                }
                Some(tactics)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_nonnegative_subtract_within_value_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, false)?;
                plan_explicit_nonnegative_subtract_within_value_is_defined(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_increment_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_lower_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_greater_equal_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_greater_equal_lower_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_strict_greater_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_strict_greater_lower_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_strict_greater_from_strict_lower_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_strict_greater_from_strict_lower(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_increment_preserves_order_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_preserves_order(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_positive_predecessor_is_nonnegative_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_positive_predecessor_is_nonnegative(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_positive_predecessor_strictly_decreases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_positive_predecessor_strictly_decreases(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_nonnegative_predecessor_upper_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_predecessor_upper_bound(goal, &recorded, false)
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_equal_one_predecessor_is_zero_pairs(derivation, premise_pairs)?;
                plan_recorded_int32_equal_one_predecessor_is_zero(goal, derivation, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_int32_equal_one_predecessor_is_nonnegative_pairs(
                    derivation,
                    premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
                        derivation,
                        premise_pairs,
                    )
                })?;
                plan_recorded_int32_equal_one_predecessor(goal, derivation, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_int32_one_le_predecessor_is_nonnegative_pairs(
                    derivation,
                    premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_one_le_predecessor_strictly_decreases_pairs(
                        derivation,
                        premise_pairs,
                    )
                })?;
                plan_explicit_one_le_predecessor(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_le_and_not_lt_implies_equality_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                plan_explicit_le_and_not_lt_implies_eq(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_ge_and_not_gt_implies_equality_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                plan_explicit_ge_and_not_gt_implies_eq(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_positive_is_nonnegative_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_positive_is_nonnegative(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_successor_le_implies_lt_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_successor_le_implies_lt(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_constant_lower_bound_weakening_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_le_transitive_constant_lower(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_negated_strict_successor_bound_step()?
                        .premise()],
                    premise_pairs,
                    true,
                )?;
                plan_explicit_negated_strict_successor_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_le_and_neq_implies_strict_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                plan_explicit_le_and_neq_implies_lt(goal, &recorded)
            })
            .or_else(|| {
                let kernels = premise_pairs
                    .iter()
                    .map(|(premise, _)| premise.clone())
                    .collect::<Vec<_>>();
                let surface_goal = search_input.surface_goal()?;
                let plan = plan_arithmetic(ArithmeticEngine::Special, goal, &kernels)
                    .and_then(ArithmeticPlan::special)?;
                Some(vec![ProofTactic::ArithmeticCertificate(
                    special_plan_to_surface_certificate(
                        &plan,
                        &premise_pairs
                            .iter()
                            .map(|(_, surface)| surface.clone())
                            .collect::<Vec<_>>(),
                        surface_goal,
                    ),
                )])
            });
        let Some(mut tactics) = tactics else {
            if matches!(goal, Proposition::MemoryLoadable { .. }) {
                attempt::record_search_note(
                    "solve view certificate planning",
                    "no source certificate plan was produced from the resolved derivation premises",
                );
            }
            return None;
        };
        // A rule closing with Integer arithmetic names the premises it reads;
        // its certificate is planned from their recorded kernel forms, as
        // `arithmetic() using` would plan it from their lowered spellings.
        if let Some(ProofTactic::ArithmeticUsing(listed)) = tactics.last()
            && let Some(certificate) =
                search_input.arithmetic_certificate_from_recorded(goal, listed, premise_pairs)
        {
            *tactics.last_mut()? = certificate;
        }
        // The planner selects only Surface-expressible explicit operations.
        // Apply those through the same recursive Proof driver used by
        // authoritative source scripts; the plan is provenance input, not an
        // independently interpreted semantic certificate.
        let checked = search_input.driver().try_generated_linear_script(&tactics);
        if matches!(goal, Proposition::MemoryLoadable { .. })
            && let Err(error) = &checked
        {
            attempt::record_search_note("solve view certificate checking", error.raw_summary());
        }
        let proof = attempt::candidate_outcome(checked)
            .ok()
            .flatten()
            .flatten()?;
        proof.focused_discharged().then_some(proof)
    }

    /// Plan a numeric induction application against the current checked facts.
    /// Each missing domain premise is a checked have; no source-wide premise
    /// pool or parallel induction executor participates in acceptance.
    pub(in crate::surface::proof) fn apply_smart_induction(
        search_input: &Proof<'a>,
        hypothesis: &str,
        arguments: &[ContractExpression],
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_smart_induction");
        let ProofContext::Pure(context) = search_input.context.as_ref() else {
            return Err(
                search_input.step_error("induction application requires a pure theorem proof")
            );
        };
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(search_input.step_error("induction hypothesis is not active"));
        };
        if hypothesis != setup.hypothesis {
            return Err(
                search_input.step_error(format!("unknown induction hypothesis `{hypothesis}`"))
            );
        }
        let [argument] = arguments else {
            return Err(search_input.step_error(format!(
                "induction hypothesis `{hypothesis}` expects one argument"
            )));
        };
        // The elided form looks each premise up and proves none: a premise
        // that is not an available fact is a search miss, fixed by stating it
        // first with `have`.
        let mut premises = pure_theorems::induction_application_surface_premises(setup, argument)?;
        let mut cited = Vec::with_capacity(premises.len());
        for mut premise in premises.drain(..) {
            let premise = &mut premise;
            let lowered =
                search_input.lower_cited_surface_proposition(premise, "induction premise")?;
            // The explicit form discharges a premise that evaluates to true,
            // such as `0 <= n - 1u64`, without evidence; cite none for it.
            if matches!(normalize_proposition(&lowered), NormalizedProposition::True) {
                continue;
            }
            // A native premise at the argument's arithmetic, `0 <= n - 1`, is
            // cited by the observations it compares.
            *premise = observed_native_arithmetic(&lowered, premise);
            // A proof states that premise in the spelling the refusal names,
            // whose lowering cites the same observations.
            // As in a `using` list, the same order claim stated from the
            // other side, `n >= 0` for `0 <= n`, is the premise.
            let available = crate::kernel::proof::fact_reasoning::order_claim_forms(&lowered)
                .iter()
                .chain(std::iter::once(&lowered))
                .any(|form| search_input.facts().contains(form))
                || search_input
                    .lower_cited_surface_proposition(premise, "induction premise")
                    .is_ok_and(|cited| search_input.facts().contains(&cited));
            if !available {
                return Err(search_input.step_error(format!(
                    "induction hypothesis `{hypothesis}` found no available fact for premise `{}`{}",
                    describe_click_proposition(premise),
                    crate::surface::proof::theorem_application::requirement_search_miss(
                        &crate::surface::printing::source_click_proposition(premise),
                    ),
                )));
            }
            cited.push(premise.clone());
        }
        search_input
            .driver()
            .apply_step(ProofStep::ApplyInductionUsing {
                hypothesis: hypothesis.to_string(),
                arguments: arguments.to_vec(),
                premises: cited,
            })
    }

    /// Applies one statement step, retaining one newly proved non-load
    /// requirement when the checked step reports it as unavailable.  The
    /// requirement is lowered again at this exact frontier and compared by
    /// the shared alpha-aware identity before any proof operation is accepted.
    /// A failed retry returns the original structured error, allowing the
    /// normal smart caller to preserve its diagnostic and planner behavior.
    pub(in crate::surface::proof) fn try_statement_step_with_retries(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_statement_step_with_retries");
        // Smart execution exposes supported missing source-backed
        // prerequisites before contextual compatibility reasoning can
        // discharge them invisibly. The retained proof retries the same
        // ordinary checked step after publishing its `have`.
        // Use the same checked-step entry point as written `step()` so
        // smart execution retains its fact deltas in the opt-in trace too.
        let initial = search_input.driver().apply_step(step.clone());
        let stepped = crate::kernel::search::ProofSearch::retry_statement_after_refusal(
            search_input,
            step.clone(),
            retried_requirements,
            initial,
        )?;
        crate::kernel::search::ProofSearch::retry_statement_keeping_store_cells(
            search_input,
            step,
            stepped,
        )
    }

    /// A store into an array forgets each cached cell of that array unless a
    /// fact states that the two element indices differ: the store-time check
    /// reads that exact fact and derives nothing. When the statement just run
    /// forgot such a cell, prove the index disequality at the statement's
    /// pre-state by selected-premise arithmetic or the disequality bridge
    /// (`try_index_disequality_closure`), retain it as a `have`, and run the same
    /// statement again, which now keeps the cell. The certificate records the
    /// `have` before the step, so expansion writes it and the expanded proof
    /// searches nothing. A disequality `solve` cannot prove leaves the
    /// statement as it first ran; the later read reports the store.
    pub(in crate::surface::proof) fn retry_statement_keeping_store_cells(
        search_input: &Proof<'a>,
        step: ProofStep,
        stepped: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retry_statement_keeping_store_cells");
        let (Some(before), Some(after)) = (search_input.execution(), stepped.execution()) else {
            return Ok(stepped);
        };
        let candidates = crate::kernel::search::store_separation::cells_forgotten_beside_stores(
            before.core.state.memory(),
            after.core.state.memory(),
            MAX_STORE_SEPARATIONS_PER_STATEMENT,
        );
        if candidates.is_empty() {
            return Ok(stepped);
        }
        let mut proof = search_input.clone();
        let mut proved = 0usize;
        // The spelled disequalities the closure did not prove, kept for the
        // report of a later read of the dropped cell. Recorded on this miss
        // path only, from what the search already constructed.
        let mut misses = Vec::new();
        for candidate in &candidates {
            // The disequality is spelled by construction from its two index
            // words, `((m - 1) as int32) != 0`, and stated for the kernel
            // comparison the store reads; the requirement's round trip
            // checks its lowering. A word with no spelling skips the
            // candidate.
            let Some(surface) = search_input.store_index_disequality_surface(candidate) else {
                continue;
            };
            let requirement = UnresolvedRequirement {
                proposition: candidate.indices_differ.clone(),
                context: None,
                introductions: Default::default(),
                call_site: None,
                assertion_condition: None,
                surface: Some(surface),
            };
            let Some(Some(spelling)) =
                attempt::candidate_outcome(proof.requirement_surface(&requirement, &step))?
            else {
                continue;
            };
            let fact = spelling.surface.clone();
            let Some(have) =
                attempt::candidate_outcome(proof.driver().open_have(spelling.surface))?
            else {
                continue;
            };
            let joined = match have.driver().try_index_disequality_closure()? {
                Some(closed) => attempt::candidate_outcome(closed.join())?,
                None => None,
            };
            let Some(joined) = joined else {
                misses.push((candidate, fact));
                continue;
            };
            proof = joined;
            proved += 1;
        }
        let kept = if proved == 0 {
            stepped
        } else {
            // The statement runs again with proved facts only; it can keep
            // more cells than its first run, never fewer.
            attempt::candidate_outcome(proof.driver().apply_step(step))?.unwrap_or(stepped)
        };
        record_store_separation_misses(search_input, kept, misses)
    }

    /// `solve`'s automatic opening (design/proof-reuse.md R4): a C operation
    /// refused because the resource it reads or writes lies inside a folded
    /// resource is retried once that resource is unfolded, one layer per
    /// refused access. The certificate records each `unfold`, so expansion
    /// writes it out. A refusal the opening does not resolve is reported as
    /// the original refusal.
    pub(in crate::surface::proof) fn retry_statement_after_solve_open(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
        error: ClickError,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retry_statement_after_solve_open");
        let mut proof = search_input.clone();
        let mut refusal = error.clone();
        for _ in 0..MAX_AUTO_OPENINGS_PER_STATEMENT {
            let Some(missing) = refusal.missing_resource() else {
                break;
            };
            let Some(opened) = Self::try_open_for_missing_resource(&proof, missing)? else {
                break;
            };
            proof = opened;
            match proof.driver().apply_step(step.clone()) {
                Ok(stepped) => return Ok(stepped),
                Err(next) if next.missing_resource().is_some() => refusal = next,
                Err(next) => {
                    return crate::kernel::search::ProofSearch::retry_statement_after_refusal(
                        &(proof),
                        step,
                        retried_requirements,
                        Err(next),
                    )
                    .map_err(|_| error);
                }
            }
        }
        Err(error)
    }

    pub(in crate::surface::proof) fn retry_statement_after_refusal(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
        initial: Result<Proof<'a>, ClickError>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retry_statement_after_refusal");
        match initial {
            Ok(proof) => Ok(proof),
            Err(error) if error.missing_resource().is_some() => {
                crate::kernel::search::ProofSearch::retry_statement_after_solve_open(
                    search_input,
                    step,
                    retried_requirements,
                    error,
                )
            }
            Err(error) => {
                let Some(mut requirement) = error.unresolved_requirement().cloned() else {
                    return Err(error);
                };
                let Some(identity) = proposition_identity_key(&requirement.proposition) else {
                    return Err(error);
                };
                if !retried_requirements.insert(identity) {
                    return Err(error);
                }
                let mut proof = search_input.clone();
                let mut error = error;
                loop {
                    let Some(spelling) = proof.requirement_surface(&requirement, &step)? else {
                        return Err(error);
                    };
                    let have = match proof.driver().open_have(spelling.surface) {
                        Ok(have) => have,
                        Err(_) => {
                            check_verification_deadline()?;
                            return Err(error);
                        }
                    };
                    let closed = have.driver().try_solve_closure()?;
                    let Some(closed) = closed else {
                        return Err(error);
                    };
                    // `join` publishes the checked proposition into the exact
                    // enclosing frontier.  Reapply the original step value so a
                    // future StepContract follows precisely the same contract
                    // selection and certificate provenance as the refused step.
                    proof = closed.join()?;
                    match proof.driver().apply_step(step.clone()) {
                        Ok(next) => return Ok(next),
                        Err(next_error) => {
                            let Some(next_requirement) =
                                next_error.unresolved_requirement().cloned()
                            else {
                                return Err(next_error);
                            };
                            let Some(next_identity) =
                                proposition_identity_key(&next_requirement.proposition)
                            else {
                                return Err(next_error);
                            };
                            if !retried_requirements.insert(next_identity) {
                                return Err(next_error);
                            }
                            requirement = next_requirement;
                            error = next_error;
                            // The next loop iteration uses the newly returned
                            // requirement, but still the same exact step.
                            continue;
                        }
                    }
                }
            }
        }
    }

    /// Tries one bare `step()` in the whole proof context. There is no premise
    /// selection: the checked step either advances the frontier or reports why
    /// the statement cannot run here. An undecided C `if` is left to the
    /// structural branch driver.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_statement_step(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_statement_step");
        crate::kernel::search::ProofSearch::try_statement_step_with_apply(search_input, |proof| {
            proof.driver().apply_step(ProofStep::Step)
        })
    }

    pub(in crate::surface::proof) fn try_smart_statement_step(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_smart_statement_step");
        crate::kernel::search::ProofSearch::try_statement_step_with_apply(search_input, |proof| {
            crate::kernel::search::ProofSearch::try_statement_step_with_retries(
                proof,
                step.clone(),
                retried_requirements,
            )
        })
    }

    pub(in crate::surface::proof) fn try_statement_step_with_apply(
        search_input: &Proof<'a>,
        mut apply: impl FnMut(&Proof<'a>) -> Result<Proof<'a>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_statement_step_with_apply");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = search_input.execution() else {
            return Err(search_input.step_error("execution-frontier proof lost its semantic state"));
        };
        // Structural frontiers belong to the branch and loop operations.
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(context),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "smart step selection",
        )?;
        if matches!(
            statement,
            ProgramStatement::If { .. } | ProgramStatement::Switch { .. }
        ) {
            // A C `if` the context decides is one step into that arm; one it
            // cannot decide is a fork for the driver's branch handling. A
            // symbolic switch likewise belongs to the bounded planner, which
            // materializes its case split before applying one switch theorem
            // per path.
            return match apply(search_input) {
                Ok(proof) => Ok(Some(proof)),
                Err(error) => {
                    if source_backed_refusal(&error, execution.core.state.memory())? {
                        Err(error)
                    } else {
                        check_verification_deadline()?;
                        Ok(None)
                    }
                }
            };
        }
        // A caught throwing call is a proof-object split frontier, not a
        // linear step failure. Let the focused execution driver publish the
        // returned/threw siblings so the eventual certificate is explicit.
        if search_input.is_at_call_outcomes_frontier()? {
            return Ok(None);
        }
        // The statement runs in the whole proof context; nothing can supply
        // more than the step already sees, so its failure is the answer,
        // with the step's diagnostic. The exception is a statement whose
        // successors are path cases: a case split on their facts supplies
        // each case's facts, and that split belongs to the planner.
        match apply(search_input) {
            Ok(proof) => Ok(Some(proof)),
            Err(error) if error.is_path_case_split() => {
                check_verification_deadline()?;
                Ok(None)
            }
            Err(error) => Err(error),
        }
    }
}

/// Retains each store-search miss on the statement's successor, so a
/// refusal that later reads the dropped cell can name the statement and
/// the fact that keeps it. Presentation only: the checked state and its
/// certificate are unchanged.
fn record_store_separation_misses<'a>(
    search_input: &Proof<'a>,
    stepped: Proof<'a>,
    misses: Vec<(
        &crate::kernel::search::store_separation::ForgottenStoreCell,
        ClickProposition,
    )>,
) -> Result<Proof<'a>, ClickError> {
    if misses.is_empty() {
        return Ok(stepped);
    }
    let Some(region) = search_input.current_statement_index()? else {
        return Ok(stepped);
    };
    let statement = crate::surface::diagnostics::describe_statement_region(region);
    let cells = match search_input.execution() {
        Some(before) => misses
            .iter()
            .map(|(candidate, _)| {
                crate::surface::diagnostics::describe_source_cell_at_state(
                    &candidate.cell,
                    &before.core.state,
                )
            })
            .collect(),
        None => vec![None; misses.len()],
    };
    let fallback = stepped.clone();
    Ok(stepped
        .edit_execution_presentation(|presentation| {
            for ((candidate, fact), cell_text) in misses.into_iter().zip(cells) {
                if presentation.store_separation_misses.len()
                    >= MAX_RECORDED_STORE_SEPARATION_MISSES
                {
                    break;
                }
                presentation.store_separation_misses.push(
                    crate::surface::proof::proof_object::StoreSeparationMiss {
                        statement: statement.clone(),
                        cell: candidate.cell.clone(),
                        cell_text,
                        store: candidate.store.clone(),
                        fact,
                    },
                );
            }
        })
        .map_or(fallback, |(proof, ())| proof))
}
