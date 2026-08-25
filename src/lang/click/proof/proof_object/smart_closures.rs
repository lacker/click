//! Smart closure search and linear script interpretation.

use super::*;
use fact_index::collect_surface_conjunct_leaves;

impl<'a> Proof<'a> {
    /// A small shared search combinator for structural proposition closure.
    /// Every candidate is accepted only through `apply_step`; `intro` is the
    /// sole nonterminal move and strictly removes one outer goal connective.
    ///
    /// A miss is `Ok(None)` and leaves `self` the unchanged authority. An
    /// error is a tooling failure such as an exceeded deadline; it must abort
    /// the enclosing search rather than read as one more rejection.
    pub(in crate::lang::click::proof) fn try_direct_logical_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let mut budget = attempt::AttemptBudget::unbounded();
        let mut proof = self.clone();
        loop {
            if let Some(closed) = attempt::try_steps(
                &proof,
                &mut budget,
                [
                    SimpleProofStep::Normalize,
                    SimpleProofStep::Assumption,
                    SimpleProofStep::Split,
                    SimpleProofStep::Left,
                    SimpleProofStep::Right,
                    SimpleProofStep::Enumerate,
                ],
            )? {
                return Ok(Some(closed));
            }
            match attempt::candidate_outcome(proof.apply_step(SimpleProofStep::Intro))? {
                Some(introduced) => proof = introduced,
                None => return Ok(None),
            }
        }
    }

    /// Searches the currently migrated `simp` vocabulary against this proof.
    ///
    /// Direct logical closers remain the cheap first choice. For a pure or
    /// point signed-order/equality derivation, the kernel-selected edge path
    /// is translated into a candidate made only of checked theorem
    /// applications, rewrites, and nested `have` scopes. The candidate
    /// advances this same `Proof`; no semantic result is produced before
    /// those simple steps have been accepted.
    pub(in crate::lang::click::proof) fn try_simp_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(proof) = self.try_direct_logical_closure()? {
            return Ok(Some(proof));
        }
        self.try_simp_closure_after_direct(false)
    }

    /// Continues smart closure after direct logical candidates have either
    /// missed or been deliberately rejected as non-replayable. When
    /// `exclude_exact_goal` is true, the atomic derivation query may not cite
    /// the goal's own ambient fact; every selected theorem step is still
    /// checked against this unchanged Proof.
    pub(super) fn try_simp_closure_after_direct(
        &self,
        exclude_exact_goal: bool,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_selected_unchanged_load_forall_goal(surface_goal, &[])
        {
            return Ok(Some(proof));
        }
        let atomic = (|| {
            let (goal, derivation, premise_pairs, point_application_closes_goal) =
                self.selected_simp_derivation(exclude_exact_goal)?;
            self.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                &premise_pairs,
                point_application_closes_goal,
            )
            .or_else(|| self.try_selected_equality_rewrite_chain(&premise_pairs))
            .or_else(|| self.try_selected_predecessor_upper_bound(&goal, &premise_pairs))
            .or_else(|| {
                self.surface_goal().and_then(|surface_goal| {
                    self.try_selected_unchanged_load_forall_goal(surface_goal, &premise_pairs)
                        .or_else(|| {
                            self.try_selected_forall_goal(&goal, surface_goal, &premise_pairs)
                        })
                })
            })
            .or_else(|| self.try_selected_forall_instantiation(&goal, &premise_pairs))
            .or_else(|| self.try_selected_disjunction_cases(&premise_pairs))
        })();
        if let Some(atomic) = atomic {
            return Ok(Some(atomic));
        }
        let anchored_pairs = self
            .selected_simp_derivation(exclude_exact_goal)
            .map(|(_, _, pairs, _)| pairs)
            .unwrap_or_default();
        if let Some(anchored) = self
            .try_outcome_anchored_order_transitivity(&anchored_pairs)
            .or_else(|| self.try_outcome_anchored_increment_order(&anchored_pairs))
        {
            return Ok(Some(anchored));
        }
        if let Some(rewritten) = self.try_indexed_goal_equality_rewrite_closure() {
            return Ok(Some(rewritten));
        }
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_outcome_snapshot_transport_closure(surface_goal)?
        {
            return Ok(Some(proof));
        }
        if let Some(instantiated) = self.try_indexed_forall_instantiation() {
            return Ok(Some(instantiated));
        }
        // The atomic helpers still classify their internal candidate misses
        // as `Option`; surface a deadline that fired inside them here rather
        // than continuing into structural search with it exceeded.
        check_verification_deadline()?;
        let Some(surface_goal) = self.surface_goal().cloned() else {
            return Ok(None);
        };
        self.try_structural_simp_closure(&surface_goal)
    }

    /// Proves a two-edge non-strict outcome bound at the return entry or its
    /// immediate predecessor. Outcome lowering deliberately keeps selected
    /// premises in their source form; anchoring those exact premises at
    /// the execution boundary lets the ordinary theorem checker connect a
    /// returned local to its result without consulting the retired planner.
    pub(super) fn try_outcome_anchored_order_transitivity(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let point = self.focused_outcome_point()?;
        let anchor = point.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
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
                    let anchored = surface_with_source_site(surface, anchor).ok()?;
                    let parts = surface_nonstrict_parts(&anchored)?;
                    Some((anchored, parts))
                })
                .collect::<Vec<_>>();
            for (first_surface, (first, middle)) in &ordered {
                for (second_surface, (second_middle, last)) in &ordered {
                    if middle != second_middle {
                        continue;
                    }
                    let theorem = SimpleProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_ge_transitive".to_string(),
                            arguments: vec![last.clone(), middle.clone(), first.clone()],
                        },
                        premises: vec![second_surface.clone(), first_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
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
    /// ordinary theorem, nested-`have`, and assumption checkers decide whether
    /// either constant-size historical application establishes the current
    /// result-aware goal.
    pub(super) fn try_outcome_anchored_increment_order(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let point = self.focused_outcome_point()?;
        let anchor = point.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        let surface_goal = self.surface_goal()?.clone();
        if surface_nonstrict_parts(&surface_goal).is_none() {
            return None;
        }
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let mut lower_bounds = Vec::new();
            let mut upper_bounds = Vec::new();
            for (_, surface) in premise_pairs {
                let anchored = surface_with_source_site(surface, anchor).ok()?;
                if let Some(parts) = surface_nonstrict_parts(&anchored) {
                    lower_bounds.push((anchored.clone(), parts));
                }
                if let Some(parts) = surface_strict_parts(&anchored) {
                    upper_bounds.push((anchored, parts));
                }
            }
            for (lower_surface, (surface_lower, lower_value)) in &lower_bounds {
                for (upper_surface, (upper_value, surface_upper)) in &upper_bounds {
                    if lower_value != upper_value {
                        continue;
                    }
                    let theorem = SimpleProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_increment_preserves_order".to_string(),
                            arguments: vec![
                                lower_value.clone(),
                                surface_lower.clone(),
                                surface_upper.clone(),
                            ],
                        },
                        premises: vec![lower_surface.clone(), upper_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    let one = ContractExpression::CFragment(CExpression::Value(int32(1)));
                    let theorem_conclusion = ClickProposition::Comparison {
                        left: ContractExpression::Add(
                            Box::new(surface_lower.clone()),
                            Box::new(one.clone()),
                        ),
                        operator: ComparisonOperator::LessEqual,
                        right: ContractExpression::Add(
                            Box::new(lower_value.clone()),
                            Box::new(one),
                        ),
                    };
                    if let Some(closed) = applied
                        .apply_step(SimpleProofStep::TransportUsing {
                            source: theorem_conclusion,
                            target: surface_goal.clone(),
                            premises: Vec::new(),
                        })
                        .ok()
                        .or_else(|| applied.try_direct_logical_closure().ok().flatten())
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Tries the focused outcome goal itself as one explicit fact transport
    /// from a recorded program point. The candidate space is the execution's
    /// program-point index, not the ambient fact set; every accepted source
    /// and target is checked by `TransportUsing` on this immutable Proof.
    pub(super) fn try_outcome_snapshot_transport_closure(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(view) = self.outcome_point_view() else {
            return Ok(None);
        };
        if let Some(source) = old_reflexive_transport_source(surface_goal) {
            match self.search_point_fact_transport(&source, surface_goal, std::iter::empty()) {
                Ok(proof) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        let entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        let selectors =
            std::iter::once(entry).chain(view.program_point_states.keys().rev().cloned());
        let mut tried = BTreeSet::new();
        for point in selectors {
            if !tried.insert(point.clone()) {
                continue;
            }
            let source = ClickProposition::At {
                selector: VisitSelector::ProgramPoint(point),
                proposition: Box::new(surface_goal.clone()),
            };
            match self.search_point_fact_transport(
                &source,
                surface_goal,
                std::iter::once(source.clone()),
            ) {
                Ok(proof) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        Ok(None)
    }

    /// Refines the Proof-owned Surface goal through audited scopes and steps.
    /// The caller cannot supply a second description of the judgment: this
    /// syntax is the view paired with the kernel goal in `PropositionGoal`.
    pub(super) fn try_structural_simp_closure(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        match (surface_goal, goal) {
            (ClickProposition::ForAll { .. }, Proposition::ForAll { .. }) => {
                if let Some(enumerated) = self.try_finite_forall_enumeration(surface_goal)? {
                    return Ok(Some(enumerated));
                }
                match attempt::candidate_outcome(self.apply_step(SimpleProofStep::Intro))? {
                    Some(introduced) => introduced.try_simp_closure(),
                    None => Ok(None),
                }
            }
            (ClickProposition::Implies(surface_antecedent, _), Proposition::Implies(_, _)) => {
                let Some(mut introduced) =
                    attempt::candidate_outcome(self.apply_step(SimpleProofStep::Intro))?
                else {
                    return Ok(None);
                };
                // The introduced antecedent itself is the uniquely selected
                // contradiction candidate. This is a constant-size probe:
                // `Contradiction` checks that exact fact and its indexed
                // opposite, without scanning ambient path facts.
                if let Some(closed) = introduced
                    .try_introduced_antecedent_contradiction(surface_antecedent.as_ref())?
                {
                    return Ok(Some(closed));
                }
                let mut conjuncts = Vec::new();
                if matches!(surface_antecedent.as_ref(), ClickProposition::And(_, _)) {
                    collect_surface_conjunct_leaves(surface_antecedent, &mut conjuncts);
                }
                for conjunct in &conjuncts {
                    let Some(extracted) = attempt::candidate_outcome(
                        introduced.apply_step(SimpleProofStep::Extract(conjunct.clone())),
                    )?
                    else {
                        return Ok(None);
                    };
                    introduced = extracted;
                    if introduced.is_complete() {
                        return Ok(Some(introduced));
                    }
                }
                if !conjuncts.is_empty()
                    && let Some(surface_goal) = introduced.surface_goal()
                    && let Some(source) = old_reflexive_transport_source(surface_goal)
                {
                    match introduced.search_point_fact_transport(
                        &source,
                        surface_goal,
                        conjuncts.iter().cloned(),
                    ) {
                        Ok(transported) if transported.is_complete() => {
                            return Ok(Some(transported));
                        }
                        Ok(_) => {}
                        Err(_) => check_verification_deadline()?,
                    }
                }
                introduced.try_simp_closure()
            }
            (ClickProposition::And(surface_left, surface_right), Proposition::And(_, _)) => {
                let Some(left) =
                    attempt::candidate_outcome(self.begin_have(surface_left.as_ref().clone()))?
                else {
                    return Ok(None);
                };
                let Some(left) = left.try_simp_closure()? else {
                    return Ok(None);
                };
                let Some(proof) = attempt::candidate_outcome(left.join())? else {
                    return Ok(None);
                };
                let Some(right) =
                    attempt::candidate_outcome(proof.begin_have(surface_right.as_ref().clone()))?
                else {
                    return Ok(None);
                };
                let Some(right) = right.try_simp_closure()? else {
                    return Ok(None);
                };
                let Some(joined) = attempt::candidate_outcome(right.join())? else {
                    return Ok(None);
                };
                attempt::candidate_outcome(joined.apply_step(SimpleProofStep::Split))
            }
            // A predicate-call goal unfolds to its body, which the
            // structural arms and logical closers then work over. Repeat
            // unfolds are refused so recursive predicate bodies cannot loop
            // the search.
            (ClickProposition::PredicateCall { name, .. }, _)
                if !self.focused_goal_unfolds().contains(name) =>
            {
                match attempt::candidate_outcome(
                    self.apply_step(SimpleProofStep::UnfoldPredicate(name.clone())),
                )? {
                    Some(unfolded) => unfolded.try_simp_closure(),
                    None => Ok(None),
                }
            }
            (ClickProposition::Or(surface_left, surface_right), Proposition::Or(_, _)) => {
                for (surface, closer) in [
                    (surface_left.as_ref(), SimpleProofStep::Left),
                    (surface_right.as_ref(), SimpleProofStep::Right),
                ] {
                    let selected = (|| {
                        let Some(scope) =
                            attempt::candidate_outcome(self.begin_have(surface.clone()))?
                        else {
                            return Ok(None);
                        };
                        let Some(scope) = scope.try_simp_closure()? else {
                            return Ok(None);
                        };
                        let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                            return Ok(None);
                        };
                        attempt::candidate_outcome(joined.apply_step(closer.clone()))
                    })();
                    if let Some(selected) = selected? {
                        return Ok(Some(selected));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Proves the kernel's deterministic constant-bounded universal table as
    /// checked nested `have` scopes, then closes with the ordinary
    /// `Enumerate` rule. Candidate discovery is output-sensitive in the
    /// explicit instance table; each non-vacuous instance recursively uses
    /// the same retained Proof search and no ambient universal scan.
    pub(super) fn try_finite_forall_enumeration(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
            return Ok(None);
        };
        let mut binder_names = Vec::new();
        let mut surface_body = surface_goal;
        while let ClickProposition::ForAll { name, body, .. } = surface_body {
            binder_names.push(name.clone());
            surface_body = body;
        }
        if binder_names.is_empty() {
            return Ok(None);
        }

        let mut proof = self.clone();
        for (values, instance) in instances {
            check_verification_deadline()?;
            if values.len() != binder_names.len() {
                return Ok(None);
            }
            if matches!(normalize_proposition(&instance), SimpProposition::True) {
                continue;
            }
            let Some(value_expressions) = values
                .iter()
                .map(|value| {
                    u32::try_from(*value)
                        .ok()
                        .map(|bits| ContractExpression::CFragment(CExpression::Value(int32(bits))))
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
            let Some(scope) = attempt::candidate_outcome(proof.begin_have(surface_instance))?
            else {
                return Ok(None);
            };
            let Some(scope) = scope.try_simp_closure()? else {
                return Ok(None);
            };
            let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(proof.apply_step(SimpleProofStep::Enumerate))
    }

    /// Closes from the just-introduced antecedent and one exact indexed
    /// opposite. The antecedent fixes the kernel pair; Surface lookup visits
    /// only forms recorded for those two facts, never the ambient set.
    pub(super) fn try_introduced_antecedent_contradiction(
        &self,
        surface_antecedent: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(introduced) = self.checked_facts().first() else {
            return Ok(None);
        };
        let opposite = match introduced {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => body.as_ref().clone(),
            proposition => Proposition::Not(Box::new(proposition.clone())),
        };
        if !self.facts().contains(&opposite) {
            return Ok(None);
        }
        if let Some(closed) = attempt::candidate_outcome(
            self.apply_step(SimpleProofStep::Contradiction(surface_antecedent.clone())),
        )? {
            return Ok(Some(closed));
        }
        let surfaces = match self.context.as_ref() {
            ProofContext::Pure(context) => context
                .theorem_context
                .surface_requirements
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::Point(context) => context
                .surface_propositions
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::Execution(_) => self
                .outcome_point_view()
                .into_iter()
                .flat_map(|view| view.surface_propositions.surfaces(&opposite))
                .cloned()
                .collect::<Vec<_>>(),
        };
        for surface in surfaces {
            if let Some(closed) = attempt::candidate_outcome(
                self.apply_step(SimpleProofStep::Contradiction(surface)),
            )? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Retains the kernel decision and every exact replayable surface form
    /// among its context premises. A typed evidence translator selects and
    /// requires its own exact premises from this subset; unrelated transitive
    /// search context need not be Surface-synthesizable. This is a read-only smart
    /// query: only the later `apply_step` calls may advance the proof.
    pub(super) fn selected_simp_derivation(
        &self,
        exclude_exact_goal: bool,
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
        bool,
    )> {
        let (surface_facts, theorem_application_closes_goal, premise_anchor) =
            match self.context.as_ref() {
                ProofContext::Pure(context) => {
                    (&context.theorem_context.surface_requirements, true, None)
                }
                ProofContext::Point(context) => (
                    context.surface_propositions,
                    true,
                    context.premise_anchor.as_ref(),
                ),
                // A judgment stated at a function outcome supplies the
                // outcome's recorded lowerings and statement-entry anchor.
                ProofContext::Execution(_) => {
                    let Some(point) = self.focused_outcome_point() else {
                        return None;
                    };
                    (
                        &point.surface_propositions,
                        // Entry-anchored premises can add a replay-equivalent
                        // outcome fact without discharging the exact goal
                        // form. Keep the ordinary trailing assumption so
                        // the checked successor decides whether it is needed.
                        false,
                        point.premise_anchor.as_ref(),
                    )
                }
            };
        let goal = self.goal()?.clone();
        let derivation = if exclude_exact_goal {
            self.facts()
                .assumptions()
                .derive_simp_proposition_without_exact_goal(&goal)?
        } else {
            let plan = plan_simp_certificate(&goal, self.facts().assumptions())?;
            let SimpEvidence::Derivation(derivation) = plan else {
                return None;
            };
            derivation
        };
        let context_premises = derivation.context_premises();
        let resolve_premise = |premise: &Proposition, anchor: Option<&ProgramPointRef>| {
            if let Some(surface) = self.replayable_surface_fact(surface_facts, anchor, premise) {
                return Some((premise.clone(), surface));
            }
            condition_polarity_forms(premise)
                .into_iter()
                .find_map(|form| {
                    let surface = self.replayable_surface_fact(surface_facts, anchor, &form);
                    surface.map(|surface| (form, surface))
                })
        };
        let mut premise_pairs = context_premises
            .iter()
            .filter_map(|premise| resolve_premise(premise, premise_anchor))
            .collect::<Vec<_>>();
        // A structured branch continuation can clear `last_step_entry`, or a
        // later common statement can move it past the point where the
        // selected premises were established. If the initially resolved
        // subset already carries one common explicit `at(...)` form,
        // retry this same finite premise list at that point. No ambient fact
        // or program-point scan participates.
        let anchors = premise_pairs
            .iter()
            .filter_map(|(_, surface)| surface_source_site(surface))
            .collect::<BTreeSet<_>>();
        if anchors.len() == 1 {
            let inferred = anchors.first().expect("one inferred anchor");
            let anchored_pairs = context_premises
                .iter()
                .filter_map(|premise| resolve_premise(premise, Some(inferred)))
                .collect::<Vec<_>>();
            if anchored_pairs.len() >= premise_pairs.len() {
                premise_pairs = anchored_pairs;
            }
        }
        Some((
            goal,
            derivation,
            premise_pairs,
            theorem_application_closes_goal,
        ))
    }

    /// Resolves one exact retained fact to a surface form that will lower
    /// back to that same kernel proposition when the selected simple step is
    /// replayed. Historical locals are anchored before ordinary forms are
    /// considered, so a same-written newer snapshot cannot be substituted.
    pub(super) fn replayable_surface_fact(
        &self,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        let matches_kernel = |candidate: &ClickProposition| {
            if self.focused_outcome_point().is_some()
                && surface_facts
                    .available_kernel_matching(candidate, |fact| self.facts().contains(fact))
                    .is_some_and(|lowered| {
                        lowered == kernel || condition_polarity_equivalent(lowered, kernel)
                    })
            {
                return Some(());
            }
            let lowered = self
                .lower_surface_proposition_direct(candidate, "typed simp premise form")
                .ok()?;
            (lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)).then_some(())
        };
        if let Some(surface) = surface_facts.surfaces(kernel).find(|surface| {
            (proposition_contains_at_expression(surface)
                || proposition_contains_old_expression(surface))
                && matches_kernel(surface).is_some()
        }) {
            return Some(surface.clone());
        }
        // Function requirements retain their original unanchored Surface
        // form while their kernel fact is entry-relative. Probe that one
        // canonical source site before the moving statement-entry anchor;
        // the direct lowering check below rejects non-entry facts, and the
        // lookup visits only forms indexed under this selected premise.
        let function_entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        if let Some(point) = self.focused_outcome_point()
            && let Some(surface) = point.requirement_surfaces.get(kernel)
        {
            let anchored = ClickProposition::At {
                selector: VisitSelector::ProgramPoint(function_entry.clone()),
                proposition: Box::new(surface.clone()),
            };
            if matches_kernel(&anchored).is_some() {
                return Some(anchored);
            }
            if let Ok(anchored) = surface_with_source_site(surface, &function_entry)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if self.focused_outcome_point().is_some() {
            if let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_with_source_site(surface, &function_entry).ok()?;
                matches_kernel(&anchored).map(|()| anchored)
            }) {
                return Some(anchored);
            }
            if let Some(view) = self.outcome_point_view()
                && let Some(surface) = synthesize_surface_proposition(
                    kernel,
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                )
                && let Ok(anchored) = surface_with_source_site(&surface, &function_entry)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(anchor) = premise_anchor
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_with_source_site(surface, anchor).ok()?;
                matches_kernel(&anchored).map(|()| anchored)
            })
        {
            return Some(anchored);
        }
        // A checked branch interface can export a kernel fact whose arm-local
        // Surface recording does not survive as a common map entry. The
        // statement-entry anchor still names the exact retained state. Rebuild
        // only this selected fact at that indexed state, anchor it, and require
        // the ordinary direct lowering to recover the same kernel premise.
        if let Some(anchor) = premise_anchor {
            let synthesis_context = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::Point(context) => Some((
                    context.parameters,
                    context.arguments,
                    context.program_point_states,
                )),
                ProofContext::Execution(_) => self
                    .outcome_point_view()
                    .map(|view| (view.parameters, view.arguments, view.program_point_states)),
            };
            if let Some((parameters, arguments, program_points)) = synthesis_context
                && let Some(state) = program_points.get(anchor)
                && let Some(surface) =
                    synthesize_surface_proposition(kernel, parameters, arguments, state)
                && let Ok(anchored) = surface_with_source_site(&surface, anchor)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(surface) = surface_facts
            .surfaces(kernel)
            .find(|surface| matches_kernel(surface).is_some())
            .cloned()
        {
            return Some(surface);
        }
        // Quantified execution facts may be retained in the canonical memory
        // form used by the kernel while their recorded Surface form
        // lowers to a replay-equivalent snapshot term. Probe only the
        // persistent alpha/canonical-form bucket for this selected premise;
        // `InstantiateUsing` validates the same equivalence on replay.
        if matches!(kernel, Proposition::ForAll { .. }) {
            for candidate in self.facts().matching_quantified_replay_facts(kernel) {
                for surface in surface_facts.surfaces(&candidate) {
                    let lowered = self
                        .lower_surface_proposition_direct(
                            surface,
                            "typed quantified simp premise form",
                        )
                        .ok()?;
                    if quantified_replay_equivalent_available_fact(
                        kernel,
                        std::slice::from_ref(&lowered),
                    )
                    .is_some()
                    {
                        return Some(surface.clone());
                    }
                }
            }
        }
        // Branch-condition facts are checked execution outputs, but their
        // arm-local Surface map entry need not survive at the shared outcome.
        // Reconstruct only this derivation-selected premise at the current
        // semantic point and accept it only when ordinary lowering recovers
        // the exact kernel fact. This is constant work per typed proof edge,
        // not an ambient form search.
        let synthesis_context = match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::Point(context) => Some((
                context.parameters,
                context.arguments,
                context.state,
                context.program_point_states,
            )),
            ProofContext::Execution(_) => self.outcome_point_view().map(|view| {
                (
                    view.parameters,
                    view.arguments,
                    view.state,
                    view.program_point_states,
                )
            }),
        };
        let (parameters, arguments, state, program_points) = synthesis_context?;
        if let Some(surface) = synthesize_surface_proposition(kernel, parameters, arguments, state)
            && matches_kernel(&surface).is_some()
        {
            return Some(surface);
        }
        // A certified statement fact may relate two execution snapshots (a
        // callee postcondition names a cell after the call and its value
        // before it), so no single point denotes both operands. Spell each
        // operand at the nearest recorded statement entry that denotes it,
        // walking back from the selected premise anchor; the candidate is
        // accepted only when ordinary lowering recovers this exact fact.
        let anchor = premise_anchor?;
        let CodeRegionRef::Statement(anchor_index) = &anchor.region else {
            return None;
        };
        let points = (0..=*anchor_index)
            .rev()
            .filter_map(|index| {
                let point = ProgramPointRef {
                    region: CodeRegionRef::Statement(index),
                    kind: ProgramPointKind::Entry,
                };
                let state = program_points.get(&point)?;
                Some((point, state))
            })
            .collect::<Vec<_>>();
        let surface =
            synthesize_surface_equality_across_points(kernel, parameters, arguments, &points)?;
        matches_kernel(&surface).map(|()| surface)
    }

    /// Tries equalities attached to terms occurring in the current goal.
    /// This complements the kernel derivation path for arithmetic goals whose
    /// normal form is exposed only after selected historical equalities are
    /// rewritten. Candidate lookup is goal-local and persistently indexed.
    /// Atomic goals may retain a same-width renaming, but each selected
    /// equality is used at most once; structural goals keep only a closing
    /// rewrite so their recursive connective proof remains visible.
    pub(super) fn try_indexed_goal_equality_rewrite_closure(&self) -> Option<Self> {
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::Point(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => {
                let point = self.focused_outcome_point()?;
                (&point.surface_propositions, point.premise_anchor.as_ref())
            }
        };
        let mut proof = self.clone();
        let mut used = BTreeSet::new();
        loop {
            let goal = proof.goal()?.clone();
            let allows_chain = matches!(goal, Proposition::ConditionIs(_, _));
            let mut refinement = None;
            for equality in proof.facts().bitvector_equalities_mentioning(&goal) {
                if used.contains(&equality) {
                    continue;
                }
                let Some(surface) =
                    proof.replayable_surface_fact(surface_facts, premise_anchor, &equality)
                else {
                    continue;
                };
                // Rewriting is directional even when its admitted premise is
                // a symmetric equality. Keep the selected fact fixed, but
                // try both Surface orientations so the side occurring in the
                // focused goal can be replaced.
                let reverse = reverse_surface_equality(&surface);
                for oriented in std::iter::once(surface).chain(reverse) {
                    let Ok(rewritten) = proof.apply_step(SimpleProofStep::Rewrite(oriented)) else {
                        continue;
                    };
                    if let Some(closed) = rewritten
                        .try_direct_logical_closure()
                        .ok()
                        .flatten()
                        .or_else(|| rewritten.try_typed_atomic_simp_closure())
                    {
                        return Some(closed);
                    }
                    if allows_chain && refinement.is_none() && rewritten.goal() != Some(&goal) {
                        refinement = Some((equality.clone(), rewritten));
                    }
                }
            }
            let (equality, rewritten) = refinement?;
            used.insert(equality);
            proof = rewritten;
        }
    }

    /// Rewrites with only the explicitly selected equality premises, at most
    /// once each. Every candidate rewrite is checked transactionally, and
    /// the finite user-written premise list is the entire search space.
    pub(super) fn try_selected_equality_rewrite_chain(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let mut proof = self.clone();
        let mut remaining = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                matches!(
                    kernel,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
                        | Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true)
                )
            })
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        while !remaining.is_empty() {
            let mut selected = None;
            for (index, surface) in remaining.iter().enumerate() {
                for oriented in
                    std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
                {
                    if let Ok(rewritten) = proof.apply_step(SimpleProofStep::Rewrite(oriented)) {
                        selected = Some((index, rewritten));
                        break;
                    }
                }
                if selected.is_some() {
                    break;
                }
            }
            let (index, rewritten) = selected?;
            remaining.remove(index);
            if let Some(closed) = rewritten
                .try_direct_logical_closure()
                .ok()
                .flatten()
                .or_else(|| rewritten.try_typed_atomic_simp_closure())
            {
                return Some(closed);
            }
            proof = rewritten;
        }
        None
    }

    /// Searches the structured predecessor proof already expressible through
    /// the checked API. The goal itself fixes the value and upper bound, so
    /// this visits only selected equalities connected to that value and one
    /// exact upper-bound premise; it never tries every partially synthesizable
    /// context fact as a candidate step.
    pub(super) fn try_selected_predecessor_upper_bound(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if !matches!(self.context.as_ref(), ProofContext::Point(_)) {
            return None;
        }
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(predecessor, goal_upper),
            true,
        ) = goal
        else {
            return None;
        };
        let Bitvector32Term::Subtract(value, amount) = predecessor.as_ref() else {
            return None;
        };
        if amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        let upper_kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(value.clone(), goal_upper.clone()),
            true,
        );
        let (_, upper_surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == &upper_kernel)?;
        let (surface_value, surface_upper) = surface_nonstrict_parts(upper_surface)?;
        let nonnegative_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: surface_value.clone(),
        };
        for (kernel, surface) in premise_pairs {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                kernel
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
            let Bitvector32Term::Constant(bits) = selected_constant else {
                continue;
            };
            if (*bits as i32) < 0 {
                continue;
            }
            let mut orientations = vec![surface.clone()];
            if let Some(reverse) = reverse_surface_equality(surface)
                && reverse != *surface
            {
                orientations.push(reverse);
            }
            for equality in orientations {
                let scope = self.begin_have(nonnegative_surface.clone()).ok()?;
                let Ok(scope) = scope.apply_step(SimpleProofStep::Rewrite(equality)) else {
                    continue;
                };
                let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                    continue;
                };
                let joined = scope.join().ok()?;
                let theorem = SimpleProofStep::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_nonnegative_predecessor_upper_bound".to_string(),
                        arguments: vec![surface_value.clone(), surface_upper.clone()],
                    },
                    premises: vec![nonnegative_surface.clone(), upper_surface.clone()],
                };
                let Ok(applied) = joined.apply_step(theorem) else {
                    continue;
                };
                if applied.is_complete() {
                    return Some(applied);
                }
                if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                    return Some(closed);
                }
            }
        }
        None
    }

    /// Eliminates one disjunction selected by the kernel derivation and
    /// proves both arms on their branch-local `Proof`s. The disjunction is
    /// never reopened once either disjunct is already available, which makes
    /// recursive branch search descend through distinct case assumptions.
    pub(super) fn try_selected_disjunction_cases(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        for (kernel, surface) in premise_pairs {
            let Proposition::Or(left, right) = kernel else {
                continue;
            };
            if self.facts().contains(left) || self.facts().contains(right) {
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
            let Ok((split_proof, split, ids)) = self.split_focused_cases(surface.clone()) else {
                continue;
            };
            let marker = split_proof.checkpoint();
            let branch_surfaces = [&surface_left, &surface_right];
            let mut proof = split_proof;
            let mut complete = true;
            for (id, assumed_surface) in ids.into_iter().zip(branch_surfaces) {
                let Ok(focused) = proof.focus(id) else {
                    complete = false;
                    break;
                };
                let selected = focused.try_simp_closure().ok().flatten().or_else(|| {
                    let rewritten = focused
                        .apply_step(SimpleProofStep::Rewrite(assumed_surface.clone()))
                        .ok()?;
                    rewritten
                        .try_direct_logical_closure()
                        .ok()
                        .flatten()
                        .or_else(|| rewritten.try_typed_atomic_simp_closure())
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

    /// Applies a planner's flat explicit candidate directly to persistent
    /// `Proof` descendants. Planning may select surface operations, but only
    /// their ordinary checked implementations can advance the proof.
    ///
    /// Generated candidates historically retain a final `assumption()` even
    /// when the preceding operation already discharged the goal. Ignore only
    /// that final no-op; any other operation after closure rejects the
    /// candidate. No certificate is materialized or interpreted here.
    pub(super) fn try_planned_explicit_steps(&self, tactics: &[ProofTactic]) -> Option<Self> {
        if tactics.is_empty() {
            return None;
        }
        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if index + 1 == tactics.len() && matches!(tactic, ProofTactic::Assumption) {
                    continue;
                }
                return None;
            }
            let step = explicit_linear_step(tactic)?;
            proof = proof.apply_step(step).ok()?;
        }
        proof.is_complete().then_some(proof)
    }

    /// Specializes one replayable universal premise selected by the atomic
    /// decision at the current goal. Planning only chooses the explicit
    /// quantified fact, argument, and guards; each selected operation advances
    /// this `Proof` directly.
    pub(super) fn try_selected_forall_instantiation(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_instantiation(goal, premise_pairs)?;
        self.try_planned_explicit_steps(&tactics)
    }

    /// Tries only universal facts introduced by checked predicate unfolds when
    /// the atomic decision cannot name an instantiated premise. Candidate
    /// discovery is read-only; a specialization is retained only after the
    /// ordinary `InstantiateUsing` operation advances and closes this Proof.
    pub(super) fn try_indexed_forall_instantiation(&self) -> Option<Self> {
        let goal = self.goal()?;
        let outcome_view = matches!(self.context.as_ref(), ProofContext::Execution(_))
            .then(|| self.outcome_point_view())
            .flatten();
        let bound_variable_names = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => goal
                .surface_bindings
                .iter()
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Variable(variable),
                    ))) => Some((*variable, name.clone())),
                    _ => None,
                })
                .collect::<BTreeMap<_, _>>(),
            _ => BTreeMap::new(),
        };
        let surface_form = |fact: &Proposition| {
            let recorded = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(fact)
                    .next()
                    .cloned(),
                ProofContext::Point(context) => {
                    context.surface_propositions.surfaces(fact).next().cloned()
                }
                ProofContext::Execution(_) => outcome_view
                    .as_ref()?
                    .surface_propositions
                    .surfaces(fact)
                    .next()
                    .cloned(),
            };
            let synthesized = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::Point(context) => {
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        context.parameters,
                        context.arguments,
                        context.state,
                        &bound_variable_names,
                    )
                }
                ProofContext::Execution(_) => {
                    let view = outcome_view.as_ref()?;
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        view.parameters,
                        view.arguments,
                        view.state,
                        &bound_variable_names,
                    )
                }
            };
            recorded.or(synthesized)
        };
        for quantified in self.facts().predicate_unfolded_universal_facts.iter() {
            // Reject shape-incompatible universals before Surface lookup or
            // synthesis. Candidate extraction is structural and bounded by
            // this one indexed fact and the focused goal; the expensive
            // form work is reserved for a specialization that can
            // actually mention the goal's concrete argument.
            let candidate_values =
                crate::kernel::forall_guided_instantiation_candidate_values(quantified, goal);
            let Proposition::ForAll { var, body, .. } = quantified else {
                unreachable!("the predicate-unfolded universal index contains only universals")
            };
            if candidate_values.is_empty() {
                continue;
            }
            let recorded_surfaces = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Point(context) => context
                    .surface_propositions
                    .surfaces(quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => outcome_view?
                    .surface_propositions
                    .surfaces(quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::Point(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let mut surfaces = Vec::new();
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
            let synthesized = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::Point(context) => synthesize_surface_proposition(
                    quantified,
                    context.parameters,
                    context.arguments,
                    context.state,
                ),
                ProofContext::Execution(_) => {
                    let view = outcome_view?;
                    synthesize_surface_proposition(
                        quantified,
                        view.parameters,
                        view.arguments,
                        view.state,
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
                let click_function_environment = match self.context.as_ref() {
                    ProofContext::Pure(context) => context.click_function_environment,
                    ProofContext::Point(context) => context.click_function_environment,
                    ProofContext::Execution(context) => context.click_function_environment,
                };
                for name in self.focused_goal_unfolds().iter() {
                    for opaque in self.facts().mentioning_predicate(name) {
                        let opaque_surfaces = match self.context.as_ref() {
                            ProofContext::Pure(context) => context
                                .theorem_context
                                .surface_requirements
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::Point(context) => context
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::Execution(_) => outcome_view?
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
                                predicate_environment,
                                click_function_environment,
                                std::slice::from_ref(name),
                                opaque,
                                self.facts().assumptions(),
                            )
                            .is_ok_and(|kernel| kernel == *quantified)
                                && !surfaces.contains(&body_surface)
                            {
                                surfaces.push(body_surface);
                            }
                        }
                    }
                }
            }
            for surface in surfaces {
                for value in candidate_values.iter().cloned() {
                    let argument = match &value {
                        Bitvector32Term::Constant(bits) => Some(ContractExpression::CFragment(
                            CExpression::Value(CValue::Int32(Bitvector32Term::Constant(*bits))),
                        )),
                        Bitvector32Term::Variable(variable) => {
                            let Some(Goal::Proposition(goal)) = self.focused_goal() else {
                                continue;
                            };
                            goal.surface_bindings.iter().find_map(|(name, binding)| {
                                matches!(
                                    binding,
                                    ContractExpression::CFragment(CExpression::Value(
                                        CValue::Int32(Bitvector32Term::Variable(bound))
                                    )) if bound == variable
                                )
                                .then(|| {
                                    ContractExpression::CFragment(CExpression::Variable(
                                        name.clone(),
                                    ))
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
                            if matches!(normalize_proposition(conjunct), SimpProposition::True) {
                                continue;
                            }
                            let exact = std::iter::once(conjunct.clone())
                                .chain(condition_polarity_forms(conjunct))
                                .find(|candidate| self.facts().contains(candidate));
                            let selected = exact.map(|fact| vec![fact]).or_else(|| {
                                self.facts()
                                    .assumptions()
                                    .derive_simp_atomic_proposition(conjunct)
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
                        match self.apply_step(SimpleProofStep::InstantiateUsing {
                            quantified: surface.clone(),
                            argument: argument.clone(),
                            premises: guard_facts
                                .iter()
                                .map(|(_, surface)| surface.clone())
                                .collect(),
                        }) {
                            Ok(proof) => proof,
                            Err(_) => continue,
                        };
                    let conclusion = current.clone();
                    if &conclusion == goal || conclusion.clone() == goal.clone() {
                        if let Ok(closed) =
                            instantiated_proof.apply_step(SimpleProofStep::Assumption)
                        {
                            return Some(closed);
                        }
                        continue;
                    }

                    let transport_assumptions = self
                        .facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone());
                    let Some(transport_derivation) =
                        transport_assumptions.derive_simp_atomic_proposition(goal)
                    else {
                        continue;
                    };
                    let mut transport_surfaces = Vec::new();
                    let mut transport_written = true;
                    for premise in transport_derivation.context_premises() {
                        if premise == conclusion {
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
                    let target = self.surface_goal()?.clone();
                    match instantiated_proof.search_fact_transport_from_candidates(
                        &source,
                        &target,
                        transport_surfaces,
                        "indexed universal conclusion transport",
                    ) {
                        Ok(transported) if transported.is_complete() => return Some(transported),
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
    pub(super) fn try_selected_forall_goal(
        &self,
        goal: &Proposition,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_goal_from_premises(goal, surface_goal, premise_pairs)?;
        self.try_planned_explicit_steps(&tactics)
    }

    /// Retains the point-wise unchanged-load certificate for a guarded
    /// universal outcome. The kernel derivation has already selected the
    /// finite context premises relevant to this goal; after introducing the
    /// binder and guard, transport searches only those forms plus the
    /// freshly extracted guard leaves.
    pub(super) fn try_selected_unchanged_load_forall_goal(
        &self,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if self.focused_outcome_point().is_none() {
            return None;
        }
        let mut cursor = surface_goal;
        let mut proof = self.clone();
        let mut introduced_forall = false;
        while let ClickProposition::ForAll { body, .. } = cursor {
            proof = proof.apply_step(SimpleProofStep::Intro).ok()?;
            cursor = body;
            introduced_forall = true;
        }
        if !introduced_forall {
            return None;
        }
        let ClickProposition::Implies(antecedent, _) = cursor else {
            return None;
        };
        proof = proof.apply_step(SimpleProofStep::Intro).ok()?;
        let mut guard_surfaces = Vec::new();
        collect_surface_conjunct_leaves(antecedent, &mut guard_surfaces);
        for guard in &guard_surfaces {
            proof = proof
                .apply_step(SimpleProofStep::Extract(guard.clone()))
                .ok()?;
        }
        let target = proof.surface_goal()?.clone();
        let source = old_reflexive_transport_source(&target)?;
        let source_pairs = proof
            .lower_surface_proposition(&source, "unchanged-load transport source")
            .ok()
            .and_then(|kernel| {
                proof
                    .facts()
                    .assumptions()
                    .derive_atomic_proposition(&kernel)
            })
            .map(|derivation| {
                let point = proof.focused_outcome_point()?;
                let pairs = derivation
                    .context_premises()
                    .into_iter()
                    .filter_map(|premise| {
                        proof
                            .replayable_surface_fact(
                                &point.surface_propositions,
                                point.premise_anchor.as_ref(),
                                &premise,
                            )
                            .map(|surface| (premise, surface))
                    })
                    .collect::<Vec<_>>();
                Some(pairs)
            })
            .flatten()
            .unwrap_or_default();
        let point = proof.focused_outcome_point()?;
        let anchor = point.premise_anchor.as_ref()?;
        let view = proof.outcome_point_view()?;
        let anchor_state = view.program_point_states.get(anchor)?;
        let mut anchored_candidates = Vec::new();
        for (kernel, _) in premise_pairs.iter().chain(&source_pairs) {
            let Some(surface) = synthesize_surface_proposition(
                kernel,
                view.parameters,
                view.arguments,
                anchor_state,
            ) else {
                continue;
            };
            let Ok(surface) = surface_with_source_site(&surface, anchor) else {
                continue;
            };
            let Some((left, right)) = surface_nonstrict_parts(&surface) else {
                continue;
            };
            let left_is_atomic_variable = match &left {
                ContractExpression::CFragment(CExpression::Variable(_)) => true,
                ContractExpression::At { expression, .. } => matches!(
                    expression.as_ref(),
                    ContractExpression::CFragment(CExpression::Variable(_))
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
        let transported = match proof.search_point_fact_transport(&source, &target, candidates) {
            Ok(transported) => transported,
            Err(error) => {
                let _ = error;
                return None;
            }
        };
        if transported.is_complete() {
            return Some(transported);
        }
        transported.try_direct_logical_closure().ok().flatten()
    }

    pub(super) fn try_typed_atomic_simp_closure(&self) -> Option<Self> {
        let (goal, derivation, premise_pairs, point_application_closes_goal) =
            self.selected_simp_derivation(false)?;
        self.check_typed_atomic_simp_candidate(
            &goal,
            &derivation,
            &premise_pairs,
            point_application_closes_goal,
        )
    }

    /// Searches from exactly the Surface premises named by `simp() using`.
    /// This query cannot add facts or close the goal: it returns only the
    /// descendant obtained by checking the typed atomic decision through the
    /// ordinary Proof transitions.
    pub(in crate::lang::click::proof) fn try_restricted_simp_closure(
        &self,
        surfaces: &[ClickProposition],
    ) -> Option<Self> {
        // A named restricted premise may be a leaf of one exact available
        // conjunction (commonly after `unfold(predicate)`). Materialize that
        // leaf through the ordinary checked `extract` transition before
        // asking the restricted planner to use it. The returned descendant
        // therefore owns both the semantic fact and the Surface provenance;
        // expansion does not need to reconstruct and replay a certificate to
        // justify the premise later.
        let mut proof = self.clone();
        for surface in surfaces {
            let kernel = proof
                .lower_surface_proposition(surface, "restricted simp premise")
                .ok()?;
            if !proof.facts().contains_top_level(&kernel)
                && !normalizes_context_free(&kernel)
                && proof.facts().contains_proper_conjunct(&kernel)
            {
                proof = proof
                    .apply_step(SimpleProofStep::Extract(surface.clone()))
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
                    .lower_surface_proposition(surface, "restricted simp premise")
                    .ok()?;
                // A listed premise that lowers to a context-free truth needs
                // no ambient fact authority. Retaining it lets the restricted
                // derivation erase reflexive field equalities after the
                // outcome state has evaluated their loads.
                (proof.facts().contains_top_level(&kernel) || normalizes_context_free(&kernel))
                    .then_some((kernel, surface.clone()))
            })
            .collect::<Option<Vec<_>>>()?;
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let plan = plan_simp_certificate(goal, &assumptions_from_propositions(&restricted))?;
        let SimpEvidence::Derivation(derivation) = &plan else {
            return None;
        };
        let theorem_application_closes_goal =
            !matches!(self.context.as_ref(), ProofContext::Execution(_));
        proof
            .check_typed_atomic_simp_candidate(
                goal,
                derivation,
                &premise_pairs,
                theorem_application_closes_goal,
            )
            .or_else(|| proof.try_selected_equality_rewrite_chain(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_order_transitivity(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_increment_order(&premise_pairs))
    }

    pub(super) fn check_typed_atomic_simp_candidate(
        &self,
        goal: &Proposition,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, ClickProposition)],
        point_application_closes_goal: bool,
    ) -> Option<Self> {
        let tactics = recorded_signed_order_pairs(derivation, &premise_pairs)
            .and_then(|ordered| {
                plan_recorded_signed_order_path_for_context(
                    goal,
                    &ordered,
                    point_application_closes_goal,
                )
            })
            .or_else(|| plan_recorded_bitvector_equality_path(goal, derivation, &premise_pairs))
            .or_else(|| {
                let recorded =
                    recorded_bitvector_equality_rewrite_path_pairs(derivation, &premise_pairs)?;
                plan_recorded_bitvector_equality_rewrite_paths(goal, derivation, &recorded)
            })
            .or_else(|| {
                plan_explicit_loadability_transport(goal, self.surface_goal()?, premise_pairs)
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_upper_bound_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_upper_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_constant_upper_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_constant_upper_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_strictly_increases_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_strictly_increases_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_one_plus_strictly_increases_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_one_plus_strictly_increases_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_below_max_is_defined_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_below_max_is_defined_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_one_plus_below_max_is_defined_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_one_plus_below_max_is_defined_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_nonnegative_add_within_max_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_nonnegative_add_within_max_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_nonnegative_subtract_within_value_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_nonnegative_subtract_within_value_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_lower_bound_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_lower_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_greater_equal_lower_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_greater_equal_lower_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_strict_greater_lower_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_strict_greater_lower_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_strict_greater_from_strict_lower_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_strict_greater_from_strict_lower_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_preserves_order_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_preserves_order_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_positive_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_positive_predecessor_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_positive_predecessor_strictly_decreases_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_positive_predecessor_strictly_decreases_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_nonnegative_predecessor_upper_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_nonnegative_predecessor_upper_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_equal_one_predecessor_is_zero_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_equal_one_predecessor_is_zero(goal, derivation, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_int32_equal_one_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
                        derivation,
                        &premise_pairs,
                    )
                })?;
                plan_recorded_int32_equal_one_predecessor_for_context(
                    goal,
                    derivation,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_one_le_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_one_le_predecessor_strictly_decreases_pairs(
                        derivation,
                        &premise_pairs,
                    )
                })?;
                plan_recorded_int32_one_le_predecessor_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_le_and_not_lt_implies_equality_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_le_and_not_lt_implies_equality_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_ge_and_not_gt_implies_equality_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_ge_and_not_gt_implies_equality_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_positive_is_nonnegative_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_positive_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_strictly_positive_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_strictly_positive_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_successor_le_implies_lt_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_successor_le_implies_lt_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_constant_lower_bound_weakening_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_constant_lower_bound_weakening_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_negated_strict_successor_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_negated_strict_successor_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_le_and_neq_implies_strict_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_le_and_neq_implies_strict_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })?;
        // The planner selects only Surface-expressible explicit operations.
        // Apply those through the same recursive Proof driver used by
        // authoritative source scripts; the plan is provenance input, not an
        // independently interpreted semantic certificate.
        let proof = self.try_planned_linear_script(&tactics).ok().flatten()?;
        proof.is_complete().then_some(proof)
    }

    /// Runs one branch arm of the linear script driver on the focused sibling
    /// goal. Both smart and explicit bodies apply their operations directly to
    /// this `Proof`; ordinary source interpretation does not first construct a
    /// certificate.
    pub(super) fn try_focused_script_arm(
        &self,
        tactics: &[ProofTactic],
        authoritative: bool,
        generated: bool,
    ) -> Result<Option<Self>, ClickError> {
        if generated {
            self.try_planned_linear_script(tactics)
        } else if authoritative {
            self.try_authoritative_linear_script(tactics)
        } else {
            self.try_linear_script(tactics)
        }
    }

    /// Interprets one supported source script directly on this proof.
    ///
    /// Smart tactics search for checked descendants while explicit tactics
    /// apply their named operation. The returned proof already owns both the
    /// semantic result and its exact provenance; no certificate is constructed
    /// or replayed to establish acceptance.
    pub(in crate::lang::click::proof) fn try_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let contains_search = script_contains_linear_search(tactics);
        match self.try_linear_script_inner(tactics, false, false) {
            // Before this migration, an explicit-only script was checked by
            // the established source interpreter whenever the typed Proof
            // surface did not yet admit it. Preserve that transactional
            // fallback while successful explicit scripts take the direct
            // path. Smart-script failures retain their checked diagnostic.
            Err(_) if !contains_search && !crate::instrumentation::deadline_exceeded() => {
                #[cfg(test)]
                EXPLICIT_LINEAR_FALLBACKS.with(|fallbacks| fallbacks.set(fallbacks.get() + 1));
                Ok(None)
            }
            result => result,
        }
    }

    /// Checks source whose caller has already selected this Proof driver as
    /// the semantic authority. Explicit operation failures propagate instead
    /// of being converted into a compatibility miss; recursive scopes and
    /// branch arms inherit the same rule.
    pub(in crate::lang::click::proof) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.try_linear_script_inner(tactics, true, false)
    }

    /// Applies one planner-selected or expansion-generated Surface script to
    /// this Proof. Generated theorem plans may retain a final `assumption()`
    /// for outcome contexts where the theorem sometimes adds only an anchored
    /// equivalent fact. If an earlier checked operation closes that body
    /// exactly, only that final generated no-op is ignored. Ordinary explicit
    /// source scripts remain strict through `try_linear_script`.
    pub(in crate::lang::click::proof) fn try_planned_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.try_linear_script_inner(tactics, true, true)
    }

    pub(super) fn try_linear_script_inner(
        &self,
        tactics: &[ProofTactic],
        authoritative: bool,
        generated: bool,
    ) -> Result<Option<Self>, ClickError> {
        if tactics.is_empty() {
            return Ok(None);
        }

        // Recognize the complete path before doing any search. `simp` closes
        // the remaining goal and is therefore meaningful only at the end.
        if !linear_script_is_supported(tactics) {
            return Ok(None);
        }

        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if generated
                    && index + 1 == tactics.len()
                    && matches!(tactic, ProofTactic::Assumption)
                {
                    continue;
                }
                // A final `simp` after an exact theorem conclusion is a
                // harmless search no-op and emits no redundant certificate
                // step, matching direct smart closure behavior.
                if matches!(tactic, ProofTactic::Simp) {
                    continue;
                }
                // Let the established explicit/source checker diagnose an
                // invalid suffix after closure. This path has produced no
                // externally visible mutation, and its source-level wording
                // remains part of the diagnostic contract.
                return Ok(None);
            }
            match tactic {
                ProofTactic::ApplyTheorem(application) => {
                    let Some(applied) = proof.try_theorem_application(application)? else {
                        return Ok(None);
                    };
                    proof = applied;
                }
                ProofTactic::Simp => {
                    let Some(closed) = proof.try_simp_closure()? else {
                        return Ok(None);
                    };
                    proof = closed;
                }
                ProofTactic::SimpUsing(simp) => {
                    let Some(closed) = proof.try_restricted_simp_closure(&simp.premises) else {
                        return Ok(None);
                    };
                    proof = closed;
                }
                ProofTactic::Have(have) => {
                    let scope = proof.begin_have(have.proposition.clone())?;
                    let selected = match &have.proof {
                        SourceProof::Default
                        | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
                            scope.try_simp_closure()?
                        }
                        SourceProof::Script(body) => {
                            if generated {
                                scope.try_planned_linear_script(body)?
                            } else if authoritative {
                                scope.try_authoritative_linear_script(body)?
                            } else {
                                scope.try_linear_script(body)?
                            }
                        }
                        SourceProof::Tactic(SmartTactic::Frame) => None,
                    };
                    let Some(selected) = selected else {
                        return Ok(None);
                    };
                    proof = selected.join()?;
                }
                ProofTactic::If(proof_if) => {
                    let (split_proof, split, ids) =
                        proof.split_focused_if(proof_if.condition.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(then_done) = split_proof.focus(ids[0])?.try_focused_script_arm(
                        &proof_if.then_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(both_done) = then_done.focus(ids[1])?.try_focused_script_arm(
                        &proof_if.else_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = both_done.join_focused_if(
                        &marker,
                        split,
                        ids,
                        proof_if.condition.clone(),
                    )?;
                }
                ProofTactic::Cases(proof_cases) => {
                    let (split_proof, split, ids) =
                        proof.split_focused_cases(proof_cases.disjunction.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(left_done) = split_proof.focus(ids[0])?.try_focused_script_arm(
                        &proof_cases.left_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(both_done) = left_done.focus(ids[1])?.try_focused_script_arm(
                        &proof_cases.right_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = both_done.join_focused_cases(
                        &marker,
                        split,
                        ids,
                        proof_cases.disjunction.clone(),
                    )?;
                }
                tactic => {
                    let step = explicit_linear_step(tactic)
                        .expect("the linear script was recognized before execution");
                    proof = proof.apply_step(step)?;
                }
            }
        }

        Ok(proof.focused_discharged().then_some(proof))
    }

    /// Smart-only compatibility wrapper retained for focused regressions.
    #[cfg(test)]
    pub(in crate::lang::click::proof) fn try_linear_smart_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        if !script_contains_linear_search(tactics) {
            return Ok(None);
        }
        self.try_linear_script(tactics)
    }

    /// Whether this source proof is wholly represented by the recursive
    /// proposition driver. This is a syntax-only capability query.
    pub(in crate::lang::click::proof) fn supports_linear_source(proof: &SourceProof) -> bool {
        source_proof_is_supported(proof)
    }

    /// Tries a bounded linear statement candidate whose explicit dependencies
    /// are visible before executing the statement.
    ///
    /// This is deliberately narrower than general smart `step` planning. It
    /// requires a general statement's proof facts to consist exactly of
    /// expression-definedness evidence. A local assignment additionally
    /// selects current Surface facts indexed under the assigned name;
    /// unrelated facts remain shared and are never scanned. Selection performs
    /// indexed fact/surface lookups only; the C transition runs once, when the
    /// resulting `StepUsing` is submitted to `apply_step` and retained by the
    /// returned descendant.
    pub(in crate::lang::click::proof) fn try_indexed_statement_step(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_indexed_statement_step_with_unrelated_context(false)
    }

    /// Selects one source smart statement step on this exact checked Proof.
    /// Preserve the established exact-context selection first; only when it
    /// cannot advance may unrelated retained effects or facts be shared by
    /// the broader checked selector. Both paths return only an accepted
    /// `StepUsing` descendant, never planning aftermath.
    pub(in crate::lang::click::proof) fn try_smart_step(&self) -> Result<Option<Self>, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        // A raw-memory transition with no preceding call effect is fully
        // decided by the checked statement operation: the kernel retains
        // exactly the permissions and facts that survive it, so the returned
        // descendant is authoritative. A named entry resource may already
        // have been unfolded out of the current resource context, while a
        // call effect may carry a post-call surface fact needed by a later
        // statement. Both still require continuation-aware search (or an
        // explicit owned scope) before a standalone `step()` can select a
        // sufficient representation.
        if execution.replay.has_resource_surface_history
            || execution.state.resources().has_named_resources()
            || !execution.replay.effect_facts.is_empty()
        {
            return Ok(None);
        }
        if let Some(proof) = self.try_indexed_statement_step()? {
            return Ok(Some(proof));
        }
        self.try_indexed_execute_step()
    }

    /// The same bounded statement selection used by a scoped smart `execute`,
    /// where unrelated facts, resources, and effects remain shared across the
    /// checked transition instead of preventing a candidate. This is separate
    /// from standalone smart `step` so `execute` can traverse an open resource
    /// scope without changing `step`'s established explicit-certificate
    /// selection policy.
    pub(in crate::lang::click::proof) fn try_indexed_execute_step(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        self.try_indexed_statement_step_with_unrelated_context(true)
    }

    pub(super) fn try_indexed_statement_step_with_unrelated_context(
        &self,
        allow_unrelated_context: bool,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = self.execution() else {
            return Err(self.step_error("execution-frontier proof lost its semantic state"));
        };
        if !allow_unrelated_context
            && (!execution.replay.effect_facts.is_empty()
                || !execution.state.resources().facts().is_empty()
                || self.facts().prioritized.is_some())
        {
            return Ok(None);
        }
        let (_, current_state, statement, _) = next_top_level_statement_from_execution_point(
            &execution.replay,
            &execution.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "smart step selection",
        )?;
        if matches!(statement, CStatement::If { .. } | CStatement::While { .. }) {
            return Ok(None);
        }
        let assigned_local = match &statement {
            CStatement::Assign { name, .. } => Some(name.as_str()),
            _ => None,
        };
        let mut required = statement_expression_definedness(&current_state, &statement)
            .into_iter()
            .filter(|fact| !PureFactContext::new().proves(fact))
            .collect::<Vec<_>>();
        required.sort();
        required.dedup();
        if !allow_unrelated_context
            && assigned_local.is_none()
            && self.facts().ordered.len() != required.len()
        {
            return Ok(None);
        }
        let mut selected = Vec::with_capacity(required.len());
        for fact in required {
            let Some(derivation) = self.facts().assumptions().derive_atomic_proposition(&fact)
            else {
                // Definedness may be discharged directly by the Proof-owned
                // resource context rather than by a pure proposition. Probe
                // the explicit empty candidate through the simple checker;
                // it either returns the checked descendant or leaves this
                // root untouched.
                if let Some(proof) = self.try_statement_step_using(Vec::new())? {
                    return Ok(Some(proof));
                }
                continue;
            };
            for premise in derivation.context_premises() {
                if !selected.contains(&premise) {
                    selected.push(premise);
                }
            }
        }
        if !allow_unrelated_context
            && assigned_local.is_none()
            && selected.len() != self.facts().ordered.len()
        {
            return Ok(None);
        }
        let mut indexed_dependencies = BTreeMap::new();
        if allow_unrelated_context {
            // A recent delta fact is a premise candidate only when the
            // focused goal actually owns it: a sibling split's delta spans
            // both arms, and the other arm's path fact may surface in this
            // arm's inherited replay record without being available here.
            for fact in self.state.added_facts.iter() {
                if self.facts().contains_top_level(fact)
                    && execution
                        .replay
                        .surface_propositions
                        .surfaces(fact)
                        .next()
                        .is_some()
                    && !selected.contains(fact)
                {
                    selected.push(fact.clone());
                }
            }
            if let Some(proof) = self.try_statement_step_with_selected_facts(
                execution,
                &selected,
                &indexed_dependencies,
            )? {
                return Ok(Some(proof));
            }
        }
        let mut dependency_names = BTreeSet::new();
        if allow_unrelated_context {
            collect_statement_variable_names(&statement, &mut dependency_names);
        } else if let Some(name) = assigned_local {
            dependency_names.insert(name.to_string());
        }
        for name in dependency_names {
            for fact in execution
                .replay
                .surface_propositions
                .current_c_variable_kernel_facts(&name)
            {
                if self.facts().contains_top_level(fact) {
                    indexed_dependencies
                        .entry(fact.clone())
                        .or_insert_with(|| name.clone());
                    if !selected.contains(fact) {
                        selected.push(fact.clone());
                        if allow_unrelated_context
                            && let Some(proof) = self.try_statement_step_with_selected_facts(
                                execution,
                                &selected,
                                &indexed_dependencies,
                            )?
                        {
                            return Ok(Some(proof));
                        }
                    }
                }
            }
        }
        if allow_unrelated_context {
            return Ok(None);
        }
        self.try_statement_step_with_selected_facts(execution, &selected, &indexed_dependencies)
    }

    pub(super) fn try_statement_step_with_selected_facts(
        &self,
        execution: &ExecutionProofState,
        selected: &[Proposition],
        indexed_dependencies: &BTreeMap<Proposition, String>,
    ) -> Result<Option<Self>, ClickError> {
        let mut premises = Vec::with_capacity(selected.len());
        for fact in selected {
            let surface = indexed_dependencies
                .get(fact)
                .and_then(|name| {
                    execution
                        .replay
                        .surface_propositions
                        .current_c_variable_surface(&fact, name)
                })
                .or_else(|| execution.replay.surface_propositions.surfaces(&fact).next());
            let Some(surface) = surface.cloned() else {
                // A resource-local justification need not have a standalone
                // Surface proposition form. The empty simple candidate
                // remains the only sound fallback and is checked normally.
                return self.try_statement_step_using(Vec::new());
            };
            premises.push(surface);
        }
        self.try_statement_step_using(premises)
    }

    pub(super) fn try_statement_step_using(
        &self,
        premises: Vec<ClickProposition>,
    ) -> Result<Option<Self>, ClickError> {
        match self.apply_step(SimpleProofStep::StepUsing(premises)) {
            Ok(proof) => Ok(Some(proof)),
            Err(_) => {
                check_verification_deadline()?;
                Ok(None)
            }
        }
    }
}
