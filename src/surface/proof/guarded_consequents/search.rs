//! Discovery adapters over the existing persistent proof.
use super::*;
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_guarded_consequent_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_guarded_consequent_closure");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        if !matches!(goal, Proposition::ConditionIs(..)) {
            return Ok(None);
        }
        let candidates = search_input.facts().guarded_implications_mentioning(goal);
        if candidates.is_empty() {
            return Ok(None);
        }
        let Some(_scope) = GuardedConsequentScope::enter() else {
            return Ok(None);
        };
        for implication in candidates.into_iter().take(MAX_GUARDED_CANDIDATES) {
            let Proposition::Implies(guard, consequent) = &implication else {
                continue;
            };
            if search_input.facts().contains(consequent)
                || crate::kernel::search::ProofSearch::antecedent_is_refuted(search_input, guard)
            {
                continue;
            }
            let Some((surface_guard, surface_consequent)) =
                search_input.guarded_implication_surfaces(guard, consequent)
            else {
                continue;
            };
            // A native consequent is spelled by the observations it compares,
            // so the step reads the same fact wherever arithmetic is Integer.
            let surface_consequent =
                super::smart_closures::observed_native_arithmetic(consequent, &surface_consequent);
            let Some(with_guard) =
                crate::kernel::search::ProofSearch::prove_guard(search_input, &surface_guard)?
            else {
                continue;
            };
            let fact = ClickProposition::Implies(
                Box::new(surface_guard.clone()),
                Box::new(surface_consequent.clone()),
            );
            let Some(extracted) = attempt::candidate_outcome(with_guard.driver().apply_step(
                ProofStep::ApplyFactUsing {
                    fact,
                    premises: vec![surface_guard.clone()],
                },
            ))?
            else {
                continue;
            };
            if extracted.is_complete() || extracted.focused_discharged() {
                return Ok(Some(extracted));
            }
            // An equality consequent names a goal operand: rewriting the goal
            // with it leaves the operands' own facts to close what remains.
            if matches!(consequent.as_ref(), Proposition::ConditionIs(condition, truth)
                if crate::kernel::machine_integer::comparison::comparison_view(condition.native_compat(), *truth)
                    .is_some_and(|v| v.relation == crate::kernel::machine_integer::Relation::Equal
                        && matches!(v.format, MachineIntegerType::Int32 | MachineIntegerType::UInt32 | MachineIntegerType::Int64 | MachineIntegerType::UInt64)))
                && let Some(rewritten) = attempt::candidate_outcome(
                    extracted
                        .driver()
                        .apply_step(ProofStep::Rewrite(surface_consequent.clone())),
                )?
            {
                if rewritten.focused_discharged() {
                    return Ok(Some(rewritten));
                }
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_solve_closure(&(rewritten))?
                {
                    return Ok(Some(closed));
                }
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_solve_closure(&(extracted))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// The `close() using { .. }` form: a listed guarded equality whose guard
    /// the list does not state.
    pub(in crate::surface::proof) fn try_restricted_guarded_consequent(
        search_input: &Proof<'a>,
        surfaces: &[ClickProposition],
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restricted_guarded_consequent");
        for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
            let Proposition::Implies(guard, consequent) = kernel else {
                continue;
            };
            let ClickProposition::Implies(surface_guard, surface_consequent) = surface else {
                continue;
            };
            if !crate::kernel::proof::is_definedness_guard(guard)
                || premise_pairs
                    .iter()
                    .any(|(listed, _)| listed == guard.as_ref())
                || !matches!(consequent.as_ref(), Proposition::ConditionIs(..))
            {
                continue;
            }
            let others = surfaces
                .iter()
                .enumerate()
                .filter(|(other, _)| *other != index)
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>();
            let scope = search_input
                .driver()
                .open_have(surface_guard.as_ref().clone())
                .ok()?;
            // The guard is a side condition of the listed fact: prefer the
            // other listed premises, and otherwise decide it as `solve` would.
            let proved = if others.is_empty() {
                None
            } else {
                (scope).driver().try_restricted_solve_closure(&others)
            }
            .or_else(|| (scope).driver().try_solve_closure().ok().flatten());
            let Some(proved) = proved else {
                continue;
            };
            let with_guard = proved.join().ok()?;
            let surface_consequent =
                super::smart_closures::observed_native_arithmetic(consequent, surface_consequent);
            let extracted = with_guard
                .driver()
                .apply_step(ProofStep::ApplyFactUsing {
                    fact: surface.clone(),
                    premises: vec![surface_guard.as_ref().clone()],
                })
                .ok()?;
            if extracted.focused_discharged() {
                return Some(extracted);
            }
            let mut remaining = others;
            remaining.push(surface_consequent);
            return crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                &(extracted),
                &remaining,
            );
        }
        None
    }

    /// Whether the kernel's own decision already refutes one conjunct of an
    /// antecedent, so proving it would be a search bound to fail (the other
    /// outcome's `result == 0 implies ..` on a path where `result == 1`).
    pub(in crate::surface::proof) fn antecedent_is_refuted(
        search_input: &Proof<'a>,
        antecedent: &Proposition,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("antecedent_is_refuted");
        let mut pending = vec![antecedent];
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                Proposition::ConditionIs(condition, value)
                    if search_input
                        .facts()
                        .assumptions()
                        .decide(condition.native_compat())
                        .is_some_and(|decided| decided != *value) =>
                {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    /// `have <guard> by { close(); }`, or the proof unchanged when the guard
    /// is already available.
    pub(in crate::surface::proof) fn prove_guard(
        search_input: &Proof<'a>,
        surface_guard: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prove_guard");
        let Some(scope) =
            attempt::candidate_outcome(search_input.driver().open_have(surface_guard.clone()))?
        else {
            return Ok(None);
        };
        let Some(proved) = (scope).driver().try_solve_closure()? else {
            return Ok(None);
        };
        attempt::candidate_outcome(proved.join())
    }
}
