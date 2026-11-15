//! Search exposes historical endpoint equalities as ordinary, explicit facts.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_history_indexed_equalities(
        search_input: &Proof<'a>,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_history_indexed_equalities");
        if search_input.surface_goal() != Some(target)
            || old_reflexive_transport_source(target).as_ref() != Some(source)
        {
            return Ok(None);
        }
        let ClickProposition::Comparison {
            left: read,
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Old(old),
        } = target
        else {
            return Ok(None);
        };
        if read != old.as_ref()
            || !matches!(
                contract_expression_as_program_expression(read),
                Some(ProgramExpression::Index(..))
            )
        {
            return Ok(None);
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let mut proof = search_input.clone();
        for (selector, _) in records.iter() {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Entry,
            }) = selector
            else {
                continue;
            };
            let exit = ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region.clone(),
                kind: ProgramPointKind::Exit,
            });
            if records.get(&exit).is_none() {
                continue;
            }
            let at = |selector| ContractExpression::At {
                selector,
                expression: Box::new(read.clone()),
            };
            let equality = ClickProposition::Comparison {
                left: at(exit),
                operator: ComparisonOperator::Equal,
                right: at(selector.clone()),
            };
            // Expose the selected endpoint terms to ordinary equality reasoning.
            // No premise or memory history is reconstructed during replay.
            let candidate = (|| {
                let scope = proof
                    .driver()
                    .open_have_with_goal_observations(equality, true)?;
                scope.driver().apply_step(ProofStep::Known)?.join()
            })();
            if let Some(unchanged) = attempt::candidate_outcome(candidate)? {
                proof = unchanged;
            }
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }
}
