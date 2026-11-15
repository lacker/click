//! Primitive outputs supply reads used by named output arguments.
use super::*;

/// The call's certified outputs, not its caller frame, provide this authority.
/// The final return transition takes each constructed fact directly; it does
/// not evaluate the clause again. Guards and entry states keep their normal
/// return evaluator, so they cannot lend unconditional post-state authority.
pub(super) fn prepare_produced_argument_supply(
    entry: &ExecutionState,
    evaluation: &mut ExecutionState,
    interface: &FunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<Option<ResourceFact>>> {
    let mut positions = Vec::new();
    let clauses = interface
        .resource_ensures()
        .iter()
        .enumerate()
        .filter_map(|(index, clause)| {
            crate::instrumentation::record_deterministic_work(1);
            if clause.role() != ResourceTransferRole::Produce
                || clause.state_source() == ResourceStateSource::Entry
                || clause.guard().is_some()
                || !matches!(clause.term(), ResourceTerm::Memory(segment) if segment.guard().is_none())
            {
                return None;
            }
            positions.push(index);
            Some(clause.clone())
        })
        .collect::<Vec<_>>();
    // This is the ordinary section evaluator's dependency queue. It wakes
    // only clauses whose missing cells have become available, so reversed
    // pointer chains do not require rounds over every pending clause.
    // These are the certified callee's own output clauses. Its checked body
    // established their subobject extents, just as an opened resource body's
    // clauses carry the extents its fold established. Reads still need the
    // section's actual cell authority; this does not relax call requirements.
    let output_assumptions = assumptions.clone().assume_entry_clause_extents();
    let checked = evaluate_resource_clauses_in_section(
        entry,
        evaluation,
        &clauses,
        &[],
        &output_assumptions,
        budget,
        false,
    )?
    .expect("unguarded partial preparation does not require unresolved clauses");
    let mut prepared = vec![None; interface.resource_ensures().len()];
    let mut views = Vec::new();
    for checked in checked {
        let index = positions[checked
            .section_index
            .expect("section retains clause indexes")];
        if let Some(view) = checked.fact.core_with_assumptions(assumptions) {
            views.push(view);
        }
        prepared[index] = Some(checked.fact);
    }
    evaluation.resources = evaluation.resources.clone().unchecked_with_facts(views);
    Ok(prepared)
}
