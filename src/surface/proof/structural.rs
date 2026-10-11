use super::*;

pub(super) fn resolve_code_region_ref(
    function_block: &FunctionBlock,
    region_ref: &CodeRegionRef,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CodeRegion, ClickError> {
    Ok(match region_ref {
        CodeRegionRef::BackEdge => {
            return Err(ClickError::new(
                "back_edge regions are supported only by `execute_until`",
            ));
        }
        CodeRegionRef::Assignment { .. } | CodeRegionRef::Read(_) => {
            return Err(ClickError::new(
                "assignment and read regions are supported only by `execute_until`",
            ));
        }
        CodeRegionRef::Function => CodeRegion::Function,
        CodeRegionRef::Loop(index) => CodeRegion::Loop(*index),
        CodeRegionRef::Statement(index) => CodeRegion::Statement(*index),
        CodeRegionRef::Label(label) => *function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.label() == Some(label.as_str()))
            .map(StructuralClause::region)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: unknown code region label `{label}`"
                ))
            })?,
    })
}

pub(super) fn requirements_with_structural_unfolds(
    spec_definitions: SpecDefinitions<'_>,
    function_block: &FunctionBlock,
    requirement_pure_facts: &PureFactList,
) -> Result<PureFactList, String> {
    let unfolded_predicates = structural_unfold_tactic_names(function_block);
    let unfolded = unfold_available_predicate_facts(
        spec_definitions,
        &unfolded_predicates,
        requirement_pure_facts,
    )?;
    // Unfolding only appends, so the result extends the list and keeps the
    // context it carried.
    debug_assert!(unfolded.starts_with(requirement_pure_facts));
    let mut facts = requirement_pure_facts.clone();
    facts.extend(unfolded.into_iter().skip(requirement_pure_facts.len()));
    Ok(facts)
}

pub(super) fn structural_unfold_tactic_names(function_block: &FunctionBlock) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for clause in function_block.structural_clauses() {
        for proof in [clause.initialize_proof(), clause.preserve_proof()]
            .into_iter()
            .flatten()
        {
            for name in proof.unfold_tactic_names() {
                if seen.insert(name.clone()) {
                    names.push(name);
                }
            }
        }
    }
    names
}
