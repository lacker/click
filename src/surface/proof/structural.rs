use super::*;

pub(super) fn resolve_code_region_ref(
    function_block: &FunctionBlock,
    region_ref: &CodeRegionRef,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CodeRegion, ClickError> {
    Ok(match region_ref {
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

pub(super) fn validate_loop_code_region(
    parsed_function: &syntax::C0Function,
    loop_index: usize,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    if loop_index >= loop_count {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: function has no `loop({loop_index})` code region; it contains {loop_count} loop(s)"
        )));
    }
    Ok(())
}

pub(super) fn requirements_with_structural_unfolds(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_block: &FunctionBlock,
    requirement_pure_facts: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    let unfolded_predicates = structural_unfold_tactic_names(function_block);
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        requirement_pure_facts,
    )
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

pub(super) fn bounded_execution_tactic_candidates(
    claim: &FunctionClaimRef<'_>,
) -> Vec<Vec<ProofTactic>> {
    match claim {
        FunctionClaimRef::Ensure(_, _) => {
            vec![vec![ProofTactic::SmartExecuteAllPaths, ProofTactic::Simp]]
        }
    }
}

pub(super) fn auto_loop_verification_tactic_candidates(
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
) -> Vec<Vec<ProofTactic>> {
    if !function_block
        .structural_clauses()
        .iter()
        .any(|clause| matches!(clause.region(), CodeRegion::Loop(_)))
    {
        return Vec::new();
    }
    let base = vec![ProofTactic::SmartExecute];

    match claim {
        FunctionClaimRef::Ensure(_, _) => {
            let mut simp = base;
            simp.push(ProofTactic::Simp);
            vec![simp]
        }
    }
}
