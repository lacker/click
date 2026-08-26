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
        CodeRegionRef::Mark(name) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: proof mark `{name}` is not a code region"
            )));
        }
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

/// Validates a code-region-qualified frame independently of the surrounding
/// function claim. Qualified frames contribute preservation facts for later
/// proposition checking; unlike an unqualified function frame, their
/// structural requirements do not depend on whether the current claim is an
/// ensure or an effect.
pub(super) fn validate_qualified_frame_code_region(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    code_region: CodeRegion,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(), ClickError> {
    match code_region {
        CodeRegion::Function => Ok(()),
        CodeRegion::Loop(loop_index) => {
            validate_loop_code_region(parsed_function, loop_index, claim_label, tactic_index)?;
            if !function_block.structural_clauses().iter().any(|clause| {
                clause.region() == &CodeRegion::Loop(loop_index)
                    && clause.items().iter().any(StructuralItem::is_effect_kind)
            }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `frame(loop({loop_index}))` needs a loop effect clause such as `mutable` or `immutable`; declare one in this proof's `loop` tactic for loop({loop_index})"
                )));
            }
            Ok(())
        }
        CodeRegion::Statement(statement_index) => {
            let statement_count = count_statements(parsed_function.body());
            if statement_index >= statement_count {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: function has no `statement({statement_index})` code region; it contains {statement_count} statement(s)"
                )));
            }
            Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `frame(statement({statement_index}))` is not supported yet"
            )))
        }
    }
}

pub(super) fn validate_function_frame_tactic(
    execution: &CFunctionExecutionCandidates,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    tactic_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    requirement_pure_facts: &[Proposition],
) -> Result<(), ClickError> {
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `frame()` had no complete execution path"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `frame()` failed on path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    requirement_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    path.facts()
                )
            )));
        }
        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        check_effect_claim_exact(
            claim_label,
            path_index,
            path.effect_facts(),
            &path_requirements,
            claim,
            parameters,
            arguments,
            state,
            path.outcome(),
        )?;
    }

    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_effect_claim_exact(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[ExecutionPureFact],
    available_pure_facts: &[Proposition],
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    let FunctionClaimRef::Effect(_, effect_clause) = claim else {
        return Err(ClickError::new(format!(
            "`frame()` requires an effect claim for `{claim_label}`"
        )));
    };
    prove_effect_clause_exact(
        claim_label,
        path_index,
        execution_pure_facts,
        available_pure_facts,
        effect_clause.effect(),
        parameters,
        arguments,
        pre_state,
        outcome,
    )
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
        for item in clause.items() {
            for name in item.proof().unfold_tactic_names() {
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
        FunctionClaimRef::Effect(_, _) => vec![vec![
            ProofTactic::SmartExecuteAllPaths,
            ProofTactic::SmartFrame(None),
        ]],
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
    let mut base = vec![ProofTactic::SmartExecute];
    base.extend(
        loop_effect_summary_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofTactic::FrameUsing {
                region: Some(CodeRegionRef::Loop(loop_index)),
                premises: Vec::new(),
            }),
    );

    match claim {
        FunctionClaimRef::Ensure(_, _) => {
            let mut simp = base;
            simp.push(ProofTactic::Simp);
            vec![simp]
        }
        FunctionClaimRef::Effect(_, _) => {
            base.push(ProofTactic::SmartFrame(None));
            vec![base]
        }
    }
}

pub(super) fn loop_effect_summary_regions(function_block: &FunctionBlock) -> BTreeSet<usize> {
    function_block
        .structural_clauses()
        .iter()
        .filter_map(|clause| match clause.region() {
            CodeRegion::Loop(index)
                if clause.items().iter().any(StructuralItem::is_effect_kind) =>
            {
                Some(*index)
            }
            _ => None,
        })
        .collect()
}
