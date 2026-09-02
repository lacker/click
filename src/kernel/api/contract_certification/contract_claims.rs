use super::*;

/// Binds a completed kernel proposition proof to the exact function path
/// theorem that produced its outcome. This records proof authority; it does
/// not attempt to prove or simplify the proposition again.
pub(crate) fn c_checked_function_proposition(
    function: &CFunction,
    specification: &CFunctionSpecification,
    theorem: &Theorem,
    completion: &crate::kernel::proof::CheckedProposition,
    path_outcome: Option<&CFunctionOutcome>,
) -> Option<CCheckedFunctionProposition> {
    let mut conclusion = theorem.proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    let theorem_specification = match conclusion {
        Proposition::CFunctionSatisfiesSpecification {
            function: proved_function,
            specification,
        }
        | Proposition::CFunctionPartiallySatisfiesSpecification {
            function: proved_function,
            specification,
        } if proved_function == function => specification,
        _ => return None,
    };
    if theorem_specification != specification {
        return None;
    }
    let CFunctionOutcome::Return { value, state } = specification.outcome() else {
        return None;
    };
    // The completion records the outcome it was proved at when its root was
    // focused from a function-outcome obligation; a root focused on a
    // fixed-state frontier records none, and the caller names the path
    // outcome that frontier was built from.
    let (result, outcome_state): (&CValue, &CState) = match completion.outcome() {
        Some(outcome) => (outcome.result.as_ref(), &outcome.state),
        None => match path_outcome {
            Some(CFunctionOutcome::Return { value, state }) => (value, state),
            _ => return None,
        },
    };
    // The sealed outcome is the proof's outcome under the contract's exit
    // rule: the same result, memory, and locals, with resources and
    // populations in the contract's representation. A proposition the proof
    // completed about the result and memory holds at either; a proposition
    // that embeds the raw state cannot match a lowering at the sealed one
    // and is simply never consulted.
    if result != value
        || outcome_state.memory() != state.memory()
        || outcome_state.locals() != state.locals()
    {
        return None;
    }
    Some(CCheckedFunctionProposition {
        function: function.clone(),
        specification: specification.clone(),
        proposition: completion.proposition().clone(),
    })
}

pub fn c_function_outcomes_definitionally_equal(
    function: &CFunction,
    left: &CFunctionOutcome,
    right: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    match (left, right) {
        (
            CFunctionOutcome::Return {
                value: _,
                state: left_state,
            },
            CFunctionOutcome::Return {
                value: _,
                state: right_state,
            },
        ) => {
            if !c_function_outcomes_program_state_definitionally_equal(left, right, assumptions) {
                return false;
            }
            resource_context_definitionally_contains(
                left_state.resources(),
                right_state.resources(),
                function.composite_resource_definitions(),
                left_state.memory(),
                assumptions,
            ) || resource_context_definitionally_contains(
                right_state.resources(),
                left_state.resources(),
                function.composite_resource_definitions(),
                left_state.memory(),
                assumptions,
            ) || resource_contexts_definitionally_equal(
                function,
                left_state.memory(),
                left_state.resources(),
                right_state.memory(),
                right_state.resources(),
                assumptions,
            )
        }
        _ => left == right,
    }
}

/// Compares the observable program portion of two outcomes, leaving ghost
/// resource representation to the definitional resource checks.
pub fn c_function_outcomes_program_state_definitionally_equal(
    left: &CFunctionOutcome,
    right: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    match (left, right) {
        (
            CFunctionOutcome::Return {
                value: left_value,
                state: left_state,
            },
            CFunctionOutcome::Return {
                value: right_value,
                state: right_state,
            },
        ) => {
            c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions)
                && c_memories_definitionally_equal(
                    left_state.memory(),
                    right_state.memory(),
                    assumptions,
                )
        }
        _ => left == right,
    }
}

/// Proves two return outcomes equal from matching certified execution
/// histories. This recognizes equal store chains and alpha-equivalent call
/// havoc snapshots without treating unrelated fresh havoc identities as
/// interchangeable.
pub fn c_function_outcomes_equal_by_execution_provenance(
    function: &CFunction,
    left: &CFunctionOutcome,
    left_facts: &[ExecutionPureFact],
    right: &CFunctionOutcome,
    right_facts: &[ExecutionPureFact],
    assumptions: &PureFactContext,
) -> bool {
    if !c_function_outcomes_program_state_equal_by_execution_provenance(
        left,
        left_facts,
        right,
        right_facts,
        assumptions,
    ) {
        return false;
    }
    let (
        CFunctionOutcome::Return {
            state: left_state, ..
        },
        CFunctionOutcome::Return {
            state: right_state, ..
        },
    ) = (left, right)
    else {
        return false;
    };
    resource_context_definitionally_contains(
        left_state.resources(),
        right_state.resources(),
        function.composite_resource_definitions(),
        left_state.memory(),
        assumptions,
    ) || resource_context_definitionally_contains(
        right_state.resources(),
        left_state.resources(),
        function.composite_resource_definitions(),
        left_state.memory(),
        assumptions,
    ) || resource_contexts_definitionally_equal(
        function,
        left_state.memory(),
        left_state.resources(),
        right_state.memory(),
        right_state.resources(),
        assumptions,
    )
}

/// Compares the observable program state of two return paths by matching their
/// certified execution histories. Resource representation remains the
/// responsibility of the separate resource certificate.
pub fn c_function_outcomes_program_state_equal_by_execution_provenance(
    left: &CFunctionOutcome,
    left_facts: &[ExecutionPureFact],
    right: &CFunctionOutcome,
    right_facts: &[ExecutionPureFact],
    assumptions: &PureFactContext,
) -> bool {
    let (
        CFunctionOutcome::Return {
            value: left_value,
            state: left_state,
        },
        CFunctionOutcome::Return {
            value: right_value,
            state: right_state,
        },
    ) = (left, right)
    else {
        return false;
    };
    memories_equal_by_execution_provenance(
        left_state.memory(),
        left_facts,
        right_state.memory(),
        right_facts,
        assumptions,
    ) && (c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions)
        || return_values_equal_by_certified_stores(
            left_value,
            left_state.memory(),
            left_facts,
            right_value,
            assumptions,
        )
        || return_values_equal_by_certified_stores(
            left_value,
            right_state.memory(),
            right_facts,
            right_value,
            assumptions,
        ))
}

fn return_values_equal_by_certified_stores(
    left: &CValue,
    post_memory: &CMemory,
    execution_facts: &[ExecutionPureFact],
    right: &CValue,
    assumptions: &PureFactContext,
) -> bool {
    let (CValue::Int32(left) | CValue::UInt8(left), CValue::Int32(right) | CValue::UInt8(right)) =
        (left, right)
    else {
        return false;
    };
    certification_proves_post_proposition(
        assumptions,
        &Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), true),
        post_memory,
        execution_facts,
    )
}

fn memories_equal_by_execution_provenance(
    left_final: &CMemory,
    left_facts: &[ExecutionPureFact],
    right_final: &CMemory,
    right_facts: &[ExecutionPureFact],
    assumptions: &PureFactContext,
) -> bool {
    if memories_equal_by_matching_derivations(left_final, right_final, assumptions, 0) {
        return true;
    }
    let left_stores = left_facts
        .iter()
        .filter_map(ExecutionPureFact::certified_store_data)
        .collect::<Vec<_>>();
    let right_stores = right_facts
        .iter()
        .filter_map(ExecutionPureFact::certified_store_data)
        .collect::<Vec<_>>();
    if left_stores.is_empty() || left_stores.len() != right_stores.len() {
        return false;
    }
    let chain_reaches_final = |stores: &[&CertifiedMemoryStore], final_memory: &CMemory| {
        stores.windows(2).all(|pair| {
            c_memories_definitionally_equal(&pair[0].after, &pair[1].before, assumptions)
        }) && c_memories_definitionally_equal(
            &stores.last().expect("store chain is nonempty").after,
            final_memory,
            assumptions,
        )
    };
    c_memories_definitionally_equal(&left_stores[0].before, &right_stores[0].before, assumptions)
        && chain_reaches_final(&left_stores, left_final)
        && chain_reaches_final(&right_stores, right_final)
        && left_stores.iter().zip(&right_stores).all(|(left, right)| {
            (pointers_proven_equal_for_memory_resolution(
                &left.pointer,
                &right.pointer,
                assumptions,
            ) || (left.pointer.block == right.pointer.block
                && c_pointer_offsets_proven_equal_for_effect(
                    &left.pointer.offset,
                    &right.pointer.offset,
                    assumptions,
                )))
                && c_values_proven_equal_for_memory_resolution(
                    &left.value,
                    &right.value,
                    assumptions,
                )
        })
}

fn memories_equal_by_matching_derivations(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
    depth: usize,
) -> bool {
    fn transparent_base(derivation: &CMemoryDerivation) -> Option<&SharedCMemory> {
        match derivation {
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
                ..
            } if pointer.block.starts_with("local:")
                || store_is_self_materialization(base, pointer, value) =>
            {
                Some(base)
            }
            CMemoryDerivation::BlockDeclared { base, block } if block.starts_with("local:") => {
                Some(base)
            }
            CMemoryDerivation::ContractAllocationClaimsChanged { base } => Some(base),
            CMemoryDerivation::CellsForgotten { base } => Some(base),
            _ => None,
        }
    }
    /// A store whose value is the base memory's own load at the stored
    /// pointer is a no-op: the produced memory denotes the same state as its
    /// base, differing only in which cells are materialized. Proof execution
    /// mints such edges when a tactic forces a symbolic load into a concrete
    /// cell, and independent certification never does, so chain matching
    /// must see through them. Purely structural — the load's memory operand
    /// must be the base itself (by interned identity), no proving.
    fn store_is_self_materialization(
        base: &SharedCMemory,
        pointer: &Pointer,
        value: &CValue,
    ) -> bool {
        let (CValue::Int32(Bitvector32Term::MemoryLoad(load_memory, load_pointer))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(load_memory, load_pointer))) = value
        else {
            return false;
        };
        load_pointer.as_ref() == pointer
            && intern_c_memory_ref(load_memory).arena_id() == base.arena_id()
    }
    const DERIVATION_MATCH_LIMIT: usize = 64;
    if depth >= DERIVATION_MATCH_LIMIT {
        return false;
    }
    if c_memories_definitionally_equal(left, right, assumptions) {
        return true;
    }
    let left = intern_c_memory_ref(left);
    let right = intern_c_memory_ref(right);
    let left_derivation = left.derivation();
    let right_derivation = right.derivation();
    if let Some(base) = left_derivation.as_deref().and_then(transparent_base) {
        return memories_equal_by_matching_derivations(base, &right, assumptions, depth + 1);
    }
    if let Some(base) = right_derivation.as_deref().and_then(transparent_base) {
        return memories_equal_by_matching_derivations(&left, base, assumptions, depth + 1);
    }
    match (left_derivation.as_deref(), right_derivation.as_deref()) {
        (
            Some(CMemoryDerivation::CallHavoc {
                base: left_base,
                mutable_ranges: left_ranges,
                ..
            }),
            Some(CMemoryDerivation::CallHavoc {
                base: right_base,
                mutable_ranges: right_ranges,
                ..
            }),
        ) => {
            memory_range_lists_definitionally_equal(left_ranges, right_ranges, assumptions)
                && memories_equal_by_matching_derivations(
                    left_base,
                    right_base,
                    assumptions,
                    depth + 1,
                )
        }
        (
            Some(CMemoryDerivation::Store {
                base: left_base,
                pointer: left_pointer,
                value: left_value,
                ..
            }),
            Some(CMemoryDerivation::Store {
                base: right_base,
                pointer: right_pointer,
                value: right_value,
                ..
            }),
        ) => {
            pointers_proven_equal_for_memory_resolution(left_pointer, right_pointer, assumptions)
                && c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions)
                && memories_equal_by_matching_derivations(
                    left_base,
                    right_base,
                    assumptions,
                    depth + 1,
                )
        }
        _ => false,
    }
}

fn memory_range_lists_definitionally_equal(
    left: &[CMemoryRange],
    right: &[CMemoryRange],
    assumptions: &PureFactContext,
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            pointers_proven_equal_for_memory_resolution(left.base(), right.base(), assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(
                    left.start(),
                    right.start(),
                    assumptions,
                )
                && bitvector_terms_proven_equal_for_memory_resolution(
                    left.end(),
                    right.end(),
                    assumptions,
                )
        })
}

pub(in crate::kernel) fn c_memories_definitionally_equal(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    if memories_proven_equal_for_memory_resolution(left, right, assumptions) {
        return true;
    }
    if !left
        .blocks
        .iter()
        .filter(|(block, _)| !block.starts_with("local:"))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !block.starts_with("local:")))
    {
        return false;
    }
    memory_cells_definitionally_contained(left, right, assumptions)
        && memory_cells_definitionally_contained(right, left, assumptions)
}

fn memory_cells_definitionally_contained(
    source: &CMemory,
    target: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    for (source_pointer, source_value) in source
        .cells
        .iter()
        .filter(|(pointer, _)| !pointer.block.starts_with("local:"))
    {
        let matching = target.cells.iter().find(|(target_pointer, _)| {
            pointers_proven_equal_for_memory_resolution(source_pointer, target_pointer, assumptions)
        });
        let equal = if let Some((_, target_value)) = matching {
            c_values_proven_equal_for_memory_resolution(source_value, target_value, assumptions)
        } else {
            materialized_load_is_unchanged(source_value, target, source_pointer, assumptions)
        };
        if !equal {
            return false;
        }
    }
    true
}

fn materialized_load_is_unchanged(
    value: &CValue,
    symbolic_memory: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let load = match value {
        CValue::Int32(Bitvector32Term::MemoryLoad(memory, load_pointer))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(memory, load_pointer)) => {
            (memory.clone(), load_pointer.as_ref().clone())
        }
        // With terms canonical at creation a materialized cell holds the
        // load variable for its load; the registry records the load it
        // stands for.
        CValue::Int32(Bitvector32Term::Variable(variable))
        | CValue::UInt8(Bitvector32Term::Variable(variable))
            if crate::kernel::eval::is_load_variable(variable) =>
        {
            let Some(load) = crate::kernel::eval::registered_load_for_variable(variable) else {
                return false;
            };
            load
        }
        _ => return false,
    };
    pointers_proven_equal_for_memory_resolution(&load.1, pointer, assumptions)
        && c_memory_load_is_unchanged(&load.0, symbolic_memory, pointer, assumptions)
}

struct CertifiedFunctionClaimPath {
    caller_state: CState,
    arguments: Vec<CExpression>,
    outcome: CFunctionOutcome,
    return_state: Option<CState>,
    entry_state: CState,
    required_resources: ResourceContext,
    entry_resources: ResourceContext,
    post_state: Option<CState>,
    post_resources: Option<ResourceContext>,
    assumptions: PureFactContext,
    execution_facts: Vec<ExecutionPureFact>,
    effect_facts: Vec<ExecutionPureFact>,
}

/// Quantifier binders of a lowered proposition, in traversal order.
fn proposition_quantifier_binders(proposition: &Proposition, binders: &mut Vec<Variable>) {
    match proposition {
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            binders.push(*var);
            proposition_quantifier_binders(body, binders);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            proposition_quantifier_binders(left, binders);
            proposition_quantifier_binders(right, binders);
        }
        Proposition::Not(body) => proposition_quantifier_binders(body, binders),
        _ => {}
    }
}

/// Quantifier binders of a specification proposition, in traversal order.
fn spec_quantifier_binders(proposition: &SpecProposition, binders: &mut Vec<Variable>) {
    match proposition {
        SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. } => {
            binders.push(*variable);
            spec_quantifier_binders(body, binders);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_quantifier_binders(left, binders);
            spec_quantifier_binders(right, binders);
        }
        SpecProposition::Not(body) => spec_quantifier_binders(body, binders),
        _ => {}
    }
}

/// Renames one quantifier binder of a specification proposition, in the
/// binder and throughout its body. Variable substitution alone stops at the
/// binding site, which is exactly the occurrence to change here.
fn rename_spec_binder(
    proposition: &SpecProposition,
    from: Variable,
    to: Variable,
) -> SpecProposition {
    let rename_body = |body: &SpecProposition| {
        crate::kernel::reasoning::substitute_bitvector_variable_in_spec_proposition(
            body,
            from,
            &Bitvector32Term::Variable(to),
        )
    };
    match proposition {
        SpecProposition::ForAllInt32 {
            name,
            variable,
            body,
        } => SpecProposition::ForAllInt32 {
            name: name.clone(),
            variable: if *variable == from { to } else { *variable },
            body: Box::new(if *variable == from {
                rename_body(body)
            } else {
                rename_spec_binder(body, from, to)
            }),
        },
        SpecProposition::ExistsInt32 {
            name,
            variable,
            body,
        } => SpecProposition::ExistsInt32 {
            name: name.clone(),
            variable: if *variable == from { to } else { *variable },
            body: Box::new(if *variable == from {
                rename_body(body)
            } else {
                rename_spec_binder(body, from, to)
            }),
        },
        SpecProposition::And(left, right) => SpecProposition::And(
            Box::new(rename_spec_binder(left, from, to)),
            Box::new(rename_spec_binder(right, from, to)),
        ),
        SpecProposition::Or(left, right) => SpecProposition::Or(
            Box::new(rename_spec_binder(left, from, to)),
            Box::new(rename_spec_binder(right, from, to)),
        ),
        SpecProposition::Implies(left, right) => SpecProposition::Implies(
            Box::new(rename_spec_binder(left, from, to)),
            Box::new(rename_spec_binder(right, from, to)),
        ),
        SpecProposition::Not(body) => {
            SpecProposition::Not(Box::new(rename_spec_binder(body, from, to)))
        }
        other => other.clone(),
    }
}

/// Lowers a quantified ensure under the binders of a completed proposition
/// that has the same quantifier shape, when every lowered path then matches
/// a completion; otherwise lowers it under its own binders. One extra
/// lowering per distinct binder list a completion names.
fn lower_ensure_under_completion_binders(
    post_state: &CState,
    ensure: &SpecProposition,
    entry_state: &CState,
    lowering_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    checked_propositions: &BTreeMap<Proposition, Vec<&CCheckedFunctionProposition>>,
) -> Result<Vec<crate::kernel::spec::SpecPropositionPath>, ExecutionLimit> {
    let mut spec_binders = Vec::new();
    spec_quantifier_binders(ensure, &mut spec_binders);
    if !spec_binders.is_empty() {
        let mut tried = std::collections::BTreeSet::new();
        for key in checked_propositions.keys() {
            let mut key_binders = Vec::new();
            proposition_quantifier_binders(key, &mut key_binders);
            if key_binders.len() != spec_binders.len()
                || key_binders == spec_binders
                || !tried.insert(key_binders.clone())
            {
                continue;
            }
            let renamed = spec_binders
                .iter()
                .zip(&key_binders)
                .fold(ensure.clone(), |proposition, (from, to)| {
                    rename_spec_binder(&proposition, *from, *to)
                });
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                post_state,
                &renamed,
                Some(entry_state),
                lowering_assumptions,
                budget,
            )?;
            if !paths.is_empty()
                && paths
                    .iter()
                    .all(|path| checked_propositions.contains_key(&path.proposition))
            {
                return Ok(paths);
            }
        }
    }
    lower_spec_proposition_at_state_with_loop_entry(
        post_state,
        ensure,
        Some(entry_state),
        lowering_assumptions,
        budget,
    )
}

fn prepare_function_claim_path(
    function: &CFunction,
    path: &SymbolicCExecutionPath,
) -> Result<CertifiedFunctionClaimPath, String> {
    let Some((caller_state, arguments, outcome, assumptions)) =
        certified_function_path_parts(function, path)
    else {
        return Err("the certified path does not belong to the exact function".to_string());
    };
    let Some(mut entry_state) = c_function_entry_state(caller_state, function, arguments) else {
        return Err("the function entry state cannot be reconstructed".to_string());
    };
    let mut budget = ExecutionBudget::default();
    let required_resources = match evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        &assumptions,
        &mut budget,
    ) {
        Ok(Ok(resources)) => resources,
        Ok(Err(error)) => {
            return Err(format!(
                "the required resource context cannot be evaluated: {error:?}"
            ));
        }
        Err(limit) => {
            return Err(format!(
                "the required resource context hit execution limit {limit:?}"
            ));
        }
    };
    let Some((_, definition_facts)) = expand_all_composite_resource_facts_and_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    ) else {
        return Err("the required composite resources cannot be expanded".to_string());
    };
    let mut assumptions = assumptions_with_propositions(&assumptions, &definition_facts);
    let Some(population_facts) = evaluate_resource_population_fact_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        &entry_state,
        &assumptions,
        false,
    ) else {
        return Err("the counted population facts cannot be evaluated".to_string());
    };
    assumptions = assumptions_with_propositions(&assumptions, &population_facts);
    let Some(entry_resources) = expand_all_composite_resource_facts(
        entry_state.resources(),
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    ) else {
        return Err("the entry resource context cannot be expanded".to_string());
    };
    let Ok(resource_facts) = entry_resources.observable_facts(&assumptions) else {
        return Err("the entry resource context is not observable".to_string());
    };
    entry_state.resources = entry_resources.clone();
    let execution_facts = path.execution_facts();
    let assumptions = assumptions_with_propositions(&assumptions, &resource_facts);
    // A verification condition may be local to one symbolic path. Branch
    // guards and independently certified callee postconditions are evidence
    // on that path, just as assumable definedness obligations are; omitting
    // them here incorrectly rejects safe guarded calls after certification.
    // Non-assumable obligations are deliberately excluded by
    // `assumptions_with_path_context`, so this cannot prove a verification
    // condition by assuming the condition itself.
    let assumptions =
        assumptions_with_path_context(&assumptions, &execution_facts, path.obligations());
    let effect_facts = path.effect_facts.clone();
    if matches!(outcome, CFunctionOutcome::VerificationDiverges) {
        if let Some(obligation) = path.obligations().iter().find(|obligation| {
            !certification_proves_proposition(&assumptions, obligation.proposition())
                && !loadable_covered_by_fact(&assumptions, obligation.proposition())
                && !forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
        }) {
            return Err(format!(
                "the divergent verification path has an unproved condition: {:?} ({})",
                obligation.proposition(),
                obligation.context().unwrap_or("no context")
            ));
        }
        return Ok(CertifiedFunctionClaimPath {
            caller_state: caller_state.clone(),
            arguments: arguments.to_vec(),
            outcome: outcome.clone(),
            return_state: None,
            entry_state,
            required_resources,
            entry_resources,
            post_state: None,
            post_resources: None,
            assumptions,
            execution_facts,
            effect_facts,
        });
    }
    let CFunctionOutcome::Return {
        value,
        state: return_state,
    } = outcome
    else {
        return Err(format!("the certified path is not safe: {outcome:?}"));
    };
    let Some(post_resources) = expand_all_composite_resource_facts(
        return_state.resources(),
        function.composite_resource_definitions(),
        return_state.memory(),
        &assumptions,
    ) else {
        return Err("the returned resource context cannot be expanded".to_string());
    };
    let Ok(post_resource_facts) = post_resources.observable_facts(&assumptions) else {
        return Err("the returned resource context is not observable".to_string());
    };
    let mut assumptions = assumptions_with_propositions(&assumptions, &post_resource_facts);
    let mut post_state = entry_state
        .clone()
        .with_memory(return_state.memory().clone());
    post_state.resources = post_resources.clone();
    post_state.counted_populations = return_state.counted_populations.clone();
    if function.return_type() != CType::Void {
        post_state
            .locals
            .set_typed("result".to_string(), value.clone(), function.return_type());
    }
    // A named predicate returned by a verified call is an opaque certified
    // execution fact. Reconstruct its registered body at the enclosing
    // function's exact post-state so other postconditions can use the
    // definition without trusting a surface-supplied expansion.
    for unfolding in function.predicate_unfoldings() {
        let Some((predicate, predicate_obligations, body, body_obligations)) =
            instantiate_contract_predicate_unfolding_with_obligations(
                &post_state,
                unfolding,
                &assumptions,
                &mut budget,
            )
        else {
            continue;
        };
        let obligations_hold =
            predicate_obligations
                .iter()
                .chain(&body_obligations)
                .all(|obligation| {
                    certification_proves_proposition(&assumptions, obligation)
                        || contract_endpoints_certify_loadability(
                            &entry_state,
                            &entry_resources,
                            &post_state,
                            &post_resources,
                            obligation,
                            &assumptions,
                        )
                        || loadable_covered_by_fact(&assumptions, obligation)
                        || forall_loadable_covered_by_fact(&assumptions, obligation)
                });
        let predicate_holds = certification_proves_proposition(&assumptions, &predicate);
        if obligations_hold && predicate_holds {
            assumptions = assumptions.assume_proposition(body);
        }
    }
    if let Some(obligation) = path.obligations().iter().find(|obligation| {
        let proved = certification_proves_proposition(&assumptions, obligation.proposition())
            || loadable_covered_by_fact(&assumptions, obligation.proposition())
            || forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
            || contract_endpoints_certify_loadability(
                &entry_state,
                &entry_resources,
                &post_state,
                &post_resources,
                obligation.proposition(),
                &assumptions,
            );
        !proved
    }) {
        return Err(format!(
            "the execution path has an unproved verification condition: {:?} ({})",
            obligation.proposition(),
            obligation.context().unwrap_or("no context")
        ));
    }

    Ok(CertifiedFunctionClaimPath {
        caller_state: caller_state.clone(),
        arguments: arguments.to_vec(),
        outcome: outcome.clone(),
        return_state: Some(return_state.clone()),
        entry_state,
        required_resources,
        entry_resources,
        post_state: Some(post_state),
        post_resources: Some(post_resources),
        assumptions,
        execution_facts,
        effect_facts,
    })
}

fn function_claim_holds_on_prepared_path(
    function: &CFunction,
    claim: &CFunctionContractClaim,
    path: &CertifiedFunctionClaimPath,
    checked_propositions: &BTreeMap<Proposition, Vec<&CCheckedFunctionProposition>>,
) -> bool {
    let CertifiedFunctionClaimPath {
        caller_state,
        arguments,
        outcome,
        return_state,
        entry_state,
        required_resources,
        entry_resources,
        post_state,
        post_resources,
        assumptions,
        execution_facts,
        effect_facts,
    } = path;
    let mut budget = ExecutionBudget::default();
    match claim.target() {
        CFunctionContractClaimTarget::BodySafety => true,
        CFunctionContractClaimTarget::EnsureProposition(index) => {
            let (Some(return_state), Some(post_state), Some(post_resources)) =
                (return_state, post_state, post_resources)
            else {
                return true;
            };
            let Some(ensure) = function.contract_ensures().get(*index) else {
                return false;
            };
            // A surface predicate ensure is stored operationally as its
            // expanded body, plus an exact registered opaque identity. If
            // that identity is already certified at this post-state, it is
            // the kernel authority for the named predicate claim itself.
            // This path deliberately applies only to the exact registered
            // body; arbitrary proposition ensures continue through ordinary
            // lowering and loadability checks below.
            let registered_predicate_ensure_holds = function
                .predicate_unfoldings()
                .iter()
                .filter(|unfolding| unfolding.body() == ensure)
                .any(|unfolding| {
                    let Some((predicate, predicate_obligations, _, _)) =
                        instantiate_contract_predicate_unfolding_with_obligations(
                            post_state,
                            unfolding,
                            assumptions,
                            &mut budget,
                        )
                    else {
                        return false;
                    };
                    predicate_obligations.iter().all(|obligation| {
                        certification_proves_proposition(assumptions, obligation)
                            || contract_endpoints_certify_loadability(
                                entry_state,
                                entry_resources,
                                post_state,
                                post_resources,
                                obligation,
                                assumptions,
                            )
                    }) && certification_proves_proposition(assumptions, &predicate)
                });
            if registered_predicate_ensure_holds {
                return true;
            }
            // Lowering records the ensure's load obligations instead of
            // searching the whole path context for each one as it goes; they
            // are discharged below, resources and exact facts first. The
            // general prover is the last resort because on a sealed path,
            // whose facts include every loadability the proof established at
            // intermediate memories, its quantified and disjunctive search is
            // the dominant certification cost.
            let lowering_assumptions = assumptions
                .clone()
                .allow_symbolic_contract_loads()
                .defer_non_exact_loadability_obligations();
            // A completed proposition from the proof spells a quantified
            // ensure under the binders the proof lowered it with, and every
            // load minted under a binder carries that binder's identity.
            // Lower the ensure under the binders the proof's completions
            // name, so the lowering can match a completion instead of being
            // proved again; the ensure's own binders remain the fallback.
            let lowered = crate::instrumentation::measure_operation(
                function.name(),
                "contract claim",
                "ensure lowering",
                || {
                    lower_ensure_under_completion_binders(
                        post_state,
                        ensure,
                        entry_state,
                        &lowering_assumptions,
                        &mut budget,
                        checked_propositions,
                    )
                },
            );
            let Ok(paths) = lowered else {
                return false;
            };
            !paths.is_empty()
                && paths.into_iter().all(|path| {
                    let obligations_hold = crate::instrumentation::measure_operation(
                        function.name(),
                        "contract claim",
                        "obligation discharge",
                        || {
                            path.obligations.iter().all(|obligation| {
                                contract_endpoints_certify_loadability(
                                    entry_state,
                                    entry_resources,
                                    post_state,
                                    post_resources,
                                    obligation.proposition(),
                                    assumptions,
                                ) || loadable_covered_by_fact(assumptions, obligation.proposition())
                                    || forall_loadable_covered_by_fact(
                                        assumptions,
                                        obligation.proposition(),
                                    )
                                    || certification_proves_exists_obligation_from_facts(
                                        assumptions,
                                        obligation.proposition(),
                                    )
                                    || certification_proves_proposition(
                                        assumptions,
                                        obligation.proposition(),
                                    )
                            })
                        },
                    );
                    let mut path_propositions = path
                        .facts
                        .iter()
                        .map(|fact| fact.proposition().clone())
                        .collect::<Vec<_>>();
                    let assumption_facts =
                        assumptions.prop_facts.iter().cloned().collect::<Vec<_>>();
                    path_propositions.extend(finite_forall_instantiations(&assumption_facts));
                    path_propositions
                        .extend(finite_forall_instantiations(&path_propositions.clone()));
                    let path_assumptions =
                        assumptions_with_propositions(assumptions, &path_propositions);
                    let proposition_holds =
                        crate::instrumentation::measure_operation(
                            function.name(),
                            "contract claim",
                            "completion match",
                            || {
                                checked_propositions
                                    .get(&path.proposition)
                                    .into_iter()
                                    .flatten()
                                    .any(|proof| {
                                        // Cheapest checks first: a completion from another
                                        // path or function is rejected before any proving.
                                        if proof.function != *function
                                            || proof.specification.state() != caller_state
                                            || proof.specification.arguments() != arguments
                                            || !c_function_outcomes_definitionally_equal(
                                                function,
                                                proof.specification.outcome(),
                                                outcome,
                                                assumptions,
                                            )
                                        {
                                            return false;
                                        }
                                        let requirements_match =
                                proof.specification.requires().iter().all(|requirement| {
                                    let ok = assumptions.proves(requirement) || match requirement {
                                        Proposition::CResourceComposition(required) => {
                                            resource_context_definitionally_contains(
                                                required_resources,
                                                required,
                                                function.composite_resource_definitions(),
                                                entry_state.memory(),
                                                assumptions,
                                            )
                                        }
                                        Proposition::Predicate { .. } => function
                                            .predicate_unfoldings()
                                            .iter()
                                            .any(|unfolding| {
                                                let mut budget = ExecutionBudget::default();
                                                let Some((
                                        predicate,
                                        predicate_obligations,
                                        body,
                                        body_obligations,
                                    )) = instantiate_contract_predicate_unfolding_with_obligations(
                                        entry_state,
                                        unfolding,
                                        assumptions,
                                        &mut budget,
                                    )
                                    else {
                                        return false;
                                    };
                                                predicate == *requirement
                                                    && predicate_obligations
                                                        .iter()
                                                        .chain(&body_obligations)
                                                        .all(|obligation| {
                                                            certification_proves_proposition(
                                                                assumptions,
                                                                obligation,
                                                            )
                                                        })
                                                    && certification_proves_proposition(
                                                        assumptions,
                                                        &body,
                                                    )
                                            }),
                                        _ => certification_proves_proposition(
                                            assumptions,
                                            requirement,
                                        ),
                                    };
                                    ok
                                });
                                        requirements_match
                                    })
                            },
                        ) || crate::instrumentation::measure_operation(
                            function.name(),
                            "contract claim",
                            "post proposition proof",
                            || {
                                certification_proves_post_proposition(
                                    &path_assumptions,
                                    &path.proposition,
                                    return_state.memory(),
                                    execution_facts,
                                )
                            },
                        );
                    obligations_hold && proposition_holds
                })
        }
        CFunctionContractClaimTarget::EnsureResource(index) => {
            let (Some(return_state), Some(post_state)) = (return_state, post_state) else {
                return true;
            };
            if *index >= function.resource_ensures().len() {
                return false;
            }
            // Resource clauses describe one jointly returned context. Checking
            // each clause independently would let one resource unit certify two
            // identical clauses. The prefix makes every claim account for all
            // units claimed up to and including its own clause.
            let resources = &function.resource_ensures()[..=*index];
            let Ok(Ok(expected)) =
                evaluate_function_resource_context(post_state, resources, assumptions, &mut budget)
            else {
                return false;
            };
            expected.facts().iter().all(|fact| {
                resource_context_satisfies_definitional_fact(
                    return_state.resources(),
                    fact,
                    function.composite_resource_definitions(),
                    return_state.memory(),
                    assumptions,
                )
            })
        }
        CFunctionContractClaimTarget::Effect => {
            let mut mutable_ranges = Vec::new();
            for segment in function.contract_mutable() {
                if segment.guard().is_some_and(|guard| {
                    evaluate_guarded_contract_condition(
                        guard,
                        entry_state,
                        assumptions,
                        &mut budget,
                    ) == Some(false)
                }) {
                    continue;
                }
                let Ok(Ok(segment)) =
                    evaluate_loop_effect_segment(entry_state, segment, assumptions, &mut budget)
                else {
                    return false;
                };
                mutable_ranges.push(CMemoryRange::new(segment.base, segment.start, segment.end));
            }
            let mut effect_memory = caller_state.memory().clone();
            let mut seen_transitions = Vec::<(CMemory, CMemory)>::new();
            let is_function_fresh_heap_pointer = |pointer: &Pointer, current: &CMemory| {
                let matches_allocation = |memory: &CMemory| {
                    memory.heap.live_allocations.keys().any(|base| {
                        base == pointer
                            || crate::kernel::assumptions::pointers_equal_ignoring_memories(
                                base, pointer,
                            )
                            || pointers_proven_equal_for_memory_resolution(
                                base,
                                pointer,
                                assumptions,
                            )
                    })
                };
                !matches_allocation(entry_state.memory())
                    && (matches!(pointer.block, PointerBlock::Heap(_))
                        || matches_allocation(current))
            };
            let effects_are_bounded = effect_facts.iter().all(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly {
                    before,
                    after,
                    pointers,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    pointers
                        .iter()
                        .filter(|pointer| !pointer.block.starts_with("local:"))
                        .all(|pointer| {
                            is_function_fresh_heap_pointer(pointer, before)
                                || mutable_ranges.iter().any(|range| {
                                    assumptions.pointer_access_in_range(
                                        pointer,
                                        4,
                                        range.base(),
                                        range.start(),
                                        range.end(),
                                    )
                                })
                        })
                }
                Proposition::CMemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges: nested_ranges,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    nested_ranges.iter().all(|nested| {
                        is_function_fresh_heap_pointer(nested.base(), before)
                            || mutable_ranges
                                .iter()
                                .any(|allowed| memory_range_covers(allowed, nested, assumptions))
                    })
                }
                Proposition::CHeapAllocationFreed {
                    before,
                    after,
                    allocation_base,
                    bytes,
                } => {
                    let repeats_transition =
                        seen_transitions.iter().any(|(seen_before, seen_after)| {
                            c_effect_memories_definitionally_equal(seen_before, before, assumptions)
                                && c_effect_memories_definitionally_equal(
                                    seen_after,
                                    after,
                                    assumptions,
                                )
                        });
                    if !repeats_transition
                        && !c_effect_memories_definitionally_equal(
                            &effect_memory,
                            before,
                            assumptions,
                        )
                        && !c_effect_memory_advances_over_internal_heap_state(
                            &effect_memory,
                            before,
                            entry_state.memory(),
                            assumptions,
                        )
                    {
                        return false;
                    }
                    if !heap_free_effect_is_valid(before, after, allocation_base, bytes) {
                        return false;
                    }
                    if !repeats_transition {
                        effect_memory = after.clone();
                        seen_transitions.push((before.clone(), after.clone()));
                    }
                    true
                }
                _ => true,
            });
            let endpoint_matches = return_state.as_ref().is_none_or(|return_state| {
                c_effect_memories_definitionally_equal(
                    &effect_memory,
                    return_state.memory(),
                    assumptions,
                ) || c_effect_memory_advances_over_internal_heap_state(
                    &effect_memory,
                    return_state.memory(),
                    entry_state.memory(),
                    assumptions,
                )
            });
            effects_are_bounded && endpoint_matches
        }
    }
}

pub(in crate::kernel) fn c_effect_memories_definitionally_equal(
    left: &CMemory,
    right: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let without_locals = |memory: &CMemory| {
        let mut external = memory.clone();
        std::sync::Arc::make_mut(&mut external.blocks)
            .retain(|block, _| !block.starts_with("local:"));
        std::sync::Arc::make_mut(&mut external.cells)
            .retain(|pointer, _| !pointer.block.starts_with("local:"));
        external
    };
    let left = without_locals(left);
    let right = without_locals(right);
    left.heap == right.heap && c_memories_definitionally_equal(&left, &right, assumptions)
}

/// Accepts internal heap bookkeeping between externally visible effects:
/// newly allocated trusted blocks and the registration of an already-owned
/// symbolic allocation before direct `free`. Removing only those additions
/// leaves a memory that must still match the preceding endpoint exactly.
pub(in crate::kernel) fn c_effect_memory_advances_over_internal_heap_state(
    before: &CMemory,
    after: &CMemory,
    function_entry: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let fresh_blocks = after
        .blocks
        .keys()
        .filter(|block| {
            matches!(block, PointerBlock::Heap(_))
                && !before.blocks.contains_key(*block)
                && !function_entry.blocks.contains_key(*block)
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let added_allocation_claims = after
        .heap
        .live_allocations
        .keys()
        .filter(|pointer| !before.heap.live_allocations.contains_key(*pointer))
        .cloned()
        .collect::<BTreeSet<_>>();
    if fresh_blocks.is_empty() && added_allocation_claims.is_empty() {
        return false;
    }
    let mut stripped = after.clone();
    std::sync::Arc::make_mut(&mut stripped.blocks).retain(|block, _| !fresh_blocks.contains(block));
    std::sync::Arc::make_mut(&mut stripped.cells)
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .live_allocations
        .retain(|pointer, _| {
            !fresh_blocks.contains(&pointer.block) && !added_allocation_claims.contains(pointer)
        });
    std::sync::Arc::make_mut(&mut stripped.heap)
        .deallocated_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .pending_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .uninitialized_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.block));
    c_effect_memories_definitionally_equal(before, &stripped, assumptions)
}

fn heap_free_effect_is_valid(
    before: &CMemory,
    after: &CMemory,
    allocation_base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    let Some(live) = (if before.live_heap_block_size(allocation_base).is_some() {
        Some(before.clone())
    } else {
        before
            .clone()
            .with_heap_allocation_claim(allocation_base.clone(), bytes.clone())
    }) else {
        return false;
    };
    live.live_heap_block_size(allocation_base) == Some(bytes)
        && live
            .free_heap_block(allocation_base)
            .is_ok_and(|expected| expected == *after)
}

/// Certifies every exact contract claim in one pass over a kernel-produced,
/// complete execution frontier.
///
/// Path validity, resource expansion, and verification conditions are checked
/// once per path and then shared by the individual claim checks.
pub fn c_verified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Option<Vec<CVerifiedFunctionContractClaim>> {
    c_verified_function_contract_claims_with_checked_propositions(function, contract_execution, &[])
}

fn checked_proposition_index(
    checked_propositions: &[CCheckedFunctionProposition],
) -> BTreeMap<Proposition, Vec<&CCheckedFunctionProposition>> {
    let mut index = BTreeMap::new();
    for checked in checked_propositions {
        index
            .entry(checked.proposition.clone())
            .or_insert_with(Vec::new)
            .push(checked);
    }
    index
}

/// Certifies contract claims while reusing proposition judgments already
/// closed by the kernel proof object. Finalization still reconstructs the
/// exact function paths and checks resources, effects, obligations, and claim
/// coverage; it does not re-prove a matching proposition claim.
pub(crate) fn c_verified_function_contract_claims_with_checked_propositions(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
    checked_propositions: &[CCheckedFunctionProposition],
) -> Option<Vec<CVerifiedFunctionContractClaim>> {
    let execution = &contract_execution.execution;
    if execution.limit().is_some() || execution.paths().is_empty() {
        return None;
    }
    let timings = crate::instrumentation::enabled();
    let prepare_started = std::time::Instant::now();
    let paths = crate::instrumentation::measure_operation(
        function.name(),
        "contract certification",
        "contract path preparation",
        || {
            execution
                .paths()
                .iter()
                .map(|path| prepare_function_claim_path(function, path))
                .collect::<Result<Vec<_>, _>>()
        },
    )
    .ok()?;
    if timings {
        crate::instrumentation::emit(
            crate::instrumentation::VerificationEvent::ClaimPathsPrepared {
                function: function.name().to_string(),
                count: paths.len(),
                elapsed: prepare_started.elapsed(),
            },
        );
    }
    let checked_propositions = checked_proposition_index(checked_propositions);
    function
        .contract_claims()
        .iter()
        .map(|claim| {
            let claim_started = std::time::Instant::now();
            let operation_name = match claim.target() {
                CFunctionContractClaimTarget::BodySafety => "contract claim: body safety",
                CFunctionContractClaimTarget::EnsureProposition(_) => "contract claim: proposition",
                CFunctionContractClaimTarget::EnsureResource(_) => "contract claim: resource",
                CFunctionContractClaimTarget::Effect => "contract claim: effect",
            };
            let claim_key = format!("{:?}", claim.key());
            let holds = crate::instrumentation::measure_operation(
                function.name(),
                &claim_key,
                operation_name,
                || {
                    paths.iter().all(|path| {
                        function_claim_holds_on_prepared_path(
                            function,
                            claim,
                            path,
                            &checked_propositions,
                        )
                    })
                },
            );
            if timings {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::ClaimFinished {
                        function: function.name().to_string(),
                        key: format!("{:?}", claim.key()),
                        elapsed: claim_started.elapsed(),
                    },
                );
            }
            holds.then(|| CVerifiedFunctionContractClaim {
                function: function.clone(),
                key: claim.key().clone(),
            })
        })
        .collect()
}

/// Reports the exact contract claims that the checked execution frontier does
/// not establish. This is diagnostic information only: unlike the companion
/// certification API, it cannot mint proof objects.
///
/// `None` means the frontier itself is incomplete or could not be prepared for
/// claim checking. An empty vector means every claim holds.
pub fn c_unverified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Result<Vec<CFunctionContractClaimKey>, String> {
    c_unverified_function_contract_claims_with_checked_propositions(
        function,
        contract_execution,
        &[],
    )
}

/// Diagnostic counterpart to checked-proposition-aware finalization. Keeping
/// the same evidence here ensures a later failing claim does not make an
/// already checked proposition look unproved in the reported claim list.
pub(crate) fn c_unverified_function_contract_claims_with_checked_propositions(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
    checked_propositions: &[CCheckedFunctionProposition],
) -> Result<Vec<CFunctionContractClaimKey>, String> {
    let execution = &contract_execution.execution;
    if let Some(limit) = execution.limit() {
        return Err(format!("symbolic execution reached its {limit:?} limit"));
    }
    if execution.paths().is_empty() {
        return Err("symbolic execution produced no paths".to_string());
    }
    let paths = execution
        .paths()
        .iter()
        .enumerate()
        .map(|(index, path)| {
            prepare_function_claim_path(function, path)
                .map_err(|reason| format!("execution path {index} is invalid: {reason}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let checked_propositions = checked_proposition_index(checked_propositions);
    Ok(function
        .contract_claims()
        .iter()
        .filter(|claim| {
            !paths.iter().all(|path| {
                function_claim_holds_on_prepared_path(function, claim, path, &checked_propositions)
            })
        })
        .map(|claim| claim.key().clone())
        .collect())
}

/// Certifies one contract claim only after a kernel-produced complete
/// execution frontier establishes that exact claim for the exact function.
pub fn c_verified_function_contract_claim(
    function: &CFunction,
    key: CFunctionContractClaimKey,
    execution: &CFunctionContractExecution,
) -> Option<CVerifiedFunctionContractClaim> {
    c_verified_function_contract_claims(function, execution)?
        .into_iter()
        .find(|proof| proof.key == key)
}

/// Packages an opaque rule only after every recorded contract claim has a
/// certificate for this exact function.
pub fn c_verified_function_rule(
    function: CFunction,
    proofs: &[CVerifiedFunctionContractClaim],
) -> Option<CVerifiedFunctionRule> {
    if !function.opaque_contract_supported()
        || function.contract_claims().is_empty()
        || proofs.iter().any(|proof| proof.function != function)
        || function
            .contract_claims()
            .iter()
            .any(|claim| !proofs.iter().any(|proof| proof.key == *claim.key()))
    {
        return None;
    }
    Some(CVerifiedFunctionRule { function })
}

/// Builds an untrusted ranking plan. Supplying a plan is not evidence; the
/// kernel validates it together with the exact verified C functions in
/// [`c_verified_function_termination_rules`].
pub fn c_function_termination_plan(
    function_name: impl Into<String>,
    recursive_measure: Option<CFunctionTerminationMeasure>,
    loop_measures: impl IntoIterator<Item = (usize, String)>,
) -> CFunctionTerminationPlan {
    CFunctionTerminationPlan {
        function_name: function_name.into(),
        recursive_measure,
        loop_measures: loop_measures.into_iter().collect(),
    }
}

/// Creates a scoped hypothesis used only while the language layer verifies one
/// closed set of mutually dependent C contracts. The verification transaction
/// returns no rules if any hypothesized contract fails independent kernel
/// certification, which is the standard partial-correctness recursion rule.
///
/// This is crate-private so an external caller cannot install an unverified
/// recursive contract into a kernel execution environment.
pub(crate) fn c_recursive_function_contract_hypothesis(
    function: CFunction,
) -> Option<CVerifiedFunctionRule> {
    (function.opaque_contract_supported() && !function.contract_claims().is_empty())
        .then_some(CVerifiedFunctionRule { function })
}
