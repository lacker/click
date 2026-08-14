use super::*;

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
/// resource representation to a separate kernel certificate.
///
/// Proof replay uses this only to select the independently reproduced path;
/// [`certify_c_function_execution_path_resource_representation`] remains the
/// authority that accepts the selected path's resources.
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

fn owned_composite_resource_names(resources: &ResourceContext) -> Vec<&str> {
    let mut names = resources
        .facts()
        .iter()
        .filter_map(|fact| match fact {
            CResourceFact::Own(CResource::Composite { name, .. }, _) => Some(name.as_str()),
            CResourceFact::Own(CResource::Memory(_) | CResource::Token { .. }, _)
            | CResourceFact::View(_) => None,
        })
        .collect::<Vec<_>>();
    names.sort_unstable();
    names.dedup();
    names
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
            } if pointer.block.starts_with("local:")
                || store_is_self_materialization(base, pointer, value) =>
            {
                Some(base)
            }
            CMemoryDerivation::BlockDeclared { base, block } if block.starts_with("local:") => {
                Some(base)
            }
            CMemoryDerivation::CellsForgotten { base } => Some(base),
            _ => None,
        }
    }
    /// A store whose value is the base memory's own load at the stored
    /// pointer is a no-op: the produced memory denotes the same state as its
    /// base, differing only in which cells are materialized. Proof replay
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
            }),
            Some(CMemoryDerivation::Store {
                base: right_base,
                pointer: right_pointer,
                value: right_value,
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

fn c_memories_definitionally_equal(
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
            (memory.as_ref(), load_pointer.as_ref())
        }
        _ => return false,
    };
    pointers_proven_equal_for_memory_resolution(load.1, pointer, assumptions)
        && c_memory_load_is_unchanged(load.0, symbolic_memory, pointer, assumptions)
}

/// Changes only the bounded symbolic representation of a certified return path.
///
/// Program values and memory must be definitionally equal using the path's
/// facts plus kernel-certified facts from the desired replay. Uncertified
/// replay facts are deliberately excluded. The old and new resource contexts
/// must mutually satisfy every fact under those same assumptions.
pub fn certify_c_function_execution_path_resource_representation(
    path: &SymbolicCExecutionPath,
    desired_outcome: CFunctionOutcome,
    desired_facts: &[ExecutionPureFact],
) -> Option<SymbolicCExecutionPath> {
    #[derive(Clone)]
    struct CachedRepresentationCertificate {
        path: SymbolicCExecutionPath,
        desired_outcome: CFunctionOutcome,
        desired_facts: Vec<ExecutionPureFact>,
        certified: SymbolicCExecutionPath,
    }
    thread_local! {
        static CACHE: std::cell::RefCell<Vec<CachedRepresentationCertificate>> =
            const { std::cell::RefCell::new(Vec::new()) };
    }
    if let Some(certified) = CACHE.with(|cache| {
        cache
            .borrow()
            .iter()
            .rev()
            .find(|entry| {
                entry.path == *path
                    && entry.desired_outcome == desired_outcome
                    && entry.desired_facts == desired_facts
            })
            .map(|entry| entry.certified.clone())
    }) {
        return Some(certified);
    }
    let cache_path = path.clone();
    let cache_outcome = desired_outcome.clone();
    let cache_facts = desired_facts.to_vec();
    let certified = certify_c_function_execution_path_resource_representation_uncached(
        path,
        desired_outcome,
        desired_facts,
    )?;
    CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 64 {
            cache.remove(0);
        }
        cache.push(CachedRepresentationCertificate {
            path: cache_path,
            desired_outcome: cache_outcome,
            desired_facts: cache_facts,
            certified: certified.clone(),
        });
    });
    Some(certified)
}

fn certify_c_function_execution_path_resource_representation_uncached(
    path: &SymbolicCExecutionPath,
    desired_outcome: CFunctionOutcome,
    desired_facts: &[ExecutionPureFact],
) -> Option<SymbolicCExecutionPath> {
    let mut proposition = path.theorem().proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proposition {
        premises.push(premise.as_ref().clone());
        proposition = body;
    }
    let (state, function, arguments, outcome, verifies) = match proposition {
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, false),
        Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, true),
        _ => return None,
    };
    let (
        CFunctionOutcome::Return {
            value,
            state: return_state,
        },
        CFunctionOutcome::Return {
            value: desired_value,
            state: desired_state,
        },
    ) = (outcome, &desired_outcome)
    else {
        return (outcome == &desired_outcome).then(|| path.clone());
    };
    premises.extend(
        path.execution_facts()
            .iter()
            .map(|fact| fact.proposition().clone()),
    );
    premises.extend(
        desired_facts
            .iter()
            .filter(|fact| fact.is_certified())
            .map(|fact| fact.proposition().clone()),
    );
    // A conditional call ensure whose antecedent this path establishes is
    // direct reconciliation evidence: discharge each implication premise once
    // (walking chained implications) and add the reached consequents. Work is
    // linear in the premise list times implication depth; antecedents are
    // decided against the same premises, never searched project-wide.
    let discharge_context = assumptions_with_propositions(&path.assumptions, &premises);
    let mut discharged = Vec::new();
    for premise in &premises {
        let mut current = premise;
        while let Proposition::Implies(antecedent, consequent) = current {
            if !discharge_context.proves(antecedent.as_ref()) {
                break;
            }
            discharged.push(consequent.as_ref().clone());
            current = consequent;
        }
    }
    premises.extend(discharged);
    let preliminary_assumptions = assumptions_with_propositions(&path.assumptions, &premises);
    let observable_resource_facts = return_state
        .resources()
        .observable_facts(&preliminary_assumptions)
        .ok()?;
    premises.extend(observable_resource_facts);
    let assumptions = assumptions_with_propositions(&path.assumptions, &premises);
    let _assumptions_memo_scope =
        crate::kernel::assumptions::PureFactContextIdScope::enter(&assumptions);
    let values_equal = crate::instrumentation::measure_operation(
        function.name(),
        "resource representation",
        "resource representation: values",
        || {
            c_values_proven_equal_for_memory_resolution(value, desired_value, &assumptions)
                || return_values_equal_by_certified_stores(
                    value,
                    return_state.memory(),
                    &path.execution_facts(),
                    desired_value,
                    &assumptions,
                )
                || return_values_equal_by_certified_stores(
                    value,
                    desired_state.memory(),
                    desired_facts,
                    desired_value,
                    &assumptions,
                )
        },
    );
    let memories_equal = crate::instrumentation::measure_operation(
        function.name(),
        "resource representation",
        "resource representation: memory",
        || {
            let definitional = crate::instrumentation::measure_operation(
                function.name(),
                "resource representation",
                "resource representation: memory definitional",
                || {
                    c_memories_definitionally_equal(
                        return_state.memory(),
                        desired_state.memory(),
                        &assumptions,
                    )
                },
            );
            definitional || {
                // Execution provenance couples deterministic store chains and two
                // alpha-renamed encodings of the same bounded call havoc.
                crate::instrumentation::measure_operation(
                    function.name(),
                    "resource representation",
                    "resource representation: memory provenance",
                    || {
                        memories_equal_by_execution_provenance(
                            return_state.memory(),
                            &path.execution_facts(),
                            desired_state.memory(),
                            desired_facts,
                            &assumptions,
                        )
                    },
                )
            }
        },
    );
    if !values_equal || !memories_equal {
        return None;
    }
    let folded_names_differ = owned_composite_resource_names(return_state.resources())
        != owned_composite_resource_names(desired_state.resources());
    let resources_equal = crate::instrumentation::measure_operation(
        function.name(),
        "resource representation",
        "resource representation: resources",
        || {
            crate::instrumentation::measure_operation(
                function.name(),
                "resource representation",
                "resource representation: contains desired",
                || {
                    resource_context_definitionally_contains(
                        return_state.resources(),
                        desired_state.resources(),
                        function.composite_resource_definitions(),
                        return_state.memory(),
                        &assumptions,
                    )
                },
            ) || (folded_names_differ
                && crate::instrumentation::measure_operation(
                    function.name(),
                    "resource representation",
                    "resource representation: contains without residue",
                    || {
                        resource_context_definitionally_contains_without_owned_residue(
                            desired_state.resources(),
                            return_state.resources(),
                            function.composite_resource_definitions(),
                            desired_state.memory(),
                            &assumptions,
                        )
                    },
                ))
                || crate::instrumentation::measure_operation(
                    function.name(),
                    "resource representation",
                    "resource representation: equal contexts",
                    || {
                        resource_contexts_definitionally_equal(
                            function,
                            return_state.memory(),
                            return_state.resources(),
                            desired_state.memory(),
                            desired_state.resources(),
                            &assumptions,
                        )
                    },
                )
        },
    );
    if !resources_equal {
        return None;
    }

    let conclusion = if verifies {
        Proposition::CFunctionVerifies {
            state: state.clone(),
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: desired_outcome,
        }
    } else {
        Proposition::CFunctionExecutes {
            state: state.clone(),
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: desired_outcome,
        }
    };
    let theorem = Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    );
    Some(SymbolicCExecutionPath {
        assumptions: path.assumptions.clone(),
        facts: path.facts.clone(),
        effect_facts: path.effect_facts.clone(),
        obligations: path.obligations.clone(),
        theorem,
    })
}

struct CertifiedFunctionClaimPath {
    caller_state: CState,
    return_state: Option<CState>,
    entry_state: CState,
    entry_resources: ResourceContext,
    post_state: Option<CState>,
    post_resources: Option<ResourceContext>,
    assumptions: PureFactContext,
    execution_facts: Vec<ExecutionPureFact>,
    effect_facts: Vec<ExecutionPureFact>,
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
            return_state: None,
            entry_state,
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
    let assumptions = assumptions_with_propositions(&assumptions, &post_resource_facts);
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
        return_state: Some(return_state.clone()),
        entry_state,
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
) -> bool {
    let CertifiedFunctionClaimPath {
        caller_state,
        return_state,
        entry_state,
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
            let lowering_assumptions = assumptions.clone().allow_symbolic_contract_loads();
            let Ok(paths) = lower_spec_proposition_at_state_with_loop_entry(
                post_state,
                ensure,
                Some(entry_state),
                &lowering_assumptions,
                &mut budget,
            ) else {
                return false;
            };
            !paths.is_empty()
                && paths.into_iter().all(|path| {
                    let obligations_hold = path.obligations.iter().all(|obligation| {
                        certification_proves_proposition(assumptions, obligation.proposition())
                            || contract_endpoints_certify_loadability(
                                entry_state,
                                entry_resources,
                                post_state,
                                post_resources,
                                obligation.proposition(),
                                assumptions,
                            )
                            || loadable_covered_by_fact(assumptions, obligation.proposition())
                            || forall_loadable_covered_by_fact(
                                assumptions,
                                obligation.proposition(),
                            )
                            || certification_proves_exists_obligation_from_facts(
                                assumptions,
                                obligation.proposition(),
                            )
                    });
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
                    let proposition_holds = certification_proves_post_proposition(
                        &path_assumptions,
                        &path.proposition,
                        return_state.memory(),
                        execution_facts,
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
                Proposition::CHeapLifetimeRetired {
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
                    if !heap_retirement_effect_is_valid(before, after, allocation_base, bytes) {
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
        .retired_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .pending_allocations
        .retain(|pointer, _| !fresh_blocks.contains(&pointer.block));
    std::sync::Arc::make_mut(&mut stripped.heap)
        .uninitialized_allocations
        .retain(|pointer| !fresh_blocks.contains(&pointer.block));
    c_effect_memories_definitionally_equal(before, &stripped, assumptions)
}

fn heap_retirement_effect_is_valid(
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
                    paths
                        .iter()
                        .all(|path| function_claim_holds_on_prepared_path(function, claim, path))
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
    Ok(function
        .contract_claims()
        .iter()
        .filter(|claim| {
            !paths
                .iter()
                .all(|path| function_claim_holds_on_prepared_path(function, claim, path))
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
