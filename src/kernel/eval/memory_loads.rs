use super::*;

#[derive(Default)]
struct MemoryLoadAliasCache {
    resolution_equal: BTreeMap<(u64, Pointer), bool>,
    resolution_distinct: BTreeMap<(u64, Pointer), bool>,
    equal: BTreeMap<(u64, Pointer), bool>,
    distinct: BTreeMap<(u64, Pointer), bool>,
}

impl MemoryLoadAliasCache {
    fn resolution_equal(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .resolution_equal
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_equal_for_memory_resolution(pointer, stored_pointer, assumptions)
            })
    }

    fn resolution_distinct(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .resolution_distinct
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| {
                pointers_proven_distinct_for_memory_resolution(pointer, stored_pointer, assumptions)
            })
    }

    fn equal(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .equal
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| pointers_proven_equal(pointer, stored_pointer, assumptions))
    }

    fn distinct(
        &mut self,
        pointer: &Pointer,
        stored_pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> bool {
        *self
            .distinct
            .entry((assumptions.memo_fingerprint(), stored_pointer.clone()))
            .or_insert_with(|| pointers_proven_distinct(pointer, stored_pointer, assumptions))
    }
}

pub(in crate::kernel) fn evaluate_c_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
) -> Vec<CExpressionPath> {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    let mut alias_cache = MemoryLoadAliasCache::default();
    evaluate_c_memory_load_paths_with_alias_cache(
        memory,
        pointer,
        value_type,
        facts,
        obligations,
        assumptions,
        has_external_read_resource,
        &mut alias_cache,
    )
}

#[allow(clippy::too_many_arguments)]
fn evaluate_c_memory_load_paths_with_alias_cache(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: Vec<ExecutionPureFact>,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    alias_cache: &mut MemoryLoadAliasCache,
) -> Vec<CExpressionPath> {
    let mut facts = facts;
    let mut load_assumptions = assumptions.clone();
    let candidates = assumptions
        .should_transport_memory_load_condition_facts()
        .then(|| {
            assumptions
                .exact_memory_load_condition_candidates(&pointer)
                .map(|(condition, value)| Proposition::ConditionIs(condition.clone(), value))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    for source in candidates {
        let Some(theorem) = prove_c_condition_fact_transport(&source, memory, assumptions) else {
            continue;
        };
        let Proposition::Implies(theorem_source, target) = theorem.proposition() else {
            continue;
        };
        if theorem_source.as_ref() != &source || target.as_ref() == &source {
            continue;
        }
        let target = target.as_ref().clone();
        load_assumptions = load_assumptions.assume_proposition(target.clone());
        let transported = ExecutionPureFact::certified_transport(source, target, theorem);
        if !facts.contains(&transported) {
            facts.push(transported);
        }
    }
    let assumptions = &load_assumptions;
    // Provenance-sensitive lowering asks for the load identity even when this
    // snapshot has already materialized the cell's concrete value. Checking
    // `known_value` first would collapse `at(mark, field == 11)` to `true` and
    // erase the address needed for later frame transport.
    if has_external_read_resource && assumptions.should_force_symbolic_external_loads() {
        let Some(value) = symbolic_load_value(memory, &pointer, value_type) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // A pointer-typed load of a materialized int32 cell that is not a bare
    // load term (for example a call-havoc variable standing for the framed
    // field) cannot be reinterpreted as a stable pointer spelling. When the
    // caller permits symbolic external loads, fall through to the symbolic
    // load below — its load-term spelling relates across snapshots — instead
    // of failing the load.
    let pointer_cell_defers_to_symbolic = |value: &CValue| {
        matches!(value, CValue::Int32(_))
            && matches!(value_type, CType::Int32Pointer | CType::UInt8Pointer)
            && has_external_read_resource
            && assumptions.should_prefer_symbolic_external_loads()
    };
    // An exact materialized cell is already the authoritative value for this
    // pointer. Avoid proving every other symbolic cell distinct before the
    // direct map lookup.
    if let Some(value) = memory.known_value(&pointer) {
        if let Some(value) = symbolic_pointer_value_from_int_cell(&pointer, &value, value_type) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        }
    } else if let Some(value) = memory.cells.iter().find_map(|(stored_pointer, value)| {
        alias_cache
            .resolution_equal(&pointer, stored_pointer, assumptions)
            .then(|| value.clone())
    }) {
        if let Some(value) = symbolic_pointer_value_from_int_cell(&pointer, &value, value_type) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !pointer_cell_defers_to_symbolic(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        }
    }

    // Unlike external argument memory, a fresh heap block has a known
    // initialization history. Permission authorizes a read but cannot turn a
    // never-written heap cell into an unconstrained initialized value.
    if memory.is_uninitialized_heap_address(&pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if memory.is_retired_heap_address(&pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        }];
    }

    if has_external_read_resource && assumptions.should_prefer_symbolic_external_loads() {
        let Some(value) = symbolic_load_value(memory, &pointer, value_type) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let mut memory = memory.clone();
    let reduction_base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&memory));
    let cells_before_reduction = memory.cells.len();
    std::sync::Arc::make_mut(&mut memory.cells).retain(|stored_pointer, _| {
        !alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions)
    });
    // The reduced memory is embedded in the returned symbolic value, so it
    // becomes a snapshot spelling other queries must relate back to its
    // source. Dropping cells provably distinct from the loaded pointer is a
    // no-op for every load, which is exactly the `CellsForgotten` edge;
    // without it the derivation walk dead-ends at this variant.
    if let Some(base) = reduction_base
        && memory.cells.len() != cells_before_reduction
    {
        record_c_memory_derivation(&memory, CMemoryDerivation::CellsForgotten { base });
    }

    if let Some(value) = memory.known_value(&pointer) {
        if let Some(value) = symbolic_pointer_value_from_int_cell(&pointer, &value, value_type) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        }
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if pointer.has_symbolic_block() && has_external_read_resource {
        let Some(value) = symbolic_load_value(&memory, &pointer, value_type) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let unresolved = memory
        .cells
        .iter()
        .find_map(|(stored_pointer, stored_value)| {
            (stored_pointer != &pointer
                && !alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions)
                && !alias_cache.resolution_equal(&pointer, stored_pointer, assumptions)
                && (assumptions.should_defer_non_exact_condition_reasoning()
                    || !alias_cache.distinct(&pointer, stored_pointer, assumptions)
                        && !alias_cache.equal(&pointer, stored_pointer, assumptions)))
            .then(|| (stored_pointer.clone(), stored_value.clone()))
        });
    if let Some((stored_pointer, stored_value)) = unresolved {
        let mut paths = Vec::new();

        let mut equal_facts = facts.clone();
        if add_pointer_offset_equality_execution_pure_facts(
            &mut equal_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            true,
        )
        .is_some()
        {
            let equal_outcome = if let Some(value) =
                symbolic_pointer_value_from_int_cell(&pointer, &stored_value, value_type)
            {
                CExpressionOutcome::Value(value)
            } else if value_type.accepts(&stored_value) {
                CExpressionOutcome::Value(stored_value)
            } else {
                CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            };
            paths.push(CExpressionPath {
                outcome: equal_outcome,
                facts: equal_facts,
                obligations: obligations.clone(),
            });
        }

        let mut distinct_facts = facts;
        if add_pointer_offset_equality_execution_pure_facts(
            &mut distinct_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            false,
        )
        .is_some()
        {
            paths.extend(evaluate_c_memory_load_paths_with_alias_cache(
                &memory.without_cell(&stored_pointer),
                pointer,
                value_type,
                distinct_facts,
                obligations,
                assumptions,
                has_external_read_resource,
                alias_cache,
            ));
        }

        return paths;
    }

    if memory.is_loadable_concretely(&pointer, value_type.byte_width()) {
        let Some(value) = symbolic_load_value(&memory, &pointer, value_type) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    // Automatic storage is allocated by a declaration, but allocation alone
    // does not initialize it. Once all possibly-aliasing stored cells have
    // been considered above, an in-bounds local load with no matching cell is
    // an uninitialized read rather than an unconstrained value.
    if pointer.block.starts_with("local:")
        && memory.access_in_bounds(&pointer, value_type.byte_width())
    {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if !has_external_read_resource {
        let proposition = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: Bitvector32Term::Constant(value_type.byte_width()),
        };
        if assumptions.should_defer_non_exact_loadability_obligations() {
            if !assumptions.proves_memory_loadable_for_memory_resolution(
                &memory,
                &pointer,
                &Bitvector32Term::Constant(value_type.byte_width()),
            ) && !assumptions.proves_exact(&proposition)
                && !obligations
                    .iter()
                    .any(|obligation| obligation.proposition() == &proposition)
            {
                obligations.push(ProofObligation::new(proposition));
            }
        } else if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
            return Vec::new();
        }
    }

    let Some(value) = symbolic_load_value(&memory, &pointer, value_type) else {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }];
    };

    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(value),
        facts,
        obligations,
    }]
}

pub(in crate::kernel) fn symbolic_pointer_value_from_int_cell(
    pointer: &Pointer,
    value: &CValue,
    value_type: CType,
) -> Option<CValue> {
    let CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _)) = value else {
        return None;
    };
    let pointee_byte_width = match value_type {
        CType::Int32Pointer => 4,
        CType::UInt8Pointer => 1,
        _ => return None,
    };
    Some(CValue::Pointer(Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::scale_int32(bits.clone(), i64::from(pointee_byte_width)),
    }))
}

pub(in crate::kernel) fn symbolic_load_value(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> Option<CValue> {
    match value_type {
        CType::Void => None,
        CType::Int32 => Some(memory.symbolic_int32_load(pointer)),
        CType::UInt8 => Some(memory.symbolic_uint8_load(pointer)),
        CType::Int32Pointer => Some(memory.symbolic_pointer_load(pointer, 4)),
        CType::UInt8Pointer => Some(memory.symbolic_pointer_load(pointer, 1)),
        CType::Int32Array(_) | CType::UInt8Array(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alias_cache_keys_answers_by_assumption_context() {
        let left = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(810)),
        };
        let right = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(811)),
        };
        let mut cache = MemoryLoadAliasCache::default();
        let empty = PureFactContext::new();
        assert!(!cache.resolution_equal(&left, &right, &empty));

        let equal = empty.assume_condition(
            ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone()),
            true,
        );
        assert!(cache.resolution_equal(&left, &right, &equal));
    }
}
