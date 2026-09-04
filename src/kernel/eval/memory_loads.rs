use super::*;

#[derive(Default)]
struct MemoryLoadAliasCache {
    resolution_equal: BTreeMap<(u64, Pointer), bool>,
    resolution_distinct: BTreeMap<(u64, Pointer), bool>,
    equal: BTreeMap<(u64, Pointer), bool>,
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
}

#[allow(clippy::too_many_arguments)]
pub(in crate::kernel) fn evaluate_c_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    has_external_read_resource: bool,
    next_kernel_variable: &mut u64,
) -> Vec<CExpressionPath> {
    let _assumptions_id_scope = assumptions.enter_id_scope();
    if memory
        .heap
        .pending_reallocations
        .values()
        .any(|pending| pending.old_pointer.block == pointer.block)
    {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome),
            facts,
            obligations,
        }];
    }
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
        next_kernel_variable,
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
    next_kernel_variable: &mut u64,
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
        let Some(value) = canonicalized_symbolic_load_value(
            memory,
            &pointer,
            value_type,
            next_kernel_variable,
            &mut facts,
            assumptions,
        ) else {
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
    // field) cannot be reinterpreted as a stable pointer form. When the
    // caller permits symbolic external loads, fall through to the symbolic
    // load below — its load-term form relates across snapshots — instead
    // of failing the load.
    let pointer_cell_defers_to_symbolic = |value: &CValue| {
        matches!(value, CValue::Int32(_))
            && value_type.is_pointer()
            && has_external_read_resource
            && assumptions.should_prefer_symbolic_external_loads()
    };
    // An exact materialized cell is already the authoritative value for this
    // pointer. Avoid proving every other symbolic cell distinct before the
    // direct map lookup.
    if let Some(value) = memory.known_value(&pointer) {
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            &pointer,
            &value,
            value_type,
            next_kernel_variable,
            &mut facts,
            assumptions,
        ) {
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
        let equal = alias_cache.resolution_equal(&pointer, stored_pointer, assumptions);
        // A bounded equality query can retain an alias guard before its
        // nested separation search reaches a compact resource composition.
        // Recheck separation at the top-level query before treating that
        // materialized cell as authoritative. If both hold, the alias guard
        // describes an unreachable branch and must not manufacture a typed
        // load from the disjoint cell.
        (equal && !alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions))
            .then(|| value.clone())
    }) {
        if let Some(value) = canonicalized_pointer_value_from_int_cell(
            &pointer,
            &value,
            value_type,
            next_kernel_variable,
            &mut facts,
            assumptions,
        ) {
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
    if memory.is_uninitialized_heap_address(&pointer, value_type.byte_width()) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            facts,
            obligations,
        }];
    }

    if memory.is_deallocated_heap_address(&pointer) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        }];
    }

    if has_external_read_resource && assumptions.should_prefer_symbolic_external_loads() {
        let Some(value) = canonicalized_symbolic_load_value(
            memory,
            &pointer,
            value_type,
            next_kernel_variable,
            &mut facts,
            assumptions,
        ) else {
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
    let reduction_base = Some(intern_c_memory_ref(&memory));
    let cells_before_reduction = memory.cells.len();
    std::sync::Arc::make_mut(&mut memory.cells).retain(|stored_pointer, _| {
        !alias_cache.resolution_distinct(&pointer, stored_pointer, assumptions)
    });
    // The returned symbolic load carries the reduced memory snapshot, so
    // other queries must relate it back to its source. Dropping cells
    // provably distinct from the loaded pointer is a
    // no-op for every load, which is exactly the `CellsForgotten` edge;
    // without it the derivation walk dead-ends at this variant.
    if let Some(base) = reduction_base
        && memory.cells.len() != cells_before_reduction
    {
        record_c_memory_derivation(&memory, CMemoryDerivation::CellsForgotten { base });
    }

    if pointer.has_symbolic_block() && has_external_read_resource {
        let Some(value) = canonicalized_symbolic_load_value(
            &memory,
            &pointer,
            value_type,
            next_kernel_variable,
            &mut facts,
            assumptions,
        ) else {
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
                    || !alias_cache.equal(&pointer, stored_pointer, assumptions)))
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
            let equal_outcome = if let Some(value) = canonicalized_pointer_value_from_int_cell(
                &pointer,
                &stored_value,
                value_type,
                next_kernel_variable,
                &mut facts,
                assumptions,
            ) {
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
                next_kernel_variable,
            ));
        }

        return paths;
    }

    if memory.is_zeroed_heap_address(&pointer, value_type.byte_width()) {
        let value = match value_type {
            CType::Int16 => int16(Bitvector32Term::Constant(0)),
            CType::Int32 => int32(Bitvector32Term::Constant(0)),
            CType::UInt8 => uint8(Bitvector32Term::Constant(0)),
            CType::UInt16 => uint16(Bitvector32Term::Constant(0)),
            _ if value_type.is_pointer() => CValue::typed_pointer(Pointer::null(), value_type),
            _ => {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts,
                    obligations,
                }];
            }
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if memory.is_loadable_concretely(&pointer, value_type.byte_width()) {
        let Some(value) = canonicalized_symbolic_load_value(
            &memory,
            &pointer,
            value_type,
            next_kernel_variable,
            &mut facts,
            assumptions,
        ) else {
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

    let Some(value) = canonicalized_symbolic_load_value(
        &memory,
        &pointer,
        value_type,
        next_kernel_variable,
        &mut facts,
        assumptions,
    ) else {
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

/// Reinterprets an int cell's loaded value as a pointer without letting the
/// load enter the offset: a loaded index never enters a pointer offset as a
/// `MemoryLoad` term. The loaded value is bound to a fresh verification
/// variable whose defining equation joins the path's fact stream, so the
/// offset arithmetic downstream works over a small term and the snapshot
/// stays proof-side, consulted only through the defining fact.
pub(in crate::kernel) fn canonicalized_pointer_value_from_int_cell(
    pointer: &Pointer,
    value: &CValue,
    value_type: CType,
    next_kernel_variable: &mut u64,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    let pointee_byte_width = value_type.pointee_type()?.byte_width();
    let fresh = match value {
        CValue::Int16(bits @ Bitvector32Term::MemoryLoad(_, _)) => {
            let fresh = mint_load_variable(bits, next_kernel_variable, facts, assumptions)?;
            return Some(CValue::Int16(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _)) => {
            mint_load_variable(bits, next_kernel_variable, facts, assumptions)?
        }
        // A cell materialized with its load variable (canonicalizing at
        // creation) already carries the variable; record its defining fact
        // in this path's stream, as minting would have.
        CValue::Int32(Bitvector32Term::Variable(variable)) if is_load_variable(variable) => {
            if let Some((memory, pointer)) = registered_load_for_variable(variable) {
                record_load_variable_defining_fact(
                    *variable,
                    Bitvector32Term::MemoryLoad(memory, Box::new(pointer)),
                    facts,
                );
            }
            *variable
        }
        _ => return None,
    };
    Some(CValue::typed_pointer(
        Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(fresh),
                i64::from(pointee_byte_width),
            ),
        },
        value_type,
    ))
}

/// The canonicalizing form of [`symbolic_load_value`]: a pointer loaded from
/// an opaque cell is written through a minted kernel variable instead
/// of embedding the `MemoryLoad` term in its offset. Non-pointer loads pass
/// through unchanged — the invariant governs pointer-offset positions, where
/// arithmetic must stay over small terms.
pub(in crate::kernel) fn canonicalized_symbolic_load_value(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
    next_kernel_variable: &mut u64,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    let value = symbolic_load_value(memory, pointer, value_type)?;
    // Terms are canonical at creation: an int or byte load evaluates to its
    // load variable, with the defining fact beside it, so every fact,
    // offset, and range built from the value is canonical.
    match &value {
        CValue::Int16(bits @ Bitvector32Term::MemoryLoad(_, _)) => {
            let fresh = mint_load_variable(bits, next_kernel_variable, facts, assumptions)?;
            return Some(CValue::Int16(Bitvector32Term::Variable(fresh)));
        }
        CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _)) => {
            let fresh = mint_load_variable(bits, next_kernel_variable, facts, assumptions)?;
            return Some(CValue::Int32(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt8(bits @ Bitvector32Term::MemoryLoad(_, _)) => {
            let fresh = mint_load_variable(bits, next_kernel_variable, facts, assumptions)?;
            return Some(CValue::UInt8(Bitvector32Term::Variable(fresh)));
        }
        CValue::UInt16(bits @ Bitvector32Term::MemoryLoad(_, _)) => {
            let fresh = mint_load_variable(bits, next_kernel_variable, facts, assumptions)?;
            return Some(CValue::UInt16(Bitvector32Term::Variable(fresh)));
        }
        _ => {}
    }
    let CValue::Pointer(pointer_value) = &value else {
        return Some(value);
    };
    let Pointer {
        block,
        offset:
            PointerOffsetTerm::Int32Scaled {
                value: bits,
                byte_width,
            },
    } = pointer_value.pointer()
    else {
        return Some(value);
    };
    if !matches!(bits.as_ref(), Bitvector32Term::MemoryLoad(_, _)) {
        return Some(value);
    }
    let fresh = mint_load_variable(bits, next_kernel_variable, facts, assumptions)?;
    Some(CValue::typed_pointer(
        Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(fresh), *byte_width),
        },
        pointer_value.c_type(),
    ))
}

const LOAD_VARIABLE_BASE: u64 = 1 << 40;
const LOAD_VARIABLE_RANGE: u64 = 1 << 40;

/// The most load identities one verification session may mint. The registry
/// is the only guard against two distinct loads sharing an id (the defining
/// equations `Var(id) == load(memory, pointer)` circulate as ambient truths),
/// so it must never forget an entry mid-session; exhausting it is a loud
/// verifier failure, never a silent clear.
const LOAD_VARIABLE_REGISTRY_CAPACITY: usize = 1_000_000;

#[cfg(test)]
thread_local! {
    static LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

fn load_variable_registry_capacity() -> usize {
    #[cfg(test)]
    if let Some(capacity) = LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.get()) {
        return capacity;
    }
    LOAD_VARIABLE_REGISTRY_CAPACITY
}

/// Runs `body` with the registry capacity lowered so a test can reach it.
#[cfg(test)]
pub(crate) fn with_load_variable_registry_capacity<T>(
    capacity: usize,
    body: impl FnOnce() -> T,
) -> T {
    let previous =
        LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.replace(Some(capacity)));
    let result = body();
    LOAD_VARIABLE_REGISTRY_CAPACITY_OVERRIDE.with(|cell| cell.set(previous));
    result
}

#[cfg(test)]
pub(crate) fn load_variable_registry_len() -> usize {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow().len())
}

/// Whether a kernel variable id lies in the reserved load-variable id space.
/// Structural: no registry consultation, so the answer is deterministic
/// and thread-agnostic.
pub(crate) fn is_load_variable(variable: &Variable) -> bool {
    (LOAD_VARIABLE_BASE..LOAD_VARIABLE_BASE + LOAD_VARIABLE_RANGE).contains(&variable.0)
}

/// Whether a proposition is a load-variable defining equation
/// (`v == load(snapshot, ptr)` for a reserved load variable). Such
/// equations are true by construction, so path wrapping treats them as
/// ambient truths rather than premises.
pub(crate) fn is_load_variable_defining_fact(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = proposition
    else {
        return false;
    };
    matches!(
        (left.as_ref(), right.as_ref()),
        (
            Bitvector32Term::Variable(variable),
            Bitvector32Term::MemoryLoad(_, _)
        ) if is_load_variable(variable)
    )
}

thread_local! {
    static LOAD_VARIABLE_REGISTRY: std::cell::RefCell<
        std::collections::HashMap<Variable, (SharedCMemory, Pointer, SharedCMemory)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static LOAD_VARIABLE_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, (Variable, Bitvector32Term)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    static TERM_CACHE: std::cell::RefCell<
        std::collections::HashMap<Bitvector32Term, Bitvector32Term>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

pub(crate) fn clear_load_canonicalization_caches() {
    LOAD_VARIABLE_CACHE.with(|cache| cache.borrow_mut().clear());
    TERM_CACHE.with(|cache| cache.borrow_mut().clear());
}

pub(crate) fn clear_load_variable_registry() {
    LOAD_VARIABLE_REGISTRY.with(|registry| registry.borrow_mut().clear());
}

/// The load represented by a load variable minted on this thread.
/// Reasoning uses this to consult the snapshot lazily: a load variable in
/// an equality query is viewed as its load exactly where a load term would
/// have triggered provenance evidence.
pub(crate) fn registered_load_for_variable(
    variable: &Variable,
) -> Option<(SharedCMemory, Pointer)> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .map(|(memory, pointer, _)| (memory.clone(), pointer.clone()))
    })
}

/// The first-seen live snapshot a load variable was minted from.
/// The canonical form is a jumped placeholder unsuited to frame checks;
/// transport resolves through this origin, which is DAG-connected and
/// cell-comparable to later effect snapshots. First-seen is deterministic
/// because mint order is execution order.
pub(crate) fn registered_load_origin_for_variable(
    variable: &Variable,
) -> Option<(SharedCMemory, Pointer)> {
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        registry
            .borrow()
            .get(variable)
            .map(|(_, pointer, origin)| (origin.clone(), pointer.clone()))
    })
}

/// Views a term as a memory load for equality reasoning: load terms pass
/// through, and registered load variables resolve to the loads they
/// represent. Other terms are not loads.
pub(crate) fn viewed_as_memory_load(term: &Bitvector32Term) -> Option<Bitvector32Term> {
    match term {
        Bitvector32Term::MemoryLoad(_, _) => Some(term.clone()),
        Bitvector32Term::Variable(variable) => registered_load_for_variable(variable)
            .map(|(memory, pointer)| Bitvector32Term::MemoryLoad(memory, Box::new(pointer))),
        _ => None,
    }
}

/// Whether a proposition mentions any registered load variable.
/// Cross-effect fact transport uses this to include facts written with load
/// variables in rewriting, exactly as load-term facts are included by
/// mentioning their snapshots.
pub(crate) fn proposition_mentions_registered_load_variable(proposition: &Proposition) -> bool {
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::reasoning::variable_collection::collect_proposition_bitvector_variables(
        proposition,
        &mut variables,
    );
    variables.iter().any(|variable| {
        is_load_variable(variable) && registered_load_for_variable(variable).is_some()
    })
}

/// The single canonical form for a term: the deep, assumption-free
/// structural canonicalization ([`canonicalize_atomic_loads`]) followed by
/// load-variable substitution, so every remaining load becomes its load
/// variable. The load variable is the canonical form of its load — a
/// consumer never expands a load variable back into its snapshot-bearing
/// load; the registered defining fact is the only bridge. Equality of
/// canonical forms holds by definition: it needs no proof evidence.
/// Deterministic and idempotent; both stages are memoized.
///
/// [`canonicalize_atomic_loads`]: crate::kernel::memory_provenance::canonicalize_atomic_loads
pub(crate) fn canonical_term(term: &Bitvector32Term) -> Bitvector32Term {
    if let Some(hit) = TERM_CACHE.with(|cache| cache.borrow().get(term).cloned()) {
        return hit;
    }
    let structural = crate::kernel::memory_provenance::canonicalize_atomic_loads(term);
    let result = substitute_load_variables(&structural, &mut None);
    TERM_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 100_000 {
            cache.clear();
        }
        cache.insert(term.clone(), result.clone());
    });
    result
}

/// The canonical form for a pointer offset: every scaled index takes its
/// [`canonical_term`] form. The offset analogue of [`canonical_term`].
pub(crate) fn canonical_offset_term(offset: &PointerOffsetTerm) -> PointerOffsetTerm {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        PointerOffsetTerm::Add(left, right) => {
            PointerOffsetTerm::add(canonical_offset_term(left), canonical_offset_term(right))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            PointerOffsetTerm::scale_int32(canonical_term(value), *byte_width)
        }
    }
}

/// Gives an index or endpoint term the model's stable representation before
/// it enters pointer-offset or range arithmetic: every load atom is replaced
/// by its load variable and each variable's defining equation joins
/// the fact stream. Every producer that scales an integer term into an
/// offset or evaluates a range endpoint must route the term through this,
/// so a loaded index never enters a `PointerOffsetTerm` or a range bound as
/// a raw `MemoryLoad`. Adoption is atomic across producers: naming one
/// birth site while another emits load terms splits one load identity into
/// two terms that only a proved equality could reconnect.
pub(crate) fn canonicalized_offset_index_term(
    bits: Bitvector32Term,
    facts: &mut Vec<ExecutionPureFact>,
) -> Bitvector32Term {
    if !term_mentions_a_memory_load(&bits) {
        return bits;
    }
    substitute_load_variables(&bits, &mut Some(facts))
}

/// The term for reading `pointer` from `memory` at a creation point with no
/// fact stream (resource materialization, contract evaluation): the load
/// variable. Load variables are content-addressed, so this agrees with
/// every other creation point; the defining fact is available through the
/// registry.
pub(crate) fn canonical_form_of_load(memory: SharedCMemory, pointer: Pointer) -> Bitvector32Term {
    let load = Bitvector32Term::MemoryLoad(memory, Box::new(pointer));
    match load_variable_for_term(&load) {
        Some((variable, _)) => Bitvector32Term::Variable(variable),
        None => load,
    }
}

/// The test-only audit of the creation-time invariant (see
/// `docs/internals/canonicalization.md`): while
/// `count_canonical_at_creation_violations` is counting on this thread,
/// every condition fact entering a `PureFactContext` is compared with its
/// canonical form. Each distinct (rewrite kind, creating module) pair is
/// reported once on stderr with an example, where the creating module is
/// the innermost `click::` frame outside the generic context-construction
/// and reasoning layers. Defining facts are exempt: they are the base of
/// the construction. The report is the work list for establishing the
/// invariant at every creation point. Off, this is one thread-local read.
pub(crate) fn check_canonical_at_creation(condition: &ConditionTerm, value: bool) {
    thread_local! {
        static SEEN: std::cell::RefCell<std::collections::BTreeSet<(String, String)>> =
            std::cell::RefCell::new(std::collections::BTreeSet::new());
    }
    if !CANONICAL_AT_CREATION_VIOLATIONS.with(|count| count.get().is_some()) {
        return;
    }
    let proposition = Proposition::ConditionIs(condition.clone(), value);
    if is_load_variable_defining_fact(&proposition) || is_store_fact(condition, value) {
        return;
    }
    let canonical = canonical_condition(condition);
    if &canonical == condition {
        return;
    }
    CANONICAL_AT_CREATION_VIOLATIONS.with(|count| {
        if let Some(seen) = count.get() {
            count.set(Some(seen + 1));
        }
    });
    let kind = if !condition_mentions_a_memory_load(&canonical) {
        let mut variables = std::collections::BTreeSet::new();
        crate::kernel::reasoning::variable_collection::collect_condition_bitvector_variables(
            &canonical,
            &mut variables,
        );
        if variables.iter().any(is_load_variable) {
            "load -> load variable"
        } else {
            "load -> recorded value"
        }
    } else {
        "load rewritten, still a load"
    };
    const GENERIC: [&str; 12] = [
        "check_canonical_at_creation",
        "assume_condition",
        "assume_proposition",
        "assumptions_from_propositions",
        "assumptions_with_path_context",
        "assumptions_with_propositions",
        "ProofFacts::",
        "atomic_derivation_premises",
        "derive_proposition",
        "::proves",
        "PureFactContext>::",
        "path_facts::",
    ];
    let backtrace = std::backtrace::Backtrace::force_capture().to_string();
    let creator = backtrace
        .lines()
        .filter_map(|line| line.trim().split_once(": ").map(|(_, frame)| frame))
        .find(|frame| {
            frame.starts_with("click::") && !GENERIC.iter().any(|generic| frame.contains(generic))
        })
        .map(|frame| {
            frame
                .split("::{{closure}}")
                .next()
                .unwrap_or(frame)
                .trim_start_matches("click::")
                .to_string()
        })
        .unwrap_or_else(|| "<no click frame>".to_string());
    let first_time = SEEN.with(|seen| {
        seen.borrow_mut()
            .insert((kind.to_string(), creator.clone()))
    });
    if !first_time {
        return;
    }
    let width = 240usize;
    let shown = format!("{condition:?}");
    let shown = &shown[..shown.len().min(width)];
    eprintln!("CANONICAL-AT-CREATION violation [{kind}] created in {creator}\n  example: {shown}");
}

thread_local! {
    /// `Some(n)` while a creation-time invariant audit is counting
    /// violations on this thread; `None` otherwise (the check is off).
    static CANONICAL_AT_CREATION_VIOLATIONS: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// Runs `body` with the creation-time invariant check on, returning the
/// body's result and the number of condition facts that entered a
/// `PureFactContext` in a non-canonical form. The standing regression for
/// `docs/internals/canonicalization.md` asserts zero over fixture verification.
#[cfg(test)]
pub(crate) fn count_canonical_at_creation_violations<T>(body: impl FnOnce() -> T) -> (T, usize) {
    let previous = CANONICAL_AT_CREATION_VIOLATIONS.with(|count| count.replace(Some(0)));
    let result = body();
    let violations = CANONICAL_AT_CREATION_VIOLATIONS
        .with(|count| count.replace(previous))
        .unwrap_or(0);
    (result, violations)
}

/// Whether a condition is a store fact `load(after, p) == v` where `after`
/// records `v` at `p`: the memory-content counterpart of a defining fact,
/// exported from a certified store record and cited by certificates through
/// `at(statement(n).exit, ...)`. Like defining facts, store facts are the
/// base the invariant rests on and keep their load term.
fn is_store_fact(condition: &ConditionTerm, value: bool) -> bool {
    if !value {
        return false;
    }
    let ConditionTerm::Bitvector32Equal(left, right) = condition else {
        return false;
    };
    let (load, stored) = match (left.as_ref(), right.as_ref()) {
        (Bitvector32Term::MemoryLoad(memory, pointer), stored)
        | (stored, Bitvector32Term::MemoryLoad(memory, pointer)) => ((memory, pointer), stored),
        _ => return false,
    };
    matches!(
        load.0.known_value(load.1),
        Some(
            CValue::Int16(recorded)
            | CValue::Int32(recorded)
            | CValue::UInt8(recorded)
            | CValue::UInt16(recorded)
            | CValue::UInt32(recorded),
        ) if &recorded == stored
    )
}

/// The canonical form for a condition: every operand takes its
/// [`canonical_term`] form, so terms that are equal by definition compare
/// identically. The comparison direction of the canonical model for
/// whole facts.
pub(crate) fn canonical_condition(condition: &ConditionTerm) -> ConditionTerm {
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            Box::new(canonical_term(left)),
            Box::new(canonical_term(right)),
        )
    };
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => condition.clone(),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32Equal(left, right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            let (left, right) = binary(left, right);
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::PointerOffsetEqual(
            Box::new(canonical_offset_term(left)),
            Box::new(canonical_offset_term(right)),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::PointerEqual(
            Box::new(Pointer {
                block: left.block.clone(),
                offset: canonical_offset_term(&left.offset),
            }),
            Box::new(Pointer {
                block: right.block.clone(),
                offset: canonical_offset_term(&right.offset),
            }),
        ),
    }
}

/// The canonical form for a condition fact; non-condition propositions pass
/// through unchanged.
pub(crate) fn canonical_condition_fact(fact: &Proposition) -> Proposition {
    let Proposition::ConditionIs(condition, value) = fact else {
        return fact.clone();
    };
    Proposition::ConditionIs(canonical_condition(condition), *value)
}

/// Replaces every load atom in a term with its load variable.
/// When `facts` carries a stream, this is the production mode: each
/// substituted load variable's defining fact joins the stream,
/// deduplicated, so the variable always travels with its defining fact. Binder scopes
/// (`RangeFold` bodies) are left untouched: a load under a fold can mention
/// bound variables, which name no load identity.
fn substitute_load_variables(
    term: &Bitvector32Term,
    facts: &mut Option<&mut Vec<ExecutionPureFact>>,
) -> Bitvector32Term {
    fn binary(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        facts: &mut Option<&mut Vec<ExecutionPureFact>>,
    ) -> (Box<Bitvector32Term>, Box<Bitvector32Term>) {
        (
            Box::new(substitute_load_variables(left, facts)),
            Box::new(substitute_load_variables(right, facts)),
        )
    }
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::MemoryLoad(_, _) => match load_variable_for_term(term) {
            Some((variable, load)) => {
                if let Some(facts) = facts.as_deref_mut() {
                    record_load_variable_defining_fact(variable, load, facts);
                }
                Bitvector32Term::Variable(variable)
            }
            None => term.clone(),
        },
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::Add(left, right)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::Subtract(left, right)
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::Multiply(left, right)
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::Divide(left, right)
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::UnsignedDivide(left, right)
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::Remainder(left, right)
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::UnsignedRemainder(left, right)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::ShiftLeft(left, right)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::ArithmeticShiftRight(left, right)
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::LogicalShiftRight(left, right)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::BitwiseAnd(left, right)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::BitwiseOr(left, right)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right, facts);
            Bitvector32Term::BitwiseXor(left, right)
        }
        Bitvector32Term::BitwiseNot(value) => {
            Bitvector32Term::BitwiseNot(Box::new(substitute_load_variables(value, facts)))
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: Box::new(substitute_load_variables_in_condition(condition, facts)),
            then_term: Box::new(substitute_load_variables(then_term, facts)),
            else_term: Box::new(substitute_load_variables(else_term, facts)),
        },
        Bitvector32Term::RangeFold { .. } => term.clone(),
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_load_variables(argument, facts))
                    .collect(),
            }
        }
    }
}

fn substitute_load_variables_in_condition(
    condition: &ConditionTerm,
    facts: &mut Option<&mut Vec<ExecutionPureFact>>,
) -> ConditionTerm {
    fn binary(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        facts: &mut Option<&mut Vec<ExecutionPureFact>>,
    ) -> (Box<Bitvector32Term>, Box<Bitvector32Term>) {
        (
            Box::new(substitute_load_variables(left, facts)),
            Box::new(substitute_load_variables(right, facts)),
        )
    }
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => condition.clone(),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedLessThan(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32Equal(left, right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            let (left, right) = binary(left, right, facts);
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::PointerOffsetEqual(
            Box::new(substitute_load_variables_in_offset(left, facts)),
            Box::new(substitute_load_variables_in_offset(right, facts)),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::PointerEqual(
            Box::new(Pointer {
                block: left.block.clone(),
                offset: substitute_load_variables_in_offset(&left.offset, facts),
            }),
            Box::new(Pointer {
                block: right.block.clone(),
                offset: substitute_load_variables_in_offset(&right.offset, facts),
            }),
        ),
    }
}

fn substitute_load_variables_in_offset(
    offset: &PointerOffsetTerm,
    facts: &mut Option<&mut Vec<ExecutionPureFact>>,
) -> PointerOffsetTerm {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            substitute_load_variables_in_offset(left, facts),
            substitute_load_variables_in_offset(right, facts),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            PointerOffsetTerm::scale_int32(substitute_load_variables(value, facts), *byte_width)
        }
    }
}

/// Whether two terms have the same canonical form. Two forms of one value
/// compare equal exactly when their [`canonical_term`] forms are
/// identical. Load-free terms are fixed points of the canonical form, so
/// they compare by identity without a canonicalization walk. Bounded by
/// term size, with both canonicalization stages memoized.
pub(crate) fn terms_have_same_canonical_form(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    if left == right {
        return true;
    }
    if !term_mentions_a_memory_load(left) && !term_mentions_a_memory_load(right) {
        return false;
    }
    canonical_term(left) == canonical_term(right)
}

/// Whether two pointer offsets have the same canonical form; the offset
/// analogue of [`terms_have_same_canonical_form`].
pub(crate) fn offsets_have_same_canonical_form(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
) -> bool {
    if left == right {
        return true;
    }
    if !offset_mentions_a_memory_load(left) && !offset_mentions_a_memory_load(right) {
        return false;
    }
    canonical_offset_term(left) == canonical_offset_term(right)
}

/// Whether a term contains any load atom the canonical form could rewrite.
/// Load-free terms are fixed points of [`canonical_term`], which the
/// comparators use to answer load-free mismatches without a walk.
fn term_mentions_a_memory_load(term: &Bitvector32Term) -> bool {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
        Bitvector32Term::MemoryLoad(_, _) => true,
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        Bitvector32Term::BitwiseNot(value) => term_mentions_a_memory_load(value),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            condition_mentions_a_memory_load(condition)
                || term_mentions_a_memory_load(then_term)
                || term_mentions_a_memory_load(else_term)
        }
        // The structural stage canonicalizes inside fold bodies even though
        // name substitution stops at the binder, so a fold may still change
        // under the canonical form.
        Bitvector32Term::RangeFold { .. } => true,
        Bitvector32Term::PureFunctionApplication { name: _, arguments } => {
            arguments.iter().any(term_mentions_a_memory_load)
        }
    }
}

fn condition_mentions_a_memory_load(condition: &ConditionTerm) -> bool {
    match condition {
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            term_mentions_a_memory_load(left) || term_mentions_a_memory_load(right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            offset_mentions_a_memory_load(left) || offset_mentions_a_memory_load(right)
        }
        ConditionTerm::PointerEqual(left, right) => {
            offset_mentions_a_memory_load(&left.offset)
                || offset_mentions_a_memory_load(&right.offset)
        }
    }
}

fn offset_mentions_a_memory_load(offset: &PointerOffsetTerm) -> bool {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
        PointerOffsetTerm::Add(left, right) => {
            offset_mentions_a_memory_load(left) || offset_mentions_a_memory_load(right)
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => term_mentions_a_memory_load(value),
    }
}

/// The load variable representing one load identity: the pair of a memory
/// snapshot (by content) and a loaded pointer. The id is derived
/// deterministically by hashing that identity into a reserved id space, so
/// every pass — contract-grant lowering, requirement evaluation, and body
/// execution — writes the same load with the same variable without sharing
/// any allocator state, and certificates check across runs. A thread-local
/// registry detects hash collisions between distinct load identities and
/// stops verification loudly instead of silently conflating them; it is
/// never cleared within a session, and exhausting its capacity is likewise
/// a loud failure rather than a silent reset.
pub(crate) fn load_variable_for_cell(memory: &SharedCMemory, pointer: &Pointer) -> Variable {
    load_variable_for_cell_with_origin(memory, pointer, memory)
}

pub(crate) fn load_variable_for_cell_with_origin(
    memory: &SharedCMemory,
    pointer: &Pointer,
    origin: &SharedCMemory,
) -> Variable {
    use std::hash::{Hash, Hasher};
    // Derive the variable from the cell's DAG epoch when one is recorded:
    // snapshots that differ only by effects provably disjoint from this
    // cell then share the variable, so bookkeeping drift and unrelated
    // stores do not mint new identities for one load.
    let epoch = crate::kernel::memory_provenance::cell_epoch_for_load_variable(memory, pointer);
    let memory = epoch.as_ref().unwrap_or(memory);
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
    pointer.hash(&mut hasher);
    let hash = hasher.finish();
    let variable = Variable(LOAD_VARIABLE_BASE + hash % LOAD_VARIABLE_RANGE);
    LOAD_VARIABLE_REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        if let Some((known_memory, known_pointer, _)) = registry.get(&variable) {
            assert!(
                known_memory == memory && known_pointer == pointer,
                "load-variable collision: {variable:?} represents two distinct loads"
            );
        } else {
            assert!(
                registry.len() < load_variable_registry_capacity(),
                "load-variable registry capacity exhausted: this verification session minted \
                 {} distinct load identities; the registry never forgets an entry because \
                 it is the only collision guard for load-variable ids",
                registry.len()
            );
            registry.insert(variable, (memory.clone(), pointer.clone(), origin.clone()));
        }
    });
    variable
}

/// Returns the load variable for a load term's provenance-stable form.
/// The term is first canonicalized without assumptions, resolving cached
/// cells and snapshot representation differences. The same cell loaded at
/// different symbolic states therefore shares one load variable whenever
/// the difference is representational. The second return value is the form
/// used by the variable's defining equation.
pub(crate) fn load_variable_for_term(
    bits: &Bitvector32Term,
) -> Option<(Variable, Bitvector32Term)> {
    let Bitvector32Term::MemoryLoad(_, _) = bits else {
        return None;
    };
    // Naming is deterministic per term, and callers ask per fact atom per
    // comparison; the epoch walk and canonicalization behind a cold call
    // are not free, so cache by term. Term hashing is cheap: embedded
    // snapshots hash by interned identity.
    if let Some(hit) = LOAD_VARIABLE_CACHE.with(|cache| cache.borrow().get(bits).cloned()) {
        return Some(hit);
    }
    crate::instrumentation::record_deterministic_work(1);
    let computed = load_variable_for_term_uncached(bits)?;
    LOAD_VARIABLE_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.len() >= 100_000 {
            cache.clear();
        }
        cache.insert(bits.clone(), computed.clone());
    });
    Some(computed)
}

fn load_variable_for_term_uncached(bits: &Bitvector32Term) -> Option<(Variable, Bitvector32Term)> {
    let canonical = crate::kernel::memory_provenance::canonicalize_atomic_loads(bits);
    if let Bitvector32Term::MemoryLoad(memory, pointer) = &canonical {
        let Bitvector32Term::MemoryLoad(origin, _) = bits else {
            unreachable!("the pattern above matched a memory load");
        };
        return Some((
            load_variable_for_cell_with_origin(memory, pointer, origin),
            canonical.clone(),
        ));
    }
    let Bitvector32Term::MemoryLoad(memory, pointer) = bits else {
        unreachable!("the pattern above matched a memory load");
    };
    Some((load_variable_for_cell(memory, pointer), bits.clone()))
}

/// Binds a load term to its load variable and records the defining
/// equation in the path's fact stream. The defining equation is
/// kernel-certified by construction: the load variable represents this
/// load. It must not demand a checkable assumption derivation
/// downstream.
fn mint_load_variable(
    bits: &Bitvector32Term,
    _next_kernel_variable: &mut u64,
    facts: &mut Vec<ExecutionPureFact>,
    _assumptions: &PureFactContext,
) -> Option<Variable> {
    let (fresh, load) = load_variable_for_term(bits)?;
    record_load_variable_defining_fact(fresh, load, facts);
    Some(fresh)
}

/// Records a load variable's exact defining fact in a fact
/// stream, deduplicated by proposition. The equation is kernel-certified by
/// construction: the load variable represents this load. It must not demand
/// a checkable assumption derivation downstream.
fn record_load_variable_defining_fact(
    variable: Variable,
    load: Bitvector32Term,
    facts: &mut Vec<ExecutionPureFact>,
) {
    let defining = ExecutionPureFact::certified(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(load),
        ),
        true,
    ));
    if !facts
        .iter()
        .any(|fact| fact.proposition == defining.proposition)
    {
        facts.push(defining);
    }
}

pub(in crate::kernel) fn symbolic_load_value(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> Option<CValue> {
    match value_type {
        CType::Void => None,
        CType::Int16 => Some(memory.symbolic_int16_load(pointer)),
        CType::Int32 => Some(memory.symbolic_int32_load(pointer)),
        CType::UInt8 => Some(memory.symbolic_uint8_load(pointer)),
        CType::UInt16 => Some(memory.symbolic_uint16_load(pointer)),
        CType::UInt32 => Some(memory.symbolic_uint32_load(pointer)),
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer => Some(memory.symbolic_pointer_load(
            pointer,
            value_type.pointee_type()?.byte_width(),
            value_type,
        )),
        CType::FunctionPointer(_) => None,
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
