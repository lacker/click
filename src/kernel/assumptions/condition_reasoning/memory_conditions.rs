use super::*;

impl PureFactContext {
    /// Decides whether two conditions are two forms of one fact that
    /// differ only in the memory snapshots their load atoms carry.
    ///
    /// Sound because it is exact everywhere except at load atoms, and a pair
    /// of load atoms is accepted only when `memory_loads_proven_equal`
    /// proves the two loads denote the same value under these assumptions —
    /// which for differing snapshots means proving the snapshots agree at the
    /// loaded pointer. Structurally different conditions never match.
    pub fn conditions_equal_modulo_proven_snapshots(
        &self,
        left: &ConditionTerm,
        right: &ConditionTerm,
    ) -> bool {
        conditions_equal_with_load_atoms(left, right, &|left, right| {
            left == right || self.memory_loads_proven_equal(left, right)
        })
    }

    /// Like [`Self::conditions_equal_modulo_proven_snapshots`], additionally
    /// accepting two loads of one pointer whose snapshots the recorded memory
    /// DAG proves agree at that pointer under these assumptions, crossing
    /// call-havoc and store edges by the separation and ownership facts in
    /// this context. This is the checked replacement for load names that
    /// were once shared across such edges by a recording path's assumptions;
    /// it is reserved for target-selected candidates, not broad matching.
    pub(crate) fn conditions_equal_modulo_origin_unchanged(
        &self,
        left: &ConditionTerm,
        right: &ConditionTerm,
    ) -> bool {
        conditions_equal_with_load_atoms(left, right, &|left, right| {
            // The recorded-DAG check runs first: the broad fact-matching
            // check below records generation-scoped negative answers for the
            // same query, which would otherwise shadow this stronger one.
            left == right
                || match (left, right) {
                    (
                        Bitvector32Term::MemoryLoad(_, left_pointer),
                        Bitvector32Term::MemoryLoad(_, right_pointer),
                    ) => {
                        left_pointer == right_pointer
                            && crate::kernel::explicit_atomic_equality_from_memory_derivations(
                                left, right, self,
                            )
                    }
                    _ => false,
                }
                || self.memory_loads_proven_equal(left, right)
        })
    }

    pub(crate) fn proves_condition_exact_or_snapshot(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts.iter().any(|(fact, fact_value)| {
            *fact_value == value
                && (fact == condition
                    || conditions_equal_ignoring_memories(fact, condition)
                        && self.conditions_equal_modulo_proven_snapshots(fact, condition))
        })
    }

    pub(in crate::kernel) fn memory_loads_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let checked_load_equality = |left: &Bitvector32Term, right: &Bitvector32Term| {
            let atomic = || {
                let (Some(left), Some(right)) = (
                    crate::kernel::eval::viewed_as_memory_load(left),
                    crate::kernel::eval::viewed_as_memory_load(right),
                ) else {
                    return false;
                };
                crate::kernel::memory_provenance::checked_recorded_atomic_load_equality(
                    &left, &right, self,
                )
            };
            crate::kernel::memory_provenance::checked_origin_load_equality(left, right, self)
                || atomic()
        };
        if checked_load_equality(left, right) {
            return true;
        }
        if let Some(left) = self.resolve_memory_load_term(left) {
            return left == *right
                || self.bitvector_terms_equal_from_facts(&left, right)
                || checked_load_equality(&left, right);
        }
        if let Some(right) = self.resolve_memory_load_term(right) {
            return *left == right
                || self.bitvector_terms_equal_from_facts(left, &right)
                || checked_load_equality(left, &right);
        }
        false
    }

    pub(in crate::kernel) fn memory_snapshots_directly_proven_equal_for_memory_resolution(
        &self,
        left: &CMemory,
        right: &CMemory,
        pointer: &Pointer,
    ) -> bool {
        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryMutatesOnly {
                before,
                after,
                pointers,
            } => {
                let matches = memories_match_for_pointer_load(before, left, pointer)
                    && memories_match_for_pointer_load(after, right, pointer)
                    || memories_match_for_pointer_load(before, right, pointer)
                        && memories_match_for_pointer_load(after, left, pointer);
                matches
                    && pointers.iter().all(|write| {
                        pointers_proven_distinct_for_memory_resolution(write, pointer, self)
                    })
            }
            Proposition::CMemoryEffectSummary {
                before,
                after,
                mutable_ranges,
            } => {
                // Endpoint matching filters candidate effect facts inside a
                // prop-facts scan, so it must stay bounded: the general
                // composition-backed alias search per differing cell per
                // candidate dominated a simple step's budget on bounded-pool
                // (370k of 500k units).
                let endpoint_matches = |expected: &CMemory, actual: &CMemory| {
                    memory_matches_effect_summary_endpoint(expected, actual, pointer)
                        || memories_match_for_pointer_load_bounded_alias(
                            expected, actual, pointer, self,
                        )
                };
                let matches = endpoint_matches(before, left) && endpoint_matches(after, right)
                    || endpoint_matches(before, right) && endpoint_matches(after, left);
                matches && self.ranges_directly_disjoint_from_pointer(mutable_ranges, pointer)
            }
            Proposition::CHeapAllocationFreed {
                before,
                after,
                allocation_base,
                bytes,
            } => {
                // Bounded for the same reason as the effect-summary arm.
                let endpoint_matches = |expected: &CMemory, actual: &CMemory| {
                    memory_matches_effect_summary_endpoint(expected, actual, pointer)
                        || memories_match_for_pointer_load_bounded_alias(
                            expected, actual, pointer, self,
                        )
                };
                let matches = endpoint_matches(before, left) && endpoint_matches(after, right)
                    || endpoint_matches(before, right) && endpoint_matches(after, left);
                matches
                    && crate::kernel::api::heap_allocation_proven_separate_from_pointer(
                        allocation_base,
                        bytes,
                        pointer,
                        self,
                    )
            }
            _ => false,
        })
    }

    pub(in crate::kernel) fn resolve_memory_load_term(
        &self,
        term: &Bitvector32Term,
    ) -> Option<Bitvector32Term> {
        // A load variable resolves as the load it represents: the cell it reads
        // may be decided by this context's facts (a bound index proven
        // distinct from every stored cell) even though the variable was
        // created without them. The result is canonical so a resolution
        // to an earlier snapshot's load compares by canonical form.
        let viewed = crate::kernel::eval::viewed_as_memory_load(term)?;
        let Bitvector32Term::MemoryLoad(memory, pointer) = &viewed else {
            return None;
        };
        let value = match self.resolve_memory_load_value(memory, pointer)? {
            CValue::Int16(value)
            | CValue::Int32(value)
            | CValue::UInt8(value)
            | CValue::UInt16(value)
            | CValue::UInt32(value)
            | CValue::Int64(value)
            | CValue::UInt64(value) => value,
            CValue::Void | CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => {
                return None;
            }
        };
        let value = if viewed == *term {
            value
        } else {
            crate::kernel::eval::canonical_term(&value)
        };
        (&value != term && value != viewed).then_some(value)
    }

    pub(in crate::kernel) fn resolve_memory_load_value(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
    ) -> Option<CValue> {
        if let Some(value) = memory.known_value(pointer) {
            return Some(value);
        }

        let mut unresolved_alias = false;
        for (cell_pointer, value) in memory.cells.iter() {
            if pointers_proven_distinct_for_memory_resolution(cell_pointer, pointer, self) {
                continue;
            }
            if pointers_proven_equal_for_memory_resolution(cell_pointer, pointer, self) {
                return Some(value.clone());
            }
            unresolved_alias = true;
        }

        if unresolved_alias {
            return None;
        }

        memory
            .is_loadable_concretely(pointer, 4)
            .then(|| memory.symbolic_int32_load(pointer))
    }
}
