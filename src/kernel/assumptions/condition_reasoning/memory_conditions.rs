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
        let Some(_depth_guard) = MemoryLoadEqualityDepthGuard::enter() else {
            return false;
        };
        if memory_load_terms_equal_for_fact_transport(left, right, self) {
            return true;
        }
        if let Some(left) = self.resolve_memory_load_term(left) {
            return self.bitvector_terms_proven_equal(&left, right);
        }
        if let Some(right) = self.resolve_memory_load_term(right) {
            return self.bitvector_terms_proven_equal(left, &right);
        }

        // Load variables are compared as the loads they represent, viewed at the
        // live snapshot each was first read from: the canonical epoch has
        // no derivation history, while the origin is DAG-connected, so the
        // frame legs below can relate two load variables for one cell across an
        // effect the facts frame it through; two variables over one epoch
        // whose addresses this context proves equal are one cell.
        let view_at_origin = |term: &Bitvector32Term| match term {
            Bitvector32Term::Variable(variable) => {
                crate::kernel::eval::registered_load_origin_for_variable(variable)
                    .map(|(memory, pointer)| Bitvector32Term::MemoryLoad(memory, Box::new(pointer)))
            }
            Bitvector32Term::MemoryLoad(_, _) => Some(term.clone()),
            _ => None,
        };
        let left_view = view_at_origin(left);
        let right_view = view_at_origin(right);
        let (
            Some(Bitvector32Term::MemoryLoad(left_memory, left_pointer)),
            Some(Bitvector32Term::MemoryLoad(right_memory, right_pointer)),
        ) = (&left_view, &right_view)
        else {
            return false;
        };
        if !pointers_proven_equal(left_pointer, right_pointer, self) {
            return false;
        }
        if memories_match_for_pointer_load(left_memory, right_memory, left_pointer) {
            return true;
        }
        // The DAG answers from recorded edges before either snapshot
        // comparison below, and long before the two `prop_facts` scans that
        // reconstruct the same write history from effect summaries.
        if crate::kernel::api::loads_equal_along_memory_derivations_at(
            left_memory,
            right_memory,
            left_pointer,
            self,
        ) {
            return true;
        }
        // The two remaining legs — whole-snapshot alias comparison and the
        // framed-load prover — are the expensive general searches. Every
        // cheap route has already answered above (fact transport,
        // resolution, structural match, the DAG walk), so the residue runs
        // under one isolated node budget: load-equality questions the cheap
        // evidence cannot settle within it fail promptly here rather than
        // fanning out into the giant-term recursion that load-variable construction
        // exists to avoid.
        crate::kernel::reasoning::with_isolated_memory_resolution_fuel(8_000, || {
            // Two forms whose marker sets differ are never syntactically
            // equal and defeat the snapshot comparison's block-set filter,
            // but the load can still be provably unchanged across the marker
            // delta: the framed-load prover consumes the recorded effect
            // summaries and mutates-only facts to frame the loaded pointer
            // across each intervening effect. Deciding the pair by that
            // proof, instead of by form coincidence, is what keeps fact
            // transport working once canonicalization preserves havoc
            // markers.
            crate::kernel::api::c_memory_load_is_unchanged(
                left_memory,
                right_memory,
                left_pointer,
                self,
            )
        })
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
        let CValue::Int32(value) = self.resolve_memory_load_value(memory, pointer)? else {
            return None;
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
