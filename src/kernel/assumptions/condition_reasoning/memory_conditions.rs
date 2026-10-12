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
                        Bitvector32Term::MemoryLoad(_, left_pointer, left_kind),
                        Bitvector32Term::MemoryLoad(_, right_pointer, right_kind),
                    ) => {
                        left_pointer == right_pointer
                            && left_kind == right_kind
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
        // This resolver also handles 8-bit, 16-bit, and 64-bit loads. Only a
        // four-byte integer read may use the int32 graph for its value.
        let is_four_byte_load = |load: &Bitvector32Term| match load {
            Bitvector32Term::Variable(variable) => {
                crate::kernel::registered_load_kind_for_variable(variable) == Some(LoadKind::Bits32)
            }
            Bitvector32Term::MemoryLoad(_, _, kind) => *kind == LoadKind::Bits32,
            _ => false,
        };
        let graph_proves_resolved_int32 =
            |load: &Bitvector32Term, resolved: &Bitvector32Term, other: &Bitvector32Term| {
                is_four_byte_load(load) && self.int32_values_known_equal(resolved, other)
            };
        if let Some(resolved_left) = self.resolve_memory_load_term(left) {
            if resolved_left == *right || graph_proves_resolved_int32(left, &resolved_left, right) {
                return true;
            }
            // Two checked resolutions may reveal equal stored values even
            // when neither value equals the other load's opaque name.
            if is_four_byte_load(left)
                && is_four_byte_load(right)
                && let Some(resolved_right) = self.resolve_memory_load_term(right)
                && self.int32_values_known_equal(&resolved_left, &resolved_right)
            {
                return true;
            }
            return checked_load_equality(&resolved_left, right);
        }
        if let Some(resolved_right) = self.resolve_memory_load_term(right) {
            return *left == resolved_right
                || graph_proves_resolved_int32(right, &resolved_right, left)
                || checked_load_equality(left, &resolved_right);
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
                writes,
            } => {
                let matches = memories_match_for_pointer_load(before, left, pointer)
                    && memories_match_for_pointer_load(after, right, pointer)
                    || memories_match_for_pointer_load(before, right, pointer)
                        && memories_match_for_pointer_load(after, left, pointer);
                matches
                    && writes.iter().all(|(write, bytes)| {
                        crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
                            write,
                            *bytes,
                            pointer,
                            crate::kernel::eval::load_access_width_at_address_or_widest(pointer),
                            self,
                        )
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
                matches
                    && (crate::kernel::memory_provenance::typed_ranges_disjoint_from_pointer_evidence(
                        mutable_ranges,
                        pointer,
                        crate::kernel::load_access_width_at_address_or_widest(pointer),
                        self,
                    ).is_some()
                        || crate::kernel::primitives::CallKeptRanges::recorded_on(after)
                            .is_some_and(|kept| {
                                kept.holds_access(
                                    pointer,
                                    crate::kernel::eval::load_access_width_at_address_or_widest(
                                        pointer,
                                    ),
                                    self,
                                )
                            }))
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
        let Bitvector32Term::MemoryLoad(memory, pointer, kind) = &viewed else {
            return None;
        };
        let value = match self.resolve_memory_load_value(memory, pointer, *kind)? {
            CValue::Int8(value) => value,
            CValue::Bool(value)
            | CValue::Int16(value)
            | CValue::Int32(value)
            | CValue::UInt8(value)
            | CValue::UInt16(value)
            | CValue::UInt32(value)
            | CValue::Int64(value)
            | CValue::UInt64(value)
            | CValue::Int128(value)
            | CValue::UInt128(value) => value,
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

    /// The value a `kind` read at `pointer` returns in `memory`: the cell
    /// proven at that address when it is exactly that read
    /// ([`LoadKind::reads_value`]), or else the read itself as a load term of
    /// the same kind, when no cell may alias it.
    pub(in crate::kernel) fn resolve_memory_load_value(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        kind: LoadKind,
    ) -> Option<CValue> {
        let byte_width = kind.byte_width();
        if let Some(value) = memory.known_value(pointer) {
            return kind.reads_value(&value).then_some(value);
        }

        // The first cell, in pointer order, proven at `pointer` answers; short
        // of one, a cell neither proven there nor proven elsewhere leaves the
        // load unresolved. Runs use compact slot selection even for symbolic
        // indexes: an unresolved alias is not a reason to enumerate the array.
        let mut unresolved_alias = false;
        let mut first_equal: Option<(Pointer, CValue)> = None;
        let normalized = std::cell::OnceCell::new();
        let consider = |cell_pointer: &Pointer,
                        value: &CValue,
                        first_equal: &mut Option<(Pointer, CValue)>| {
            if pointers_proven_distinct_for_memory_resolution(cell_pointer, pointer, self) {
                return false;
            }
            if pointers_proven_equal_for_memory_resolution(cell_pointer, pointer, self) {
                if first_equal
                    .as_ref()
                    .is_none_or(|(earlier, _)| cell_pointer < earlier)
                {
                    *first_equal = Some((cell_pointer.clone(), value.clone()));
                }
                return true;
            }
            true
        };
        // A cell or run outside the load's alias candidates is in a block
        // proven distinct from it, which `consider` and
        // `run_slots_resolving_load` answer as elsewhere, so only the
        // candidates are asked. Each candidate asked, cell or run, is one
        // unit, independent of the run's logical element count.
        let candidates = crate::kernel::primitives::AliasCandidates::of_block(&pointer.block);
        for run in memory.cells.candidate_runs(&candidates) {
            crate::instrumentation::record_deterministic_work(1);
            match crate::kernel::reasoning::memory_resolution::run_slots_resolving_load(
                run, pointer,
            ) {
                Some((equal, unresolved)) => {
                    #[cfg(debug_assertions)]
                    if run.count() <= crate::kernel::primitives::CHECKED_RUN_SLOTS {
                        crate::instrumentation::uncharged_debug_check(|| {
                            let mut slot_equal = None;
                            let mut slot_unresolved = false;
                            for index in run.live_indexes() {
                                let cell_pointer = run.slot_pointer(index);
                                if pointers_proven_distinct_for_memory_resolution(
                                    &cell_pointer,
                                    pointer,
                                    self,
                                ) {
                                    continue;
                                }
                                if pointers_proven_equal_for_memory_resolution(
                                    &cell_pointer,
                                    pointer,
                                    self,
                                ) {
                                    slot_equal = slot_equal.or(Some(index));
                                } else {
                                    slot_unresolved = true;
                                }
                            }
                            assert_eq!(
                                (slot_equal, slot_unresolved && slot_equal.is_none()),
                                (equal, unresolved && equal.is_none()),
                                "a run's whole-run load resolution disagrees with its slots for {pointer:?} in {run:?}"
                            );
                        });
                    }
                    unresolved_alias |= unresolved;
                    if let Some(index) = equal {
                        let cell_pointer = run.slot_pointer(index);
                        if first_equal
                            .as_ref()
                            .is_none_or(|(earlier, _)| cell_pointer < *earlier)
                        {
                            first_equal = Some((cell_pointer, run.value(index)));
                        }
                    }
                }
                None => {
                    let (slots, _) =
                        crate::kernel::reasoning::memory_resolution::run_slots_equal_to_load(
                            run,
                            pointer,
                            &normalized,
                            self,
                        );
                    let selected = match slots {
                        crate::kernel::primitives::SlotSet::Elements(index, end)
                            if end == index + 1 =>
                        {
                            Some(index)
                        }
                        _ => None,
                    };
                    // A field/base alias may be known through recorded load
                    // identities rather than the exact alias index. Propose
                    // one slot from the constant offset difference, then ask
                    // the full pointer matcher about that candidate only.
                    let selected = selected.or_else(|| {
                        use crate::kernel::reasoning::memory_resolution::offset_atoms_and_constant;
                        let (_, read_shift) = offset_atoms_and_constant(&pointer.offset);
                        let (_, base_shift) = offset_atoms_and_constant(&run.base().offset);
                        let shift = read_shift.checked_sub(base_shift)?;
                        let stride = i64::from(run.element_width());
                        if stride <= 0 || shift < 0 || shift % stride != 0 {
                            return None;
                        }
                        let index = u32::try_from(shift / stride).ok()?;
                        (index < run.count()
                            && !run.holes().contains(index)
                            && pointers_proven_equal_for_memory_resolution(
                                &run.slot_pointer(index),
                                pointer,
                                self,
                            ))
                        .then_some(index)
                    });
                    if let Some(index) = selected.filter(|index| !run.holes().contains(*index)) {
                        let cell_pointer = run.slot_pointer(index);
                        if first_equal
                            .as_ref()
                            .is_none_or(|(earlier, _)| cell_pointer < *earlier)
                        {
                            first_equal = Some((cell_pointer, run.value(index)));
                        }
                    } else if !run.holes().covers_range(0, run.count()) {
                        // Keeping a possibly aliasing run unresolved is
                        // conservative. Only a whole-range separation proof
                        // permits falling through to an unrecorded load.
                        unresolved_alias |= crate::kernel::memory_provenance::typed_ranges_disjoint_from_pointer_evidence(
                            &[run.range()], pointer, byte_width, self,
                        ).is_none();
                    }
                }
            }
        }
        for (cell_pointer, value) in candidates.entries(memory.cells.concrete()) {
            crate::instrumentation::record_deterministic_work(1);
            let met = consider(cell_pointer, value, &mut first_equal);
            unresolved_alias |= met
                && !first_equal
                    .as_ref()
                    .is_some_and(|(equal, _)| equal == cell_pointer);
        }
        if let Some((_, value)) = first_equal {
            return kind.reads_value(&value).then_some(value);
        }

        if unresolved_alias {
            return None;
        }

        if !memory.is_loadable_concretely(pointer, byte_width) {
            return None;
        }
        match kind {
            LoadKind::Int8 => Some(memory.symbolic_int8_load(pointer)),
            LoadKind::UInt8 => Some(memory.symbolic_uint8_load(pointer)),
            LoadKind::Int16 => Some(memory.symbolic_int16_load(pointer)),
            LoadKind::UInt16 => Some(memory.symbolic_uint16_load(pointer)),
            LoadKind::Bits32 => Some(memory.symbolic_int32_load(pointer)),
            LoadKind::Bits64 => Some(memory.symbolic_int64_load(pointer)),
            LoadKind::Int128 => {
                memory.symbolic_wide_integer_load(pointer, MachineIntegerType::Int128)
            }
            LoadKind::UInt128 => {
                memory.symbolic_wide_integer_load(pointer, MachineIntegerType::UInt128)
            }
            LoadKind::Float32 | LoadKind::Float64 | LoadKind::Pointer => None,
        }
    }
}
