use super::*;

impl Assumptions {
    pub(in crate::kernel) fn proves_memory_access(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.proves_memory_loadable(memory, pointer, &Bitvector32Term::Constant(byte_width))
    }

    pub(in crate::kernel) fn proves_memory_loadable(
        &self,
        memory: &CMemory,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        // The loadable prover is the one consumer of the extended DAG
        // bridging: a permission fact recorded at one snapshot spelling must
        // discharge a load extracted at another. Scoping the power here
        // keeps execution pruning and simp planning byte-identical to the
        // pre-arc path (see api.rs).
        crate::kernel::api::with_extended_dag_bridging(|| {
            self.proves_memory_loadable_inner(memory, base, bytes)
        })
    }

    fn proves_memory_loadable_inner(
        &self,
        memory: &CMemory,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        let _id_scope = AssumptionsIdScope::enter(self);
        // A loadability claim quantifies over the bytes in the range.  An
        // empty range has no accesses to justify, irrespective of whether
        // its base currently names a live block.
        if bytes.as_const() == Some(0) {
            return true;
        }
        if bytes
            .as_const()
            .is_some_and(|bytes| memory.access_in_bounds(base, bytes))
        {
            return true;
        }
        if let Some(byte_width) = bytes.as_const()
            && self.proves_access_from_memory_block(memory, base, byte_width)
        {
            return true;
        }
        if self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryLoadable {
                memory: range_memory,
                base: range_base,
                bytes: range_bytes,
            } = proposition
            else {
                return false;
            };

            memory_range_still_available(range_memory, memory, range_base)
                && self.proves_loadable_region_from_structural_range(
                    range_base,
                    range_bytes,
                    base,
                    bytes,
                )
        }) {
            return true;
        }

        if self
            .adjacent_loadable_region_facts(memory, base, bytes)
            .is_some()
        {
            return true;
        }

        if crate::kernel::api::contract_certification::quantified_int32_fact_certifies_loadable_range(
            self, memory, base, bytes,
        ) {
            return true;
        }

        if self.proves_memory_loadable_for_memory_resolution(memory, base, bytes) {
            return true;
        }

        let mut ranges = self
            .prop_facts
            .iter()
            .filter_map(|proposition| {
                let Proposition::CMemoryLoadable {
                    memory: range_memory,
                    base: range_base,
                    bytes: range_bytes,
                } = proposition
                else {
                    return None;
                };
                memory_range_still_available(range_memory, memory, range_base).then(|| {
                    let preferred = bytes.as_const() == Some(4)
                        && self
                            .pointer_element_index_from_base_for_memory_resolution(base, range_base)
                            .is_some();
                    (preferred, range_base, range_bytes)
                })
            })
            .collect::<Vec<_>>();
        ranges.sort_by_key(|(preferred, _, _)| !preferred);
        ranges.into_iter().any(|(_, range_base, range_bytes)| {
            self.proves_loadable_region_from_range(range_base, range_bytes, base, bytes)
        }) || bytes.as_const() == Some(4)
            && crate::kernel::api::contract_certification::quantified_int32_fact_certifies_loadable_cell(self, base)
    }

    /// A loadable prefix followed immediately by another loadable region
    /// certifies their concatenation. This is the range form produced when a
    /// store initializes the next cell of an already-initialized prefix.
    pub(super) fn adjacent_loadable_region_facts(
        &self,
        memory: &CMemory,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> Option<Vec<Proposition>> {
        let compatible = |fact_memory: &CMemory, fact_base: &Pointer| {
            fact_memory == memory
                // Stores change cell contents, not whether the surrounding
                // stack blocks or heap allocations are live. Pointer terms
                // retain their source snapshot, so a stored-to index field
                // cannot silently retarget the earlier region.
                || (fact_memory.blocks.get(&fact_base.block)
                    == memory.blocks.get(&fact_base.block)
                    && fact_memory.heap == memory.heap)
                || memory_range_still_available(fact_memory, memory, fact_base)
                || crate::kernel::api::c_memories_canonically_equal(fact_memory, memory)
                || crate::kernel::api::c_memories_connected_by_effects(fact_memory, memory, self)
        };
        let equal = |left: &Bitvector32Term, right: &Bitvector32Term| {
            let left = self.simplify_bitvector_under_assumptions(left);
            let right = self.simplify_bitvector_under_assumptions(right);
            left == right
                || self.decide(&ConditionTerm::Bitvector32Equal(
                    Box::new(left.clone()),
                    Box::new(right.clone()),
                )) == Some(true)
                || crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                    &left, &right, self,
                )
        };
        let mut regions = self
            .prop_facts
            .iter()
            .filter_map(|fact| {
                let Proposition::CMemoryLoadable {
                    memory: fact_memory,
                    base: fact_base,
                    bytes: fact_bytes,
                } = fact
                else {
                    return None;
                };
                (fact_base.block == base.block && compatible(fact_memory, fact_base)).then(|| {
                    (
                        Some(fact),
                        crate::kernel::api::canonicalize_pointer_loads(fact_base, 0),
                        fact_bytes.clone(),
                        fact_memory == memory
                            || crate::kernel::api::c_memories_canonically_equal(
                                fact_memory,
                                memory,
                            ),
                    )
                })
            })
            .collect::<Vec<_>>();
        // A materialized cell is loadable without a separate proposition.
        // Including it as a premise-free region lets a store extend an
        // already-loadable prefix in the same kernel rule.
        regions.extend(memory.cells.iter().filter_map(|(pointer, value)| {
            let byte_width = value.byte_width();
            (byte_width > 0 && memory.is_loadable_concretely(pointer, byte_width)).then(|| {
                (
                    None,
                    crate::kernel::api::canonicalize_pointer_loads(pointer, 0),
                    Bitvector32Term::Constant(byte_width),
                    true,
                )
            })
        }));
        let base = crate::kernel::api::canonicalize_pointer_loads(base, 0);
        for (prefix_index, (prefix_fact, prefix_base, prefix_bytes, prefix_current)) in
            regions.iter().enumerate()
        {
            let prefix_starts_at_goal = prefix_base == &base
                || crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                    prefix_base,
                    &base,
                    self,
                )
                || pointer_byte_offset_from_base(prefix_base, &base)
                    .is_some_and(|offset| equal(&offset, &Bitvector32Term::Constant(0)));
            if !prefix_starts_at_goal {
                continue;
            }
            for (suffix_index, (suffix_fact, suffix_base, suffix_bytes, suffix_current)) in
                regions.iter().enumerate()
            {
                if prefix_index == suffix_index {
                    continue;
                }
                // Historical proposition facts cannot be concatenated with
                // each other to manufacture a fact at the current snapshot.
                // The cross-snapshot case is specifically an earlier prefix
                // extended by a cell materialized by the current store.
                if prefix_fact.is_some()
                    && suffix_fact.is_some()
                    && !(*prefix_current && *suffix_current)
                {
                    continue;
                }
                let byte_concatenation = pointer_byte_offset_from_base(suffix_base, &base)
                    .is_some_and(|suffix_start| equal(&suffix_start, prefix_bytes))
                    && equal(
                        bytes,
                        &Bitvector32Term::add((*prefix_bytes).clone(), (*suffix_bytes).clone()),
                    );
                let element_concatenation = int32_element_count_from_bytes(prefix_bytes)
                    .zip(int32_element_count_from_bytes(suffix_bytes))
                    .zip(int32_element_count_from_bytes(bytes))
                    .is_some_and(|((prefix_count, suffix_count), goal_count)| {
                        let expected_suffix = base.offset_by_int32_elements(prefix_count.clone());
                        (suffix_base == &expected_suffix
                            || crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                                suffix_base,
                                &expected_suffix,
                                self,
                            ))
                            && equal(
                                &goal_count,
                                &Bitvector32Term::add(prefix_count, suffix_count),
                            )
                    });
                if byte_concatenation || element_concatenation {
                    return Some(
                        [*prefix_fact, *suffix_fact]
                            .into_iter()
                            .flatten()
                            .cloned()
                            .collect(),
                    );
                }
            }
        }
        None
    }

    pub(crate) fn proves_memory_loadable_for_memory_resolution(
        &self,
        memory: &CMemory,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        if bytes
            .as_const()
            .is_some_and(|bytes| memory.access_in_bounds(base, bytes))
        {
            return true;
        }
        self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryLoadable {
                memory: range_memory,
                base: range_base,
                bytes: range_bytes,
            } = proposition
            else {
                return false;
            };
            if !memory_range_still_available(range_memory, memory, range_base) {
                return false;
            }
            if range_base == base && range_bytes == bytes {
                return true;
            }
            let Some(byte_width) = bytes.as_const() else {
                return false;
            };
            if byte_width != 4 {
                return false;
            }
            let Some(element_count) = int32_element_count_from_bytes(range_bytes) else {
                return false;
            };
            pointer_in_range_for_memory_resolution(
                base,
                range_base,
                &Bitvector32Term::Constant(0),
                &element_count,
                self,
            )
        })
    }

    fn proves_loadable_region_from_structural_range(
        &self,
        range_base: &Pointer,
        range_bytes: &Bitvector32Term,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        if range_base == base && range_bytes == bytes {
            return true;
        }
        if let Some(byte_width) = bytes.as_const()
            && byte_width == 4
            && let Some(index) = base.element_index_from_base(range_base)
            && let Some(element_count) = int32_element_count_from_bytes(range_bytes)
        {
            let lower =
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone());
            let upper = ConditionTerm::signed_less_than(index.clone(), element_count.clone());
            if self.exact_condition_value(&lower) == Some(true)
                && self.exact_condition_value(&upper) == Some(true)
            {
                return true;
            }
            if let Some(index_constant) = signed_bitvector_constant(&index) {
                if let Some(element_count) = signed_bitvector_constant(&element_count) {
                    return 0 <= index_constant && index_constant < element_count;
                }
                if 0 <= index_constant && self.has_exact_order_path(&index, &element_count, true) {
                    return true;
                }
            }
            if let (
                Bitvector32Term::Subtract(target_index, range_start),
                Bitvector32Term::Subtract(range_end, count_start),
            ) = (&index, &element_count)
                && range_start == count_start
                && self.has_exact_order_path(range_start, target_index, false)
                && self.has_exact_order_path(target_index, range_end, true)
            {
                return true;
            }
        }
        let Some(byte_offset) = pointer_byte_offset_from_base(base, range_base) else {
            return false;
        };
        let (Some(byte_offset), Some(bytes), Some(range_bytes)) = (
            signed_bitvector_constant(&byte_offset),
            signed_bitvector_constant(bytes),
            signed_bitvector_constant(range_bytes),
        ) else {
            return false;
        };
        0 <= byte_offset && byte_offset + bytes <= range_bytes
    }

    pub(in crate::kernel) fn proves_loadable_region_from_range(
        &self,
        range_base: &Pointer,
        range_bytes: &Bitvector32Term,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        if range_base == base && range_bytes == bytes {
            return true;
        }

        if let Some(byte_width) = bytes.as_const()
            && self.proves_loadable_cell_from_region(range_base, range_bytes, base, byte_width)
        {
            return true;
        }

        if let Some(byte_offset) = pointer_byte_offset_from_base(base, range_base) {
            let access_end = Bitvector32Term::add(byte_offset.clone(), bytes.clone());
            return self.decide(&ConditionTerm::signed_greater_equal(
                byte_offset,
                Bitvector32Term::Constant(0),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(
                    access_end,
                    range_bytes.clone(),
                )) == Some(true);
        }

        false
    }

    pub(in crate::kernel) fn proves_access_from_memory_block(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        let Some(block) = memory.blocks.get(&pointer.block) else {
            return false;
        };
        let base = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        self.proves_loadable_cell_from_region(&base, block.size(), pointer, byte_width)
    }

    pub(in crate::kernel) fn proves_loadable_cell_from_region(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        if base.block != pointer.block {
            return false;
        }

        if byte_width == 4
            && let Some(index) = self.pointer_element_index_from_base(pointer, base)
            && let Some(element_count) = int32_element_count_from_bytes(bytes)
        {
            let lower_condition =
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone());
            let upper_condition = ConditionTerm::signed_less_than(index, element_count);
            let lower = self
                .exact_condition_value(&lower_condition)
                .or_else(|| self.decide(&lower_condition));
            let upper = self
                .exact_condition_value(&upper_condition)
                .or_else(|| self.decide(&upper_condition));
            if lower == Some(true) && upper == Some(true) {
                return true;
            }
        }

        if let Some(byte_offset) = pointer_byte_offset_from_base(pointer, base) {
            let access_end =
                Bitvector32Term::add(byte_offset.clone(), Bitvector32Term::Constant(byte_width));
            return self.decide(&ConditionTerm::signed_greater_equal(
                byte_offset,
                Bitvector32Term::Constant(0),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(access_end, bytes.clone()))
                    == Some(true);
        }

        false
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                self.pointer_in_range(left, left_base, left_start, left_end)
                    && self.pointer_in_range(right, right_base, right_start, right_end)
                    || self.pointer_in_range(right, left_base, left_start, left_end)
                        && self.pointer_in_range(left, right_base, right_start, right_end)
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                self.pointer_in_range(
                    left,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                ) && self.pointer_in_range(
                    right,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                ) || self.pointer_in_range(
                    right,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                ) && self.pointer_in_range(
                    left,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                )
            }
            _ => false,
        }) || self.proves_resource_separate(
            &CResource::Memory(CMemoryRange::new(
                left.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &CResource::Memory(CMemoryRange::new(
                right.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
        )
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_explicit_range_for_memory_resolution(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        crate::kernel::reasoning::with_memory_resolution_fuel(|| {
            self.pointers_proven_disjoint_by_explicit_range_for_memory_resolution_with_depth(
                left, right, 0,
            )
        })
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_shallow_explicit_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                self.pointer_in_range_by_shallow_fact_graph(left, left_base, left_start, left_end)
                    && self.pointer_in_range_by_shallow_fact_graph(
                        right,
                        right_base,
                        right_start,
                        right_end,
                    )
                    || self.pointer_in_range_by_shallow_fact_graph(
                        right, left_base, left_start, left_end,
                    ) && self.pointer_in_range_by_shallow_fact_graph(
                        left,
                        right_base,
                        right_start,
                        right_end,
                    )
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                self.pointer_in_range_by_shallow_fact_graph(
                    left,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                ) && self.pointer_in_range_by_shallow_fact_graph(
                    right,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                ) || self.pointer_in_range_by_shallow_fact_graph(
                    right,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                ) && self.pointer_in_range_by_shallow_fact_graph(
                    left,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                )
            }
            _ => false,
        })
    }

    fn pointer_in_range_by_shallow_fact_graph(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        if pointer_in_range_shallow(pointer, base, start, end) {
            return true;
        }
        if pointer.block != base.block {
            return false;
        }
        let offset_matches = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            pointer_offsets_match_by_shallow_fact_graph(left, right, self)
        };
        let index = match &pointer.offset {
            PointerOffsetTerm::Add(left, right) if offset_matches(left, &base.offset) => {
                int32_element_index_from_offset(right)
            }
            PointerOffsetTerm::Add(left, right) if offset_matches(right, &base.offset) => {
                int32_element_index_from_offset(left)
            }
            _ if offset_matches(&pointer.offset, &base.offset) => {
                Some(Bitvector32Term::Constant(0))
            }
            _ => None,
        };
        let Some(index) = index else {
            return false;
        };
        let (Some(offset), Some(length)) = (
            affine_bitvector_difference_constant(&index, start),
            affine_bitvector_difference_constant(end, start),
        ) else {
            return false;
        };
        0 <= offset && offset < length
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_explicit_range_for_memory_resolution_with_depth(
        &self,
        left: &Pointer,
        right: &Pointer,
        depth: usize,
    ) -> bool {
        // Most execution-time separation certificates name the exact ranges
        // being accessed. Resolve those structurally before asking the
        // snapshot-aware containment prover, which may itself inspect memory
        // loads and is deliberately the more expensive second phase.
        if self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                pointer_in_range_shallow(left, left_base, left_start, left_end)
                    && pointer_in_range_shallow(right, right_base, right_start, right_end)
                    || pointer_in_range_shallow(right, left_base, left_start, left_end)
                        && pointer_in_range_shallow(left, right_base, right_start, right_end)
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                pointer_in_memory_range_shallow(left, left_range)
                    && pointer_in_memory_range_shallow(right, right_range)
                    || pointer_in_memory_range_shallow(right, left_range)
                        && pointer_in_memory_range_shallow(left, right_range)
            }
            _ => false,
        }) {
            return true;
        }

        // The recursive second phase re-enters offset-equality reasoning.
        // Keep it shallow: nested queries past the expensive-edge budget use
        // the shallow answer above, which bounds the mutual recursion without
        // losing the direct certificates.
        if depth > crate::kernel::reasoning::MEMORY_RESOLUTION_EXPENSIVE_DEPTH_LIMIT {
            return false;
        }
        self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                pointer_in_range_for_memory_resolution_with_depth(
                    left, left_base, left_start, left_end, self, depth,
                ) && pointer_in_range_for_memory_resolution_with_depth(
                    right,
                    right_base,
                    right_start,
                    right_end,
                    self,
                    depth,
                ) || pointer_in_range_for_memory_resolution_with_depth(
                    left,
                    right_base,
                    right_start,
                    right_end,
                    self,
                    depth,
                ) && pointer_in_range_for_memory_resolution_with_depth(
                    right, left_base, left_start, left_end, self, depth,
                )
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                pointer_in_memory_range_for_memory_resolution_with_depth(
                    left, left_range, self, depth,
                ) && pointer_in_memory_range_for_memory_resolution_with_depth(
                    right,
                    right_range,
                    self,
                    depth,
                ) || pointer_in_memory_range_for_memory_resolution_with_depth(
                    right, left_range, self, depth,
                ) && pointer_in_memory_range_for_memory_resolution_with_depth(
                    left,
                    right_range,
                    self,
                    depth,
                )
            }
            _ => false,
        })
    }

    pub(in crate::kernel) fn memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
        &self,
        left: &CMemoryRange,
        right: &CMemoryRange,
    ) -> bool {
        crate::kernel::reasoning::with_memory_resolution_fuel(|| {
            self.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution_with_depth(
                left, right, 0,
            )
        })
    }

    fn memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution_with_depth(
        &self,
        left: &CMemoryRange,
        right: &CMemoryRange,
        depth: usize,
    ) -> bool {
        // Prefer certificates where one queried range is structurally inside
        // one side. This gives the other side a single, directed equivalence
        // check instead of exploring both orientations of every separation
        // fact before reaching the structurally relevant certificate.
        if self.prop_facts.iter().any(|proposition| {
            let Proposition::CResourceSeparate {
                left: CResource::Memory(fact_left),
                right: CResource::Memory(fact_right),
            } = proposition
            else {
                return false;
            };
            memory_range_shallowly_contained(left, fact_left)
                && memory_range_contained_for_memory_resolution_with_depth(
                    right, fact_right, self, depth,
                )
                || memory_range_shallowly_contained(right, fact_right)
                    && memory_range_contained_for_memory_resolution_with_depth(
                        left, fact_left, self, depth,
                    )
                || memory_range_shallowly_contained(right, fact_left)
                    && memory_range_contained_for_memory_resolution_with_depth(
                        left, fact_right, self, depth,
                    )
                || memory_range_shallowly_contained(left, fact_right)
                    && memory_range_contained_for_memory_resolution_with_depth(
                        right, fact_left, self, depth,
                    )
        }) {
            return true;
        }
        if depth > crate::kernel::reasoning::MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT {
            return false;
        }

        self.prop_facts.iter().any(|proposition| {
            let Proposition::CResourceSeparate {
                left: CResource::Memory(fact_left),
                right: CResource::Memory(fact_right),
            } = proposition
            else {
                return false;
            };
            memory_range_contained_for_memory_resolution_with_depth(left, fact_left, self, depth)
                && memory_range_contained_for_memory_resolution_with_depth(
                    right, fact_right, self, depth,
                )
                || memory_range_contained_for_memory_resolution_with_depth(
                    right, fact_left, self, depth,
                ) && memory_range_contained_for_memory_resolution_with_depth(
                    left, fact_right, self, depth,
                )
        })
    }

    fn pointer_element_index_from_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Bitvector32Term> {
        if pointer.block != base.block {
            return None;
        }
        if let Some(index) =
            self.pointer_element_index_from_base_for_memory_resolution(pointer, base)
        {
            return Some(index);
        }

        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if self.decide(&ConditionTerm::pointer_offset_equal(
                left.as_ref().clone(),
                base.offset.clone(),
            )) == Some(true)
            {
                return int32_element_index_from_offset(right);
            }
            if self.decide(&ConditionTerm::pointer_offset_equal(
                right.as_ref().clone(),
                base.offset.clone(),
            )) == Some(true)
            {
                return int32_element_index_from_offset(left);
            }
        }

        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                left.as_ref().clone(),
            )) == Some(true)
            {
                return int32_element_index_from_offset(right)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
            if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                right.as_ref().clone(),
            )) == Some(true)
            {
                return int32_element_index_from_offset(left)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
        }

        if self.decide(&ConditionTerm::pointer_offset_equal(
            pointer.offset.clone(),
            base.offset.clone(),
        )) == Some(true)
        {
            return Some(Bitvector32Term::Constant(0));
        }

        pointer.element_index_from_base(base)
    }

    fn pointer_element_index_from_base_for_memory_resolution(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Bitvector32Term> {
        if pointer.block != base.block {
            return None;
        }
        if pointer.offset == base.offset {
            return Some(Bitvector32Term::Constant(0));
        }
        let offsets_match_for_resolution = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            left == right
                || crate::kernel::reasoning::with_memory_resolution_fuel(|| {
                    crate::kernel::reasoning::pointer_offsets_equal_for_memory_resolution(
                        left, right, self, 0,
                    ) == Some(true)
                })
        };
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if offsets_match_for_resolution(left, &base.offset) {
                return int32_element_index_from_offset(right);
            }
            if offsets_match_for_resolution(right, &base.offset) {
                return int32_element_index_from_offset(left);
            }
        }
        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if offsets_match_for_resolution(&pointer.offset, left) {
                return int32_element_index_from_offset(right)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
            if offsets_match_for_resolution(&pointer.offset, right) {
                return int32_element_index_from_offset(left)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
        }
        None
    }

    pub(in crate::kernel) fn pointer_in_range(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        let range_base = base.offset_by_int32_elements(start.clone());
        if let Some(index) = self.pointer_element_index_from_base(pointer, &range_base) {
            let range_length = Bitvector32Term::subtract(end.clone(), start.clone());
            if self.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                index.clone(),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_than(index, range_length)) == Some(true)
            {
                return true;
            }
        }

        let Some(index) = self.pointer_element_index_from_base(pointer, base) else {
            return false;
        };
        self.decide(&ConditionTerm::signed_less_equal(
            start.clone(),
            index.clone(),
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(index, end.clone())) == Some(true)
    }

    pub(in crate::kernel) fn proves_memory_disjoint(
        &self,
        left_base: &Pointer,
        left_start: &Bitvector32Term,
        left_end: &Bitvector32Term,
        right_base: &Pointer,
        right_start: &Bitvector32Term,
        right_end: &Bitvector32Term,
    ) -> bool {
        let left = CMemoryRange::new(left_base.clone(), left_start.clone(), left_end.clone());
        let right = CMemoryRange::new(right_base.clone(), right_start.clone(), right_end.clone());
        self.range_covered_by_disjoint_fact_ranges(&left, &right)
            || self.range_covered_by_disjoint_fact_ranges(&right, &left)
    }

    pub(in crate::kernel) fn proves_memory_disjoint_from_resource_separate(
        &self,
        left_base: &Pointer,
        left_start: &Bitvector32Term,
        left_end: &Bitvector32Term,
        right_base: &Pointer,
        right_start: &Bitvector32Term,
        right_end: &Bitvector32Term,
    ) -> bool {
        let left = CMemoryRange::new(left_base.clone(), left_start.clone(), left_end.clone());
        let right = CMemoryRange::new(right_base.clone(), right_start.clone(), right_end.clone());
        self.proves_resource_separate(
            &CResource::Memory(left.clone()),
            &CResource::Memory(right.clone()),
        ) || self.range_covered_by_resource_separate_ranges(&left, &right)
            || self.range_covered_by_resource_separate_ranges(&right, &left)
    }

    pub(in crate::kernel) fn proves_resource_contains(
        &self,
        parent: &CResource,
        child: &CResource,
    ) -> bool {
        crate::kernel::reasoning::with_resource_prover_fuel(|| {
            self.proves_resource_contains_inner(parent, child)
        })
    }

    fn proves_resource_contains_inner(&self, parent: &CResource, child: &CResource) -> bool {
        if self.resource_contains_builtin(parent, child) {
            return true;
        }

        let mut seen = BTreeSet::new();
        let mut stack = vec![parent.clone()];
        while let Some(current) = stack.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            if !crate::kernel::reasoning::consume_resource_prover_fuel() {
                return false;
            }
            if self.resource_contains_builtin(&current, child) {
                return true;
            }
            for proposition in &self.prop_facts {
                let Proposition::CResourceContains {
                    parent: fact_parent,
                    child: fact_child,
                } = proposition
                else {
                    continue;
                };
                if self.resource_contains_builtin(&current, fact_parent) {
                    stack.push(fact_child.clone());
                }
            }
        }
        false
    }

    pub(in crate::kernel) fn proves_resource_separate(
        &self,
        left: &CResource,
        right: &CResource,
    ) -> bool {
        crate::kernel::reasoning::with_resource_prover_fuel(|| {
            self.proves_resource_separate_inner(left, right)
        })
    }

    fn proves_resource_separate_inner(&self, left: &CResource, right: &CResource) -> bool {
        if let (CResource::Memory(left), CResource::Memory(right)) = (left, right)
            && left.base().blocks_proven_distinct(right.base())
        {
            return true;
        }

        if let (CResource::Memory(left), CResource::Memory(right)) = (left, right)
            && left.base() == right.base()
            && let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
                signed_bitvector_constant(left.start()),
                signed_bitvector_constant(left.end()),
                signed_bitvector_constant(right.start()),
                signed_bitvector_constant(right.end()),
            )
            && (left_end <= right_start || right_end <= left_start)
        {
            return true;
        }

        if self.prop_facts.iter().any(|proposition| {
            let Proposition::CResourceSeparate {
                left: fact_left,
                right: fact_right,
            } = proposition
            else {
                return false;
            };
            crate::kernel::reasoning::consume_resource_prover_fuel()
                && (self.proves_resource_contains_inner(fact_left, left)
                    && self.proves_resource_contains_inner(fact_right, right)
                    || self.proves_resource_contains_inner(fact_left, right)
                        && self.proves_resource_contains_inner(fact_right, left))
        }) {
            return true;
        }

        if let (CResource::Memory(left), CResource::Memory(right)) = (left, right) {
            return self.range_covered_by_resource_separate_ranges(left, right)
                || self.range_covered_by_resource_separate_ranges(right, left);
        }

        false
    }

    fn resource_contains_builtin(&self, parent: &CResource, child: &CResource) -> bool {
        if parent == child {
            return true;
        }
        if !crate::kernel::reasoning::consume_resource_prover_fuel() {
            return false;
        }
        let (CResource::Memory(parent), CResource::Memory(child)) = (parent, child) else {
            return false;
        };
        if self.memory_ranges_proven_equal(parent, child) {
            return true;
        }
        if Bitvector32Term::subtract(child.end.clone(), child.start.clone()).as_const() == Some(1) {
            let child_pointer = child.base.offset_by_int32_elements(child.start.clone());
            return self.pointer_in_range(
                &child_pointer,
                parent.base(),
                parent.start(),
                parent.end(),
            );
        }
        self.range_covered_by_fact_range(child, parent.base(), parent.start(), parent.end())
    }

    fn memory_ranges_proven_equal(&self, left: &CMemoryRange, right: &CMemoryRange) -> bool {
        let left_length = memory_range_length_term(left);
        let right_length = memory_range_length_term(right);
        self.pointers_proven_equal_for_fact_transport(left.base(), right.base())
            && self.bitvector_terms_equal_for_fact_transport(left.start(), right.start())
            && self.bitvector_terms_equal_for_fact_transport(&left_length, &right_length)
    }

    fn pointers_proven_equal_for_fact_transport(&self, left: &Pointer, right: &Pointer) -> bool {
        if pointers_proven_equal(left, right, self) {
            return true;
        }
        if left.block != right.block {
            return false;
        }
        let (Some(left), Some(right)) = (
            int32_element_index_from_offset(&left.offset),
            int32_element_index_from_offset(&right.offset),
        ) else {
            return false;
        };
        self.bitvector_terms_equal_for_fact_transport(&left, &right)
    }

    fn bitvector_terms_equal_for_fact_transport(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        // Snapshot-aware endpoints are valid only for bounded fact transport.
        // Keeping them out of the global equality graph avoids recursive
        // memory resolution and changes to symbolic execution paths.
        if self.bitvector_terms_equal_for_transport(left, right)
            || self.bitvector_terms_equal_from_snapshot_facts(left, right)
        {
            return true;
        }

        match (left, right) {
            (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
            | (
                Bitvector32Term::Subtract(left_a, left_b),
                Bitvector32Term::Subtract(right_a, right_b),
            )
            | (
                Bitvector32Term::Multiply(left_a, left_b),
                Bitvector32Term::Multiply(right_a, right_b),
            ) => {
                self.bitvector_terms_equal_for_fact_transport(left_a, right_a)
                    && self.bitvector_terms_equal_for_fact_transport(left_b, right_b)
            }
            _ => false,
        }
    }

    fn bitvector_terms_equal_from_snapshot_facts(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let endpoint_matches = |left: &Bitvector32Term, right: &Bitvector32Term| {
            left == right || memory_load_terms_equal_for_fact_transport(left, right, self)
        };
        let mut seen = BTreeSet::new();
        let mut stack = vec![left.clone()];
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if endpoint_matches(&term, right) {
                return true;
            }
            for (condition, value) in &self.condition_facts {
                if !*value {
                    continue;
                }
                let (fact_left, fact_right) = match condition {
                    ConditionTerm::Bitvector32Equal(fact_left, fact_right) => {
                        (fact_left.as_ref().clone(), fact_right.as_ref().clone())
                    }
                    ConditionTerm::PointerOffsetEqual(fact_left, fact_right) => {
                        let (Some(fact_left), Some(fact_right)) = (
                            int32_element_index_from_offset(fact_left),
                            int32_element_index_from_offset(fact_right),
                        ) else {
                            continue;
                        };
                        (fact_left, fact_right)
                    }
                    _ => continue,
                };
                if endpoint_matches(&fact_left, &term) {
                    stack.push(fact_right.clone());
                }
                if endpoint_matches(&fact_right, &term) {
                    stack.push(fact_left);
                }
            }
        }
        false
    }

    fn range_covered_by_resource_separate_ranges(
        &self,
        target: &CMemoryRange,
        other: &CMemoryRange,
    ) -> bool {
        let mut intervals = Vec::new();
        for proposition in &self.prop_facts {
            let Proposition::CResourceSeparate { left, right } = proposition else {
                continue;
            };

            if self.proves_resource_contains(right, &CResource::Memory(other.clone()))
                && let CResource::Memory(left) = left
                && let Some(interval) = self.fact_range_interval_on_target(
                    target,
                    left.base(),
                    left.start(),
                    left.end(),
                )
            {
                intervals.push(interval);
            }

            if self.proves_resource_contains(left, &CResource::Memory(other.clone()))
                && let CResource::Memory(right) = right
                && let Some(interval) = self.fact_range_interval_on_target(
                    target,
                    right.base(),
                    right.start(),
                    right.end(),
                )
            {
                intervals.push(interval);
            }
        }
        range_intervals_cover_target(target, intervals)
    }

    fn range_covered_by_disjoint_fact_ranges(
        &self,
        target: &CMemoryRange,
        other: &CMemoryRange,
    ) -> bool {
        let mut intervals = Vec::new();
        for proposition in &self.prop_facts {
            let Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } = proposition
            else {
                continue;
            };

            if self.range_covered_by_fact_range(other, right_base, right_start, right_end)
                && let Some(interval) =
                    self.fact_range_interval_on_target(target, left_base, left_start, left_end)
            {
                intervals.push(interval);
            }
            if self.range_covered_by_fact_range(other, left_base, left_start, left_end)
                && let Some(interval) =
                    self.fact_range_interval_on_target(target, right_base, right_start, right_end)
            {
                intervals.push(interval);
            }
        }
        range_intervals_cover_target(target, intervals)
    }

    fn fact_range_interval_on_target(
        &self,
        target: &CMemoryRange,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> Option<(i64, i64)> {
        if target.base.block != base.block {
            return None;
        }
        let base_delta = self.pointer_element_index_from_base(base, &target.base)?;
        let start = Bitvector32Term::add(base_delta.clone(), start.clone());
        let end = Bitvector32Term::add(base_delta, end.clone());
        Some((
            signed_bitvector_constant(&start)?,
            signed_bitvector_constant(&end)?,
        ))
    }

    pub(in crate::kernel) fn pointer_access_in_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        // Scalar and pointer fields both occupy one surface element: ranges
        // count fields, so a pointer-width access at an in-range element
        // index is authorized exactly like an int32 access.
        if (byte_width == 4 || byte_width == crate::kernel::C_POINTER_BYTE_WIDTH)
            && let Some(index) = pointer.element_index_from_base(base)
            && self.decide(&ConditionTerm::signed_less_equal(
                start.clone(),
                index.clone(),
            )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_than(index, end.clone())) == Some(true)
        {
            return true;
        }

        if byte_width.is_multiple_of(4) {
            let range_base = base.offset_by_int32_elements(start.clone());
            let access_length = Bitvector32Term::Constant(byte_width / 4);
            if pointer == &range_base
                && end == &Bitvector32Term::add(start.clone(), access_length.clone())
            {
                return true;
            }
            if let Some(index) = self.pointer_element_index_from_base(pointer, &range_base) {
                let range_length = Bitvector32Term::subtract(end.clone(), start.clone());
                let access_end = Bitvector32Term::add(index.clone(), access_length);
                if self.decide(&ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    index,
                )) == Some(true)
                    && self.decide(&ConditionTerm::signed_less_equal(access_end, range_length))
                        == Some(true)
                {
                    return true;
                }
            }
        }

        if let Some(index) = self.pointer_element_index_from_base(pointer, base) {
            if byte_width == 4 {
                return self.decide(&ConditionTerm::signed_less_equal(
                    start.clone(),
                    index.clone(),
                )) == Some(true)
                    && self.decide(&ConditionTerm::signed_less_than(index, end.clone()))
                        == Some(true);
            }
            if byte_width > 4 && byte_width.is_multiple_of(4) {
                let element_width = Bitvector32Term::Constant(byte_width / 4);
                let access_end = Bitvector32Term::add(index.clone(), element_width);
                return self.decide(&ConditionTerm::signed_less_equal(start.clone(), index))
                    == Some(true)
                    && self.decide(&ConditionTerm::signed_less_equal(access_end, end.clone()))
                        == Some(true);
            }
        }

        if byte_width == 1 {
            let Some(index) = pointer_byte_offset_from_base(pointer, base) else {
                return false;
            };
            return self.decide(&ConditionTerm::signed_less_equal(
                start.clone(),
                index.clone(),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_than(index, end.clone())) == Some(true);
        }

        false
    }

    pub(in crate::kernel) fn ranges_proven_disjoint_from_pointer(
        &self,
        ranges: &[CMemoryRange],
        pointer: &Pointer,
    ) -> bool {
        ranges
            .iter()
            .all(|range| self.range_proven_disjoint_from_pointer(range, pointer))
    }

    pub(in crate::kernel) fn ranges_directly_disjoint_from_pointer(
        &self,
        ranges: &[CMemoryRange],
        pointer: &Pointer,
    ) -> bool {
        ranges.iter().all(|range| {
            if range.base.blocks_proven_distinct(pointer) {
                return true;
            }
            if pointer_in_memory_range_shallow(pointer, range) {
                return false;
            }
            let direct_index = self.direct_pointer_element_index_from_base(pointer, &range.base);
            if let Some(index) = direct_index.as_ref()
                && let (Some(index), Some(start), Some(end)) = (
                    signed_bitvector_constant(index),
                    signed_bitvector_constant(&range.start),
                    signed_bitvector_constant(&range.end),
                )
            {
                return index < start || end <= index;
            }
            if self.prop_facts.iter().any(|proposition| match proposition {
                Proposition::CMemoryDisjoint {
                    left_base,
                    left_start,
                    left_end,
                    right_base,
                    right_start,
                    right_end,
                } => {
                    memory_range_shallowly_contained_in_parts(
                        range, left_base, left_start, left_end,
                    ) && pointer_in_range_shallow(pointer, right_base, right_start, right_end)
                        || memory_range_shallowly_contained_in_parts(
                            range,
                            right_base,
                            right_start,
                            right_end,
                        ) && pointer_in_range_shallow(pointer, left_base, left_start, left_end)
                }
                Proposition::CResourceSeparate {
                    left: CResource::Memory(left_range),
                    right: CResource::Memory(right_range),
                } => {
                    memory_range_shallowly_contained(range, left_range)
                        && (pointer_in_memory_range_shallow(pointer, right_range)
                            || self.pointer_directly_in_memory_range(pointer, right_range))
                        || memory_range_shallowly_contained(range, right_range)
                            && (pointer_in_memory_range_shallow(pointer, left_range)
                                || self.pointer_directly_in_memory_range(pointer, left_range))
                        || pointer_in_memory_range_shallow(pointer, left_range)
                            && memory_range_contained_for_memory_resolution(
                                range,
                                right_range,
                                self,
                            )
                        || pointer_in_memory_range_shallow(pointer, right_range)
                            && memory_range_contained_for_memory_resolution(range, left_range, self)
                        || self.pointer_directly_in_memory_range(pointer, left_range)
                            && memory_range_contained_for_memory_resolution(
                                range,
                                right_range,
                                self,
                            )
                        || self.pointer_directly_in_memory_range(pointer, right_range)
                            && memory_range_contained_for_memory_resolution(range, left_range, self)
                }
                _ => false,
            }) {
                return true;
            }

            let Some(index) = direct_index else {
                return false;
            };
            bitvector_index_outside_range_shallow(&index, &range.start, &range.end, self)
        })
    }

    fn direct_pointer_element_index_from_base(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Bitvector32Term> {
        if pointer.block != base.block {
            return None;
        }
        let offsets_equal = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            if left == right {
                return true;
            }
            match (left, right) {
                (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) => {
                    left_width == right_width && self.bitvector_terms_equal_from_facts(left, right)
                }
                _ => false,
            }
        };
        if offsets_equal(&pointer.offset, &base.offset) {
            return Some(Bitvector32Term::Constant(0));
        }
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if offsets_equal(left, &base.offset) {
                return int32_element_index_from_offset(right);
            }
            if offsets_equal(right, &base.offset) {
                return int32_element_index_from_offset(left);
            }
        }
        pointer.element_index_from_base(base)
    }

    fn pointer_directly_in_memory_range(&self, pointer: &Pointer, range: &CMemoryRange) -> bool {
        let Some(index) = self.direct_pointer_element_index_from_base(pointer, &range.base) else {
            return false;
        };
        if let (Some(index), Some(start), Some(end)) = (
            signed_bitvector_constant(&index),
            signed_bitvector_constant(&range.start),
            signed_bitvector_constant(&range.end),
        ) {
            return start <= index && index < end;
        }
        bitvector_index_in_range_shallow(&index, &range.start, &range.end, self)
    }

    fn range_proven_disjoint_from_pointer(&self, range: &CMemoryRange, pointer: &Pointer) -> bool {
        if range.base.blocks_proven_distinct(pointer) {
            return true;
        }
        if pointer_in_memory_range_shallow(pointer, range) {
            return false;
        }

        if self.prop_facts.iter().any(|proposition| match proposition {
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                memory_range_shallowly_contained_in_parts(range, left_base, left_start, left_end)
                    && pointer_in_range_shallow(pointer, right_base, right_start, right_end)
                    || memory_range_shallowly_contained_in_parts(
                        range,
                        right_base,
                        right_start,
                        right_end,
                    ) && pointer_in_range_shallow(pointer, left_base, left_start, left_end)
            }
            Proposition::CResourceSeparate {
                left: CResource::Memory(left_range),
                right: CResource::Memory(right_range),
            } => {
                memory_range_shallowly_contained(range, left_range)
                    && pointer_in_memory_range_shallow(pointer, right_range)
                    || memory_range_shallowly_contained(range, right_range)
                        && pointer_in_memory_range_shallow(pointer, left_range)
            }
            _ => false,
        }) {
            return true;
        }

        let pointer_range = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        if self.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            range,
            &pointer_range,
        ) {
            return true;
        }

        if let PointerOffsetTerm::Add(left, right) = &range.base.offset {
            let forward_offset = if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                left.as_ref().clone(),
            )) == Some(true)
            {
                int32_element_index_from_offset(right)
            } else if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                right.as_ref().clone(),
            )) == Some(true)
            {
                int32_element_index_from_offset(left)
            } else {
                None
            };
            if let Some(forward_offset) = forward_offset {
                let range_start = Bitvector32Term::add(forward_offset, range.start.clone());
                if self.decide(&ConditionTerm::signed_less_than(
                    Bitvector32Term::Constant(0),
                    range_start,
                )) == Some(true)
                {
                    return true;
                }
            }
        }

        if let Some(index) = self.direct_pointer_element_index_from_base(pointer, &range.base) {
            // Literal constants first; otherwise resolve each bound through
            // equality facts with per-load snapshot bridging, so a range
            // like data[split..split+1] with split provably 1 proves
            // disjoint from data[0].
            let resolve = |term: &Bitvector32Term| {
                signed_bitvector_constant(term)
                    .or_else(|| self.known_signed_constant_after_normalization(term))
            };
            if let (Some(index), Some(start), Some(end)) =
                (resolve(&index), resolve(&range.start), resolve(&range.end))
                && (index < start || end <= index)
            {
                return true;
            }
            if self.decide(&ConditionTerm::signed_less_than(
                index.clone(),
                range.start.clone(),
            )) == Some(true)
                || self.decide(&ConditionTerm::signed_less_equal(range.end.clone(), index))
                    == Some(true)
            {
                return true;
            }
        }

        self.prop_facts.iter().any(|proposition| {
            let Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } = proposition
            else {
                return false;
            };

            self.range_covered_by_fact_range(range, left_base, left_start, left_end)
                && self.pointer_in_range(pointer, right_base, right_start, right_end)
                || self.range_covered_by_fact_range(range, right_base, right_start, right_end)
                    && self.pointer_in_range(pointer, left_base, left_start, left_end)
        })
    }

    pub(in crate::kernel) fn range_covered_by_fact_range(
        &self,
        range: &CMemoryRange,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
    ) -> bool {
        if &range.base == base {
            let base_delta = relative_range_offset(range.start(), start);
            let range_length =
                Bitvector32Term::subtract(range.end().clone(), range.start().clone());
            let fact_length = Bitvector32Term::subtract(end.clone(), start.clone());
            let end_is_covered = if range_length == Bitvector32Term::Constant(1) {
                self.decide(&ConditionTerm::signed_less_than(
                    base_delta.clone(),
                    fact_length.clone(),
                )) == Some(true)
            } else {
                let range_end = Bitvector32Term::add(base_delta.clone(), range_length);
                self.decide(&ConditionTerm::signed_less_equal(range_end, fact_length)) == Some(true)
            };
            if self.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                base_delta,
            )) == Some(true)
                && end_is_covered
            {
                return true;
            }
        }

        let fact_base = base.offset_by_int32_elements(start.clone());
        let range_base = range.base.offset_by_int32_elements(range.start.clone());
        if let Some(base_delta) = self.pointer_element_index_from_base(&range_base, &fact_base) {
            let range_length = Bitvector32Term::subtract(range.end.clone(), range.start.clone());
            let fact_length = Bitvector32Term::subtract(end.clone(), start.clone());
            let range_end = Bitvector32Term::add(base_delta.clone(), range_length);
            if self.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                base_delta,
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(range_end, fact_length))
                    == Some(true)
            {
                return true;
            }
        }

        let Some(base_delta) = self.pointer_element_index_from_base(&range.base, base) else {
            return false;
        };
        let range_start = Bitvector32Term::add(base_delta.clone(), range.start.clone());
        let range_end = Bitvector32Term::add(base_delta, range.end.clone());

        self.decide(&ConditionTerm::signed_less_equal(
            start.clone(),
            range_start,
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_equal(range_end, end.clone())) == Some(true)
    }
}
