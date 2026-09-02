use super::*;

#[cfg(test)]
thread_local! {
    static PROOF_AWARE_POINTER_INDEX_QUERIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

thread_local! {
    /// Composite resource definitions available to internal frame evidence.
    ///
    /// Frame reasoning asks whether a call's mutable ranges or a store's
    /// written cell can touch a loaded pointer. When the pointer sits inside
    /// a composite's footprint, answering needs the composite's definition —
    /// but publishing that expansion as an ambient fact would also make a
    /// user's `separate(...)` goal provable without the `observe(...)` chain
    /// the language requires for nested composites (pinned by
    /// `mdtests/composite_resource_nested_observe_not_automatic.md`).
    ///
    /// Separation is a property, not an authority grant: consulting the
    /// definitions here decides disjointness for framing without making any
    /// resource usable, so this channel is deliberately readable only by the
    /// frame-evidence prover in this module.
    static FRAME_COMPOSITE_DEFINITIONS: std::cell::RefCell<
        Vec<std::sync::Arc<Vec<CCompositeResourceDefinition>>>,
    > = const { std::cell::RefCell::new(Vec::new()) };
}

/// Arms [`FRAME_COMPOSITE_DEFINITIONS`] for the guard's lifetime. Definitions
/// are file-global, so one guard covers a whole verification.
#[must_use = "definitions stay armed only while the guard is alive"]
pub struct FrameCompositeDefinitionsGuard {
    _private: (),
}

impl Drop for FrameCompositeDefinitionsGuard {
    fn drop(&mut self) {
        FRAME_COMPOSITE_DEFINITIONS.with(|definitions| {
            definitions.borrow_mut().pop();
        });
    }
}

pub fn arm_frame_composite_definitions(
    definitions: Vec<CCompositeResourceDefinition>,
) -> FrameCompositeDefinitionsGuard {
    FRAME_COMPOSITE_DEFINITIONS
        .with(|armed| armed.borrow_mut().push(std::sync::Arc::new(definitions)));
    FrameCompositeDefinitionsGuard { _private: () }
}

thread_local! {
    /// Composite expansions keyed by composition storage address and
    /// interned memory id; see `frame_expanded_compositions`.
    static EXPANSION_MEMO: std::cell::RefCell<
        std::collections::HashMap<(usize, (u32, u32)), (ResourceContext, Option<ResourceContext>)>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Empties the frame-expansion memo at a verification boundary: its keys
/// carry arena ids, which a fresh arena reuses.
pub(crate) fn clear_frame_expansion_memo() {
    EXPANSION_MEMO.with(|memo| memo.borrow_mut().clear());
}

fn frame_composite_definitions() -> Option<std::sync::Arc<Vec<CCompositeResourceDefinition>>> {
    FRAME_COMPOSITE_DEFINITIONS.with(|definitions| definitions.borrow().last().cloned())
}

impl PureFactContext {
    #[cfg(test)]
    pub(crate) fn reset_proof_aware_pointer_index_queries() {
        PROOF_AWARE_POINTER_INDEX_QUERIES.with(|queries| queries.set(0));
    }

    #[cfg(test)]
    pub(crate) fn proof_aware_pointer_index_queries() -> usize {
        PROOF_AWARE_POINTER_INDEX_QUERIES.with(std::cell::Cell::get)
    }

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
        // bridging: a loadability fact carrying one memory snapshot must
        // discharge a load carrying another. Scoping the power here
        // keeps execution pruning and simp planning byte-identical to the
        // pre-arc path (see api.rs).
        let proved = crate::kernel::api::with_extended_dag_bridging(|| {
            self.proves_memory_loadable_inner(memory, base, bytes)
        });
        if proved {
            record_implicit_reasoning_provenance(
                self,
                &Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: base.clone(),
                    bytes: bytes.clone(),
                },
            );
        }
        proved
    }

    fn proves_memory_loadable_inner(
        &self,
        memory: &CMemory,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        let _id_scope = PureFactContextIdScope::enter(self);
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
        if self
            .memory_loadable_candidates_for_base(base)
            .any(|proposition| {
                crate::instrumentation::record_deterministic_work(1);
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
            })
        {
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
            .memory_loadable_candidates_for_base(base)
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
            && crate::kernel::api::contract_certification::quantified_int32_fact_certifies_loadable_cell(
                self, memory, base,
            )
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
            .memory_loadable_candidates_for_base(base)
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
        if bytes.as_const() == Some(4)
            && crate::kernel::api::contract_certification::quantified_int32_fact_certifies_loadable_cell(
                self, memory, base,
            )
        {
            return true;
        }
        self.memory_loadable_candidates_for_base(base)
            .any(|proposition| {
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

    /// The indexed-candidates leg of [`Self::pointers_proven_disjoint_by_range`]
    /// alone: separation facts plus range membership, no derived-separation
    /// fallback. Per-edge callers (the memory-DAG walk) use this so an
    /// undecided edge fails prompt instead of paying the composition-backed
    /// search per hop.
    pub(in crate::kernel) fn pointers_directly_disjoint_by_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        let direct = self
            .memory_separation_candidates(&left.block, &right.block)
            .find_map(|(proposition, left_range, right_range)| {
                (self.pointer_in_range(
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
                ))
                .then_some(proposition)
            });
        if let Some(proposition) = direct {
            record_implicit_reasoning_provenance(self, proposition);
            return true;
        }
        false
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        let direct = crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "range disjointness: indexed facts",
            || {
                self.memory_separation_candidates(&left.block, &right.block)
                    .find_map(|(proposition, left_range, right_range)| {
                        crate::instrumentation::measure_operation(
                            "kernel",
                            "resource context equality",
                            "range disjointness: indexed candidate",
                            || {
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
                            },
                        )
                        .then_some(proposition)
                    })
            },
        );
        if let Some(proposition) = direct {
            record_implicit_reasoning_provenance(self, proposition);
            return true;
        }
        crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "range disjointness: derived separation",
            || {
                self.proves_resource_separate(
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
            },
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
        self.memory_separation_candidates(&left.block, &right.block)
            .any(|(_, left_range, right_range)| {
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
            })
            || self
                .resource_compositions
                .iter()
                .any(|resources| resources.proves_owned_pointers_separate_shallow(left, right))
    }

    pub(in crate::kernel) fn pointer_in_range_by_shallow_fact_graph(
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
        if self.exact_condition_value(&ConditionTerm::signed_less_equal(
            start.clone(),
            index.clone(),
        )) == Some(true)
            && self
                .exact_condition_value(&ConditionTerm::signed_less_than(index.clone(), end.clone()))
                == Some(true)
        {
            return true;
        }
        let (Some(offset), Some(length)) = (
            affine_bitvector_difference_constant(&index, start),
            affine_bitvector_difference_constant(end, start),
        ) else {
            return false;
        };
        0 <= offset && offset < length
    }

    /// One indexed explicit-fact step beyond structural containment. This is
    /// intentionally narrower than the general shallow fact-graph helper:
    /// it accepts only an exact base-offset alias and the two exact range
    /// bounds, so a named separation candidate does not need recursive
    /// memory resolution merely because its member index is symbolic.
    fn pointer_in_range_by_exact_facts(&self, pointer: &Pointer, range: &CMemoryRange) -> bool {
        if pointer_in_memory_range_shallow(pointer, range) {
            return true;
        }
        if pointer.block != range.base().block {
            return false;
        }
        let offset_matches = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            pointer_offsets_match_by_shallow_fact_graph(left, right, self)
        };
        let index =
            pointer
                .element_index_from_base(range.base())
                .or_else(|| match &pointer.offset {
                    PointerOffsetTerm::Add(left, right)
                        if offset_matches(left, &range.base().offset) =>
                    {
                        int32_element_index_from_offset(right)
                    }
                    PointerOffsetTerm::Add(left, right)
                        if offset_matches(right, &range.base().offset) =>
                    {
                        int32_element_index_from_offset(left)
                    }
                    _ if offset_matches(&pointer.offset, &range.base().offset) => {
                        Some(Bitvector32Term::Constant(0))
                    }
                    _ => None,
                });
        let Some(index) = index else {
            return false;
        };
        self.exact_condition_value(&ConditionTerm::signed_less_equal(
            range.start().clone(),
            index.clone(),
        )) == Some(true)
            && self
                .exact_condition_value(&ConditionTerm::signed_less_than(index, range.end().clone()))
                == Some(true)
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
        let mut candidates = self.memory_separation_candidates(&left.block, &right.block);
        if crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: shallow candidates",
            || {
                candidates.clone().any(|(_, left_range, right_range)| {
                    #[cfg(test)]
                    MEMORY_SEPARATION_CANDIDATE_CHECKS.with(|checks| checks.set(checks.get() + 1));
                    pointer_in_memory_range_shallow(left, left_range)
                        && pointer_in_memory_range_shallow(right, right_range)
                        || pointer_in_memory_range_shallow(right, left_range)
                            && pointer_in_memory_range_shallow(left, right_range)
                })
            },
        ) {
            return true;
        }
        if crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: exact-fact candidates",
            || {
                candidates.clone().any(|(_, left_range, right_range)| {
                    #[cfg(test)]
                    MEMORY_SEPARATION_CANDIDATE_CHECKS.with(|checks| checks.set(checks.get() + 1));
                    self.pointer_in_range_by_exact_facts(left, left_range)
                        && self.pointer_in_range_by_exact_facts(right, right_range)
                        || self.pointer_in_range_by_exact_facts(right, left_range)
                            && self.pointer_in_range_by_exact_facts(left, right_range)
                })
            },
        ) {
            return true;
        }
        if crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: resource shallow",
            || {
                self.resource_compositions
                    .iter()
                    .any(|resources| resources.proves_owned_pointers_separate_shallow(left, right))
            },
        ) {
            return true;
        }
        if crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: resource fact graph",
            || {
                self.resource_compositions.iter().any(|resources| {
                    resources.proves_owned_pointers_separate_by(left, right, |pointer, range| {
                        self.pointer_in_range_by_shallow_fact_graph(
                            pointer,
                            range.base(),
                            range.start(),
                            range.end(),
                        )
                    })
                })
            },
        ) {
            return true;
        }

        // The recursive second phase re-enters offset-equality reasoning.
        // Keep it shallow: nested queries past the expensive-edge budget use
        // the shallow answer above, which bounds the mutual recursion without
        // losing the direct certificates.
        if depth > crate::kernel::reasoning::MEMORY_RESOLUTION_EXPENSIVE_DEPTH_LIMIT {
            return false;
        }
        crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: recursive candidates",
            || {
                candidates.any(|(_, left_range, right_range)| {
                    #[cfg(test)]
                    {
                        MEMORY_SEPARATION_CANDIDATE_CHECKS
                            .with(|checks| checks.set(checks.get() + 1));
                        MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS
                            .with(|checks| checks.set(checks.get() + 1));
                    }
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
                })
            },
        )
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
        if left.base().blocks_proven_distinct(right.base()) {
            return true;
        }
        if left.element_width() != right.element_width() {
            return false;
        }
        if self
            .resource_compositions
            .iter()
            .any(|resources| resources.proves_owned_memory_ranges_separate_shallow(left, right))
        {
            return true;
        }
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
        }) || self.resource_compositions.iter().any(|resources| {
            // The proof-aware form of the shallow composition fallback above:
            // the same containment relation the materialized-pair loops use,
            // served by the compact composition's indexed candidates.
            resources.proves_owned_memory_ranges_separate_by(left, right, |child, parent| {
                memory_range_contained_for_memory_resolution_with_depth(child, parent, self, depth)
            })
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
        // Exact syntax and direct offset arithmetic are authoritative on
        // their own. Resolve them before snapshot-aware equality: generated
        // range endpoints commonly retain a literal base plus an index, and
        // sending that shape through memory resolution first recursively
        // compares every nested load in the base expression.
        if let Some(index) = pointer.element_index_from_base(base)
            && index.as_const().is_some()
        {
            return Some(index);
        }
        if let Some(index) =
            self.pointer_element_index_from_base_for_memory_resolution(pointer, base)
        {
            return Some(index);
        }

        // Bounded comparison scopes answer offset equality by structure and
        // load variables only; the general decider's per-pair cost is the
        // breadth that bounded callers exist to avoid.
        let offsets_equal = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            if crate::kernel::reasoning::memory_resolution::bounded_snapshot_comparison_active() {
                crate::kernel::eval::offsets_have_same_canonical_form(left, right)
            } else {
                self.decide(&ConditionTerm::pointer_offset_equal(
                    left.clone(),
                    right.clone(),
                )) == Some(true)
            }
        };
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if offsets_equal(left, &base.offset) {
                return int32_element_index_from_offset(right);
            }
            if offsets_equal(right, &base.offset) {
                return int32_element_index_from_offset(left);
            }
        }

        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if offsets_equal(&pointer.offset, left) {
                return int32_element_index_from_offset(right)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
            if offsets_equal(&pointer.offset, right) {
                return int32_element_index_from_offset(left)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
        }

        if offsets_equal(&pointer.offset, &base.offset) {
            return Some(Bitvector32Term::Constant(0));
        }
        None
    }

    fn pointer_element_index_from_base_for_memory_resolution(
        &self,
        pointer: &Pointer,
        base: &Pointer,
    ) -> Option<Bitvector32Term> {
        #[cfg(test)]
        PROOF_AWARE_POINTER_INDEX_QUERIES.with(|queries| queries.set(queries.get() + 1));
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
        let proves = |condition: ConditionTerm| {
            self.exact_condition_value(&condition) == Some(true)
                || self.exact_ordering_modulo_canonical_atoms(&condition)
                || self.nonnegative_successor_by_exact_facts(&condition)
                // Bounded comparison scopes answer from exact facts only:
                // the general decider's order-fact matching resolves loads
                // and fans out. Suppression records a truncation so this
                // weaker context's negatives are never memoized where the
                // full check would have run.
                || if crate::kernel::reasoning::memory_resolution::bounded_snapshot_comparison_active() {
                    crate::kernel::assumptions::note_search_truncation();
                    false
                } else {
                    self.decide(&condition) == Some(true)
                }
        };
        let range_base = base.offset_by_int32_elements(start.clone());
        if let Some(index) = self.pointer_element_index_from_base(pointer, &range_base) {
            let range_length = Bitvector32Term::subtract(end.clone(), start.clone());
            if proves(ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                index.clone(),
            )) && proves(ConditionTerm::signed_less_than(index, range_length))
            {
                return true;
            }
        }

        let Some(index) = self.pointer_element_index_from_base(pointer, base) else {
            return false;
        };
        proves(ConditionTerm::signed_less_equal(
            start.clone(),
            index.clone(),
        )) && proves(ConditionTerm::signed_less_than(index, end.clone()))
    }

    /// An exact ordering fact whose operands match the queried condition's
    /// operands modulo load variables: facts may write a load atom at
    /// a recorded snapshot while the query carries the placeholder load or
    /// the load variable, and all of those are one atom. Bounded by
    /// the exact fact set and term size.
    fn exact_ordering_modulo_canonical_atoms(&self, condition: &ConditionTerm) -> bool {
        let query = match condition {
            ConditionTerm::Bitvector32SignedLessEqual(left, right)
            | ConditionTerm::Bitvector32SignedLessThan(left, right) => (left, right),
            _ => return false,
        };
        self.condition_facts.iter().any(|(fact, value)| {
            if !*value {
                return false;
            }
            let operands = match (condition, fact) {
                (
                    ConditionTerm::Bitvector32SignedLessEqual(_, _),
                    ConditionTerm::Bitvector32SignedLessEqual(left, right),
                )
                | (
                    ConditionTerm::Bitvector32SignedLessThan(_, _),
                    ConditionTerm::Bitvector32SignedLessThan(left, right),
                ) => (left, right),
                _ => return false,
            };
            let left_match =
                crate::kernel::eval::terms_have_same_canonical_form(query.0, operands.0);
            let right_match =
                crate::kernel::eval::terms_have_same_canonical_form(query.1, operands.1);
            left_match && right_match
        })
    }

    /// Proves `0 <= t + 1` from two exact facts: `0 <= t` and any exact
    /// strict upper bound `t < u`. The upper bound is the no-overflow
    /// witness — a signed int32 strictly below another cannot be the
    /// maximum, so its successor does not wrap. Exact-fact-only, so range
    /// membership over successor indices (`data[len + 1]` under
    /// `0 <= len` and `len < cap` requires) decides without the general
    /// prover.
    fn nonnegative_successor_by_exact_facts(&self, condition: &ConditionTerm) -> bool {
        let ConditionTerm::Bitvector32SignedLessEqual(low, sum) = condition else {
            return false;
        };
        if !matches!(low.as_ref(), Bitvector32Term::Constant(0)) {
            return false;
        }
        let Bitvector32Term::Add(term, one) = sum.as_ref() else {
            return false;
        };
        if !matches!(one.as_ref(), Bitvector32Term::Constant(1)) {
            return false;
        }
        // Facts may write the load atom by its load variable while the
        // index carries the raw load (or vice versa); try both forms.
        let mut forms = vec![term.as_ref().clone()];
        if let Some((variable, _)) = crate::kernel::eval::load_variable_for_term(term.as_ref()) {
            let named = Bitvector32Term::Variable(variable);
            if !forms.contains(&named) {
                forms.push(named);
            }
        }
        forms.iter().any(|form| {
            let nonnegative =
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), form.clone());
            (self.exact_condition_value(&nonnegative) == Some(true)
                || self.exact_ordering_modulo_canonical_atoms(&nonnegative))
                && self.condition_facts.iter().any(|(fact, value)| {
                    *value
                        && matches!(
                            fact,
                            ConditionTerm::Bitvector32SignedLessThan(left, _)
                                if crate::kernel::eval::terms_have_same_canonical_form(
                                    left, form,
                                )
                        )
                })
        })
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
            for proposition in self.prop_facts.iter() {
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

        let separation_fact_entails = |fact_left: &CResource, fact_right: &CResource| {
            crate::kernel::reasoning::consume_resource_prover_fuel()
                && (self.proves_resource_contains_inner(fact_left, left)
                    && self.proves_resource_contains_inner(fact_right, right)
                    || self.proves_resource_contains_inner(fact_left, right)
                        && self.proves_resource_contains_inner(fact_right, left))
        };
        // For a memory-memory query, memory-memory separation facts live in
        // the block-pair index and are consulted by the indexed pass below;
        // the linear pass covers only the residual facts with a non-memory
        // side, whose containment can still entail memory separation
        // through a composite body. Any other query shape keeps the full
        // scan: the indexed pass below does not run for it.
        let memory_memory_query =
            matches!((left, right), (CResource::Memory(_), CResource::Memory(_)));
        let scan_facts: &dyn Fn(&dyn Fn(&Proposition) -> bool) -> bool = &|entails| {
            if memory_memory_query {
                self.nonmemory_separation_facts.iter().any(|p| entails(p))
            } else {
                self.prop_facts.iter().any(|p| entails(p))
            }
        };
        let residual_hit = scan_facts(&|proposition| {
            let Proposition::CResourceSeparate {
                left: fact_left,
                right: fact_right,
            } = proposition
            else {
                return false;
            };
            separation_fact_entails(fact_left, fact_right)
        });
        if memory_memory_query && std::env::var_os("CLICK_DBG_SEP_PARITY").is_some() {
            let legacy_hit = self.prop_facts.iter().any(|proposition| {
                let Proposition::CResourceSeparate {
                    left: fact_left,
                    right: fact_right,
                } = proposition
                else {
                    return false;
                };
                separation_fact_entails(fact_left, fact_right)
            });
            let indexed_hit = residual_hit
                || match (left, right) {
                    (CResource::Memory(left_range), CResource::Memory(right_range)) => self
                        .memory_separation_candidates(
                            &left_range.base().block,
                            &right_range.base().block,
                        )
                        .any(|(_, fact_left, fact_right)| {
                            separation_fact_entails(
                                &CResource::Memory(fact_left.clone()),
                                &CResource::Memory(fact_right.clone()),
                            )
                        }),
                    _ => false,
                };
            if legacy_hit != indexed_hit {
                eprintln!("SEP-PARITY-FLIP legacy={legacy_hit} indexed={indexed_hit}");
            }
        }
        if residual_hit {
            return true;
        }
        // The same candidates, projected from the compact compositions
        // instead of materialized propositions; two owned facts of one valid
        // composition are separate by the composition law.
        if let (CResource::Memory(left_range), CResource::Memory(right_range)) = (left, right)
            && self
                .memory_separation_candidates(&left_range.base().block, &right_range.base().block)
                .any(|(_, fact_left, fact_right)| {
                    separation_fact_entails(
                        &CResource::Memory(fact_left.clone()),
                        &CResource::Memory(fact_right.clone()),
                    )
                })
        {
            return true;
        }

        if self
            .resource_compositions
            .iter()
            .any(|resources| resources.proves_owned_resources_separate(left, right, self))
        {
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
        left.element_width() == right.element_width()
            && self.pointers_proven_equal_for_fact_transport(left.base(), right.base())
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
            for (condition, value) in self.condition_facts.iter() {
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
        for proposition in self.prop_facts.iter() {
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
        for proposition in self.prop_facts.iter() {
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
        let proves_below_predecessor = |left: &Bitvector32Term, right: &Bitvector32Term| {
            let predecessor_upper =
                Bitvector32Term::subtract(right.clone(), Bitvector32Term::Constant(1));
            self.proves(&Proposition::ConditionIs(
                ConditionTerm::signed_less_than(left.clone(), predecessor_upper),
                true,
            )) && self.proves(&Proposition::ConditionIs(
                ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), right.clone()),
                true,
            ))
        };
        let proves_successor_below_predecessor =
            |left: &Bitvector32Term, right: &Bitvector32Term| {
                let Some((predecessor, 1)) = left.add_const_parts() else {
                    return false;
                };
                // If predecessor < upper - 1 and 0 < upper, then
                // predecessor + 1 < upper in the defined signed-int32
                // domain. The positivity premise also rules out underflow
                // in the predecessor expression.
                let predecessor_upper =
                    Bitvector32Term::subtract(right.clone(), Bitvector32Term::Constant(1));
                let predecessor_bounded = self.proves(&Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(predecessor, predecessor_upper),
                    true,
                ));
                let upper_positive = self.proves(&Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), right.clone()),
                    true,
                ));
                predecessor_bounded && upper_positive
            };
        let proves_order = |left: &Bitvector32Term, right: &Bitvector32Term, strict: bool| {
            let condition = if strict {
                ConditionTerm::signed_less_than(left.clone(), right.clone())
            } else {
                ConditionTerm::signed_less_equal(left.clone(), right.clone())
            };
            self.exact_condition_value(&condition) == Some(true)
                || crate::instrumentation::measure_operation(
                    "kernel",
                    "resource read",
                    "resource read: exact order path",
                    || self.has_exact_order_path(left, right, strict),
                )
                || crate::instrumentation::measure_operation(
                    "kernel",
                    "resource read",
                    "resource read: fallback order decision",
                    || self.decide(&condition) == Some(true),
                )
                || !strict && self.nonnegative_successor_by_exact_facts(&condition)
                || strict && proves_below_predecessor(left, right)
                || strict && proves_successor_below_predecessor(left, right)
        };
        // Scalar and pointer fields both occupy one surface element: ranges
        // count fields, so a pointer-width access at an in-range element
        // index is authorized exactly like an int32 access.
        if (byte_width == 4 || byte_width == crate::kernel::C_POINTER_BYTE_WIDTH)
            && let Some(index) = pointer.element_index_from_base(base)
            && proves_order(start, &index, false)
            && proves_order(&index, end, true)
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

    /// [`Self::ranges_proven_disjoint_from_pointer`] for internal frame
    /// evidence, which may also look through composite definitions.
    ///
    /// A pointer inside a composite's footprint is invisible to the ordinary
    /// prover, because a composite own carries no memory range of its own.
    /// Framing may consult the definition to decide the disjointness;
    /// nothing is published, so a user's `separate(...)` goal over a nested
    /// composite still needs its `observe(...)` chain. Deliberately kept off
    /// the ordinary prover, whose per-cell store-drop callers must not pay
    /// for an expansion they never need.
    pub(in crate::kernel) fn ranges_proven_disjoint_from_pointer_for_frame(
        &self,
        ranges: &[CMemoryRange],
        pointer: &Pointer,
        memory: &CMemory,
    ) -> bool {
        if self.ranges_proven_disjoint_from_pointer(ranges, pointer) {
            return true;
        }
        let expanded = self.frame_expanded_compositions(memory);
        if expanded.is_empty() {
            return false;
        }
        ranges.iter().all(|range| {
            expanded.iter().any(|resources| {
                resources.proves_owned_range_separate_from_pointer_with(
                    range,
                    pointer,
                    |range, available| {
                        memory_range_shallowly_contained(range, available)
                            || self.memory_range_contained_by_decided_endpoints(range, available)
                    },
                    |pointer, available| {
                        self.pointer_in_range_by_shallow_fact_graph(
                            pointer,
                            available.base(),
                            available.start(),
                            available.end(),
                        ) || self.pointer_directly_in_memory_range(pointer, available)
                    },
                )
            })
        })
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
            if self.resource_compositions.iter().any(|resources| {
                resources.proves_owned_range_separate_from_pointer_shallow(
                    range,
                    pointer,
                    |pointer, available| {
                        self.pointer_in_range_by_shallow_fact_graph(
                            pointer,
                            available.base(),
                            available.start(),
                            available.end(),
                        ) || self.pointer_directly_in_memory_range(pointer, available)
                    },
                )
            }) {
                return true;
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

    /// The armed compositions with their composites definitionally expanded,
    /// for frame evidence only.
    ///
    /// Expansion is definitional and runs against no assumptions, so it
    /// cannot re-enter the prover that called it, and its result is a pure
    /// function of the composition and the armed definitions — memoized per
    /// thread. Composite bodies are evaluated over an empty snapshot: the
    /// segments this answers for are the ones whose addresses do not depend
    /// on field values, and a body that needs a live snapshot simply does
    /// not expand here.
    /// `range` inside `available` by one bounded decision per endpoint: the
    /// bases share an element index and the indexed bounds decide
    /// `available.start <= range.start` and `range.end <= available.end`.
    fn memory_range_contained_by_decided_endpoints(
        &self,
        range: &CMemoryRange,
        available: &CMemoryRange,
    ) -> bool {
        let Some(base_index) = range.base().element_index_from_base(available.base()) else {
            return false;
        };
        let range_start = Bitvector32Term::add(base_index.clone(), range.start().clone());
        let range_end = Bitvector32Term::add(base_index, range.end().clone());
        self.decide(&ConditionTerm::signed_less_equal(
            available.start().clone(),
            range_start,
        )) == Some(true)
            && self.decide(&ConditionTerm::signed_less_equal(
                range_end,
                available.end().clone(),
            )) == Some(true)
    }

    /// The compositions with their owned composites expanded over `memory`:
    /// a composite's footprint is the regions its body denotes at the
    /// snapshot the composition holds at, so the expansion names those
    /// regions with the same load variables the live facts use.
    fn frame_expanded_compositions(&self, memory: &CMemory) -> Vec<ResourceContext> {
        // Cheap gates first: this runs on the store cell-drop path, so a
        // composition with nothing composite to look through must cost a
        // scan of its own facts and no more.
        if self.resource_compositions.is_empty() {
            return Vec::new();
        }
        let has_composite_own = self.resource_compositions.iter().any(|composition| {
            composition
                .facts()
                .iter()
                .any(|fact| fact.is_own() && matches!(fact.resource(), CResource::Composite { .. }))
        });
        if !has_composite_own {
            return Vec::new();
        }
        let Some(definitions) = frame_composite_definitions() else {
            return Vec::new();
        };
        if definitions.is_empty() {
            return Vec::new();
        }
        // Keyed by the composition's storage identity, not its contents: a
        // structural key would re-walk the whole context on every query, and
        // this runs on the store cell-drop path. Retaining the keyed context
        // keeps its allocation alive, so an address cannot be recycled under
        // a stale entry.
        const EXPANSION_MEMO_LIMIT: usize = 10_000;
        let memory_id = crate::kernel::intern_c_memory_ref(memory).arena_id();
        let mut expanded = Vec::new();
        for composition in self.resource_compositions.iter() {
            let key = (
                std::sync::Arc::as_ptr(&composition.storage) as usize,
                memory_id,
            );
            if let Some(hit) =
                EXPANSION_MEMO.with(|memo| memo.borrow().get(&key).map(|(_, value)| value.clone()))
            {
                expanded.extend(hit);
                continue;
            }
            let computed = crate::kernel::functions::expand_all_composite_resource_facts(
                composition,
                &definitions,
                memory,
                &PureFactContext::new(),
            )
            .filter(|context| context != composition);
            EXPANSION_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= EXPANSION_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(key, (composition.clone(), computed.clone()));
            });
            expanded.extend(computed);
        }
        expanded
    }

    fn range_proven_disjoint_from_pointer(&self, range: &CMemoryRange, pointer: &Pointer) -> bool {
        if range.base.blocks_proven_distinct(pointer) {
            return true;
        }
        if pointer_in_memory_range_shallow(pointer, range) {
            return false;
        }
        let owned_member_holds_pointer = |resources: &ResourceContext| {
            resources.proves_owned_range_separate_from_pointer_shallow(
                range,
                pointer,
                |pointer, available| {
                    self.pointer_in_range_by_shallow_fact_graph(
                        pointer,
                        available.base(),
                        available.start(),
                        available.end(),
                    ) || self.pointer_directly_in_memory_range(pointer, available)
                },
            )
        };
        if self
            .resource_compositions
            .iter()
            .any(owned_member_holds_pointer)
        {
            return true;
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

        // Direct address arithmetic is both stronger for the common
        // same-allocation case and bounded independently of the number of
        // available separation certificates. Keep the recursive certificate
        // prover below as the fallback for genuinely indirect aliases.
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
            let same_base_timing = crate::instrumentation::OperationTiming::new(
                "kernel",
                "fact range coverage",
                "fact range coverage: exact base",
            );
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
            drop(same_base_timing);
        }

        let fact_base = base.offset_by_int32_elements(start.clone());
        let range_base = range.base.offset_by_int32_elements(range.start.clone());
        let shifted_base_delta = crate::instrumentation::measure_operation(
            "kernel",
            "fact range coverage",
            "fact range coverage: shifted base relation",
            || self.pointer_element_index_from_base(&range_base, &fact_base),
        );
        if let Some(base_delta) = shifted_base_delta {
            let range_length = Bitvector32Term::subtract(range.end.clone(), range.start.clone());
            let fact_length = Bitvector32Term::subtract(end.clone(), start.clone());
            let range_end = Bitvector32Term::add(base_delta.clone(), range_length);
            if crate::instrumentation::measure_operation(
                "kernel",
                "fact range coverage",
                "fact range coverage: shifted bounds",
                || {
                    self.decide(&ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        base_delta,
                    )) == Some(true)
                        && self.decide(&ConditionTerm::signed_less_equal(range_end, fact_length))
                            == Some(true)
                },
            ) {
                return true;
            }
        }

        let base_delta = crate::instrumentation::measure_operation(
            "kernel",
            "fact range coverage",
            "fact range coverage: direct base relation",
            || self.pointer_element_index_from_base(&range.base, base),
        );
        let Some(base_delta) = base_delta else {
            return false;
        };
        let range_start = Bitvector32Term::add(base_delta.clone(), range.start.clone());
        let range_end = Bitvector32Term::add(base_delta, range.end.clone());

        crate::instrumentation::measure_operation(
            "kernel",
            "fact range coverage",
            "fact range coverage: direct bounds",
            || {
                self.decide(&ConditionTerm::signed_less_equal(
                    start.clone(),
                    range_start,
                )) == Some(true)
                    && self.decide(&ConditionTerm::signed_less_equal(range_end, end.clone()))
                        == Some(true)
            },
        )
    }
}
