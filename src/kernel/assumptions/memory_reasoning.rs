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

/// How many of a range's logical elements an access of `byte_width` bytes
/// occupies for the *permission* question, where a range authorizes a read.
///
/// A range counts logical elements and an access is measured in bytes, so an
/// `int64` read spans two elements of a four-byte range. The exception is the
/// historical struct field unit: a loaded C pointer occupies one four-byte
/// *field* even though its ABI footprint is two physical words, and
/// [`PureFactContext::pointer_access_in_range`] has counted it that way since
/// struct ranges existed. Keeping that rule here is what makes this a pure
/// extraction of the code it replaces.
///
/// `None` for a width that names no elements at all, which declines the
/// element question rather than rounding an answer onto a boundary.
fn authorized_access_element_length(byte_width: u32, element_width: u32) -> Option<u32> {
    if element_width == 0 || byte_width == 0 {
        return None;
    }
    if byte_width == crate::kernel::C_POINTER_BYTE_WIDTH && element_width == 4 {
        return Some(1);
    }
    Some(byte_width.div_ceil(element_width))
}

/// How many bytes the access at this address reads, for a separation question
/// whose caller holds only the address.
///
/// The C type at an address does not vary with the snapshot a framing walk
/// happens to start from, so the address-keyed half of the record
/// [`crate::kernel::eval::symbolic_load_value`] writes is the answer, and the
/// widest scalar stands in where no typed load was ever seen. Over-stating a
/// width can only shrink the set an exclusion rule calls separate, so the
/// fallback is the safe direction.
fn access_byte_width_for_separation(pointer: &Pointer) -> u32 {
    crate::kernel::load_access_width_at_address_or_widest(pointer)
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
    /// interned memory id; see `frame_frontier_compositions`.
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

use crate::kernel::scaled_extent_element_width;

/// A term as a base plus a constant shift, peeling the additive and
/// subtractive constants a range endpoint is written with. `hi - 1` is `hi`
/// shifted by `-1`; anything else is itself shifted by `0`. One level, no
/// facts, no recursion budget.
fn endpoint_base_and_shift(term: &Bitvector32Term) -> (&Bitvector32Term, i64) {
    match term {
        Bitvector32Term::Add(left, right) => match (left.as_ref(), right.as_ref()) {
            (base, Bitvector32Term::Constant(shift)) => (base, i64::from(*shift as i32)),
            (Bitvector32Term::Constant(shift), base) => (base, i64::from(*shift as i32)),
            _ => (term, 0),
        },
        Bitvector32Term::Subtract(left, right) => match right.as_ref() {
            Bitvector32Term::Constant(shift) => (left.as_ref(), -i64::from(*shift as i32)),
            _ => (term, 0),
        },
        _ => (term, 0),
    }
}

/// The two element endpoints an element-count term names.
///
/// `p[a..b]` lowers its extent to `(b - a) * w`, so dividing that extent by
/// the width gives back `b - a` and the endpoints read straight off the
/// subtraction. A range that starts at `0` is the same term with the start
/// already folded away — the subtraction constructor returns `b` for `b - 0` —
/// so a count that is not a subtraction is a count from `0`, and `0` is the
/// start it names.
///
/// This is a reading of the term, not an assumption about it: `count - 0` and
/// `count` are the same term, so the fact's byte count is `(end - start) * w`
/// in either spelling and every reader below is asking about the same bytes.
/// [`Assumptions::assumed_extent_covers_its_element_count`] already restores
/// the same start for the same reason; sharing one reading keeps a range
/// written from `0` — which is how a C contract usually writes one — from
/// being a different kind of range to the rules than `p[a..b]` is.
fn element_count_endpoints(
    element_count: &Bitvector32Term,
) -> (&Bitvector32Term, &Bitvector32Term) {
    const ZERO: &Bitvector32Term = &Bitvector32Term::Constant(0);
    match element_count {
        Bitvector32Term::Subtract(end, start) => (start.as_ref(), end.as_ref()),
        _ => (ZERO, element_count),
    }
}

/// The value of an element-count term that is a constant, including the
/// structural case where the two endpoints are the same term shifted by
/// constants: `hi - (hi - 1)` counts one element whatever `hi` is.
///
/// This decides the extent of a single-cell range written from a symbolic
/// endpoint, which the byte-count canonicalizer leaves as a subtraction. It
/// reads the term and consults no facts, and the difference it reports is the
/// term's own modular value: for a shared base the base cancels, so the count
/// is exactly the shift difference.
fn constant_element_count(element_count: &Bitvector32Term) -> Option<i64> {
    if let Some(value) = signed_bitvector_constant(element_count) {
        return Some(value);
    }
    let Bitvector32Term::Subtract(end, start) = element_count else {
        return None;
    };
    let (end_base, end_shift) = endpoint_base_and_shift(end);
    let (start_base, start_shift) = endpoint_base_and_shift(start);
    (end_base == start_base).then_some(end_shift - start_shift)
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

    pub(crate) fn proves_memory_access(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.proves_memory_loadable(memory, pointer, &Bitvector32Term::Constant(byte_width))
    }

    pub(crate) fn proves_memory_loadable(
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
                            .pointer_element_index_from_base_for_memory_resolution(
                                base,
                                range_base,
                                bytes.as_const().unwrap_or(4),
                            )
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
    pub(crate) fn adjacent_loadable_region_facts(
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
                    && fact_memory.forgotten.ended_local_blocks == memory.forgotten.ended_local_blocks
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
                        crate::kernel::api::canonicalize_pointer_loads(fact_base),
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
                    crate::kernel::api::canonicalize_pointer_loads(pointer),
                    Bitvector32Term::Constant(byte_width),
                    true,
                )
            })
        }));
        regions.extend(
            memory
                .union_cells
                .iter()
                .filter_map(|((pointer, _), value)| {
                    let byte_width = value.byte_width();
                    (byte_width > 0 && memory.is_loadable_concretely(pointer, byte_width)).then(
                        || {
                            (
                                None,
                                crate::kernel::api::canonicalize_pointer_loads(pointer),
                                Bitvector32Term::Constant(byte_width),
                                true,
                            )
                        },
                    )
                }),
        );
        let base = crate::kernel::api::canonicalize_pointer_loads(base);
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
                        if !self.assumed_extent_covers_its_element_count(&prefix_count, 4)
                            || !self.assumed_extent_covers_its_element_count(&suffix_count, 4)
                        {
                            return false;
                        }
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
                let Some(element_count) = element_count_from_bytes(range_bytes, byte_width) else {
                    return false;
                };
                if !self.assumed_extent_covers_its_element_count(&element_count, byte_width) {
                    return false;
                }
                pointer_in_range_for_memory_resolution(
                    base,
                    range_base,
                    &Bitvector32Term::Constant(0),
                    &element_count,
                    byte_width,
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
            && let Some(index) = base.element_index_from_base_with_width(range_base, byte_width)
            && let Some(element_count) = element_count_from_bytes(range_bytes, byte_width)
            // Every branch below reads the assumed extent as `element_count`
            // elements and compares an index against it in signed arithmetic.
            // That reading is the fact's meaning only while the extent is a
            // valid byte extent; a wrapped one covers fewer bytes than its
            // count claims, and the cell would come from nothing.
            && self.assumed_extent_covers_its_element_count(&element_count, byte_width)
        {
            let lower =
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone());
            let upper = ConditionTerm::signed_less_than(index.clone(), element_count.clone());
            if self.exact_condition_value(&lower) == Some(true)
                && self.exact_condition_value(&upper) == Some(true)
            {
                return true;
            }
            if let Some(index_constant) = super::exact_signed_constant(&index, self) {
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
        if self.proves_loadable_subrange_by_element_endpoints(range_base, range_bytes, base, bytes)
        {
            return true;
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

    /// Range narrowing: a goal range the stated order facts place inside an
    /// assumed loadable range is loadable.
    ///
    /// This is the one rule here whose goal extent may stay symbolic. Every
    /// other route needs a constant byte width, which is why a single cell
    /// inside `loadable(p[a..b])` is found while the range `p[c..d]` inside
    /// the same fact is not: a segment `p[x..y]` lowers to the base
    /// `p + x * w` and the byte count `(y - x) * w`, so a symbolic upper
    /// endpoint leaves a symbolic product behind.
    ///
    /// Read both extents at element granularity — the granularity the cell
    /// rules above already use — and the endpoints come back exactly: the
    /// fact covers elements `a..b`, the goal names elements `c..d`, and the
    /// pointer offset says where `c` sits relative to `a`. The rule then
    /// concludes `loadable(p[c..d])` from `loadable(p[a..b])` and the order
    /// facts `a <= c`, `c <= d`, `d <= b`.
    ///
    /// The endpoints come back through [`element_count_endpoints`], so a range
    /// written from `0` reads the same way as any other. Its count term has the
    /// start folded out of it — `n - 0` is `n` — and taking that folded term
    /// for the count itself, with no start, would leave the rule unable to
    /// narrow `loadable(p[0..n])`, which is how a C contract usually states a
    /// range. The pointer offset is compared the same way: it has to be the
    /// difference of the two start endpoints, asked for through the folding
    /// constructor, so the comparison is between one canonical spelling and
    /// another rather than between two term shapes.
    ///
    /// Soundness, in the arithmetic the terms are actually written in. An
    /// extent is a `Bitvector32Term`: `(b - a) * w` is modular, so reading the
    /// fact as "the elements `a..b`" is only legitimate while that product is
    /// the true count of bytes. The rule therefore requires the assumed fact's
    /// own byte-count guards —
    /// [`crate::kernel::memory_range_byte_count_guards`], the one definition
    /// of "this element range is a valid 32-bit byte extent": `a <= b` signed,
    /// and `(b - a) <= u32::MAX / w` unsigned. With those established,
    /// `0 <= b - a` and `(b - a) * w` does not wrap, so the fact's extent is
    /// exactly `(b - a) * w` bytes from `p + a * w`.
    ///
    /// The goal's guards then follow rather than being asked for again.
    /// `a <= c`, `c <= d`, `d <= b` give `0 <= d - c <= b - a` with no
    /// intermediate wrap, because each difference is bounded by `b - a`, which
    /// is itself nonnegative and small enough that `(b - a) * w` fits; so
    /// `(d - c) * w <= (b - a) * w` as true integers, `(d - c) * w` does not
    /// wrap either, and `(c - a) * w + (d - c) * w = (d - a) * w <= (b - a) * w`.
    /// The goal's byte interval is therefore a sub-interval of the fact's, at
    /// the same width and in the same block, and every byte it names the fact
    /// already covers.
    ///
    /// `c <= d` is required rather than assumed, so a reversed goal range is
    /// refused instead of being read as a negative extent. An empty goal range
    /// (`c == d`) is accepted and claims nothing, matching the empty-range case
    /// in `proves_memory_loadable_inner`. No product is rescaled and no new
    /// byte count is formed: `(d - c) * w` is the goal's own lowered extent.
    /// The snapshot side condition stays with the caller, which has already
    /// established that the assumed range is still available in the goal's
    /// memory.
    ///
    /// The fits guard is what makes this rule self-contained. Without it a
    /// wrapped assumed extent — `loadable(v[0..n])` at `n == 1 << 30`, whose
    /// `n * 4` is `0` — would be a vacuously true premise that narrowing could
    /// turn into a real one. The sibling cell rules above still read a wrapped
    /// extent as its element count, and a witness for that is
    /// `mdtests/wrapped_viewable_extent_is_not_a_cell.md`, quarantined.
    fn proves_loadable_subrange_by_element_endpoints(
        &self,
        range_base: &Pointer,
        range_bytes: &Bitvector32Term,
        base: &Pointer,
        bytes: &Bitvector32Term,
    ) -> bool {
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        if range_base.block != base.block {
            return false;
        }
        let Some(element_width) = scaled_extent_element_width(bytes) else {
            return false;
        };
        if scaled_extent_element_width(range_bytes) != Some(element_width) {
            return false;
        }
        let (Some(goal_count), Some(range_count)) = (
            element_count_from_bytes(bytes, element_width),
            element_count_from_bytes(range_bytes, element_width),
        ) else {
            return false;
        };
        let Some(index) = base.element_index_from_base_with_width(range_base, element_width) else {
            return false;
        };
        let (goal_start, goal_end) = element_count_endpoints(&goal_count);
        let (range_start, range_end) = element_count_endpoints(&range_count);
        crate::instrumentation::record_deterministic_work(1);
        // The goal's own byte count names its endpoints; the pointer offset
        // must agree that its start element is the fact's start advanced by
        // that offset. Otherwise the two counts describe unrelated endpoints
        // and nothing follows from comparing them. The offset is built by the
        // same folding constructor the endpoints are read back through, so
        // asking for the difference itself asks the one question in the one
        // spelling both sides already have.
        let offset_agrees =
            index == Bitvector32Term::subtract(goal_start.clone(), range_start.clone());
        offset_agrees
            && self.proves_element_endpoint_order(range_start, goal_start)
            && self.proves_element_endpoint_order(goal_start, goal_end)
            && self.proves_element_endpoint_order(goal_end, range_end)
            && self.assumed_range_is_a_valid_byte_extent(range_start, range_end, element_width)
    }

    /// Whether the assumed range is established here to be a valid 32-bit byte
    /// extent — the side condition
    /// [`crate::kernel::memory_range_byte_count_guards`] states wherever a
    /// contract supplies a range.
    ///
    /// Constant endpoints are decided by that shared definition, so a constant
    /// range cannot be read one way here and another way in a contract.
    ///
    /// Symbolic endpoints need the element count `b - a` pinned to
    /// `0..=limit`, where `limit` is
    /// [`crate::kernel::memory_range_element_count_limit`] — the same bound the
    /// shared `fits` guard uses, read from the same place. The guard itself is
    /// an unsigned comparison, and Click's surface has no unsigned comparison
    /// to write it with; these two signed facts imply it and a proof can state
    /// both, which is the spelling
    /// [`crate::kernel::memory_range_element_count_guards`] states them in.
    /// `0 <= b - a` is the load-bearing one: without it `a = INT_MIN`,
    /// `b = INT_MAX` satisfies `a <= b` and `b - a <= limit` while `b - a` is
    /// really `-1` and the extent has wrapped.
    fn assumed_range_is_a_valid_byte_extent(
        &self,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
        element_width: u32,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        // One-byte elements: the extent is the count, unscaled, so no product
        // can wrap and the fact's byte count is already exact. There is
        // nothing for a proof to establish, and the signed index comparison
        // the readers make handles a count whose bit pattern is negative.
        if element_width == 1 {
            return true;
        }
        match crate::kernel::memory_range_byte_count_extent(
            start.clone(),
            end.clone(),
            element_width,
        ) {
            crate::kernel::MemoryRangeExtent::ConstantValid => true,
            crate::kernel::MemoryRangeExtent::ConstantInvalid { .. } => false,
            crate::kernel::MemoryRangeExtent::Guards(guards) => {
                // The shared guards themselves, where the range was stated and
                // so carries them: a contract's own `a <= b` and the unsigned
                // `b - a <= limit` are the definition, and an assumed range
                // brings both. This is the route that lets a range fact be
                // used at element granularity without the proof restating a
                // bound the range already promised.
                if guards.iter().all(|guard| self.proves_exact(guard)) {
                    return true;
                }
                let element_count = Bitvector32Term::subtract(end.clone(), start.clone());
                // A count the term itself decides needs no facts: the shared
                // definition above only sees two symbolic endpoints, while
                // `hi - (hi - 1)` is one element for every `hi`.
                if let Some(count) = constant_element_count(&element_count) {
                    return (0..=i64::from(crate::kernel::memory_range_element_count_limit(
                        element_width,
                    )))
                        .contains(&count);
                }
                // The count spelling, which is both what a proof can write and
                // what a stated range carries: each guard by the exact routes
                // the loadability rules already use.
                crate::kernel::memory_range_element_count_guards(element_count, element_width)
                    .iter()
                    .all(|guard| match guard {
                        Proposition::ConditionIs(
                            ConditionTerm::Bitvector32SignedLessEqual(lower, upper),
                            true,
                        ) => self.proves_element_endpoint_order(lower, upper),
                        guard => self.proves_exact(guard),
                    })
            }
        }
    }

    /// [`Self::assumed_range_is_a_valid_byte_extent`] for an extent recovered
    /// as an element count rather than as a pair of endpoints.
    ///
    /// A rule that divides an assumed extent by an element width has the count
    /// but not always the endpoints: `loadable(p[0..n])` lowers its extent to
    /// `n * w`, whose count term is `n` with the zero start already folded
    /// away. The condition is the same one, and it is a condition on the count:
    /// `0 <= count` signed and `count <= u32::MAX / w` unsigned make `count * w`
    /// the true number of bytes the fact covers, so reading the fact as `count`
    /// elements of `w` bytes is exact. Restoring the start as `0` states it in
    /// the shared definition's own terms, and `count - 0` is `count`, so the
    /// facts a proof must supply are spelled over the count the user wrote.
    fn assumed_extent_covers_its_element_count(
        &self,
        element_count: &Bitvector32Term,
        element_width: u32,
    ) -> bool {
        // When the count still names both endpoints, ask about those: the
        // guards a contract states for `p[a..b]` are written over `a` and `b`,
        // and asking in the same spelling finds them.
        if let Bitvector32Term::Subtract(end, start) = element_count
            && self.assumed_range_is_a_valid_byte_extent(start, end, element_width)
        {
            return true;
        }
        self.assumed_range_is_a_valid_byte_extent(
            &Bitvector32Term::Constant(0),
            element_count,
            element_width,
        )
    }

    /// An upper bound on the number of elements a range can really span, from
    /// the range's own established extent facts, or `None` when it has none.
    ///
    /// This is what an affine constant difference needs before it may be read
    /// as an order. [`crate::kernel::assumptions::affine_bitvector_difference_constant`]
    /// works in `i64` while the endpoints are modular `Bitvector32Term`s, so
    /// its result is the true difference only modulo `2^32`; a residue is
    /// outside the range exactly when it is at least the range's element
    /// count, and that comparison needs the count bounded.
    ///
    /// The bound comes from the one shared definition of a valid 32-bit byte
    /// extent, [`crate::kernel::memory_range_element_count_guards`]. Its
    /// signed `0 <= count` half is the load-bearing one here: it pins the
    /// count below `2^31`, whatever the element width. The width's own
    /// element-count limit tightens it where that limit constrains an `int32`
    /// count at all — for four-byte elements to `1073741823`.
    pub(super) fn established_range_element_count_bound(
        &self,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
        element_width: u32,
    ) -> Option<i64> {
        crate::instrumentation::record_deterministic_work(1);
        let count = Bitvector32Term::subtract(end.clone(), start.clone());
        let guards = crate::kernel::memory_range_element_count_guards(count, element_width);
        guards
            .iter()
            .all(|guard| match guard {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessEqual(lower, upper),
                    true,
                ) => self.proves_element_endpoint_order(lower, upper),
                guard => self.proves_exact(guard),
            })
            .then(|| {
                i64::from(crate::kernel::memory_range_element_count_limit(
                    element_width,
                ))
                .min(i64::from(i32::MAX))
            })
    }

    /// `lower <= upper` for two element endpoints, by the exact routes the
    /// loadability rules already use: identical terms, two constants, an
    /// exact assumed comparison, or the bounded order-fact walk. A strict
    /// path also answers the non-strict question.
    pub(super) fn proves_element_endpoint_order(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if lower == upper {
            return true;
        }
        if let (Some(lower), Some(upper)) = (
            signed_bitvector_constant(lower),
            signed_bitvector_constant(upper),
        ) {
            return lower <= upper;
        }
        let condition = ConditionTerm::signed_less_equal(lower.clone(), upper.clone());
        if self.exact_condition_value(&condition) == Some(true)
            || self.has_exact_order_path(lower, upper, false)
        {
            return true;
        }
        // `c <= x - d` is `c + d <= x`, and the rewriting is exact when both
        // constants and their sum fit `int32`: `x - d` is then the number it
        // looks like, since `c + d <= x` puts it at or above `c`. This is the
        // shape a range carved one element short leaves — `p[0..n - 1]`, whose
        // own extent guard is `0 <= n - 1` while what the contract states is
        // `1 <= n` — and without it such a range has no established count.
        let Bitvector32Term::Subtract(base, decrement) = upper else {
            return false;
        };
        let (Some(lower), Some(decrement)) = (
            signed_bitvector_constant(lower),
            signed_bitvector_constant(decrement),
        ) else {
            return false;
        };
        // Subtracting a negative would be an addition, which can overflow out
        // of the bound rather than into it.
        if decrement < 0 {
            return false;
        }
        let Some(shifted) = lower
            .checked_add(decrement)
            .and_then(|shifted| i32::try_from(shifted).ok())
        else {
            return false;
        };
        self.proves_element_endpoint_order(&Bitvector32Term::Constant(shifted as u32), base)
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
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        if base.block != pointer.block {
            return false;
        }

        if let Some(index) =
            self.pointer_element_index_from_base_with_width(pointer, base, byte_width)
            && let Some(element_count) = element_count_from_bytes(bytes, byte_width)
            && self.assumed_extent_covers_its_element_count(&element_count, byte_width)
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

    /// Decides separation from indexed facts plus range membership, without
    /// invoking the composition-backed derived-separation search.
    pub(in crate::kernel) fn pointers_directly_disjoint_by_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        let direct = self
            .memory_separation_candidates(&left.block, &right.block)
            .find_map(|(proposition, left_range, right_range, _)| {
                (self.pointer_in_range_with_width(
                    left,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                    left_range.element_width(),
                ) && self.pointer_in_range_with_width(
                    right,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                    right_range.element_width(),
                ) || self.pointer_in_range_with_width(
                    right,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                    left_range.element_width(),
                ) && self.pointer_in_range_with_width(
                    left,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                    right_range.element_width(),
                ))
                .then_some(proposition)
            });
        if let Some(proposition) = direct {
            record_implicit_reasoning_provenance(self, proposition);
            return true;
        }
        false
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_shallow_explicit_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        self.memory_separation_candidates(&left.block, &right.block)
            .any(|(proposition, left_range, right_range, composition)| {
                let proved = self.pointer_in_range_by_shallow_fact_graph_with_width(
                    left,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                    left_range.element_width(),
                ) && self.pointer_in_range_by_shallow_fact_graph_with_width(
                    right,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                    right_range.element_width(),
                ) || self.pointer_in_range_by_shallow_fact_graph_with_width(
                    right,
                    left_range.base(),
                    left_range.start(),
                    left_range.end(),
                    left_range.element_width(),
                ) && self.pointer_in_range_by_shallow_fact_graph_with_width(
                    left,
                    right_range.base(),
                    right_range.start(),
                    right_range.end(),
                    right_range.element_width(),
                );
                if proved {
                    let authority = composition.map_or_else(
                        || proposition.clone(),
                        |resources| Proposition::CResourceComposition(resources.clone()),
                    );
                    record_implicit_reasoning_provenance(self, &authority);
                }
                proved
            })
            || self
                .resource_compositions
                .iter()
                .any(|resources| resources.proves_owned_pointers_separate_shallow(left, right))
    }

    pub(in crate::kernel) fn pointer_in_range_by_shallow_fact_graph_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
        element_width: u32,
    ) -> bool {
        if pointer_in_range_shallow(pointer, base, start, end, element_width, Some(self)) {
            return true;
        }
        if pointer.block != base.block {
            return false;
        }
        let offset_matches = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            pointer_offsets_match_by_shallow_fact_graph(left, right, self)
        };
        // The exact split, not `element_index_from_offset`: this rule ends in a
        // membership conclusion, and the index that function returns names the
        // pointer's element delta only modulo `2^32`.
        let delta = match &pointer.offset {
            PointerOffsetTerm::Add(left, right) if offset_matches(left, &base.offset) => {
                exact_element_delta_from_offset(right, element_width)
            }
            PointerOffsetTerm::Add(left, right) if offset_matches(right, &base.offset) => {
                exact_element_delta_from_offset(left, element_width)
            }
            _ if offset_matches(&pointer.offset, &base.offset) => Some(ExactElementDelta::zero()),
            _ => None,
        };
        let Some(delta) = delta else {
            return false;
        };
        // The exact bounds arm still wants the index as one term, which is what
        // a wholly symbolic or wholly constant delta already is.
        if let Some(index) = delta.as_index_term()
            && self.exact_condition_value(&ConditionTerm::signed_less_equal(
                start.clone(),
                index.clone(),
            )) == Some(true)
            && self
                .exact_condition_value(&ConditionTerm::signed_less_than(index.clone(), end.clone()))
                == Some(true)
        {
            return true;
        }
        let Some(count) = affine_range_element_count(start, end) else {
            return false;
        };
        exact_affine_index_difference(&delta.index, start, Some(self))
            .and_then(|difference| difference.checked_add(delta.constant))
            .is_some_and(|offset| 0 <= offset && offset < count)
    }

    /// One indexed explicit-fact step beyond structural containment. This is
    /// intentionally narrower than the general shallow fact-graph helper:
    /// it accepts only an exact base-offset alias and the two exact range
    /// bounds, so a named separation candidate does not need recursive
    /// memory resolution merely because its member index is symbolic.
    fn pointer_in_range_by_exact_facts(&self, pointer: &Pointer, range: &CMemoryRange) -> bool {
        if pointer_in_memory_range_shallow_with_facts(pointer, range, self) {
            return true;
        }
        if pointer.block != range.base().block {
            return false;
        }
        let offset_matches = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            pointer_offsets_match_by_shallow_fact_graph(left, right, self)
        };
        let index = pointer
            .element_index_from_base_with_width(range.base(), range.element_width())
            .or_else(|| match &pointer.offset {
                PointerOffsetTerm::Add(left, right)
                    if offset_matches(left, &range.base().offset) =>
                {
                    element_index_from_offset(right, range.element_width())
                }
                PointerOffsetTerm::Add(left, right)
                    if offset_matches(right, &range.base().offset) =>
                {
                    element_index_from_offset(left, range.element_width())
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

    pub(in crate::kernel) fn pointers_proven_disjoint_by_explicit_range_for_memory_resolution(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        let Some(_query) = crate::kernel::reasoning::ResolutionQueryGuard::enter(
            crate::kernel::reasoning::ResolutionQuery::RangeDisjoint(left.clone(), right.clone()),
        ) else {
            return false;
        };
        // Most execution-time separation certificates name the exact ranges
        // being accessed. Resolve those structurally before asking the
        // snapshot-aware containment prover, which may itself inspect memory
        // loads and is deliberately the more expensive second phase.
        let mut candidates = self.memory_separation_candidates(&left.block, &right.block);
        let record_candidate =
            |proposition: &Proposition, composition: Option<&ResourceContext>| {
                let authority = composition.map_or_else(
                    || proposition.clone(),
                    |resources| Proposition::CResourceComposition(resources.clone()),
                );
                record_implicit_reasoning_provenance(self, &authority);
            };
        if crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: shallow candidates",
            || {
                candidates
                    .clone()
                    .any(|(proposition, left_range, right_range, composition)| {
                        #[cfg(test)]
                        MEMORY_SEPARATION_CANDIDATE_CHECKS
                            .with(|checks| checks.set(checks.get() + 1));
                        let proved =
                            pointer_in_memory_range_shallow_with_facts(left, left_range, self)
                                && pointer_in_memory_range_shallow_with_facts(
                                    right,
                                    right_range,
                                    self,
                                )
                                || pointer_in_memory_range_shallow_with_facts(
                                    right, left_range, self,
                                ) && pointer_in_memory_range_shallow_with_facts(
                                    left,
                                    right_range,
                                    self,
                                );
                        if proved {
                            record_candidate(proposition, composition);
                        }
                        proved
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
                candidates
                    .clone()
                    .any(|(proposition, left_range, right_range, composition)| {
                        #[cfg(test)]
                        MEMORY_SEPARATION_CANDIDATE_CHECKS
                            .with(|checks| checks.set(checks.get() + 1));
                        let proved = self.pointer_in_range_by_exact_facts(left, left_range)
                            && self.pointer_in_range_by_exact_facts(right, right_range)
                            || self.pointer_in_range_by_exact_facts(right, left_range)
                                && self.pointer_in_range_by_exact_facts(left, right_range);
                        if proved {
                            record_candidate(proposition, composition);
                        }
                        proved
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
                self.resource_compositions.iter().any(|resources| {
                    let proved = resources.proves_owned_pointers_separate_shallow(left, right);
                    if proved {
                        record_implicit_reasoning_provenance(
                            self,
                            &Proposition::CResourceComposition(resources.clone()),
                        );
                    }
                    proved
                })
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
                    let proved = resources.proves_owned_pointers_separate_by(
                        left,
                        right,
                        |pointer, range| {
                            self.pointer_in_range_by_shallow_fact_graph_with_width(
                                pointer,
                                range.base(),
                                range.start(),
                                range.end(),
                                range.element_width(),
                            )
                        },
                    );
                    if proved {
                        record_implicit_reasoning_provenance(
                            self,
                            &Proposition::CResourceComposition(resources.clone()),
                        );
                    }
                    proved
                })
            },
        ) {
            return true;
        }

        // The recursive second phase re-enters offset-equality reasoning.
        crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: recursive candidates",
            || {
                candidates.any(|(proposition, left_range, right_range, composition)| {
                    #[cfg(test)]
                    {
                        MEMORY_SEPARATION_CANDIDATE_CHECKS
                            .with(|checks| checks.set(checks.get() + 1));
                        MEMORY_SEPARATION_RECURSIVE_CANDIDATE_CHECKS
                            .with(|checks| checks.set(checks.get() + 1));
                    }
                    let proved =
                        pointer_in_memory_range_for_memory_resolution(left, left_range, self)
                            && pointer_in_memory_range_for_memory_resolution(
                                right,
                                right_range,
                                self,
                            )
                            || pointer_in_memory_range_for_memory_resolution(
                                right, left_range, self,
                            ) && pointer_in_memory_range_for_memory_resolution(
                                left,
                                right_range,
                                self,
                            );
                    if proved {
                        record_candidate(proposition, composition);
                    }
                    proved
                })
            },
        )
    }

    pub(in crate::kernel) fn memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
        &self,
        left: &CMemoryRange,
        right: &CMemoryRange,
    ) -> bool {
        if left.base().blocks_proven_distinct(right.base()) {
            return true;
        }
        let Some(_query) = crate::kernel::reasoning::ResolutionQueryGuard::enter(
            crate::kernel::reasoning::ResolutionQuery::RangesSeparate(left.clone(), right.clone()),
        ) else {
            return false;
        };
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
            memory_range_shallowly_contained_with_facts(left, fact_left, self)
                && memory_range_contained_for_memory_resolution(right, fact_right, self)
                || memory_range_shallowly_contained_with_facts(right, fact_right, self)
                    && memory_range_contained_for_memory_resolution(left, fact_left, self)
                || memory_range_shallowly_contained_with_facts(right, fact_left, self)
                    && memory_range_contained_for_memory_resolution(left, fact_right, self)
                || memory_range_shallowly_contained_with_facts(left, fact_right, self)
                    && memory_range_contained_for_memory_resolution(right, fact_left, self)
        }) {
            return true;
        }
        self.prop_facts.iter().any(|proposition| {
            let Proposition::CResourceSeparate {
                left: CResource::Memory(fact_left),
                right: CResource::Memory(fact_right),
            } = proposition
            else {
                return false;
            };
            memory_range_contained_for_memory_resolution(left, fact_left, self)
                && memory_range_contained_for_memory_resolution(right, fact_right, self)
                || memory_range_contained_for_memory_resolution(right, fact_left, self)
                    && memory_range_contained_for_memory_resolution(left, fact_right, self)
        }) || self.resource_compositions.iter().any(|resources| {
            // The proof-aware form of the shallow composition fallback above:
            // the same containment relation the materialized-pair loops use,
            // served by the compact composition's indexed candidates.
            resources.proves_owned_memory_ranges_separate_by(left, right, |child, parent| {
                memory_range_contained_for_memory_resolution(child, parent, self)
            })
        })
    }

    fn pointer_element_index_from_base_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        byte_width: u32,
    ) -> Option<Bitvector32Term> {
        if pointer.block != base.block {
            return None;
        }
        // Exact syntax and direct offset arithmetic are authoritative on
        // their own. Resolve them before snapshot-aware equality: generated
        // range endpoints commonly retain a literal base plus an index, and
        // sending that shape through memory resolution first recursively
        // compares every nested load in the base expression.
        if let Some(index) = pointer.element_index_from_base_with_width(base, byte_width)
            && index.as_const().is_some()
        {
            return Some(index);
        }
        if let Some(index) =
            self.pointer_element_index_from_base_for_memory_resolution(pointer, base, byte_width)
        {
            return Some(index);
        }

        let offsets_equal = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            self.decide(&ConditionTerm::pointer_offset_equal(
                left.clone(),
                right.clone(),
            )) == Some(true)
        };
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if offsets_equal(left, &base.offset) {
                return element_index_from_offset(right, byte_width);
            }
            if offsets_equal(right, &base.offset) {
                return element_index_from_offset(left, byte_width);
            }
        }

        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if offsets_equal(&pointer.offset, left) {
                return element_index_from_offset(right, byte_width)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
            if offsets_equal(&pointer.offset, right) {
                return element_index_from_offset(left, byte_width)
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
        byte_width: u32,
    ) -> Option<Bitvector32Term> {
        #[cfg(test)]
        PROOF_AWARE_POINTER_INDEX_QUERIES.with(|queries| queries.set(queries.get() + 1));
        if pointer.block != base.block {
            return None;
        }
        if pointer.offset == base.offset {
            return Some(Bitvector32Term::Constant(0));
        }
        // A zero-offset object base leaves the pointer's scaled offset as
        // the exact element index. Preserve that symbolic index so the
        // ordinary endpoint checks can certify an in-bounds access directly.
        if base.offset == PointerOffsetTerm::Constant(0) {
            return element_index_from_offset(&pointer.offset, byte_width);
        }
        let offsets_match_for_resolution = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            left == right
                || crate::kernel::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
                    left, right, self,
                )
        };
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if offsets_match_for_resolution(left, &base.offset) {
                return element_index_from_offset(right, byte_width);
            }
            if offsets_match_for_resolution(right, &base.offset) {
                return element_index_from_offset(left, byte_width);
            }
        }
        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if offsets_match_for_resolution(&pointer.offset, left) {
                return element_index_from_offset(right, byte_width)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
            if offsets_match_for_resolution(&pointer.offset, right) {
                return element_index_from_offset(left, byte_width)
                    .map(|index| Bitvector32Term::subtract(Bitvector32Term::Constant(0), index));
            }
        }
        None
    }

    fn pointer_in_range_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
        element_width: u32,
    ) -> bool {
        // A loop invariant can establish that a havoced pointer local names
        // an address in an argument-backed range. Its symbolic block cannot
        // be indexed against that range directly, so follow the explicit
        // equality once to the concrete argument block. Restricting the
        // transport to symbolic blocks keeps this bounded and avoids walking
        // equality cycles back into the havoced pointer.
        if matches!(pointer.block, PointerBlock::Symbolic(_))
            && self.condition_facts.iter().any(|(condition, value)| {
                let ConditionTerm::PointerEqual(left, right) = condition else {
                    return false;
                };
                if !*value {
                    return false;
                }
                let equivalent = if left.as_ref() == pointer {
                    Some(right.as_ref())
                } else if right.as_ref() == pointer {
                    Some(left.as_ref())
                } else {
                    None
                };
                equivalent.is_some_and(|equivalent| {
                    !matches!(equivalent.block, PointerBlock::Symbolic(_))
                        && self.pointer_in_range_with_width(
                            equivalent,
                            base,
                            start,
                            end,
                            element_width,
                        )
                })
            })
        {
            return true;
        }
        let proves = |condition: ConditionTerm| {
            self.exact_condition_value(&condition) == Some(true)
                || self.exact_ordering_modulo_canonical_atoms(&condition)
                || self.nonnegative_successor_by_exact_facts(&condition)
                || self.decide(&condition) == Some(true)
        };
        let range_base = base.offset_by_elements(start.clone(), element_width);
        if let Some(index) =
            self.pointer_element_index_from_base_with_width(pointer, &range_base, element_width)
        {
            let range_length = Bitvector32Term::subtract(end.clone(), start.clone());
            if proves(ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                index.clone(),
            )) && proves(ConditionTerm::signed_less_than(index, range_length))
            {
                return true;
            }
        }

        let Some(index) =
            self.pointer_element_index_from_base_with_width(pointer, base, element_width)
        else {
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

    pub(crate) fn proves_resource_contains(&self, parent: &CResource, child: &CResource) -> bool {
        self.proves_resource_contains_inner(parent, child)
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

    pub(crate) fn proves_resource_separate(&self, left: &CResource, right: &CResource) -> bool {
        self.proves_resource_separate_inner(left, right)
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
            self.proves_resource_contains_inner(fact_left, left)
                && self.proves_resource_contains_inner(fact_right, right)
                || self.proves_resource_contains_inner(fact_left, right)
                    && self.proves_resource_contains_inner(fact_right, left)
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
                self.nonmemory_separation_facts.iter().any(entails)
            } else {
                self.prop_facts.iter().any(entails)
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
        if residual_hit {
            return true;
        }
        // The same candidates, projected from the compact compositions
        // instead of materialized propositions; two owned facts of one valid
        // composition are separate by the composition law.
        if let (CResource::Memory(left_range), CResource::Memory(right_range)) = (left, right)
            && self
                .memory_separation_candidates(&left_range.base().block, &right_range.base().block)
                .any(|(_, fact_left, fact_right, _)| {
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
            let composition_covers = |target: &CMemoryRange, other: &CMemoryRange| {
                self.resource_compositions.iter().any(|resources| {
                    let intervals = resources
                        .owned_memory_ranges_separate_from(
                            &target.base().block,
                            &CResource::Memory(other.clone()),
                            |owner, child| self.proves_resource_contains_inner(owner, child),
                        )
                        .into_iter()
                        .filter_map(|range| {
                            self.fact_range_interval_on_target(
                                target,
                                range.base(),
                                range.start(),
                                range.end(),
                            )
                        })
                        .collect();
                    range_intervals_cover_target(target, intervals)
                })
            };
            if composition_covers(left, right) || composition_covers(right, left) {
                return true;
            }
            return self.range_covered_by_resource_separate_ranges(left, right)
                || self.range_covered_by_resource_separate_ranges(right, left);
        }

        false
    }

    fn resource_contains_builtin(&self, parent: &CResource, child: &CResource) -> bool {
        if parent == child {
            return true;
        }
        let (CResource::Memory(parent), CResource::Memory(child)) = (parent, child) else {
            return false;
        };
        if self.memory_ranges_proven_equal(parent, child) {
            return true;
        }
        if Bitvector32Term::subtract(child.end.clone(), child.start.clone()).as_const() == Some(1) {
            let child_pointer = child
                .base
                .offset_by_elements(child.start.clone(), child.element_width());
            return self.pointer_in_range_with_width(
                &child_pointer,
                parent.base(),
                parent.start(),
                parent.end(),
                parent.element_width(),
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
        let Some(element_width) = common_pointer_offset_element_width(&left.offset, &right.offset)
        else {
            return false;
        };
        let (Some(left), Some(right)) = (
            element_index_from_offset(&left.offset, element_width),
            element_index_from_offset(&right.offset, element_width),
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
                        let Some(element_width) =
                            common_pointer_offset_element_width(fact_left, fact_right)
                        else {
                            continue;
                        };
                        let (Some(fact_left), Some(fact_right)) = (
                            element_index_from_offset(fact_left, element_width),
                            element_index_from_offset(fact_right, element_width),
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
        let base_delta = self.pointer_element_index_from_base_with_width(
            base,
            &target.base,
            target.element_width(),
        )?;
        let start = Bitvector32Term::add(base_delta.clone(), start.clone());
        let end = Bitvector32Term::add(base_delta, end.clone());
        Some((
            signed_bitvector_constant(&start)?,
            signed_bitvector_constant(&end)?,
        ))
    }

    /// Whether an access of `byte_width` bytes at element `index` of a range
    /// whose elements are `element_width` bytes lies wholly outside
    /// `start..end`.
    ///
    /// The access spans [`access_element_span`] elements from `index`, not
    /// one. It is outside the range when it ends at or before the range
    /// starts, or starts at or after the range ends. Deciding it from `index`
    /// alone — `index < start || end <= index` — let an `int64` read at the
    /// element just below a range be called separate from it, while its upper
    /// half sits on the range's first element; every framing route that asks
    /// this question then carried the read across a write there.
    ///
    /// `access_element_span` is the exclusion side's count and deliberately
    /// not [`authorized_access_element_length`]: eight bytes at an address
    /// could be a pointer or an `int64`, and the permission side's struct
    /// field rule reads that width as one four-byte field. The two may
    /// disagree only in this direction — a range may authorize an access it is
    /// not proven separate from, which costs a framing conclusion, while the
    /// reverse is the false theorem.
    ///
    /// Returns `None` when the access has no element span in this range's
    /// coordinates, which is the same declining that
    /// [`Self::pointer_access_in_range`] does rather than rounding onto a
    /// boundary.
    fn constant_access_outside_range(
        index: i64,
        start: i64,
        end: i64,
        byte_width: u32,
        element_width: u32,
    ) -> Option<bool> {
        let length =
            crate::kernel::memory_provenance::access_element_span(byte_width, element_width)?;
        Some(
            index
                .checked_add(length)
                .is_some_and(|access_end| access_end <= start)
                || end <= index,
        )
    }

    pub(in crate::kernel) fn pointer_access_in_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        base: &Pointer,
        start: &Bitvector32Term,
        end: &Bitvector32Term,
        element_width: u32,
    ) -> bool {
        // Keep an access at its selected range base when their equality is
        // explicit. Resolving only the access can otherwise lose an exact
        // match after learning that a symbolic callback result aliases an
        // external argument. This probes one equality, not ambient facts.
        let resolved = if pointer == base
            || self
                .exact_condition_value(&ConditionTerm::pointer_equal(pointer.clone(), base.clone()))
                == Some(true)
        {
            base.clone()
        } else {
            crate::kernel::reasoning::resolve_symbolic_pointer_alias(pointer, self)
        };
        let pointer = &resolved;
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
        };
        // Ranges count logical elements, while accesses are measured in
        // bytes. A pointer-sized field is therefore two int32-width
        // elements, but a byte access is one byte element.
        if element_width > 0
            && byte_width.is_multiple_of(element_width)
            && let Some(index) = pointer.element_index_from_base_with_width(base, element_width)
            && let Some(logical_access_length) =
                authorized_access_element_length(byte_width, element_width)
        {
            let access_length = Bitvector32Term::Constant(logical_access_length);
            let access_end = Bitvector32Term::add(index.clone(), access_length);
            let exact_within_range = match (
                super::exact_signed_constant(&index, self),
                super::exact_signed_constant(start, self),
                super::exact_signed_constant(end, self),
            ) {
                (Some(index), Some(start), Some(end)) => {
                    let access_length = i64::from(logical_access_length);
                    start <= index
                        && index
                            .checked_add(access_length)
                            .is_some_and(|access_end| access_end <= end)
                }
                _ => false,
            };
            let within_range = exact_within_range
                || if byte_width == element_width {
                    // A one-element access occupies the half-open interval
                    // [index, index + 1), so its endpoint is expressed by the
                    // strict element-membership check below. Wider accesses
                    // need their successor endpoint to be at most `end`.
                    proves_order(start, &index, false) && proves_order(&index, end, true)
                } else {
                    proves_order(start, &index, false) && proves_order(&access_end, end, false)
                };
            if within_range {
                return true;
            }
        }

        // A held range describes a physical byte footprint even when its
        // public bounds use another logical element width. This matters for
        // ABI structs: the allocation's complete int32-indexed access can
        // authorize a uint8 field or a pointer field at its byte offset.
        // Keep this fallback read-only; resource consumption still requires
        // matching logical range units so splitting ownership remains exact.
        let range_base = base.offset_by_elements(start.clone(), element_width);
        let range_bytes = Bitvector32Term::multiply(
            Bitvector32Term::subtract(end.clone(), start.clone()),
            Bitvector32Term::Constant(element_width),
        );
        if let Some(byte_offset) = pointer_byte_offset_from_base(pointer, &range_base) {
            let access_end =
                Bitvector32Term::add(byte_offset.clone(), Bitvector32Term::Constant(byte_width));
            if self.decide(&ConditionTerm::signed_greater_equal(
                byte_offset,
                Bitvector32Term::Constant(0),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(access_end, range_bytes))
                    == Some(true)
            {
                return true;
            }
        }

        if element_width > 0 && byte_width.is_multiple_of(element_width) {
            let range_base = base.offset_by_elements(start.clone(), element_width);
            let access_length = Bitvector32Term::Constant(byte_width / element_width);
            if pointer == &range_base
                && end == &Bitvector32Term::add(start.clone(), access_length.clone())
            {
                return true;
            }
            if let Some(index) =
                self.pointer_element_index_from_base_with_width(pointer, &range_base, element_width)
            {
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

        if byte_width == 1 && element_width == 1 {
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
        let expanded = self.frame_frontier_compositions(memory);
        if expanded.is_empty() {
            return false;
        }
        ranges.iter().all(|range| {
            expanded.iter().any(|resources| {
                resources.proves_owned_range_separate_from_pointer_with(
                    range,
                    pointer,
                    |range, available| {
                        memory_range_shallowly_contained_with_facts(range, available, self)
                            || self.memory_range_contained_by_decided_endpoints(range, available)
                    },
                    |pointer, available| {
                        self.pointer_in_range_by_shallow_fact_graph_with_width(
                            pointer,
                            available.base(),
                            available.start(),
                            available.end(),
                            available.element_width(),
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
        self.ranges_directly_disjoint_from_access(
            ranges,
            pointer,
            access_byte_width_for_separation(pointer),
        )
    }

    /// [`Self::ranges_directly_disjoint_from_pointer`] for a caller that knows
    /// how many bytes the access reads. Separation is a question about bytes,
    /// and the callers above hold only an address, so they recover the width
    /// from the record every typed C load writes.
    pub(in crate::kernel) fn ranges_directly_disjoint_from_access(
        &self,
        ranges: &[CMemoryRange],
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        ranges.iter().all(|range| {
            if range.base.blocks_proven_distinct(pointer) {
                return true;
            }
            if pointer_in_memory_range_shallow_with_facts(pointer, range, self) {
                return false;
            }
            if self.resource_compositions.iter().any(|resources| {
                resources.proves_owned_range_separate_from_pointer_shallow(
                    range,
                    pointer,
                    |pointer, available| {
                        self.pointer_in_range_by_shallow_fact_graph_with_width(
                            pointer,
                            available.base(),
                            available.start(),
                            available.end(),
                            available.element_width(),
                        ) || self.pointer_directly_in_memory_range(pointer, available)
                    },
                )
            }) {
                return true;
            }
            let direct_index = self.direct_pointer_element_index_from_base_with_width(
                pointer,
                &range.base,
                range.element_width(),
            );
            if let Some(index) = direct_index.as_ref()
                && let (Some(index), Some(start), Some(end)) = (
                    signed_bitvector_constant(index),
                    signed_bitvector_constant(&range.start),
                    signed_bitvector_constant(&range.end),
                )
                && let Some(outside) = Self::constant_access_outside_range(
                    index,
                    start,
                    end,
                    byte_width,
                    range.element_width(),
                )
            {
                return outside;
            }
            if let Some(proposition) =
                self.prop_facts
                    .iter()
                    .find(|proposition| match proposition {
                        Proposition::CResourceSeparate {
                            left: CResource::Memory(left_range),
                            right: CResource::Memory(right_range),
                        } => {
                            memory_range_shallowly_contained_with_facts(range, left_range, self)
                                && (pointer_in_memory_range_shallow_with_facts(
                                    pointer,
                                    right_range,
                                    self,
                                ) || self
                                    .pointer_directly_in_memory_range(pointer, right_range))
                                || memory_range_shallowly_contained_with_facts(
                                    range,
                                    right_range,
                                    self,
                                ) && (pointer_in_memory_range_shallow_with_facts(
                                    pointer, left_range, self,
                                ) || self
                                    .pointer_directly_in_memory_range(pointer, left_range))
                                || pointer_in_memory_range_shallow_with_facts(
                                    pointer, left_range, self,
                                ) && memory_range_contained_for_memory_resolution(
                                    range,
                                    right_range,
                                    self,
                                )
                                || pointer_in_memory_range_shallow_with_facts(
                                    pointer,
                                    right_range,
                                    self,
                                ) && memory_range_contained_for_memory_resolution(
                                    range, left_range, self,
                                )
                                || self.pointer_directly_in_memory_range(pointer, left_range)
                                    && memory_range_contained_for_memory_resolution(
                                        range,
                                        right_range,
                                        self,
                                    )
                                || self.pointer_directly_in_memory_range(pointer, right_range)
                                    && memory_range_contained_for_memory_resolution(
                                        range, left_range, self,
                                    )
                        }
                        _ => false,
                    })
            {
                record_implicit_reasoning_provenance(self, proposition);
                return true;
            }

            let Some(index) = direct_index else {
                return false;
            };
            bitvector_index_outside_range_shallow(
                &index,
                &range.start,
                &range.end,
                range.element_width(),
                self,
            )
        })
    }

    /// Whether two pointer offsets name the same displacement, by equality of
    /// the offsets themselves or of two equally scaled indices.
    fn pointer_offsets_equal_from_facts(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
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
            ) => left_width == right_width && self.bitvector_terms_equal_from_facts(left, right),
            _ => false,
        }
    }

    fn direct_pointer_element_index_from_base_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        element_width: u32,
    ) -> Option<Bitvector32Term> {
        if pointer.block != base.block {
            return None;
        }
        if self.pointer_offsets_equal_from_facts(&pointer.offset, &base.offset) {
            return Some(Bitvector32Term::Constant(0));
        }
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if self.pointer_offsets_equal_from_facts(left, &base.offset) {
                return element_index_from_offset(right, element_width);
            }
            if self.pointer_offsets_equal_from_facts(right, &base.offset) {
                return element_index_from_offset(left, element_width);
            }
        }
        pointer.element_index_from_base_with_width(base, element_width)
    }

    /// [`Self::direct_pointer_element_index_from_base_with_width`] for a caller
    /// that concludes *membership* rather than exclusion.
    ///
    /// The same shapes, refusing the ones where the index it would return is
    /// the pointer's element delta only modulo `2^32`. An exclusion survives
    /// that reduction and a membership does not; see
    /// [`crate::kernel::reasoning::ExactElementDelta`].
    fn direct_pointer_exact_element_delta_from_base_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        element_width: u32,
    ) -> Option<ExactElementDelta> {
        if pointer.block != base.block {
            return None;
        }
        if self.pointer_offsets_equal_from_facts(&pointer.offset, &base.offset) {
            return Some(ExactElementDelta::zero());
        }
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if self.pointer_offsets_equal_from_facts(left, &base.offset) {
                return exact_element_delta_from_offset(right, element_width);
            }
            if self.pointer_offsets_equal_from_facts(right, &base.offset) {
                return exact_element_delta_from_offset(left, element_width);
            }
        }
        pointer.exact_element_delta_from_base(base, element_width, Some(self))
    }

    fn pointer_directly_in_memory_range(&self, pointer: &Pointer, range: &CMemoryRange) -> bool {
        let Some(delta) = self.direct_pointer_exact_element_delta_from_base_with_width(
            pointer,
            &range.base,
            range.element_width(),
        ) else {
            return false;
        };
        // The rule below states the index as a term, so a delta that is one
        // term — a symbolic index, or a wholly constant one — gets all of it.
        // A symbolic index beside a nonzero constant can only be joined by a
        // modular add, so that shape takes the affine tail directly, which
        // keeps the constant in `i64`.
        let Some(index) = delta.as_index_term() else {
            return element_delta_in_range_by_affine_arithmetic(
                &delta,
                &range.start,
                &range.end,
                self,
            );
        };
        if let (Some(index), Some(start), Some(end)) = (
            super::exact_signed_constant(&index, self),
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
        let Some(base_index) = range
            .base()
            .element_index_from_base_with_width(available.base(), available.element_width())
        else {
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

    /// The compositions with each owned composite opened exactly one level
    /// over `memory`: a composite's frontier is the regions its body denotes
    /// at the snapshot the composition holds at, named with the same load
    /// variables the live facts use. Nested composites stay folded, so a
    /// cell below the frontier is framed only through a live observation or
    /// an unfold, never by the kernel reading inside a folded body.
    fn frame_frontier_compositions(&self, memory: &CMemory) -> Vec<ResourceContext> {
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
            let computed =
                crate::kernel::functions::expand_owned_composite_resource_facts_one_level(
                    composition,
                    &definitions,
                    memory,
                    &PureFactContext::new(),
                );
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
        if pointer_in_memory_range_shallow_with_facts(pointer, range, self) {
            return false;
        }
        let owned_member_holds_pointer = |resources: &ResourceContext| {
            resources.proves_owned_range_separate_from_pointer_shallow(
                range,
                pointer,
                |pointer, available| {
                    self.pointer_in_range_by_shallow_fact_graph_with_width(
                        pointer,
                        available.base(),
                        available.start(),
                        available.end(),
                        available.element_width(),
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
        if let Some(proposition) = self
            .prop_facts
            .iter()
            .find(|proposition| match proposition {
                Proposition::CResourceSeparate {
                    left: CResource::Memory(left_range),
                    right: CResource::Memory(right_range),
                } => {
                    memory_range_shallowly_contained_with_facts(range, left_range, self)
                        && pointer_in_memory_range_shallow_with_facts(pointer, right_range, self)
                        || memory_range_shallowly_contained_with_facts(range, right_range, self)
                            && pointer_in_memory_range_shallow_with_facts(pointer, left_range, self)
                }
                _ => false,
            })
        {
            record_implicit_reasoning_provenance(self, proposition);
            return true;
        }
        if let Some(index) = self.direct_pointer_element_index_from_base_with_width(
            pointer,
            &range.base,
            range.element_width(),
        ) {
            // Literal constants first; otherwise resolve each bound through
            // equality facts with per-load snapshot bridging, so a range
            // like data[split..split+1] with split provably 1 proves
            // disjoint from data[0].
            let resolve = |term: &Bitvector32Term| {
                signed_bitvector_constant(term)
                    .or_else(|| self.known_signed_constant_after_normalization(term))
            };
            let byte_width = access_byte_width_for_separation(pointer);
            if let (Some(index), Some(start), Some(end)) =
                (resolve(&index), resolve(&range.start), resolve(&range.end))
                && Self::constant_access_outside_range(
                    index,
                    start,
                    end,
                    byte_width,
                    range.element_width(),
                ) == Some(true)
            {
                return true;
            }
            // `index < start` says the access *starts* below the range, which
            // places the whole of it below only while the access is one
            // element wide. A wider one is declined here rather than restated
            // as `index + length <= start`: that sum is a modular add, and
            // `ad1a0050`/`b92ab3c0` are what reading a wrapped sum as an order
            // costs. The range's upper side needs no length, because an access
            // at or above `end` extends away from the range.
            let single_element = crate::kernel::memory_provenance::access_element_span(
                byte_width,
                range.element_width(),
            ) == Some(1);
            if single_element
                && self.decide(&ConditionTerm::signed_less_than(
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
        // Direct address arithmetic on the range's base offset, last: it
        // decides only what the layers above could not name, and each
        // attempt costs two decisions.
        if let PointerOffsetTerm::Add(left, right) = &range.base.offset {
            let forward_offset = if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                left.as_ref().clone(),
            )) == Some(true)
            {
                element_index_from_offset(right, range.element_width())
            } else if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                right.as_ref().clone(),
            )) == Some(true)
            {
                element_index_from_offset(left, range.element_width())
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
        false
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

        let fact_base = base.offset_by_elements(start.clone(), range.element_width());
        let range_base = range
            .base
            .offset_by_elements(range.start.clone(), range.element_width());
        let shifted_base_delta = crate::instrumentation::measure_operation(
            "kernel",
            "fact range coverage",
            "fact range coverage: shifted base relation",
            || {
                self.pointer_element_index_from_base_with_width(
                    &range_base,
                    &fact_base,
                    range.element_width(),
                )
            },
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
            || {
                self.pointer_element_index_from_base_with_width(
                    &range.base,
                    base,
                    range.element_width(),
                )
            },
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
