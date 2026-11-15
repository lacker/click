use super::*;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{MachineCastSpelling, MachineTerm};
use crate::kernel::{bits32_constant, constant_u32, int32_constant};

#[cfg(test)]
thread_local! {
    static PROOF_AWARE_POINTER_INDEX_QUERIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

thread_local! {
    /// Definitions used when a store opens selected live resource instances
    /// whose arguments name cached cells. Recorded compositions remain folded;
    /// frame queries consult only the facts their indexes already expose.
    static FRAME_COMPOSITE_DEFINITIONS: std::cell::RefCell<
        Vec<std::sync::Arc<Vec<CompositeResourceDefinition>>>,
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
/// Minimum footprint a read candidate may need under the kernel's existing
/// logical pointer-cell convention. This only selects candidates: the range's
/// actual element width and the complete permission check remain authoritative.
/// The struct count `m` and struct width `k` a wide range at element 0
/// holds: `m` of a byte range `base[0..m * k]` (a `uint64` product with a
/// constant `k >= 2`, the block of `malloc(m * sizeof(struct T))`), or the end
/// `m` of a range `base[0..m]` of `k >= 2`-byte elements (a contract's
/// `owns p[0..n]` on a struct pointer). A structural reading of the range's
/// own endpoints; `None` for any other shape.
pub(in crate::kernel) fn wide_struct_array_count(
    range: &MemoryRange,
) -> Option<(&MachineTerm, i64)> {
    let (start, end) = range.wide_bounds()?;
    if start.uint64_as_const() != Some(0) {
        return None;
    }
    let (count, stride) = if range.element_width() == 1 {
        let binary_term!(UInt64, Multiply, left, right) = end else {
            return None;
        };
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (None, Some(stride)) => (left.as_ref(), stride),
            (Some(stride), None) => (right.as_ref(), stride),
            _ => return None,
        }
    } else {
        (end, u64::from(range.element_width()))
    };
    let stride = i64::try_from(stride).ok().filter(|stride| *stride >= 2)?;
    Some((count, stride))
}

pub(in crate::kernel) fn read_candidate_byte_width(byte_width: u32) -> u32 {
    if byte_width == crate::kernel::C_POINTER_BYTE_WIDTH {
        4
    } else {
        byte_width
    }
}

fn authorized_access_element_length(byte_width: u32, element_width: u32) -> Option<u32> {
    if element_width == 0 || byte_width == 0 {
        return None;
    }
    if element_width == 4 {
        return Some(read_candidate_byte_width(byte_width).div_ceil(element_width));
    }
    Some(byte_width.div_ceil(element_width))
}

/// How many bytes the access at this address reads, for a separation question
/// whose caller holds only the address.
///
/// The C type at an address does not vary with the state a framing walk
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
    definitions: Vec<CompositeResourceDefinition>,
) -> FrameCompositeDefinitionsGuard {
    FRAME_COMPOSITE_DEFINITIONS
        .with(|armed| armed.borrow_mut().push(std::sync::Arc::new(definitions)));
    FrameCompositeDefinitionsGuard { _private: () }
}

pub(in crate::kernel) fn frame_composite_definitions()
-> Option<std::sync::Arc<Vec<CompositeResourceDefinition>>> {
    FRAME_COMPOSITE_DEFINITIONS.with(|definitions| definitions.borrow().last().cloned())
}

use crate::kernel::scaled_extent_element_width;

/// A term as a base plus a constant shift, peeling the additive and
/// subtractive constants a range endpoint is written with. `hi - 1` is `hi`
/// shifted by `-1`; anything else is itself shifted by `0`. One level, no
/// facts, no recursion budget.
fn endpoint_base_and_shift(term: &MachineTerm) -> (&MachineTerm, i64) {
    match term {
        binary_term!(Int32, Add, left, right) => match (left.as_ref(), right.as_ref()) {
            (base, bits32_constant!(shift)) => (base, i64::from(constant_u32(*shift) as i32)),
            (int32_constant!(shift), base) => (base, i64::from(constant_u32(*shift) as i32)),
            _ => (term, 0),
        },
        binary_term!(Int32, Subtract, left, right) => match right.as_ref() {
            bits32_constant!(shift) => (left.as_ref(), -i64::from(constant_u32(*shift) as i32)),
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
/// [`PureFactContext::assumed_extent_covers_its_element_count`] already restores
/// the same start for the same reason; sharing one reading keeps a range
/// written from `0` — which is how a C contract usually writes one — from
/// being a different kind of range to the rules than `p[a..b]` is.
fn element_count_endpoints(element_count: &MachineTerm) -> (&MachineTerm, &MachineTerm) {
    const ZERO: &MachineTerm = &MachineTerm::constant(0);
    match element_count {
        binary_term!(Int32, Subtract, end, start) => (start.as_ref(), end.as_ref()),
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
fn constant_element_count(element_count: &MachineTerm) -> Option<i64> {
    if let Some(value) = signed_bitvector_constant(element_count) {
        return Some(value);
    }
    let binary_term!(Int32, Subtract, end, start) = element_count else {
        return None;
    };
    let (end_base, end_shift) = endpoint_base_and_shift(end);
    let (start_base, start_shift) = endpoint_base_and_shift(start);
    (end_base == start_base).then_some(end_shift - start_shift)
}

/// A constant byte extent still written as an endpoint difference, possibly
/// scaled once by an element width. Read only this expression, without facts
/// or rewriting away the endpoints other range rules need. The cast and
/// product use the extent's own modular 32-bit arithmetic.
fn structural_constant_byte_extent(bytes: &MachineTerm) -> Option<u32> {
    crate::instrumentation::record_deterministic_work(1);
    match bytes {
        binary_term!(Int32, Multiply, left, right) => match (left.as_ref(), right.as_ref()) {
            (count, bits32_constant!(width)) | (int32_constant!(width), count) => {
                constant_element_count(count)
                    .map(|count| (count as u32).wrapping_mul(constant_u32(*width)))
            }
            _ => None,
        },
        _ => constant_element_count(bytes).map(|count| count as u32),
    }
}

pub(in crate::kernel) fn signed_byte_sum_is_nonwrapping_views(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
    sum: MachineOperandView<'_>,
    mut proves_signed_less_equal: impl FnMut(MachineOperandView<'_>, MachineOperandView<'_>) -> bool,
) -> bool {
    let zero = MachineTerm::constant(0);
    proves_signed_less_equal(MachineOperandView::Legacy(&zero), left)
        && proves_signed_less_equal(MachineOperandView::Legacy(&zero), right)
        && proves_signed_less_equal(left, sum)
}

impl PureFactContext {
    /// A validity premise frames only across a lifetime-preserving, value-
    /// preserving memory edge. Value equalities alone are never authority.
    pub(crate) fn has_memory_read_defined_evidence(
        &self,
        memory: &Memory,
        pointer: &Pointer,
        value_type: ProgramType,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if self.memory_read_defined_facts.is_empty() {
            return false;
        }
        let evidence_at = |candidate: &Pointer| {
            let key = (
                crate::kernel::api::canonicalize_pointer_loads(candidate),
                value_type,
            );
            crate::instrumentation::record_deterministic_work(1);
            let Some(facts) = self.memory_read_defined_facts.get(&key) else {
                return false;
            };
            let exact = Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: pointer.clone(),
                value_type,
            };
            if facts.contains(&exact) {
                return true;
            }
            // Allocation bookkeeping and local cleanup have one adjacent
            // entry. Select its fact by state key, without enumerating
            // other facts about this address. The edge check below must prove
            // that cleanup did not retire this cell.
            let current = crate::kernel::intern_memory_ref(memory);
            if let Some(step) = current.derivation()
                && matches!(
                    step.as_ref(),
                    crate::kernel::MemoryDerivation::HeapAllocationPending { .. }
                        | crate::kernel::MemoryDerivation::HeapAllocationFailed { .. }
                        | crate::kernel::MemoryDerivation::LocalLifetimeEnded { .. }
                )
            {
                let before = step.base();
                let premise = Proposition::MemoryReadDefined {
                    memory: before.as_ref().clone(),
                    pointer: candidate.clone(),
                    value_type,
                };
                if facts.contains(&premise)
                    && !candidate.blocks_proven_distinct(pointer)
                    && self.pointers_known_equal(candidate, pointer)
                    && crate::kernel::memory_provenance::typed_read_has_same_memory_source(
                        before,
                        memory,
                        candidate,
                        value_type.byte_width(),
                        self,
                    )
                {
                    return true;
                }
            }
            // A state bucket is not a premise list. A selected source must
            // retain its type, address, lifetime, and value-preserving edge.
            if facts.len() != 1 {
                return false;
            }
            let Some(Proposition::MemoryReadDefined {
                memory: before,
                pointer: source,
                ..
            }) = facts.iter().next()
            else {
                return false;
            };
            if source.blocks_proven_distinct(pointer) || !self.pointers_known_equal(source, pointer)
            {
                return false;
            }
            before == memory
                || before.read_region_identity(source) == memory.read_region_identity(source)
                    && crate::kernel::memory_provenance::typed_read_has_same_memory_source(
                        before,
                        memory,
                        source,
                        value_type.byte_width(),
                        self,
                    )
        };
        if evidence_at(pointer) {
            return true;
        }
        let storage = self.equality_graph.storage_address(pointer);
        if storage != *pointer && evidence_at(&storage) {
            return true;
        }
        if let Some(coordinate) = self.equality_graph.canonical_pointer(pointer)
            && let Some(offset) = coordinate.offset.to_offset_term()
            && evidence_at(&Pointer {
                block: coordinate.representative,
                offset,
            })
        {
            return true;
        }
        // Explicit source selection may use a nonrepresentative spelling.
        // Cached lengths identify that one source without walking its class.
        self.memory_read_defined_facts.len() == 1
            && self
                .memory_read_defined_facts
                .keys()
                .next()
                .is_some_and(|(source, kind)| *kind == value_type && evidence_at(source))
    }

    /// Typed read validity requires initialization as well as a live range.
    /// Specification evaluation and value equalities alone cannot initialize bytes.
    pub(crate) fn proves_memory_read_defined(
        &self,
        memory: &Memory,
        pointer: &Pointer,
        value_type: ProgramType,
    ) -> bool {
        if self.has_memory_read_defined_evidence(memory, pointer, value_type) {
            return true;
        }
        let initialized_cell = |address: &Pointer| {
            memory
                .known_value(address)
                .is_some_and(|value| value_type.read_cell(&value).is_some())
                && !memory.is_ended_local_address(address)
                && !memory.is_deallocated_heap_address(address, self)
                && !memory.is_uninitialized_heap_address(address, value_type.byte_width(), self)
        };
        if initialized_cell(pointer) {
            return true;
        }
        // The equality index selects one concrete storage anchor, including
        // its affine offset. Do not enumerate alternative address spellings.
        let storage = self.equality_graph.storage_address(pointer);
        // Viewability establishes an address range, not initialized contents.
        // A typed read can span several cached cells (for example a pointer
        // in a struct represented by 32-bit cells). Inspect only its selected
        // bytes, never the cache or memory history. Specification evaluation
        // below still checks the typed value, bounds, and lifetime.
        let initialized_bytes = |address: &Pointer| {
            let width = value_type.byte_width();
            if memory.has_initialized_bytes_at(address, width) {
                return true;
            }
            let mut covered = 0;
            while covered < width {
                crate::instrumentation::record_deterministic_work(1);
                let Some(value) = memory.known_value(&address.offset_by_bytes(covered)) else {
                    return false;
                };
                let bytes = value.byte_width();
                if bytes == 0 {
                    return false;
                }
                covered += bytes.min(width - covered);
            }
            true
        };
        let canonical = self
            .equality_graph
            .canonical_pointer(pointer)
            .and_then(|coordinate| {
                Some(Pointer {
                    block: coordinate.representative,
                    offset: coordinate.offset.to_offset_term()?,
                })
            });
        if !initialized_bytes(pointer)
            && (storage == *pointer || !initialized_bytes(&storage))
            && !canonical.as_ref().is_some_and(|address| {
                address != pointer && address != &storage && initialized_bytes(address)
            })
        {
            return false;
        }
        // With no range, alias, or allocation evidence, other materialized
        // cells cannot justify this unknown address. This is also the empty
        // context used by lowering to recognize structurally valid reads.
        if self.condition_facts.is_empty()
            && self.prop_facts.is_empty()
            && self.resource_compositions.is_empty()
            && memory.blocks.is_empty()
        {
            return false;
        }
        // Validity cannot hold without a covering byte range. Check that
        // first: in particular, the empty context used by logical lowering
        // must not resolve aliases across a whole symbolic memory merely to
        // discover that no range was available.
        if !self.proves_memory_access(memory, pointer, value_type.byte_width()) {
            return false;
        }
        let paths = crate::kernel::eval::evaluate_spec_memory_load_paths(
            memory,
            pointer.clone(),
            value_type,
            Vec::new().into(),
            Vec::new(),
            self,
        );
        matches!(paths.as_slice(), [path]
            if matches!(path.outcome, ExpressionOutcome::Value(_))
                // Read equations are certified results of this evaluation,
                // not additional premises the caller must already know.
                && path.facts.iter().all(|fact| fact.is_logical_read_equation()
                    || self.proves_exact(fact.proposition())
                    || crate::kernel::is_load_variable_defining_fact(fact.proposition()))
                && path.obligations.iter().all(|obligation|
                    self.proves_exact(obligation.proposition())
                    || self.proves_atomic_memory_or_resource(obligation.proposition())))
    }

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
        memory: &Memory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.proves_memory_loadable(memory, pointer, &MachineTerm::constant(byte_width))
    }

    /// Carry a native liveness range, or a checked subrange, through
    /// memory states. Counts are compared as complete unsigned 64-bit
    /// values; this does not transport byte values. Retirement is checked at
    /// the evidence's address, just as for ordinary read ranges.
    pub(crate) fn proves_native_memory_loadable(
        &self,
        memory: &Memory,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        // Exact evidence is an indexed lookup even when its address holds
        // many other views. Choosing a different premise belongs to search.
        crate::instrumentation::record_deterministic_work(1);
        if self.contains_assumed_exact(&Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: bytes.clone(),
            wide: true,
        }) {
            return true;
        }

        if bytes.uint64_as_const() == Some(0) {
            return true;
        }
        // A constant count inside the base's own allocation is live by the
        // block rules the 32-bit prover uses; both read only that block.
        if let Some(count) = bytes.uint64_as_const()
            && let Ok(count) = u32::try_from(count)
            && (memory.access_in_bounds(base, count)
                || self.proves_access_from_memory_block(memory, base, count))
        {
            return true;
        }
        // A count no larger than a 32-bit constant range at this base names
        // bytes inside that range, which the narrow prover carries through
        // states. It is consulted only when this base indexes such a
        // range, so a refusal stays independent of other addresses' facts.
        let narrow_cover = self
            .memory_loadable_exact_candidates_for_base(base)
            .filter_map(|fact| match fact {
                Proposition::MemoryLoadable {
                    bytes: int32_constant!(held),
                    wide: false,
                    ..
                } => Some(constant_u32(*held)),
                _ => None,
            })
            .max();
        if let Some(held) = narrow_cover
            && (bytes
                .uint64_as_const()
                .is_some_and(|count| count <= u64::from(held))
                || self.decide(&ConditionTerm::uint64_less_equal(
                    bytes.clone(),
                    MachineTerm::uint64_constant(u64::from(held)),
                )) == Some(true))
            && self.proves_memory_loadable(memory, base, &MachineTerm::constant(held))
        {
            return true;
        }
        let prefix = self
            .memory_loadable_exact_candidates_for_base(base)
            .any(|fact| {
                let Proposition::MemoryLoadable {
                    memory: before,
                    base: source_base,
                    bytes: source_bytes,
                    wide: true,
                } = fact
                else {
                    return false;
                };
                crate::instrumentation::record_deterministic_work(1);
                source_base == base
                    && (source_bytes == bytes
                        || self.decide(&ConditionTerm::uint64_less_equal(
                            bytes.clone(),
                            source_bytes.clone(),
                        )) == Some(true))
                    && before.read_region_identity(source_base) == memory.read_region_identity(base)
                    && memory_range_still_available(before, memory, source_base, self)
            });
        if prefix {
            return true;
        }
        // A cursor commonly advances from an exact parent offset, or from
        // offset zero in its symbolic block. Query only those structural
        // anchors; do not enumerate the other views in the block.
        let mut offsets = vec![base.offset.clone(), PointerOffsetTerm::Constant(0)];
        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            offsets.push(left.as_ref().clone());
            offsets.push(right.as_ref().clone());
        }
        let mut seen = Vec::new();
        for offset in offsets {
            if seen.contains(&offset) {
                continue;
            }
            seen.push(offset.clone());
            let anchor = Pointer {
                block: base.block.clone(),
                offset,
            };
            if self
                .memory_loadable_exact_candidates_for_base(&anchor)
                .any(|fact| self.native_loadable_subrange_from(fact, memory, base, bytes))
            {
                return true;
            }
        }
        // Explicit transport selects one source view. A lone source can
        // therefore cover a shifted constant base even when normalization
        // has removed the structural parent. Inspect at most two entries to
        // recognize this case, never scan an ambient block's ranges.
        let mut candidates = self.memory_loadable_candidates_for_base(base);
        let first = candidates.next();
        match (first, candidates.next()) {
            (Some(source), None) => self.native_loadable_subrange_from(source, memory, base, bytes),
            _ => false,
        }
    }

    fn native_loadable_subrange_from(
        &self,
        fact: &Proposition,
        memory: &Memory,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        let Proposition::MemoryLoadable {
            memory: before,
            base: source,
            bytes: held,
            wide: true,
        } = fact
        else {
            return false;
        };
        if base.blocks_proven_distinct(source) {
            return false;
        }
        // The source is selected already. Align these two addresses through
        // the maintained graph instead of trying every spelling of the query.
        let aligned = self.loadable_query_at_source(base, source);
        let Some(delta) = self.shared_wide_element_index_of_access(&aligned, source, 1) else {
            return false;
        };
        self.decide(&wide_index_comparison(
            CompareRelation::LessEqual,
            delta.operand_view(),
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(i64::MAX as u64)),
        )) == Some(true)
            && self.decide(&wide_index_comparison(
                CompareRelation::LessEqual,
                delta.operand_view(),
                MachineOperandView::Legacy(held),
            )) == Some(true)
            && self.window_fits_after(delta.operand_view(), bytes, held)
            && before.read_region_identity(source) == memory.read_region_identity(source)
            && memory_range_still_available(before, memory, source, self)
    }

    /// Whether `bytes` from `delta` stay inside `held`, given `delta <= held`.
    /// A window `p[a..b]` can instead use its own bounds `a <= b <= held`
    /// when the direct subtraction comparison is not decided.
    fn window_fits_after(
        &self,
        delta: MachineOperandView<'_>,
        bytes: &MachineTerm,
        held: &MachineTerm,
    ) -> bool {
        let remaining = wide_index_binary(
            MachineBinaryOp::Subtract,
            MachineOperandView::Legacy(held),
            delta,
        );
        if self.decide(&wide_index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(bytes),
            remaining.operand_view(),
        )) == Some(true)
        {
            return true;
        }
        let MachineTerm::Binary {
            op: MachineBinaryOp::Subtract,
            format: MachineIntegerType::UInt64,
            left: end,
            right: start,
        } = bytes
        else {
            return false;
        };
        MachineOperandView::Legacy(start).retain(MachineIntegerType::UInt64)
            == delta.retain(MachineIntegerType::UInt64)
            && self.decide(&wide_index_comparison(
                CompareRelation::LessEqual,
                delta,
                MachineOperandView::Legacy(end),
            )) == Some(true)
            && self.decide(&ConditionTerm::uint64_less_equal(
                end.as_ref().clone(),
                held.clone(),
            )) == Some(true)
    }

    pub(crate) fn proves_memory_loadable(
        &self,
        memory: &Memory,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        // The loadable prover is the one consumer of the extended DAG
        // bridging: a loadability fact carrying one memory state must
        // discharge a load carrying another. Scoping the power here
        // keeps execution pruning and solve planning byte-identical to the
        // pre-arc path (see api.rs).
        let proved = crate::kernel::api::with_extended_dag_bridging(|| {
            self.proves_memory_loadable_inner(memory, base, bytes)
        });
        if proved {
            record_implicit_reasoning_provenance(
                self,
                &Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base: base.clone(),
                    bytes: bytes.clone(),
                    wide: false,
                },
            );
        }
        proved
    }

    fn proves_memory_loadable_inner(
        &self,
        memory: &Memory,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        // Exact evidence is an indexed lookup even when its address holds
        // many other views. Choosing a different premise belongs to search.
        crate::instrumentation::record_deterministic_work(1);
        if self.contains_assumed_exact(&Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: bytes.clone(),
            wide: false,
        }) {
            return true;
        }

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
        // Candidate lookup uses structural and canonical address keys. It
        // never restates the query at every alias to discover a source view.
        if self
            .memory_loadable_candidates_for_base(base)
            .any(|proposition| {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::MemoryLoadable {
                    memory: range_memory,
                    base: range_base,
                    bytes: range_bytes,
                    wide: false,
                } = proposition
                else {
                    return false;
                };

                memory_range_still_available(range_memory, memory, range_base, self)
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

        // One whole element of a wide range that is live: the access is at
        // an exact unsigned 64-bit index `i` from the fact's base, with
        // `i < n` where the fact counts `n` elements of this width, and
        // `n` within the object-size limit, which makes the index's byte
        // offset exact.
        if let Some(width) = bytes.as_const().filter(|width| *width > 0)
            && self.memory_loadable_candidates_for_base(base).any(|fact| {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::MemoryLoadable {
                    memory: range_memory,
                    base: range_base,
                    bytes: range_bytes,
                    wide: true,
                } = fact
                else {
                    return false;
                };
                let Some(elements) = crate::kernel::wide_loadable_element_count(range_bytes, width)
                else {
                    return false;
                };
                let Some(index) = self.shared_wide_element_index_of_access(base, range_base, width)
                else {
                    return false;
                };
                let limit = MachineTerm::uint64_constant(i64::MAX as u64 / u64::from(width));
                memory_range_still_available(range_memory, memory, range_base, self)
                    && self.decide(&wide_index_comparison(
                        CompareRelation::LessThan,
                        index.operand_view(),
                        MachineOperandView::Legacy(&elements),
                    )) == Some(true)
                    && self.decide(&ConditionTerm::uint64_less_equal(elements.clone(), limit))
                        == Some(true)
            })
        {
            return true;
        }

        if self.proves_memory_loadable_for_memory_resolution(memory, base, bytes) {
            return true;
        }

        let mut ranges = self
            .memory_loadable_candidates_for_base(base)
            .filter_map(|proposition| {
                let Proposition::MemoryLoadable {
                    memory: range_memory,
                    base: range_base,
                    bytes: range_bytes,
                    wide: false,
                } = proposition
                else {
                    return None;
                };
                memory_range_still_available(range_memory, memory, range_base, self).then(|| {
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
        memory: &Memory,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> Option<Vec<Proposition>> {
        let compatible = |fact_memory: &Memory, fact_base: &Pointer| {
            fact_memory == memory
                // Stores change cell contents, not whether the surrounding
                // stack blocks or heap allocations are live. Pointer terms
                // retain their source state, so a stored-to index field
                // cannot silently retarget the earlier region.
                || (fact_memory.blocks.get(&fact_base.block)
                    == memory.blocks.get(&fact_base.block)
                    && fact_memory.forgotten.ended_local_blocks == memory.forgotten.ended_local_blocks
                    && fact_memory.heap == memory.heap)
                || memory_range_still_available(fact_memory, memory, fact_base, self)
                || crate::kernel::api::memories_canonically_equal(fact_memory, memory)
                || crate::kernel::api::memories_connected_by_effects(fact_memory, memory, self)
        };
        let equal = |left: &MachineTerm, right: &MachineTerm| {
            let left = self.simplify_bitvector_under_assumptions(left);
            let right = self.simplify_bitvector_under_assumptions(right);
            left == right
                || self.decide(&ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                }) == Some(true)
                || crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                    &left, &right, self,
                )
        };
        let mut regions = self
            .memory_loadable_candidates_for_base(base)
            .filter_map(|fact| {
                let Proposition::MemoryLoadable {
                    memory: fact_memory,
                    base: fact_base,
                    bytes: fact_bytes,
                    wide: false,
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
                            || crate::kernel::api::memories_canonically_equal(fact_memory, memory),
                    )
                })
            })
            .collect::<Vec<_>>();
        // A materialized cell is selected at the requested address, never
        // by enumerating the memory's unrelated cells, runs or union fields.
        let cell_region = |pointer: &Pointer| {
            memory
                .cells
                .contiguous_bytes_at(pointer)
                .filter(|width| *width > 0)
                .map(|width| (None, pointer.clone(), MachineTerm::constant(width), true))
        };
        regions.extend(cell_region(base));
        let base = crate::kernel::api::canonicalize_pointer_loads(base);
        for (prefix_fact, prefix_base, prefix_bytes, prefix_current) in &regions {
            let prefix_starts_at_goal = prefix_base == &base
                || crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                    prefix_base,
                    &base,
                    self,
                )
                || shared_pointer_byte_offset_from_base(prefix_base, &base).is_some_and(|offset| {
                    self.byte_operands_equal(
                        offset.operand_view(),
                        MachineOperandView::Legacy(&MachineTerm::constant(0)),
                    )
                });
            if !prefix_starts_at_goal {
                continue;
            }
            // The prefix names its endpoint, so read suffix evidence at
            // that key instead of pairing it with every range in the block.
            let endpoint = prefix_bytes
                .as_const()
                .map(|width| base.offset_by_bytes(width))
                .or_else(|| {
                    int32_element_count_from_bytes(prefix_bytes)
                        .map(|count| base.offset_by_int32_elements(count))
                });
            let Some(endpoint) = endpoint else {
                continue;
            };
            let mut suffixes = self
                .memory_loadable_candidates_for_base(&endpoint)
                .filter_map(|fact| {
                    let Proposition::MemoryLoadable {
                        memory: before,
                        base: address,
                        bytes: extent,
                        wide: false,
                    } = fact
                    else {
                        return None;
                    };
                    compatible(before, address).then(|| {
                        (
                            Some(fact),
                            crate::kernel::api::canonicalize_pointer_loads(address),
                            extent.clone(),
                            before == memory
                                || crate::kernel::api::memories_canonically_equal(before, memory),
                        )
                    })
                })
                .collect::<Vec<_>>();
            suffixes.extend(cell_region(&endpoint));
            for (suffix_fact, suffix_base, suffix_bytes, suffix_current) in &suffixes {
                if prefix_fact.is_some() && prefix_fact == suffix_fact {
                    continue;
                }
                // Historical proposition facts cannot be concatenated with
                // each other to manufacture a fact at the current state.
                // The cross-state case is specifically an earlier prefix
                // extended by a cell materialized by the current store.
                if prefix_fact.is_some()
                    && suffix_fact.is_some()
                    && !(*prefix_current && *suffix_current)
                {
                    continue;
                }
                let byte_adjacent = if let Some(width) = prefix_bytes.as_const() {
                    // A concrete byte extent is an unsigned mathematical
                    // distance, not its signed 32-bit residue. Match the
                    // actual pointer, including extents above INT32_MAX.
                    let expected = base.offset_by_bytes(width);
                    suffix_base == &expected
                        || crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                            suffix_base,
                            &expected,
                            self,
                        )
                } else {
                    shared_pointer_byte_offset_from_base(suffix_base, &base).is_some_and(
                        |suffix_start| {
                            self.byte_operands_equal(
                                suffix_start.operand_view(),
                                MachineOperandView::Legacy(prefix_bytes),
                            )
                        },
                    )
                };
                let byte_concatenation = byte_adjacent
                    && equal(
                        bytes,
                        &MachineTerm::add((*prefix_bytes).clone(), (*suffix_bytes).clone()),
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
                                &MachineTerm::add(prefix_count, suffix_count),
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
        memory: &Memory,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        // Exact evidence is an indexed lookup even when its address holds
        // many other views. Choosing a different premise belongs to search.
        crate::instrumentation::record_deterministic_work(1);
        if self.contains_assumed_exact(&Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: bytes.clone(),
            wide: false,
        }) {
            return true;
        }

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
                let Proposition::MemoryLoadable {
                    memory: range_memory,
                    base: range_base,
                    bytes: range_bytes,
                    wide: false,
                } = proposition
                else {
                    return false;
                };
                if !memory_range_still_available(range_memory, memory, range_base, self) {
                    return false;
                }
                if self.same_base_and_loadable_extent_match(range_base, range_bytes, base, bytes) {
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
                    &MachineTerm::constant(0),
                    &element_count,
                    byte_width,
                    self,
                )
            })
    }

    fn nonwrapping_signed_byte_sum_end(
        &self,
        left: MachineOperandView<'_>,
        right: &MachineTerm,
    ) -> Option<SharedMachineIntegerTerm> {
        let left = self.simplify_machine_operand_under_assumptions(left, MachineIntegerType::Int32);
        let right = self.simplify_machine_operand_under_assumptions(
            MachineOperandView::Legacy(right),
            MachineIntegerType::Int32,
        );
        let sum = self.simplify_machine_operand_under_assumptions(
            index_binary(
                MachineBinaryOp::Add,
                left.operand_view(),
                right.operand_view(),
            )
            .operand_view(),
            MachineIntegerType::Int32,
        );
        signed_byte_sum_is_nonwrapping_views(
            left.operand_view(),
            right.operand_view(),
            sum.operand_view(),
            |lower, upper| {
                self.decide(&index_comparison(CompareRelation::LessEqual, lower, upper))
                    == Some(true)
            },
        )
        .then_some(sum)
    }

    /// Preserve same-block range expressions: their written endpoint guards
    /// refer to those terms, not to a reassociated affine difference. Equality
    /// can replace an exact selected address; otherwise only a different block
    /// needs the indexed coordinate projection.
    fn loadable_query_at_source(&self, query: &Pointer, source: &Pointer) -> Pointer {
        if self.pointers_known_equal(query, source) {
            source.clone()
        } else if query.block == source.block {
            query.clone()
        } else {
            self.equality_graph
                .pointer_at_base(query, source)
                .unwrap_or_else(|| query.clone())
        }
    }

    /// Callers establish that the source range is available in the relevant
    /// state before comparing its base and 32-bit byte extent.
    fn same_base_and_loadable_extent_match(
        &self,
        range_base: &Pointer,
        range_bytes: &MachineTerm,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        range_base == base
            && (structural_constant_byte_extent(range_bytes)
                .zip(structural_constant_byte_extent(bytes))
                .is_some_and(|(left, right)| left == right)
                || crate::kernel::reasoning::int32_values_proven_equal_for_memory_resolution(
                    range_bytes,
                    bytes,
                    self,
                ))
    }

    fn proves_loadable_region_from_structural_range(
        &self,
        range_base: &Pointer,
        range_bytes: &MachineTerm,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        if base.blocks_proven_distinct(range_base) {
            return false;
        }
        let aligned = self.loadable_query_at_source(base, range_base);
        let base = &aligned;

        if self.same_base_and_loadable_extent_match(range_base, range_bytes, base, bytes) {
            return true;
        }
        if let Some(byte_width) = bytes.as_const()
            // A 64-bit index keeps its own form in the pointer; against
            // this 32-bit count it is read as one where it is proved to fit.
            && let Some(index) = base
                .shared_element_index_from_base_with_width(range_base, byte_width)
                .or_else(|| {
                    crate::kernel::reasoning::shared_element_index_from_offset_with_facts(
                        &base.offset_from_base(range_base)?,
                        byte_width,
                        self,
                    )
                })
            && let Some(element_count) = element_count_from_bytes(range_bytes, byte_width)
            // Every branch below reads the assumed extent as `element_count`
            // elements and compares an index against it in signed arithmetic.
            // That reading is the fact's meaning only while the extent is a
            // valid byte extent; a wrapped one covers fewer bytes than its
            // count claims, and the cell would come from nothing.
            && self.assumed_extent_covers_its_element_count(&element_count, byte_width)
        {
            let lower = index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
                index.operand_view(),
            );
            let upper = index_comparison(
                CompareRelation::LessThan,
                index.operand_view(),
                MachineOperandView::Legacy(&element_count),
            );
            if self.selected_comparison_value(&lower) == Some(true)
                && self.selected_comparison_value(&upper) == Some(true)
            {
                return true;
            }
            if let Some(index_constant) =
                super::exact_signed_constant_view(index.operand_view(), self)
            {
                if let Some(element_count) = signed_bitvector_constant(&element_count) {
                    return 0 <= index_constant && index_constant < element_count;
                }
                if 0 <= index_constant
                    && self.has_exact_order_path_views(
                        index.operand_view(),
                        MachineOperandView::Legacy(&element_count),
                        true,
                    )
                {
                    return true;
                }
            }
            if let (
                Some((
                    MachineIntegerType::Int32,
                    MachineBinaryOp::Subtract,
                    [target_index, range_start],
                )),
                binary_term!(Int32, Subtract, range_end, count_start),
            ) = (index.operand_view().binary(), &element_count)
                && checked_scalar_facts::ScalarOperandKey::new(range_start)
                    == checked_scalar_facts::ScalarOperandKey::new(MachineOperandView::Legacy(
                        count_start,
                    ))
                && self.has_exact_order_path_views(range_start, target_index, false)
                && self.has_exact_order_path_views(
                    target_index,
                    MachineOperandView::Legacy(range_end),
                    true,
                )
            {
                return true;
            }
        }
        if self.proves_loadable_subrange_by_element_endpoints(range_base, range_bytes, base, bytes)
        {
            return true;
        }
        let Some(byte_offset) = shared_pointer_byte_offset_from_base(base, range_base) else {
            return false;
        };
        let Some(access_end) =
            self.nonwrapping_signed_byte_sum_end(byte_offset.operand_view(), bytes)
        else {
            return false;
        };
        self.decide(&index_comparison(
            CompareRelation::LessEqual,
            access_end.operand_view(),
            MachineOperandView::Legacy(&range_bytes),
        )) == Some(true)
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
    /// extent is a `MachineTerm`: `(b - a) * w` is modular, so reading the
    /// fact as "the elements `a..b`" is only legitimate while that product is
    /// the true count of bytes. The rule therefore requires the assumed fact's
    /// own byte-count guards —
    /// [`crate::kernel::memory_range_byte_count_extent`], the one definition
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
    /// The state side condition stays with the caller, which has already
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
        range_bytes: &MachineTerm,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        if range_base.block != base.block {
            return false;
        }
        // A range of one-byte elements lowers its extent unscaled — the byte
        // count of `p[a..b]` over `uint8` is `b - a` itself — so an extent
        // with no width factor is read at byte granularity. The argument
        // below holds at `w = 1` unchanged, and
        // `assumed_range_is_a_valid_byte_extent` already answers for it.
        let element_width = scaled_extent_element_width(bytes).unwrap_or(1);
        if scaled_extent_element_width(range_bytes).unwrap_or(1) != element_width {
            return false;
        }
        let (Some(goal_count), Some(range_count)) = (
            element_count_from_bytes(bytes, element_width),
            element_count_from_bytes(range_bytes, element_width),
        ) else {
            return false;
        };
        let Some(index) = base.shared_element_index_from_base_with_width(range_base, element_width)
        else {
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
        let offset_agrees = index
            == index_binary(
                MachineBinaryOp::Subtract,
                MachineOperandView::Legacy(goal_start),
                MachineOperandView::Legacy(range_start),
            );
        offset_agrees
            && self.proves_element_endpoint_order(range_start, goal_start)
            && self.proves_element_endpoint_order(goal_start, goal_end)
            && self.proves_element_endpoint_order(goal_end, range_end)
            && self.assumed_range_is_a_valid_byte_extent(range_start, range_end, element_width)
    }

    /// Whether the assumed range is established here to be a valid 32-bit byte
    /// extent — the side condition
    /// [`crate::kernel::memory_range_byte_count_extent`] states wherever a
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
        start: &MachineTerm,
        end: &MachineTerm,
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
                let element_count = MachineTerm::subtract(end.clone(), start.clone());
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
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::LessEqual,
                                left: lower,
                                right: upper,
                            },
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
        element_count: &MachineTerm,
        element_width: u32,
    ) -> bool {
        // When the count still names both endpoints, ask about those: the
        // guards a contract states for `p[a..b]` are written over `a` and `b`,
        // and asking in the same spelling finds them.
        if let binary_term!(Int32, Subtract, end, start) = element_count
            && self.assumed_range_is_a_valid_byte_extent(start, end, element_width)
        {
            return true;
        }
        self.assumed_range_is_a_valid_byte_extent(
            &MachineTerm::constant(0),
            element_count,
            element_width,
        )
    }

    /// An upper bound on the number of elements a range can really span, from
    /// the range's own established extent facts, or `None` when it has none.
    ///
    /// This is what an affine constant difference needs before it may be read
    /// as an order. [`crate::kernel::assumptions::affine_bitvector_difference_constant`]
    /// works in `i64` while the endpoints are modular `MachineTerm`s, so
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
        start: &MachineTerm,
        end: &MachineTerm,
        element_width: u32,
    ) -> Option<i64> {
        crate::instrumentation::record_deterministic_work(1);
        let count = MachineTerm::subtract(end.clone(), start.clone());
        let guards = crate::kernel::memory_range_element_count_guards(count, element_width);
        guards
            .iter()
            .all(|guard| match guard {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: lower,
                        right: upper,
                    },
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
        lower: &MachineTerm,
        upper: &MachineTerm,
    ) -> bool {
        self.proves_element_endpoint_order_views(
            MachineOperandView::Legacy(lower),
            MachineOperandView::Legacy(upper),
        )
    }

    pub(in crate::kernel) fn proves_element_endpoint_order_views(
        &self,
        lower: MachineOperandView<'_>,
        upper: MachineOperandView<'_>,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if let (Some(lower), Some(upper)) =
            (signed_index_constant(lower), signed_index_constant(upper))
        {
            return lower <= upper;
        }
        if checked_scalar_facts::ScalarOperandKey::new(lower)
            == checked_scalar_facts::ScalarOperandKey::new(upper)
        {
            return true;
        }
        let condition = index_comparison(CompareRelation::LessEqual, lower, upper);
        if self.selected_comparison_value(&condition) == Some(true)
            || self.has_exact_order_path_views(lower, upper, false)
        {
            return true;
        }
        // `c <= x - d` is `c + d <= x`, and the rewriting is exact when both
        // constants and their sum fit `int32`: `x - d` is then the number it
        // looks like, since `c + d <= x` puts it at or above `c`. This is the
        // shape a range carved one element short leaves — `p[0..n - 1]`, whose
        // own extent guard is `0 <= n - 1` while what the contract states is
        // `1 <= n` — and without it such a range has no established count.
        let Some((MachineIntegerType::Int32, MachineBinaryOp::Subtract, [base, decrement])) =
            upper.binary()
        else {
            return false;
        };
        let (Some(lower), Some(decrement)) = (
            signed_index_constant(lower),
            signed_index_constant(decrement),
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
        self.proves_element_endpoint_order_views(
            MachineOperandView::Legacy(&MachineTerm::constant(shifted as u32)),
            base,
        )
    }

    pub(in crate::kernel) fn proves_loadable_region_from_range(
        &self,
        range_base: &Pointer,
        range_bytes: &MachineTerm,
        base: &Pointer,
        bytes: &MachineTerm,
    ) -> bool {
        if self.same_base_and_loadable_extent_match(range_base, range_bytes, base, bytes) {
            return true;
        }

        if let Some(byte_width) = bytes.as_const()
            && self.proves_loadable_cell_from_region(range_base, range_bytes, base, byte_width)
        {
            return true;
        }

        if let Some(byte_offset) = shared_pointer_byte_offset_from_base(base, range_base) {
            let Some(access_end) =
                self.nonwrapping_signed_byte_sum_end(byte_offset.operand_view(), bytes)
            else {
                return false;
            };
            return self.decide(&index_comparison(
                CompareRelation::LessEqual,
                access_end.operand_view(),
                MachineOperandView::Legacy(&range_bytes),
            )) == Some(true);
        }

        false
    }

    pub(in crate::kernel) fn proves_access_from_memory_block(
        &self,
        memory: &Memory,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        // The region proof compares 32-bit extents.
        let Some(bytes) = memory
            .blocks
            .get(&pointer.block)
            .and_then(|block| block.extent().int32_bytes())
        else {
            return false;
        };
        let base = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        self.proves_loadable_cell_from_region(&base, bytes, pointer, byte_width)
    }

    /// Coverage through an element count whose byte extent has its validity
    /// guards. Unlike the general cell resolver, this does not compare a
    /// potentially wrapped byte-offset sum.
    pub(in crate::kernel) fn proves_loadable_cell_from_region_elements(
        &self,
        base: &Pointer,
        bytes: &MachineTerm,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        let Some(pointer) = crate::kernel::reasoning::pointer_in_block_for_memory_resolution(
            pointer,
            &base.block,
            self,
        ) else {
            return false;
        };
        let pointer = &pointer;
        if let Some(index) =
            self.pointer_element_index_from_base_with_width(pointer, base, byte_width)
            && let Some(element_count) = element_count_from_bytes(bytes, byte_width)
            && self.assumed_extent_covers_its_element_count(&element_count, byte_width)
        {
            let lower_condition = index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
                index.operand_view(),
            );
            let upper_condition = index_comparison(
                CompareRelation::LessThan,
                index.operand_view(),
                MachineOperandView::Legacy(&element_count),
            );
            let lower = self
                .selected_comparison_value(&lower_condition)
                .or_else(|| self.decide(&lower_condition));
            let upper = self
                .selected_comparison_value(&upper_condition)
                .or_else(|| self.decide(&upper_condition));
            if lower == Some(true) && upper == Some(true) {
                return true;
            }
        }

        self.proves_cell_within_strided_region(
            base,
            bytes,
            pointer,
            byte_width,
            &|left, right, strict| {
                let condition = index_comparison(
                    if strict {
                        CompareRelation::LessThan
                    } else {
                        CompareRelation::LessEqual
                    },
                    left,
                    right,
                );
                self.selected_comparison_value(&condition)
                    .or_else(|| self.decide(&condition))
                    == Some(true)
            },
        )
    }

    /// The element rule above for an access narrower than the element it
    /// lands in: a field of a struct-array element, or a cell of an array
    /// inside one.
    ///
    /// The address is `base + index * stride + rest`, with `stride` the
    /// widest scaled summand. It is in the region when `index` is an element
    /// of it, `0 <= index < bytes / stride`, which is the scalar question
    /// with the struct size as the element width, and the access at `rest`
    /// lies within the `stride` bytes of one element, which is this same
    /// question about a region of `stride` bytes. Every byte offset here is
    /// a mathematical sum, so the two bounds compose exactly:
    /// `index * stride + rest + width <= (count - 1) * stride + stride`.
    ///
    /// `holds` is the caller's own exact bound check for the two index
    /// conditions, so a region and a resource range ask them the way their
    /// scalar rules do.
    fn proves_cell_within_strided_region(
        &self,
        base: &Pointer,
        bytes: &MachineTerm,
        pointer: &Pointer,
        byte_width: u32,
        holds: &dyn Fn(MachineOperandView<'_>, MachineOperandView<'_>, bool) -> bool,
    ) -> bool {
        let Some(delta) = pointer.offset_from_base(base) else {
            return false;
        };
        let mut summands = Vec::new();
        let mut pending = vec![&delta];
        while let Some(term) = pending.pop() {
            match term {
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                other => summands.push(other),
            }
        }
        let scaled = |term: &PointerOffsetTerm| match term {
            PointerOffsetTerm::Int32Scaled { value, byte_width } => u32::try_from(*byte_width)
                .ok()
                .map(|stride| (value.clone(), stride)),
            _ => None,
        };
        let Some(stride) = summands
            .iter()
            .filter_map(|term| scaled(term).map(|(_, stride)| stride))
            .max()
        else {
            return false;
        };
        // An element as wide as the access is the scalar rule's case.
        if stride <= byte_width {
            return false;
        }
        let mut indices = summands.iter().enumerate().filter_map(|(position, term)| {
            scaled(term)
                .filter(|(_, width)| *width == stride)
                .map(|(index, _)| (position, index))
        });
        let (Some((position, index)), None) = (indices.next(), indices.next()) else {
            return false;
        };
        let Some(element_count) = element_count_from_bytes(bytes, stride) else {
            return false;
        };
        if !self.assumed_extent_covers_its_element_count(&element_count, stride) {
            return false;
        }
        if !holds(
            MachineOperandView::Legacy(&MachineTerm::constant(0)),
            index.operand_view(),
            false,
        ) || !holds(
            index.operand_view(),
            MachineOperandView::Legacy(&element_count),
            true,
        ) {
            return false;
        }
        let rest = summands
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != position)
            .map(|(_, term)| (*term).clone())
            .reduce(PointerOffsetTerm::add)
            .unwrap_or(PointerOffsetTerm::Constant(0));
        let element = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let within = Pointer {
            block: base.block.clone(),
            offset: rest,
        };
        self.proves_loadable_cell_from_region(
            &element,
            &MachineTerm::constant(stride),
            &within,
            byte_width,
        )
    }

    pub(in crate::kernel) fn proves_loadable_cell_from_region(
        &self,
        base: &Pointer,
        bytes: &MachineTerm,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        let Some(pointer) = crate::kernel::reasoning::pointer_in_block_for_memory_resolution(
            pointer,
            &base.block,
            self,
        ) else {
            return false;
        };
        let pointer = &pointer;

        if self.proves_loadable_cell_from_region_elements(base, bytes, pointer, byte_width) {
            return true;
        }

        if let Some(byte_offset) = shared_pointer_byte_offset_from_base(pointer, base) {
            let byte_width = MachineTerm::constant(byte_width);
            let Some(access_end) =
                self.nonwrapping_signed_byte_sum_end(byte_offset.operand_view(), &byte_width)
            else {
                return false;
            };
            return self.decide(&index_comparison(
                CompareRelation::LessEqual,
                access_end.operand_view(),
                MachineOperandView::Legacy(bytes),
            )) == Some(true);
        }

        false
    }

    /// Prepare ownership separation for a store of `bytes` at `write`.
    /// Explicit store owners supply singleton containing members once per
    /// written base. Crowded member buckets decline automatic preservation.
    /// Without them, retain the write's base spellings until
    /// [`Self::access_owned_apart_from_store`] can select stated compositions
    /// through the member index under both the write and the cached read.
    ///
    /// Members are found through each composition's base index under the
    /// additive base spellings of `write` (see [`additive_base_spellings`]),
    /// never by walking a block bucket: every object a parameter reaches
    /// shares the one `ExternalArgument` block, so a bucket walk would visit
    /// every owned object in the function for each cell.
    pub(in crate::kernel) fn owned_store_footprint(
        &self,
        write: &Pointer,
        bytes: u32,
    ) -> OwnedStoreFootprint<'_> {
        if self.resource_compositions.is_empty() {
            return OwnedStoreFootprint::Members(Vec::new());
        }
        let spellings = self.written_base_spellings(write);
        match self.store_owners() {
            Some(owners) => OwnedStoreFootprint::Members(self.store_members_in(
                owners.iter(),
                &spellings,
                bytes,
            )),
            // Select the root and singleton historical buckets only once the
            // read's written bases are known too. Ambiguous buckets decline.
            None => OwnedStoreFootprint::Indexed {
                spellings,
                bytes,
                members: Default::default(),
            },
        }
    }

    fn store_members_in<'a>(
        &self,
        compositions: impl IntoIterator<Item = &'a ResourceContext>,
        spellings: &[(Pointer, Pointer)],
        bytes: u32,
    ) -> OwnedStoreMembers<'a> {
        let mut members = Vec::new();
        // A range restated by multiple candidate compositions needs only
        // one containment decision.
        let mut decided = BTreeMap::<&MemoryRange, bool>::new();
        for resources in compositions {
            crate::instrumentation::record_deterministic_work(1);
            for (base, access) in spellings {
                if let Some((entry, range)) = resources.unique_owned_memory_member_with_base(base) {
                    let contains = *decided
                        .entry(range)
                        .or_insert_with(|| self.access_within_memory_range(access, bytes, range));
                    if contains {
                        members.push((resources, entry, range));
                    }
                }
            }
        }
        members
    }

    /// Only bases written in the access itself. Derive separation under a
    /// different spelling explicitly and transport the needed read across the
    /// store; automatic ownership lookup never enumerates pointer aliases.
    fn written_base_spellings(&self, pointer: &Pointer) -> Vec<(Pointer, Pointer)> {
        additive_base_spellings(pointer)
            .into_iter()
            .map(|base| {
                crate::instrumentation::record_deterministic_work(1);
                (base, pointer.clone())
            })
            .collect()
    }

    /// A flat parameter partition without path equalities. Non-atomic bases
    /// and accesses needing facts stay on the ordinary store ladder.
    pub(in crate::kernel) fn parameter_store_partition(
        &self,
        write: &Pointer,
        bytes: u32,
    ) -> Option<(&ResourceContext, Pointer)> {
        if self
            .equality_graph
            .offset_has_source_dependencies(&write.offset)
        {
            return None;
        }
        let members = match self.owned_store_footprint(write, bytes) {
            OwnedStoreFootprint::Members(members) => members,
            OwnedStoreFootprint::Indexed {
                spellings, bytes, ..
            } => {
                // This optimization needs any composition holding the write,
                // not all compositions that could separate a pair. The first
                // admission of its member is listed under the write or is
                // the index's root.
                let candidates = self
                    .composition_members
                    .directly_listed_under_bases(spellings.iter().map(|(base, _)| base));
                self.store_members_in(candidates, &spellings, bytes)
            }
        };
        members.into_iter().find_map(|(resources, _, range)| {
            parameter_partition_root(range.base()).map(|base| (resources, base))
        })
    }

    /// Cross-block equalities are filed under their exact endpoints, so a
    /// parameter follows only its own aliases rather than the shared external
    /// block's entire class. Same-block and scalar alias premises fall back.
    pub(in crate::kernel) fn parameter_store_alias_bases(
        &self,
        base: &Pointer,
    ) -> Option<BTreeSet<Pointer>> {
        self.equality_graph.parameter_store_alias_bases(base)
    }

    /// The objects whose addresses known 64-bit equalities connect with the
    /// address of the object `pointer` points into. A C pointer comparison
    /// states such an equality and not a pointer equality, and memory is
    /// addressed, so a store through `pointer` may write the bytes of any
    /// object returned here: separation keeps none of their cached cells.
    /// Computed once per store; the walk follows only the equalities filed
    /// under the objects it reaches.
    pub(in crate::kernel) fn address_connected_objects(
        &self,
        pointer: &Pointer,
    ) -> BTreeSet<Pointer> {
        self.equality_graph.address_connected_objects(pointer)
    }

    pub(in crate::kernel) fn parameter_partition_cell_base(
        &self,
        resources: &ResourceContext,
        pointer: &Pointer,
        bytes: u32,
    ) -> Option<Pointer> {
        additive_base_spellings(pointer)
            .iter()
            .find_map(|written_base| {
                let (_, range) = resources.unique_owned_memory_member_with_base(written_base)?;
                if !self.access_within_memory_range(pointer, bytes, range) {
                    return None;
                }
                let base = parameter_partition_root(range.base())?;
                (parameter_partition_root(pointer)? == base).then_some(base)
            })
    }

    /// Whether ownership alone keeps an access of `bytes` at `pointer` off a
    /// store's written bytes: some composition owns the write through one
    /// member and every byte of this access through a different one.
    ///
    /// This is the partition law of a valid composition, the one
    /// [`crate::kernel::memory_provenance::owned_composition_store_separated_evidence`]
    /// and [`Self::composition_separated_members`] already apply; only the
    /// route to the two members differs. Both memberships
    /// are full, assumption-checked containments of the whole access, not
    /// of its first element, and the same guards apply: the two addresses
    /// must not be proven equal, and ranges whose distinct base spellings
    /// were later proven equal must not overlap. Lookup is by base, so the
    /// question checks only singleton member buckets under the written bases.
    /// Without explicit owners it also checks the root and singleton historical
    /// composition buckets. Crowded buckets need explicit frame reasoning.
    pub(in crate::kernel) fn access_owned_apart_from_store<'a>(
        &'a self,
        footprint: &OwnedStoreFootprint<'a>,
        write: &Pointer,
        pointer: &Pointer,
        bytes: u32,
    ) -> bool {
        if matches!(footprint, OwnedStoreFootprint::Members(members) if members.is_empty()) {
            return false;
        }
        let spellings = self.written_base_spellings(pointer);
        let selected;
        let members = match footprint {
            OwnedStoreFootprint::Members(members) => members,
            OwnedStoreFootprint::Indexed {
                spellings: write_spellings,
                bytes: write_bytes,
                members,
            } => {
                let candidates = self.composition_members.directly_listed_under_bases(
                    write_spellings
                        .iter()
                        .chain(&spellings)
                        .map(|(base, _)| base),
                );
                // One immutable context and write own this footprint. A
                // composition selected by several cached reads needs its
                // write-containment result only once, including a miss.
                let mut cached = members.borrow_mut();
                selected = candidates
                    .into_iter()
                    .flat_map(|resources| {
                        crate::instrumentation::record_deterministic_work(1);
                        let identity = std::sync::Arc::as_ptr(&resources.storage) as usize;
                        cached
                            .entry(identity)
                            .or_insert_with(|| {
                                self.store_members_in(
                                    std::iter::once(resources),
                                    write_spellings,
                                    *write_bytes,
                                )
                            })
                            .clone()
                    })
                    .collect::<Vec<_>>();
                &selected
            }
        };
        let separated = members
            .iter()
            .find(|(resources, write_entry, write_range)| {
                spellings.iter().any(|(base, access)| {
                    resources
                        .unique_owned_memory_member_with_base(base)
                        .is_some_and(|(entry, range)| {
                            entry != *write_entry
                                && self.access_within_memory_range(access, bytes, range)
                                && !self
                                    .memory_ranges_overlap_after_base_equality(write_range, range)
                        })
                })
            });
        let Some((resources, _, _)) = separated else {
            return false;
        };
        if self.pointers_proven_equal_ignoring_memory_separation(pointer, write) {
            return false;
        }
        record_implicit_reasoning_provenance(
            self,
            &Proposition::ResourceComposition((*resources).clone()),
        );
        true
    }

    /// Whether one owned memory member of `resources` holds every byte of an
    /// access of `bytes` at `pointer`, found through the composition's base
    /// index under the access's additive base spellings, as
    /// [`Self::owned_store_footprint`] finds a store's member.
    pub(in crate::kernel) fn access_held_by_owned_member(
        &self,
        resources: &ResourceContext,
        pointer: &Pointer,
        bytes: u32,
    ) -> bool {
        self.owned_member_holding_access(resources, pointer, bytes)
            .is_some()
    }

    /// The owned memory member of `resources` that holds every byte of an
    /// access of `bytes` at `pointer`, as [`Self::access_held_by_owned_member`]
    /// finds it.
    pub(in crate::kernel) fn owned_member_holding_access<'a>(
        &self,
        resources: &'a ResourceContext,
        pointer: &Pointer,
        bytes: u32,
    ) -> Option<&'a MemoryRange> {
        additive_base_spellings(pointer).iter().find_map(|base| {
            resources
                .owned_memory_members_with_base(base)
                .find(|(_, range)| self.access_within_memory_range(pointer, bytes, range))
                .map(|(_, range)| range)
        })
    }

    /// A flat caller owner or surviving view selected by the access's own
    /// base spellings, without resolving ambient aliases or memory history.
    pub(in crate::kernel) fn readable_member_holding_access<'a>(
        &self,
        resources: &'a ResourceContext,
        pointer: &Pointer,
        bytes: u32,
    ) -> Option<&'a MemoryRange> {
        additive_base_spellings(pointer).iter().find_map(|base| {
            resources
                .memory_members_with_base(base, true)
                .find(|(_, range)| self.access_within_memory_range(pointer, bytes, range))
                .map(|(_, range)| range)
        })
    }

    /// The range of `ranges` -- memory a caller kept owning across a call --
    /// that holds every byte of an access of `bytes` at `pointer`.
    ///
    /// The prepared address index selects a member first. Raw contexts use
    /// singleton base buckets under the access's structural and indexed
    /// coordinates. Only a selected candidate builds the placement context;
    /// unrelated aliases and block members never trigger placement.
    pub(in crate::kernel) fn kept_range_holding_access<'a>(
        &self,
        ranges: &'a ResourceContext,
        placement: impl FnOnce() -> Option<PureFactContext>,
        pointer: &Pointer,
        bytes: u32,
    ) -> Option<&'a MemoryRange> {
        self.kept_memory_range_holding_access(ranges, placement, pointer, bytes, false)
    }

    /// A surviving caller view preserves values without supplying write access.
    pub(in crate::kernel) fn kept_read_range_holding_access<'a>(
        &self,
        ranges: &'a ResourceContext,
        placement: impl FnOnce() -> Option<PureFactContext>,
        pointer: &Pointer,
        bytes: u32,
    ) -> Option<&'a MemoryRange> {
        self.kept_memory_range_holding_access(ranges, placement, pointer, bytes, true)
    }

    fn kept_memory_range_holding_access<'a>(
        &self,
        ranges: &'a ResourceContext,
        placement: impl FnOnce() -> Option<PureFactContext>,
        pointer: &Pointer,
        bytes: u32,
        include_views: bool,
    ) -> Option<&'a MemoryRange> {
        // Folded resources supply no flat memory to this lookup. Avoid
        // resolving a read's history just to query that empty index;
        // composite ownership is queried separately by the caller.
        let empty = if include_views {
            ranges.memory_input_facts().is_empty()
        } else {
            ranges.flat_owned_memory_ranges().is_empty()
        };
        if empty {
            return None;
        }
        // Checked pointer classes select readable memory for ordinary accesses.
        // A kept call frame must use that same selection: one-hop aliases
        // and a block-local fallback miss transitive model-pointer aliases
        // crossing symbolic blocks. Coverage remains the selected access's
        // whole byte extent. A kept view preserves values without granting writes.
        if let Some(range) =
            ranges.kept_range_via_address_class(pointer, bytes, self, include_views)
        {
            return Some(range);
        }
        let mut candidates = Vec::new();
        for base in additive_base_spellings(pointer) {
            crate::instrumentation::record_deterministic_work(1);
            let mut anchors = vec![base.clone()];
            // An opaque read is not an invitation to resolve memory history
            // just to look for a supplier. Its explicit keys still work.
            let opaque = matches!(&base.block, PointerBlock::LoadedPointer(_))
                || matches!(&base.block, PointerBlock::Symbolic(variable)
                    if crate::kernel::is_load_variable(variable));
            if !opaque {
                anchors.push(self.equality_graph.storage_address(&base));
                if let Some(coordinate) = self.equality_graph.canonical_pointer(&base)
                    && let Some(offset) = coordinate.offset.to_offset_term()
                {
                    anchors.push(Pointer {
                        block: coordinate.representative,
                        offset,
                    });
                }
            }
            if let Some(alias) = self.equality_graph.unique_exact_pointer_alias(&base) {
                anchors.push(alias.clone());
            }
            for anchor in anchors {
                if let Some(range) = ranges.unique_memory_member_with_base(&anchor, include_views) {
                    candidates.push(range);
                }
            }
        }
        if candidates.is_empty() {
            return None;
        }
        let placed = placement();
        let context = placed.as_ref().unwrap_or(self);
        candidates
            .into_iter()
            .find(|range| context.kept_range_holds_access(range, pointer, bytes))
    }

    /// Whether every byte of an access of `bytes` at `pointer` lies in the
    /// kept `range`, decided in this context: the placement step of
    /// [`Self::kept_range_holding_access`].
    pub(in crate::kernel) fn kept_range_holds_access(
        &self,
        range: &MemoryRange,
        pointer: &Pointer,
        bytes: u32,
    ) -> bool {
        let width = range.element_width();
        if width == 0 {
            return false;
        }
        if self.access_within_memory_range(pointer, bytes, range)
            || crate::kernel::resource_tracker::cell_source::AccessInRangeEvidence::for_access(
                pointer, bytes, range, self,
            )
            .is_some()
        {
            return true;
        }
        if range.wide_bounds().is_some() {
            return false;
        }
        let contains = |pointer: &Pointer| {
            self.pointer_in_range_with_width(
                pointer,
                range.base(),
                range.start(),
                range.end(),
                width,
            )
        };
        let elements = bytes.max(1).div_ceil(width);
        if contains(pointer)
            && (elements == 1
                || contains(
                    &pointer.offset_by_elements(MachineTerm::constant(elements - 1), width),
                ))
        {
            return true;
        }
        // A field of a struct-array element inside a range that starts at its
        // base: the range is `end * width` bytes there, and the strided rule
        // asks the element and field questions with this rule's bound check.
        range.constant_start() == Some(0)
            && self.proves_cell_within_strided_region(
                range.base(),
                &MachineTerm::multiply(range.end().clone(), MachineTerm::constant(width)),
                pointer,
                bytes,
                &|left, right, strict| {
                    self.proves_range_bound(index_comparison(
                        if strict {
                            CompareRelation::LessThan
                        } else {
                            CompareRelation::LessEqual
                        },
                        left,
                        right,
                    ))
                },
            )
    }

    /// Whether every byte of an access of `bytes` at `pointer` lies in
    /// `range`: its first element and, for an access wider than one element,
    /// its last. Element membership places `pointer` exactly on an element
    /// boundary, so the elements in between are in the range as well.
    ///
    /// Membership is read structurally: `pointer` must be the range's base
    /// itself or that base plus one displacement, the direct route of
    /// [`Self::pointer_in_range_with_width`], and only the two endpoint
    /// bounds are then proved. The other routes there compare offsets that
    /// are *not* syntactically related, and on a miss that comparison is a
    /// failing distinctness search, which is exactly the cost this rung
    /// exists to avoid; a pointer spelled some other way leaves the
    /// decision to the caller's full ladder.
    fn access_within_memory_range(
        &self,
        pointer: &Pointer,
        bytes: u32,
        range: &MemoryRange,
    ) -> bool {
        if range.wide_bounds().is_some() {
            return self.pointer_access_in_wide_range(pointer, bytes, range);
        }
        let width = range.element_width();
        if width == 0 {
            return false;
        }
        let contains = |pointer: &Pointer| {
            structural_element_index(pointer, range.base(), width, self).is_some_and(|index| {
                self.proves_range_bound(index_comparison(
                    CompareRelation::LessEqual,
                    MachineOperandView::Legacy(&range.start()),
                    index.operand_view(),
                )) && self.proves_range_bound(index_comparison(
                    CompareRelation::LessThan,
                    index.operand_view(),
                    MachineOperandView::Legacy(&range.end()),
                ))
            })
        };
        let elements = bytes.max(1).div_ceil(width);
        contains(pointer)
            && (elements == 1
                || contains(
                    &pointer.offset_by_elements(MachineTerm::constant(elements - 1), width),
                ))
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_shallow_explicit_range(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        if self.pointers_proven_equal_ignoring_memory_separation(left, right) {
            return false;
        }
        let contains = |pointer: &Pointer, range: &MemoryRange| {
            // A wide range has its one membership rule.
            if range.wide_bounds().is_some() {
                return self.pointer_access_in_wide_range(pointer, range.element_width(), range);
            }
            self.pointer_in_range_by_shallow_fact_graph_with_width(
                pointer,
                range.base(),
                range.start(),
                range.end(),
                range.element_width(),
            )
        };
        self.memory_separation_candidates(&left.block, &right.block)
            .any(|(proposition, left_range, right_range)| {
                let proved = contains(left, left_range) && contains(right, right_range)
                    || contains(right, left_range) && contains(left, right_range);
                let proved = proved
                    && !self.memory_ranges_overlap_after_base_equality(left_range, right_range);
                if proved {
                    record_implicit_reasoning_provenance(self, proposition);
                }
                proved
            })
            || self
                .composition_separated_members(
                    left,
                    right,
                    |range| contains(left, range),
                    |range| contains(right, range),
                    |left_range, right_range| {
                        !self.memory_ranges_overlap_after_base_equality(left_range, right_range)
                    },
                )
                .inspect(|(resources, _, _)| {
                    record_implicit_reasoning_provenance(
                        self,
                        &Proposition::ResourceComposition((*resources).clone()),
                    );
                })
                .is_some()
            // Two owned members, one in each pointer's block: a composition
            // holding both is listed under both blocks
            // (`CompositionMemberIndex`).
            || self
                .composition_members
                .listed_under([], [&left.block, &right.block])
                .into_iter()
                .any(|resources| resources.proves_owned_pointers_separate_shallow(left, right))
    }

    pub(in crate::kernel) fn pointer_in_range_by_shallow_fact_graph_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &MachineTerm,
        end: &MachineTerm,
        element_width: u32,
    ) -> bool {
        if pointer_in_range_shallow(pointer, base, start, end, element_width, Some(self)) {
            return true;
        }
        let Some(pointer) = self.pointer_in_block(pointer, &base.block) else {
            return false;
        };
        let pointer = &pointer;
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
            && self.selected_comparison_value(&index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(start),
                index.operand_view(),
            )) == Some(true)
            && self.selected_comparison_value(&index_comparison(
                CompareRelation::LessThan,
                index.operand_view(),
                MachineOperandView::Legacy(end),
            )) == Some(true)
        {
            return true;
        }
        let Some(count) = affine_range_element_count(start, end) else {
            return false;
        };
        exact_affine_index_difference_views(
            delta.index.operand_view(),
            MachineOperandView::Legacy(start),
            Some(self),
        )
        .and_then(|difference| difference.checked_add(delta.constant))
        .is_some_and(|offset| 0 <= offset && offset < count)
    }

    /// One indexed explicit-fact step beyond structural containment. This is
    /// intentionally narrower than the general shallow fact-graph helper:
    /// it accepts only an exact base-offset alias and the two exact range
    /// bounds, so a named separation candidate does not need recursive
    /// memory resolution merely because its member index is symbolic.
    fn pointer_in_range_by_exact_facts(&self, pointer: &Pointer, range: &MemoryRange) -> bool {
        if pointer_in_memory_range_shallow_with_facts(pointer, range, self) {
            return true;
        }
        // The shallow check above is a wide range's whole membership rule.
        if range.wide_bounds().is_some() {
            return false;
        }
        let Some(pointer) = self.pointer_in_block(pointer, &range.base().block) else {
            return false;
        };
        let pointer = &pointer;
        let offset_matches = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            pointer_offsets_match_by_shallow_fact_graph(left, right, self)
        };
        let index = pointer
            .shared_element_index_from_base_with_width(range.base(), range.element_width())
            .or_else(|| match &pointer.offset {
                PointerOffsetTerm::Add(left, right)
                    if offset_matches(left, &range.base().offset) =>
                {
                    shared_element_index_from_offset(right, range.element_width())
                }
                PointerOffsetTerm::Add(left, right)
                    if offset_matches(right, &range.base().offset) =>
                {
                    shared_element_index_from_offset(left, range.element_width())
                }
                _ if offset_matches(&pointer.offset, &range.base().offset) => Some(
                    MachineOperandView::Legacy(&MachineTerm::constant(0))
                        .retain(MachineIntegerType::Int32),
                ),
                _ => None,
            });
        let Some(index) = index else {
            return false;
        };
        self.selected_comparison_value(&index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&range.start()),
            index.operand_view(),
        )) == Some(true)
            && self.selected_comparison_value(&index_comparison(
                CompareRelation::LessThan,
                index.operand_view(),
                MachineOperandView::Legacy(&range.end()),
            )) == Some(true)
    }

    pub(in crate::kernel) fn pointers_proven_disjoint_by_explicit_range_for_memory_resolution(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        if self.pointers_proven_equal_ignoring_memory_separation(left, right) {
            return false;
        }
        let Some(_query) = crate::kernel::reasoning::ResolutionQueryGuard::enter(
            crate::kernel::reasoning::ResolutionQuery::RangeDisjoint(left.clone(), right.clone()),
        ) else {
            return false;
        };
        // Most execution-time separation certificates name the exact ranges
        // being accessed. Resolve those structurally before asking the
        // state-aware containment prover, which may itself inspect memory
        // loads and is deliberately the more expensive second phase.
        let mut candidates = self.memory_separation_candidates(&left.block, &right.block);
        let record_candidate = |proposition: &Proposition| {
            record_implicit_reasoning_provenance(self, proposition);
        };
        // The same law asked of each held composition, with a phase's own
        // membership relation: two owned members, one holding each pointer.
        let composition_candidate = |contains: &dyn Fn(&Pointer, &MemoryRange) -> bool| {
            let found = self.composition_separated_members(
                left,
                right,
                |range| {
                    #[cfg(test)]
                    MEMORY_SEPARATION_CANDIDATE_CHECKS.with(|checks| checks.set(checks.get() + 1));
                    contains(left, range)
                },
                |range| contains(right, range),
                |left_range, right_range| {
                    !self.memory_ranges_overlap_after_base_equality(left_range, right_range)
                },
            );
            if let Some((resources, _, _)) = found {
                record_implicit_reasoning_provenance(
                    self,
                    &Proposition::ResourceComposition(resources.clone()),
                );
            }
            found.is_some()
        };
        if crate::instrumentation::measure_operation(
            "kernel",
            "explicit range arms",
            "explicit range: shallow candidates",
            || {
                candidates
                    .clone()
                    .any(|(proposition, left_range, right_range)| {
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
                        let proved = proved
                            && !self
                                .memory_ranges_overlap_after_base_equality(left_range, right_range);
                        if proved {
                            record_candidate(proposition);
                        }
                        proved
                    })
                    || composition_candidate(&|pointer, range| {
                        pointer_in_memory_range_shallow_with_facts(pointer, range, self)
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
                    .any(|(proposition, left_range, right_range)| {
                        #[cfg(test)]
                        MEMORY_SEPARATION_CANDIDATE_CHECKS
                            .with(|checks| checks.set(checks.get() + 1));
                        let proved = self.pointer_in_range_by_exact_facts(left, left_range)
                            && self.pointer_in_range_by_exact_facts(right, right_range)
                            || self.pointer_in_range_by_exact_facts(right, left_range)
                                && self.pointer_in_range_by_exact_facts(left, right_range);
                        let proved = proved
                            && !self
                                .memory_ranges_overlap_after_base_equality(left_range, right_range);
                        if proved {
                            record_candidate(proposition);
                        }
                        proved
                    })
                    || composition_candidate(&|pointer, range| {
                        self.pointer_in_range_by_exact_facts(pointer, range)
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
                self.composition_members
                    .listed_under([], [&left.block, &right.block])
                    .into_iter()
                    .any(|resources| {
                        let proved = resources.proves_owned_pointers_separate_shallow(left, right);
                        if proved {
                            record_implicit_reasoning_provenance(
                                self,
                                &Proposition::ResourceComposition(resources.clone()),
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
                // The members `proves_owned_pointers_separate_by` finds are in
                // the two pointers' blocks, the keys a composition holding
                // both is listed under (`CompositionMemberIndex`).
                self.composition_members
                    .listed_under([], [&left.block, &right.block])
                    .into_iter()
                    .any(|resources| {
                        let proved = resources.proves_owned_pointers_separate_by(
                            left,
                            right,
                            |pointer, range| {
                                if range.wide_bounds().is_some() {
                                    self.pointer_access_in_wide_range(
                                        pointer,
                                        range.element_width(),
                                        range,
                                    )
                                } else {
                                    self.pointer_in_range_by_shallow_fact_graph_with_width(
                                        pointer,
                                        range.base(),
                                        range.start(),
                                        range.end(),
                                        range.element_width(),
                                    )
                                }
                            },
                        );
                        if proved {
                            record_implicit_reasoning_provenance(
                                self,
                                &Proposition::ResourceComposition(resources.clone()),
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
                candidates.any(|(proposition, left_range, right_range)| {
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
                    let proved = proved
                        && !self.memory_ranges_overlap_after_base_equality(left_range, right_range);
                    if proved {
                        record_candidate(proposition);
                    }
                    proved
                }) || composition_candidate(&|pointer, range| {
                    pointer_in_memory_range_for_memory_resolution(pointer, range, self)
                })
            },
        )
    }

    pub(in crate::kernel) fn memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
        &self,
        left: &MemoryRange,
        right: &MemoryRange,
    ) -> bool {
        if left.base().blocks_proven_distinct(right.base()) {
            return true;
        }
        // Exact byte overlap cannot be undone by a separation certificate.
        // Coverage and call transfer frequently ask this of a held range and
        // its own subrange; do not search unrelated authority for that pair.
        if crate::kernel::primitives::constant_memory_overlap(left, right) == Some(true) {
            return false;
        }
        if self.memory_ranges_overlap_after_base_equality(left, right) {
            return false;
        }
        let Some(_query) = crate::kernel::reasoning::ResolutionQueryGuard::enter(
            crate::kernel::reasoning::ResolutionQuery::RangesSeparate(left.clone(), right.clone()),
        ) else {
            return false;
        };
        if self
            .borrow_partition_separated_members(
                left.base(),
                right.base(),
                |range| memory_range_contained_for_memory_resolution(left, range, self),
                |range| memory_range_contained_for_memory_resolution(right, range, self),
            )
            .is_some()
        {
            return true;
        }
        // Separate sides need not have the same logical element width.
        // Each query is contained in its own certificate side below.
        // Two owned members in the ranges' blocks: listed under both
        // (`CompositionMemberIndex`).
        if self
            .composition_members
            .listed_under([], [&left.base().block, &right.base().block])
            .into_iter()
            .any(|resources| resources.proves_owned_memory_ranges_separate_shallow(left, right))
        {
            return true;
        }
        // Prefer certificates where one queried range is structurally inside
        // one side. This gives the other side a single, directed equivalence
        // check instead of exploring both orientations of every separation
        // fact before reaching the structurally relevant certificate.
        let directed = |proposition: &Proposition| {
            let Some((fact_left, fact_right)) = proposition.memory_separation() else {
                return false;
            };
            (memory_range_shallowly_contained_with_facts(left, fact_left, self)
                && memory_range_contained_for_memory_resolution(right, fact_right, self)
                || memory_range_shallowly_contained_with_facts(right, fact_right, self)
                    && memory_range_contained_for_memory_resolution(left, fact_left, self)
                || memory_range_shallowly_contained_with_facts(right, fact_left, self)
                    && memory_range_contained_for_memory_resolution(left, fact_right, self)
                || memory_range_shallowly_contained_with_facts(left, fact_right, self)
                    && memory_range_contained_for_memory_resolution(right, fact_left, self))
                && !self.memory_ranges_overlap_after_base_equality(fact_left, fact_right)
        };
        // Each certificate shape has one shallow side, which a narrow query
        // range meets only in its own block.
        if if left.wide_bounds().is_none() && right.wide_bounds().is_none() {
            self.memory_separations_near(
                [&left.base().block, &right.base().block],
                [left.base(), right.base()],
            )
            .into_iter()
            .any(directed)
        } else {
            self.separation_facts_related_to(left, right, directed)
        } {
            return true;
        }
        // Both sides by memory resolution, which can cross blocks through
        // any proven base equality.
        self.separation_facts_related_to(left, right, |proposition| {
            let Some((fact_left, fact_right)) = proposition.memory_separation() else {
                return false;
            };
            (memory_range_contained_for_memory_resolution(left, fact_left, self)
                && memory_range_contained_for_memory_resolution(right, fact_right, self)
                || memory_range_contained_for_memory_resolution(right, fact_left, self)
                    && memory_range_contained_for_memory_resolution(left, fact_right, self))
                && !self.memory_ranges_overlap_after_base_equality(fact_left, fact_right)
        }) || self.composition_separates_owned_ranges(left, right)
    }

    /// Whether `certifies` holds of a stated memory separation that can
    /// contain `left` and `right`. A side contains a queried range only up
    /// to memory resolution, which reaches a block through a proven base
    /// equality, so the candidates are the separations filed under the
    /// blocks related to either queried base, including wide sides
    /// (`memory_separations_near`). Debug builds compare every answer with
    /// the scan of every separation.
    fn separation_facts_related_to(
        &self,
        left: &MemoryRange,
        right: &MemoryRange,
        certifies: impl Fn(&Proposition) -> bool,
    ) -> bool {
        let blocks = [left.base(), right.base()]
            .into_iter()
            .flat_map(|base| crate::kernel::primitives::related_pointer_root_blocks(base, self))
            .collect::<BTreeSet<_>>();
        let indexed = self
            .memory_separations_near(blocks.iter(), [left.base(), right.base()])
            .into_iter()
            .any(&certifies);
        #[cfg(debug_assertions)]
        if !crate::instrumentation::in_uncharged_debug_check() {
            crate::instrumentation::uncharged_debug_check(|| {
                let scanned = self.separation_facts.scan_for_upkeep().any(&certifies);
                assert_eq!(
                    indexed, scanned,
                    "the related blocks' separations differ from every separation"
                );
            });
        }
        indexed
    }

    /// Two ranges are separate as distinct owned members of one held
    /// composition, each found among the members under its related roots
    /// (`proves_owned_memory_ranges_separate_by`). Those members are in the
    /// roots' blocks, and owned members of a valid composition are disjoint,
    /// so a composition holding the two finds them; the compositions listed
    /// under those blocks reach one (`CompositionMemberIndex`). Debug builds
    /// compare every answer with the scan.
    fn composition_separates_owned_ranges(&self, left: &MemoryRange, right: &MemoryRange) -> bool {
        let separates = |resources: &ResourceContext| {
            resources.proves_owned_memory_ranges_separate_by(left, right, self, |child, parent| {
                memory_range_contained_for_memory_resolution(child, parent, self)
            })
        };
        let blocks = [left.base(), right.base()]
            .into_iter()
            .flat_map(|base| crate::kernel::primitives::related_pointer_root_blocks(base, self))
            .collect::<BTreeSet<_>>();
        let indexed = self
            .composition_members
            .listed_under([], blocks.iter())
            .into_iter()
            .any(separates);
        #[cfg(debug_assertions)]
        if !crate::instrumentation::in_uncharged_debug_check() {
            crate::instrumentation::uncharged_debug_check(|| {
                let scanned = self.resource_compositions.scan_for_upkeep().any(separates);
                assert_eq!(
                    indexed, scanned,
                    "the listed compositions' owned separation differs from every composition's"
                );
            });
        }
        indexed
    }

    fn pointer_element_index_from_base_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        byte_width: u32,
    ) -> Option<SharedMachineIntegerTerm> {
        let pointer = &self.pointer_in_block(pointer, &base.block)?;
        // Exact syntax and direct offset arithmetic are authoritative on
        // their own. Resolve them before state-aware equality: generated
        // range endpoints commonly retain a literal base plus an index, and
        // sending that shape through memory resolution first recursively
        // compares every nested load in the base expression.
        if let Some(index) = pointer.shared_element_index_from_base_with_width(base, byte_width)
            && index.operand_view().word32_constant().is_some()
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
                return shared_element_index_from_offset_with_facts(right, byte_width, self);
            }
            if offsets_equal(right, &base.offset) {
                return shared_element_index_from_offset_with_facts(left, byte_width, self);
            }
        }

        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if offsets_equal(&pointer.offset, left) {
                return shared_element_index_from_offset_with_facts(right, byte_width, self).map(
                    |index| {
                        index_binary(
                            MachineBinaryOp::Subtract,
                            MachineOperandView::Legacy(&MachineTerm::constant(0)),
                            index.operand_view(),
                        )
                    },
                );
            }
            if offsets_equal(&pointer.offset, right) {
                return shared_element_index_from_offset_with_facts(left, byte_width, self).map(
                    |index| {
                        index_binary(
                            MachineBinaryOp::Subtract,
                            MachineOperandView::Legacy(&MachineTerm::constant(0)),
                            index.operand_view(),
                        )
                    },
                );
            }
        }

        if offsets_equal(&pointer.offset, &base.offset) {
            return Some(
                MachineOperandView::Legacy(&MachineTerm::constant(0))
                    .retain(MachineIntegerType::Int32),
            );
        }
        None
    }

    fn pointer_element_index_from_base_for_memory_resolution(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        byte_width: u32,
    ) -> Option<SharedMachineIntegerTerm> {
        #[cfg(test)]
        PROOF_AWARE_POINTER_INDEX_QUERIES.with(|queries| queries.set(queries.get() + 1));
        let pointer = &crate::kernel::reasoning::pointer_in_block_for_memory_resolution(
            pointer,
            &base.block,
            self,
        )?;
        if pointer.offset == base.offset {
            return Some(
                MachineOperandView::Legacy(&MachineTerm::constant(0))
                    .retain(MachineIntegerType::Int32),
            );
        }
        // A zero-offset object base leaves the pointer's scaled offset as
        // the exact element index. Preserve that symbolic index so the
        // ordinary endpoint checks can certify an in-bounds access directly.
        if base.offset == PointerOffsetTerm::Constant(0) {
            return shared_element_index_from_offset_with_facts(&pointer.offset, byte_width, self);
        }
        let offsets_match_for_resolution = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
            left == right
                || crate::kernel::reasoning::pointer_offsets_proven_equal_for_memory_resolution(
                    left, right, self,
                )
        };
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if offsets_match_for_resolution(left, &base.offset) {
                return shared_element_index_from_offset_with_facts(right, byte_width, self);
            }
            if offsets_match_for_resolution(right, &base.offset) {
                return shared_element_index_from_offset_with_facts(left, byte_width, self);
            }
        }
        if let PointerOffsetTerm::Add(left, right) = &base.offset {
            if offsets_match_for_resolution(&pointer.offset, left) {
                return shared_element_index_from_offset_with_facts(right, byte_width, self).map(
                    |index| {
                        index_binary(
                            MachineBinaryOp::Subtract,
                            MachineOperandView::Legacy(&MachineTerm::constant(0)),
                            index.operand_view(),
                        )
                    },
                );
            }
            if offsets_match_for_resolution(&pointer.offset, right) {
                return shared_element_index_from_offset_with_facts(left, byte_width, self).map(
                    |index| {
                        index_binary(
                            MachineBinaryOp::Subtract,
                            MachineOperandView::Legacy(&MachineTerm::constant(0)),
                            index.operand_view(),
                        )
                    },
                );
            }
        }
        None
    }

    /// One endpoint bound of a range-membership question, by the exact
    /// routes first and the decision procedure last.
    fn proves_range_bound(&self, condition: ConditionTerm) -> bool {
        self.selected_comparison_value(&condition) == Some(true)
            || self.exact_ordering_modulo_canonical_atoms(&condition)
            || self.nonnegative_successor_by_exact_facts(&condition)
            || self.decide(&condition) == Some(true)
    }

    pub(in crate::kernel) fn pointer_in_range_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        start: &MachineTerm,
        end: &MachineTerm,
        element_width: u32,
    ) -> bool {
        // A loop invariant can establish that a havoced pointer local names
        // an address in an argument-backed range. Its symbolic block cannot
        // be indexed against that range directly, so follow the explicit
        // equality once to the concrete argument block. Restricting the
        // transport to symbolic blocks keeps this bounded and avoids walking
        // equality cycles back into the havoced pointer.
        // The true pointer equalities naming this pointer are filed under it
        // (`pointer_block_aliases`), so the hop reads them by key.
        if matches!(pointer.block, PointerBlock::Symbolic(_))
            && self.exact_pointer_aliases(pointer).any(|equivalent| {
                crate::instrumentation::record_deterministic_work(1);
                super::count_condition_fact_visit();
                !matches!(equivalent.block, PointerBlock::Symbolic(_))
                    && self.pointer_in_range_with_width(equivalent, base, start, end, element_width)
            })
        {
            return true;
        }
        let proves = |condition: ConditionTerm| self.proves_range_bound(condition);
        let range_base = base.offset_by_elements(start.clone(), element_width);
        if let Some(index) =
            self.pointer_element_index_from_base_with_width(pointer, &range_base, element_width)
        {
            let range_length = MachineTerm::subtract(end.clone(), start.clone());
            if proves(index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
                index.operand_view(),
            )) && proves(index_comparison(
                CompareRelation::LessThan,
                index.operand_view(),
                MachineOperandView::Legacy(&range_length),
            )) {
                return true;
            }
        }

        let Some(index) =
            self.pointer_element_index_from_base_with_width(pointer, base, element_width)
        else {
            return false;
        };
        proves(index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&start),
            index.operand_view(),
        )) && proves(index_comparison(
            CompareRelation::LessThan,
            index.operand_view(),
            MachineOperandView::Legacy(&end),
        ))
    }

    /// An exact ordering fact whose operands match the queried condition's
    /// operands modulo load variables: facts may write a load atom at
    /// a recorded state while the query carries the placeholder load or
    /// the load variable, and all of those are one atom. Bounded by
    /// the exact fact set and term size.
    pub(in crate::kernel) fn exact_ordering_modulo_canonical_atoms(
        &self,
        condition: &ConditionTerm,
    ) -> bool {
        if !matches!(
            condition,
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: _,
                right: _
            } | ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: _,
                right: _
            }
        ) {
            return false;
        }
        // A fact matches when each side has the query side's canonical form
        // (a load-free term is its own canonical form), so the facts that
        // match are among the ones filed under the query's canonical key,
        // which also holds the mirrored `>=`/`>` spellings. The lookup is
        // keyed; each fact filed there is one unit.
        let Some(key) = crate::kernel::assumptions::condition_match_key(condition) else {
            return false;
        };
        self.condition_facts_by_sides
            .get(&key)
            .is_some_and(|facts| {
                facts.iter().any(|(fact, value)| {
                    crate::instrumentation::record_deterministic_work(1);
                    super::count_condition_fact_visit();
                    *value && std::mem::discriminant(fact) == std::mem::discriminant(condition)
                })
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
        let ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: low,
            right: sum,
        } = condition
        else {
            return false;
        };
        if !matches!(low.as_ref(), bits32_constant!(0)) {
            return false;
        }
        let binary_term!(Int32, Add, term, one) = sum.as_ref() else {
            return false;
        };
        if !matches!(one.as_ref(), bits32_constant!(1)) {
            return false;
        }
        // Facts may write the load atom by its load variable while the
        // index carries the raw load (or vice versa); try both forms.
        let mut forms = vec![term.as_ref().clone()];
        if let MachineTerm::MemoryLoad(memory, pointer, kind) = term.as_ref() {
            let named = crate::kernel::canonical_form_of_load(
                memory.clone(),
                pointer.as_ref().clone(),
                *kind,
            );
            if !forms.contains(&named) {
                forms.push(named);
            }
        }
        forms.iter().any(|form| {
            let nonnegative =
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), form.clone());
            (self.selected_comparison_value(&nonnegative) == Some(true)
                || self.exact_ordering_modulo_canonical_atoms(&nonnegative))
                // A true `left < _` fact is an order fact filed under the
                // canonical form of `left` (`OrderFactsByLower`).
                && self
                    .order_facts_by_lower
                    .canonical_from(&crate::kernel::eval::canonical_term(form))
                    .any(|fact| {
                        self.condition_facts.get(fact) == Some(&true)
                            && matches!(
                                fact,
                                ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessThan, left, right: _ }
                                    if crate::kernel::eval::terms_have_same_canonical_form(
                                        left, form,
                                    )
                            )
                    })
        })
    }

    pub(crate) fn proves_resource_contains(&self, parent: &Resource, child: &Resource) -> bool {
        self.proves_resource_contains_inner(parent, child)
    }

    fn proves_resource_contains_inner(&self, parent: &Resource, child: &Resource) -> bool {
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
            for proposition in self.resource_contains_candidates(&current) {
                let Proposition::ResourceContains {
                    parent: fact_parent,
                    child: fact_child,
                } = proposition
                else {
                    continue;
                };
                if self.resource_contains_builtin(&current, fact_parent) {
                    stack.push(*fact_child.clone());
                }
            }
        }
        false
    }

    /// Address equality from the path facts, intentionally before consulting
    /// any resource-separation premise. A stale separation must not veto the
    /// equality that makes that same premise invalid.
    pub(in crate::kernel) fn pointers_proven_equal_ignoring_memory_separation(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        if left == right {
            return true;
        }
        // Memory is addressed: two pointers with equal addresses name the
        // same bytes, whatever objects they designate. A C pointer comparison
        // states exactly that (`program_pointer_comparison_condition`). Such a
        // fact files its address endpoints by object, so a context with none
        // filed asks nothing.
        if self.equality_graph.has_wide_pointer_sources()
            && self.uint64_values_known_equal(
                &MachineTerm::pointer_address(left.clone()),
                &MachineTerm::pointer_address(right.clone()),
            )
        {
            return true;
        }
        if left.blocks_proven_distinct(right) {
            return false;
        }
        self.pointers_known_equal(left, right)
    }

    /// Physical byte geometry from numeric address classes. A spelling from
    /// a different pointer origin is useful here without transferring that
    /// origin, ownership, or permission to either operand.
    pub(in crate::kernel) fn numeric_access_byte_overlap(
        &self,
        left: &Pointer,
        left_bytes: u32,
        right: &Pointer,
        right_bytes: u32,
    ) -> Option<crate::kernel::reasoning::AccessByteOverlap> {
        if !self.equality_graph.has_wide_pointer_sources() {
            return None;
        }
        let (left, right) = self.equality_graph.numeric_address_spellings(left, right);
        if left.block != right.block {
            return None;
        }
        crate::kernel::reasoning::exact_access_byte_overlap(&left, left_bytes, &right, right_bytes)
    }

    /// Whether a recorded separation between these ranges contradicts pointer
    /// equalities now known in this context. Separation is path evidence, so
    /// an entry-time fact is usable only while the ranges it names still miss
    /// each other. When their bases are proven equal, decide overlap in bytes;
    /// unknown bounds fail closed because they cannot validate the separation.
    pub(in crate::kernel) fn memory_ranges_overlap_after_base_equality(
        &self,
        left: &MemoryRange,
        right: &MemoryRange,
    ) -> bool {
        // A separation between ranges already written against the exact same
        // base was not made stale by a later alias. Keep that range authority;
        // the check here is only for formerly distinct base spellings.
        if left.base() == right.base()
            || !self.pointers_proven_equal_ignoring_memory_separation(left.base(), right.base())
        {
            return false;
        }
        if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
            if left.element_width() != right.element_width() {
                return true;
            }
            let bounds = |range: &MemoryRange| {
                crate::kernel::primitives::shared_wide_range_bounds(range, self)
            };
            let (Some((left_start, left_end)), Some((right_start, right_end))) =
                (bounds(left), bounds(right))
            else {
                return true;
            };
            return !(self.decide(&wide_index_comparison(
                CompareRelation::LessEqual,
                left_end.operand_view(),
                right_start.operand_view(),
            )) == Some(true)
                || self.decide(&wide_index_comparison(
                    CompareRelation::LessEqual,
                    right_end.operand_view(),
                    left_start.operand_view(),
                )) == Some(true));
        }
        if left.element_width() == right.element_width()
            && (self.decide(&ConditionTerm::signed_less_equal(
                left.end().clone(),
                right.start().clone(),
            )) == Some(true)
                || self.decide(&ConditionTerm::signed_less_equal(
                    right.end().clone(),
                    left.start().clone(),
                )) == Some(true))
        {
            return false;
        }
        let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
            left.signed_constant_start(),
            left.signed_constant_end(),
            right.signed_constant_start(),
            right.signed_constant_end(),
        ) else {
            return true;
        };
        if left_start >= left_end || right_start >= right_end {
            return false;
        }
        let left_width = i64::from(left.element_width());
        let right_width = i64::from(right.element_width());
        let Some(left_start) = left_start.checked_mul(left_width) else {
            return true;
        };
        let Some(left_end) = left_end.checked_mul(left_width) else {
            return true;
        };
        let Some(right_start) = right_start.checked_mul(right_width) else {
            return true;
        };
        let Some(right_end) = right_end.checked_mul(right_width) else {
            return true;
        };
        left_start < right_end && right_start < left_end
    }

    pub(in crate::kernel) fn pointer_overlaps_range_after_path_equality(
        &self,
        pointer: &Pointer,
        range: &MemoryRange,
    ) -> bool {
        if pointer_in_memory_range_shallow_with_facts(pointer, range, self) {
            return true;
        }
        if self.pointers_proven_equal_ignoring_memory_separation(pointer, range.base()) {
            let (Some(start), Some(end)) =
                (range.signed_constant_start(), range.signed_constant_end())
            else {
                return true;
            };
            return start <= 0 && 0 < end && range.element_width() > 0;
        }
        // A field of an object the range is spelled through another alias of:
        // `arena + 16` against `x[4..5)` of width 4 under `arena == x`. The
        // displacement is a constant, so the element it lands on is decided
        // without a search, and a cell inside the range is never separate
        // from it.
        let PointerOffsetTerm::Add(object, displacement) = &pointer.offset else {
            return false;
        };
        let (PointerOffsetTerm::Constant(displacement), Some(start), Some(end)) = (
            displacement.as_ref(),
            range.signed_constant_start(),
            range.signed_constant_end(),
        ) else {
            return false;
        };
        let width = i64::from(range.element_width());
        if width == 0 || displacement % width != 0 {
            return false;
        }
        let element = displacement / width;
        let object = Pointer {
            block: pointer.block.clone(),
            offset: object.as_ref().clone(),
        };
        start <= element
            && element < end
            && self.pointers_proven_equal_ignoring_memory_separation(&object, range.base())
    }

    pub(in crate::kernel) fn resource_separation_conflicts_with_equalities(
        &self,
        left: &Resource,
        right: &Resource,
    ) -> bool {
        match (left, right) {
            (Resource::Memory(left), Resource::Memory(right)) => {
                self.memory_ranges_overlap_after_base_equality(left, right)
            }
            _ => false,
        }
    }

    /// A stated separation covering two physical byte spans. Allocation sizes
    /// are unsigned; never reinterpret their high bit as a signed range bound.
    /// Only the matching block-pair bucket is visited. Clause bounds retain
    /// their signed Click meaning and are widened before multiplying widths.
    pub(in crate::kernel) fn proves_stated_byte_separation(
        &self,
        left: &Pointer,
        left_bytes: u32,
        right: &Pointer,
        right_bytes: u32,
    ) -> bool {
        let covers = |fact: &MemoryRange, base: &Pointer, bytes: u32| {
            let Some(delta) = fact
                .base()
                .exact_element_delta_from_base(base, 1, Some(self))
            else {
                return false;
            };
            if !delta.is_constant() {
                return false;
            }
            let bounds = (|| {
                let start = i64::from(fact.constant_start()? as i32)
                    .checked_mul(i64::from(fact.element_width()))?
                    .checked_add(delta.constant)?;
                let end = i64::from(fact.constant_end()? as i32)
                    .checked_mul(i64::from(fact.element_width()))?
                    .checked_add(delta.constant)?;
                Some(start <= 0 && i64::from(bytes) <= end && start < end)
            })();
            bounds == Some(true)
        };
        self.memory_separation_candidates(&left.block, &right.block)
            .any(|(proposition, fact_left, fact_right)| {
                let entails = (covers(fact_left, left, left_bytes)
                    && covers(fact_right, right, right_bytes))
                    || (covers(fact_left, right, right_bytes)
                        && covers(fact_right, left, left_bytes));
                if entails {
                    record_implicit_reasoning_provenance(self, proposition);
                }
                entails
            })
    }

    pub(crate) fn proves_resource_separate(&self, left: &Resource, right: &Resource) -> bool {
        self.proves_resource_separate_inner(left, right)
    }

    /// Project one selected separation from the live ownership partition.
    /// Each operand must be a different exact owned member, or a memory
    /// range fully contained in a different owned member; views and two
    /// slices of the same member provide no such evidence.
    /// Member lookup uses exact resources or the queried bases and aliases,
    /// without publishing or scanning the whole frame.
    pub(crate) fn proves_held_resources_separate(
        &self,
        resources: &ResourceContext,
        left: &Resource,
        right: &Resource,
    ) -> bool {
        if left == right || self.resource_separation_conflicts_with_equalities(left, right) {
            return false;
        }
        // Two different resources the state owns exactly are separate,
        // whatever kind each is: a folded instance beside a cell as much as
        // two cells.
        if resources
            .exact_resource_facts(left)
            .iter()
            .any(ResourceFact::is_own)
            && resources
                .exact_resource_facts(right)
                .iter()
                .any(ResourceFact::is_own)
        {
            return true;
        }
        // Finding an operand inside a larger owned member is a memory rule.
        let (Resource::Memory(left_range), Resource::Memory(right_range)) = (left, right) else {
            return false;
        };
        let (Some((left_entry, left_owner)), Some((right_entry, right_owner))) = (
            self.held_member_covering_range(resources, left_range),
            self.held_member_covering_range(resources, right_range),
        ) else {
            return false;
        };
        left_entry != right_entry
            && !self.resource_separation_conflicts_with_equalities(
                &Resource::Memory(left_owner.clone()),
                &Resource::Memory(right_owner.clone()),
            )
    }

    fn held_member_covering_range<'a>(
        &self,
        resources: &'a ResourceContext,
        requested: &MemoryRange,
    ) -> Option<(u64, &'a MemoryRange)> {
        // Keep symbolic and wide exact ownership on the fast path above.
        // A fixed-size field/range uses the same complete-access membership
        // judgment as memory framing, including mixed element widths.
        let elements = requested
            .signed_constant_end()?
            .checked_sub(requested.signed_constant_start()?)?;
        let bytes = u32::try_from(elements)
            .ok()?
            .checked_mul(requested.element_width())?;
        if bytes == 0 {
            return None;
        }
        let pointer = requested.start_pointer();
        for base in additive_base_spellings(&pointer) {
            for alias in std::iter::once(&base).chain(self.exact_pointer_aliases(&base)) {
                for (entry, range) in resources.owned_memory_members_with_base(alias) {
                    if self.kept_range_holds_access(range, &pointer, bytes) {
                        return Some((entry, range));
                    }
                }
            }
        }
        // The immediate spelling index is only a fast path. A transitive
        // address equality must select the same live owner as a checked read
        // or write; do not search unrelated resources or enumerate aliases.
        resources.owned_memory_member_covering_access(&pointer, bytes, self)
    }

    fn proves_resource_separate_inner(&self, left: &Resource, right: &Resource) -> bool {
        if self.resource_separation_conflicts_with_equalities(left, right) {
            return false;
        }
        // Iterated ownership is separate from a range its elements provably
        // miss: another block, or outside the span of every element. One
        // decision, whatever the index range's size; a range that might hold
        // an element is never proved separate.
        match (left, right) {
            (Resource::Iterated(iterated), Resource::Memory(range))
            | (Resource::Memory(range), Resource::Iterated(iterated)) => {
                return crate::kernel::iterated::iterated_separate_from_range(
                    iterated, range, self,
                );
            }
            (Resource::Iterated(_), _) | (_, Resource::Iterated(_)) => return false,
            _ => {}
        }
        // Separation is a claim about bytes, so a range may be spelled at the
        // coordinate its base is proven equal to: the argument block or a
        // storage block its class has, where held ranges are spelled. Address
        // equality decides bytes; it grants no access, which ownership
        // coverage checks separately.
        if let (Resource::Memory(left_range), Resource::Memory(right_range)) = (left, right) {
            let rebase = |range: &MemoryRange| {
                let coordinate = self.equality_graph.canonical_pointer(range.base())?;
                if coordinate.representative == range.base().block
                    || !matches!(coordinate.representative, PointerBlock::ExternalArgument)
                        && !matches!(
                            coordinate.representative,
                            PointerBlock::Heap(_)
                                | PointerBlock::Temporary(_)
                                | PointerBlock::StringLiteral { .. }
                        )
                        && !matches!(&coordinate.representative, PointerBlock::Concrete(name) if name != "null")
                {
                    return None;
                }
                let base = Pointer {
                    block: coordinate.representative,
                    offset: coordinate.offset.to_offset_term()?,
                };
                let (start, end) = range.bound_terms();
                Some(range.with_bounds(base, start.clone(), end.clone()))
            };
            let (rebased_left, rebased_right) = (rebase(left_range), rebase(right_range));
            if (rebased_left.is_some() || rebased_right.is_some())
                && self.proves_resource_separate_inner(
                    &Resource::Memory(rebased_left.unwrap_or_else(|| left_range.clone())),
                    &Resource::Memory(rebased_right.unwrap_or_else(|| right_range.clone())),
                )
            {
                return true;
            }
        }
        if let (Resource::Memory(left), Resource::Memory(right)) = (left, right)
            && left.base().blocks_proven_distinct(right.base())
        {
            return true;
        }

        if let (Resource::Memory(left), Resource::Memory(right)) = (left, right)
            && left.base() == right.base()
            && let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
                left.signed_constant_start(),
                left.signed_constant_end(),
                right.signed_constant_start(),
                right.signed_constant_end(),
            )
            && (left_end <= right_start || right_end <= left_start)
        {
            return true;
        }

        if let (Resource::Memory(a), Resource::Memory(b)) = (left, right)
            && self
                .borrow_partition_separated_members(
                    a.base(),
                    b.base(),
                    |range| {
                        self.proves_resource_contains_inner(&Resource::Memory(range.clone()), left)
                    },
                    |range| {
                        self.proves_resource_contains_inner(&Resource::Memory(range.clone()), right)
                    },
                )
                .is_some()
        {
            return true;
        }

        let separation_fact_entails = |fact_left: &Resource, fact_right: &Resource| {
            (self.proves_resource_contains_inner(fact_left, left)
                && self.proves_resource_contains_inner(fact_right, right)
                || self.proves_resource_contains_inner(fact_left, right)
                    && self.proves_resource_contains_inner(fact_right, left))
                && !self.resource_separation_conflicts_with_equalities(fact_left, fact_right)
        };
        // For a memory-memory query, memory-memory separation facts live in
        // the block-pair index and are consulted by the indexed pass below;
        // the linear pass covers only the residual facts with a non-memory
        // side, whose containment can still entail memory separation
        // through a composite body. Any other query shape scans every
        // separation fact: the indexed pass below does not run for it.
        // A non-memory side's containers are found upward from it
        // (`separations_with_side_containing`).
        let memory_memory_query =
            matches!((left, right), (Resource::Memory(_), Resource::Memory(_)));
        let scan_facts: &dyn Fn(&dyn Fn(&Proposition) -> bool) -> bool = &|entails| {
            if memory_memory_query {
                return self.nonmemory_separation_facts.iter().any(entails);
            }
            let keyed = if matches!(left, Resource::Memory(_)) {
                right
            } else {
                left
            };
            let indexed = self
                .separations_with_side_containing(keyed)
                .into_iter()
                .any(entails);
            #[cfg(debug_assertions)]
            if !crate::instrumentation::in_uncharged_debug_check() {
                crate::instrumentation::uncharged_debug_check(|| {
                    let scanned = self.separation_facts.scan_for_upkeep().any(entails);
                    assert_eq!(
                        indexed, scanned,
                        "the separations containing a side differ from every separation"
                    );
                });
            }
            indexed
        };
        let residual_hit = crate::instrumentation::measure_operation(
            "kernel",
            "resource separation",
            "resource separation: residual facts",
            || {
                scan_facts(&|proposition| {
                    let Proposition::ResourceSeparate {
                        left: fact_left,
                        right: fact_right,
                    } = proposition
                    else {
                        return false;
                    };
                    separation_fact_entails(fact_left, fact_right)
                })
            },
        );
        if residual_hit {
            return true;
        }
        // The stated memory separations of this block pair, then the same law
        // asked of each held composition: two owned members of one valid
        // composition are separate.
        if let (Resource::Memory(left_range), Resource::Memory(right_range)) = (left, right)
            && (crate::instrumentation::measure_operation(
                "kernel",
                "resource separation",
                "resource separation: stated block pair",
                || {
                    self.memory_separation_candidates(
                        &left_range.base().block,
                        &right_range.base().block,
                    )
                    .any(|(_, fact_left, fact_right)| {
                        separation_fact_entails(
                            &Resource::Memory(fact_left.clone()),
                            &Resource::Memory(fact_right.clone()),
                        )
                    })
                },
            ) || crate::instrumentation::measure_operation(
                "kernel",
                "resource separation",
                "resource separation: composition members",
                || {
                    self.composition_separated_members(
                        &left_range.start_pointer(),
                        &right_range.start_pointer(),
                        |member| {
                            self.proves_resource_contains_inner(
                                &Resource::Memory(member.clone()),
                                left,
                            )
                        },
                        |member| {
                            self.proves_resource_contains_inner(
                                &Resource::Memory(member.clone()),
                                right,
                            )
                        },
                        |member_left, member_right| {
                            !self.resource_separation_conflicts_with_equalities(
                                &Resource::Memory(member_left.clone()),
                                &Resource::Memory(member_right.clone()),
                            )
                        },
                    )
                    .is_some()
                },
            ))
        {
            return true;
        }

        if crate::instrumentation::measure_operation(
            "kernel",
            "resource separation",
            "resource separation: owned resources",
            || {
                // Two memory sides find their owners in their ranges' blocks,
                // the keys `CompositionMemberIndex` lists a composition
                // under; other resources are matched by identity, which it
                // does not index.
                if let (Resource::Memory(left_range), Resource::Memory(right_range)) = (left, right)
                {
                    self.composition_members
                        .listed_under([], [&left_range.base().block, &right_range.base().block])
                        .into_iter()
                        .any(|resources| {
                            resources.proves_owned_resources_separate(left, right, self)
                        })
                } else {
                    // Each side is matched in its own bucket: a memory side
                    // by block, another by the `OwnedMemberKey`s that hold
                    // every member able to entail it, the keys
                    // `CompositionMemberIndex` lists a composition under.
                    let mut blocks = Vec::new();
                    let mut members = Vec::new();
                    for side in [left, right] {
                        match side {
                            Resource::Memory(range) => blocks.push(range.base().block.clone()),
                            other => members.extend(OwnedMemberKey::probed(
                                &crate::kernel::ResourceFact::View(other.clone()),
                                self,
                            )),
                        }
                    }
                    let separates = |resources: &ResourceContext| {
                        resources.proves_owned_resources_separate(left, right, self)
                    };
                    let indexed = self
                        .composition_members
                        .listed_under_members(blocks.iter(), members.iter())
                        .into_iter()
                        .any(separates);
                    #[cfg(debug_assertions)]
                    if !crate::instrumentation::in_uncharged_debug_check() {
                        crate::instrumentation::uncharged_debug_check(|| {
                            let scanned =
                                self.resource_compositions.scan_for_upkeep().any(separates);
                            assert_eq!(
                                indexed, scanned,
                                "the listed compositions' owned separation differs from every \
                                 composition's"
                            );
                        });
                    }
                    indexed
                }
            },
        ) {
            return true;
        }

        if let (Resource::Memory(left), Resource::Memory(right)) = (left, right) {
            let composition_covers = |target: &MemoryRange, other: &MemoryRange| {
                if target.wide_bounds().is_some() {
                    return false;
                }
                let covers = |resources: &ResourceContext| {
                    let cover = |ranges: Vec<MemoryRange>| {
                        let intervals = ranges
                            .into_iter()
                            .filter_map(|range| {
                                if range.wide_bounds().is_some() {
                                    return None;
                                }
                                self.fact_range_interval_on_target(
                                    target,
                                    range.base(),
                                    range.start(),
                                    range.end(),
                                )
                            })
                            .collect();
                        range_intervals_cover_target(target, intervals)
                    };
                    let indexed = cover(resources.owned_memory_ranges_separate_from(
                        target,
                        other,
                        self,
                        |owner, child| self.proves_resource_contains_inner(owner, child),
                    ));
                    #[cfg(debug_assertions)]
                    if crate::instrumentation::separation_candidate_cross_checks_enabled()
                        && !crate::instrumentation::in_uncharged_debug_check()
                    {
                        crate::instrumentation::uncharged_debug_check(|| {
                            let full =
                                cover(resources.owned_memory_ranges_separate_from_full_scan(
                                    &target.base().block,
                                    &Resource::Memory(other.clone()),
                                    |owner, child| {
                                        self.proves_resource_contains_inner(owner, child)
                                    },
                                ));
                            assert_eq!(
                                indexed, full,
                                "indexed separation interval cover differs from full scan"
                            );
                        });
                    }
                    indexed
                };
                // A composition covers `target` with its owned members in
                // `target`'s block, apart from an owner of `other`: a member
                // in `other`'s block or in one its address equals, or a
                // container of such memory through containment facts,
                // walked upward from `other`'s blocks (`memory_containers`,
                // `resource_containers`). The compositions listed under
                // those blocks and the non-memory containers' keys are
                // enough (`CompositionMemberIndex`): one listed under none
                // of them holds no member there beyond its predecessor,
                // which then covers whatever it covers.
                let mut blocks = Vec::new();
                let mut pending_blocks = Vec::new();
                let add_blocks =
                    |range: &MemoryRange,
                     blocks: &mut Vec<PointerBlock>,
                     pending: &mut Vec<PointerBlock>| {
                        let mut add = |block: PointerBlock| {
                            if !blocks.contains(&block) {
                                blocks.push(block.clone());
                                pending.push(block);
                            }
                        };
                        add(range.base().block.clone());
                        for pointer in [range.base().clone(), range.start_pointer()] {
                            for (alias, _) in self.pointer_equality_component(&pointer) {
                                add(alias.block);
                            }
                        }
                    };
                add_blocks(other, &mut blocks, &mut pending_blocks);
                let mut containers = BTreeSet::new();
                let mut pending_containers = Vec::new();
                loop {
                    let facts = if let Some(block) = pending_blocks.pop() {
                        self.memory_containers.get(&block)
                    } else if let Some(container) = pending_containers.pop() {
                        self.resource_containers.get(container)
                    } else {
                        break;
                    };
                    for fact in facts
                        .into_iter()
                        .flat_map(crate::persistent::PersistentSet::iter)
                    {
                        crate::instrumentation::record_deterministic_work(1);
                        let Proposition::ResourceContains { parent, .. } = fact else {
                            continue;
                        };
                        match &**parent {
                            Resource::Memory(range) => {
                                add_blocks(range, &mut blocks, &mut pending_blocks);
                            }
                            container => {
                                if containers.insert(container) {
                                    pending_containers.push(container);
                                }
                            }
                        }
                    }
                }
                if !blocks.contains(&target.base().block) {
                    blocks.push(target.base().block.clone());
                }
                let members = containers
                    .into_iter()
                    .filter_map(|container| {
                        OwnedMemberKey::exact(&crate::kernel::ResourceFact::View(container.clone()))
                    })
                    .collect::<Vec<_>>();
                let indexed = self
                    .composition_members
                    .listed_under_members(blocks.iter(), members.iter())
                    .into_iter()
                    .any(covers);
                #[cfg(debug_assertions)]
                if !crate::instrumentation::in_uncharged_debug_check() {
                    crate::instrumentation::uncharged_debug_check(|| {
                        let scanned = self.resource_compositions.scan_for_upkeep().any(covers);
                        assert_eq!(
                            indexed, scanned,
                            "the listed compositions' cover differs from every composition's"
                        );
                    });
                }
                indexed
            };
            if crate::instrumentation::measure_operation(
                "kernel",
                "resource separation",
                "resource separation: composition covers",
                || composition_covers(left, right) || composition_covers(right, left),
            ) {
                return true;
            }
            return crate::instrumentation::measure_operation(
                "kernel",
                "resource separation",
                "resource separation: separate-range covers",
                || {
                    self.range_covered_by_resource_separate_ranges(left, right)
                        || self.range_covered_by_resource_separate_ranges(right, left)
                },
            );
        }

        false
    }

    fn resource_contains_builtin(&self, parent: &Resource, child: &Resource) -> bool {
        if parent == child {
            return true;
        }
        let (Resource::Memory(parent), Resource::Memory(child)) = (parent, child) else {
            return false;
        };
        if self.memory_ranges_proven_equal(parent, child) {
            return true;
        }
        if parent.wide_bounds().is_some() || child.wide_bounds().is_some() {
            return crate::kernel::primitives::wide_memory_range_covers(parent, child, self);
        }
        // Constant byte intervals can cross element-width boundaries. Compare
        // the complete child span, not merely its first addressed element.
        fn constant_delta(offset: &PointerOffsetTerm, base: &PointerOffsetTerm) -> Option<i64> {
            if offset == base {
                return Some(0);
            }
            match (offset, base) {
                (PointerOffsetTerm::Constant(a), PointerOffsetTerm::Constant(b)) => {
                    a.checked_sub(*b)
                }
                (PointerOffsetTerm::Add(a, b), _) => match b.as_ref() {
                    PointerOffsetTerm::Constant(bytes) => {
                        constant_delta(a, base)?.checked_add(*bytes)
                    }
                    _ => match a.as_ref() {
                        PointerOffsetTerm::Constant(bytes) => {
                            constant_delta(b, base)?.checked_add(*bytes)
                        }
                        _ => None,
                    },
                },
                (_, PointerOffsetTerm::Add(a, b)) => match b.as_ref() {
                    PointerOffsetTerm::Constant(bytes) => {
                        constant_delta(offset, a)?.checked_sub(*bytes)
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        if parent.base().block == child.base().block
            && let (Some(delta), Some(lo), Some(hi), Some(inner_lo), Some(inner_hi)) = (
                constant_delta(&child.base().offset, &parent.base().offset),
                parent.start().as_const(),
                parent.end().as_const(),
                child.start().as_const(),
                child.end().as_const(),
            )
        {
            let lo = i128::from(lo as i32) * i128::from(parent.element_width());
            let hi = i128::from(hi as i32) * i128::from(parent.element_width());
            let inner_lo =
                i128::from(delta) + i128::from(inner_lo as i32) * i128::from(child.element_width());
            let inner_hi =
                i128::from(delta) + i128::from(inner_hi as i32) * i128::from(child.element_width());
            return lo <= hi
                && inner_lo <= inner_hi
                && (inner_lo == inner_hi || lo <= inner_lo && inner_hi <= hi);
        }
        // The element-membership rule below checks one parent element. A
        // differently sized child needs a byte-span proof, not that rule.
        if parent.element_width() != child.element_width() {
            return false;
        }
        if MachineTerm::subtract(child.end().clone(), child.start().clone()).as_const() == Some(1) {
            let child_pointer = child
                .base
                .offset_by_elements(child.start().clone(), child.element_width());
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

    fn memory_ranges_proven_equal(&self, left: &MemoryRange, right: &MemoryRange) -> bool {
        if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
            return crate::kernel::primitives::wide_memory_range_covers(left, right, self)
                && crate::kernel::primitives::wide_memory_range_covers(right, left, self);
        }
        let left_length = memory_range_length_term(left);
        let right_length = memory_range_length_term(right);
        left.element_width() == right.element_width()
            && self.pointers_proven_equal_for_fact_transport(left.base(), right.base())
            && self.bitvector_terms_equal_for_fact_transport(left.start(), right.start())
            && self.bitvector_terms_equal_for_fact_transport(&left_length, &right_length)
    }

    fn pointers_proven_equal_for_fact_transport(&self, left: &Pointer, right: &Pointer) -> bool {
        if pointers_proven_equal_by_reasoning(left, right, self) {
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
            shared_element_index_from_offset(&left.offset, element_width),
            shared_element_index_from_offset(&right.offset, element_width),
        ) else {
            return false;
        };
        self.bitvector_terms_equal_for_fact_transport_views(
            left.operand_view(),
            right.operand_view(),
        )
    }

    fn bitvector_terms_equal_for_fact_transport(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.bitvector_terms_equal_for_fact_transport_views(
            MachineOperandView::Legacy(left),
            MachineOperandView::Legacy(right),
        )
    }

    fn bitvector_terms_equal_for_fact_transport_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        if self.bitvector_terms_equal_for_transport_views(left, right) {
            return true;
        }
        // Only selected load leaves cross the state machinery's native boundary.
        let source = |v: MachineOperandView<'_>| {
            v.read_source().map(|s| s.into_owned()).or_else(|| {
                v.variable()
                    .and_then(crate::kernel::eval::registered_load_origin_term_for_variable)
            })
        };
        if let (Some(a), Some(b)) = (source(left), source(right))
            && memory_load_terms_equal_for_fact_transport(&a, &b, self)
        {
            return true;
        }
        match (left.binary(), right.binary()) {
            (Some((lf, lo, [la, lb])), Some((rf, ro, [ra, rb])))
                if lf == rf
                    && lf.format().bits() == 32
                    && lo == ro
                    && matches!(
                        lo,
                        MachineBinaryOp::Add
                            | MachineBinaryOp::Subtract
                            | MachineBinaryOp::Multiply
                    ) =>
            {
                self.bitvector_terms_equal_for_fact_transport_views(la, ra)
                    && self.bitvector_terms_equal_for_fact_transport_views(lb, rb)
            }
            _ => false,
        }
    }

    fn range_covered_by_resource_separate_ranges(
        &self,
        target: &MemoryRange,
        other: &MemoryRange,
    ) -> bool {
        if target.wide_bounds().is_some() {
            return false;
        }
        let mut intervals = Vec::new();
        // The separations between the blocks of the target's base and
        // `other`'s, each with its exact aliases, and those with a non-memory
        // side, which may contain `other` through a composite body: the
        // block-pair index and its residue.
        let blocks = |base: &Pointer| {
            let mut blocks = vec![base.block.clone()];
            for alias in self.exact_pointer_aliases(base) {
                if !blocks.contains(&alias.block) {
                    blocks.push(alias.block.clone());
                }
            }
            blocks
        };
        let mut candidates = Vec::new();
        for target_block in blocks(target.base()) {
            for other_block in blocks(other.base()) {
                for (proposition, _, _) in
                    self.memory_separation_candidates(&target_block, &other_block)
                {
                    crate::instrumentation::record_deterministic_work(1);
                    if !candidates.contains(&proposition) {
                        candidates.push(proposition);
                    }
                }
            }
        }
        candidates.extend(self.nonmemory_separation_facts.iter());
        for proposition in candidates {
            let Proposition::ResourceSeparate { left, right } = proposition else {
                continue;
            };
            if self.resource_separation_conflicts_with_equalities(left, right) {
                continue;
            }

            if self.proves_resource_contains(right, &Resource::Memory(other.clone()))
                && let Resource::Memory(left) = &**left
                && left.wide_bounds().is_none()
                && let Some(interval) = self.fact_range_interval_on_target(
                    target,
                    left.base(),
                    left.start(),
                    left.end(),
                )
            {
                intervals.push(interval);
            }

            if self.proves_resource_contains(left, &Resource::Memory(other.clone()))
                && let Resource::Memory(right) = &**right
                && right.wide_bounds().is_none()
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
        target: &MemoryRange,
        base: &Pointer,
        start: &MachineTerm,
        end: &MachineTerm,
    ) -> Option<(i64, i64)> {
        let base = &self.pointer_in_block(base, &target.base.block)?;
        let base_delta = self.pointer_element_index_from_base_with_width(
            base,
            &target.base,
            target.element_width(),
        )?;
        let start = index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Legacy(start),
        );
        let end = index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Legacy(end),
        );
        Some((
            signed_index_constant(start.operand_view())?,
            signed_index_constant(end.operand_view())?,
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

    /// The unsigned 64-bit element index of an access at `pointer` from
    /// `base`. Beside the exact wide forms
    /// ([`Pointer::shared_wide_element_index_from_base`]), an offset already
    /// rewritten to a signed 32-bit index is read back: `(int32)i` scaled,
    /// or `(int32)i + c`, is the offset of `i` or `i + c` when that 64-bit
    /// value is decided to be at most `INT_MAX`, since truncation commutes
    /// with the addition and is then exact and nonnegative. Any other `int32`
    /// index is read as its sign extension.
    pub(in crate::kernel) fn shared_wide_element_index_of_access(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        element_width: u32,
    ) -> Option<SharedMachineIntegerTerm> {
        let literal = |value| {
            let root = KernelTerm::retained_native_machine_operand(
                MachineIntegerType::UInt64,
                &MachineTerm::uint64_constant(value),
            );
            MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64)
        };
        let cast = |value: MachineOperandView<'_>, source, encoding| {
            let root = KernelTerm::machine_cast_shared(
                encoding,
                source,
                MachineIntegerType::UInt64,
                KernelTerm::retained_machine_operand(source, value),
            );
            MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64)
        };
        if let Some(index) = pointer.shared_wide_element_index_from_base(base, element_width) {
            return Some(index);
        }
        // A negative signed index has its high bit set when read unsigned,
        // placing it beyond every permitted wide range endpoint.
        if let Some(PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned: false,
        }) = pointer.offset_from_base(base)
            && byte_width == i64::from(element_width)
        {
            return Some(if let Some(value) = value.operand_view().int64_constant() {
                literal(value as u64)
            } else {
                cast(
                    value.operand_view(),
                    MachineIntegerType::Int64,
                    MachineCastSpelling::UInt64FromInt64,
                )
            });
        }
        if let Some(PointerOffsetTerm::Add(first, second)) = pointer.offset_from_base(base) {
            let width = i64::from(element_width);
            let whole_elements = |offset: &PointerOffsetTerm| match offset {
                PointerOffsetTerm::Constant(bytes) if *bytes >= 0 && bytes % width == 0 => {
                    Some((bytes / width) as u64)
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned: true,
                } if *byte_width == width => value.operand_view().uint64_constant(),
                _ => None,
            };
            let symbolic_index = |offset: &PointerOffsetTerm| match offset {
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned: true,
                } if *byte_width == width && value.operand_view().uint64_constant().is_none() => {
                    Some(value.clone())
                }
                _ => None,
            };
            let stepped = symbolic_index(&first)
                .zip(whole_elements(&second))
                .or_else(|| symbolic_index(&second).zip(whole_elements(&first)));
            // Advancing a native index requires the same complete no-wrap bound.
            if let Some((index, elements)) = stepped
                && self.decide(&wide_index_comparison(
                    CompareRelation::LessEqual,
                    index.operand_view(),
                    literal(u64::MAX - elements).operand_view(),
                )) == Some(true)
            {
                return Some(wide_index_binary(
                    MachineBinaryOp::Add,
                    index.operand_view(),
                    literal(elements).operand_view(),
                ));
            }
            if let (Some(outer), Some(inner)) = (symbolic_index(&first), symbolic_index(&second)) {
                let small = |index: &SharedMachineIntegerTerm| {
                    self.decide(&wide_index_comparison(
                        CompareRelation::LessEqual,
                        index.operand_view(),
                        literal(i64::MAX as u64).operand_view(),
                    )) == Some(true)
                };
                if small(&outer) && small(&inner) {
                    return Some(wide_index_binary(
                        MachineBinaryOp::Add,
                        outer.operand_view(),
                        inner.operand_view(),
                    ));
                }
            }
        }
        let PointerOffsetTerm::Int32Scaled { value, byte_width } =
            pointer.offset_from_base(base)?
        else {
            return None;
        };
        if byte_width != i64::from(element_width) {
            return None;
        }
        Some(
            crate::kernel::primitives::checked_shared_native_range_endpoint(
                value.operand_view(),
                self,
            )
            .unwrap_or_else(|| {
                cast(
                    value.operand_view(),
                    MachineIntegerType::Int32,
                    MachineCastSpelling::UInt64FromInt32,
                )
            }),
        )
    }

    /// A complete aligned access lies outside a native range. Both byte
    /// extents remain non-wrapping; a low-word index supplies no separation.
    fn pointer_access_outside_wide_range(
        &self,
        pointer: &Pointer,
        bytes: u32,
        range: &MemoryRange,
    ) -> bool {
        let Some((start, end)) = range.wide_bounds() else {
            return false;
        };
        let width = range.element_width();
        let Some(span) = crate::kernel::memory_provenance::access_element_span(bytes, width)
            .and_then(|span| u64::try_from(span).ok())
        else {
            return false;
        };
        let selected = self
            .equality_graph
            .pointer_at_base(pointer, range.base())
            .unwrap_or_else(|| pointer.clone());
        let Some(index) = self.shared_wide_element_index_of_access(&selected, range.base(), width)
        else {
            return false;
        };
        let limit = i64::MAX as u64 / u64::from(width);
        let Some(last_start) = limit.checked_sub(span) else {
            return false;
        };
        let holds = |lower: MachineOperandView<'_>, upper: MachineOperandView<'_>| {
            lower.retain(MachineIntegerType::UInt64) == upper.retain(MachineIntegerType::UInt64)
                || self.decide(&wide_index_comparison(
                    CompareRelation::LessEqual,
                    lower,
                    upper,
                )) == Some(true)
        };
        holds(
            MachineOperandView::Legacy(end),
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(limit)),
        ) && holds(
            index.operand_view(),
            MachineOperandView::Legacy(&MachineTerm::uint64_constant(last_start)),
        ) && (holds(MachineOperandView::Legacy(end), index.operand_view()) || {
            let access_end = wide_index_binary(
                MachineBinaryOp::Add,
                index.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(span)),
            );
            holds(access_end.operand_view(), MachineOperandView::Legacy(start))
        })
    }

    /// [`Self::pointer_access_in_range`] or [`Self::pointer_access_in_wide_range`],
    /// as `range`'s index kind requires. A wide range places whole-element
    /// accesses, and fields of a struct-array byte range.
    pub(in crate::kernel) fn pointer_access_in_held_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        range: &MemoryRange,
    ) -> bool {
        if range.wide_bounds().is_some() {
            return self.pointer_access_in_wide_range(pointer, byte_width, range);
        }
        self.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
            range.element_width(),
        )
    }

    /// Whether an access of `byte_width` bytes at `pointer` lies in a wide
    /// range holding `m` structs of `k` bytes ([`wide_struct_array_count`]:
    /// the byte range `base[0..m * k]` or the `k`-byte element range
    /// `base[0..m]`), for an access inside one struct: a constant byte offset
    /// `c` with
    /// `ceil((c + byte_width) / k) <= m`, or a field of element `i`,
    /// `i * k + c` ([`scaled_element_offset`]) with `c + byte_width <= k`,
    /// with `0 <= i < m` ([`wide_index_bound_conditions`]). False when the
    /// range or the offset has another shape or a comparison is not decided;
    /// the caller then tries the whole-element rule.
    ///
    /// The byte comparison `offset + byte_width <= m * k` reads the wrapping
    /// `uint64` product, which the facts about `m` do not decide. The element
    /// comparisons are equivalent once `m <= i64::MAX / k` is decided, which
    /// this rule decides itself: then `m * k` is the mathematical byte count
    /// and at most `i64::MAX`, the object-size limit the whole-element rule
    /// asks of its end. (A heap block's range ends at its extent, which was
    /// admitted with that bound decided; an element range's own extent guard
    /// is the same bound.)
    ///
    /// [`scaled_element_offset`]: crate::kernel::reasoning::scaled_element_offset
    /// [`wide_index_bound_conditions`]: crate::kernel::reasoning::wide_index_bound_conditions
    pub(in crate::kernel) fn field_access_in_wide_struct_array(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        range: &MemoryRange,
    ) -> bool {
        byte_width > 0 && self.place_in_wide_struct_array(pointer, byte_width, range)
    }

    /// Whether `pointer` is a position in a wide struct array
    /// ([`wide_struct_array_count`]) that may be formed: the formation rule
    /// a heap block's 64-bit extent uses (`wide_element_block_bounds` in
    /// `eval/operators.rs`), over a held range's own struct count. A constant
    /// byte offset `c` is `ceil(c / k) <= m`, and `i * k + c` with
    /// `0 <= c < k` is `i <= m` when `c == 0` (the one-past position), else
    /// `i < m`. The bound `m <= i64::MAX / k` is decided as for an access.
    pub(in crate::kernel) fn position_in_wide_struct_array(
        &self,
        pointer: &Pointer,
        range: &MemoryRange,
    ) -> bool {
        self.place_in_wide_struct_array(pointer, 0, range)
    }

    /// An access of `byte_width` bytes, or with `byte_width == 0` a formed
    /// position, inside one struct of a wide struct array.
    fn place_in_wide_struct_array(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        range: &MemoryRange,
    ) -> bool {
        let Some((count, stride)) = wide_struct_array_count(range) else {
            return false;
        };
        let bytes = i64::from(byte_width);
        let holds = |condition: ConditionTerm| self.decide(&condition) == Some(true);
        let exact = || {
            holds(ConditionTerm::uint64_less_equal(
                count.clone(),
                MachineTerm::uint64_constant((i64::MAX / stride) as u64),
            ))
        };
        let Some(offset) = pointer.offset_from_base(range.base()) else {
            return false;
        };
        if let PointerOffsetTerm::Constant(field) = offset {
            // A constant offset before the range is never inside it.
            let Some(last) = (field >= 0)
                .then(|| field.checked_add(bytes))
                .flatten()
                .and_then(|last| u64::try_from(last).ok())
            else {
                return false;
            };
            let bound = MachineTerm::uint64_constant(last.div_ceil(stride as u64));
            return exact() && holds(ConditionTerm::uint64_less_equal(bound, count.clone()));
        }
        let Some(element) = crate::kernel::reasoning::scaled_element_offset(&offset) else {
            return false;
        };
        if element.stride != stride
            || !(0..stride).contains(&element.field)
            || element
                .field
                .checked_add(bytes)
                .is_none_or(|last| last > stride)
        {
            return false;
        }
        // Only the start of an element may be one past the last one.
        let strict = bytes > 0 || element.field != 0;
        exact()
            && crate::kernel::reasoning::wide_index_bound_conditions(
                &element.index,
                element.signed,
                count,
                strict,
                self,
            )
            .into_iter()
            .all(holds)
    }

    /// Whether an access of `byte_width` bytes at `pointer` lies in the wide
    /// range `base[start..end]` of `element_width`-byte elements.
    ///
    /// A field of a struct in a byte range `base[0..m * k]` or a struct
    /// range `base[0..m]` is placed over the struct count
    /// ([`Self::field_access_in_wide_struct_array`]).
    /// Otherwise the access must be one whole element at an exact offset `i *
    /// element_width` from the base, where `i` is an unsigned 64-bit index
    /// (or a constant), with `start <= i`, `i < end` and `end <= i64::MAX /
    /// element_width` decided as 64-bit unsigned comparisons. The last is
    /// the object-size limit: under it `i * element_width` does not exceed
    /// `i64::MAX`, so the offset term is the mathematical offset and the
    /// two comparisons place the access. No 32-bit reading of an index or a
    /// bound takes part.
    pub(in crate::kernel) fn pointer_access_in_wide_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        range: &MemoryRange,
    ) -> bool {
        let Some((start, end)) = range.wide_bounds() else {
            return false;
        };
        let base = range.base();
        let element_width = range.element_width();
        // Only a struct array places a narrower access, as a field.
        if byte_width != element_width && wide_struct_array_count(range).is_none() {
            return false;
        }
        let resolved = if pointer == base || self.pointers_known_equal(pointer, base) {
            base.clone()
        } else {
            self.equality_graph
                .pointer_at_base(pointer, base)
                .unwrap_or_else(|| pointer.clone())
        };
        if self.field_access_in_wide_struct_array(&resolved, byte_width, range) {
            return true;
        }
        if byte_width != element_width {
            return false;
        }
        let Some(index) = self.shared_wide_element_index_of_access(&resolved, base, element_width)
        else {
            return false;
        };
        let limit = i64::MAX as u64 / u64::from(element_width);
        let holds = |relation, left: MachineOperandView<'_>, right: MachineOperandView<'_>| {
            self.decide(&wide_index_comparison(relation, left, right)) == Some(true)
        };
        let end_view = MachineOperandView::Legacy(end);
        let below_equal_spelling = || {
            let Some((MachineIntegerType::UInt64, MachineBinaryOp::Subtract, [whole, taken])) =
                index.operand_view().binary()
            else {
                return false;
            };
            (holds(CompareRelation::Equal, whole, end_view)
                || holds(CompareRelation::Equal, end_view, whole))
                && (holds(
                    CompareRelation::LessThan,
                    wide_index_binary(MachineBinaryOp::Subtract, end_view, taken).operand_view(),
                    end_view,
                ) || (holds(
                    CompareRelation::LessEqual,
                    MachineOperandView::Legacy(&MachineTerm::uint64_constant(1)),
                    taken,
                ) && holds(CompareRelation::LessEqual, taken, end_view)))
        };
        // A successor endpoint must still owe its original no-wrap guard.
        let below_unwrapped_successor = || {
            let Some((MachineIntegerType::UInt64, MachineBinaryOp::Add, [whole, added])) =
                end_view.binary()
            else {
                return false;
            };
            let Some(added) = added.uint64_constant().filter(|value| *value >= 1) else {
                return false;
            };
            holds(
                CompareRelation::LessEqual,
                whole,
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(u64::MAX - added)),
            ) && (index
                .operand_view()
                .uint64_constant()
                .is_some_and(|value| value < added)
                || holds(CompareRelation::LessEqual, index.operand_view(), whole)
                || holds(CompareRelation::Equal, index.operand_view(), whole))
        };
        (start.uint64_as_const() == Some(0)
            || holds(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(start),
                index.operand_view(),
            ))
            && (holds(CompareRelation::LessThan, index.operand_view(), end_view)
                || below_equal_spelling()
                || below_unwrapped_successor())
            && holds(
                CompareRelation::LessEqual,
                end_view,
                MachineOperandView::Legacy(&MachineTerm::uint64_constant(limit)),
            )
    }

    /// Check an access in the range's declared index domain.
    pub(in crate::kernel) fn pointer_access_in_memory_range(
        &self,
        pointer: &Pointer,
        bytes: u32,
        range: &MemoryRange,
    ) -> bool {
        match range.int32_bounds() {
            Some((start, end)) => self.pointer_access_in_range(
                pointer,
                bytes,
                range.base(),
                start,
                end,
                range.element_width(),
            ),
            None => self.pointer_access_in_wide_range(pointer, bytes, range),
        }
    }

    /// Coverage of a complete pointer's opaque domain. Numeric address
    /// classes select candidates; only full extent identity admits evidence.
    pub(in crate::kernel) fn opaque_pointer_covers(
        &self,
        value: &PointerValue,
        position: &Pointer,
        bytes: u32,
    ) -> bool {
        let Some(origin) = value.opaque_extent() else {
            return false;
        };
        self.equality_graph
            .subobject_coverage_facts(origin)
            .iter()
            .any(|fact| {
                let Proposition::Predicate { arguments, .. } = fact else {
                    return false;
                };
                let Some(Term::ProgramValue(ProgramValue::Pointer(source))) = arguments.first()
                else {
                    return false;
                };
                if !self.opaque_extents_equal(origin, source.pointer()) {
                    return false;
                }
                let covered = if let Some(range) = SubobjectExtent::covered_wide_range(fact) {
                    let contains = |pointer| {
                        crate::kernel::primitives::pointer_formation_in_range(
                            pointer,
                            value.pointer(),
                            &range,
                            self,
                        )
                    };
                    contains(position) && (bytes == 0 || contains(&position.offset_by_bytes(bytes)))
                } else {
                    SubobjectExtent::covered_range(fact).is_some_and(|(from, count, width)| {
                        let contains = |position: &Pointer, bytes| {
                            self.pointer_access_in_range(
                                position,
                                bytes,
                                &from,
                                &MachineTerm::constant(0),
                                &count,
                                width,
                            )
                        };
                        contains(position, bytes)
                            && (bytes > 0
                                || contains(value.pointer(), 0)
                                || contains(position, 1)
                                || self.decide(&ConditionTerm::signed_less_than(
                                    MachineTerm::constant(0),
                                    count,
                                )) == Some(true))
                    })
                };
                if covered {
                    record_reasoning_provenance(self, fact);
                }
                covered
            })
    }

    pub(in crate::kernel) fn pointer_access_in_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        base: &Pointer,
        start: &MachineTerm,
        end: &MachineTerm,
        element_width: u32,
    ) -> bool {
        // An owned range keeps its own base spelling. Once the trusted graph
        // proves the access names that base, use that spelling for the range
        // check; a late or transitive equality needs no alias walk. This
        // changes address matching only: the range still supplies authority
        // and its bounds still decide whether the access is covered.
        let resolved = if pointer == base || self.pointers_known_equal(pointer, base) {
            base.clone()
        } else {
            self.equality_graph
                .pointer_at_base(pointer, base)
                .unwrap_or_else(|| pointer.clone())
        };
        let pointer = &resolved;
        if byte_width > 0 && byte_width < element_width {
            let available = MemoryRange::new_with_element_width(
                base.clone(),
                start.clone(),
                end.clone(),
                element_width,
            );
            let required = MemoryRange::new_with_element_width(
                pointer.clone(),
                0u32.into(),
                byte_width.into(),
                1,
            );
            if crate::kernel::primitives::memory_range_covers_interior_element(
                &available, &required, self,
            ) && !self
                .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    &available, &required,
                )
            {
                return true;
            }
        }
        let proves_order =
            |left: MachineOperandView<'_>, right: MachineOperandView<'_>, strict: bool| {
                let condition = if strict {
                    index_comparison(CompareRelation::LessThan, left, right)
                } else {
                    index_comparison(CompareRelation::LessEqual, left, right)
                };
                self.selected_comparison_value(&condition) == Some(true)
                    || self.decide_from_variable_chain(&condition) == Some(true)
                    || crate::instrumentation::measure_operation(
                        "kernel",
                        "resource read",
                        "resource read: exact order path",
                        || self.has_exact_order_path_views(left, right, strict),
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
            && let Some(index) =
                pointer.shared_element_index_from_base_with_width(base, element_width)
            && let Some(logical_access_length) = if byte_width == 0 {
                Some(0)
            } else {
                authorized_access_element_length(byte_width, element_width)
            }
        {
            let access_length = MachineTerm::constant(logical_access_length);
            let access_end = index_binary(
                MachineBinaryOp::Add,
                index.operand_view(),
                MachineOperandView::Legacy(&access_length),
            );
            let exact_within_range = match (
                super::exact_signed_constant_view(index.operand_view(), self),
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
                    proves_order(
                        MachineOperandView::Legacy(start),
                        index.operand_view(),
                        false,
                    ) && proves_order(index.operand_view(), MachineOperandView::Legacy(end), true)
                } else {
                    proves_order(
                        MachineOperandView::Legacy(start),
                        index.operand_view(),
                        false,
                    ) && proves_order(
                        access_end.operand_view(),
                        MachineOperandView::Legacy(end),
                        false,
                    )
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
        let range_bytes = MachineTerm::multiply(
            MachineTerm::subtract(end.clone(), start.clone()),
            MachineTerm::constant(element_width),
        );
        if let Some(byte_offset) = shared_pointer_byte_offset_from_base(pointer, &range_base) {
            let access_end = index_binary(
                MachineBinaryOp::Add,
                byte_offset.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::constant(byte_width)),
            );
            if self.decide(&index_comparison(
                CompareRelation::GreaterEqual,
                byte_offset.operand_view(),
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
            )) == Some(true)
                && self.decide(&index_comparison(
                    CompareRelation::LessEqual,
                    access_end.operand_view(),
                    MachineOperandView::Legacy(&range_bytes),
                )) == Some(true)
            {
                return true;
            }
        }
        // The same footprint holding a struct-array element's field: the
        // element index and the field are bounded separately.
        if self.proves_cell_within_strided_region(
            &range_base,
            &range_bytes,
            pointer,
            byte_width,
            &proves_order,
        ) {
            return true;
        }

        if element_width > 0 && byte_width.is_multiple_of(element_width) {
            let range_base = base.offset_by_elements(start.clone(), element_width);
            let access_length = MachineTerm::constant(byte_width / element_width);
            if pointer == &range_base
                && end == &MachineTerm::add(start.clone(), access_length.clone())
            {
                return true;
            }
            if let Some(index) =
                self.pointer_element_index_from_base_with_width(pointer, &range_base, element_width)
            {
                let range_length = MachineTerm::subtract(end.clone(), start.clone());
                let access_end = index_binary(
                    MachineBinaryOp::Add,
                    index.operand_view(),
                    MachineOperandView::Legacy(&access_length),
                );
                if self.decide(&index_comparison(
                    CompareRelation::LessEqual,
                    MachineOperandView::Legacy(&MachineTerm::constant(0)),
                    index.operand_view(),
                )) == Some(true)
                    && self.decide(&index_comparison(
                        CompareRelation::LessEqual,
                        access_end.operand_view(),
                        MachineOperandView::Legacy(&range_length),
                    )) == Some(true)
                {
                    return true;
                }
            }
        }

        if byte_width == 1 && element_width == 1 {
            let Some(index) = shared_pointer_byte_offset_from_base(pointer, base) else {
                return false;
            };
            return self.decide(&index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(start),
                index.operand_view(),
            )) == Some(true)
                && self.decide(&index_comparison(
                    CompareRelation::LessThan,
                    index.operand_view(),
                    MachineOperandView::Legacy(&end),
                )) == Some(true);
        }

        false
    }

    pub(in crate::kernel) fn ranges_proven_disjoint_from_pointer(
        &self,
        ranges: &[MemoryRange],
        pointer: &Pointer,
    ) -> bool {
        // A range the pointer is decided to lie in is never separate from
        // it; find one before any range's separation search runs, since
        // `all` would otherwise search the ranges ahead of it first.
        !self.pointer_overlaps_one_of_ranges(ranges, pointer)
            && ranges
                .iter()
                .all(|range| self.range_proven_disjoint_from_pointer(range, pointer))
    }

    /// Whether the pointer is decided to lie inside one of `ranges` by the
    /// cheap overlap rules of [`Self::pointer_overlaps_range_after_path_equality`].
    /// Linear in the ranges, with no separation search.
    fn pointer_overlaps_one_of_ranges(&self, ranges: &[MemoryRange], pointer: &Pointer) -> bool {
        ranges.iter().any(|range| {
            !range.base.blocks_proven_distinct(pointer)
                && self.pointer_overlaps_range_after_path_equality(pointer, range)
        })
    }

    pub(in crate::kernel) fn ranges_directly_disjoint_from_pointer(
        &self,
        ranges: &[MemoryRange],
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
        ranges: &[MemoryRange],
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        ranges.iter().all(|range| {
            if range.base.blocks_proven_distinct(pointer) {
                return true;
            }
            if range.wide_bounds().is_some() {
                return self.pointer_access_outside_wide_range(pointer, byte_width, range);
            }
            if pointer_in_memory_range_shallow_with_facts(pointer, range, self) {
                return false;
            }
            // The owners are in the range's and the pointer's blocks, the
            // keys a composition holding both is listed under
            // (`CompositionMemberIndex`).
            if self
                .composition_members
                .listed_under([], [&range.base().block, &pointer.block])
                .into_iter()
                .any(|resources| {
                    resources.proves_owned_range_separate_from_pointer_shallow(
                        range,
                        pointer,
                        self,
                        |pointer, available| {
                            (available.wide_bounds().is_none()
                                && self.pointer_in_range_by_shallow_fact_graph_with_width(
                                    pointer,
                                    available.base(),
                                    available.start(),
                                    available.end(),
                                    available.element_width(),
                                ))
                                || self.pointer_directly_in_memory_range(pointer, available)
                        },
                    )
                })
            {
                return true;
            }
            let direct_index = self.direct_pointer_element_index_from_base_with_width(
                pointer,
                &range.base,
                range.element_width(),
            );
            if let Some(index) = direct_index.as_ref()
                && let (Some(index), Some(start), Some(end)) = (
                    signed_index_constant(index.operand_view()),
                    signed_bitvector_constant(range.start()),
                    signed_bitvector_constant(range.end()),
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
            // `range` is narrow here. Each certificate shape has a shallow
            // side in its block or `pointer`'s, or a direct side in a block of
            // `pointer`'s class (`pointer_in_block`).
            let mut blocks = self.equality_graph.pointer_class_blocks(&pointer.block);
            blocks.push(range.base().block.clone());
            blocks.push(pointer.block.clone());
            let candidates = self.memory_separations_near(blocks.iter(), [range.base(), pointer]);
            if let Some(proposition) = candidates.into_iter().find(|proposition| match proposition
                .memory_separation()
            {
                Some((left_range, right_range)) => {
                    (memory_range_shallowly_contained_with_facts(range, left_range, self)
                        && (pointer_in_memory_range_shallow_with_facts(pointer, right_range, self)
                            || self.pointer_directly_in_memory_range(pointer, right_range))
                        || memory_range_shallowly_contained_with_facts(range, right_range, self)
                            && (pointer_in_memory_range_shallow_with_facts(
                                pointer, left_range, self,
                            ) || self.pointer_directly_in_memory_range(pointer, left_range))
                        || pointer_in_memory_range_shallow_with_facts(pointer, left_range, self)
                            && memory_range_contained_for_memory_resolution(
                                range,
                                right_range,
                                self,
                            )
                        || pointer_in_memory_range_shallow_with_facts(pointer, right_range, self)
                            && memory_range_contained_for_memory_resolution(
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
                            ))
                        && !self.memory_ranges_overlap_after_base_equality(left_range, right_range)
                }
                _ => false,
            }) {
                record_implicit_reasoning_provenance(self, proposition);
                return true;
            }

            let Some(index) = direct_index else {
                return false;
            };
            bitvector_index_outside_range_shallow_view(
                index.operand_view(),
                range.start(),
                range.end(),
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
            ) => {
                left_width == right_width
                    && self
                        .equality_graph
                        .are_int32_equal_views(left.operand_view(), right.operand_view())
            }
            _ => false,
        }
    }

    fn direct_pointer_element_index_from_base_with_width(
        &self,
        pointer: &Pointer,
        base: &Pointer,
        element_width: u32,
    ) -> Option<SharedMachineIntegerTerm> {
        let pointer = &self.pointer_in_block(pointer, &base.block)?;
        if self.pointer_offsets_equal_from_facts(&pointer.offset, &base.offset) {
            return Some(
                MachineOperandView::Legacy(&MachineTerm::constant(0))
                    .retain(MachineIntegerType::Int32),
            );
        }
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            if self.pointer_offsets_equal_from_facts(left, &base.offset) {
                return shared_element_index_from_offset(right, element_width);
            }
            if self.pointer_offsets_equal_from_facts(right, &base.offset) {
                return shared_element_index_from_offset(left, element_width);
            }
        }
        pointer.shared_element_index_from_base_with_width(base, element_width)
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
        let pointer = &self.pointer_in_block(pointer, &base.block)?;
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

    fn pointer_directly_in_memory_range(&self, pointer: &Pointer, range: &MemoryRange) -> bool {
        // A wide range has its one membership rule.
        if range.wide_bounds().is_some() {
            return self.pointer_access_in_wide_range(pointer, range.element_width(), range);
        }
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
                range.start(),
                range.end(),
                self,
            );
        };
        if let (Some(index), Some(start), Some(end)) = (
            super::exact_signed_constant_view(index.operand_view(), self),
            signed_bitvector_constant(range.start()),
            signed_bitvector_constant(range.end()),
        ) {
            return start <= index && index < end;
        }
        bitvector_index_in_range_shallow_views(
            index.operand_view(),
            MachineOperandView::Legacy(range.start()),
            MachineOperandView::Legacy(range.end()),
            self,
        )
    }

    /// The armed compositions with their composites definitionally expanded,
    /// for frame evidence only.
    ///
    /// Expansion is definitional and runs against no assumptions, so it
    /// cannot re-enter the prover that called it, and its result is a pure
    /// function of the composition and the armed definitions — memoized per
    /// thread. Composite bodies are evaluated over an empty state: the
    /// segments this answers for are the ones whose addresses do not depend
    /// on field values, and a body that needs a live state simply does
    /// not expand here.
    fn range_proven_disjoint_from_pointer(&self, range: &MemoryRange, pointer: &Pointer) -> bool {
        if range.base.blocks_proven_distinct(pointer) {
            return true;
        }
        if range.wide_bounds().is_some() {
            return self.pointer_access_outside_wide_range(
                pointer,
                access_byte_width_for_separation(pointer),
                range,
            );
        }
        if self.pointer_overlaps_range_after_path_equality(pointer, range) {
            return false;
        }
        if self
            .borrow_partition_separated_members(
                range.base(),
                pointer,
                |available| memory_range_shallowly_contained_with_facts(range, available, self),
                |available| self.pointer_directly_in_memory_range(pointer, available),
            )
            .is_some()
        {
            return true;
        }
        let owned_member_holds_pointer = |resources: &ResourceContext| {
            resources.proves_owned_range_separate_from_pointer_shallow(
                range,
                pointer,
                self,
                |pointer, available| {
                    (available.wide_bounds().is_none()
                        && self.pointer_in_range_by_shallow_fact_graph_with_width(
                            pointer,
                            available.base(),
                            available.start(),
                            available.end(),
                            available.element_width(),
                        ))
                        || self.pointer_directly_in_memory_range(pointer, available)
                },
            )
        };
        if self
            .composition_members
            .listed_under([], [&range.base().block, &pointer.block])
            .into_iter()
            .any(owned_member_holds_pointer)
        {
            return true;
        }
        // `range` is narrow here, and both certificate shapes contain it
        // shallowly in one side, so that side is in its block.
        let candidates =
            self.memory_separations_near([&range.base().block], [range.base(), pointer]);
        if let Some(proposition) =
            candidates
                .into_iter()
                .find(|proposition| match proposition.memory_separation() {
                    Some((left_range, right_range)) => {
                        (memory_range_shallowly_contained_with_facts(range, left_range, self)
                            && pointer_in_memory_range_shallow_with_facts(
                                pointer,
                                right_range,
                                self,
                            )
                            || memory_range_shallowly_contained_with_facts(
                                range,
                                right_range,
                                self,
                            ) && pointer_in_memory_range_shallow_with_facts(
                                pointer, left_range, self,
                            ))
                            && !self
                                .memory_ranges_overlap_after_base_equality(left_range, right_range)
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
            // equality facts with per-load state bridging, so a range
            // like data[split..split+1] with split provably 1 proves
            // disjoint from data[0].
            let resolve = |term: MachineOperandView<'_>| {
                signed_index_constant(term)
                    .or_else(|| self.known_signed_constant_after_normalization_view(term))
            };
            let byte_width = access_byte_width_for_separation(pointer);
            if let (Some(index), Some(start), Some(end)) = (
                resolve(index.operand_view()),
                resolve(MachineOperandView::Legacy(range.start())),
                resolve(MachineOperandView::Legacy(range.end())),
            ) && Self::constant_access_outside_range(
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
                && self.decide(&index_comparison(
                    CompareRelation::LessThan,
                    index.operand_view(),
                    MachineOperandView::Legacy(&range.start()),
                )) == Some(true)
                || self.decide(&index_comparison(
                    CompareRelation::LessEqual,
                    MachineOperandView::Legacy(&range.end()),
                    index.operand_view(),
                )) == Some(true)
            {
                return true;
            }
        }
        let pointer_range = MemoryRange::new(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
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
                shared_element_index_from_offset(right, range.element_width())
            } else if self.decide(&ConditionTerm::pointer_offset_equal(
                pointer.offset.clone(),
                right.as_ref().clone(),
            )) == Some(true)
            {
                shared_element_index_from_offset(left, range.element_width())
            } else {
                None
            };
            if let Some(forward_offset) = forward_offset {
                let range_start = index_binary(
                    MachineBinaryOp::Add,
                    forward_offset.operand_view(),
                    MachineOperandView::Legacy(&range.start()),
                );
                if self.decide(&index_comparison(
                    CompareRelation::LessThan,
                    MachineOperandView::Legacy(&MachineTerm::constant(0)),
                    range_start.operand_view(),
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
        range: &MemoryRange,
        base: &Pointer,
        start: &MachineTerm,
        end: &MachineTerm,
    ) -> bool {
        if range.wide_bounds().is_some() {
            let available = MemoryRange::new_with_element_width(
                base.clone(),
                start.clone(),
                end.clone(),
                range.element_width(),
            );
            return crate::kernel::primitives::wide_memory_range_covers(&available, range, self);
        }
        if &range.base == base {
            let same_base_timing = crate::instrumentation::OperationTiming::new(
                "kernel",
                "fact range coverage",
                "fact range coverage: exact base",
            );
            let base_delta =
                MachineOperandView::Legacy(&relative_range_offset(range.start(), start))
                    .retain(MachineIntegerType::Int32);
            let range_length = MachineTerm::subtract(range.end().clone(), range.start().clone());
            let fact_length = MachineTerm::subtract(end.clone(), start.clone());
            let end_is_covered = if range_length == MachineTerm::constant(1) {
                self.decide(&index_comparison(
                    CompareRelation::LessThan,
                    base_delta.operand_view(),
                    MachineOperandView::Legacy(&fact_length),
                )) == Some(true)
            } else {
                let range_end = index_binary(
                    MachineBinaryOp::Add,
                    base_delta.operand_view(),
                    MachineOperandView::Legacy(&range_length),
                );
                self.decide(&index_comparison(
                    CompareRelation::LessEqual,
                    range_end.operand_view(),
                    MachineOperandView::Legacy(&fact_length),
                )) == Some(true)
            };
            if self.decide(&index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(&MachineTerm::constant(0)),
                base_delta.operand_view(),
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
            .offset_by_elements(range.start().clone(), range.element_width());
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
            let range_length = MachineTerm::subtract(range.end().clone(), range.start().clone());
            let fact_length = MachineTerm::subtract(end.clone(), start.clone());
            let range_end = index_binary(
                MachineBinaryOp::Add,
                base_delta.operand_view(),
                MachineOperandView::Legacy(&range_length),
            );
            if crate::instrumentation::measure_operation(
                "kernel",
                "fact range coverage",
                "fact range coverage: shifted bounds",
                || {
                    self.decide(&index_comparison(
                        CompareRelation::LessEqual,
                        MachineOperandView::Legacy(&MachineTerm::constant(0)),
                        base_delta.operand_view(),
                    )) == Some(true)
                        && self.decide(&index_comparison(
                            CompareRelation::LessEqual,
                            range_end.operand_view(),
                            MachineOperandView::Legacy(&fact_length),
                        )) == Some(true)
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
        let range_start = index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Legacy(&range.start()),
        );
        let range_end = index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Legacy(&range.end()),
        );

        crate::instrumentation::measure_operation(
            "kernel",
            "fact range coverage",
            "fact range coverage: direct bounds",
            || {
                self.decide(&index_comparison(
                    CompareRelation::LessEqual,
                    MachineOperandView::Legacy(&start),
                    range_start.operand_view(),
                )) == Some(true)
                    && self.decide(&index_comparison(
                        CompareRelation::LessEqual,
                        range_end.operand_view(),
                        MachineOperandView::Legacy(&end),
                    )) == Some(true)
            },
        )
    }
}

/// Current store owners' containing members, or the write keys needed to
/// select historical compositions once the read is known; see
/// [`PureFactContext::owned_store_footprint`].
pub(in crate::kernel) enum OwnedStoreFootprint<'a> {
    Members(OwnedStoreMembers<'a>),
    Indexed {
        spellings: Vec<(Pointer, Pointer)>,
        bytes: u32,
        // Keys are storage identities; the borrowed context keeps all their
        // compositions alive, even cached misses with no member reference.
        members: std::cell::RefCell<BTreeMap<usize, OwnedStoreMembers<'a>>>,
    },
}

type OwnedStoreMembers<'a> = Vec<(&'a ResourceContext, u64, &'a MemoryRange)>;

pub(in crate::kernel) fn parameter_partition_variable(base: &Pointer) -> Option<&Variable> {
    if base.block != crate::kernel::PointerBlock::ExternalArgument {
        return None;
    }
    let variable = match &base.offset {
        PointerOffsetTerm::Variable(variable) => variable,
        PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width > 0 => {
            value.operand_view().variable()?
        }
        _ => return None,
    };
    crate::kernel::registered_load_for_variable(variable)
        .is_none()
        .then_some(variable)
}

pub(in crate::kernel) fn parameter_alias_bucket(pointer: &Pointer) -> Pointer {
    let mut stem = &pointer.offset;
    if pointer.block != crate::kernel::PointerBlock::ExternalArgument {
        return Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
    }
    while let PointerOffsetTerm::Add(left, right) = stem {
        if right.as_const().is_none() {
            break;
        }
        stem = left;
    }
    Pointer {
        block: pointer.block.clone(),
        offset: stem.clone(),
    }
}

pub(in crate::kernel) fn parameter_partition_root(pointer: &Pointer) -> Option<Pointer> {
    let mut stem = &pointer.offset;
    while let PointerOffsetTerm::Add(left, right) = stem {
        right.as_const()?;
        stem = left;
    }
    let base = Pointer {
        block: pointer.block.clone(),
        offset: stem.clone(),
    };
    parameter_partition_variable(&base)?;
    Some(base)
}

/// The element index of `pointer` from `base` when `pointer` is `base`
/// itself or `base` plus one displacement: the syntactic branches of the
/// proof-aware index, with no offset comparison that could fail slowly.
fn structural_element_index(
    pointer: &Pointer,
    base: &Pointer,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<SharedMachineIntegerTerm> {
    crate::instrumentation::record_deterministic_work(1);
    if pointer.block != base.block {
        return None;
    }
    if pointer.offset == base.offset {
        return Some(
            MachineOperandView::Legacy(&MachineTerm::constant(0)).retain(MachineIntegerType::Int32),
        );
    }
    // From a base at offset zero, such as a loaded pointer's own read or a
    // symbolic pointer, the whole offset is the displacement.
    if base.offset == PointerOffsetTerm::Constant(0) {
        return shared_element_index_from_offset_with_facts(
            &pointer.offset,
            element_width,
            assumptions,
        );
    }
    let PointerOffsetTerm::Add(left, right) = &pointer.offset else {
        return None;
    };
    if left.as_ref() != &base.offset {
        return None;
    }
    shared_element_index_from_offset_with_facts(right, element_width, assumptions)
}

/// The owned instances of `resources` whose C pointer arguments name one of
/// the additive base spellings of `pointer` (see [`additive_base_spellings`]),
/// each once, keyed by entry: the instances whose body a cell at `pointer`
/// could be owned by one layer down, found through the argument index. Cost
/// is the access's spellings and the instances they name, never the
/// context's other instances.
pub(in crate::kernel) fn owned_instances_naming_access_base<'a>(
    resources: &'a ResourceContext,
    pointer: &Pointer,
    found: &mut BTreeMap<u64, &'a ResourceFact>,
) {
    for base in additive_base_spellings(pointer) {
        for (entry, fact) in resources.owned_instances_with_pointer_argument(&base) {
            found.entry(entry).or_insert(fact);
        }
    }
}

/// The bases an owned range could be stated over for an access at `pointer`:
/// the pointer itself and each left operand down its offset's additive spine.
///
/// Pointer arithmetic and member access both build `Add(base, displacement)`
/// (`PointerOffsetTerm::add`), so `p->f` is `Add(p, f)`, `p[i]` is
/// `Add(p, i·w)`, and `p->a[i]` is `Add(Add(p, a), i·w)`: the spine walks back
/// through every one of them. A range stated over a base spelled some other
/// way is simply not found here; the caller then asks its full ladder, so a
/// miss costs time and never a decision. Linear in the offset's size.
pub(in crate::kernel) fn additive_base_spellings(pointer: &Pointer) -> Vec<Pointer> {
    let mut spellings = vec![pointer.clone()];
    let mut offset = &pointer.offset;
    while let PointerOffsetTerm::Add(left, _) = offset {
        crate::instrumentation::record_deterministic_work(1);
        spellings.push(Pointer {
            block: pointer.block.clone(),
            offset: left.as_ref().clone(),
        });
        offset = left;
    }
    // Outside the shared parameter block, a pointer's block at offset zero is
    // the base an access through it extends: a loaded pointer's own read, a
    // symbolic pointer such as a matched arm's binding, an allocation.
    if pointer.block != PointerBlock::ExternalArgument && *offset != PointerOffsetTerm::Constant(0)
    {
        spellings.push(Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        });
    }
    spellings
}

#[cfg(test)]
mod seeded_interval_adjacency_tests {
    use super::*;
    use crate::kernel::primitives::{CellRun, IndexIntervals};

    #[test]
    fn materialized_run_adjacency_rejects_signed_residue_as_unsigned_distance() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: "wide-run-adjacency".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let source = crate::kernel::intern_memory(Memory::new());
        let run = CellRun::new(
            base.clone(),
            1,
            ProgramType::UInt8,
            0x8000_0000,
            source,
            IndexIntervals::default(),
        );
        let mut memory = Memory::new();
        std::sync::Arc::make_mut(&mut memory.cells).add_run(run);
        let wrong = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(-0x8000_0000),
        };
        let memory = memory.store(wrong, crate::kernel::uint8(7));
        let context = PureFactContext::new();
        assert!(
            context
                .adjacent_loadable_region_facts(&memory, &base, &MachineTerm::constant(0x8000_0001))
                .is_none()
        );
        let memory = memory.store(base.offset_by_bytes(0x8000_0000), crate::kernel::uint8(9));
        assert!(
            context
                .adjacent_loadable_region_facts(&memory, &base, &MachineTerm::constant(0x8000_0001))
                .is_some()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/assumptions/memory_reasoning/seeded_interval_adjacency_tests.rs"
        );
        include!(
            "../../scaling_tests/kernel/assumptions/memory_reasoning/explicit_separation_lookup_tests.rs"
        );
    }
}

#[cfg(test)]
mod nonnegative_successor_tests {
    use super::*;

    /// The successor rule's `term < _` fact is read from the order facts
    /// filed under `term`'s canonical form (`OrderFactsByLower`); it once
    /// scanned every condition fact, so a miss grew with unrelated facts.
    #[test]
    fn successor_rule_ignores_unrelated_condition_facts() {
        let term = MachineTerm::Variable(Variable(96_000));
        let goal = ConditionTerm::signed_less_equal(
            MachineTerm::constant(0),
            MachineTerm::add(term.clone(), MachineTerm::constant(1)),
        );
        let work = [16_u64, 64, 256]
            .into_iter()
            .map(|unrelated| {
                let mut context = PureFactContext::new().assume_condition(
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), term.clone()),
                    true,
                );
                for index in 0..unrelated {
                    context = context.assume_condition(
                        ConditionTerm::signed_less_than(
                            MachineTerm::Variable(Variable(96_100 + index)),
                            MachineTerm::Variable(Variable(96_600 + index)),
                        ),
                        true,
                    );
                }
                let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                    context.nonnegative_successor_by_exact_facts(&goal)
                });
                assert!(!proved, "no fact bounds the term above");
                work
            })
            .collect::<Vec<_>>();
        assert!(
            work.windows(2).all(|pair| pair[0] == pair[1]),
            "unrelated facts changed the successor rule's work: {work:?}"
        );
    }
}

#[cfg(test)]
mod shallow_composition_separation_tests {
    use super::*;

    fn owner_of(pointers: &[Pointer]) -> Proposition {
        Proposition::ResourceComposition(ResourceContext::new().unchecked_with_facts(
            pointers.iter().map(|pointer| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    pointer.clone(),
                    0u32.into(),
                    1u32.into(),
                    4,
                ))
            }),
        ))
    }

    fn at(block: &str) -> Pointer {
        Pointer {
            block: block.into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    /// Two pointers owned as distinct members of one composition are
    /// disjoint. The shallow check reads the compositions listed under the
    /// two pointers' blocks (`CompositionMemberIndex`); it once asked every
    /// composition the path had stated.
    #[test]
    fn shallow_owned_separation_ignores_unrelated_compositions() {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let (left, right) = (at("shallow-left"), at("shallow-right"));
            // The first composition is the index's unlisted root; keep the
            // pair out of it.
            let facts = (0..size)
                .fold(PureFactContext::new(), |facts, index| {
                    facts.assume_proposition(owner_of(&[at(&format!("shallow-other-{index}"))]))
                })
                .assume_proposition(owner_of(&[left.clone(), right.clone()]));
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.pointers_proven_disjoint_by_shallow_explicit_range(&left, &right)
            });
            assert!(separate);
            samples.push((size, work));
        }
        let (_, smallest) = samples[0];
        assert!(
            samples.iter().all(|(_, work)| *work <= smallest + 4),
            "shallow owned separation grew with unrelated compositions: {samples:?}"
        );
    }
    /// A pointer's own block, which may alias any other pointer's.
    fn symbolic(variable: u64) -> Pointer {
        Pointer {
            block: PointerBlock::Symbolic(crate::kernel::Variable(variable)),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn cells(variable: u64) -> MemoryRange {
        MemoryRange::new_with_element_width(symbolic(variable), 0u32.into(), 1u32.into(), 4)
    }

    fn separate(left: u64, right: u64) -> Proposition {
        Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(cells(left))),
            right: Box::new(Resource::Memory(cells(right))),
        }
    }

    /// A range is separate from another when a composition's owned members
    /// in its block cover it apart from the other's owner. The cover reads
    /// the compositions listed under the two ranges' blocks
    /// (`CompositionMemberIndex`); it once asked every stated composition.
    #[test]
    fn composition_cover_ignores_unrelated_compositions() {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            // The first composition is the index's unlisted root.
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(owner_of(&[at(&format!("cover-other-{index}"))]))
            });
            let (left, right) = (cells(9_200), cells(9_201));
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.proves_resource_separate(
                    &Resource::Memory(left.clone()),
                    &Resource::Memory(right.clone()),
                )
            });
            assert!(!separate);
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "the composition cover grew with unrelated compositions: {samples:?}"
        );
    }

    /// The cover also finds an owner of the other range that contains it
    /// only through a containment fact with a non-memory parent, as
    /// composite expansion states for every opened composite. It walks the
    /// containment facts upward from the other range's block
    /// (`memory_containers`); while any such fact was stated it once asked
    /// every stated composition.
    #[test]
    fn composition_cover_with_a_token_container_ignores_unrelated_compositions() {
        let holder = token("cover-holder");
        let contains = Proposition::ResourceContains {
            parent: Box::new(holder.clone()),
            child: Box::new(Resource::Memory(cells(9_211))),
        };
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = (0..size).fold(
                PureFactContext::new().assume_proposition(contains.clone()),
                |facts, index| {
                    facts.assume_proposition(owner_of(&[at(&format!("cover-token-other-{index}"))]))
                },
            );
            let (left, right) = (
                Resource::Memory(cells(9_210)),
                Resource::Memory(cells(9_211)),
            );
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.proves_resource_separate(&left, &right)
            });
            assert!(!separate);
            let held = facts.assume_proposition(Proposition::ResourceComposition(
                ResourceContext::new().unchecked_with_facts([
                    ResourceFact::own_memory(cells(9_210)),
                    ResourceFact::own(holder.clone()),
                ]),
            ));
            assert!(held.proves_resource_separate(&left, &right));
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "the composition cover grew with unrelated compositions: {samples:?}"
        );
    }

    /// Two ranges are separate as distinct owned members of one composition,
    /// found through their bases' related roots. The check reads the
    /// compositions listed under those roots' blocks; it once asked every
    /// stated composition.
    #[test]
    fn owned_range_separation_ignores_unrelated_compositions() {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(owner_of(&[at(&format!("owned-other-{index}"))]))
            });
            let (left, right) = (cells(9_300), cells(9_301));
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.composition_separates_owned_ranges(&left, &right)
            });
            assert!(!separate);
            let held = facts.assume_proposition(owner_of(&[symbolic(9_300), symbolic(9_301)]));
            assert!(held.composition_separates_owned_ranges(&left, &right));
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "owned range separation grew with unrelated compositions: {samples:?}"
        );
    }

    fn token(name: &str) -> Resource {
        Resource::Token {
            name: name.into(),
            arguments: Vec::new().into(),
        }
    }

    fn separate_resources(left: Resource, right: Resource) -> Proposition {
        Proposition::ResourceSeparate {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// A non-memory resource is separate from another when a stated
    /// separation's sides contain the two. The check reads the separations
    /// filed under the resource's containers, walked upward through the
    /// containment facts (`separations_with_side_containing`); it once
    /// scanned every stated separation.
    #[test]
    fn token_separation_ignores_unrelated_separations() {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(separate_resources(
                    token(&format!("apart-left-{index}")),
                    token(&format!("apart-right-{index}")),
                ))
            });
            let (left, right) = (token("apart-query-left"), token("apart-query-right"));
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.proves_resource_separate(&left, &right)
            });
            assert!(!separate);
            // A container of the left token, separate from the right one.
            let held = facts
                .assume_proposition(Proposition::ResourceContains {
                    parent: Box::new(token("apart-container")),
                    child: Box::new(left.clone()),
                })
                .assume_proposition(separate_resources(token("apart-container"), right.clone()));
            assert!(held.proves_resource_separate(&left, &right));
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "token separation grew with unrelated separations: {samples:?}"
        );
    }

    /// Two tokens are separate as distinct owned members of one composition.
    /// The check reads the compositions listed under the tokens' member keys
    /// (`OwnedMemberKey`); it once asked every stated composition.
    #[test]
    fn token_ownership_ignores_unrelated_compositions() {
        let owning =
            |tokens: &[Resource]| {
                Proposition::ResourceComposition(ResourceContext::new().unchecked_with_facts(
                    tokens.iter().map(|token| ResourceFact::own(token.clone())),
                ))
            };
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(owning(&[token(&format!("owned-token-{index}"))]))
            });
            let (left, right) = (token("owned-query-left"), token("owned-query-right"));
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.proves_resource_separate(&left, &right)
            });
            assert!(!separate);
            let held = facts.assume_proposition(owning(&[left.clone(), right.clone()]));
            assert!(held.proves_resource_separate(&left, &right));
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "token ownership grew with unrelated compositions: {samples:?}"
        );
    }

    /// Two `boxed(p)` composites at distinct pointers are separate as
    /// distinct owned members of one composition. The check reads the
    /// compositions listed under the two pointers' roots, not every
    /// composition owning a `boxed` (`OwnedMemberKey::ShapeRoot`): all of
    /// those share the composite's name and arity.
    #[test]
    fn composite_ownership_ignores_compositions_of_other_roots() {
        let boxed = |variable: u64| Resource::Composite {
            name: "boxed".into(),
            arguments: vec![crate::kernel::AlgebraicValue::Program(
                crate::kernel::ProgramValue::Pointer(crate::kernel::PointerValue::new(
                    symbolic(variable),
                    crate::kernel::ProgramType::Int32Pointer,
                )),
            )]
            .into(),
        };
        let owning = |members: &[Resource]| {
            Proposition::ResourceComposition(
                ResourceContext::new().unchecked_with_facts(
                    members
                        .iter()
                        .map(|member| ResourceFact::own(member.clone())),
                ),
            )
        };
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(owning(&[boxed(9_400 + index)]))
            });
            let (left, right) = (boxed(9_300), boxed(9_301));
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.proves_resource_separate(&left, &right)
            });
            assert!(!separate);
            let held = facts.assume_proposition(owning(&[left.clone(), right.clone()]));
            assert!(held.proves_resource_separate(&left, &right));
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "composite ownership grew with compositions of other roots: {samples:?}"
        );
    }

    /// A range and a pointer are disjoint by a stated separation whose sides
    /// hold them. The shallow checks read the separations filed under the
    /// range's block and the pointer's class (`memory_separations_near`);
    /// they once scanned every stated separation. Only the access check's
    /// miss is measured: `range_proven_disjoint_from_pointer` goes on to
    /// the memory-resolution range separation, which still scans.
    #[test]
    fn pointer_separation_ignores_unrelated_separations() {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = (0..size).fold(PureFactContext::new(), |facts, index| {
                facts.assume_proposition(separate(9_100 + 2 * index, 9_101 + 2 * index))
            });
            let (range, pointer) = (cells(9_000), symbolic(9_001));
            let (missed, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.ranges_directly_disjoint_from_access(
                    std::slice::from_ref(&range),
                    &pointer,
                    4,
                )
            });
            assert!(!missed);
            let held = facts.assume_proposition(separate(9_000, 9_001));
            assert!(held.range_proven_disjoint_from_pointer(&range, &pointer));
            assert!(held.ranges_directly_disjoint_from_access(
                std::slice::from_ref(&range),
                &pointer,
                4,
            ));
            samples.push((size, work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0].1 == pair[1].1),
            "pointer separation grew with unrelated separations: {samples:?}"
        );
    }
}

#[cfg(test)]
mod wide_separation_index_tests {
    use super::*;

    #[test]
    fn wide_separation_context_preserves_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |id: u64| Pointer::symbolic(Variable(9_993_000 + id));
        let wide = |base| {
            MemoryRange::new_wide(
                base,
                MachineTerm::uint64_constant(0),
                MachineTerm::uint64_constant(8),
                4,
            )
        };
        let left = wide(pointer(0));
        let right = wide(pointer(1));
        let fact = Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(left.clone())),
            right: Box::new(Resource::Memory(right.clone())),
        };
        let parent = PureFactContext::new().assume_proposition(fact);
        let separate = |context: &PureFactContext| {
            context.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                &left, &right,
            )
        };
        assert!(separate(&parent));
        assert!(!separate(&PureFactContext::new()));
    }
}

#[cfg(test)]
mod written_store_base_scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/assumptions/memory_reasoning/written_store_bases.rs");
}

impl PureFactContext {
    fn byte_operands_equal(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        let left = self.simplify_machine_operand_under_assumptions(left, MachineIntegerType::Int32);
        let right =
            self.simplify_machine_operand_under_assumptions(right, MachineIntegerType::Int32);
        self.decide(&index_comparison(
            CompareRelation::Equal,
            left.operand_view(),
            right.operand_view(),
        )) == Some(true)
            || crate::kernel::reasoning::int32_operand_values_equal_for_memory_resolution(
                left.operand_view(),
                right.operand_view(),
                self,
            )
    }
}

#[cfg(test)]
mod shared_range_index_tests {
    use super::*;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, VerificationSession};

    fn retained_index() -> SharedMachineIntegerTerm {
        let x = KernelTerm::variable(
            KernelType::Program(MachineIntegerType::Int32.program_type()),
            Variable(1018301),
        );
        let one =
            MachineOperandView::Legacy(&MachineTerm::constant(1)).retain(MachineIntegerType::Int32);
        MachineOperandView::Shared(&KernelTerm::machine_binary_shared(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            [
                x,
                KernelTerm::retained_machine_operand(MachineIntegerType::Int32, one.operand_view()),
            ],
        ))
        .retain(MachineIntegerType::Int32)
    }

    #[test]
    fn shared_wide_coordinates_require_full_width_bounds() {
        let _session = VerificationSession::enter();
        let wide = MachineTerm::Variable(Variable(1018320));
        let narrow = MachineTerm::add(
            MachineTerm::uint32_from_64(wide.clone()),
            MachineTerm::constant(1),
        );
        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &narrow);
        let empty = PureFactContext::new();
        let bounded = empty.clone().assume_condition(
            ConditionTerm::uint64_less_equal(
                wide.clone(),
                MachineTerm::uint64_constant(i32::MAX as u64 - 1),
            ),
            true,
        );
        let truncated = empty.clone().assume_condition(
            ConditionTerm::unsigned_less_equal(
                MachineTerm::uint32_from_64(wide.clone()),
                MachineTerm::constant(i32::MAX as u32 - 1),
            ),
            true,
        );
        let exports = KernelTermExport::machine_export_count();
        assert!(
            crate::kernel::primitives::checked_shared_native_range_endpoint(
                MachineOperandView::Shared(&root),
                &empty
            )
            .is_none()
        );
        assert!(
            crate::kernel::primitives::checked_shared_native_range_endpoint(
                MachineOperandView::Shared(&root),
                &truncated
            )
            .is_none()
        );
        let result = crate::kernel::primitives::checked_shared_native_range_endpoint(
            MachineOperandView::Shared(&root),
            &bounded,
        )
        .unwrap();
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(
            result.structural_value(),
            &MachineTerm::uint64_add(wide, MachineTerm::uint64_constant(1))
        );
    }

    #[test]
    fn retained_strided_fields_need_both_index_bounds_without_export() {
        let _session = VerificationSession::enter();
        let index = retained_index();
        let base = Pointer {
            block: "retained_strided_fields".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pointer = base
            .offset_by_shared_elements(index.clone(), 16)
            .offset_by_bytes(4);
        let low = index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&MachineTerm::constant(0)),
            index.operand_view(),
        );
        let high = index_comparison(
            CompareRelation::LessThan,
            index.operand_view(),
            MachineOperandView::Legacy(&MachineTerm::constant(8)),
        );
        let empty = PureFactContext::new();
        let lower = empty.clone().assume_condition(low, true);
        let both = lower.clone().assume_condition(high, true);
        let exports = KernelTermExport::machine_export_count();
        for (facts, expected) in [(&empty, false), (&lower, false), (&both, true)] {
            assert_eq!(
                facts.proves_cell_within_strided_region(
                    &base,
                    &MachineTerm::constant(128),
                    &pointer,
                    4,
                    &|a, b, strict| {
                        facts.selected_comparison_value(&index_comparison(
                            if strict {
                                CompareRelation::LessThan
                            } else {
                                CompareRelation::LessEqual
                            },
                            a,
                            b,
                        )) == Some(true)
                    }
                ),
                expected
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_range_indices_require_the_selected_bounds_without_exports() {
        let _session = VerificationSession::enter();
        let index = retained_index();
        let base = Pointer {
            block: "shared_range".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pointer = base.offset_by_shared_elements(index.clone(), 4);
        let zero = MachineTerm::constant(0);
        let end = MachineTerm::constant(8);
        let range = MemoryRange::new(base.clone(), zero.clone(), end.clone());
        let lower = index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&zero),
            index.operand_view(),
        );
        let upper = index_comparison(
            CompareRelation::LessThan,
            index.operand_view(),
            MachineOperandView::Legacy(&end),
        );
        let parent = PureFactContext::new();
        let lower_only = parent.clone().assume_condition(lower.clone(), true);
        let bounded = lower_only.clone().assume_condition(upper.clone(), true);
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(
            pointer
                .exact_element_delta_from_base(&base, 4, None)
                .unwrap()
                .index,
            index
        );
        assert!(bounded.pointer_directly_in_memory_range(&pointer, &range));
        assert!(bounded.pointer_in_range_by_exact_facts(&pointer, &range));
        assert!(bounded.access_within_memory_range(&pointer, 4, &range));
        assert!(!lower_only.pointer_directly_in_memory_range(&pointer, &range));
        assert!(!parent.pointer_directly_in_memory_range(&pointer, &range));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_range_query_accepts_original_native_symbolic_bounds() {
        let _session = VerificationSession::enter();
        let start = MachineTerm::Variable(Variable(1018320));
        let end = MachineTerm::Variable(Variable(1018321));
        let absolute = MachineTerm::add(start.clone(), MachineTerm::Variable(Variable(1018322)));
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(1018323)), 4),
        };
        let pointer = base.offset_by_int32_elements(absolute.clone());
        let range = MemoryRange::new(base.clone(), start.clone(), end.clone());
        let lower = ConditionTerm::signed_less_equal(start.clone(), absolute.clone());
        let upper = ConditionTerm::signed_less_than(absolute, end.clone());
        let lower_only = PureFactContext::new().assume_condition(lower, true);
        let facts = lower_only.clone().assume_condition(upper, true);
        let delta = pointer
            .exact_element_delta_from_base(&base, 4, Some(&facts))
            .unwrap();
        let exports = KernelTermExport::machine_export_count();
        assert!(
            bitvector_index_in_range_shallow_views(
                delta.index.operand_view(),
                MachineOperandView::Legacy(&start),
                MachineOperandView::Legacy(&end),
                &facts
            ),
            "shallow bounds"
        );
        assert!(
            facts.pointer_directly_in_memory_range(&pointer, &range),
            "direct membership"
        );
        assert!(
            facts.pointer_in_range_by_exact_facts(&pointer, &range),
            "exact bounds"
        );
        assert!(
            facts.access_within_memory_range(&pointer, 4, &range),
            "range access"
        );
        assert!(!lower_only.pointer_in_range_by_exact_facts(&pointer, &range));
        assert!(!PureFactContext::new().pointer_in_range_by_exact_facts(&pointer, &range));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_exact_delta_preserves_large_constants_and_wrap_refusals() {
        let _session = VerificationSession::enter();
        let index = retained_index();
        let delta = ExactElementDelta {
            index: index.clone(),
            constant: 1i64 << 32,
        };
        let exports = KernelTermExport::machine_export_count();
        assert!(delta.as_index_term().is_none());
        assert!(!delta.is_constant());
        let zero = MachineTerm::constant(0);
        let end = MachineTerm::constant(8);
        assert!(!element_delta_in_range_by_affine_arithmetic(
            &delta,
            &zero,
            &end,
            &PureFactContext::new()
        ));
        let shifted = index_binary(
            MachineBinaryOp::Add,
            index.operand_view(),
            MachineOperandView::Legacy(&MachineTerm::constant(1)),
        );
        assert_eq!(
            exact_affine_index_difference_views(shifted.operand_view(), index.operand_view(), None),
            None
        );
        let facts = PureFactContext::new().assume_condition(
            index_comparison(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(&zero),
                shifted.operand_view(),
            ),
            true,
        );
        assert_eq!(
            exact_affine_index_difference_views(
                shifted.operand_view(),
                index.operand_view(),
                Some(&facts)
            ),
            Some(1)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[cfg(test)]
    mod scaling_tests {
        use super::*;
        include!(
            "../../scaling_tests/kernel/assumptions/memory_reasoning/shared_range_index_tests.rs"
        );
    }
}
