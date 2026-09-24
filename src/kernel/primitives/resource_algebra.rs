use super::*;

/// A proof-aware composition query in progress on this thread. Bridging a
/// query's snapshot form to a carrier entry can itself ask whether a
/// pointer survived a call havoc, which is served by the same composition,
/// so queries nest. A query met again while it runs is a cycle through the
/// facts and proves nothing on that path, noted as a truncation so the memo
/// layers do not cache the weakened answer; distinct queries nest freely,
/// bounded by the resources the facts connect.
// Every variant asks the same separation question about a different kind of
// operand, so the shared suffix is the meaning rather than redundant naming.
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CompositionQuery {
    ResourcesSeparate(CResource, CResource),
    RangesSeparate(CMemoryRange, CMemoryRange),
    PointersSeparate(Pointer, Pointer),
}

thread_local! {
    static COMPOSITION_QUERIES_IN_PROGRESS: std::cell::RefCell<BTreeSet<CompositionQuery>> =
        const { std::cell::RefCell::new(BTreeSet::new()) };
}

struct ResourceCompositionQueryGuard {
    query: CompositionQuery,
}

impl ResourceCompositionQueryGuard {
    fn enter(query: CompositionQuery) -> Option<Self> {
        let entered = COMPOSITION_QUERIES_IN_PROGRESS
            .with(|queries| queries.borrow_mut().insert(query.clone()));
        if !entered {
            crate::kernel::assumptions::note_incomplete_reasoning();
        }
        // `then`, not `then_some`: a guard built eagerly and discarded on
        // the cycle path would run `drop` and unregister the outer query.
        entered.then(|| Self { query })
    }
}

impl Drop for ResourceCompositionQueryGuard {
    fn drop(&mut self) {
        COMPOSITION_QUERIES_IN_PROGRESS.with(|queries| {
            queries.borrow_mut().remove(&self.query);
        });
    }
}

/// A composition query already in progress refuses re-entry without
/// unregistering the outer query, and distinct queries nest.
#[cfg(test)]
#[test]
fn composition_query_guard_refuses_reentry_and_keeps_the_outer_query() {
    let range = |index: i64| {
        CMemoryRange::new(
            Pointer {
                block: "buffer".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(index as u32),
            Bitvector32Term::Constant(index as u32 + 1),
        )
    };
    let first = CompositionQuery::RangesSeparate(range(0), range(1));
    let second = CompositionQuery::RangesSeparate(range(2), range(3));
    let outer =
        ResourceCompositionQueryGuard::enter(first.clone()).expect("the first query registers");
    assert!(
        ResourceCompositionQueryGuard::enter(first.clone()).is_none(),
        "re-entering the query is a cycle"
    );
    let nested = ResourceCompositionQueryGuard::enter(second);
    assert!(nested.is_some(), "a distinct query nests");
    drop(nested);
    assert!(
        ResourceCompositionQueryGuard::enter(first.clone()).is_none(),
        "the refused re-entry left the outer query registered"
    );
    drop(outer);
    assert!(ResourceCompositionQueryGuard::enter(first).is_some());
}

fn insert_resource_index_entry<K: Ord>(
    index: &PersistentMap<K, ResourceEntryIds>,
    key: K,
    entry: ResourceEntryId,
) -> PersistentMap<K, ResourceEntryIds> {
    let entries = index
        .get(&key)
        .cloned()
        .unwrap_or_default()
        .with_value(entry);
    index.with_inserted(key, entries)
}

fn insert_occurrence_index_entry<K: Ord>(
    index: &PersistentMap<K, ResourceOccurrenceIds>,
    key: K,
    occurrence: ResourceOccurrenceId,
) -> PersistentMap<K, ResourceOccurrenceIds> {
    let entries = index
        .get(&key)
        .cloned()
        .unwrap_or_default()
        .with_value(occurrence);
    index.with_inserted(key, entries)
}

fn remove_occurrence_index_entry<K: Ord + Clone>(
    index: &PersistentMap<K, ResourceOccurrenceIds>,
    key: &K,
    occurrence: ResourceOccurrenceId,
) -> PersistentMap<K, ResourceOccurrenceIds> {
    let Some(entries) = index.get(key) else {
        return index.clone();
    };
    let entries = entries.without_value(&occurrence);
    if entries.is_empty() {
        index.without_key(key)
    } else {
        index.with_inserted(key.clone(), entries)
    }
}

pub(crate) fn memory_interval_nodes(
    range: &CMemoryRange,
) -> Option<Vec<ResourceMemoryIntervalNode>> {
    let (start, end) = concrete_memory_range_bounds(range)?;
    let start = start.checked_sub(i64::from(i32::MIN))?;
    let end = end.checked_sub(i64::from(i32::MIN))?;
    if start < 0 || end <= start || end > (1_i64 << 32) {
        return None;
    }
    let mut nodes = Vec::new();
    let mut cursor = start as u64;
    let end = end as u64;
    while cursor < end {
        let alignment = if cursor == 0 {
            32
        } else {
            cursor.trailing_zeros().min(32)
        };
        let magnitude = 63 - (end - cursor).leading_zeros();
        let level = alignment.min(magnitude).min(32) as u8;
        nodes.push(ResourceMemoryIntervalNode {
            block: range.base().block.clone(),
            level,
            start: ((cursor >> level) << level) as u32,
        });
        cursor += 1_u64 << level;
    }
    Some(nodes)
}

/// Whether a write through this block may land in any object at all, so that a
/// resource footprint stated over another block cannot be shown to miss it.
///
/// This is a *variant* test, not a name test, and it is deliberately coarser
/// than [`PointerBlock::proven_distinct`]: one of these blocks stands for an
/// address the caller chose, and the answer here is spent dropping a resource
/// projection, where being coarse only ever drops more. The three predicates
/// below are the evidence language of the resource tracker's footprint arm
/// (`src/kernel/resource_tracker/step_effect.rs`), which is the only decider
/// that reads them.
pub(in crate::kernel) fn memory_block_may_alias(block: &PointerBlock) -> bool {
    matches!(
        block,
        PointerBlock::ExternalArgument
            | PointerBlock::Symbolic(_)
            | PointerBlock::FunctionSymbolic(_)
    )
}

pub(crate) fn memory_interval_ancestors(
    node: &ResourceMemoryIntervalNode,
) -> Vec<ResourceMemoryIntervalNode> {
    (node.level..=32)
        .map(|level| ResourceMemoryIntervalNode {
            block: node.block.clone(),
            level,
            start: (u64::from(node.start) >> level << level) as u32,
        })
        .collect()
}

/// A range's two endpoints as the signed `int32` numbers they are, present
/// only when both are constant.
///
/// This is the reading every *order* over endpoints takes — the partition
/// check's sort, the `concrete_memory` key its neighbour probes walk — as
/// against `as_const`, which answers the bit pattern and is what an equality
/// or a width scaling wants. The two disagree exactly on the ranges that
/// begin below their base, and those are the ranges a caller reaches with
/// `q = p + 1` or with a clause instantiated at a negative index.
fn signed_range_endpoints(range: &CMemoryRange) -> (Option<i64>, Option<i64>) {
    (
        signed_bitvector_constant(range.start()),
        signed_bitvector_constant(range.end()),
    )
}

fn remove_resource_index_entry<K: Ord + Clone>(
    index: &PersistentMap<K, ResourceEntryIds>,
    key: &K,
    entry: ResourceEntryId,
) -> PersistentMap<K, ResourceEntryIds> {
    let Some(entries) = index.get(key) else {
        return index.clone();
    };
    let entries = entries.without_value(&entry);
    if entries.is_empty() {
        index.without_key(key)
    } else {
        index.with_inserted(key.clone(), entries)
    }
}

impl ResourceContextIndex {
    fn with_inserted(&self, entry: ResourceEntryId, fact: &CResourceFact) -> Self {
        let mut result = self.clone();
        if let CResource::Instance(instance) = fact.resource() {
            result.instances =
                insert_resource_index_entry(&result.instances, instance.identity, entry);
            result.instance_shapes = insert_resource_index_entry(
                &result.instance_shapes,
                (instance.name.clone(), instance.arguments.len()),
                entry,
            );
        }
        result.exact = insert_resource_index_entry(&result.exact, fact.clone(), entry);
        result.by_resource =
            insert_resource_index_entry(&result.by_resource, fact.resource().clone(), entry);
        if let Some(range) = fact.memory_range() {
            let block = range.base().block.clone();
            let mode = fact.is_own();
            result.memory_by_block =
                insert_resource_index_entry(&result.memory_by_block, block.clone(), entry);
            result.memory_by_base =
                insert_resource_index_entry(&result.memory_by_base, range.base().clone(), entry);
            if mode {
                result.owned_memory_by_block = insert_resource_index_entry(
                    &result.owned_memory_by_block,
                    block.clone(),
                    entry,
                );
                if result
                    .owned_memory_by_block
                    .get(&block)
                    .is_some_and(|entries| entries.len() >= 2)
                {
                    result.shared_owned_memory_blocks = result
                        .shared_owned_memory_blocks
                        .with_inserted(block.clone(), ());
                }
            }
            result.memory_starts = insert_resource_index_entry(
                &result.memory_starts,
                (block.clone(), mode, range.start().clone()),
                entry,
            );
            result.memory_ends = insert_resource_index_entry(
                &result.memory_ends,
                (block, mode, range.end().clone()),
                entry,
            );
            if let (Some(start), Some(end)) = signed_range_endpoints(range) {
                let base = (range.base().clone(), mode);
                result.concrete_memory = insert_resource_index_entry(
                    &result.concrete_memory,
                    (base.0.clone(), mode, start, end),
                    entry,
                );
                let count = result
                    .concrete_memory_by_base
                    .get(&base)
                    .copied()
                    .unwrap_or(0)
                    + 1;
                result.concrete_memory_by_base =
                    result.concrete_memory_by_base.with_inserted(base, count);
            }
        } else if let CResource::Composite { name, arguments }
        | CResource::Token { name, arguments } = fact.resource()
        {
            result.exact_shapes = insert_resource_index_entry(
                &result.exact_shapes,
                (fact.family(), name.clone(), arguments.len()),
                entry,
            );
        }
        result
    }

    fn without_entry(&self, entry: ResourceEntryId, fact: &CResourceFact) -> Self {
        let mut result = self.clone();
        if let CResource::Instance(instance) = fact.resource() {
            result.instances =
                remove_resource_index_entry(&result.instances, &instance.identity, entry);
            result.instance_shapes = remove_resource_index_entry(
                &result.instance_shapes,
                &(instance.name.clone(), instance.arguments.len()),
                entry,
            );
        }
        result.exact = remove_resource_index_entry(&result.exact, fact, entry);
        result.by_resource =
            remove_resource_index_entry(&result.by_resource, fact.resource(), entry);
        if let Some(range) = fact.memory_range() {
            let block = range.base().block.clone();
            let mode = fact.is_own();
            result.memory_by_block =
                remove_resource_index_entry(&result.memory_by_block, &block, entry);
            result.memory_by_base =
                remove_resource_index_entry(&result.memory_by_base, range.base(), entry);
            if mode {
                result.owned_memory_by_block =
                    remove_resource_index_entry(&result.owned_memory_by_block, &block, entry);
                if !result
                    .owned_memory_by_block
                    .get(&block)
                    .is_some_and(|entries| entries.len() >= 2)
                {
                    result.shared_owned_memory_blocks =
                        result.shared_owned_memory_blocks.without_key(&block);
                }
            }
            result.memory_starts = remove_resource_index_entry(
                &result.memory_starts,
                &(block.clone(), mode, range.start().clone()),
                entry,
            );
            result.memory_ends = remove_resource_index_entry(
                &result.memory_ends,
                &(block, mode, range.end().clone()),
                entry,
            );
            if let (Some(start), Some(end)) = signed_range_endpoints(range) {
                let base = (range.base().clone(), mode);
                result.concrete_memory = remove_resource_index_entry(
                    &result.concrete_memory,
                    &(base.0.clone(), mode, start, end),
                    entry,
                );
                let count = result
                    .concrete_memory_by_base
                    .get(&base)
                    .copied()
                    .expect("concrete resource index count exists");
                result.concrete_memory_by_base = if count == 1 {
                    result.concrete_memory_by_base.without_key(&base)
                } else {
                    result
                        .concrete_memory_by_base
                        .with_inserted(base, count - 1)
                };
            }
        } else if let CResource::Composite { name, arguments }
        | CResource::Token { name, arguments } = fact.resource()
        {
            result.exact_shapes = remove_resource_index_entry(
                &result.exact_shapes,
                &(fact.family(), name.clone(), arguments.len()),
                entry,
            );
        }
        result
    }
}

/// Whether one recorded step can have written a projection's stated footprint.
///
/// The per-step rule is the resource tracker's, asked about
/// [`crate::kernel::resource_tracker::Resource::Ranges`] for a footprint the
/// kernel could name and
/// [`crate::kernel::resource_tracker::Resource::AnyMemory`] for one it could
/// not, so a new step kind has one answer for a footprint rather than one per
/// caller. A footprint with no memory in it is never touched and is not asked
/// about at all.
/// `evidence` is the caller's, built once per invalidation rather than per
/// step: the footprint arm reads none of it, and constructing an empty context
/// inside this loop would be work the rule does not need.
fn memory_derivation_affects_footprint(
    derivation: &CMemoryDerivation,
    produced: &crate::kernel::SharedCMemory,
    footprint: &ResourceMemoryFootprint,
    evidence: &crate::kernel::resource_tracker::step_effect::Evidence<'_>,
) -> bool {
    use crate::kernel::resource_tracker::{Resource, step_effect};
    let resource = match footprint {
        ResourceMemoryFootprint::Exact(ranges) => Resource::Ranges(ranges),
        ResourceMemoryFootprint::Unknown => Resource::AnyMemory,
        ResourceMemoryFootprint::None => return false,
    };
    !matches!(
        step_effect::affects(derivation, produced, resource, evidence),
        step_effect::StepEffect::Separate(step_effect::Separation::Footprint(_))
    )
}

/// The widest scalar access the kernel performs. `int64`, `uint64`, `double`
/// and every LP64 object pointer are eight bytes; no `CValue` is wider, so a
/// caller that cannot name its own access width may stand in this one and
/// still bound the bytes touched.
pub(in crate::kernel) const MAX_SCALAR_ACCESS_BYTES: i64 = 8;

/// Whether the byte intervals `[left_start, left_start + left_bytes)` and
/// `[right_start, right_start + right_bytes)` are disjoint.
///
/// The kernel's one decision point for constant byte-interval overlap. Both
/// sides are required to supply a width so that no caller can leave one out
/// by accident: an interval test that carries a real width on one side and a
/// constant on the other answers a narrower question than it appears to, and
/// reports overlapping bytes as disjoint whenever the real access is wider
/// than the constant. A caller with no width of its own passes
/// [`MAX_SCALAR_ACCESS_BYTES`], which can only shrink the disjoint set.
pub(in crate::kernel) fn byte_intervals_disjoint(
    left_start: i64,
    left_bytes: i64,
    right_start: i64,
    right_bytes: i64,
) -> bool {
    left_start.saturating_add(left_bytes) <= right_start
        || right_start.saturating_add(right_bytes) <= left_start
}

pub(in crate::kernel) fn memory_range_overlaps_pointer(
    range: &CMemoryRange,
    pointer: &Pointer,
    bytes: u32,
) -> bool {
    let pointer_base = Pointer {
        block: pointer.block.clone(),
        offset: pointer.offset.clone(),
    };
    if range.base().blocks_proven_distinct(&pointer_base) {
        return false;
    }
    let Some((start, end)) = concrete_memory_range_bounds(range) else {
        return true;
    };
    let Some(pointer_offset) = pointer.offset.as_const() else {
        return true;
    };
    // An access whose end is not representable is read as reaching everything,
    // as is a range whose extent is not; neither is a bound to subtract from.
    let (Some(_), Some(extent)) = (
        pointer_offset.checked_add(i64::from(bytes)),
        end.checked_sub(start),
    ) else {
        return true;
    };
    !byte_intervals_disjoint(pointer_offset, i64::from(bytes), start, extent)
}

fn add_memory_interval_candidates(
    index: &PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    subtree: &PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    range: &CMemoryRange,
    occurrences: &mut ResourceOccurrenceIds,
) {
    let Some(query_nodes) = memory_interval_nodes(range) else {
        return;
    };
    for query in query_nodes {
        crate::instrumentation::record_deterministic_work(1);
        for ancestor in memory_interval_ancestors(&query) {
            #[cfg(test)]
            crate::instrumentation::record_deterministic_work(index.lookup_comparisons(&ancestor));
            #[cfg(not(test))]
            crate::instrumentation::record_deterministic_work(1);
            if let Some(bucket) = index.get(&ancestor) {
                for occurrence in bucket.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    *occurrences = occurrences.with_value(*occurrence);
                }
            }
        }
        #[cfg(test)]
        crate::instrumentation::record_deterministic_work(subtree.lookup_comparisons(&query));
        #[cfg(not(test))]
        crate::instrumentation::record_deterministic_work(1);
        if let Some(bucket) = subtree.get(&query) {
            for occurrence in bucket.iter() {
                crate::instrumentation::record_deterministic_work(1);
                *occurrences = occurrences.with_value(*occurrence);
            }
        }
    }
}

pub(in crate::kernel) fn memory_ranges_overlap(left: &CMemoryRange, right: &CMemoryRange) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return false;
    }
    let (Some((left_start, left_end)), Some((right_start, right_end))) = (
        concrete_memory_range_bounds(left),
        concrete_memory_range_bounds(right),
    ) else {
        return true;
    };
    left_start < right_end && right_start < left_end
}

pub(crate) fn concrete_memory_range_bounds(range: &CMemoryRange) -> Option<(i64, i64)> {
    let base = range.base().offset.as_const()?;
    let start_elements = signed_bitvector_constant(range.start())?;
    let end_elements = signed_bitvector_constant(range.end())?;
    if start_elements >= end_elements {
        return None;
    }
    let width = i64::from(range.element_width());
    let start = base.checked_add(start_elements.checked_mul(width)?)?;
    let byte_count = end_elements
        .checked_sub(start_elements)?
        .checked_mul(width)?;
    let end = start.checked_add(byte_count)?;
    // The interval index and the resource-clause waiter index share this
    // fixed signed 32-bit physical coordinate space. In particular, the
    // exclusive end is not allowed to be i32::MAX + 1.
    (i64::from(i32::MIN)..=i64::from(i32::MAX))
        .contains(&start)
        .then_some(())?;
    (i64::from(i32::MIN)..=i64::from(i32::MAX))
        .contains(&end)
        .then_some(())?;
    Some((start, end))
}

fn memory_footprint_for_fact(fact: &CResourceFact) -> ResourceMemoryFootprint {
    if let Some(range) = fact.memory_range() {
        let mut ranges = vec![range.clone()];
        let mut uncertain = false;
        let mut source_snapshot = None;
        collect_memory_load_ranges(
            &range.base().offset,
            &mut ranges,
            &mut uncertain,
            &mut source_snapshot,
        );
        collect_memory_load_ranges_from_term(
            range.start(),
            &mut ranges,
            &mut uncertain,
            &mut source_snapshot,
        );
        collect_memory_load_ranges_from_term(
            range.end(),
            &mut ranges,
            &mut uncertain,
            &mut source_snapshot,
        );
        if uncertain {
            return ResourceMemoryFootprint::Unknown;
        }
        ranges.sort();
        ranges.dedup();
        return ResourceMemoryFootprint::Exact(std::sync::Arc::from(ranges));
    }
    // A composite core is the result of one or more body loads.  Until the
    // lowering supplies those prerequisite ranges explicitly, treating it as
    // unknown is the only sound choice; it still remains independently
    // indexed from concrete sibling projections.
    if matches!(fact.resource(), CResource::Composite { .. }) {
        ResourceMemoryFootprint::Unknown
    } else {
        ResourceMemoryFootprint::None
    }
}

/// Add the checked scalar cells that were read to form a projected address.
/// A memory resource's final range is not sufficient when its base or bounds
/// contain a load (for example, `owner->items[owner->length]`).  The compact
/// term walk is deliberately conservative for expression forms whose load
/// children are not exposed by this routine: those projections become an
/// unknown footprint instead of escaping invalidation.
fn collect_memory_load_ranges(
    offset: &PointerOffsetTerm,
    ranges: &mut Vec<CMemoryRange>,
    uncertain: &mut bool,
    source_snapshot: &mut Option<CMemorySnapshotIdentity>,
) {
    collect_memory_load_work(
        [MemoryLoadFootprintWork::Offset(offset, 0)],
        ranges,
        uncertain,
        source_snapshot,
    );
}

const MAX_MEMORY_LOAD_FOOTPRINT_DEPTH: usize = 64;

enum MemoryLoadFootprintWork<'a> {
    Offset(&'a PointerOffsetTerm, usize),
    Term(&'a Bitvector32Term, usize),
}

fn collect_memory_load_ranges_from_term(
    term: &Bitvector32Term,
    ranges: &mut Vec<CMemoryRange>,
    uncertain: &mut bool,
    source_snapshot: &mut Option<CMemorySnapshotIdentity>,
) {
    collect_memory_load_work(
        [MemoryLoadFootprintWork::Term(term, 0)],
        ranges,
        uncertain,
        source_snapshot,
    );
}

fn collect_memory_load_work<'a>(
    initial: impl IntoIterator<Item = MemoryLoadFootprintWork<'a>>,
    ranges: &mut Vec<CMemoryRange>,
    uncertain: &mut bool,
    source_snapshot: &mut Option<CMemorySnapshotIdentity>,
) {
    let mut work = initial.into_iter().collect::<Vec<_>>();
    while let Some(item) = work.pop() {
        match item {
            MemoryLoadFootprintWork::Offset(offset, depth) => {
                if depth > MAX_MEMORY_LOAD_FOOTPRINT_DEPTH {
                    *uncertain = true;
                    continue;
                }
                match offset {
                    PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
                    PointerOffsetTerm::Add(left, right) => {
                        work.push(MemoryLoadFootprintWork::Offset(left, depth + 1));
                        work.push(MemoryLoadFootprintWork::Offset(right, depth + 1));
                    }
                    PointerOffsetTerm::Int32Scaled { value, .. }
                    | PointerOffsetTerm::Int64Scaled { value, .. } => {
                        work.push(MemoryLoadFootprintWork::Term(value, depth + 1));
                    }
                }
            }
            MemoryLoadFootprintWork::Term(term, depth) => {
                if depth > MAX_MEMORY_LOAD_FOOTPRINT_DEPTH {
                    *uncertain = true;
                    continue;
                }
                match term {
                    Bitvector32Term::MemoryLoad(memory, pointer) => {
                        // MemoryLoad is shared by every CValue variant. Only
                        // the checked source snapshot can provide the loaded
                        // scalar's ABI width; absent evidence is ambiguous.
                        let Some(value) = memory.memory().known_value(pointer) else {
                            *uncertain = true;
                            continue;
                        };
                        let width = value.byte_width();
                        if width == 0 {
                            *uncertain = true;
                            continue;
                        }
                        let snapshot = CMemorySnapshotIdentity::of(memory.memory());
                        if source_snapshot.is_some_and(|previous| previous != snapshot) {
                            *uncertain = true;
                            continue;
                        }
                        *source_snapshot = Some(snapshot);
                        ranges.push(CMemoryRange::new_with_element_width(
                            pointer.as_ref().clone(),
                            Bitvector32Term::Constant(0),
                            Bitvector32Term::Constant(1),
                            width,
                        ));
                        work.push(MemoryLoadFootprintWork::Offset(&pointer.offset, depth + 1));
                    }
                    Bitvector32Term::PointerAddress(pointer) => {
                        work.push(MemoryLoadFootprintWork::Offset(&pointer.offset, depth + 1));
                    }
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
                    | Bitvector32Term::BitwiseXor(left, right)
                    | Bitvector32Term::Int64Add(left, right)
                    | Bitvector32Term::Int64Subtract(left, right)
                    | Bitvector32Term::Int64Multiply(left, right)
                    | Bitvector32Term::Int64Divide(left, right)
                    | Bitvector32Term::Int64Remainder(left, right)
                    | Bitvector32Term::Int64ShiftLeft(left, right)
                    | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
                    | Bitvector32Term::Int64BitwiseAnd(left, right)
                    | Bitvector32Term::Int64BitwiseOr(left, right)
                    | Bitvector32Term::Int64BitwiseXor(left, right)
                    | Bitvector32Term::UInt64Add(left, right)
                    | Bitvector32Term::UInt64Subtract(left, right)
                    | Bitvector32Term::UInt64Multiply(left, right)
                    | Bitvector32Term::UInt64Divide(left, right)
                    | Bitvector32Term::UInt64Remainder(left, right)
                    | Bitvector32Term::UInt64ShiftLeft(left, right)
                    | Bitvector32Term::UInt64LogicalShiftRight(left, right)
                    | Bitvector32Term::UInt64BitwiseAnd(left, right)
                    | Bitvector32Term::UInt64BitwiseOr(left, right)
                    | Bitvector32Term::UInt64BitwiseXor(left, right)
                    | Bitvector32Term::Float32Binary { left, right, .. }
                    | Bitvector32Term::Float64Binary { left, right, .. } => {
                        work.push(MemoryLoadFootprintWork::Term(left, depth + 1));
                        work.push(MemoryLoadFootprintWork::Term(right, depth + 1));
                    }
                    Bitvector32Term::BitwiseNot(value)
                    | Bitvector32Term::Float32Negate(value)
                    | Bitvector32Term::Float64Negate(value)
                    | Bitvector32Term::Int64From32(value)
                    | Bitvector32Term::Int64FromUInt32(value)
                    | Bitvector32Term::UInt64From32(value)
                    | Bitvector32Term::UInt32From64(value)
                    | Bitvector32Term::UInt64FromInt32(value)
                    | Bitvector32Term::UInt64FromInt64(value)
                    | Bitvector32Term::Int64BitwiseNot(value)
                    | Bitvector32Term::UInt64BitwiseNot(value) => {
                        work.push(MemoryLoadFootprintWork::Term(value, depth + 1));
                    }
                    Bitvector32Term::Constant(_)
                    | Bitvector32Term::Int64Constant(_)
                    | Bitvector32Term::UInt64Constant(_)
                    | Bitvector32Term::Variable(_) => {}
                    // These forms can hide load-bearing children behind a
                    // separate semantic object. Until checked read evidence
                    // is exposed for that object, invalidate conservatively.
                    Bitvector32Term::If { .. }
                    | Bitvector32Term::RangeFold { .. }
                    | Bitvector32Term::PureFunctionApplication { .. }
                    | Bitvector32Term::ClickFunctionApplication { .. }
                    | Bitvector32Term::AlgebraicMatch { .. }
                    | Bitvector32Term::IntegerToMachine { .. } => *uncertain = true,
                }
            }
        }
    }
}

impl ResourceContext {
    fn instance_validity_error(
        &self,
        fact: &CResourceFact,
    ) -> Option<ResourceContextValidityError> {
        let CResource::Instance(instance) = fact.resource() else {
            return None;
        };
        if !fact.has_valid_instance_access() {
            return Some(ResourceContextValidityError::InvalidInstanceAccess(
                fact.clone(),
            ));
        }
        let valid = self
            .storage
            .index
            .instances
            .get(&instance.identity)
            .is_some_and(|entries| entries.len() == 1);
        (!valid).then(|| ResourceContextValidityError::DuplicateOwnedResourceFact(fact.clone()))
    }

    /// The owned instances of one resource family and arity.
    ///
    /// Selection by family and arguments reads this shape bucket, so a loop
    /// binder's search costs the instances of its own family rather than the
    /// whole resource context.
    pub(crate) fn owned_instances_of_shape(
        &self,
        name: &str,
        arity: usize,
    ) -> Vec<&ResourceInstance> {
        let Some(entries) = self
            .storage
            .index
            .instance_shapes
            .get(&(name.to_string(), arity))
        else {
            return Vec::new();
        };
        entries
            .iter()
            .filter_map(|entry| match self.fact(*entry) {
                CResourceFact::Own(CResource::Instance(instance), quantity)
                    if quantity.as_const() == Some(1) =>
                {
                    Some(instance)
                }
                _ => None,
            })
            .collect()
    }

    pub fn owned_instance(&self, identity: Variable) -> Option<&ResourceInstance> {
        let entries = self.storage.index.instances.get(&identity)?;
        if entries.len() != 1 {
            return None;
        }
        let CResourceFact::Own(CResource::Instance(instance), quantity) =
            self.fact(*entries.iter().next()?)
        else {
            return None;
        };
        (quantity.as_const() == Some(1)).then_some(instance)
    }

    pub fn new() -> Self {
        Self::default()
    }

    /// Whether two resource snapshots are the exact same persistent value.
    ///
    /// Proof joins use this constant-time identity check to retain a resource
    /// context that was untouched in every arm without enumerating it.
    #[cfg(test)]
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.storage, &other.storage)
    }

    /// Whether this snapshot contains the exact named representation.
    ///
    /// This deliberately does not use proof-aware resource entailment.
    /// Representation-sensitive operations such as structural joins and
    /// scoped composite opening need to know whether the entry itself is
    /// present, rather than whether a cached projection entails it.
    pub(crate) fn contains_exact_representation(&self, fact: &CResourceFact) -> bool {
        self.storage.index.exact.contains_key(fact)
    }

    fn history_tail_is(
        current: Option<&std::sync::Arc<ResourceContextChange>>,
        expected: Option<&std::sync::Arc<ResourceContextChange>>,
    ) -> bool {
        match (current, expected) {
            (Some(current), Some(expected)) => std::sync::Arc::ptr_eq(current, expected),
            (None, None) => true,
            _ => false,
        }
    }

    pub(crate) fn changed_facts_since(&self, ancestor: &Self) -> Option<BTreeSet<CResourceFact>> {
        if !std::sync::Arc::ptr_eq(&self.storage.origin, &ancestor.storage.origin) {
            return None;
        }
        let expected = ancestor.storage.history.as_ref();
        let mut current = self.storage.history.as_ref();
        let mut changed = BTreeSet::new();
        while !Self::history_tail_is(current, expected) {
            let change = current?;
            changed.insert(change.fact.clone());
            current = change.parent.as_ref();
        }
        Some(changed)
    }

    /// Exact multiplicity of one representation, for an opt-in proof trace.
    pub(crate) fn exact_count(&self, fact: &CResourceFact) -> usize {
        self.storage
            .index
            .exact
            .get(fact)
            .map_or(0, PersistentSet::len)
    }

    /// Whether this snapshot was obtained by persistent resource mutations
    /// from `ancestor`.
    pub(crate) fn descends_from(&self, ancestor: &Self) -> bool {
        self.changed_facts_since(ancestor).is_some()
    }

    /// Compare only the explicit exchanges since a shared proof frontier.
    /// Supported projections and cached expansions are checked at each changed
    /// key as well; neither can be smuggled in as an ownership-equivalent delta.
    pub(crate) fn same_exchange_from(&self, other: &Self, ancestor: &Self) -> bool {
        let Some(mut changed) = self.changed_facts_since(ancestor) else {
            return false;
        };
        let Some(other_changed) = other.changed_facts_since(ancestor) else {
            return false;
        };
        changed.extend(other_changed);
        for fact in changed {
            let representations = |context: &Self| {
                let mut counts = BTreeMap::new();
                for entry in context
                    .storage
                    .index
                    .exact
                    .get(&fact)
                    .into_iter()
                    .flat_map(ResourceEntryIds::iter)
                {
                    let support = context
                        .storage
                        .support_occurrence_by_projection
                        .get(entry)
                        .copied();
                    *counts
                        .entry((support, context.storage.supported_by.get(entry).cloned()))
                        .or_insert(0usize) += 1;
                }
                counts
            };
            let cached_expansions = |context: &Self| {
                context
                    .storage
                    .index
                    .exact
                    .get(&fact)
                    .into_iter()
                    .flat_map(ResourceEntryIds::iter)
                    .filter_map(|entry| {
                        let occurrence = context.occurrence(*entry);
                        let cache_key = if context
                            .storage
                            .projections_by_support_occurrence
                            .get(&occurrence)
                            .is_some()
                        {
                            occurrence
                        } else {
                            let (_, rank) = context.support_cache_key(*entry);
                            ResourceOccurrenceId {
                                arena: 0,
                                ordinal: rank as u64,
                            }
                        };
                        context
                            .storage
                            .expansions_by_support_occurrence
                            .get(&occurrence)
                            .map(|expansion| (cache_key, expansion.clone()))
                    })
                    .collect::<BTreeMap<_, _>>()
            };
            if representations(self) != representations(other)
                || cached_expansions(self) != cached_expansions(other)
            {
                return false;
            }
        }
        true
    }

    /// Exact common resource representation of two descendants.
    ///
    /// Only keys changed after `ancestor` are inspected. Starting from the
    /// left descendant preserves the legacy intersection's insertion order;
    /// changed exact facts are trimmed to the multiplicity present in both
    /// descendants.
    pub(crate) fn common_exact_descendant(
        left: &Self,
        right: &Self,
        ancestor: &Self,
    ) -> Option<Self> {
        let mut changed = left.changed_facts_since(ancestor)?;
        changed.extend(right.changed_facts_since(ancestor)?);
        let representations = |context: &Self, fact: &CResourceFact| {
            let mut explicit = 0usize;
            let mut supported = BTreeMap::<
                (CResourceFact, ResourceOccurrenceId),
                (usize, Option<ResourceSupportMetadata>, bool),
            >::new();
            for entry in context
                .storage
                .index
                .exact
                .get(fact)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
            {
                if let Some(support) = context.storage.supported_by.get(entry) {
                    let Some(support_entry) = context
                        .storage
                        .support_occurrence_by_projection
                        .get(entry)
                        .copied()
                    else {
                        continue;
                    };
                    let metadata = context
                        .storage
                        .support_metadata_by_projection
                        .get(&context.occurrence(*entry))
                        .cloned();
                    let slot = supported
                        .entry((support.clone(), support_entry))
                        .or_insert((0, metadata.clone(), true));
                    if slot.1 != metadata {
                        // Equal projections with different dependency
                        // topology cannot be safely joined under one record.
                        // The explicit consistency bit distinguishes this
                        // from a legacy projection that has no metadata at
                        // all; the former is dropped, the latter remains
                        // valid support-only evidence.
                        slot.1 = None;
                        slot.2 = false;
                    }
                    slot.0 += 1;
                } else {
                    explicit += 1;
                }
            }
            (explicit, supported)
        };
        let mut common_representations = Vec::new();
        for fact in &changed {
            let (left_explicit, left_supported) = representations(left, fact);
            let (right_explicit, right_supported) = representations(right, fact);
            let supported = left_supported
                .into_iter()
                .filter_map(|(support, (left_count, left_metadata, left_consistent))| {
                    right_supported
                        .get(&support)
                        .filter(|(_, right_metadata, right_consistent)| {
                            left_consistent
                                && *right_consistent
                                && left_metadata.as_ref().map(|metadata| &metadata.footprint)
                                    == right_metadata.as_ref().map(|metadata| &metadata.footprint)
                        })
                        .map(|_| {
                            let right_count = right_supported[&support].0;
                            (support, left_count.min(right_count), left_metadata)
                        })
                })
                .collect::<Vec<_>>();
            let shared_owned = if fact.is_own() {
                let left_occurrences = left
                    .storage
                    .index
                    .exact
                    .get(fact)
                    .into_iter()
                    .flat_map(ResourceEntryIds::iter)
                    .map(|entry| left.occurrence(*entry))
                    .collect::<BTreeSet<_>>();
                right
                    .storage
                    .index
                    .exact
                    .get(fact)
                    .into_iter()
                    .flat_map(ResourceEntryIds::iter)
                    .map(|entry| right.occurrence(*entry))
                    .filter(|occurrence| left_occurrences.contains(occurrence))
                    .collect::<BTreeSet<_>>()
            } else {
                BTreeSet::new()
            };
            let common_expansions = left
                .storage
                .index
                .exact
                .get(fact)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .filter_map(|entry| {
                    let occurrence = left.occurrence(*entry);
                    let left_expansion = left
                        .storage
                        .expansions_by_support_occurrence
                        .get(&occurrence)?;
                    let right_entry = right.storage.entry_by_occurrence.get(&occurrence)?;
                    if right.fact(*right_entry) != fact {
                        return None;
                    }
                    let right_expansion = right
                        .storage
                        .expansions_by_support_occurrence
                        .get(&occurrence)?;
                    (left_expansion == right_expansion)
                        .then(|| (occurrence, left_expansion.clone()))
                })
                .collect::<Vec<_>>();
            common_representations.push((
                fact.clone(),
                left_explicit.min(right_explicit),
                supported,
                shared_owned,
                common_expansions,
            ));
        }

        let mut common = left.clone();
        for (fact, _, _, shared_owned, common_expansions) in &common_representations {
            let entries = common
                .storage
                .index
                .exact
                .get(fact)
                .cloned()
                .unwrap_or_default();
            for entry in entries.iter().copied() {
                let preserve = fact.is_own() && shared_owned.contains(&common.occurrence(entry));
                if !preserve && common.storage.facts.contains_key(&entry) {
                    common.remove_entry(entry);
                }
            }
            if fact.is_own() {
                let retained_expansions = common_expansions
                    .iter()
                    .map(|(occurrence, _)| *occurrence)
                    .collect::<BTreeSet<_>>();
                let retained_entries = common
                    .storage
                    .index
                    .exact
                    .get(fact)
                    .into_iter()
                    .flat_map(ResourceEntryIds::iter)
                    .copied()
                    .collect::<Vec<_>>();
                for entry in retained_entries {
                    let occurrence = common.occurrence(entry);
                    if common
                        .storage
                        .expansions_by_support_occurrence
                        .contains_key(&occurrence)
                        && !retained_expansions.contains(&occurrence)
                    {
                        common =
                            common.without_cached_supported_expansion_for_occurrence(occurrence);
                    }
                }
            }
        }
        for (fact, explicit, _, shared_owned, _) in &common_representations {
            let additions = (*explicit).saturating_sub(shared_owned.len());
            for _ in 0..additions {
                common.insert_fact(fact.clone());
            }
        }
        for (fact, _, supported, _, _) in &common_representations {
            for ((support, support_occurrence), count, metadata) in supported.iter() {
                if !common.storage.index.exact.contains_key(support) {
                    continue;
                }
                for _ in 0..*count {
                    if common
                        .storage
                        .entry_by_occurrence
                        .get(support_occurrence)
                        .is_some_and(|entry| common.fact(*entry) == support)
                    {
                        common.insert_fact_with_support_occurrence_and_metadata(
                            fact.clone(),
                            Some(support.clone()),
                            Some(*support_occurrence),
                            metadata.clone(),
                        );
                    }
                }
            }
        }
        Some(common)
    }

    fn iter(&self) -> impl DoubleEndedIterator<Item = &CResourceFact> + ExactSizeIterator {
        self.storage.facts.iter().map(|(_, fact)| fact)
    }

    fn fact(&self, entry: ResourceEntryId) -> &CResourceFact {
        self.storage
            .facts
            .get(&entry)
            .expect("resource index refers to a live entry")
    }

    pub(crate) fn occurrence(&self, entry: ResourceEntryId) -> ResourceOccurrenceId {
        *self
            .storage
            .occurrence_by_entry
            .get(&entry)
            .expect("resource index refers to a live occurrence")
    }

    pub(crate) fn owned_occurrence_matches(
        &self,
        occurrence: ResourceOccurrenceId,
        fact: &CResourceFact,
    ) -> bool {
        self.storage
            .entry_by_occurrence
            .get(&occurrence)
            .is_some_and(|entry| self.storage.facts.get(entry) == Some(fact) && fact.is_own())
    }

    /// Return the exact live view fact at an occurrence selected from a
    /// checked input requirement. This never searches by fact equality.
    pub(crate) fn view_fact_at_occurrence(
        &self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<&CResourceFact> {
        let entry = self.storage.entry_by_occurrence.get(&occurrence)?;
        let fact = self.storage.facts.get(entry)?;
        fact.is_view().then_some(fact)
    }

    /// Retire the exact principal view installed for a checked loan. General
    /// resource consumption leaves views in place because descriptions are
    /// copyable; closing an escrow instead removes its particular occurrence
    /// before returning the owner. The dependency ties this removal to the
    /// same live binding the loan recovery just discharged.
    pub(crate) fn without_bound_view_occurrence(
        mut self,
        occurrence: ResourceOccurrenceId,
        binding: &crate::kernel::loans::LoanViewBinding,
    ) -> Option<Self> {
        if !self.view_occurrence_is_principal(occurrence)
            || self.view_fact_at_occurrence(occurrence) != Some(&binding.viewed)
            || self.loan_dependency(occurrence) != Some(binding)
        {
            return None;
        }
        let entry = *self.storage.entry_by_occurrence.get(&occurrence)?;
        self.remove_entry(entry);
        Some(self)
    }

    pub(crate) fn view_occurrence_is_principal(&self, occurrence: ResourceOccurrenceId) -> bool {
        self.storage
            .entry_by_occurrence
            .get(&occurrence)
            .is_some_and(|entry| {
                self.fact(*entry).is_view()
                    && !self.storage.supported_by.contains_key(entry)
                    && !self
                        .storage
                        .support_occurrence_by_projection
                        .contains_key(entry)
            })
    }

    fn support_cache_key(&self, entry: ResourceEntryId) -> (CResourceFact, usize) {
        let fact = self.fact(entry).clone();
        let rank = self
            .storage
            .index
            .exact
            .get(&fact)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter(|candidate| self.fact(**candidate).is_own())
            .take_while(|candidate| **candidate != entry)
            .count();
        (fact, rank)
    }

    fn insert_fact(&mut self, fact: CResourceFact) {
        self.insert_fact_with_support(fact, None);
    }

    fn insert_fact_with_support(&mut self, fact: CResourceFact, support: Option<CResourceFact>) {
        let support_entry = support.as_ref().and_then(|support| {
            self.storage
                .index
                .exact
                .get(support)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .find(|entry| self.fact(**entry) == support && self.fact(**entry).is_own())
                .copied()
        });
        let support_occurrence =
            support_entry.and_then(|entry| self.storage.occurrence_by_entry.get(&entry).copied());
        self.insert_fact_with_support_occurrence(fact, support, support_occurrence);
    }

    fn insert_fact_with_support_occurrence(
        &mut self,
        fact: CResourceFact,
        support: Option<CResourceFact>,
        support_occurrence: Option<ResourceOccurrenceId>,
    ) {
        self.insert_fact_with_support_occurrence_and_metadata(
            fact,
            support,
            support_occurrence,
            None,
        );
    }

    fn insert_fact_with_support_occurrence_and_metadata(
        &mut self,
        fact: CResourceFact,
        support: Option<CResourceFact>,
        support_occurrence: Option<ResourceOccurrenceId>,
        support_metadata: Option<ResourceSupportMetadata>,
    ) {
        self.insert_fact_with_support_occurrence_and_metadata_at(
            fact,
            support,
            support_occurrence,
            support_metadata,
            None,
        );
    }

    fn insert_fact_with_support_occurrence_and_metadata_at(
        &mut self,
        fact: CResourceFact,
        support: Option<CResourceFact>,
        support_occurrence: Option<ResourceOccurrenceId>,
        support_metadata: Option<ResourceSupportMetadata>,
        occurrence_override: Option<ResourceOccurrenceId>,
    ) {
        let entry = self.storage.next_entry_id;
        let occurrence = occurrence_override.unwrap_or_else(ResourceOccurrenceId::fresh);
        let next_entry_id = self
            .storage
            .next_entry_id
            .checked_add(1)
            .expect("resource entry id space exhausted");
        let supported_by = support.as_ref().map_or_else(
            || self.storage.supported_by.clone(),
            |support| {
                self.storage
                    .supported_by
                    .with_inserted(entry, support.clone())
            },
        );
        let projections_by_support = support.as_ref().map_or_else(
            || self.storage.projections_by_support.clone(),
            |support| {
                insert_resource_index_entry(
                    &self.storage.projections_by_support,
                    support.clone(),
                    entry,
                )
            },
        );
        let support_occurrence_by_projection = support_occurrence.map_or_else(
            || self.storage.support_occurrence_by_projection.clone(),
            |support_occurrence| {
                self.storage
                    .support_occurrence_by_projection
                    .with_inserted(entry, support_occurrence)
            },
        );
        let projections_by_support_occurrence = support_occurrence.map_or_else(
            || self.storage.projections_by_support_occurrence.clone(),
            |support_occurrence| {
                insert_resource_index_entry(
                    &self.storage.projections_by_support_occurrence,
                    support_occurrence,
                    entry,
                )
            },
        );
        let support_metadata_by_projection = support_metadata.as_ref().map_or_else(
            || self.storage.support_metadata_by_projection.clone(),
            |metadata| {
                self.storage
                    .support_metadata_by_projection
                    .with_inserted(occurrence, metadata.clone())
            },
        );
        let projections_by_memory_block = match support_metadata
            .as_ref()
            .map(|metadata| &metadata.footprint)
        {
            Some(ResourceMemoryFootprint::Exact(ranges)) => ranges.iter().fold(
                self.storage.projections_by_memory_block.clone(),
                |index, footprint| {
                    insert_occurrence_index_entry(
                        &index,
                        footprint.base().block.clone(),
                        occurrence,
                    )
                },
            ),
            Some(ResourceMemoryFootprint::None | ResourceMemoryFootprint::Unknown) | None => {
                self.storage.projections_by_memory_block.clone()
            }
        };
        let unknown_memory_support = support_metadata.as_ref().map_or_else(
            || self.storage.unknown_memory_support.clone(),
            |metadata| match metadata.footprint {
                ResourceMemoryFootprint::Exact(_) | ResourceMemoryFootprint::None => {
                    self.storage.unknown_memory_support.clone()
                }
                ResourceMemoryFootprint::Unknown => {
                    self.storage.unknown_memory_support.with_value(occurrence)
                }
            },
        );
        let projections_by_memory_interval = match support_metadata
            .as_ref()
            .map(|metadata| &metadata.footprint)
        {
            Some(ResourceMemoryFootprint::Exact(ranges)) => ranges.iter().fold(
                self.storage.projections_by_memory_interval.clone(),
                |index, footprint| {
                    let Some(nodes) = memory_interval_nodes(footprint) else {
                        return index;
                    };
                    nodes.into_iter().fold(index, |index, node| {
                        insert_occurrence_index_entry(&index, node, occurrence)
                    })
                },
            ),
            Some(ResourceMemoryFootprint::None | ResourceMemoryFootprint::Unknown) | None => {
                self.storage.projections_by_memory_interval.clone()
            }
        };
        let projections_by_memory_interval_subtree = match support_metadata
            .as_ref()
            .map(|metadata| &metadata.footprint)
        {
            Some(ResourceMemoryFootprint::Exact(ranges)) => ranges.iter().fold(
                self.storage.projections_by_memory_interval_subtree.clone(),
                |index, footprint| {
                    let Some(nodes) = memory_interval_nodes(footprint) else {
                        return index;
                    };
                    nodes
                        .into_iter()
                        .flat_map(|node| memory_interval_ancestors(&node))
                        .fold(index, |index, ancestor| {
                            insert_occurrence_index_entry(&index, ancestor, occurrence)
                        })
                },
            ),
            Some(ResourceMemoryFootprint::None | ResourceMemoryFootprint::Unknown) | None => {
                self.storage.projections_by_memory_interval_subtree.clone()
            }
        };
        let symbolic_memory_support = support_metadata.as_ref().map_or_else(
            || self.storage.symbolic_memory_support.clone(),
            |metadata| match &metadata.footprint {
                ResourceMemoryFootprint::Exact(ranges)
                    if ranges.iter().any(|range| {
                        memory_interval_nodes(range).is_none()
                            || memory_block_may_alias(&range.base().block)
                    }) =>
                {
                    self.storage.symbolic_memory_support.with_value(occurrence)
                }
                _ => self.storage.symbolic_memory_support.clone(),
            },
        );
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.with_inserted(entry, fact.clone()),
            next_entry_id,
            occurrence_by_entry: self
                .storage
                .occurrence_by_entry
                .with_inserted(entry, occurrence),
            entry_by_occurrence: self
                .storage
                .entry_by_occurrence
                .with_inserted(occurrence, entry),
            index: self.storage.index.with_inserted(entry, &fact),
            supported_by,
            support_occurrence_by_projection,
            projections_by_support,
            projections_by_support_occurrence,
            support_metadata_by_projection,
            projections_by_memory_block,
            projections_by_memory_interval,
            projections_by_memory_interval_subtree,
            symbolic_memory_support,
            unknown_memory_support,
            expansions_by_support_occurrence: self.storage.expansions_by_support_occurrence.clone(),
            expansions_by_support_entry: self.storage.expansions_by_support_entry.clone(),
            origin: self.storage.origin.clone(),
            history: Some(std::sync::Arc::new(ResourceContextChange {
                fact,
                parent: self.storage.history.clone(),
            })),
            materialized: std::sync::OnceLock::new(),
        });
    }

    fn remove_entry(&mut self, entry: ResourceEntryId) -> CResourceFact {
        // Remove the complete support-descendant closure. An explicit stack
        // keeps work proportional to affected output, and the visited set
        // makes malformed cyclic evidence harmless.
        let fact = self.fact(entry).clone();
        let mut pending = vec![(entry, false)];
        let mut scheduled = BTreeSet::new();
        let mut visited = BTreeSet::new();
        let mut removed_occurrences = Vec::new();
        scheduled.insert(entry);
        while let Some((current, leaving)) = pending.pop() {
            if leaving {
                if self.storage.facts.contains_key(&current) {
                    removed_occurrences.push(self.occurrence(current));
                    self.remove_entry_only(current);
                }
                continue;
            }
            if !visited.insert(current) || !self.storage.facts.contains_key(&current) {
                continue;
            }
            pending.push((current, true));
            let projections = self
                .storage
                .projections_by_support_occurrence
                .get(&self.occurrence(current))
                .cloned()
                .unwrap_or_default();
            for projection in projections.iter().copied().rev() {
                if scheduled.insert(projection) {
                    crate::instrumentation::record_deterministic_work(1);
                    pending.push((projection, false));
                }
            }
        }
        if !removed_occurrences.is_empty() {
            let map = removed_occurrences
                .into_iter()
                .fold(self.loan_dependencies.map.clone(), |map, occurrence| {
                    map.without_key(&occurrence)
                });
            self.loan_dependencies =
                std::sync::Arc::new(crate::kernel::loans::LoanViewBindingsState {
                    identity: crate::kernel::loans::next_loan_binding_identity(),
                    map,
                });
        }
        fact
    }

    fn remove_entry_only(&mut self, entry: ResourceEntryId) -> CResourceFact {
        let fact = self.fact(entry).clone();
        let support = self.storage.supported_by.get(&entry).cloned();
        let supported_by = self.storage.supported_by.without_key(&entry);
        let support_occurrence = self
            .storage
            .support_occurrence_by_projection
            .get(&entry)
            .copied();
        let support_occurrence_by_projection = self
            .storage
            .support_occurrence_by_projection
            .without_key(&entry);
        let projections_by_support = support.as_ref().map_or_else(
            || self.storage.projections_by_support.clone(),
            |support| {
                remove_resource_index_entry(&self.storage.projections_by_support, support, entry)
            },
        );
        let projections_by_support_occurrence = support_occurrence.map_or_else(
            || self.storage.projections_by_support_occurrence.clone(),
            |support_occurrence| {
                remove_resource_index_entry(
                    &self.storage.projections_by_support_occurrence,
                    &support_occurrence,
                    entry,
                )
            },
        );
        let occurrence = self.occurrence(entry);
        let support_metadata = self
            .storage
            .support_metadata_by_projection
            .get(&occurrence)
            .cloned();
        let projections_by_memory_block = match support_metadata
            .as_ref()
            .map(|metadata| &metadata.footprint)
        {
            Some(ResourceMemoryFootprint::Exact(ranges)) => ranges.iter().fold(
                self.storage.projections_by_memory_block.clone(),
                |index, footprint| {
                    remove_occurrence_index_entry(&index, &footprint.base().block, occurrence)
                },
            ),
            Some(ResourceMemoryFootprint::None | ResourceMemoryFootprint::Unknown) | None => {
                self.storage.projections_by_memory_block.clone()
            }
        };
        let projections_by_memory_interval = match support_metadata
            .as_ref()
            .map(|metadata| &metadata.footprint)
        {
            Some(ResourceMemoryFootprint::Exact(ranges)) => ranges.iter().fold(
                self.storage.projections_by_memory_interval.clone(),
                |index, footprint| {
                    let Some(nodes) = memory_interval_nodes(footprint) else {
                        return index;
                    };
                    nodes.into_iter().fold(index, |index, node| {
                        remove_occurrence_index_entry(&index, &node, occurrence)
                    })
                },
            ),
            Some(ResourceMemoryFootprint::None | ResourceMemoryFootprint::Unknown) | None => {
                self.storage.projections_by_memory_interval.clone()
            }
        };
        let projections_by_memory_interval_subtree = match support_metadata
            .as_ref()
            .map(|metadata| &metadata.footprint)
        {
            Some(ResourceMemoryFootprint::Exact(ranges)) => ranges.iter().fold(
                self.storage.projections_by_memory_interval_subtree.clone(),
                |index, footprint| {
                    let Some(nodes) = memory_interval_nodes(footprint) else {
                        return index;
                    };
                    nodes
                        .into_iter()
                        .flat_map(|node| memory_interval_ancestors(&node))
                        .fold(index, |index, ancestor| {
                            remove_occurrence_index_entry(&index, &ancestor, occurrence)
                        })
                },
            ),
            Some(ResourceMemoryFootprint::None | ResourceMemoryFootprint::Unknown) | None => {
                self.storage.projections_by_memory_interval_subtree.clone()
            }
        };
        let symbolic_memory_support = support_metadata.as_ref().map_or_else(
            || self.storage.symbolic_memory_support.clone(),
            |metadata| match &metadata.footprint {
                ResourceMemoryFootprint::Exact(ranges)
                    if ranges.iter().any(|range| {
                        memory_interval_nodes(range).is_none()
                            || memory_block_may_alias(&range.base().block)
                    }) =>
                {
                    self.storage
                        .symbolic_memory_support
                        .without_value(&occurrence)
                }
                _ => self.storage.symbolic_memory_support.clone(),
            },
        );
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.without_key(&entry),
            next_entry_id: self.storage.next_entry_id,
            occurrence_by_entry: self.storage.occurrence_by_entry.without_key(&entry),
            entry_by_occurrence: self.storage.entry_by_occurrence.without_key(&occurrence),
            index: self.storage.index.without_entry(entry, &fact),
            supported_by,
            support_occurrence_by_projection,
            projections_by_support,
            projections_by_support_occurrence,
            support_metadata_by_projection: self
                .storage
                .support_metadata_by_projection
                .without_key(&occurrence),
            projections_by_memory_block,
            projections_by_memory_interval,
            projections_by_memory_interval_subtree,
            symbolic_memory_support,
            unknown_memory_support: self
                .storage
                .unknown_memory_support
                .without_value(&occurrence),
            expansions_by_support_occurrence: self
                .storage
                .expansions_by_support_occurrence
                .without_key(&occurrence),
            expansions_by_support_entry: self.storage.expansions_by_support_entry.clone(),
            origin: self.storage.origin.clone(),
            history: Some(std::sync::Arc::new(ResourceContextChange {
                fact: fact.clone(),
                parent: self.storage.history.clone(),
            })),
            materialized: std::sync::OnceLock::new(),
        });
        if fact.is_own() {
            self.rekey_cached_support_entries(&fact);
        }
        fact
    }

    /// Rebuild only the canonical cache keys for one support fact. Removing
    /// an earlier equal authority changes the rank of every later equal
    /// authority; leaving the old `(fact, rank)` entries in place would let a
    /// later insertion inherit stale expansion evidence.
    fn rekey_cached_support_entries(&mut self, fact: &CResourceFact) {
        let mut bucket = PersistentMap::default();
        let mut rank = 0usize;
        for entry in self
            .storage
            .index
            .exact
            .get(fact)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
        {
            crate::instrumentation::record_deterministic_work(1);
            if self.fact(*entry).is_own() {
                if let Some(expansion) = self
                    .storage
                    .expansions_by_support_occurrence
                    .get(&self.occurrence(*entry))
                {
                    bucket = bucket.with_inserted(rank, expansion.clone());
                }
                rank += 1;
            }
        }
        let expansions_by_support_entry = if bucket.is_empty() {
            self.storage.expansions_by_support_entry.without_key(fact)
        } else {
            self.storage
                .expansions_by_support_entry
                .with_inserted(fact.clone(), bucket)
        };
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.clone(),
            next_entry_id: self.storage.next_entry_id,
            occurrence_by_entry: self.storage.occurrence_by_entry.clone(),
            entry_by_occurrence: self.storage.entry_by_occurrence.clone(),
            index: self.storage.index.clone(),
            supported_by: self.storage.supported_by.clone(),
            support_occurrence_by_projection: self.storage.support_occurrence_by_projection.clone(),
            projections_by_support: self.storage.projections_by_support.clone(),
            projections_by_support_occurrence: self
                .storage
                .projections_by_support_occurrence
                .clone(),
            support_metadata_by_projection: self.storage.support_metadata_by_projection.clone(),
            projections_by_memory_block: self.storage.projections_by_memory_block.clone(),
            projections_by_memory_interval: self.storage.projections_by_memory_interval.clone(),
            projections_by_memory_interval_subtree: self
                .storage
                .projections_by_memory_interval_subtree
                .clone(),
            symbolic_memory_support: self.storage.symbolic_memory_support.clone(),
            unknown_memory_support: self.storage.unknown_memory_support.clone(),
            expansions_by_support_occurrence: self.storage.expansions_by_support_occurrence.clone(),
            expansions_by_support_entry,
            origin: self.storage.origin.clone(),
            history: self.storage.history.clone(),
            materialized: std::sync::OnceLock::new(),
        });
    }

    fn replace_facts(
        &mut self,
        facts: impl IntoIterator<Item = (Option<ResourceOccurrenceId>, CResourceFact)>,
        changed_facts: impl IntoIterator<Item = CResourceFact>,
    ) {
        // Normalization rebuilds the indexed representation, but unchanged
        // facts keep their opaque authority occurrence. This lets the
        // support relation be restored after an unrelated merge without
        // manufacturing a fresh scope for an observation.
        let mut replacement_facts = PersistentMap::default();
        let mut replacement_index = ResourceContextIndex::default();
        let mut replacement_occurrences = PersistentMap::default();
        let mut replacement_entries = PersistentMap::default();
        let mut next_entry_id = 0_u64;
        for (occurrence, fact) in facts {
            // Normalization carries the occurrence alongside its slot. Equal
            // facts therefore cannot exchange authorities merely because a
            // BTreeMap happens to return them in a different order. A slot
            // whose fact was merged or otherwise replaced has no occurrence
            // and receives a fresh authority below.
            let occurrence = occurrence.unwrap_or_else(ResourceOccurrenceId::fresh);
            replacement_facts = replacement_facts.with_inserted(next_entry_id, fact.clone());
            replacement_index = replacement_index.with_inserted(next_entry_id, &fact);
            replacement_occurrences =
                replacement_occurrences.with_inserted(next_entry_id, occurrence);
            replacement_entries = replacement_entries.with_inserted(occurrence, next_entry_id);
            next_entry_id = next_entry_id
                .checked_add(1)
                .expect("resource entry id space exhausted");
        }
        let mut history = self.storage.history.clone();
        for fact in changed_facts {
            history = Some(std::sync::Arc::new(ResourceContextChange {
                fact,
                parent: history,
            }));
        }
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: replacement_facts,
            next_entry_id,
            occurrence_by_entry: replacement_occurrences,
            entry_by_occurrence: replacement_entries,
            index: replacement_index,
            supported_by: PersistentMap::default(),
            support_occurrence_by_projection: PersistentMap::default(),
            projections_by_support: PersistentMap::default(),
            projections_by_support_occurrence: PersistentMap::default(),
            support_metadata_by_projection: PersistentMap::default(),
            projections_by_memory_block: PersistentMap::default(),
            projections_by_memory_interval: PersistentMap::default(),
            projections_by_memory_interval_subtree: PersistentMap::default(),
            symbolic_memory_support: ResourceOccurrenceIds::default(),
            unknown_memory_support: ResourceOccurrenceIds::default(),
            expansions_by_support_occurrence: PersistentMap::default(),
            expansions_by_support_entry: PersistentMap::default(),
            origin: self.storage.origin.clone(),
            history,
            materialized: std::sync::OnceLock::new(),
        });
    }

    pub(in crate::kernel) fn memory_block_facts(
        &self,
        block: &PointerBlock,
    ) -> impl Iterator<Item = &CResourceFact> {
        self.storage
            .index
            .memory_by_block
            .get(block)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.fact(*entry))
    }

    /// Necessary-shape candidates for proof-aware direct resource matching.
    /// Snapshot-insensitive matching cannot change a pointer block, resource
    /// family, composite/token name, or arity, so unrelated facts need not
    /// enter the expensive memory-resolution comparator.
    pub(in crate::kernel) fn direct_match_candidates(
        &self,
        fact: &CResourceFact,
    ) -> impl Iterator<Item = &CResourceFact> {
        self.direct_match_candidate_positions(fact)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.fact(*entry))
    }

    /// Returns one retained fact that directly entails `required` without
    /// expanding a composite or normalizing unrelated resources.
    ///
    /// This is the evidence-preserving counterpart of `satisfies_fact` for
    /// operations, such as fold/unfold checking, that must subsequently act
    /// on the exact held representation rather than merely learn that a
    /// requirement is available.
    pub(crate) fn directly_supporting_fact(
        &self,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<&CResourceFact> {
        self.direct_match_candidates(required)
            .find(|available| resource_fact_entails(available, required, assumptions))
    }

    /// Select an exact owned occurrence for a fact-only API. Equal owned
    /// facts are distinct authorities, so callers that need to attach a
    /// projection must reject an ambiguous value-only lookup.
    pub(crate) fn unique_owned_occurrence_for_fact(
        &self,
        required: &CResourceFact,
    ) -> Option<(ResourceOccurrenceId, &CResourceFact)> {
        let mut entries = self
            .storage
            .index
            .exact
            .get(required)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter(|entry| self.fact(**entry).is_own())
            .copied();
        let entry = entries.next()?;
        if entries.next().is_some() {
            return None;
        }
        Some((self.occurrence(entry), self.fact(entry)))
    }

    pub(crate) fn owned_occurrences_for_fact(
        &self,
        required: &CResourceFact,
    ) -> Vec<ResourceOccurrenceId> {
        self.storage
            .index
            .exact
            .get(required)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter(|entry| self.fact(**entry).is_own())
            .map(|entry| self.occurrence(*entry))
            .collect()
    }

    /// Return every exact occurrence for a representation, including viewed
    /// entries.  Resource rewrites use this only after inserting the exact
    /// child representation, so the caller can attach a dependency to the
    /// returned opaque occurrence rather than guessing by value.
    pub(crate) fn occurrences_for_fact(
        &self,
        required: &CResourceFact,
    ) -> Vec<ResourceOccurrenceId> {
        self.storage
            .index
            .exact
            .get(required)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.occurrence(*entry))
            .collect()
    }

    /// Finds the owned authority that directly supports a requirement. A
    /// supported projection records an owned fact (never another projection)
    /// as its support, so this is deliberately one indexed hop rather than a
    /// recursive search through caller-controlled metadata.
    pub(crate) fn directly_supporting_owned_entry(
        &self,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<(ResourceOccurrenceId, &CResourceFact)> {
        // Concrete memory requirements have a monotone start position.  Use
        // the exact bucket or its immediate predecessor before falling back
        // to the block bucket; repeated disjoint consumption otherwise
        // revisits every residual range produced by earlier clauses.
        if let CResource::Memory(range) = required.resource()
            && let Some(indexed) = self.concrete_memory_start_candidates(range, true)
        {
            for entry in indexed {
                let candidate = self.fact(entry);
                if resource_fact_entails(candidate, required, assumptions) && candidate.is_own() {
                    return Some((self.occurrence(entry), candidate));
                }
            }
        }
        self.direct_match_candidate_positions(required)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter_map(|entry| {
                let candidate = self.fact(*entry);
                if !resource_fact_entails(candidate, required, assumptions) {
                    return None;
                }
                if candidate.is_own() {
                    return Some((self.occurrence(*entry), candidate));
                }
                self.storage.supported_by.get(entry).and_then(|support| {
                    self.storage
                        .support_occurrence_by_projection
                        .get(entry)
                        .copied()
                        .filter(|support_occurrence| {
                            self.storage
                                .entry_by_occurrence
                                .get(support_occurrence)
                                .is_some_and(|entry| self.storage.facts.get(entry) == Some(support))
                                && support.is_own()
                        })
                        .map(|support_occurrence| (support_occurrence, support))
                })
            })
            .next()
    }

    fn concrete_memory_start_candidates(
        &self,
        range: &CMemoryRange,
        owned: bool,
    ) -> Option<Vec<ResourceEntryId>> {
        (range.start().as_const().is_some() && range.end().as_const().is_some()).then(|| {
            let key = (range.base().block.clone(), owned, range.start().clone());
            self.storage
                .index
                .memory_starts
                .get(&key)
                .into_iter()
                .chain(
                    self.storage
                        .index
                        .memory_starts
                        .get_less_than(&key)
                        .map(|(_, entries)| entries),
                )
                .flat_map(ResourceEntryIds::iter)
                .copied()
                .collect()
        })
    }

    /// Return indexed view occurrences that entail `required`. The caller
    /// resolves each occurrence through an explicit checked-state binding;
    /// this method never searches the loan ledger or unrelated frame entries.
    pub(crate) fn view_occurrences_for_fact(
        &self,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Vec<ResourceOccurrenceId> {
        self.direct_match_candidate_positions(required)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter_map(|entry| {
                let fact = self.fact(*entry);
                (fact.is_view() && resource_fact_entails(fact, required, assumptions))
                    .then_some(self.occurrence(*entry))
            })
            .collect()
    }

    /// Whether an exact projected representation is attached to the supplied
    /// owned support. This is kept indexed by the projected fact so proof
    /// evidence can validate the support relation without scanning the frame.
    pub(crate) fn has_supported_projection(
        &self,
        fact: &CResourceFact,
        support_occurrence: ResourceOccurrenceId,
        support: &CResourceFact,
    ) -> bool {
        self.storage
            .index
            .exact
            .get(fact)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .any(|entry| {
                self.storage.supported_by.get(entry) == Some(support)
                    && self.storage.support_occurrence_by_projection.get(entry)
                        == Some(&support_occurrence)
            })
    }

    /// The exact owned support recorded for a projected representation of
    /// `fact`, when that support occurrence is still held here.
    ///
    /// A supported projection is not an independent capability. It is an
    /// observation published from one exact owned occurrence, indexed under
    /// it, and dropped when that occurrence is consumed or its memory support
    /// is invalidated. Provenance decisions therefore use this record instead
    /// of asking whether some owner in the frame happens to satisfy the fact:
    /// an equal owner is not the owner a projection came from, and a view
    /// justified by equality alone would survive that owner's consumption.
    pub(crate) fn exact_projection_support(
        &self,
        fact: &CResourceFact,
    ) -> Option<(ResourceOccurrenceId, &CResourceFact)> {
        self.storage
            .index
            .exact
            .get(fact)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .find_map(|entry| {
                let support = self.storage.supported_by.get(entry)?;
                let support_occurrence = self
                    .storage
                    .support_occurrence_by_projection
                    .get(entry)
                    .copied()?;
                (support.is_own()
                    && self
                        .storage
                        .entry_by_occurrence
                        .get(&support_occurrence)
                        .is_some_and(|support_entry| {
                            self.storage.facts.get(support_entry) == Some(support)
                        }))
                .then_some((support_occurrence, support))
            })
    }

    /// Validate every projection indexed under one exact support occurrence.
    /// The reverse index bounds this check by the affected support rather than
    /// scanning unrelated resources in the frame.
    pub(crate) fn support_occurrence_is_live(
        &self,
        support_occurrence: ResourceOccurrenceId,
        support: &CResourceFact,
    ) -> bool {
        let Some(support_entry) = self.storage.entry_by_occurrence.get(&support_occurrence) else {
            return false;
        };
        if self.storage.facts.get(support_entry) != Some(support) || !support.is_own() {
            return false;
        }
        self.storage
            .projections_by_support_occurrence
            .get(&support_occurrence)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .all(|entry| {
                self.storage.facts.contains_key(entry)
                    && self.storage.supported_by.get(entry) == Some(support)
                    && self.storage.support_occurrence_by_projection.get(entry)
                        == Some(&support_occurrence)
            })
    }

    /// Drop memory-dependent projections whose exact support footprint is
    /// touched by a memory transition.  The transition is walked through the
    /// existing memory DAG; indexed block buckets bound the work to affected
    /// observations rather than the ambient resource frame.
    pub(crate) fn invalidate_memory_support(mut self, before: &CMemory, after: &CMemory) -> Self {
        if before.diagnostic_identity() == after.diagnostic_identity()
            || self.storage.support_metadata_by_projection.is_empty()
        {
            return self;
        }
        // A footprint's answer is spent removing a resource fact, which records
        // no premise, so the rule's footprint arm reads no fact context. Built
        // once here so the walk below pays nothing per step for it.
        let no_facts = PureFactContext::new();
        let evidence = crate::kernel::resource_tracker::step_effect::Evidence {
            assumptions: &no_facts,
            cross_loop_havoc: false,
        };
        let before_node = crate::kernel::intern_c_memory_ref(before);
        let mut current = crate::kernel::intern_c_memory_ref(after);
        let mut affected = ResourceEntryIds::default();
        let mut reached_before = false;
        loop {
            if current == before_node {
                reached_before = true;
                break;
            }
            let Some(derivation) = current.derivation() else {
                break;
            };
            let candidates = self.entries_affected_by_memory_derivation(&derivation);
            for occurrence in candidates.iter() {
                let Some(metadata) = self.storage.support_metadata_by_projection.get(occurrence)
                else {
                    continue;
                };
                if memory_derivation_affects_footprint(
                    &derivation,
                    &current,
                    &metadata.footprint,
                    &evidence,
                ) && let Some(entry) = self.storage.entry_by_occurrence.get(occurrence)
                {
                    affected = affected.with_value(*entry);
                }
            }
            current = derivation.base().clone();
        }
        if !reached_before {
            // A provenance barrier (for example an interface join) has no
            // typed write set.  Only memory-qualified projections are stale;
            // the entry index bounds this conservative cleanup.
            for occurrence in self.storage.support_metadata_by_projection.keys() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(entry) = self.storage.entry_by_occurrence.get(occurrence) {
                    affected = affected.with_value(*entry);
                }
            }
        }
        for entry in affected.iter().copied().collect::<Vec<_>>() {
            if self.storage.facts.contains_key(&entry) {
                self.remove_entry(entry);
            }
        }
        self
    }

    fn entries_affected_by_memory_derivation(
        &self,
        derivation: &CMemoryDerivation,
    ) -> ResourceOccurrenceIds {
        let mut entries = self.storage.unknown_memory_support.clone();
        entries = self
            .storage
            .symbolic_memory_support
            .iter()
            .fold(entries, |entries, occurrence| {
                entries.with_value(*occurrence)
            });
        let ambiguous_event = match derivation {
            CMemoryDerivation::Store { pointer, .. } => memory_block_may_alias(&pointer.block),
            CMemoryDerivation::CallHavoc { mutable_ranges, .. }
            | CMemoryDerivation::LoopHavoc {
                mutable_ranges: Some(mutable_ranges),
                ..
            } => mutable_ranges
                .iter()
                .any(|range| memory_block_may_alias(&range.base().block)),
            CMemoryDerivation::HeapFreed {
                allocation_base, ..
            }
            | CMemoryDerivation::ContractAllocationRetired {
                allocation_base, ..
            }
            | CMemoryDerivation::HeapAllocationPending {
                allocation_base, ..
            } => memory_block_may_alias(&allocation_base.block),
            CMemoryDerivation::LocalLifetimeEnded { block, .. } => memory_block_may_alias(block),
            CMemoryDerivation::LoopHavoc {
                mutable_ranges: None,
                ..
            }
            | CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. } => false,
        };
        if ambiguous_event {
            for occurrence in self.storage.support_metadata_by_projection.keys() {
                crate::instrumentation::record_deterministic_work(1);
                entries = entries.with_value(*occurrence);
            }
        }
        match derivation {
            CMemoryDerivation::Store { pointer, value, .. } => {
                let write = CMemoryRange::new_with_element_width(
                    pointer.clone(),
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                    value.byte_width(),
                );
                if memory_interval_nodes(&write).is_some() {
                    add_memory_interval_candidates(
                        &self.storage.projections_by_memory_interval,
                        &self.storage.projections_by_memory_interval_subtree,
                        &write,
                        &mut entries,
                    );
                } else if let Some(bucket) =
                    self.storage.projections_by_memory_block.get(&pointer.block)
                {
                    for occurrence in bucket.iter() {
                        entries = entries.with_value(*occurrence);
                    }
                }
            }
            CMemoryDerivation::CallHavoc { mutable_ranges, .. }
            | CMemoryDerivation::LoopHavoc {
                mutable_ranges: Some(mutable_ranges),
                ..
            } => {
                for range in mutable_ranges {
                    if memory_interval_nodes(range).is_some() {
                        add_memory_interval_candidates(
                            &self.storage.projections_by_memory_interval,
                            &self.storage.projections_by_memory_interval_subtree,
                            range,
                            &mut entries,
                        );
                    } else if let Some(bucket) = self
                        .storage
                        .projections_by_memory_block
                        .get(&range.base().block)
                    {
                        for occurrence in bucket.iter() {
                            entries = entries.with_value(*occurrence);
                        }
                    }
                }
            }
            CMemoryDerivation::HeapFreed {
                allocation_base,
                bytes,
                ..
            }
            | CMemoryDerivation::ContractAllocationRetired {
                allocation_base,
                bytes,
                ..
            } => {
                if let Some(byte_count) = bytes.as_const() {
                    let freed = CMemoryRange::new_with_element_width(
                        allocation_base.clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(byte_count),
                        1,
                    );
                    add_memory_interval_candidates(
                        &self.storage.projections_by_memory_interval,
                        &self.storage.projections_by_memory_interval_subtree,
                        &freed,
                        &mut entries,
                    );
                } else if let Some(bucket) = self
                    .storage
                    .projections_by_memory_block
                    .get(&allocation_base.block)
                {
                    for occurrence in bucket.iter() {
                        entries = entries.with_value(*occurrence);
                    }
                }
            }
            CMemoryDerivation::LoopHavoc {
                mutable_ranges: None,
                ..
            } => {
                // An interface loop barrier has no checked write set.  It
                // invalidates every memory-dependent projection, including
                // exact ones, but leaves pure observations alone.
                for occurrence in self.storage.support_metadata_by_projection.keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    entries = entries.with_value(*occurrence);
                }
            }
            CMemoryDerivation::LocalLifetimeEnded { block, .. } => {
                if memory_block_may_alias(block) {
                    for occurrence in self.storage.support_metadata_by_projection.keys() {
                        crate::instrumentation::record_deterministic_work(1);
                        entries = entries.with_value(*occurrence);
                    }
                } else if let Some(bucket) = self.storage.projections_by_memory_block.get(block) {
                    for occurrence in bucket.iter() {
                        entries = entries.with_value(*occurrence);
                    }
                }
            }
            CMemoryDerivation::BlockDeclared { .. }
            | CMemoryDerivation::HeapAllocated { .. }
            | CMemoryDerivation::HeapAllocationPending { .. }
            | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
            | CMemoryDerivation::CellsForgotten { .. } => {}
        }
        entries
    }

    pub(crate) fn proves_owned_resources_separate(
        &self,
        left: &CResource,
        right: &CResource,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter(
            CompositionQuery::ResourcesSeparate(left.clone(), right.clone()),
        ) else {
            return false;
        };
        let left_view = CResourceFact::View(left.clone());
        let right_view = CResourceFact::View(right.clone());
        let Some(left_positions) = self.direct_match_candidate_positions(&left_view) else {
            return false;
        };
        let Some(right_positions) = self.direct_match_candidate_positions(&right_view) else {
            return false;
        };
        left_positions.iter().any(|left_entry| {
            self.fact(*left_entry).is_own()
                && resource_fact_entails(self.fact(*left_entry), &left_view, assumptions)
                && right_positions.iter().any(|right_entry| {
                    left_entry != right_entry
                        && self.fact(*right_entry).is_own()
                        && resource_fact_entails(self.fact(*right_entry), &right_view, assumptions)
                })
        })
    }

    /// The owned memory fact of this composition that structurally contains
    /// `range`, as its entry and its own range.
    ///
    /// One block bucket, structural containment only: this cannot re-enter
    /// snapshot or alias reasoning. Two lookups decide the composition law
    /// for a pair without materializing any pair.
    fn owned_memory_member_containing(
        &self,
        range: &CMemoryRange,
    ) -> Option<(ResourceEntryId, &CMemoryRange)> {
        self.storage
            .index
            .memory_by_block
            .get(&range.base().block)?
            .iter()
            .copied()
            .find_map(|entry| {
                let available = self.fact(entry).memory_own_range()?;
                crate::kernel::assumptions::memory_range_shallowly_contained(range, available)
                    .then_some((entry, available))
            })
    }

    /// The owned memory fact of this composition that structurally contains
    /// `pointer`, as its entry and its own range.
    pub(in crate::kernel) fn owned_memory_member_containing_pointer(
        &self,
        pointer: &Pointer,
    ) -> Option<(ResourceEntryId, &CMemoryRange)> {
        self.storage
            .index
            .memory_by_block
            .get(&pointer.block)?
            .iter()
            .copied()
            .find_map(|entry| {
                let available = self.fact(entry).memory_own_range()?;
                crate::kernel::assumptions::pointer_in_memory_range_shallow(pointer, available)
                    .then_some((entry, available))
            })
    }

    /// Non-recursive projection for memory-resolution fast paths. It uses
    /// only block indexing and structural containment, so it cannot re-enter
    /// snapshot or alias reasoning.
    ///
    /// Each side is looked up in its own block's bucket. Two owned members of
    /// one valid composition hold disjoint *bytes* — the partition invariant
    /// `MemoryResourceAlgebra::pair_validity_error` enforces — and a byte set
    /// does not depend on how the pointer that names it is spelled, so the
    /// law answers a cross-block pair exactly as it answers a same-block one.
    /// Restricting it to one bucket would have been an indexing shortcut with
    /// no rule behind it, and it is precisely the pair the kernel cannot
    /// spell apart — an unresolved `Symbolic` pointer beside a named object —
    /// that the shortcut refused.
    pub(in crate::kernel) fn proves_owned_memory_ranges_separate_shallow(
        &self,
        left: &CMemoryRange,
        right: &CMemoryRange,
    ) -> bool {
        if string_literal_blocks_may_alias(&left.base().block, &right.base().block) {
            return false;
        }
        let Some((left_position, _)) = self.owned_memory_member_containing(left) else {
            return false;
        };
        let Some(positions) = self.storage.index.memory_by_block.get(&right.base().block) else {
            return false;
        };
        positions.iter().copied().any(|entry| {
            entry != left_position
                && self
                    .fact(entry)
                    .memory_own_range()
                    .is_some_and(|available| {
                        crate::kernel::assumptions::memory_range_shallowly_contained(
                            right, available,
                        )
                    })
        })
    }

    pub(in crate::kernel) fn proves_owned_pointers_separate_shallow(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> bool {
        if left.block != right.block {
            return false;
        }
        let Some(positions) = self.storage.index.memory_by_block.get(&left.block) else {
            return false;
        };
        let containing = |pointer: &Pointer| {
            positions.iter().copied().find(|entry| {
                self.fact(*entry).memory_own_range().is_some_and(|range| {
                    crate::kernel::assumptions::pointer_in_memory_range_shallow(pointer, range)
                })
            })
        };
        containing(left)
            .zip(containing(right))
            .is_some_and(|(left, right)| left != right)
    }

    /// The same-block separation candidates this valid composition supports:
    /// one entry per unordered pair of distinct owned memory facts sharing a
    /// block, skipping pairs the kernel proves separate from their
    /// constructors alone and blocks whose ranges all share one concrete
    /// base. These are exactly the pair propositions the composition used to
    /// materialize eagerly, now projected on demand.
    ///
    /// A block with one owned range has no pair, so only the blocks the index
    /// records as holding two or more are visited, each in entry order.
    pub(in crate::kernel) fn same_block_separation_candidates(
        &self,
    ) -> Vec<(Proposition, CMemoryRange, CMemoryRange)> {
        crate::instrumentation::record_deterministic_work(1);
        let by_block = self
            .storage
            .index
            .shared_owned_memory_blocks
            .keys()
            .map(|block| {
                self.storage
                    .index
                    .owned_memory_by_block
                    .get(block)
                    .into_iter()
                    .flat_map(ResourceEntryIds::iter)
                    .filter_map(|entry| self.fact(*entry).memory_own_range())
                    .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut entries = Vec::new();
        for owned in &by_block {
            let one_concrete_base = owned.first().is_some_and(|first| {
                owned.iter().all(|range| {
                    range.base() == first.base()
                        && range.start().as_const().is_some()
                        && range.end().as_const().is_some()
                })
            });
            if one_concrete_base {
                // Validity already established that these ordered intervals
                // do not overlap, and the kernel proves their concrete
                // separation without a premise.
                continue;
            }
            for (position, left) in owned.iter().enumerate() {
                for right in &owned[position + 1..] {
                    crate::instrumentation::record_deterministic_work(1);
                    let left_resource = CResource::Memory((*left).clone());
                    let right_resource = CResource::Memory((*right).clone());
                    if resources_structurally_separate(&left_resource, &right_resource) {
                        continue;
                    }
                    entries.push((
                        Proposition::CResourceSeparate {
                            left: left_resource,
                            right: right_resource,
                        },
                        (*left).clone(),
                        (*right).clone(),
                    ));
                }
            }
        }
        entries
    }

    /// Pointer projection using an explicitly bounded caller-supplied
    /// containment relation. The context contributes only indexed candidates,
    /// so callers can recognize shallow equality forms without expanding
    /// all owned pairs.
    /// Range projection using a caller-supplied proof-aware containment
    /// relation: two distinct owned facts of one valid composition are
    /// separate by the composition law, so a range each of them provably
    /// contains inherits that separation. This is the on-demand form of the
    /// former materialized pair facts for range queries; the context
    /// contributes only indexed candidates, and the caller decides
    /// containment.
    pub(in crate::kernel) fn proves_owned_memory_ranges_separate_by(
        &self,
        left: &CMemoryRange,
        right: &CMemoryRange,
        contains: impl Fn(&CMemoryRange, &CMemoryRange) -> bool,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter(CompositionQuery::RangesSeparate(
            left.clone(),
            right.clone(),
        )) else {
            return false;
        };
        if left.base().block != right.base().block {
            return false;
        }
        let Some(positions) = self.storage.index.memory_by_block.get(&left.base().block) else {
            return false;
        };
        let containing = |child: &CMemoryRange| {
            positions.iter().copied().find(|entry| {
                self.fact(*entry)
                    .memory_own_range()
                    .is_some_and(|available| contains(child, available))
            })
        };
        containing(left)
            .zip(containing(right))
            .is_some_and(|(left_position, right_position)| left_position != right_position)
    }

    /// Returns the owned memory members that are distinct from every owned
    /// resource containing `other`. A caller can use the returned members to
    /// cover a larger queried range without enumerating all member pairs.
    pub(in crate::kernel) fn owned_memory_ranges_separate_from(
        &self,
        block: &PointerBlock,
        other: &CResource,
        contains: impl Fn(&CResource, &CResource) -> bool,
    ) -> Vec<CMemoryRange> {
        let facts = self.iter().collect::<Vec<_>>();
        let excluded = facts
            .iter()
            .enumerate()
            .filter_map(|(index, fact)| {
                (fact.is_own() && contains(fact.resource(), other)).then_some(index)
            })
            .collect::<BTreeSet<_>>();
        if excluded.is_empty() {
            return Vec::new();
        }
        facts
            .iter()
            .enumerate()
            .filter_map(|(index, fact)| {
                if excluded.contains(&index) || !fact.is_own() {
                    return None;
                }
                let range = fact.memory_own_range()?;
                (range.base().block == *block).then_some(range.clone())
            })
            .collect()
    }

    pub(in crate::kernel) fn proves_owned_pointers_separate_by(
        &self,
        left: &Pointer,
        right: &Pointer,
        contains: impl Fn(&Pointer, &CMemoryRange) -> bool,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter(
            CompositionQuery::PointersSeparate(left.clone(), right.clone()),
        ) else {
            return false;
        };
        if left.block != right.block {
            return false;
        }
        let Some(positions) = self.storage.index.memory_by_block.get(&left.block) else {
            return false;
        };
        let containing = |pointer: &Pointer| {
            positions.iter().copied().find(|entry| {
                self.fact(*entry)
                    .memory_own_range()
                    .is_some_and(|range| contains(pointer, range))
            })
        };
        containing(left)
            .zip(containing(right))
            .is_some_and(|(left, right)| left != right)
    }

    /// Projects separation between a structurally identified owned range and
    /// a pointer identified by a caller's bounded shallow fact graph. This is
    /// the mixed query used while deciding which memory facts survive a
    /// store; it avoids materializing every pair in the composition.
    pub(in crate::kernel) fn proves_owned_range_separate_from_pointer_shallow(
        &self,
        range: &CMemoryRange,
        pointer: &Pointer,
        contains_pointer: impl Fn(&Pointer, &CMemoryRange) -> bool,
    ) -> bool {
        self.proves_owned_range_separate_from_pointer_with(
            range,
            pointer,
            crate::kernel::assumptions::memory_range_shallowly_contained,
            contains_pointer,
        )
    }

    /// As [`Self::proves_owned_range_separate_from_pointer_shallow`], with
    /// the caller's bounded relation deciding when `range` lies inside an
    /// owned member (a frame check may decide the endpoints from indexed
    /// bounds rather than by constant difference alone).
    pub(in crate::kernel) fn proves_owned_range_separate_from_pointer_with(
        &self,
        range: &CMemoryRange,
        pointer: &Pointer,
        range_contained: impl Fn(&CMemoryRange, &CMemoryRange) -> bool,
        contains_pointer: impl Fn(&Pointer, &CMemoryRange) -> bool,
    ) -> bool {
        if range.base().block != pointer.block {
            return false;
        }
        let Some(positions) = self.storage.index.memory_by_block.get(&pointer.block) else {
            return false;
        };
        let range_position = positions.iter().copied().find(|entry| {
            self.fact(*entry)
                .memory_own_range()
                .is_some_and(|available| range_contained(range, available))
        });
        let Some(range_position) = range_position else {
            return false;
        };
        positions.iter().copied().any(|entry| {
            entry != range_position
                && self
                    .fact(entry)
                    .memory_own_range()
                    .is_some_and(|available| contains_pointer(pointer, available))
        })
    }

    /// Refutes one offset-alias guard from this composition without expanding
    /// all memory pairs. Each block bucket is searched twice for the two
    /// containing owned members; the caller supplies the bounded shallow
    /// membership relation used by contradiction checking.
    pub(in crate::kernel) fn refutes_offset_alias(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
        contains: impl Fn(&Pointer, &CMemoryRange) -> bool,
    ) -> bool {
        self.storage
            .index
            .memory_by_block
            .iter()
            .any(|(block, entries)| {
                let containing = |offset: &PointerOffsetTerm| {
                    entries.iter().copied().find(|entry| {
                        self.fact(*entry).memory_own_range().is_some_and(|range| {
                            contains(
                                &Pointer {
                                    block: block.clone(),
                                    offset: offset.clone(),
                                },
                                range,
                            )
                        })
                    })
                };
                containing(left)
                    .zip(containing(right))
                    .is_some_and(|(left, right)| left != right)
            })
    }

    fn direct_match_candidate_positions(&self, fact: &CResourceFact) -> Option<&ResourceEntryIds> {
        match fact.resource() {
            CResource::Instance(instance) => self.storage.index.instances.get(&instance.identity),
            CResource::Memory(range) => self.storage.index.memory_by_block.get(&range.base().block),
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => self
                .storage
                .index
                .exact_shapes
                .get(&(fact.family(), name.clone(), arguments.len())),
        }
    }

    /// Adds a resource fact without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_fact` when proposition assumptions are
    /// available.
    pub fn unchecked_with_fact(mut self, fact: CResourceFact) -> Self {
        self.insert_fact(fact);
        self
    }

    /// Adds resource facts without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_facts` when proposition assumptions are
    /// available.
    pub fn unchecked_with_facts(mut self, facts: impl IntoIterator<Item = CResourceFact>) -> Self {
        for fact in facts {
            self.insert_fact(fact);
        }
        self
    }

    pub(crate) fn unchecked_with_facts_and_occurrences(
        mut self,
        facts: impl IntoIterator<Item = CResourceFact>,
    ) -> (Self, Vec<(CResourceFact, ResourceOccurrenceId)>) {
        let mut inserted = Vec::new();
        for fact in facts {
            let entry = self.storage.next_entry_id;
            self.insert_fact(fact.clone());
            inserted.push((fact, self.occurrence(entry)));
        }
        (self, inserted)
    }

    /// Adds duplicable views derived from one exact owned resource.
    ///
    /// The reverse support index makes later removal proportional to the
    /// projections of this authority rather than the size of the context.
    #[allow(dead_code)]
    pub(crate) fn unchecked_with_supported_facts(
        self,
        support: &CResourceFact,
        facts: impl IntoIterator<Item = CResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert!(self.storage.index.exact.contains_key(support));
        let support_entry =
            self.unique_owned_occurrence_for_fact(support)
                .map(|(occurrence, _)| {
                    self.storage
                        .entry_by_occurrence
                        .get(&occurrence)
                        .copied()
                        .expect("owned occurrence must refer to a live entry")
                });
        self.unchecked_with_supported_facts_from_entry(
            support_entry.expect("supported projections require an owned support entry"),
            support,
            facts,
        )
    }

    #[allow(dead_code)]
    pub(crate) fn unchecked_with_supported_facts_from_entry(
        self,
        support_entry: ResourceEntryId,
        support: &CResourceFact,
        facts: impl IntoIterator<Item = CResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert_eq!(self.fact(support_entry), support);
        let support_occurrence = self.occurrence(support_entry);
        self.unchecked_with_supported_facts_from_occurrence(support_occurrence, support, facts)
    }

    pub(crate) fn unchecked_with_supported_facts_from_occurrence(
        mut self,
        support_occurrence: ResourceOccurrenceId,
        support: &CResourceFact,
        facts: impl IntoIterator<Item = CResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert!(
            self.storage
                .entry_by_occurrence
                .get(&support_occurrence)
                .is_some_and(|entry| self.fact(*entry) == support)
        );
        for fact in facts {
            debug_assert!(fact.is_view());
            self.insert_fact_with_support_occurrence(
                fact,
                Some(support.clone()),
                Some(support_occurrence),
            );
        }
        self
    }

    /// Adds observation projections while recording the memory snapshot and
    /// exact footprint used to derive each one.  This is the memory-aware
    /// counterpart to the legacy support-only API used by call packaging.
    pub(crate) fn unchecked_with_supported_facts_from_occurrence_with_memory(
        self,
        support_occurrence: ResourceOccurrenceId,
        support: &CResourceFact,
        facts: impl IntoIterator<Item = CResourceFact>,
        memory: &CMemory,
    ) -> Self {
        self.unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
            support_occurrence,
            support,
            facts,
            memory,
        )
        .0
    }

    pub(crate) fn unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
        mut self,
        support_occurrence: ResourceOccurrenceId,
        support: &CResourceFact,
        facts: impl IntoIterator<Item = CResourceFact>,
        memory: &CMemory,
    ) -> (Self, Vec<(CResourceFact, ResourceOccurrenceId)>) {
        debug_assert!(support.is_own());
        debug_assert!(
            self.storage
                .entry_by_occurrence
                .get(&support_occurrence)
                .is_some_and(|entry| self.fact(*entry) == support)
        );
        let memory_snapshot = CMemorySnapshotIdentity::of(memory);
        let mut inserted = Vec::new();
        for fact in facts {
            debug_assert!(fact.is_view());
            let entry = self.storage.next_entry_id;
            let metadata = ResourceSupportMetadata {
                memory_snapshot,
                footprint: memory_footprint_for_fact(&fact),
            };
            self.insert_fact_with_support_occurrence_and_metadata(
                fact.clone(),
                Some(support.clone()),
                Some(support_occurrence),
                Some(metadata),
            );
            inserted.push((fact, self.occurrence(entry)));
        }
        (self, inserted)
    }

    #[allow(dead_code)]
    pub(crate) fn with_cached_supported_expansion(
        self,
        support: &CResourceFact,
        expansion: Vec<CResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert!(self.storage.index.exact.contains_key(support));
        let (support_occurrence, _) = self
            .unique_owned_occurrence_for_fact(support)
            .expect("cached expansions require one unambiguous owned support entry");
        self.with_cached_supported_expansion_for_occurrence(support_occurrence, support, expansion)
    }

    pub(crate) fn with_cached_supported_expansion_for_occurrence(
        mut self,
        support_occurrence: ResourceOccurrenceId,
        support: &CResourceFact,
        expansion: Vec<CResourceFact>,
    ) -> Self {
        debug_assert!(
            self.storage
                .entry_by_occurrence
                .get(&support_occurrence)
                .is_some_and(|entry| self.fact(*entry) == support)
        );
        let expansion = std::sync::Arc::new(expansion);
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.clone(),
            next_entry_id: self.storage.next_entry_id,
            occurrence_by_entry: self.storage.occurrence_by_entry.clone(),
            entry_by_occurrence: self.storage.entry_by_occurrence.clone(),
            index: self.storage.index.clone(),
            supported_by: self.storage.supported_by.clone(),
            support_occurrence_by_projection: self.storage.support_occurrence_by_projection.clone(),
            projections_by_support: self.storage.projections_by_support.clone(),
            projections_by_support_occurrence: self
                .storage
                .projections_by_support_occurrence
                .clone(),
            support_metadata_by_projection: self.storage.support_metadata_by_projection.clone(),
            projections_by_memory_block: self.storage.projections_by_memory_block.clone(),
            projections_by_memory_interval: self.storage.projections_by_memory_interval.clone(),
            projections_by_memory_interval_subtree: self
                .storage
                .projections_by_memory_interval_subtree
                .clone(),
            symbolic_memory_support: self.storage.symbolic_memory_support.clone(),
            unknown_memory_support: self.storage.unknown_memory_support.clone(),
            expansions_by_support_occurrence: self
                .storage
                .expansions_by_support_occurrence
                .with_inserted(support_occurrence, expansion.clone()),
            expansions_by_support_entry: self.storage.expansions_by_support_entry.clone(),
            origin: self.storage.origin.clone(),
            history: Some(std::sync::Arc::new(ResourceContextChange {
                fact: support.clone(),
                parent: self.storage.history.clone(),
            })),
            materialized: std::sync::OnceLock::new(),
        });
        self.rekey_cached_support_entries(support);
        self
    }

    #[allow(dead_code)]
    pub(crate) fn cached_supported_expansion(
        &self,
        support: &CResourceFact,
    ) -> Option<&[CResourceFact]> {
        self.cached_expansion_for_fact(support)
            .map(|expansion| expansion.as_slice())
    }

    /// Return every cached expansion attached to an exact support occurrence.
    /// Fact-only lookup is intentionally plural: equal authorities may carry
    /// distinct folded snapshots and silently selecting one would discard the
    /// other authority's evidence.
    pub(crate) fn cached_supported_expansions(
        &self,
        support: &CResourceFact,
    ) -> Vec<(ResourceOccurrenceId, Vec<CResourceFact>)> {
        self.storage
            .index
            .exact
            .get(support)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter_map(|entry| {
                self.storage
                    .expansions_by_support_occurrence
                    .get(&self.occurrence(*entry))
                    .map(|expansion| (self.occurrence(*entry), expansion.as_ref().clone()))
            })
            .collect()
    }

    fn cached_expansion_for_fact(
        &self,
        support: &CResourceFact,
    ) -> Option<&std::sync::Arc<Vec<CResourceFact>>> {
        self.cached_expansion_with_occurrence_for_fact(support)
            .map(|(_, expansion)| expansion)
    }

    fn cached_expansion_with_occurrence_for_fact(
        &self,
        support: &CResourceFact,
    ) -> Option<(ResourceOccurrenceId, &std::sync::Arc<Vec<CResourceFact>>)> {
        let mut matches = self
            .storage
            .index
            .exact
            .get(support)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter_map(|entry| {
                self.storage
                    .expansions_by_support_occurrence
                    .get(&self.occurrence(*entry))
                    .map(|expansion| (self.occurrence(*entry), expansion))
            });
        let result = matches.next()?;
        matches.next().is_none().then_some(result)
    }

    fn without_cached_supported_expansion_for_occurrence(
        mut self,
        occurrence: ResourceOccurrenceId,
    ) -> Self {
        let support_entry = *self
            .storage
            .entry_by_occurrence
            .get(&occurrence)
            .expect("cached expansion occurrence must be live");
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.clone(),
            next_entry_id: self.storage.next_entry_id,
            occurrence_by_entry: self.storage.occurrence_by_entry.clone(),
            entry_by_occurrence: self.storage.entry_by_occurrence.clone(),
            index: self.storage.index.clone(),
            supported_by: self.storage.supported_by.clone(),
            support_occurrence_by_projection: self.storage.support_occurrence_by_projection.clone(),
            projections_by_support: self.storage.projections_by_support.clone(),
            projections_by_support_occurrence: self
                .storage
                .projections_by_support_occurrence
                .clone(),
            support_metadata_by_projection: self.storage.support_metadata_by_projection.clone(),
            projections_by_memory_block: self.storage.projections_by_memory_block.clone(),
            projections_by_memory_interval: self.storage.projections_by_memory_interval.clone(),
            projections_by_memory_interval_subtree: self
                .storage
                .projections_by_memory_interval_subtree
                .clone(),
            symbolic_memory_support: self.storage.symbolic_memory_support.clone(),
            unknown_memory_support: self.storage.unknown_memory_support.clone(),
            expansions_by_support_occurrence: self
                .storage
                .expansions_by_support_occurrence
                .without_key(&occurrence),
            expansions_by_support_entry: self.storage.expansions_by_support_entry.clone(),
            origin: self.storage.origin.clone(),
            history: self.storage.history.clone(),
            materialized: std::sync::OnceLock::new(),
        });
        let support = self.fact(support_entry).clone();
        self.rekey_cached_support_entries(&support);
        self
    }

    pub(crate) fn without_exact_representation_for_occurrence(
        mut self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<Self> {
        let entry = *self.storage.entry_by_occurrence.get(&occurrence)?;
        self.remove_entry(entry);
        Some(self)
    }

    /// Finds an owned support whose certified expansion contains `target`.
    ///
    /// The exact core projection is the forward index into the support
    /// relation. This avoids comparing every same-shaped resource through
    /// snapshot equality merely to rediscover a folded resource's already
    /// certified body.
    pub(crate) fn cached_support_exposing_fact(
        &self,
        target: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<&CResourceFact> {
        let core = target.core_with_assumptions(assumptions)?;
        let entries = self.storage.index.exact.get(&core)?;
        entries
            .iter()
            .filter_map(|entry| {
                let support = self.storage.supported_by.get(entry)?;
                let support_occurrence =
                    self.storage.support_occurrence_by_projection.get(entry)?;
                self.storage
                    .expansions_by_support_occurrence
                    .get(support_occurrence)
                    .filter(|expansion| expansion.iter().any(|fact| fact == target))
                    .map(|_| support)
            })
            .next()
    }

    pub fn try_compose_with_fact(
        self,
        fact: CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts(std::iter::once(fact), assumptions)
    }

    pub fn try_compose_with_facts(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts_delaying_normalization(facts, assumptions)
            .map(|context| context.normalized(assumptions))
    }

    pub(crate) fn try_compose_with_facts_delaying_normalization(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts_delaying_normalization_with_occurrences(facts, assumptions)
            .map(|(context, _)| context)
    }

    /// Compose facts while retaining the exact occurrence allocated for each
    /// input. Callers that publish derived projections must use this relation
    /// instead of rediscovering a support by its fact value: an equal caller
    /// authority may already be live in the destination context.
    pub(crate) fn try_compose_with_facts_delaying_normalization_with_occurrences(
        mut self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(CResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        let mut inserted = Vec::new();
        for fact in facts {
            let entry = self.storage.next_entry_id;
            self.insert_fact(fact.clone());
            inserted.push((fact, self.occurrence(entry)));
        }
        let context = self;
        if let Some(error) = context.validity_error(assumptions) {
            return Err(error);
        }
        Ok((context, inserted))
    }

    pub(crate) fn try_compose_with_fact_with_occurrence(
        self,
        fact: CResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Option<ResourceOccurrenceId>), ResourceContextValidityError> {
        let (context, mut inserted) = self
            .try_compose_with_facts_delaying_normalization_with_occurrences(
                std::iter::once(fact.clone()),
                assumptions,
            )?;
        let occurrence = inserted.pop().map(|(_, occurrence)| occurrence);
        let context = context.normalized(assumptions);
        let occurrence = occurrence.filter(|occurrence| {
            context
                .storage
                .entry_by_occurrence
                .get(occurrence)
                .is_some_and(|entry| context.storage.facts.get(entry) == Some(&fact))
        });
        Ok((context, occurrence))
    }

    /// Extends a context whose validity has already been checked, validating
    /// only pairs that contain at least one newly added fact.
    pub(crate) fn try_compose_into_valid_context_delaying_normalization(
        mut self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        let first_new = self.storage.next_entry_id;
        for fact in facts {
            self.insert_fact(fact);
        }
        for right_entry in first_new..self.storage.next_entry_id {
            let right = self.fact(right_entry);
            if let Some(error) = self.instance_validity_error(right) {
                return Err(error);
            }
            let Some(right_range) = right.memory_own_range() else {
                continue;
            };
            // Same-block ranges are selected below. Exact pointer equalities
            // also connect bases across blocks, so check only the entries at
            // each directly stated alias using the exact-base index.
            for alias in assumptions.exact_pointer_aliases(right_range.base()) {
                if alias.block == right_range.base().block {
                    continue;
                }
                if let Some(entries) = self.storage.index.memory_by_base.get(alias) {
                    for left_entry in entries.iter().copied().filter(|entry| *entry < right_entry) {
                        crate::instrumentation::record_deterministic_work(1);
                        let left = self.fact(left_entry);
                        if let Some(error) = resource_family_algebra(left.family())
                            .pair_validity_error(left, right, assumptions)
                        {
                            return Err(error);
                        }
                    }
                }
            }
            let (start, end) = signed_range_endpoints(right_range);
            let same_base_concrete = start.zip(end).and_then(|(start, end)| {
                let owned_in_block = self
                    .storage
                    .index
                    .owned_memory_by_block
                    .get(&right_range.base().block)?
                    .len();
                let represented = *self
                    .storage
                    .index
                    .concrete_memory_by_base
                    .get(&(right_range.base().clone(), true))?;
                (represented == owned_in_block).then_some((start, end))
            });
            if let Some((start, end)) = same_base_concrete {
                let key = (right_range.base().clone(), true, start, end);
                let mut candidates = BTreeSet::new();
                if let Some(duplicates) = self.storage.index.concrete_memory.get(&key) {
                    candidates.extend(
                        duplicates
                            .iter()
                            .copied()
                            .filter(|entry| *entry != right_entry),
                    );
                }
                if let Some((candidate_key, entries)) =
                    self.storage.index.concrete_memory.get_less_than(&key)
                    && candidate_key.0 == key.0
                    && candidate_key.1 == key.1
                    && let Some(entry) = entries.iter().next_back()
                {
                    candidates.insert(*entry);
                }
                if let Some((candidate_key, entries)) =
                    self.storage.index.concrete_memory.get_greater_than(&key)
                    && candidate_key.0 == key.0
                    && candidate_key.1 == key.1
                    && let Some(entry) = entries.iter().next()
                {
                    candidates.insert(*entry);
                }
                for left_entry in candidates {
                    crate::instrumentation::record_deterministic_work(1);
                    let left = self.fact(left_entry);
                    if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                        left,
                        right,
                        assumptions,
                    ) {
                        return Err(error);
                    }
                }
                continue;
            }
            for left_entry in self
                .storage
                .index
                .memory_by_block
                .get(&right_range.base().block)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .copied()
                .take_while(|entry| *entry != right_entry)
            {
                crate::instrumentation::record_deterministic_work(1);
                let left = self.fact(left_entry);
                if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                    left,
                    right,
                    assumptions,
                ) {
                    return Err(error);
                }
            }
        }
        Ok(self)
    }

    /// Extends a valid context with one already-certified valid resource
    /// group, checking only pairs that cross the group boundary.
    ///
    /// Composite expansion checks its children together before caching the
    /// group. Rechecking child/child pairs when that expansion is later
    /// installed can recursively rediscover snapshot and range separation
    /// through an unrelated call history. Only a conflict with the existing
    /// caller frame is new information at installation time.
    pub(crate) fn try_compose_certified_group_into_valid_context_delaying_normalization(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_certified_group_into_valid_context_delaying_normalization_with_occurrences(
            facts,
            assumptions,
        )
        .map(|(context, _)| context)
    }

    pub(crate) fn try_compose_certified_group_into_valid_context_delaying_normalization_with_occurrences(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(CResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        let facts = facts.into_iter().collect::<Vec<_>>();
        for fact in &facts {
            self.clone()
                .try_compose_into_valid_context_delaying_normalization(
                    std::iter::once(fact.clone()),
                    assumptions,
                )?;
        }
        Ok(self.unchecked_with_facts_and_occurrences(facts))
    }

    pub fn facts(&self) -> &[CResourceFact] {
        self.storage
            .materialized
            .get_or_init(|| self.iter().cloned().collect())
    }

    pub fn validity_error(
        &self,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        for (_, entries) in self.storage.index.instances.iter() {
            for entry in entries.iter() {
                if let Some(error) = self.instance_validity_error(self.fact(*entry)) {
                    return Some(error);
                }
            }
        }
        for (_, entries) in self.storage.index.memory_by_block.iter() {
            let owned = entries
                .iter()
                .filter_map(|entry| {
                    let fact = self.fact(*entry);
                    fact.memory_own_range().map(|range| (fact, range))
                })
                .collect::<Vec<_>>();
            // The sweep replaces the pairwise scan below, and it is sound
            // only on the order it assumes. Sorted by *signed* start, an
            // overlap with any earlier range is an overlap with the earlier
            // range of greatest end, so comparing each range against that one
            // decides the whole block. Sorted by the `u32` bit pattern, a
            // range starting below its base sorts past every range there is:
            // `p[-1..1]` beside `p[0..2]` and a decoy `p[5..6]` was compared
            // only against the decoy, and two owners of element `p[0]` — the
            // partition violation the whole resource model rests on — were
            // admitted. Both endpoints, and the running maximum, are the
            // signed numbers they are.
            let one_concrete_base = owned.first().map(|(_, range)| range.base()).filter(|base| {
                owned.iter().all(|(_, range)| {
                    let (start, end) = signed_range_endpoints(range);
                    range.base() == *base && start.is_some() && end.is_some()
                })
            });
            if one_concrete_base.is_some() {
                let mut ordered = owned
                    .into_iter()
                    .map(|(fact, range)| {
                        let (start, end) = signed_range_endpoints(range);
                        (start.unwrap(), end.unwrap(), fact, range)
                    })
                    .collect::<Vec<_>>();
                ordered.sort_by_key(|(start, end, _, _)| (*start, *end));
                let mut furthest: Option<(i64, &CResourceFact)> = None;
                for (_, end, fact, _) in ordered {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some((furthest_end, left)) = furthest {
                        if let Some(error) = resource_family_algebra(left.family())
                            .pair_validity_error(left, fact, assumptions)
                        {
                            return Some(error);
                        }
                        if end > furthest_end {
                            furthest = Some((end, fact));
                        }
                    } else {
                        furthest = Some((end, fact));
                    }
                }
                continue;
            }
            let entries = entries.iter().copied().collect::<Vec<_>>();
            for (offset, left_entry) in entries.iter().enumerate() {
                let left = self.fact(*left_entry);
                if left.memory_own_range().is_none() {
                    continue;
                }
                for right_entry in &entries[offset + 1..] {
                    crate::instrumentation::record_deterministic_work(1);
                    let right = self.fact(*right_entry);
                    if right.memory_own_range().is_none() {
                        continue;
                    }
                    if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                        left,
                        right,
                        assumptions,
                    ) {
                        return Some(error);
                    }
                }
            }
        }

        // The block sweep above covers every same-block pair. Visit the
        // output-sized set of exact-base matches for direct cross-block
        // pointer equalities separately.
        for (_, entries) in self.storage.index.memory_by_base.iter() {
            for entry in entries.iter().copied() {
                let Some(range) = self.fact(entry).memory_own_range() else {
                    continue;
                };
                for alias in assumptions.exact_pointer_aliases(range.base()) {
                    if alias.block == range.base().block {
                        continue;
                    }
                    let Some(alias_entries) = self.storage.index.memory_by_base.get(alias) else {
                        continue;
                    };
                    for alias_entry in alias_entries.iter().copied() {
                        // Exact aliases are indexed symmetrically, so the
                        // lower entry id owns this pair's one comparison.
                        if entry >= alias_entry {
                            continue;
                        }
                        let left = self.fact(entry);
                        let right = self.fact(alias_entry);
                        if left.memory_own_range().is_none() || right.memory_own_range().is_none() {
                            continue;
                        }
                        crate::instrumentation::record_deterministic_work(1);
                        if let Some(error) = resource_family_algebra(left.family())
                            .pair_validity_error(left, right, assumptions)
                        {
                            return Some(error);
                        }
                    }
                }
            }
        }
        None
    }

    pub fn is_valid(&self, assumptions: &PureFactContext) -> bool {
        self.validity_error(assumptions).is_none()
    }

    pub fn observable_facts(
        &self,
        assumptions: &PureFactContext,
    ) -> Result<Vec<Proposition>, ResourceContextValidityError> {
        if let Some(error) = self.validity_error(assumptions) {
            return Err(error);
        }
        Ok(self.observable_facts_assuming_valid(assumptions))
    }

    /// Projects facts from a resource composition whose validity has already
    /// been established by an enclosing resource law.
    pub(crate) fn observable_facts_assuming_valid(
        &self,
        assumptions: &PureFactContext,
    ) -> Vec<Proposition> {
        let mut propositions = Vec::new();
        let memory_facts = self
            .iter()
            .filter(|fact| fact.family() == ResourceFamily::Memory)
            .collect::<Vec<_>>();
        propositions.extend(MEMORY_RESOURCE_ALGEBRA.observable_facts(&memory_facts, assumptions));
        // Two owned members are pairwise separate, and one owned composite
        // expands to several: either way the composition is what a frame
        // check consults for ownership-derived disjointness.
        let owned = self.iter().filter(|fact| fact.is_own());
        let owned_composite = self
            .iter()
            .any(|fact| fact.is_own() && matches!(fact.resource(), CResource::Composite { .. }));
        if owned.count() >= 2 || owned_composite {
            propositions.push(Proposition::CResourceComposition(self.clone()));
        }
        propositions
    }

    pub fn satisfies_fact(&self, fact: &CResourceFact, assumptions: &PureFactContext) -> bool {
        if !fact.has_valid_instance_access() {
            return false;
        }
        if fact
            .owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
        {
            return true;
        }
        if self.storage.index.exact.contains_key(fact) {
            return true;
        }
        // Exact ownership of a resource definitionally includes its exact
        // view. The resource-key index already erases access mode and owned
        // quantity, so answer this common core-projection query without
        // entering proof-aware memory/snapshot entailment.
        if fact.is_view()
            && self
                .storage
                .index
                .by_resource
                .get(fact.resource())
                .is_some_and(|entries| {
                    entries
                        .iter()
                        .any(|entry| resource_fact_entails(self.fact(*entry), fact, assumptions))
                })
        {
            return true;
        }
        if crate::instrumentation::measure_operation(
            "kernel",
            "resource satisfaction",
            "resource satisfaction: indexed direct entailment",
            || {
                self.direct_match_candidates(fact)
                    .any(|available| resource_fact_entails(available, fact, assumptions))
            },
        ) {
            return true;
        }
        // Zero ownership is the multiplicative identity even when the zero
        // is visible only after resolving a short chain of checked symbolic
        // equalities. Pay for that bounded proof only after the indexed
        // resource lookup misses, so ordinary positive-resource queries keep
        // their direct fast path.
        if fact
            .owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_resolves_to_zero(quantity, assumptions))
        {
            return true;
        }
        // A required fact may span several adjacent held resources; merge
        // them and retry once. Only memory resources have a split/merge
        // algebra: token and composite entailment is decided one fact at a
        // time above. Normalizing an unrelated ambient memory context while
        // looking for a missing token or composite makes an exact resource
        // query depend on every symbolic range the caller happens to hold.
        if fact.family() != ResourceFamily::Memory {
            return false;
        }
        // Normalization can only merge facts within one access mode. A
        // viewed context cannot acquire ownership by normalizing, so avoid
        // scanning unrelated composite views for an impossible owned-memory
        // query.
        if fact.is_own()
            && !self
                .direct_match_candidates(fact)
                .any(CResourceFact::is_own)
        {
            return false;
        }
        let normalized = crate::instrumentation::measure_operation(
            "kernel",
            "resource satisfaction",
            "resource satisfaction: normalization fallback",
            || self.clone().normalized(assumptions),
        );
        normalized.storage.facts.len() < self.storage.facts.len()
            && normalized
                .direct_match_candidates(fact)
                .any(|available| resource_fact_entails(available, fact, assumptions))
    }

    pub fn is_empty(&self) -> bool {
        self.storage.facts.is_empty()
    }

    /// Whether a memory fact is held by structure alone: an exact entry, or
    /// a fact on the same block whose constant bounds cover the required
    /// range at an equal or constant-offset base. No reasoning is applied;
    /// this is the indexed answer a search asks at each context before any
    /// proof.
    pub(in crate::kernel) fn satisfies_memory_fact_structurally(
        &self,
        fact: &CResourceFact,
    ) -> bool {
        if self.storage.index.exact.contains_key(fact) {
            return true;
        }
        let Some(required) = fact.memory_range() else {
            return false;
        };
        self.memory_block_facts(&required.base().block)
            .any(|available| {
                let available = if fact.is_own() {
                    available.memory_own_range().cloned()
                } else {
                    resource_fact_read_core_range(available)
                };
                available.is_some_and(|available| {
                    memory_range_structurally_covers(&available, required, None) == Some(true)
                })
            })
    }

    pub(in crate::kernel) fn permits_memory_read(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        // A contract expression can reload a pointer-valued field after an
        // opaque call. Match that kernel-minted name to the resource's
        // retained load origin before consulting the block and range
        // indexes, just as the write lookup below does. The indexed
        // structural check then answers from the exact supporting resource
        // instead of comparing every historical range through call havoc.
        //
        // A proved pointer equality names the same cell two ways: a frame's
        // identity payload (symbolic) and the C value loaded for it
        // (external plus an offset). The facts sit under whichever spelling
        // the unfold that published them used, so the lookup consults both;
        // resolving to one spelling and looking only there refused a read
        // of a cell the state plainly owned.
        let spellings = self.pointer_spellings(pointer, assumptions);
        if spellings.iter().any(|pointer| {
            self.permits_memory_read_structurally(pointer, byte_width, assumptions)
                || self.memory_block_facts(&pointer.block).any(|resource| {
                    memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
                })
        }) {
            return true;
        }
        // The indexed lookups answer every read whose pointer names the
        // owning fact's block. A pointer proved equal to one in another
        // block is decided by the range check under the assumptions, as
        // the write lookup below already does; this is reached only when
        // the indexed answer was no, so a permitted read pays for it only
        // through an alias.
        spellings.iter().any(|pointer| {
            self.iter().any(|resource| {
                memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
            })
        })
    }

    /// The spellings of one address a resource lookup consults: the pointer
    /// itself, its retained load origin when it is a kernel-minted name,
    /// and the non-symbolic side of a proved pointer equality when it is a
    /// symbolic block. At most three, deduplicated, in that order.
    fn pointer_spellings(&self, pointer: &Pointer, assumptions: &PureFactContext) -> Vec<Pointer> {
        let mut spellings = vec![pointer.clone()];
        let minted = crate::kernel::reasoning::resolve_minted_load_pointer(pointer, assumptions);
        if !spellings.contains(&minted) {
            spellings.push(minted.clone());
        }
        let aliased =
            crate::kernel::reasoning::resolve_symbolic_pointer_alias(&minted, assumptions);
        if !spellings.contains(&aliased) {
            spellings.push(aliased);
        }
        spellings
    }

    pub(in crate::kernel) fn permits_memory_read_structurally(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        for resource in self.memory_block_facts(&pointer.block) {
            let Some(range) = resource_fact_read_core_range(resource) else {
                continue;
            };
            if pointer_has_structural_range_base(pointer, range.base())
                && memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
            {
                return true;
            }
        }
        false
    }

    pub(in crate::kernel) fn memory_write_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> Option<&CMemoryRange> {
        // A kernel-minted address resolves to its load term first, so it
        // matches owned ranges still written through loads; a proved
        // pointer equality's other spelling is consulted as for reads.
        let spellings = self.pointer_spellings(pointer, assumptions);
        for pointer in &spellings {
            for resource in self.memory_block_facts(&pointer.block) {
                let CResourceFact::Own(CResource::Memory(range), _) = resource else {
                    continue;
                };
                if pointer_has_structural_range_base(pointer, range.base())
                    && memory_resource_fact_permits_write(
                        resource,
                        pointer,
                        byte_width,
                        assumptions,
                    )
                {
                    return Some(range);
                }
            }
        }
        spellings.iter().find_map(|pointer| {
            self.iter().find_map(|resource| {
                memory_resource_fact_permits_write(resource, pointer, byte_width, assumptions)
                    .then(|| resource.memory_own_range())
                    .flatten()
            })
        })
    }

    pub fn without_fact(self, fact: &CResourceFact, assumptions: &PureFactContext) -> Option<Self> {
        self.without_fact_delaying_normalization(fact, assumptions)
            .map(|context| context.normalized(assumptions))
    }

    pub(in crate::kernel) fn without_fact_delaying_normalization(
        mut self,
        fact: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        self.consume_fact_without_normalizing(fact, assumptions)
            .then_some(self)
    }

    /// Consumes one fact while normalizing only its indexed candidate bucket.
    ///
    /// Direct algebraic consumption is the common path. If several retained
    /// representations must be combined first, this operation rebuilds only
    /// the exact-resource bucket and then, if equality-aware matching is
    /// needed, the resource's necessary-shape bucket. Unrelated resources are
    /// neither scanned nor materialized, and the returned snapshot preserves
    /// this context's mutation ancestry.
    pub(crate) fn without_fact_incrementally(
        mut self,
        fact: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if !fact.has_valid_instance_access() {
            return None;
        }
        if fact
            .owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
        {
            return Some(self);
        }

        if let CResource::Memory(range) = fact.resource()
            && let Some(candidates) = self.concrete_memory_start_candidates(range, fact.is_own())
            && self.consume_fact_from_candidates(fact, assumptions, candidates)
        {
            return Some(self);
        }

        let exact_resource_entries = self.storage.index.by_resource.get(fact.resource()).cloned();
        if exact_resource_entries.as_ref().is_some_and(|entries| {
            self.consume_fact_from_candidates(fact, assumptions, entries.iter().copied())
        }) {
            return Some(self);
        }
        let shape_entries = self.direct_match_candidate_positions(fact).cloned();
        for entries in exact_resource_entries.into_iter() {
            let mut candidates = ResourceContext::new();
            for entry in entries.iter() {
                candidates.insert_fact(self.fact(*entry).clone());
            }
            candidates = candidates.normalized(assumptions);
            if !candidates.consume_fact_without_normalizing(fact, assumptions) {
                continue;
            }
            let residual = candidates.iter().cloned().collect::<Vec<_>>();
            for entry in entries.iter() {
                self.remove_entry(*entry);
            }
            for residual in residual {
                self.insert_fact(residual);
            }
            return Some(self);
        }
        if self.consume_fact_without_normalizing(fact, assumptions) {
            return Some(self);
        }
        for entries in shape_entries.into_iter() {
            let mut candidates = ResourceContext::new();
            for entry in entries.iter() {
                candidates.insert_fact(self.fact(*entry).clone());
            }
            candidates = candidates.normalized(assumptions);
            if !candidates.consume_fact_without_normalizing(fact, assumptions) {
                continue;
            }
            let residual = candidates.iter().cloned().collect::<Vec<_>>();
            for entry in entries.iter() {
                self.remove_entry(*entry);
            }
            for residual in residual {
                self.insert_fact(residual);
            }
            return Some(self);
        }
        None
    }

    /// Normalizes only the resource buckets affected by `seeds`.
    ///
    /// Exact token/composite resources use their full resource key, so other
    /// arguments in the same declared family are not visited. Memory uses its
    /// block bucket because splitting and recombining one exported range may
    /// touch adjacent residual ranges in that block.
    pub(crate) fn normalized_around_facts(
        mut self,
        seeds: &[CResourceFact],
        assumptions: &PureFactContext,
    ) -> Self {
        let supported = self.supported_projection_pairs();
        let expansions = self.cached_support_expansions();
        let mut exact_resources = BTreeSet::new();
        let mut memory_blocks = BTreeSet::new();
        for fact in seeds {
            match fact.resource() {
                CResource::Memory(range) => {
                    memory_blocks.insert(range.base().block.clone());
                }
                resource => {
                    exact_resources.insert(resource.clone());
                }
            }
        }
        let mut buckets = Vec::new();
        for resource in exact_resources {
            if let Some(entries) = self.storage.index.by_resource.get(&resource) {
                buckets.push(entries.clone());
            }
        }
        for block in memory_blocks {
            if let Some(entries) = self.storage.index.memory_by_block.get(&block) {
                buckets.push(entries.clone());
            }
        }
        for entries in buckets {
            let original = entries
                .iter()
                .map(|entry| self.fact(*entry).clone())
                .collect::<Vec<_>>();
            let mut reusable_occurrences = original
                .iter()
                .zip(entries.iter())
                .filter(|(fact, _)| fact.is_own())
                .fold(
                    BTreeMap::<CResourceFact, Vec<ResourceOccurrenceId>>::new(),
                    |mut occurrences, (fact, entry)| {
                        occurrences
                            .entry(fact.clone())
                            .or_default()
                            .push(self.occurrence(*entry));
                        occurrences
                    },
                );
            let normalized = ResourceContext::new()
                .unchecked_with_facts(original.iter().cloned())
                .normalized(assumptions)
                .iter()
                .cloned()
                .collect::<Vec<_>>();
            if original == normalized {
                continue;
            }
            for entry in entries.iter() {
                self.remove_entry(*entry);
            }
            for fact in normalized {
                let occurrence = fact
                    .is_own()
                    .then(|| reusable_occurrences.get_mut(&fact))
                    .flatten()
                    .and_then(Vec::pop);
                self.insert_fact_with_support_occurrence_and_metadata_at(
                    fact, None, None, None, occurrence,
                );
            }
        }
        self.restore_supported_projection_pairs(supported)
            .restore_cached_support_expansions(expansions)
    }

    pub(crate) fn without_exact_representation(mut self, fact: &CResourceFact) -> Option<Self> {
        let entry = *self.storage.index.exact.get(fact)?.iter().next()?;
        self.remove_entry(entry);
        Some(self)
    }

    /// Consumes several facts while postponing whole-context normalization
    /// until the end. If a required fact is only available after adjacent
    /// resources are merged, normalize once at that point and retry it.
    pub fn without_facts(
        self,
        facts: &[CResourceFact],
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let mut context = self;
        for fact in facts {
            if context.consume_fact_without_normalizing(fact, assumptions) {
                continue;
            }
            context = context.normalized(assumptions);
            if !context.consume_fact_without_normalizing(fact, assumptions) {
                return None;
            }
        }
        Some(context.normalized(assumptions))
    }

    fn consume_fact_without_normalizing(
        &mut self,
        fact: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        if !fact.has_valid_instance_access() {
            return false;
        }
        if fact
            .owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
        {
            return true;
        }
        let mut candidates = self
            .storage
            .index
            .exact
            .get(fact)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .copied()
            .collect::<Vec<_>>();
        let exact_candidates = candidates.iter().copied().collect::<BTreeSet<_>>();
        if let Some(shape) = self.direct_match_candidate_positions(fact) {
            let remaining = shape
                .iter()
                .copied()
                .filter(|entry| !exact_candidates.contains(entry));
            if let CResource::Memory(required_range) = fact.resource() {
                let remaining = remaining.collect::<Vec<_>>();
                candidates.extend(remaining.iter().copied().filter(|entry| {
                    self.fact(*entry).memory_range().is_some_and(|available| {
                        crate::kernel::assumptions::pointers_equal_ignoring_memories(
                            available.base(),
                            required_range.base(),
                        )
                    })
                }));
                candidates.extend(remaining.into_iter().filter(|entry| {
                    !self.fact(*entry).memory_range().is_some_and(|available| {
                        crate::kernel::assumptions::pointers_equal_ignoring_memories(
                            available.base(),
                            required_range.base(),
                        )
                    })
                }));
            } else {
                candidates.extend(remaining);
            }
        }
        if self.consume_fact_from_candidates(fact, assumptions, candidates) {
            return true;
        }
        fact.owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_resolves_to_zero(quantity, assumptions))
    }

    fn consume_fact_from_candidates(
        &mut self,
        fact: &CResourceFact,
        assumptions: &PureFactContext,
        candidates: impl IntoIterator<Item = ResourceEntryId>,
    ) -> bool {
        let algebra = resource_family_algebra(fact.family());
        for entry in candidates {
            crate::instrumentation::record_deterministic_work(1);
            // Exact representation is the common path and needs no algebraic
            // decomposition. In particular, splitting an exactly matching
            // symbolic memory range can require arithmetic facts that are
            // irrelevant to consuming the range itself.
            if self.fact(entry) == fact {
                if fact.is_view() {
                    return true;
                }
                self.remove_entry(entry);
                return true;
            }
            let available = self.fact(entry);
            let Some(consumption) = algebra.consume(available, fact, assumptions) else {
                continue;
            };
            if let ResourceFactConsumption::Replace(residual) = consumption {
                self.remove_entry(entry);
                for residual in residual {
                    self.insert_fact(residual);
                }
            }
            return true;
        }
        false
    }

    pub(in crate::kernel) fn normalized(mut self, assumptions: &PureFactContext) -> Self {
        if !self.storage.supported_by.is_empty()
            || !self.storage.expansions_by_support_occurrence.is_empty()
        {
            let supported = self.supported_projection_pairs();
            let expansions = self.cached_support_expansions();
            let entries = self
                .storage
                .supported_by
                .iter()
                .map(|(entry, _)| *entry)
                .collect::<Vec<_>>();
            for entry in entries {
                self.remove_entry_only(entry);
            }
            self.storage = std::sync::Arc::new(ResourceContextStorage {
                facts: self.storage.facts.clone(),
                next_entry_id: self.storage.next_entry_id,
                occurrence_by_entry: self.storage.occurrence_by_entry.clone(),
                entry_by_occurrence: self.storage.entry_by_occurrence.clone(),
                index: self.storage.index.clone(),
                supported_by: self.storage.supported_by.clone(),
                support_occurrence_by_projection: self
                    .storage
                    .support_occurrence_by_projection
                    .clone(),
                projections_by_support: self.storage.projections_by_support.clone(),
                projections_by_support_occurrence: self
                    .storage
                    .projections_by_support_occurrence
                    .clone(),
                support_metadata_by_projection: self.storage.support_metadata_by_projection.clone(),
                projections_by_memory_block: self.storage.projections_by_memory_block.clone(),
                projections_by_memory_interval: self.storage.projections_by_memory_interval.clone(),
                projections_by_memory_interval_subtree: self
                    .storage
                    .projections_by_memory_interval_subtree
                    .clone(),
                unknown_memory_support: self.storage.unknown_memory_support.clone(),
                symbolic_memory_support: self.storage.symbolic_memory_support.clone(),
                expansions_by_support_occurrence: PersistentMap::default(),
                expansions_by_support_entry: PersistentMap::default(),
                origin: self.storage.origin.clone(),
                history: self.storage.history.clone(),
                materialized: std::sync::OnceLock::new(),
            });
            return self
                .normalized(assumptions)
                .restore_supported_projection_pairs(supported)
                .restore_cached_support_expansions(expansions);
        }
        let mut changed_facts = BTreeSet::new();
        let retained = self
            .storage
            .facts
            .iter()
            .filter_map(|(entry, fact)| {
                if fact.has_valid_instance_access()
                    && fact
                        .owned_quantity_term()
                        .is_some_and(|quantity| quantity.as_const() == Some(0))
                {
                    changed_facts.insert(fact.clone());
                    None
                } else {
                    Some((Some(self.occurrence(*entry)), fact.clone()))
                }
            })
            .collect::<Vec<_>>();
        let mut slots = retained.iter().cloned().map(Some).collect::<Vec<_>>();
        let mut index = ResourceNormalizationIndex::default();
        for (position, (_, fact)) in retained.iter().enumerate() {
            index.insert(position, fact);
        }
        // A merged fact is a new authority with no occurrence, so merging a
        // loan-bound view would silently discard the dependency that
        // authorizes reading it. Under stable-loan semantics the split
        // representation is the checked one; keep it. The map is empty under
        // legacy semantics, so this costs nothing and changes nothing there.
        let loan_bound = |occurrence: &Option<ResourceOccurrenceId>| {
            !self.loan_dependencies.map.is_empty()
                && occurrence
                    .is_some_and(|occurrence| self.loan_dependencies.map.get(&occurrence).is_some())
        };
        let mut i = 0;
        while i < slots.len() {
            let Some((occurrence, fact)) = slots[i].clone() else {
                i += 1;
                continue;
            };
            if loan_bound(&occurrence) {
                i += 1;
                continue;
            }
            let mut changed = false;
            for j in index.candidates_after(i, &fact) {
                crate::instrumentation::record_deterministic_work(1);
                let Some((right_occurrence, right)) = slots[j].as_ref() else {
                    continue;
                };
                if loan_bound(right_occurrence) {
                    continue;
                }
                if let Some(merged) = normalize_resource_fact_pair(&fact, right, assumptions) {
                    changed_facts.insert(fact.clone());
                    changed_facts.insert(right.clone());
                    changed_facts.insert(merged.clone());
                    index.remove(i, &fact);
                    index.remove(j, right);
                    slots[j] = None;
                    // The merged fact is a new authority. Do not inherit
                    // either input occurrence, but keep every untouched slot
                    // tied to its original occurrence.
                    slots[i] = Some((None, merged.clone()));
                    index.insert(i, &merged);
                    changed = true;
                    break;
                }
            }
            if !changed {
                i += 1;
            }
        }
        if changed_facts.is_empty() {
            return self;
        }
        self.replace_facts(slots.into_iter().flatten(), changed_facts);
        self
    }

    fn supported_projection_pairs(
        &self,
    ) -> Vec<(
        Option<ResourceOccurrenceId>,
        CResourceFact,
        CResourceFact,
        Option<ResourceSupportMetadata>,
    )> {
        self.storage
            .supported_by
            .iter()
            .map(|(entry, support)| {
                (
                    self.storage
                        .support_occurrence_by_projection
                        .get(entry)
                        .copied(),
                    support.clone(),
                    self.fact(*entry).clone(),
                    self.storage
                        .support_metadata_by_projection
                        .get(&self.occurrence(*entry))
                        .cloned(),
                )
            })
            .collect()
    }

    fn restore_supported_projection_pairs(
        mut self,
        supported: Vec<(
            Option<ResourceOccurrenceId>,
            CResourceFact,
            CResourceFact,
            Option<ResourceSupportMetadata>,
        )>,
    ) -> Self {
        for (support_entry, support, projection, metadata) in supported {
            if !self.storage.index.exact.contains_key(&support) {
                continue;
            }
            let already_present = support_entry.is_some_and(|support_entry| {
                self.has_supported_projection(&projection, support_entry, &support)
            });
            if !already_present {
                if let Some(support_occurrence) = support_entry.filter(|occurrence| {
                    self.storage
                        .entry_by_occurrence
                        .get(occurrence)
                        .is_some_and(|entry| self.storage.facts.get(entry) == Some(&support))
                }) {
                    self.insert_fact_with_support_occurrence_and_metadata(
                        projection,
                        Some(support),
                        Some(support_occurrence),
                        metadata,
                    );
                } else if support_entry.is_none() {
                    self.insert_fact_with_support(projection, Some(support));
                }
            }
        }
        self
    }

    fn cached_support_expansions(&self) -> Vec<(ResourceOccurrenceId, Vec<CResourceFact>)> {
        self.storage
            .expansions_by_support_occurrence
            .iter()
            .map(|(support_occurrence, expansion)| {
                (*support_occurrence, expansion.as_ref().clone())
            })
            .collect()
    }

    fn restore_cached_support_expansions(
        mut self,
        expansions: Vec<(ResourceOccurrenceId, Vec<CResourceFact>)>,
    ) -> Self {
        for (support_occurrence, expansion) in expansions {
            let Some(entry) = self.storage.entry_by_occurrence.get(&support_occurrence) else {
                continue;
            };
            let support = self.fact(*entry).clone();
            if support.is_own() {
                self = self.with_cached_supported_expansion_for_occurrence(
                    support_occurrence,
                    &support,
                    expansion,
                );
            }
        }
        self
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ResourceNormalizationKey {
    Instance(Variable),
    Resource(CResource),
    ExactShape(ResourceFamily, String, usize),
    /// A token or composite whose first argument is a pointer into a block
    /// proven distinct from every block but itself and a symbolic one.
    ExactShapeAnchored(ResourceFamily, String, usize, PointerBlock),
    /// Every anchored token or composite of one shape, for the unanchored
    /// facts that may still name the same block.
    ExactShapeAnchoredAll(ResourceFamily, String, usize),
    MemoryStart(PointerBlock, bool, Bitvector32Term),
    MemoryEnd(PointerBlock, bool, Bitvector32Term),
}

/// The adjacency coordinate one memory bound contributes to the
/// normalization index.
///
/// Two owned ranges merge when they abut in bytes, and the element width is
/// only how those bytes are spelled (D6), so a concrete bound is keyed by its
/// absolute byte position: `p[0..2]` at width 4 ends where `p[8..12]` at
/// width 1 begins, and the index has to offer that pair to
/// [`merge_memory_ranges`] for either spelling to disappear again. A bound
/// that is not concrete, or whose base offset is not, keeps its element-unit
/// term, which remains the only form the symbolic adjacency comparison can
/// use. The two forms never collide: a concrete key is always a constant and
/// a retained term never is.
fn memory_normalization_position(range: &CMemoryRange, bound: &Bitvector32Term) -> Bitvector32Term {
    let byte_position = || -> Option<Bitvector32Term> {
        let base = range.base().offset.as_const()?;
        let elements = signed_bitvector_constant(bound)?;
        let byte = base.checked_add(elements.checked_mul(i64::from(range.element_width()))?)?;
        Some(Bitvector32Term::Constant(i32::try_from(byte).ok()? as u32))
    };
    byte_position().unwrap_or_else(|| bound.clone())
}

#[derive(Default)]
struct ResourceNormalizationIndex {
    positions: BTreeMap<ResourceNormalizationKey, BTreeSet<usize>>,
}

impl ResourceNormalizationIndex {
    fn keys(fact: &CResourceFact) -> Vec<ResourceNormalizationKey> {
        let mut keys = vec![ResourceNormalizationKey::Resource(fact.resource().clone())];
        match fact.resource() {
            CResource::Instance(instance) => {
                keys.push(ResourceNormalizationKey::Instance(instance.identity))
            }
            CResource::Memory(range) => {
                keys.push(ResourceNormalizationKey::MemoryStart(
                    range.base().block.clone(),
                    fact.is_own(),
                    memory_normalization_position(range, range.start()),
                ));
                keys.push(ResourceNormalizationKey::MemoryEnd(
                    range.base().block.clone(),
                    fact.is_own(),
                    memory_normalization_position(range, range.end()),
                ));
            }
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                let shape = (fact.family(), name.clone(), arguments.len());
                match normalization_anchor(arguments) {
                    Some(block) => {
                        keys.push(ResourceNormalizationKey::ExactShapeAnchored(
                            shape.0,
                            shape.1.clone(),
                            shape.2,
                            block.clone(),
                        ));
                        keys.push(ResourceNormalizationKey::ExactShapeAnchoredAll(
                            shape.0, shape.1, shape.2,
                        ));
                    }
                    None => keys.push(ResourceNormalizationKey::ExactShape(
                        shape.0, shape.1, shape.2,
                    )),
                }
            }
        }
        keys
    }

    fn insert(&mut self, position: usize, fact: &CResourceFact) {
        for key in Self::keys(fact) {
            self.positions.entry(key).or_default().insert(position);
        }
    }

    fn remove(&mut self, position: usize, fact: &CResourceFact) {
        for key in Self::keys(fact) {
            if let Some(positions) = self.positions.get_mut(&key) {
                positions.remove(&position);
            }
        }
    }

    fn candidates_after(&self, position: usize, fact: &CResourceFact) -> Vec<usize> {
        let mut keys = vec![ResourceNormalizationKey::Resource(fact.resource().clone())];
        match fact.resource() {
            CResource::Instance(instance) => {
                keys.push(ResourceNormalizationKey::Instance(instance.identity))
            }
            CResource::Memory(range) => {
                keys.push(ResourceNormalizationKey::MemoryEnd(
                    range.base().block.clone(),
                    fact.is_own(),
                    memory_normalization_position(range, range.start()),
                ));
                keys.push(ResourceNormalizationKey::MemoryStart(
                    range.base().block.clone(),
                    fact.is_own(),
                    memory_normalization_position(range, range.end()),
                ));
            }
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                // Two facts of one shape merge only when their arguments are
                // proven equal, and a pointer is never proven equal to one in
                // a block proven distinct from its own. So an anchored fact
                // meets the facts anchored in its own block and the
                // unanchored ones; an unanchored fact meets every fact of its
                // shape.
                let shape = (fact.family(), name.clone(), arguments.len());
                keys.push(ResourceNormalizationKey::ExactShape(
                    shape.0,
                    shape.1.clone(),
                    shape.2,
                ));
                match normalization_anchor(arguments) {
                    Some(block) => keys.push(ResourceNormalizationKey::ExactShapeAnchored(
                        shape.0,
                        shape.1,
                        shape.2,
                        block.clone(),
                    )),
                    None => keys.push(ResourceNormalizationKey::ExactShapeAnchoredAll(
                        shape.0, shape.1, shape.2,
                    )),
                }
            }
        }
        let mut candidates = BTreeSet::new();
        for key in keys {
            if let Some(positions) = self.positions.get(&key) {
                candidates.extend(positions.range((position + 1)..).copied());
            }
        }
        candidates.into_iter().collect()
    }
}

/// The block of a token or composite's first argument when that argument is
/// a pointer into a heap or temporary block. `PointerBlock::proven_distinct`
/// separates such a block from every block except itself and a symbolic one,
/// with no assumption able to override it, so two facts anchored in
/// different blocks can never have their first arguments proven equal and
/// never normalize together.
fn normalization_anchor(arguments: &[AlgebraicValue]) -> Option<&PointerBlock> {
    match arguments.first() {
        Some(AlgebraicValue::C(CValue::Pointer(pointer)))
            if matches!(
                pointer.pointer().block,
                PointerBlock::Heap(_) | PointerBlock::Temporary(_)
            ) =>
        {
            Some(&pointer.pointer().block)
        }
        _ => None,
    }
}

fn resource_family_algebra(family: ResourceFamily) -> &'static dyn ResourceFamilyAlgebra {
    let algebra: &'static dyn ResourceFamilyAlgebra = match family {
        ResourceFamily::Memory => &MEMORY_RESOURCE_ALGEBRA,
        ResourceFamily::Composite => &COMPOSITE_RESOURCE_ALGEBRA,
        ResourceFamily::Token => &TOKEN_RESOURCE_ALGEBRA,
        ResourceFamily::Instance => &INSTANCE_RESOURCE_ALGEBRA,
    };
    debug_assert_eq!(algebra.family(), family);
    algebra
}

pub(super) fn validate_resource_spec(spec: &CResourceSpec) -> Result<(), CResourceSpecError> {
    resource_family_algebra(spec.family()).validate_spec(spec)
}

fn resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    available.family() == required.family()
        && resource_family_algebra(available.family()).entails(available, required, assumptions)
}

fn normalize_resource_fact_pair(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &PureFactContext,
) -> Option<CResourceFact> {
    if left.family() != right.family() {
        return None;
    }
    resource_family_algebra(left.family()).normalize_pair(left, right, assumptions)
}

fn memory_resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    if available == required {
        return true;
    }
    match (available, required) {
        (_, _) if required.memory_view_range().is_some() => {
            let required = required.memory_view_range().expect("checked above");
            let Some(available) = resource_fact_read_core_range(available) else {
                return false;
            };
            memory_range_covers(&available, required, assumptions)
        }
        (_, _) if required.memory_own_range().is_some() => {
            let Some(available) = available.memory_own_range() else {
                return false;
            };
            let required = required.memory_own_range().expect("checked above");
            memory_range_covers(available, required, assumptions)
        }
        _ => false,
    }
}

fn consume_memory_resource_fact(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &PureFactContext,
) -> Option<ResourceFactConsumption> {
    if let Some(required) = required.memory_view_range() {
        // `Preserve` here is the owner-observation rule in consumption form
        // (the owner-observation rule in docs/internals/stable-views.md, and see `owner_observation_core`): a viewed clause is
        // discharged by read authority the consuming context already holds,
        // and the holding is left untouched, whether it is a view or the
        // ownership the view is read off.
        //
        // The owner route serves the observation sites D7 names — folding,
        // unfolding, and observing a resource body whose `contains` lists a
        // viewed range the same context owns. It stays because an owner may
        // read and inspect what it owns without lending to itself.
        //
        // It is not how a call's `views` requirement is met. That takes an
        // escrowed owner and an opened loan, which only the stable-view
        // planner does, and the planner reserves and lends before any
        // requirement it planned can reach consumption: a call transfer sends
        // exactly the requirements the plan did not reserve down the
        // definitional route, and those are owned, population-quantity, or
        // definitionally empty. A view requirement never arrives here from a
        // call.
        //
        // The distinction is not one this algebra can draw: it is handed two
        // bare facts, so it cannot see whether the requirer is the context
        // itself or another participant. Keeping the call side honest is the
        // planner's job, not this function's.
        return resource_fact_read_core_range(available)
            .is_some_and(|available| memory_range_covers(&available, required, assumptions))
            .then_some(ResourceFactConsumption::Preserve);
    }
    if let Some(required) = required.memory_own_range() {
        let available = available.memory_own_range()?;
        if !memory_range_covers(available, required, assumptions) {
            return None;
        }
        return Some(ResourceFactConsumption::Replace(
            split_memory_range(available, required, assumptions)?
                .into_iter()
                .map(CResourceFact::own_memory)
                .collect(),
        ));
    }
    unreachable!("non-memory resource sent to memory resource consumer")
}

fn exact_resources_proven_equal(
    left: &CResource,
    right: &CResource,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (CResource::Instance(left), CResource::Instance(right)) => {
            left.identity == right.identity
                && left.name == right.name
                && left.schema == right.schema
                && left.arguments.len() == right.arguments.len()
                && left.fields.len() == right.fields.len()
                && left
                    .arguments
                    .iter()
                    .chain(left.fields.iter())
                    .zip(right.arguments.iter().chain(right.fields.iter()))
                    .all(|(a, b)| crate::kernel::resource_arguments_proven_equal(a, b, assumptions))
        }
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments.iter())
                    .all(|(left, right)| {
                        crate::kernel::resource_arguments_proven_equal(left, right, assumptions)
                    })
        }
        _ => false,
    }
}

fn exact_resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    match (available, required) {
        (
            CResourceFact::Own(available, available_quantity),
            CResourceFact::Own(required, required_quantity),
        ) => {
            resource_quantity_at_least(available_quantity, required_quantity, assumptions)
                && exact_resources_proven_equal(available, required, assumptions)
        }
        (CResourceFact::Own(available, available_quantity), CResourceFact::View(required)) => {
            resource_quantity_is_positive(available_quantity, assumptions)
                && exact_resources_proven_equal(available, required, assumptions)
        }
        (CResourceFact::View(available), CResourceFact::View(required)) => {
            exact_resources_proven_equal(available, required, assumptions)
        }
        _ => false,
    }
}

/// Decides one resource-quantity condition by exact routes only.
///
/// Exact indexed lookup first, then the retained atomic condition checker on
/// the bare condition. Neither route recurses through logical structure, tries
/// alternative rules, nor scans unrelated propositions, so the work is the
/// condition's own size plus indexed lookups. A quantity relation that only
/// follows logically is deliberately not decided here: it becomes an explicit
/// obligation at the operation that consumes it.
///
/// The counted-population helpers in `functions.rs` share this routine.
/// `quantity_relations_ignore_unrelated_facts` is the scaling regression.
pub(in crate::kernel) fn quantity_condition_holds(
    assumptions: &PureFactContext,
    condition: ConditionTerm,
) -> bool {
    assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), true))
        || assumptions.decide(&condition) == Some(true)
}

fn resource_quantity_at_least(
    available: &Bitvector32Term,
    required: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    available == required
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(available.clone()),
                Box::new(required.clone()),
            ),
        )
}

/// Whether a constant owned quantity is positive, as the signed number it is.
///
/// An owned quantity is an `int32`, and `resource_quantity_at_least` beside it
/// asks `Bitvector32SignedGreaterEqual`, so reading this one through
/// `Bitvector32Term::as_const` made the two arms disagree about one number:
/// `-1` was the largest quantity there is. `a98a05e4` is the same confusion at
/// the surface `fold`, and this is the kernel's own copy of it — the one that
/// decides whether an owned population exposes a viewed description of itself.
fn constant_quantity_is_positive(quantity: &Bitvector32Term) -> bool {
    signed_bitvector_constant(quantity).is_some_and(|value| value > 0)
}

fn resource_quantity_is_positive(
    quantity: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    constant_quantity_is_positive(quantity)
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
        )
}

/// The total of two population quantities, as the natural number a count is.
///
/// A population count is a mathematical natural number. The kernel holds one
/// in an `int32` term, and [`Bitvector32Term::add`] is modular, so
/// `2000000000 + 2000000000` is `-294967296`: four billion units reading as a
/// negative population. Every quantity rule beneath this one is signed —
/// [`resource_quantity_at_least`], [`constant_quantity_is_positive`],
/// `population_quantity_is_positive` — so a wrapped total is not an
/// imprecision, it is a different and smaller number. Two `produces k of
/// tok(o)` clauses at `k == 2000000000` composed to `k + k` this way, and
/// `ensures count(tok(o)) < 0` verified on the result.
///
/// A total may be formed only when it is exact. Constants and recombining a
/// split need no extra premise. Other sums require the no-overflow condition
/// in the supplied context, checked by indexed lookup and atomic arithmetic.
/// Declining a merge leaves its two resource facts intact.
pub(in crate::kernel) fn population_quantity_sum(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    if let (Some(left_value), Some(right_value)) = (
        signed_bitvector_constant(left),
        signed_bitvector_constant(right),
    ) {
        let total = left_value + right_value;
        return u32::try_from(total)
            .ok()
            .filter(|_| total <= i64::from(i32::MAX))
            .map(Bitvector32Term::Constant);
    }
    if left.as_const() == Some(0) {
        return Some(right.clone());
    }
    if right.as_const() == Some(0) {
        return Some(left.clone());
    }
    // Recombining a framed remainder is what a contract refinement does
    // (`mdtests/c_named_contract_refines_symbolic_resource_quantity.md`), and
    // the term it lands on is the one it started from.
    if let Bitvector32Term::Subtract(total, taken) = right
        && taken.as_ref() == left
    {
        return Some(total.as_ref().clone());
    }
    if let Bitvector32Term::Subtract(total, taken) = left
        && taken.as_ref() == right
    {
        return Some(total.as_ref().clone());
    }
    let no_overflow = ConditionTerm::Bitvector32SignedAddOverflows(
        Box::new(left.clone()),
        Box::new(right.clone()),
    );
    (assumptions.proves_exact(&Proposition::ConditionIs(no_overflow.clone(), false))
        || assumptions.decide(&no_overflow) == Some(false))
    .then(|| Bitvector32Term::add(left.clone(), right.clone()))
}

fn resource_quantity_is_zero(quantity: &Bitvector32Term, assumptions: &PureFactContext) -> bool {
    quantity.as_const() == Some(0)
        || assumptions.proves_exact(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ))
}

fn resource_quantity_resolves_to_zero(
    quantity: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    resource_quantity_is_zero(quantity, assumptions)
        || crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
            quantity,
            &Bitvector32Term::Constant(0),
            assumptions,
        )
}

fn consume_exact_resource_fact(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &PureFactContext,
) -> Option<ResourceFactConsumption> {
    if !exact_resource_fact_entails(available, required, assumptions) {
        return None;
    }
    // `Preserve` for a viewed token or composite is the owner-observation
    // rule in consumption form, exactly as for memory
    // (`consume_memory_resource_fact`; docs/internals/stable-views.md): a
    // viewed clause is discharged by authority the consuming context already
    // holds, whether a view or the ownership the view is read off, and the
    // holding is left untouched. It serves the fold, unfold, and observe
    // discharge of a body's viewed clause. It is not how a call's `views`
    // requirement is met: the planner reserves and lends before any
    // requirement reaches the definitional route, which afterwards receives
    // only owned, population-quantity, and definitionally-empty facts.
    Some(if required.is_view() {
        ResourceFactConsumption::Preserve
    } else {
        let CResourceFact::Own(available, available_quantity) = available else {
            unreachable!("owned exact requirement entailed by a viewed fact")
        };
        let CResourceFact::Own(_, required_quantity) = required else {
            unreachable!("checked above")
        };
        let residual = Bitvector32Term::subtract(
            available_quantity.as_ref().clone(),
            required_quantity.as_ref().clone(),
        );
        let residual_is_zero = residual.as_const() == Some(0)
            || quantity_condition_holds(
                assumptions,
                ConditionTerm::Bitvector32Equal(
                    Box::new(residual.clone()),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
            );
        ResourceFactConsumption::Replace(if residual_is_zero {
            Vec::new()
        } else {
            vec![CResourceFact::own_quantity(available.clone(), residual)]
        })
    })
}

/// Normalization for the exact families, including the owner-absorbs-view
/// case (the owner-observation rule and law 4 in docs/internals/stable-views.md).
///
/// An owner absorbing an equal viewed description drops a *description*, not
/// authority: the owner keeps every capability the pair had, and a view read
/// off an owner the same context holds is an observation of that ownership.
/// D2 law 4 says dropping a description changes no live access share and no
/// recovery entitlement, so this merge is sound exactly while the view it
/// swallows is unbound.
///
/// A **bound** view — one whose occurrence carries a live `loan_dependency` —
/// must never be absorbed: the merged fact is a new authority with no
/// occurrence, so the dependency that authorizes reading it would vanish and
/// the loan would disappear with it. `ResourceContext::normalized` is the
/// only caller, and its `loan_bound` guard skips both sides of every pair
/// whose occurrence has a live dependency, and detaches supported projections
/// before normalizing at all. That guard, not this function, is what makes
/// the merge safe: `normalize_pair` sees two bare facts and cannot tell a
/// bound description from an unbound one.
fn combine_exact_resource_facts(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &PureFactContext,
) -> Option<CResourceFact> {
    match (left, right) {
        (CResourceFact::Own(left, quantity), CResourceFact::View(right))
        | (CResourceFact::View(right), CResourceFact::Own(left, quantity))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(CResourceFact::Own(left.clone(), quantity.clone()))
        }
        (CResourceFact::View(left), CResourceFact::View(right))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(CResourceFact::View(left.clone()))
        }
        _ => None,
    }
}

/// The owner-observation rule (docs/internals/stable-views.md).
///
/// An owner may read what it owns and inspect its composite without issuing a
/// stable loan to itself, so a positive owned fact exposes a viewed
/// description of the same resource. That description is an *observation* of
/// ownership the same context holds: it mints no access share, no scope, and
/// no recovery right, and it is only as good as the ownership it is read off.
///
/// Its consumers are the observation sites D7 names:
///
/// * [`resource_fact_read_core_range`], which lets an owner load its own bytes
///   (`memory_resource_fact_permits_read`), and which
///   [`consume_memory_resource_fact`] reuses to discharge a resource body's
///   viewed clause at a fold, an unfold, or an observation;
/// * the escrow record in `crate::kernel::loans`, which names the viewed
///   description a checked lend transition hands the callee.
///
/// It never answers a *call's* `views` requirement on its own. Meeting one
/// escrows the owner and opens a loan, and only the stable-view planner does
/// that; a call transfer never routes a view requirement into consumption.
/// The projection is not authority the callee could carry: it is read off
/// ownership that stays where it is, so nothing survives the observing
/// context.
fn owner_observation_core(resource: &CResourceFact) -> Option<CResourceFact> {
    match resource {
        CResourceFact::Own(resource, quantity) if constant_quantity_is_positive(quantity) => {
            Some(CResourceFact::View(resource.clone()))
        }
        CResourceFact::Own(_, _) => None,
        CResourceFact::View(resource) => Some(CResourceFact::View(resource.clone())),
    }
}

fn same_family_separate_facts(facts: &[&CResourceFact]) -> Vec<Proposition> {
    let owned = facts
        .iter()
        .filter_map(|fact| fact.owned_resource())
        .collect::<Vec<_>>();
    let mut propositions = Vec::new();
    for i in 0..owned.len() {
        for right in &owned[i + 1..] {
            if resources_structurally_separate(owned[i], right) {
                continue;
            }
            propositions.push(Proposition::CResourceSeparate {
                left: owned[i].clone(),
                right: (*right).clone(),
            });
        }
    }
    propositions
}

/// Separation cases whose proof depends only on the resource constructors,
/// not on ambient facts or the composition that happened to contain them.
pub(in crate::kernel) fn resources_structurally_separate(
    left: &CResource,
    right: &CResource,
) -> bool {
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            left.base().blocks_proven_distinct(right.base())
                || left.base() == right.base()
                    && matches!(
                        (
                            signed_bitvector_constant(left.start()),
                            signed_bitvector_constant(left.end()),
                            signed_bitvector_constant(right.start()),
                            signed_bitvector_constant(right.end()),
                        ),
                        (Some(left_start), Some(left_end), Some(right_start), Some(right_end))
                            if left_end <= right_start || right_end <= left_start
                    )
        }
        _ => false,
    }
}

/// Equal-content string literal blocks may be merged by the C implementation.
/// They provide shared, read-only access, so two such literal facts do not
/// compete for mutable ownership and cannot establish separation by spelling.
fn string_literal_blocks_may_alias(left: &PointerBlock, right: &PointerBlock) -> bool {
    if left == right {
        return false;
    }
    matches!(
        (left, right),
        (
            PointerBlock::StringLiteral { bytes: left, .. },
            PointerBlock::StringLiteral { bytes: right, .. }
        ) if left == right
    )
}

impl ResourceFamilyAlgebra for MemoryResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Memory
    }

    /// Two owners of overlapping bytes are a partition violation. An owner
    /// overlapping a *view* is decided by the view's binding, which this
    /// check cannot see (the owner-observation rule in docs/internals/stable-views.md).
    ///
    /// A **bound** view — one carrying a live `loan_dependency` — beside a
    /// usable owner of the same bytes is invalid: lending escrows the owner
    /// out of the caller residual, so the two cannot coexist. That is
    /// enforced where the binding is visible, not here: the planner refuses
    /// an `owns` requirement inside a lent range (its exclusive reservations
    /// are taken before any view is planned, and the composite lend composes
    /// them back beside the frontier), and the ledger refuses a write or a
    /// retire through a lent range.
    ///
    /// An **unbound** viewed description beside its owner is an observation
    /// of that ownership (`owner_observation_core`) or intrinsic read
    /// authority over read-only or callee-unreachable storage, and is valid.
    ///
    /// The discriminator is therefore the binding, and a `ResourceFamilyAlgebra`
    /// sees two bare facts and the ambient assumptions: no occurrence, no
    /// context, no ledger. Deciding it here would need the whole trait to
    /// carry occurrence identity, and it would duplicate a check the planner
    /// and the ledger already make with the evidence in hand. The check stays
    /// owner/owner.
    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        let (Some(left), Some(right)) = (left.memory_own_range(), right.memory_own_range()) else {
            return None;
        };
        if string_literal_blocks_may_alias(&left.base().block, &right.base().block) {
            return None;
        }
        memory_ranges_proven_overlapping(left, right, assumptions).then(|| {
            ResourceContextValidityError::OverlappingOwnedMemoryResources {
                left: left.clone(),
                right: right.clone(),
            }
        })
    }

    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        memory_resource_fact_entails(available, required, assumptions)
    }

    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        consume_memory_resource_fact(available, required, assumptions)
    }

    fn normalize_pair(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<CResourceFact> {
        combine_memory_resource_facts(left, right, assumptions)
    }

    fn core(&self, fact: &CResourceFact) -> Option<CResourceFact> {
        owner_observation_core(fact)
    }

    fn observable_facts(
        &self,
        facts: &[&CResourceFact],
        _assumptions: &PureFactContext,
    ) -> Vec<Proposition> {
        // Same-block separation is no longer materialized into ambient
        // propositions; `PureFactContext` projects the identical candidate
        // set lazily from the retained compact composition when a separation
        // query for the block pair actually occurs.
        let _ = facts;
        Vec::new()
    }
}

macro_rules! impl_exact_resource_algebra {
    ($algebra:ty, $family:expr) => {
        impl ResourceFamilyAlgebra for $algebra {
            fn family(&self) -> ResourceFamily {
                $family
            }

            fn pair_validity_error(
                &self,
                _left: &CResourceFact,
                _right: &CResourceFact,
                _assumptions: &PureFactContext,
            ) -> Option<ResourceContextValidityError> {
                None
            }

            fn entails(
                &self,
                available: &CResourceFact,
                required: &CResourceFact,
                assumptions: &PureFactContext,
            ) -> bool {
                exact_resource_fact_entails(available, required, assumptions)
            }

            fn consume(
                &self,
                available: &CResourceFact,
                required: &CResourceFact,
                assumptions: &PureFactContext,
            ) -> Option<ResourceFactConsumption> {
                consume_exact_resource_fact(available, required, assumptions)
            }

            fn normalize_pair(
                &self,
                left: &CResourceFact,
                right: &CResourceFact,
                assumptions: &PureFactContext,
            ) -> Option<CResourceFact> {
                match (left, right) {
                    (
                        CResourceFact::Own(left, left_quantity),
                        CResourceFact::Own(right, right_quantity),
                    ) if exact_resources_proven_equal(left, right, assumptions) => {
                        // A merge that cannot state the total exactly is
                        // declined rather than wrapped: leaving both facts
                        // in the state costs precision, and a wrapped
                        // quantity is a count that is not the population's.
                        Some(CResourceFact::Own(
                            left.clone(),
                            Box::new(population_quantity_sum(
                                left_quantity,
                                right_quantity,
                                assumptions,
                            )?),
                        ))
                    }
                    _ => combine_exact_resource_facts(left, right, assumptions),
                }
            }

            fn core(&self, fact: &CResourceFact) -> Option<CResourceFact> {
                owner_observation_core(fact)
            }

            fn observable_facts(
                &self,
                facts: &[&CResourceFact],
                _assumptions: &PureFactContext,
            ) -> Vec<Proposition> {
                same_family_separate_facts(facts)
            }
        }
    };
}

impl_exact_resource_algebra!(TokenResourceAlgebra, ResourceFamily::Token);
impl_exact_resource_algebra!(CompositeResourceAlgebra, ResourceFamily::Composite);

impl ResourceFamilyAlgebra for InstanceResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Instance
    }
    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        match (left.resource(), right.resource()) {
            (CResource::Instance(a), CResource::Instance(b)) if a.identity == b.identity => Some(
                ResourceContextValidityError::DuplicateOwnedResourceFact(right.clone()),
            ),
            _ => None,
        }
    }
    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        matches!((available,required),(CResourceFact::Own(_,a),CResourceFact::Own(_,b)) if a.as_const()==Some(1) && b.as_const()==Some(1))
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions)
            .then(|| ResourceFactConsumption::Replace(vec![]))
    }
    fn normalize_pair(
        &self,
        _: &CResourceFact,
        _: &CResourceFact,
        _: &PureFactContext,
    ) -> Option<CResourceFact> {
        None
    }
    fn core(&self, _: &CResourceFact) -> Option<CResourceFact> {
        None
    }
    fn observable_facts(&self, _: &[&CResourceFact], _: &PureFactContext) -> Vec<Proposition> {
        vec![]
    }
}

fn resource_fact_read_core_range(resource: &CResourceFact) -> Option<CMemoryRange> {
    match resource.core()? {
        CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::View(
            CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
        )
        | CResourceFact::Own(..) => None,
    }
}

fn memory_resource_fact_permits_read(
    resource: &CResourceFact,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    resource_fact_read_core_range(resource).is_some_and(|range| {
        assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
            range.element_width(),
        )
    })
}

fn memory_resource_fact_permits_write(
    resource: &CResourceFact,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    match resource {
        CResourceFact::Own(CResource::Memory(range), _) => assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
            range.element_width(),
        ),
        CResourceFact::Own(
            CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
            _,
        )
        | CResourceFact::View(_) => false,
    }
}

fn pointer_has_structural_range_base(pointer: &Pointer, base: &Pointer) -> bool {
    if pointer.block != base.block {
        return false;
    }
    if crate::kernel::assumptions::pointers_equal_ignoring_memories(pointer, base) {
        return true;
    }
    matches!(
        &pointer.offset,
        PointerOffsetTerm::Add(left, right)
            if crate::kernel::assumptions::pointers_equal_ignoring_memories(
                &Pointer {
                    block: pointer.block.clone(),
                    offset: left.as_ref().clone(),
                },
                base,
            ) || crate::kernel::assumptions::pointers_equal_ignoring_memories(
                &Pointer {
                    block: pointer.block.clone(),
                    offset: right.as_ref().clone(),
                },
                base,
            )
    )
}

/// Range endpoints compare like ordinary terms, and additionally two loads
/// of one pointer are equal when the pointed-to cell is provably unchanged
/// between their snapshots — a range written through metadata loads then
/// survives writes to unrelated cells.
fn range_endpoint_terms_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    fn loads_bridged(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> bool {
        if let (
            Bitvector32Term::MemoryLoad(_, left_pointer),
            Bitvector32Term::MemoryLoad(_, right_pointer),
        ) = (left, right)
            && left_pointer == right_pointer
        {
            return crate::kernel::explicit_atomic_equality_from_memory_derivations(
                left,
                right,
                assumptions,
            );
        }
        false
    }
    if loads_bridged(left, right, assumptions) {
        return true;
    }
    // Structural descent covers the common affine endpoint forms
    // (base + load, load - base, load * scale).
    let structurally_bridged = match (left, right) {
        (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
        | (
            Bitvector32Term::Subtract(left_a, left_b),
            Bitvector32Term::Subtract(right_a, right_b),
        )
        | (
            Bitvector32Term::Multiply(left_a, left_b),
            Bitvector32Term::Multiply(right_a, right_b),
        ) => {
            range_endpoint_terms_equal(left_a, right_a, assumptions)
                && range_endpoint_terms_equal(left_b, right_b, assumptions)
        }
        _ => false,
    };
    structurally_bridged
        || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

/// Pointer bases compare with the same load bridging as range endpoints:
/// two forms of one loaded base pointer are equal when the loaded cell
/// is provably unchanged between their snapshots.
fn pointer_bases_equal_with_load_bridging(
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    left.block == right.block
        && pointer_offsets_equal_with_load_bridging(&left.offset, &right.offset, assumptions)
}

fn pointer_offsets_equal_with_load_bridging(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_equal_with_load_bridging(left_a, right_a, assumptions)
                && pointer_offsets_equal_with_load_bridging(left_b, right_b, assumptions)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && range_endpoint_terms_equal(left_value, right_value, assumptions)
        }
        _ => false,
    }
}

/// A range as its physical byte footprint: width 1, based at its first byte.
///
/// This is the shared spelling-independent form of a memory footprint (D6).
/// [`CMemoryRange::byte_footprint`] already derives the pointer and the byte
/// length, and `protected_range_proven_overlapping` in the loan oracle asks
/// its question in exactly these terms; this helper keeps the memory family's
/// relations on that one normalization rather than inventing a second.
fn byte_normalized_memory_range(range: &CMemoryRange) -> CMemoryRange {
    let (base, bytes) = range.byte_footprint();
    CMemoryRange::new_with_element_width(base, Bitvector32Term::Constant(0), bytes, 1)
}

/// Re-spells a range in another element width, naming the same bytes.
///
/// `p[2..3]` at width 4 and `p[8..12]` at width 1 are two spellings of one
/// four-byte footprint, so either may be rewritten as the other. Re-spelling
/// keeps the range's base pointer, and therefore every base relation the
/// equal-width relations already decide, which is why the relations below
/// prefer it to [`byte_normalized_memory_range`]: the byte form moves the
/// base to the range's first byte and loses those relations. It succeeds only
/// when the bounds are concrete and the byte offsets divide into whole
/// `width` elements.
fn memory_range_in_element_width(range: &CMemoryRange, width: u32) -> Option<CMemoryRange> {
    if range.element_width() == width {
        return Some(range.clone());
    }
    let source_width = i64::from(range.element_width());
    let target_width = i64::from(width);
    let start = signed_bitvector_constant(range.start())?.checked_mul(source_width)?;
    let end = signed_bitvector_constant(range.end())?.checked_mul(source_width)?;
    if start % target_width != 0 || end % target_width != 0 {
        return None;
    }
    let start = i32::try_from(start / target_width).ok()?;
    let end = i32::try_from(end / target_width).ok()?;
    Some(CMemoryRange::new_with_element_width(
        range.base().clone(),
        Bitvector32Term::Constant(start as u32),
        Bitvector32Term::Constant(end as u32),
        width,
    ))
}

pub(in crate::kernel) fn memory_range_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if available.element_width() != required.element_width() {
        // A footprint is bytes and the element width is only how the bytes
        // are spelled (D6), so a mismatch is rewritten into one coordinate
        // system instead of refusing. Neither rewrite adds or drops a byte,
        // so both are sound; the re-spelling is tried first because it keeps
        // the bases and endpoints the equal-width paths reason about.
        if memory_range_in_element_width(required, available.element_width())
            .is_some_and(|required| memory_range_covers(available, &required, assumptions))
        {
            return true;
        }
        return memory_range_covers(
            &byte_normalized_memory_range(available),
            &byte_normalized_memory_range(required),
            assumptions,
        );
    }
    if available == required {
        return true;
    }
    if available.base().blocks_proven_distinct(required.base()) {
        return false;
    }
    if crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: explicit separation",
        || {
            assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                available, required,
            )
        },
    ) {
        return false;
    }
    if memory_range_covers_with_exact_index(available, required, assumptions) {
        return true;
    }
    if crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: exact endpoints",
        || {
            (pointers_proven_equal_for_memory_resolution(
                available.base(),
                required.base(),
                assumptions,
            ) || pointer_bases_equal_with_load_bridging(
                available.base(),
                required.base(),
                assumptions,
            )) && range_endpoint_terms_equal(available.start(), required.start(), assumptions)
                && range_endpoint_terms_equal(available.end(), required.end(), assumptions)
        },
    ) {
        return true;
    }
    if let Some(covers) = memory_range_structurally_covers(available, required, Some(assumptions)) {
        return covers;
    }
    if crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: derived containment",
        || {
            crate::kernel::assumptions::memory_range_contained_for_memory_resolution(
                required,
                available,
                assumptions,
            )
        },
    ) {
        return true;
    }
    crate::instrumentation::measure_operation(
        "kernel",
        "memory range coverage",
        "memory range coverage: fact range",
        || {
            assumptions.range_covered_by_fact_range(
                required,
                available.base(),
                available.start(),
                available.end(),
            )
        },
    )
}

fn memory_resource_fact_range(fact: &CResourceFact) -> Option<&CMemoryRange> {
    match fact {
        CResourceFact::Own(CResource::Memory(range), _)
        | CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::Own(
            CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
            _,
        )
        | CResourceFact::View(
            CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
        ) => None,
    }
}

/// A constant range as the pair an address statement is made of: the signed
/// index of its first element, and how many elements it holds.
///
/// A range is never read as its two endpoints. `p[start..end)` is
/// `memory_range_byte_count` bytes from the *address* of element `start`, so
/// its element count is the signed value of the 32-bit term `end - start` —
/// the residue, read as `int32`. `end` is `start + count` only while that add
/// does not carry, and `p[i32::MAX..i32::MIN]` is a forward range of exactly
/// one element. Taking the count by the wrapping subtraction and the start by
/// its signed value makes both exact, in `i64`, with nothing left modular.
fn constant_range_extent(range: &CMemoryRange) -> Option<(i64, i64)> {
    let start = range.start().as_const()? as i32;
    let end = range.end().as_const()? as i32;
    Some((i64::from(start), i64::from(end.wrapping_sub(start))))
}

/// Whether `required`, whose first element sits `delta` elements from
/// `available`'s base, lies inside `available`.
///
/// Every input is an exact `i64`, so this is interval containment and owes no
/// premise of its own: the caller's obligation is to have obtained `delta`
/// exactly. A reversed range is refused rather than answered, because neither
/// side of this test means what it reads as when a count runs backwards.
fn constant_extents_contain(
    available: (i64, i64),
    delta: i64,
    required: (i64, i64),
) -> Option<bool> {
    let (available_start, available_count) = available;
    let (required_start, required_count) = required;
    if available_count < 0 || required_count < 0 {
        return None;
    }
    let required_start = delta.checked_add(required_start)?;
    let required_end = required_start.checked_add(required_count)?;
    let available_end = available_start.checked_add(available_count)?;
    Some(available_start <= required_start && required_end <= available_end)
}

/// The delta from `available`'s base to `required`'s, as an exact number of
/// elements.
///
/// `Pointer::element_index_from_base_with_width` answers with one modular
/// term, which names the delta only modulo `2^32`; a containment conclusion
/// reads the delta as a number, so it takes
/// [`Pointer::exact_element_delta_from_base`] instead. That keeps the constant
/// part in `i64` beside at most one symbolic index, and the index's *signed*
/// value is part of the delta — which is why `exact_signed_constant` may be
/// asked for it, and may not be asked for a residue.
fn exact_constant_base_delta(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: Option<&PureFactContext>,
) -> Option<i64> {
    let delta = required.base().exact_element_delta_from_base(
        available.base(),
        available.element_width(),
        assumptions,
    )?;
    if delta.is_constant() {
        return Some(delta.constant);
    }
    crate::kernel::assumptions::exact_signed_constant(&delta.index, assumptions?)?
        .checked_add(delta.constant)
}

/// Containment decided by arithmetic alone, for two ranges whose endpoints are
/// constants and whose bases differ by a constant number of elements.
///
/// This is `memory_range_covers`'s structural arm and it short-circuits the
/// exact derived-containment rule below it, so its positive answer has to be
/// exact for the same reason `memory_range_shallowly_contained`'s is (`b92ab3c0`):
/// the wrapped reading of a residue is `r - 2^32`, which is *outside*, and
/// "covers" holds under neither reading unless the wrap is ruled out. It used
/// to build both relative endpoints with the modular `Bitvector32Term::add`
/// and compare them as an order, so a base `i32::MIN` elements below the owner
/// carried `q[-1..0]` back into it.
///
/// Answering `None` rather than `Some(false)` where the arithmetic no longer
/// settles it matters: `Some` is a short-circuit, and the routes below this one
/// are the exact ones.
fn memory_range_structurally_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: Option<&PureFactContext>,
) -> Option<bool> {
    if available.element_width() != required.element_width() {
        return None;
    }
    let delta = if required.base() == available.base() {
        0
    } else {
        exact_constant_base_delta(available, required, assumptions)?
    };
    constant_extents_contain(
        constant_range_extent(available)?,
        delta,
        constant_range_extent(required)?,
    )
}

fn memory_ranges_structurally_disjoint(left: &CMemoryRange, right: &CMemoryRange) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return true;
    }
    if left.element_width() != right.element_width() {
        return false;
    }
    let Some(base_delta) = right
        .base()
        .element_index_from_base_with_width(left.base(), left.element_width())
    else {
        return false;
    };
    let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
        left.start().as_const().map(|value| value as i32),
        left.end().as_const().map(|value| value as i32),
        Bitvector32Term::add(base_delta.clone(), right.start().clone())
            .as_const()
            .map(|value| value as i32),
        Bitvector32Term::add(base_delta, right.end().clone())
            .as_const()
            .map(|value| value as i32),
    ) else {
        return false;
    };
    left_end < right_start || right_end < left_start
}

/// Decides whether a consumed range runs forward.
///
/// Splitting `available` around `[start, end)` can leave a residue on each
/// side, `[available.start, start)` and `[end, available.end)`. Two such
/// residues overlap exactly when the consumed range runs backwards, so a
/// reversed range such as `p[lo..hi]` with `hi < lo` would hand the holder two
/// owned facts over the same cells. Distinct owned facts are assumed separate,
/// so a store through one would not invalidate a load through the other.
/// Containment does not rule this out: a reversed range is trivially contained
/// in anything.
///
/// This is asked only when both residues survive, since one residue cannot
/// overlap itself; a whole-range consumption of symbolic length stays
/// consumable without deciding its orientation.
///
/// A structural difference covers the ordinary shapes (`p[i..i + 1]`,
/// `p[0..3]`) the way [`memory_range_contained_for_memory_resolution`] already
/// reads them; anything else has to be decided from the context, as
/// `p[0..n]` is under `0 <= n`.
fn consumed_range_is_well_formed(
    start: &Bitvector32Term,
    end: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    // An affine constant difference is the true one only modulo 2^32, so
    // `difference >= 0` is not "runs forward": a difference of 2^32 is a range
    // of zero elements, and one of -2^32 is too. The residue is the count, and
    // reading it as a forward span needs it inside the signed range a count
    // may occupy; anything else falls through to the decision procedure rather
    // than answering from arithmetic that wrapped.
    if let Some(difference) =
        crate::kernel::assumptions::affine_bitvector_difference_constant(end, start)
        && (0..=i64::from(i32::MAX)).contains(&difference)
    {
        return true;
    }
    assumptions.decide(&ConditionTerm::signed_less_equal(
        start.clone(),
        end.clone(),
    )) == Some(true)
}

/// `delta + endpoint`, when that add is the sum rather than its residue.
///
/// [`split_memory_range`] installs these two terms as the *residue ranges' own
/// bounds*, so a carry here hands the holder an owned fact over cells the
/// requirement took away. [`consumed_range_is_well_formed`] cannot see it: it
/// compares the same two wrapped terms with each other, and they are
/// consistent with each other however far they both are from the truth.
///
/// Three routes settle it with no context at all, and they are the shapes a
/// split arrives in: a zero delta, which is the requirement already stated in
/// the owner's coordinates; a zero endpoint, which is a range at the pointer
/// the delta names; and two constants whose sum occupies an `int32`. Anything
/// else is a modular add of a symbolic index, and the one thing that makes it
/// the sum is that it does not carry — which is what it asks.
fn exact_shifted_endpoint(
    delta: &Bitvector32Term,
    endpoint: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    if delta == &Bitvector32Term::Constant(0) {
        return Some(endpoint.clone());
    }
    if endpoint == &Bitvector32Term::Constant(0) {
        return Some(delta.clone());
    }
    if let (Some(delta), Some(endpoint)) = (delta.as_const(), endpoint.as_const()) {
        let sum = i64::from(delta as i32) + i64::from(endpoint as i32);
        return i32::try_from(sum)
            .ok()
            .map(|sum| Bitvector32Term::Constant(sum as u32));
    }
    (assumptions.decide(&ConditionTerm::signed_add_overflows(
        delta.clone(),
        endpoint.clone(),
    )) == Some(false))
    .then(|| Bitvector32Term::add(delta.clone(), endpoint.clone()))
}

/// The owned ranges left to the holder once `required` is taken out of
/// `available`, or `None` where the remainder cannot be stated soundly.
///
/// The requirement's endpoints arrive in its own base's coordinates and the
/// residues are stated in the owner's, so the base delta joins them — and that
/// join has to be the sum and not its residue. See [`exact_shifted_endpoint`]:
/// a carry would leave a retained owned fact over cells the requirement
/// consumed, and distinct owned facts are assumed separate, so a store through
/// one would not invalidate a load through the other.
pub(in crate::kernel) fn split_memory_range(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<Vec<CMemoryRange>> {
    if available.element_width() != required.element_width() {
        // Subtraction is bytewise for the same reason coverage is: the
        // residue is the available bytes the requirement does not name, and
        // the spelling each side arrived in does not change them. Rewriting
        // the requirement into the owner's width keeps the residues in the
        // owner's own coordinate system, so taking a width-1 field out of a
        // width-4 owner leaves width-4 remainders; only bounds that do not
        // divide fall back to the byte footprint of both sides.
        if let Some(required) = memory_range_in_element_width(required, available.element_width()) {
            return split_memory_range(available, &required, assumptions);
        }
        return split_memory_range(
            &byte_normalized_memory_range(available),
            &byte_normalized_memory_range(required),
            assumptions,
        );
    }
    // Prefer the held range's own start form when the required base is
    // provably that address. A merely structural delta can contain an
    // equivalent load from a later memory snapshot; retaining it would create
    // a symbolic zero-length residue when the required range exhausts the
    // beginning of `available`.
    let available_start_pointer = available
        .base()
        .offset_by_elements(available.start().clone(), available.element_width());
    let base_delta = if pointers_proven_equal_for_memory_resolution(
        required.base(),
        &available_start_pointer,
        assumptions,
    ) {
        Some(available.start().clone())
    } else {
        required
            .base()
            .element_index_from_base_with_width(available.base(), available.element_width())
            .or_else(|| {
                pointer_bases_equal_with_load_bridging(
                    required.base(),
                    available.base(),
                    assumptions,
                )
                .then_some(Bitvector32Term::Constant(0))
            })
    }?;
    let required_start = Bitvector32Term::add(base_delta.clone(), required.start().clone());
    let required_end = Bitvector32Term::add(base_delta.clone(), required.end().clone());
    let keeps_prefix =
        !bitvector_terms_proven_equal(available.start(), &required_start, assumptions)
            && !range_endpoint_terms_equal(available.start(), &required_start, assumptions);
    let keeps_suffix = !bitvector_terms_proven_equal(&required_end, available.end(), assumptions)
        && !range_endpoint_terms_equal(&required_end, available.end(), assumptions);
    // A join that becomes a residue's own bound has to be the sum and not its
    // residue; see `exact_shifted_endpoint`. A join that bounds no residue is
    // never read as a position — it has just been shown equal to an endpoint
    // the owner already carried — so it owes nothing.
    if keeps_prefix && exact_shifted_endpoint(&base_delta, required.start(), assumptions).is_none()
    {
        return None;
    }
    if keeps_suffix && exact_shifted_endpoint(&base_delta, required.end(), assumptions).is_none() {
        return None;
    }
    if keeps_prefix
        && keeps_suffix
        && !consumed_range_is_well_formed(&required_start, &required_end, assumptions)
    {
        return None;
    }
    let mut residues = Vec::new();
    if keeps_prefix {
        residues.push(available.with_bounds(
            available.base().clone(),
            available.start().clone(),
            required_start.clone(),
        ));
    }
    if keeps_suffix {
        residues.push(available.with_bounds(
            available.base().clone(),
            required_end,
            available.end().clone(),
        ));
    }
    Some(residues)
}

pub(crate) fn memory_ranges_proven_overlapping(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // Rebase through the indexed, directly stated equalities before asking
    // the same-block range relation. This catches equal addresses whose
    // pointer spellings live in different blocks.
    let aliases = |range: &CMemoryRange| {
        std::iter::once(range.base().clone())
            .chain(assumptions.exact_pointer_aliases(range.base()).cloned())
            .chain(assumptions.exact_pointer_offset_aliases(range.base()))
            .collect::<Vec<_>>()
    };
    let left_aliases = aliases(left);
    let right_aliases = aliases(right);
    for (left_index, left_base) in left_aliases.iter().cloned().enumerate() {
        let left_alias = left.with_bounds(left_base, left.start().clone(), left.end().clone());
        for (right_index, right_base) in right_aliases.iter().cloned().enumerate() {
            if left_index != 0 || right_index != 0 {
                crate::instrumentation::record_deterministic_work(1);
            }
            let right_alias =
                right.with_bounds(right_base, right.start().clone(), right.end().clone());
            if memory_ranges_proven_overlapping_without_aliases(
                &left_alias,
                &right_alias,
                assumptions,
            ) {
                return true;
            }
        }
    }
    false
}

fn memory_ranges_proven_overlapping_without_aliases(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return false;
    }
    // Footprints are bytes (D6): two spellings of overlapping bytes at
    // different element widths overlap, so the memory family's validity check
    // refuses two owners of them. Rewrite both sides to width-1 footprints
    // before deciding, exactly as the loan oracle does
    // (`protected_range_proven_overlapping`).
    if left.element_width() != right.element_width() {
        let left = byte_normalized_memory_range(left);
        let right = byte_normalized_memory_range(right);
        return memory_ranges_proven_overlapping_without_aliases(&left, &right, assumptions);
    }
    if assumptions
        .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(left, right)
    {
        return false;
    }
    let Some(base_delta) = right
        .base()
        .element_index_from_base_with_width(left.base(), left.element_width())
    else {
        return false;
    };
    let right_start = Bitvector32Term::add(base_delta.clone(), right.start().clone());
    let right_end = Bitvector32Term::add(base_delta, right.end().clone());

    assumptions.decide(&ConditionTerm::signed_less_than(
        left.start().clone(),
        right_end,
    )) == Some(true)
        && assumptions.decide(&ConditionTerm::signed_less_than(
            right_start,
            left.end().clone(),
        )) == Some(true)
}

/// The same containment as [`memory_range_structurally_covers`], for a base
/// delta the facts pin rather than the offsets alone.
///
/// An element index is signed: `Pointer::offset_by_elements` sign-extends it
/// before scaling, so element `-1` of `p` is the element below `p`. This read
/// both endpoints of both ranges through `as_const`, which answers `u32`, so a
/// `-1` start arrived as `4294967295` and `p[-1..0]` — the element *before*
/// the range — passed `available_start <= required_start` against every owner
/// whose own end cleared `0`. A caller owning `p[0..1]` could hand `p[-1..0]`
/// to a callee and have it written.
fn memory_range_covers_with_exact_index(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    let Some(delta) = exact_constant_base_delta(available, required, Some(assumptions)) else {
        return false;
    };
    let (Some(available), Some(required)) = (
        constant_range_extent(available),
        constant_range_extent(required),
    ) else {
        return false;
    };
    constant_extents_contain(available, delta, required) == Some(true)
}

impl CResource {
    pub fn family(&self) -> ResourceFamily {
        match self {
            Self::Memory(_) => ResourceFamily::Memory,
            Self::Composite { .. } => ResourceFamily::Composite,
            Self::Token { .. } => ResourceFamily::Token,
            Self::Instance(_) => ResourceFamily::Instance,
        }
    }
}

impl CResourceFact {
    fn has_valid_instance_access(&self) -> bool {
        !matches!(self.resource(), CResource::Instance(_))
            || matches!(self, Self::Own(_, quantity) if quantity.as_const() == Some(1))
    }

    pub const ALLOCATION_RESOURCE_NAME: &'static str = "allocation";

    pub fn own_memory(range: CMemoryRange) -> Self {
        Self::own(CResource::Memory(range))
    }

    pub fn view_memory(range: CMemoryRange) -> Self {
        Self::View(CResource::Memory(range))
    }

    pub fn own_composite(name: String, arguments: Vec<CValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::C).collect();
        Self::own(CResource::Composite { name, arguments })
    }

    pub fn view_composite(name: String, arguments: Vec<CValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::C).collect();
        Self::View(CResource::Composite { name, arguments })
    }

    pub fn own_token(name: String, arguments: Vec<CValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::C).collect();
        Self::own(CResource::Token { name, arguments })
    }

    pub fn own(resource: CResource) -> Self {
        Self::Own(resource, Box::new(Bitvector32Term::Constant(1)))
    }

    pub fn own_quantity(resource: CResource, quantity: Bitvector32Term) -> Self {
        Self::Own(resource, Box::new(quantity))
    }

    pub(crate) fn has_proven_zero_quantity(&self, assumptions: &PureFactContext) -> bool {
        self.has_valid_instance_access()
            && self
                .owned_quantity_term()
                .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
    }

    pub(crate) fn has_proven_positive_quantity(&self, assumptions: &PureFactContext) -> bool {
        self.has_valid_instance_access()
            && self
                .owned_quantity_term()
                .is_some_and(|quantity| resource_quantity_is_positive(quantity, assumptions))
    }

    pub fn own_allocation(base: Pointer, bytes: impl Into<Bitvector32Term>) -> Self {
        let bytes = bytes.into();
        Self::own_token(
            Self::ALLOCATION_RESOURCE_NAME.to_string(),
            vec![CValue::pointer(base), int32(bytes)],
        )
    }

    pub fn allocation(&self) -> Option<(&Pointer, &Bitvector32Term)> {
        let Self::Own(CResource::Token { name, arguments }, _) = self else {
            return None;
        };
        if name != Self::ALLOCATION_RESOURCE_NAME {
            return None;
        }
        let [
            AlgebraicValue::C(CValue::Pointer(base)),
            AlgebraicValue::C(CValue::Int32(bytes)),
        ] = arguments.as_ref()
        else {
            return None;
        };
        Some((base.pointer(), bytes))
    }

    pub(in crate::kernel) fn may_refer_to_memory_block(&self, block: &PointerBlock) -> bool {
        match self.resource() {
            CResource::Memory(range) => &range.base().block == block,
            CResource::Composite { arguments, .. } => arguments.iter().any(
                |argument| matches!(argument, AlgebraicValue::C(CValue::Pointer(pointer)) if &pointer.block == block),
            ),
            CResource::Token { .. } | CResource::Instance(_) => false,
        }
    }

    pub(in crate::kernel) fn is_proven_separate_from_allocation(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> bool {
        self.is_proven_separate_from_allocation_with_element_width(base, bytes, 4, assumptions)
    }

    pub(in crate::kernel) fn is_proven_separate_from_allocation_with_element_width(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        element_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(element_count) =
            crate::kernel::reasoning::element_count_from_bytes(bytes, element_width)
        else {
            return false;
        };
        let allocation_memory = CResource::Memory(CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            element_count,
            element_width,
        ));
        // Exact fact lookup, then the retained atomic separation checker.
        // The general prover added nothing here but its logical fallbacks
        // (context inconsistency, singleton substitution), which are proof
        // search rather than resource theory.
        let right = self.resource().clone();
        assumptions.proves_exact(&Proposition::CResourceSeparate {
            left: allocation_memory.clone(),
            right: right.clone(),
        }) || assumptions.proves_resource_separate(&allocation_memory, &right)
    }

    pub fn view_token(name: String, arguments: Vec<CValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::C).collect();
        Self::View(CResource::Token { name, arguments })
    }

    pub fn resource(&self) -> &CResource {
        match self {
            Self::Own(resource, _) | Self::View(resource) => resource,
        }
    }

    pub fn is_own(&self) -> bool {
        matches!(self, Self::Own(..))
    }

    pub fn is_view(&self) -> bool {
        matches!(self, Self::View(_))
    }

    pub fn family(&self) -> ResourceFamily {
        self.resource().family()
    }

    /// This fact's owner observation, per [`owner_observation_core`]: a viewed
    /// description of ownership this context holds, carrying no access share,
    /// scope, or recovery right of its own.
    pub fn core(&self) -> Option<Self> {
        resource_family_algebra(self.family()).core(self)
    }

    /// [`Self::core`] with a symbolic owned quantity decided against
    /// `assumptions` rather than by constant folding. The same observation
    /// rule, and the same restriction: it is not a capability a call could
    /// carry away, and it never stands in for the checked lend a `views`
    /// requirement takes.
    pub fn core_with_assumptions(&self, assumptions: &PureFactContext) -> Option<Self> {
        if matches!(self.resource(), CResource::Instance(_)) {
            return None;
        }
        match self {
            Self::Own(resource, quantity)
                if resource_quantity_is_positive(quantity.as_ref(), assumptions) =>
            {
                Some(Self::View(resource.clone()))
            }
            Self::Own(_, _) => None,
            Self::View(resource) => Some(Self::View(resource.clone())),
        }
    }

    pub fn memory_own_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range), _) => Some(range),
            Self::Own(
                CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
                _,
            )
            | Self::View(_) => None,
        }
    }

    pub fn memory_view_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::View(CResource::Memory(range)) => Some(range),
            Self::View(
                CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
            )
            | Self::Own(..) => None,
        }
    }

    pub fn memory_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range), _) | Self::View(CResource::Memory(range)) => {
                Some(range)
            }
            Self::Own(
                CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
                _,
            )
            | Self::View(
                CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
            ) => None,
        }
    }

    pub fn owned_resource(&self) -> Option<&CResource> {
        match self {
            Self::Own(resource, _) => Some(resource),
            Self::View(_) => None,
        }
    }

    pub fn owned_quantity(&self) -> Option<u32> {
        match self {
            Self::Own(_, quantity) => quantity.as_const(),
            Self::View(_) => None,
        }
    }

    pub fn owned_quantity_term(&self) -> Option<&Bitvector32Term> {
        match self {
            Self::Own(_, quantity) => Some(quantity.as_ref()),
            Self::View(_) => None,
        }
    }
}

/// Memory-family normalization. The first two arms absorb an entailed fact
/// into the entailing one, which includes an owner swallowing a viewed
/// description of bytes it already covers.
///
/// That case is the owner-observation rule again: the view is a description
/// of ownership this context holds, and dropping a description changes no
/// live access share (the owner-observation rule and law 4 in docs/internals/stable-views.md). It is sound only because a
/// *bound* view never reaches here — `ResourceContext::normalized` skips any
/// entry with a live `loan_dependency` and detaches supported projections
/// first. See [`combine_exact_resource_facts`] for the full argument; the
/// same guard covers both families.
fn combine_memory_resource_facts(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &PureFactContext,
) -> Option<CResourceFact> {
    if let (Some(left_range), Some(right_range)) = (
        memory_resource_fact_range(left),
        memory_resource_fact_range(right),
    ) && memory_ranges_structurally_disjoint(left_range, right_range)
    {
        return None;
    }
    match (left, right) {
        _ if memory_resource_fact_entails(left, right, assumptions) => Some(left.clone()),
        _ if memory_resource_fact_entails(right, left, assumptions) => Some(right.clone()),
        (
            CResourceFact::View(CResource::Memory(left)),
            CResourceFact::View(CResource::Memory(right)),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceFact::view_memory),
        (
            CResourceFact::Own(CResource::Memory(left), _),
            CResourceFact::Own(CResource::Memory(right), _),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceFact::own_memory),
        _ => None,
    }
}

fn merge_memory_ranges(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<CMemoryRange> {
    if left.element_width() != right.element_width() {
        // Bytes that abut still abut under either spelling, so a bytewise
        // split's residue rejoins the owner it came from instead of leaving
        // the context permanently fragmented across two widths.
        if let Some(right) = memory_range_in_element_width(right, left.element_width()) {
            return merge_memory_ranges(left, &right, assumptions);
        }
        let left = memory_range_in_element_width(left, right.element_width())?;
        return merge_memory_ranges(&left, right, assumptions);
    }
    if left.base() != right.base() {
        return None;
    }
    if left.end() == right.start()
        || bitvector_terms_proven_equal(left.end(), right.start(), assumptions)
    {
        return Some(CMemoryRange::new_with_element_width(
            left.base().clone(),
            left.start().clone(),
            right.end().clone(),
            left.element_width(),
        ));
    }
    if right.end() == left.start()
        || bitvector_terms_proven_equal(right.end(), left.start(), assumptions)
    {
        return Some(CMemoryRange::new_with_element_width(
            left.base().clone(),
            right.start().clone(),
            left.end().clone(),
            left.element_width(),
        ));
    }
    None
}

fn bitvector_terms_proven_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || assumptions.decide(&ConditionTerm::equal(left.clone(), right.clone())) == Some(true)
        || assumptions.bitvector_terms_equal_from_facts(left, right)
}

#[cfg(test)]
mod support_removal_tests {
    use super::*;

    #[test]
    fn concrete_interval_rejects_exclusive_end_outside_shared_coordinate_space() {
        let range = CMemoryRange::new(
            Pointer {
                block: "boundary".into(),
                offset: PointerOffsetTerm::Constant(1),
            },
            Bitvector32Term::Constant((i32::MAX - 1) as u32),
            Bitvector32Term::Constant(i32::MAX as u32),
        );
        assert_eq!(concrete_memory_range_bounds(&range), None);
    }

    #[test]
    fn memory_load_footprints_use_checked_snapshot_widths() {
        let short_pointer = Pointer {
            block: "typed-loads".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let wide_pointer = Pointer {
            block: "typed-loads".into(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let memory = CMemory::new()
            .with_block("typed-loads", 24)
            .store(short_pointer.clone(), int16(0))
            .store(
                wide_pointer.clone(),
                CValue::Float64(Bitvector32Term::Constant(0)),
            );
        let short_load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(short_pointer.clone()),
        );
        let wide_load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(wide_pointer.clone()),
        );
        let fact = CResourceFact::view_memory(CMemoryRange::new(
            Pointer {
                block: "result".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            short_load,
            wide_load,
        ));
        let ResourceMemoryFootprint::Exact(ranges) = memory_footprint_for_fact(&fact) else {
            panic!("known typed source cells should yield an exact footprint");
        };
        assert!(
            ranges
                .iter()
                .any(|range| range.base() == &short_pointer && range.element_width() == 2)
        );
        assert!(
            ranges
                .iter()
                .any(|range| range.base() == &wide_pointer && range.element_width() == 8)
        );
    }

    #[test]
    fn memory_load_footprints_reject_mixed_source_snapshots() {
        let pointer = Pointer {
            block: "mixed-loads".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first = CMemory::new()
            .with_block("mixed-loads", 8)
            .store(pointer.clone(), int16(0));
        let second = first.clone().store(pointer.clone(), int16(1));
        let first_load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&first),
            Box::new(pointer.clone()),
        );
        let second_load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&second),
            Box::new(pointer),
        );
        let fact = CResourceFact::view_memory(CMemoryRange::new(
            Pointer {
                block: "mixed-result".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            first_load,
            second_load,
        ));
        assert_eq!(
            memory_footprint_for_fact(&fact),
            ResourceMemoryFootprint::Unknown
        );
    }

    #[test]
    fn memory_load_footprint_depth_is_bounded_conservatively() {
        let pointer = Pointer {
            block: "deep-load".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new()
            .with_block("deep-load", 8)
            .store(pointer.clone(), int16(0));
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(&memory),
            Box::new(pointer),
        );
        let mut nested = load;
        for _ in 0..(MAX_MEMORY_LOAD_FOOTPRINT_DEPTH + 8) {
            nested = Bitvector32Term::Add(Box::new(nested), Box::new(Bitvector32Term::Constant(0)));
        }
        let fact = CResourceFact::view_memory(CMemoryRange::new(
            Pointer {
                block: "deep-result".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            nested,
        ));
        assert_eq!(
            memory_footprint_for_fact(&fact),
            ResourceMemoryFootprint::Unknown
        );
    }

    #[test]
    fn removing_support_cascades_through_nested_projection_chain() {
        let parent = CResourceFact::own_composite("parent".into(), Vec::new());
        let child = CResourceFact::view_token("child".into(), Vec::new());
        let grandchild = CResourceFact::view_token("grandchild".into(), Vec::new());
        let mut context = ResourceContext::new().unchecked_with_fact(parent.clone());
        let parent_entry = *context
            .storage
            .index
            .exact
            .get(&parent)
            .expect("parent entry")
            .iter()
            .next()
            .expect("parent entry id");
        let parent_occurrence = context.occurrence(parent_entry);
        // These direct calls intentionally exercise the internal support graph
        // beyond the public owned-authority constructor: normalization and
        // future observation composition must not leave nested descendants
        // behind when an ancestor is invalidated.
        context.insert_fact_with_support_occurrence(
            child.clone(),
            Some(parent.clone()),
            Some(parent_occurrence),
        );
        let child_entry = *context
            .storage
            .index
            .exact
            .get(&child)
            .expect("child entry")
            .iter()
            .next()
            .expect("child entry id");
        context.insert_fact_with_support_occurrence(
            grandchild.clone(),
            Some(child.clone()),
            Some(context.occurrence(child_entry)),
        );

        context.remove_entry(parent_entry);

        assert!(context.storage.facts.is_empty());
        assert!(context.storage.projections_by_support_occurrence.is_empty());
    }

    #[test]
    fn removing_cyclic_support_graph_terminates_and_cleans_all_nodes() {
        let left = CResourceFact::view_token("left".into(), Vec::new());
        let right = CResourceFact::view_token("right".into(), Vec::new());
        let mut context = ResourceContext::new().unchecked_with_fact(left.clone());
        let left_entry = *context
            .storage
            .index
            .exact
            .get(&left)
            .expect("left entry")
            .iter()
            .next()
            .expect("left entry id");
        let left_occurrence = context.occurrence(left_entry);
        context.insert_fact_with_support_occurrence(
            right.clone(),
            Some(left.clone()),
            Some(left_occurrence),
        );
        let right_entry = *context
            .storage
            .index
            .exact
            .get(&right)
            .expect("right entry")
            .iter()
            .next()
            .expect("right entry id");
        // Build malformed cyclic evidence only to verify the removal guard;
        // production constructors never create this edge.
        context.insert_fact_with_support_occurrence(
            left.clone(),
            Some(right.clone()),
            Some(context.occurrence(right_entry)),
        );

        context.remove_entry(left_entry);

        assert!(context.storage.facts.is_empty());
    }
}
