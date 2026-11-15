//! Persistent pairing of resource occurrences with trusted pointer classes.
//!
//! Equality only selects candidates. Consumption checks the live occurrence's
//! ownership, quantity and coverage in the ordinary resource algebra. Derived
//! roots are excluded from semantic resource equality and fork with the context.
#[cfg(test)]
mod cell_tests;
#[cfg(test)]
mod projection_tests;
mod read_intervals;
mod shape_points;
pub(super) mod structural;
pub(super) mod symbolic;
use read_intervals::ReadIntervals;

use super::*;
use crate::kernel::equality_graph::{AffineOffset, EqualityGraph, PointerClassMerge};

/// A selected full-pointer frame can select the same supplier without entering
/// the caller's unconditional graph. The derived input lineage is local to
/// this query, so an index with its checked union cannot serve a weakened
/// context that no longer proves the frame's authority.
fn graph_for_memory_query(assumptions: &PureFactContext, pointer: &Pointer) -> EqualityGraph {
    let graph = assumptions.equality_graph.clone();
    // A loaded pointer names its read in its block, so an interior access
    // displaces that read by a constant. Check the read itself, with the
    // same complete-cell endpoint evidence, into this query-local graph.
    // Only a pointer the checked walk found stored in the cell is united
    // with the read; another state's read of the same cell is not.
    if matches!(pointer.block, PointerBlock::LoadedPointer(_)) {
        let read = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        if let Some(stored) =
            crate::kernel::memory_provenance::checked_pointer_read_stored_value(&read, assumptions)
        {
            graph.add_checked_read_equality(&read, &stored);
        }
    }
    // A symbolic read identity can sit as an additive prefix of an interior
    // access. Check only those explicit prefixes, using the same complete-cell
    // endpoint evidence as footprint selection; do not publish equality into
    // the caller.
    let mut offsets = vec![&pointer.offset];
    while let Some(offset) = offsets.pop() {
        if let PointerOffsetTerm::Add(left, right) = offset {
            offsets.push(right);
            offsets.push(left);
            continue;
        }
        let selected = Pointer {
            block: pointer.block.clone(),
            offset: offset.clone(),
        };
        if assumptions
            .retained_pointer_read_application(&selected)
            .is_some()
            && let Some(endpoint) = crate::kernel::memory_provenance::checked_pointer_read_endpoint(
                &selected,
                assumptions,
            )
        {
            graph.add_checked_read_equality(&selected, &endpoint);
        }
    }
    graph
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AddressKind {
    OwnedStart,
    ViewedStart,
}

fn range_addresses(range: &MemoryRange, owned: bool) -> Vec<(AddressKind, Pointer)> {
    let addresses = vec![(
        if owned {
            AddressKind::OwnedStart
        } else {
            AddressKind::ViewedStart
        },
        range.start_pointer(),
    )];
    addresses
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AddressCoordinate(AffineOffset);
impl Ord for AddressCoordinate {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.address_order(&other.0)
    }
}
impl PartialOrd for AddressCoordinate {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Positive concrete read cores contribute physical byte intervals.
/// Unsupported entries are counted too: an incomplete interval index can
/// supply positive candidates, but cannot establish a decisive miss.
pub(super) fn read_extent(fact: &ResourceFact) -> Option<u64> {
    if let ResourceFact::Own(_, quantity) = fact
        && !quantity.as_const().is_some_and(|value| (value as i32) > 0)
    {
        return None;
    }
    let range = fact.memory_range()?;
    // Native constant bounds can supply a physical interval only when both
    // scaled endpoints fit the pointer coordinate domain. Symbolic native
    // bounds remain unsupported; their low words never supply an extent.
    if let Some((start, end)) = range.wide_bounds() {
        let start = start.uint64_as_const()?;
        let end = end.uint64_as_const()?;
        let width = u64::from(range.element_width());
        if start >= end || end > i64::MAX as u64 / width {
            return None;
        }
        return end.checked_sub(start)?.checked_mul(width);
    }
    let (start, end) = range.int32_bounds()?;
    let start = start.as_const()? as i32;
    let end = end.as_const()? as i32;
    let count = u64::try_from(i64::from(end) - i64::from(start)).ok()?;
    let width = u64::from(range.element_width());
    let extent = count.checked_mul(width)?;
    (extent > 0).then_some(extent)
}

// A symbolic interval with a constant modular endpoint difference can
// supply a candidate at its exact start. This is only candidate eligibility:
// the ordinary checker still proves signed bounds, width and quantity. Do not
// put such intervals in a complete physical containment summary.
fn start_access_extent(fact: &ResourceFact) -> Option<u64> {
    read_extent(fact).or_else(|| {
        if let ResourceFact::Own(_, quantity) = fact
            && !quantity.as_const().is_some_and(|value| (value as i32) > 0)
        {
            return None;
        }
        let range = fact.memory_range()?;
        let (start, end) = range.int32_bounds()?;
        let count = crate::kernel::assumptions::affine_bitvector_difference_constant(end, start)?;
        let count = u64::try_from(count).ok()?;
        (count > 0 && count <= i32::MAX as u64)
            .then_some(count.checked_mul(u64::from(range.element_width()))?)
    })
}

// Whole-cell candidates carry their own authorized read footprints. The existing int32-slot interpretation of pointer reads is special:
// eight bytes may read one logical four-byte element, including an interior
// element of a longer range. Those partial reads retain the range checker.
fn exact_access_sizes(fact: &ResourceFact) -> Vec<u32> {
    let Some(extent) = read_extent(fact).and_then(|extent| u32::try_from(extent).ok()) else {
        return Vec::new();
    };
    let width = fact.memory_range().expect("memory extent").element_width();
    match (extent, width) {
        (8, 4) => Vec::new(),
        (4, 4) => vec![4, 8],
        _ => vec![extent],
    }
}

#[derive(Clone, Debug, Default)]
struct AddressBucket {
    /// Bucket coordinates can differ from the graph representative. Choosing
    /// the larger payload's coordinates lets merges move only the smaller
    /// resource payload, even when the graph chooses the other representative.
    origin: AffineOffset,
    entries: PersistentMap<(AddressKind, AddressCoordinate), ResourceEntryIds>,
    weight: usize,
    read_intervals: ReadIntervals,
    // Writes must not enumerate covering views before reaching an owner.
    // Both summaries follow the same persistent updates and class merges.
    write_intervals: ReadIntervals,
    // All memory owners, independently of views or representable extents.
    // Cardinality selects a sole supplier; quantity and bounds are checked later.
    owners: ResourceEntryIds,
    suppliers: ResourceEntryIds,
    memory_count: usize,
    // Structural queries require constant raw start coordinates.
    general_coordinates: usize,
}

#[derive(Clone, Debug, Default)]
pub(super) struct MemoryAddresses {
    classes: PersistentMap<PointerBlock, AddressBucket>,
}

impl MemoryAddresses {
    pub(super) fn update(
        &mut self,
        range: &MemoryRange,
        owned: bool,
        entry: ResourceEntryId,
        insert: bool,
        fact: &ResourceFact,
    ) {
        let extent = read_extent(fact);
        for (kind, pointer) in range_addresses(range, owned) {
            let Some(offset) = AffineOffset::of(&pointer.offset) else {
                continue;
            };
            self.update_coordinate(pointer.block, kind, offset, entry, insert, extent);
        }
        self.update_memory_count(range.base().block.clone(), entry, owned, insert);
    }

    fn update_in_graph(
        &mut self,
        range: &MemoryRange,
        owned: bool,
        entry: ResourceEntryId,
        insert: bool,
        graph: &EqualityGraph,
        fact: &ResourceFact,
    ) {
        // Track unsupported offsets too: they must prevent a decisive
        // indexed miss, even when they contribute no address row.
        let Some(base) = graph.canonical_pointer(&Pointer {
            block: range.base().block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        }) else {
            return;
        };
        let extent = read_extent(fact);
        for (kind, pointer) in range_addresses(range, owned) {
            let Some(pointer) = graph.canonical_pointer(&pointer) else {
                continue;
            };
            self.update_coordinate(
                pointer.representative,
                kind,
                pointer.offset,
                entry,
                insert,
                extent,
            );
        }
        self.update_memory_count(base.representative, entry, owned, insert);
    }

    fn update_memory_count(
        &mut self,
        block: PointerBlock,
        entry: ResourceEntryId,
        owned: bool,
        insert: bool,
    ) {
        let mut bucket = self.classes.get(&block).cloned().unwrap_or_default();
        if owned {
            bucket.owners = if insert {
                bucket.owners.with_value(entry)
            } else {
                bucket.owners.without_value(&entry)
            };
        }
        bucket.suppliers = if insert {
            bucket.suppliers.with_value(entry)
        } else {
            bucket.suppliers.without_value(&entry)
        };
        if insert {
            bucket.memory_count += 1;
        } else {
            bucket.memory_count -= 1;
        }
        self.classes = if bucket.weight == 0 && bucket.memory_count == 0 {
            self.classes.without_key(&block)
        } else {
            self.classes.with_inserted(block, bucket)
        };
    }

    fn update_coordinate(
        &mut self,
        block: PointerBlock,
        kind: AddressKind,
        offset: AffineOffset,
        entry: ResourceEntryId,
        insert: bool,
        read_extent: Option<u64>,
    ) {
        let mut bucket = self.classes.get(&block).cloned().unwrap_or_default();
        let Some(key) = offset.checked_add(&bucket.origin) else {
            return;
        };
        let general = !key.is_constant();
        let key = (kind, AddressCoordinate(key));
        let entries = bucket.entries.get(&key).cloned().unwrap_or_default();
        let present = entries.contains(&entry);
        if insert == present {
            return;
        }
        if let Some(extent) = read_extent {
            for intervals in std::iter::once(&mut bucket.read_intervals)
                .chain((key.0 == AddressKind::OwnedStart).then_some(&mut bucket.write_intervals))
            {
                if insert {
                    if let Some(end) = key
                        .1
                        .0
                        .checked_add(&AffineOffset::constant(i128::from(extent)))
                    {
                        intervals.insert(key.1.clone(), AddressCoordinate(end), entry);
                    }
                } else {
                    intervals.remove(key.1.clone(), entry);
                }
            }
        }
        if insert {
            bucket.entries = bucket.entries.with_inserted(key, entries.with_value(entry));
            bucket.weight += 1;
            bucket.general_coordinates += usize::from(general);
        } else {
            let entries = entries.without_value(&entry);
            bucket.entries = if entries.is_empty() {
                bucket.entries.without_key(&key)
            } else {
                bucket.entries.with_inserted(key, entries)
            };
            bucket.weight -= 1;
            bucket.general_coordinates -= usize::from(general);
        }
        self.classes = if bucket.weight == 0 && bucket.memory_count == 0 {
            self.classes.without_key(&block)
        } else {
            self.classes.with_inserted(block, bucket)
        };
    }

    fn merge(&mut self, merge: PointerClassMerge) {
        let Some(moved) = self.classes.get(&merge.moved).cloned() else {
            return;
        };
        let kept = self.classes.get(&merge.kept).cloned().unwrap_or_default();
        self.classes = self.classes.without_key(&merge.moved);
        let (mut larger, smaller, shift) = if moved.weight <= kept.weight {
            let Some(shift) = merge
                .moved_from_kept
                .checked_add(&kept.origin)
                .and_then(|value| value.checked_sub(&moved.origin))
            else {
                return;
            };
            (kept, moved, shift)
        } else {
            let Some(origin) = moved.origin.checked_sub(&merge.moved_from_kept) else {
                return;
            };
            let Some(shift) = origin.checked_sub(&kept.origin) else {
                return;
            };
            let mut moved = moved;
            moved.origin = origin;
            (moved, kept, shift)
        };
        larger.memory_count += smaller.memory_count;
        for entry in smaller.suppliers.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger.suppliers = larger.suppliers.with_value(*entry);
        }
        for entry in smaller.owners.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger.owners = larger.owners.with_value(*entry);
        }
        for (larger_intervals, smaller_intervals) in [
            (&mut larger.read_intervals, &smaller.read_intervals),
            (&mut larger.write_intervals, &smaller.write_intervals),
        ] {
            for (start, end, entry) in smaller_intervals.iter() {
                let Some(start) = start.0.checked_add(&shift) else {
                    continue;
                };
                let Some(end) = end.0.checked_add(&shift) else {
                    continue;
                };
                larger_intervals.insert(AddressCoordinate(start), AddressCoordinate(end), entry);
            }
        }
        for ((kind, offset), entries) in smaller.entries.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let Some(offset) = offset.0.checked_add(&shift) else {
                continue;
            };
            let general = !offset.is_constant();
            let offset = (kind.clone(), AddressCoordinate(offset));
            let mut combined = larger.entries.get(&offset).cloned().unwrap_or_default();
            for entry in entries.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if !combined.contains(entry) {
                    combined = combined.with_value(*entry);
                    larger.weight += 1;
                    larger.general_coordinates += usize::from(general);
                }
            }
            larger.entries = larger.entries.with_inserted(offset, combined);
        }
        self.classes = self.classes.with_inserted(merge.kept, larger);
    }
}

#[derive(Clone)]
pub(super) struct PairedMemoryIndex {
    resources: std::sync::Arc<ResourceContextStorage>,
    graph: EqualityGraph,
    // Queries may register read definitions in `graph`. Payload coordinates
    // belong to this immutable checkpoint until their merge delta is applied.
    indexed_graph: EqualityGraph,
    addresses: MemoryAddresses,
    points: AddressPoints,
    shapes: shape_points::ShapePoints,
    symbolic: symbolic::RangeSupports,
    points_initialized: bool,
}

/// Disposable derived views keyed by admitted equality inputs. Term registrations
/// may differ across forks; they are never used as proof-context identities.
#[derive(Clone, Default)]
pub(super) struct MemoryPairings {
    by_inputs:
        PersistentMap<crate::kernel::equality_graph::InputKey, std::sync::Arc<PairedMemoryIndex>>,
    published: Option<std::sync::Arc<PairedMemoryIndex>>,
    // One producer-selected caller boundary, before temporary opening facts.
    // It has no memory payload and is refreshed while the input remains empty.
    empty_caller: Option<std::sync::Arc<PairedMemoryIndex>>,
}

/// A payload attached to typed address classes in the trusted graph. It has
/// no equality solver of its own: graph merges move only affected entries.
#[derive(Clone, Default)]
struct AddressPointBucket {
    // Fold selection considers every occurrence. Reads select only entries
    // with the requested checked footprint, independent of other shapes at
    // this address or elsewhere in the pointer-block class.
    entries: ResourceEntryIds,
    // Symbolic fragment selection must not enumerate views to find an owner.
    owners: ResourceEntryIds,
    reads: PersistentMap<u32, ResourceEntryIds>,
    // Writes require their own payload: a read footprint may contain only
    // views, even when a larger owner shares the same start address.
    writes: PersistentMap<u32, ResourceEntryIds>,
    read_capacities: PersistentMap<u64, ResourceEntryIds>,
    write_capacities: PersistentMap<u64, ResourceEntryIds>,
}

#[derive(Clone, Default)]
struct AddressPoints {
    classes: PersistentMap<u64, AddressPointBucket>,
    entries: PersistentMap<ResourceEntryId, u64>,
}
impl AddressPoints {
    fn merge(&mut self, moved: u64, kept: u64) {
        let Some(mut smaller) = self.classes.get(&moved).cloned() else {
            return;
        };
        let mut larger = self.classes.get(&kept).cloned().unwrap_or_default();
        self.classes.remove(&moved);
        if larger.entries.len() < smaller.entries.len() {
            std::mem::swap(&mut larger, &mut smaller);
        }
        for entry in smaller.entries.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger.entries = larger.entries.with_value(*entry);
        }
        for entry in smaller.owners.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger.owners = larger.owners.with_value(*entry);
        }
        // Each occurrence contributes at most two footprints per access kind. Using the
        // same smaller occurrence payload for both indexes bounds all moves,
        // even when the graph chooses the other class representative.
        for (larger_access, smaller_access) in [
            (&mut larger.reads, &smaller.reads),
            (&mut larger.writes, &smaller.writes),
        ] {
            for (bytes, entries) in smaller_access.iter() {
                let mut combined = larger_access.get(bytes).cloned().unwrap_or_default();
                for entry in entries.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    combined = combined.with_value(*entry);
                }
                larger_access.insert(*bytes, combined);
            }
        }
        for (larger_access, smaller_access) in [
            (&mut larger.read_capacities, &smaller.read_capacities),
            (&mut larger.write_capacities, &smaller.write_capacities),
        ] {
            for (bytes, entries) in smaller_access.iter() {
                let mut combined = larger_access.get(bytes).cloned().unwrap_or_default();
                for entry in entries.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    combined = combined.with_value(*entry);
                }
                larger_access.insert(*bytes, combined);
            }
        }
        self.classes.insert(kept, larger);
    }
    fn update(
        &mut self,
        entry: ResourceEntryId,
        insert: bool,
        fact: &ResourceFact,
        graph: &EqualityGraph,
    ) {
        let Some(range) = fact.memory_range() else {
            return;
        };
        let class = if insert {
            let start = range.start_pointer();
            let Some(class) = graph.address_class(&start) else {
                return;
            };
            self.entries.insert(entry, class);
            class
        } else {
            let Some(class) = self.entries.get(&entry).copied() else {
                return;
            };
            self.entries.remove(&entry);
            graph.address_class_root(class)
        };
        let mut bucket = self.classes.get(&class).cloned().unwrap_or_default();
        bucket.entries = if insert {
            bucket.entries.with_value(entry)
        } else {
            bucket.entries.without_value(&entry)
        };
        if fact.is_own() {
            bucket.owners = if insert {
                bucket.owners.with_value(entry)
            } else {
                bucket.owners.without_value(&entry)
            };
        }
        if let Some(extent) = start_access_extent(fact) {
            for access in std::iter::once(&mut bucket.read_capacities)
                .chain(fact.is_own().then_some(&mut bucket.write_capacities))
            {
                let entries = access.get(&extent).cloned().unwrap_or_default();
                let entries = if insert {
                    entries.with_value(entry)
                } else {
                    entries.without_value(&entry)
                };
                if entries.is_empty() {
                    access.remove(&extent);
                } else {
                    access.insert(extent, entries);
                }
            }
        }
        let sizes = exact_access_sizes(fact);
        for access in
            std::iter::once(&mut bucket.reads).chain(fact.is_own().then_some(&mut bucket.writes))
        {
            for bytes in &sizes {
                let entries = access.get(bytes).cloned().unwrap_or_default();
                let entries = if insert {
                    entries.with_value(entry)
                } else {
                    entries.without_value(&entry)
                };
                if entries.is_empty() {
                    access.remove(bytes);
                } else {
                    access.insert(*bytes, entries);
                }
            }
        }
        if bucket.entries.is_empty() {
            self.classes.remove(&class);
        } else {
            self.classes.insert(class, bucket);
        }
    }
}

pub(super) enum MemoryAccessEntries {
    Intervals(read_intervals::CoveringIntervals),
    Relative(Box<dyn Iterator<Item = ResourceEntryId>>),
    Prefixed(Option<ResourceEntryId>, read_intervals::CoveringIntervals),
    Exact(crate::persistent::OwnedSetValues<ResourceEntryId>),
    SingleSupplier(Option<ResourceEntryId>),
    Structural(std::collections::btree_set::IntoIter<ResourceEntryId>),
}
impl Iterator for MemoryAccessEntries {
    type Item = ResourceEntryId;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Intervals(entries) => entries.next(),
            Self::Relative(entries) => entries.next(),
            Self::Prefixed(first, entries) => first.take().or_else(|| entries.next()),
            Self::Exact(entries) => entries.next(),
            Self::SingleSupplier(entry) => entry.take(),
            Self::Structural(entries) => entries.next(),
        }
    }
}
impl MemoryAccessEntries {
    pub(super) fn exact(&self) -> bool {
        matches!(self, Self::Exact(_))
    }
}

/// Candidates and their address evidence retain the same private graph
/// checkpoint. Class IDs and representative coordinates never cross forks.
pub(super) struct MemoryAccessCandidates {
    entries: MemoryAccessEntries,
    query: Pointer,
    index: std::sync::Arc<PairedMemoryIndex>,
    preferred_owner: Option<(ResourceEntryId, bool)>,
}
impl Iterator for MemoryAccessCandidates {
    type Item = ResourceEntryId;
    fn next(&mut self) -> Option<Self::Item> {
        let Some((owner, pending)) = &mut self.preferred_owner else {
            return self.entries.next();
        };
        if std::mem::take(pending) {
            return Some(*owner);
        }
        let owner = *owner;
        self.entries.find(|entry| *entry != owner)
    }
}
/// One implicit supplier selected by the address/width index. A failed quantity,
/// provenance, or containment check is final; checking cannot request alternatives.
/// Explicit footprint composition keeps its separate, output-sensitive iterator.
pub(super) struct SelectedMemoryAccess {
    source: MemoryAccessCandidates,
    entry: ResourceEntryId,
}
impl SelectedMemoryAccess {
    pub(super) fn entry(&self) -> ResourceEntryId {
        self.entry
    }
    pub(super) fn address(&self) -> Option<Pointer> {
        self.source.address(self.entry)
    }
}
impl MemoryAccessCandidates {
    fn select(mut self) -> Option<SelectedMemoryAccess> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select indexed memory supplier", 1);
        let entry = self.next()?;
        Some(SelectedMemoryAccess {
            source: self,
            entry,
        })
    }

    // Affine interval hits are tentative. A view of a split prefix must not
    // hide the sole owner of the query's selected base. Keep the supplier in
    // this same graph checkpoint and let the ordinary consumer check it.
    fn prefer_owned_supplier(mut self, read: bool, bytes: u32) -> Self {
        if read && !self.entries.exact() {
            let direct = ResourceContext::sole_access_supplier(&self.index, &self.query, true);
            let owner = direct.or_else(|| {
                (!matches!(self.query.offset, PointerOffsetTerm::Add(_, _)))
                    .then(|| self.index.graph.additive_address(&self.query))
                    .flatten()
                    .and_then(|query| {
                        ResourceContext::sole_access_supplier(&self.index, &query, true)
                    })
            });
            // Structural supplier indexes also retain zero quantities and
            // other fields of the same object. Such an owner must not hide the
            // interval selected for this access. Read only this occurrence's
            // indexed coordinates; unknown symbolic coverage remains tentative.
            self.preferred_owner = owner
                .filter(|entry| {
                    let Some(fact) = self.index.resources.facts.get(entry) else {
                        return false;
                    };
                    if fact
                        .owned_quantity_term()
                        .and_then(|quantity| quantity.as_const())
                        == Some(0)
                    {
                        return false;
                    }
                    let in_span = || {
                        let range = fact.memory_range()?;
                        let start = i128::from(range.signed_constant_start()?)
                            * i128::from(range.element_width());
                        let end = i128::from(range.signed_constant_end()?)
                            * i128::from(range.element_width());
                        let query = self.index.graph.canonical_pointer(&self.query)?;
                        let base = self.index.graph.canonical_pointer(range.base())?;
                        if query.representative != base.representative {
                            return None;
                        }
                        let offset = query.offset.constant_difference(&base.offset)?;
                        let bytes = i128::from(
                            crate::kernel::assumptions::read_candidate_byte_width(bytes),
                        );
                        Some(start <= offset && offset.checked_add(bytes)? <= end)
                    };
                    in_span() != Some(false)
                })
                .map(|entry| (entry, true));
        }
        self
    }

    #[cfg(test)]
    fn exact(&self) -> bool {
        self.entries.exact()
    }

    /// Align the retained occurrence against this query and this graph fork.
    /// Consumers supply an occurrence ID, never an alternate pointer spelling
    /// or a reconstructed range. Equality supplies evidence, not permission;
    /// the ordinary checker still validates quantity, width and containment.
    pub(super) fn address(&self, entry: ResourceEntryId) -> Option<Pointer> {
        let range = self.index.resources.facts.get(&entry)?.memory_range()?;
        if self.entries.exact() {
            let start = range.start_pointer();
            self.index
                .graph
                .are_equal(&self.query, &start)
                .then_some(start)
        } else {
            if range.wide_bounds().is_some() {
                // A narrow alias can share this address while carrying none
                // of the bounds stated on its native producer's index.
                // Preserve that index as borrow matching already does; the
                // caller still checks width, quantity, and containment.
                return self
                    .index
                    .graph
                    .pointer_at_base_with_wide_index(&self.query, range.base());
            }
            if let Some(address) = self
                .index
                .graph
                .pointer_at_constant_base(&self.query, range.base())
            {
                return Some(address);
            }
            let spelling = if matches!(self.query.offset, PointerOffsetTerm::Add(_, _)) {
                self.query.clone()
            } else {
                self.index
                    .graph
                    .additive_address(&self.query)
                    .unwrap_or_else(|| self.query.clone())
            };
            self.index.graph.pointer_at_base(&spelling, range.base())
        }
    }
}

/// Pure composition provenance is a derived source index, not a resource
/// context that callers may consume. It retains its first source's persistent
/// storage and adds only explicitly admitted source deltas thereafter.
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct ObjectEvidenceSources {
    resources: ResourceContext,
    partition_sources: PersistentMap<Pointer, imbl::Vector<ResourceContext>>,
    source_checkpoints: PersistentMap<usize, ResourceContext>,
    // Address selection retains only producer-published inputs. Raw provenance
    // sources remain cheap to hold and never initialize a logical read index.
    address_resources: ResourceContext,
    address_source_checkpoints: PersistentMap<usize, ResourceContext>,
}
impl ObjectEvidenceSources {
    pub(in crate::kernel) fn admit(&mut self, source: &ResourceContext) {
        if !source.loan_dependencies.map.is_empty() {
            let origin = std::sync::Arc::as_ptr(&source.storage.origin) as usize;
            let delta = self
                .source_checkpoints
                .get(&origin)
                .and_then(|prior| source.changed_memory_inputs_from(prior));
            let facts = delta.unwrap_or_else(|| source.iter().cloned().collect());
            let mut bases = facts
                .iter()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .filter_map(|fact| fact.memory_range())
                .map(|range| range.base().clone())
                .collect::<std::collections::BTreeSet<_>>();
            if let Some(prior) = self.source_checkpoints.get(&origin) {
                for occurrence in source
                    .loan_dependencies
                    .changed_occurrences_since(&prior.loan_dependencies)
                {
                    if let Some(binding) = source.loan_dependency(occurrence)
                        && let Some(range) = binding.viewed.memory_range()
                    {
                        bases.insert(range.base().clone());
                    }
                }
            }
            for base in bases {
                crate::instrumentation::record_deterministic_work(1);
                let mut sources = self
                    .partition_sources
                    .get(&base)
                    .cloned()
                    .unwrap_or_default();
                sources.push_back(source.clone());
                self.partition_sources.insert(base, sources);
            }
        }
        Self::admit_into(&mut self.resources, &mut self.source_checkpoints, source);
        if !source.storage.index.memory_by_block.is_empty()
            && source
                .memory_equalities
                .lock()
                .expect("memory equality index")
                .published
                .is_some()
        {
            Self::admit_into(
                &mut self.address_resources,
                &mut self.address_source_checkpoints,
                source,
            );
        }
    }

    /// Only sources that changed a queried address are candidates. Persistent
    /// delta admission avoids rescanning unchanged resources or proof history.
    pub(in crate::kernel) fn partition_sources_at<'a>(
        &'a self,
        pointers: &[&Pointer],
    ) -> impl Iterator<Item = &'a ResourceContext> {
        let mut keys = std::collections::BTreeSet::new();
        for pointer in pointers {
            let mut base = (*pointer).clone();
            loop {
                keys.insert(base.clone());
                base.offset = match &base.offset {
                    PointerOffsetTerm::Add(left, _) => (**left).clone(),
                    PointerOffsetTerm::Constant(value) if *value != 0 => {
                        PointerOffsetTerm::Constant(0)
                    }
                    _ => break,
                };
            }
        }
        keys.into_iter().flat_map(move |key| {
            crate::instrumentation::record_deterministic_work(1);
            self.partition_sources
                .get(&key)
                .into_iter()
                .flat_map(|sources| sources.iter().rev())
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
        })
    }

    fn admit_into(
        resources: &mut ResourceContext,
        checkpoints: &mut PersistentMap<usize, ResourceContext>,
        source: &ResourceContext,
    ) {
        // Retained sources keep their origin alive; keys cannot be reused.
        let origin = std::sync::Arc::as_ptr(&source.storage.origin) as usize;
        let delta = checkpoints
            .get(&origin)
            .and_then(|prior| source.changed_memory_inputs_from(prior));
        if resources.is_empty() {
            *resources = source.clone();
        } else if let Some(delta) = delta {
            *resources = resources.clone().unchecked_with_facts(delta);
        } else {
            // Raw and observable forms can share memory inputs without
            // sharing an admission history. Compare their persistent input
            // indexes, admitting only facts absent from the accumulated set.
            let held = resources.memory_input_facts();
            let incoming = source.memory_input_facts();
            let added = if incoming.len() < held.len() {
                // A small contract beside a large caller frame: removed
                // caller facts are irrelevant to monotone admission.
                incoming
                    .keys()
                    .filter(|fact| !held.contains_key(*fact))
                    .cloned()
                    .collect::<Vec<_>>()
            } else {
                held.diff(incoming)
                    .filter_map(|change| match change {
                        HashedOrdMapChange::Added(fact) => Some(fact.clone()),
                        HashedOrdMapChange::Changed(_) | HashedOrdMapChange::Removed(_) => None,
                    })
                    .collect::<Vec<_>>()
            };
            *resources = resources.clone().unchecked_with_facts(added);
        }
        checkpoints.insert(origin, source.clone());
    }

    /// Apply admitted class deltas at their producer, so selecting a logical
    /// address never catches up by walking unrelated equality history.
    pub(in crate::kernel) fn advance_memory_equalities(&self, assumptions: &PureFactContext) {
        self.address_resources
            .advance_prepared_memory_equalities(assumptions);
    }

    /// Select one admitted footprint's address coordinates through the class
    /// index. Its quantity and extent grant no authority to a logical read.
    pub(in crate::kernel) fn memory_address_spelling(
        &self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> Option<Pointer> {
        // A logical read cannot publish an ambient input or initialize its
        // suppliers. Construction and checked proof boundaries do that work.
        self.address_resources
            .memory_equalities
            .lock()
            .expect("memory equality index")
            .published
            .as_ref()?;
        let candidates = self
            .address_resources
            .read_access(pointer, 1, assumptions)?;
        let entry = candidates.entry();
        let range = candidates
            .source
            .index
            .resources
            .facts
            .get(&entry)?
            .memory_range()?;
        // A loaded pointer can have a variable offset within its storage
        // block. Preserve the supplier's complete base, rather than asking
        // for a constant displacement from that block's zero coordinate.
        candidates
            .source
            .index
            .graph
            .pointer_at_constant_base(pointer, range.base())
    }

    pub(in crate::kernel) fn memory_object_evidence(
        &self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> Option<&ResourceFact> {
        self.resources.memory_object_evidence(pointer, assumptions)
    }
}

/// Explicit supplier occurrences and the graph checkpoint which selected them.
/// Consumers cannot replace this evidence with a spelling from another fork.
pub(super) struct MemoryFactCandidates {
    pub(super) entries: MemoryFactEntries,
    index: std::sync::Arc<PairedMemoryIndex>,
}
/// One explicit bound in object-relative element coordinates. This is a
/// candidate key, not a numeric equality or a provenance judgment: combining
/// bitvector indices can wrap, and ordinary coverage/merging must validate the
/// selected original footprints. No alternative resource spelling is tried.
fn memory_candidate_coordinate(
    range: &MemoryRange,
    bound: &MachineTerm,
) -> Option<(Pointer, SharedMachineIntegerTerm)> {
    let base = range.base().object_base();
    let delta = range
        .base()
        .exact_element_delta_from_base(&base, range.element_width(), None)?;
    let constant = i32::try_from(delta.constant).ok()? as u32;
    Some((
        base,
        crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Add,
            crate::kernel::assumptions::index_binary(
                MachineBinaryOp::Add,
                delta.index.operand_view(),
                MachineOperandView::Legacy(bound),
            )
            .operand_view(),
            MachineOperandView::Legacy(&MachineTerm::constant(constant)),
        ),
    ))
}

/// Supplier delivery is lazy: a direct proof pays only for the occurrences it
/// checks. Only explicit fragment composition exhausts the selected frontier.
pub(super) struct MemoryFactEntries {
    index: std::sync::Arc<PairedMemoryIndex>,
    range: MemoryRange,
    owned: bool,
    assumptions: PureFactContext,
    bound_coordinates: Option<(Pointer, SharedMachineIntegerTerm)>,
}
impl MemoryFactEntries {
    /// Nominate one whole-range supplier. Fragment starts, fragment chains,
    /// and incident order premises belong to composition/search, not this
    /// single-owner query. The consumer checks the nominated entry once.
    pub(super) fn single_supplier(&self) -> Option<ResourceEntryId> {
        crate::instrumentation::record_deterministic_work(1);
        let index = &self.index;
        let range = &self.range;
        let exact = if self.owned {
            ResourceFact::own_memory(range.clone())
        } else {
            ResourceFact::view_memory(range.clone())
        };
        if let Some(entries) = index.resources.index.exact.get(&exact) {
            return entries.iter().next().copied();
        }
        if let Some(entries) = index
            .resources
            .index
            .by_resource
            .get(&Resource::Memory(range.clone()))
            && entries.len() == 1
        {
            let entry = *entries.iter().next()?;
            if !self.owned || index.resources.facts.get(&entry)?.is_own() {
                return Some(entry);
            }
        }
        let graph = &index.graph;
        if index.points_initialized {
            if let Some(class) = graph.footprint_class(range)
                && let Some(entries) = index.symbolic.footprint_entries(class, self.owned)
                && entries.len() == 1
            {
                return entries.iter().next().copied();
            }
            // An exact start address with one supplier is more precise than
            // a tentative affine covering interval. In particular x[j..j+1]
            // must supply x+j before an unrelated symbolic prefix is tried.
            if let Some(class) = graph.address_class(&range.start_pointer())
                && let Some(bucket) = index.points.classes.get(&class)
            {
                let entries = if self.owned {
                    &bucket.owners
                } else {
                    &bucket.entries
                };
                if entries.len() == 1 {
                    return entries.iter().next().copied();
                }
            }
            if let Some(mut entries) = index.symbolic.relative_entries(range, self.owned, graph)
                && let Some(entry) = entries.next()
            {
                return Some(entry);
            }
        }
        let start_pointer = range.start_pointer();
        let end_pointer = range.end_pointer();
        if let (Some(point), Some(limit)) = (
            graph.canonical_pointer(&start_pointer),
            graph.canonical_pointer(&end_pointer),
        ) && point.representative == limit.representative
            && limit
                .offset
                .constant_difference(&point.offset)
                .is_some_and(|bytes| bytes > 0)
            && let Some(bucket) = index.addresses.classes.get(&point.representative)
            && let (Some(start), Some(end)) = (
                point.offset.checked_add(&bucket.origin),
                limit.offset.checked_add(&bucket.origin),
            )
        {
            let intervals = if self.owned {
                &bucket.write_intervals
            } else {
                &bucket.read_intervals
            };
            if let Some(entry) = intervals
                .covering(&AddressCoordinate(start), &AddressCoordinate(end))
                .next()
            {
                return Some(entry);
            }
        }
        if !index.points_initialized {
            return None;
        }
        ResourceContext::sole_access_supplier(index, &start_pointer, self.owned)
            .or_else(|| ResourceContext::sole_affine_supplier(index, &start_pointer, self.owned))
    }

    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.iter().count()
    }

    pub(super) fn iter(&self) -> Box<dyn Iterator<Item = ResourceEntryId> + '_> {
        let index = &self.index;
        let graph = &index.graph;
        let range = &self.range;
        let owned = self.owned;
        let mut streams: Vec<Box<dyn Iterator<Item = ResourceEntryId> + '_>> = Vec::new();
        // Exact typed footprints need no publication or equality inference.
        // This also supports explicitly supplied, unpublished symbolic inputs.
        if let Some(entries) = index
            .resources
            .index
            .by_resource
            .get(&Resource::Memory(range.clone()))
        {
            streams.push(Box::new(entries.clone().owned_values()));
        }
        if index.points_initialized
            && let Some(class) = graph.footprint_class(range)
            && let Some(entries) = index.symbolic.footprint_entries(class, owned)
        {
            streams.push(Box::new(entries.owned_values()));
        }
        if index.points_initialized
            && let Some(entries) = index.symbolic.relative_entries(range, owned, graph)
        {
            streams.push(entries);
        }
        let start_pointer = range.start_pointer();
        let end_pointer = range.end_pointer();
        if let (Some(point), Some(limit)) = (
            graph.canonical_pointer(&start_pointer),
            graph.canonical_pointer(&end_pointer),
        ) && point.representative == limit.representative
            && limit
                .offset
                .constant_difference(&point.offset)
                .is_some_and(|bytes| bytes > 0)
            && let Some(bucket) = index.addresses.classes.get(&point.representative)
            && let (Some(start), Some(end)) = (
                point.offset.checked_add(&bucket.origin),
                limit.offset.checked_add(&bucket.origin),
            )
        {
            let intervals = if owned {
                &bucket.write_intervals
            } else {
                &bucket.read_intervals
            };
            // Check whole-span suppliers before the fragment frontier. Otherwise
            // a late owner can be hidden behind arbitrarily many short views.
            streams.push(Box::new(intervals.covering(
                &AddressCoordinate(start.clone()),
                &AddressCoordinate(end.clone()),
            )));
            if let Some(after) = start.checked_add(&AffineOffset::constant(1)) {
                streams.push(Box::new(intervals.covering(
                    &AddressCoordinate(start.clone()),
                    &AddressCoordinate(after),
                )));
            }
            for kind in std::iter::once(AddressKind::OwnedStart)
                .chain((!owned).then_some(AddressKind::ViewedStart))
            {
                let entries = bucket.entries.clone();
                let mut cursor = (kind.clone(), AddressCoordinate(start.clone()));
                let mut current = entries
                    .get(&cursor)
                    .cloned()
                    .unwrap_or_default()
                    .owned_values();
                let end = end.clone();
                streams.push(Box::new(std::iter::from_fn(move || {
                    loop {
                        if let Some(entry) = current.next() {
                            return Some(entry);
                        }
                        let (next, values) = entries.get_greater_than(&cursor)?;
                        if next.0 != kind
                            || !end
                                .constant_difference(&next.1.0)
                                .is_some_and(|distance| distance > 0)
                        {
                            return None;
                        }
                        crate::instrumentation::record_deterministic_work(1);
                        cursor = next.clone();
                        current = values.clone().owned_values();
                    }
                })));
            }
        }
        if index.points_initialized
            && let Some((bound_base, bound_start)) = &self.bound_coordinates
            // Shared literals (especially zero) have unrelated bound neighbors.
            // Constant queries use geometric indexes, never that neighborhood.
            && bound_start.operand_view().word32_constant().is_none()
        {
            // An indexed lower-bound premise names a possible residual start.
            // i < j selects the unique start at i+1; i+1 <= j names it directly.
            // This visits only bounds incident to the query, never resource
            // spellings or a block's holdings. Coverage still checks authority.
            streams.push(Box::new(
                self.assumptions
                    .signed_order_bound_views(bound_start.operand_view())
                    .filter_map(move |(endpoint, lower, strict, forward)| {
                        crate::instrumentation::record_deterministic_work(1);
                        if forward
                            || !graph.are_int32_equal_views(endpoint, bound_start.operand_view())
                        {
                            return None;
                        }
                        let class = graph.indexed_address_class(
                            bound_base,
                            lower,
                            strict,
                            range.element_width(),
                        )?;
                        let bucket = index.points.classes.get(&class)?;
                        let suppliers = if !bucket.owners.is_empty() {
                            &bucket.owners
                        } else if !owned {
                            &bucket.entries
                        } else {
                            return None;
                        };
                        (suppliers.len() == 1)
                            .then(|| *suppliers.iter().next().expect("unique bound supplier"))
                    }),
            ));
        }
        if index.points_initialized {
            let paired = self.index.clone();
            let requested = range.clone();
            let assumptions = self.assumptions.clone();
            // Fragments are chained from the request's start address to its
            // end: in 32-bit element coordinates for an `Int32` range, and at
            // the range's own start and end pointers for a wide one.
            let (mut cursor, target) = match range.int32_bounds() {
                Some((start, end)) => (
                    memory_candidate_coordinate(range, start).map(|(base, start)| {
                        base.offset_by_shared_elements(start, range.element_width())
                    }),
                    memory_candidate_coordinate(range, end).map(|(base, end)| {
                        base.offset_by_shared_elements(end, range.element_width())
                    }),
                ),
                None => (Some(range.start_pointer()), Some(range.end_pointer())),
            };
            let mut visited = BTreeSet::new();
            streams.push(Box::new(std::iter::from_fn(move || {
                let pointer = cursor.take()?;
                if paired.graph.are_equal(&pointer, target.as_ref()?) {
                    return None;
                }
                let class = paired.graph.address_class(&pointer)?;
                let bucket = paired.points.classes.get(&class)?;
                let suppliers = if !bucket.owners.is_empty() {
                    &bucket.owners
                } else if !owned {
                    &bucket.entries
                } else {
                    return None;
                };
                // No choice/search among overlapping symbolic fragment starts.
                if suppliers.len() != 1 {
                    return None;
                }
                let entry = *suppliers.iter().next()?;
                if !visited.insert(entry) {
                    return None;
                }
                let available = paired.resources.facts.get(&entry)?.memory_range()?;
                let mut aligned = available.clone();
                aligned.base = paired
                    .graph
                    .pointer_at_base(available.base(), requested.base())?;
                // Only follow an endpoint after ordinary coverage establishes
                // that this selected fragment belongs to the explicit request.
                // A larger supplier is still delivered for direct entailment,
                // but cannot start a walk outside the requested footprint.
                if super::resource_algebra::memory_range_covers(&requested, &aligned, &assumptions)
                {
                    cursor = if available.wide_bounds().is_some() {
                        Some(aligned.end_pointer())
                    } else if requested.wide_bounds().is_some()
                        && let Some((root, _start, end)) =
                            super::resource_algebra::wide_normalization_form(available)
                    {
                        // A window at a 64-bit index ends where its wide
                        // neighbour starts, spelled as that neighbour is.
                        Some(Pointer {
                            block: root.block,
                            offset: PointerOffsetTerm::add(
                                root.offset,
                                crate::kernel::memory_provenance::rebuild_scaled_pointer_index(
                                    end,
                                    i64::from(available.element_width()),
                                    Some(true),
                                ),
                            ),
                        })
                    } else {
                        memory_candidate_coordinate(available, available.end()).map(
                            |(base, end)| {
                                base.offset_by_shared_elements(end, available.element_width())
                            },
                        )
                    };
                }
                Some(entry)
            })));
        }
        let mut entries = streams.into_iter().flatten().peekable();
        let sole = if entries.peek().is_none() && index.points_initialized {
            ResourceContext::sole_access_supplier(index, &start_pointer, owned)
                .or_else(|| ResourceContext::sole_affine_supplier(index, &start_pointer, owned))
        } else {
            None
        };
        let mut seen = BTreeSet::new();
        Box::new(entries.chain(sole).filter(move |entry| {
            seen.insert(*entry)
                && (!owned
                    || index.resources.facts.get(entry).is_some_and(|fact| {
                        fact.owned_quantity_term().is_some_and(|quantity| {
                            super::resource_algebra::resource_quantity_is_positive(
                                quantity,
                                &self.assumptions,
                            )
                        })
                    }))
        }))
    }
}
impl MemoryFactCandidates {
    /// Restate one selected supplier in the query's checked byte coordinates.
    /// This uses the same query-local graph as requirement alignment; it does
    /// not publish an equality or change object designation/validity metadata.
    pub(super) fn supplier_at_base(
        &self,
        entry: ResourceEntryId,
        base: &Pointer,
    ) -> Option<ResourceFact> {
        let fact = self.index.resources.facts.get(&entry)?;
        let available = fact.memory_range()?;
        let mut range = available.clone();
        range.base = if available.wide_bounds().is_some() {
            self.index
                .graph
                .pointer_at_base_with_wide_index(available.base(), base)?
        } else {
            self.index.graph.pointer_at_base(available.base(), base)?
        };
        Some(match fact {
            ResourceFact::Own(_, quantity) => {
                ResourceFact::Own(Resource::Memory(range), quantity.clone())
            }
            ResourceFact::View(_) => ResourceFact::View(Resource::Memory(range)),
        })
    }

    /// One owned occurrence starting at this exact address class. Ambiguity
    /// declines the binary composition rule; no candidate list is inspected.
    pub(super) fn sole_owned_start(&self, pointer: &Pointer) -> Option<ResourceEntryId> {
        crate::instrumentation::record_deterministic_work(1);
        if !self.index.points_initialized {
            return None;
        }
        let class = self.index.graph.address_class(pointer)?;
        let owners = &self.index.points.classes.get(&class)?.owners;
        (owners.len() == 1).then(|| *owners.iter().next().expect("one owner"))
    }

    pub(super) fn requirement(
        &self,
        entry: ResourceEntryId,
        fact: &ResourceFact,
    ) -> Option<ResourceFact> {
        let range = fact.memory_range()?;
        let available = self.index.resources.facts.get(&entry)?.memory_range()?;
        let base = if available.wide_bounds().is_some() {
            self.index
                .graph
                .pointer_at_base_with_wide_index(range.base(), available.base())?
        } else {
            self.index
                .graph
                .pointer_at_base(range.base(), available.base())?
        };
        let mut range = range.clone();
        range.base = base;
        Some(match fact {
            ResourceFact::Own(_, quantity) => {
                ResourceFact::Own(Resource::Memory(range), quantity.clone())
            }
            ResourceFact::View(_) => ResourceFact::View(Resource::Memory(range)),
        })
    }
}

#[derive(Clone, Copy)]
enum MemoryQuery<'a> {
    Address(&'a Pointer),
    Footprint(&'a MemoryRange),
}
impl MemoryQuery<'_> {
    fn register(self, graph: &EqualityGraph) {
        match self {
            Self::Address(pointer) => {
                let mut pending = vec![pointer.offset.clone()];
                while let Some(offset) = pending.pop() {
                    if let PointerOffsetTerm::Add(left, right) = &offset {
                        pending.push(left.as_ref().clone());
                        pending.push(right.as_ref().clone());
                    }
                    graph.address_class(&Pointer {
                        block: pointer.block.clone(),
                        offset,
                    });
                }
                graph.address_class(&Pointer {
                    block: pointer.block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                });
            }
            Self::Footprint(range) => {
                let start = range.start_pointer();
                let end = range.end_pointer();
                MemoryQuery::Address(range.base()).register(graph);
                MemoryQuery::Address(&start).register(graph);
                MemoryQuery::Address(&end).register(graph);
                graph.footprint_class(range);
            }
        }
    }
}

impl ResourceContext {
    #[cfg(test)]
    pub(in crate::kernel) fn observe_composite_context(&self) {
        projection_tests::record_context(self);
    }

    #[cfg(test)]
    pub(crate) fn memory_write_selection_is_known_for_test(
        &self,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> bool {
        let pointer = range.start_pointer();
        self.write_access(&pointer, range.element_width(), assumptions)
            .is_some()
            && self.memory_write_range(&pointer, range.element_width(), assumptions) == Some(range)
    }

    /// Select a retained call-frame member through already published address
    /// classes. Permission selection supplies candidates and coordinates;
    /// physical framing still checks the complete original byte interval.
    /// Raw inputs have no class payload and must not bootstrap a graph while
    /// an assumption-free memory walk is only trying to name its read.
    pub(in crate::kernel) fn kept_range_via_address_class(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
        include_views: bool,
    ) -> Option<&MemoryRange> {
        // A view-only frame can answer an explicit base or an admitted alias
        // in the caller's structural lookup. Do not resolve an opaque pointer
        // read merely to discover whether its pointee might have a supplier.
        if self.flat_owned_memory_ranges().is_empty()
            && (matches!(&pointer.block, PointerBlock::LoadedPointer(_))
                || matches!(&pointer.block, PointerBlock::Symbolic(variable)
                    if crate::kernel::is_load_variable(variable)))
        {
            return None;
        }
        let published = self
            .memory_equalities
            .lock()
            .expect("memory equality index")
            .published
            .clone()?;
        let select = |entries: SelectedMemoryAccess, needs_current_equality: bool| {
            let entry = entries.entry();
            crate::instrumentation::record_deterministic_work(1);
            let fact = self.storage.facts.get(&entry)?;
            let range = (if include_views {
                fact.memory_range()
            } else {
                fact.memory_own_range()
            })?;
            if fact.owned_quantity_term().is_some_and(|quantity| {
                !super::resource_algebra::resource_quantity_is_positive(quantity, assumptions)
            }) {
                return None;
            }
            let address = entries.address()?;
            if needs_current_equality && !assumptions.pointers_known_equal(pointer, &address) {
                return None;
            }
            if assumptions.kept_range_holds_access(range, &address, bytes) {
                return Some(range);
            }
            None
        };
        // Content-addressed call states retain their first frame. Rechecking
        // a proof gives that frame another input lineage, whose class IDs cannot
        // be paired with the retained payload. Its prepared index can still
        // select a spelling; the current graph must establish that equality.
        // Try this bounded selection before pairing another input, so recheck
        // does not rebuild an index over the frame or ambient equality history.
        if published.graph.input_key().root() != assumptions.equality_graph.input_key().root()
            && let Some(entries) =
                Self::indexed_access_entries(&published, pointer, bytes, !include_views)
                    .or_else(|| {
                        Self::partial_start_entries(&published, pointer, bytes, !include_views)
                    })
                    .or_else(|| {
                        Self::relative_access_entries(&published, pointer, bytes, !include_views)
                    })
            && let Some(selected) = (MemoryAccessCandidates {
                entries,
                query: pointer.clone(),
                index: published,
                preferred_owner: None,
            })
            .select()
            && let Some(range) = select(selected, true)
        {
            return Some(range);
        }
        let candidates = if include_views {
            self.read_access(pointer, bytes, assumptions)
        } else {
            self.write_access(pointer, bytes, assumptions)
        }?;
        select(candidates, false)
    }

    /// Pair at proof boundaries, then apply only resource and class deltas.
    /// Forks share the registered input and apply only their admitted delta.
    /// Independent lineages start from raw roots; no sibling premise leaks.
    pub(crate) fn synchronize_memory_equalities(&self, assumptions: &PureFactContext) {
        self.pair_memory_equalities(assumptions, true, None);
    }

    /// A provisional clause prefix captures its checked graph before any
    /// memory supplier is admitted. Nonempty retained inputs keep their
    /// existing publication; this boundary never republishes an ambient frame.
    pub(in crate::kernel) fn capture_empty_memory_input(&self, assumptions: &PureFactContext) {
        if shape_points::payload_is_empty(&self.storage) {
            let caller = self.pair_memory_equalities(assumptions, true, None);
            self.memory_equalities
                .lock()
                .expect("memory equality index")
                .empty_caller = Some(caller);
        }
    }

    /// Maintain the two published checkpoints at the resource mutation that
    /// produces the delta. Other cached forks remain persistent lazy views.
    /// This never initializes a cold input or enumerates cached branches.
    pub(super) fn advance_published_resource_entries(&self) {
        let checkpoints = {
            let cache = self
                .memory_equalities
                .lock()
                .expect("memory equality index");
            cache.published.as_ref().and_then(|published| {
                // Keep a single first memory delta on the empty checkpoint.
                // Its next attachment can adopt that branch's closed graph
                // without traversing unrelated admitted inputs. A second
                // mutation flushes both deltas, so work cannot accumulate.
                if shape_points::payload_is_empty(&published.resources)
                    && !shape_points::payload_is_empty(&self.storage)
                    && Self::history_tail_is(
                        self.storage
                            .history
                            .as_ref()
                            .and_then(|change| change.parent.as_ref()),
                        published.resources.history.as_ref(),
                    )
                {
                    return None;
                }
                let key = published.graph.input_key();
                let root = cache
                    .by_inputs
                    .get(&key.root())
                    .expect("published input root");
                Some((root.graph.clone(), published.graph.clone()))
            })
        };
        let Some((root, published)) = checkpoints else {
            return;
        };
        let same = root.input_key() == published.input_key();
        self.pair_memory_equalities_in_graph(root, true, None);
        if !same {
            self.pair_memory_equalities_in_graph(published, true, None);
        }
    }

    /// Delta-only composition must not attach an unrelated ambient input.
    /// Advance a prepared lineage; first attachment belongs to fresh construction
    /// or an explicit whole-input validation/publication boundary.
    pub(super) fn advance_prepared_memory_equalities(&self, assumptions: &PureFactContext) {
        let root = assumptions.equality_graph.input_key().root();
        let prepared = self
            .memory_equalities
            .lock()
            .expect("memory equality index")
            .by_inputs
            .get(&root)
            .is_some_and(|index| index.points_initialized);
        if prepared {
            self.synchronize_memory_equalities(assumptions);
        }
    }

    // Pair against admitted inputs, not a foreign graph's query registrations.
    // The index owns its graph checkpoint and term IDs. Advancing a fork applies
    // only its explicit equality delta into that checkpoint, preserving payloads.
    // Complete resource registration remains a proof-boundary operation.
    fn pair_memory_equalities(
        &self,
        assumptions: &PureFactContext,
        register_input: bool,
        query: Option<&Pointer>,
    ) -> std::sync::Arc<PairedMemoryIndex> {
        self.pair_memory_equalities_in_graph(
            query
                .map(|pointer| graph_for_memory_query(assumptions, pointer))
                .unwrap_or_else(|| assumptions.equality_graph.clone()),
            register_input,
            query.map(MemoryQuery::Address),
        )
    }

    fn pair_memory_equalities_in_graph(
        &self,
        source: EqualityGraph,
        register_input: bool,
        query: Option<MemoryQuery<'_>>,
    ) -> std::sync::Arc<PairedMemoryIndex> {
        let key = source.input_key();
        let mut cache = self
            .memory_equalities
            .lock()
            .expect("memory equality index");
        if shape_points::payload_is_empty(&self.storage) {
            // No address-keyed resource occurrences means no IDs to rebase.
            // Capture the already closed source in constant work. Retain only
            // the producer-selected caller boundary alongside the current one;
            // a temporary opening context must not discard their common prefix.
            // Refresh its empty resource payload, so old resource history does
            // not accumulate behind a checkpoint with no memory occurrences.
            let caller = cache
                .empty_caller
                .as_ref()
                .filter(|caller| caller.graph.input_key().root() == key.root())
                .map(|caller| self.empty_memory_index(caller.graph.clone()));
            let mut inputs = PersistentMap::default();
            if let Some(caller) = &caller {
                inputs = inputs.with_inserted(caller.graph.input_key(), caller.clone());
            }
            cache.empty_caller = caller;
            let root = self.empty_memory_index(source.input_root());
            let paired = self.empty_memory_index(source);
            cache.by_inputs = inputs
                .with_inserted(key.root(), root)
                .with_inserted(key, paired.clone());
            // Empty memory input is trivially complete, even on a cold query.
            cache.published = Some(paired.clone());
            return paired;
        }
        // A cold view made before publication cannot shadow the completed
        // registered root. Prefer complete ancestors once this lineage has one.
        let require_complete = register_input
            || cache
                .by_inputs
                .get(&key.root())
                .is_some_and(|index| index.points_initialized);
        let ancestor = cache
            .by_inputs
            .get(&key)
            .filter(|index| !require_complete || index.points_initialized)
            .cloned()
            .or_else(|| {
                cache
                    .by_inputs
                    .get(&key.root())
                    .filter(|index| {
                        index.points_initialized && shape_points::payload_is_empty(&index.resources)
                    })
                    .cloned()
            })
            .or_else(|| {
                if cache.by_inputs.is_empty()
                    || (require_complete
                        && !cache
                            .by_inputs
                            .get(&key.root())
                            .is_some_and(|index| index.points_initialized))
                {
                    return None;
                }
                source.input_checkpoints().find_map(|key| {
                    cache
                        .by_inputs
                        .get(&key)
                        .filter(|index| !require_complete || index.points_initialized)
                        .cloned()
                })
            });
        let incompatible_checkpoint = ancestor.is_some();
        if let Some(mut paired) = ancestor
            && std::sync::Arc::ptr_eq(&self.storage.origin, &paired.resources.origin)
        {
            let expected = paired.resources.history.as_ref();
            let mut cursor = self.storage.history.as_ref();
            let mut changed = Vec::new();
            let mut descendant = true;
            while !Self::history_tail_is(cursor, expected) {
                let Some(change) = cursor else {
                    descendant = false;
                    break;
                };
                crate::instrumentation::record_deterministic_work(1);
                if let Some((entry, insert)) = change.entry_delta {
                    changed.push((entry, insert, change.fact.clone()));
                }
                cursor = change.parent.as_ref();
            }
            if descendant {
                let index = std::sync::Arc::make_mut(&mut paired);
                // An empty payload has no namespace coupling. Adopt the
                // source's closed state, including on a preexisting sibling,
                // instead of walking or reapplying unrelated input history.
                let adopt_source = shape_points::payload_is_empty(&index.resources);
                let mut graph = if adopt_source {
                    source.clone()
                } else {
                    index.graph.clone()
                };
                if !adopt_source {
                    assert!(graph.append_inputs_from(&source), "input checkpoint prefix");
                }
                if let Some(query) = query {
                    query.register(&graph);
                }
                // Removed suppliers may have acquired read definitions since
                // insertion too. Finish registering the entire selected delta
                // before moving payloads into their new classes.
                for (_, _, fact) in changed.iter().rev() {
                    if index.points_initialized {
                        shape_points::ShapePoints::register(fact, &graph);
                    }
                    if index.points_initialized
                        && let Some(range) = fact.memory_range()
                    {
                        index.symbolic.register_object(range, &graph);
                        symbolic::RangeSupports::register(range, &graph);
                    }
                }
                let merges = if adopt_source {
                    Vec::new()
                } else {
                    for merge in graph
                        .address_merges_since(&index.indexed_graph)
                        .expect("address prefix")
                    {
                        index.points.merge(merge.moved, merge.kept);
                        index.shapes.merge(merge.moved, merge.kept);
                        index.symbolic.merge(merge.moved, merge.kept);
                    }
                    graph
                        .pointer_merges_since(&index.indexed_graph)
                        .expect("pointer prefix")
                };
                for (entry, insert, fact) in changed.into_iter().rev() {
                    if index.points_initialized {
                        index.points.update(entry, insert, &fact, &graph);
                        index.shapes.update(entry, insert, &fact, &graph);
                        index.symbolic.update(entry, insert, &fact, &graph);
                    }
                    let Some(range) = fact.memory_range() else {
                        continue;
                    };
                    index.addresses.update_in_graph(
                        range,
                        fact.is_own(),
                        entry,
                        insert,
                        if adopt_source {
                            &graph
                        } else {
                            &index.indexed_graph
                        },
                        &fact,
                    );
                }
                for merge in merges {
                    index.addresses.merge(merge);
                }
                index.resources = self.storage.clone();
                index.indexed_graph = graph.clone();
                index.graph = graph;
                cache.by_inputs = cache.by_inputs.with_inserted(key, paired.clone());
                if register_input {
                    cache.published = Some(paired.clone());
                }
                return paired;
            }
        }
        if incompatible_checkpoint {
            // A cached view of another resource lineage or a non-ancestor
            // frame cannot be reused. Drop this memo; never register the input
            // on a read-only lookup or carry obsolete occurrence IDs forward.
            cache.by_inputs = PersistentMap::default();
            cache.published = None;
            cache.empty_caller = None;
        }
        if register_input {
            // Register both input boundaries directly. The current view shares
            // the source's already closed graph; initial publication must not
            // walk unrelated admitted inputs to reconstruct that state.
            let root = self.registered_memory_index(source.input_root());
            let paired = if root.graph.input_key() == key {
                root.clone()
            } else {
                self.registered_memory_index(source)
            };
            cache.by_inputs = cache
                .by_inputs
                .with_inserted(key.root(), root)
                .with_inserted(key, paired.clone());
            cache.published = Some(paired.clone());
            return paired;
        }
        let graph = source;
        if let Some(query) = query {
            query.register(&graph);
        }
        let mut complete_addresses = true;
        let addresses = if self.storage.facts.len() < graph.pointer_merge_count() {
            // A small, cold contract beside a large caller equality history:
            // index its actual occurrences in the already closed namespace.
            // Keep this a raw index; it publishes no read or storage authority.
            let mut addresses = MemoryAddresses::default();
            for (entry, fact) in self.storage.facts.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(range) = fact.memory_range() {
                    addresses.update_in_graph(range, fact.is_own(), *entry, true, &graph, fact);
                }
            }
            addresses
        } else {
            let mut addresses = self.storage.index.memory_addresses.clone();
            let merges = match query {
                Some(MemoryQuery::Address(pointer)) => {
                    complete_addresses = false;
                    graph.pointer_merges_for_block(&pointer.block)
                }
                Some(MemoryQuery::Footprint(range)) => {
                    complete_addresses = false;
                    graph.pointer_merges_for_block(&range.base().block)
                }
                None => graph.pointer_merges(),
            };
            for merge in merges {
                addresses.merge(merge);
            }
            addresses
        };
        let paired = std::sync::Arc::new(PairedMemoryIndex {
            resources: self.storage.clone(),
            indexed_graph: graph.clone(),
            graph,
            addresses,
            points: AddressPoints::default(),
            shapes: shape_points::ShapePoints::default(),
            symbolic: symbolic::RangeSupports::default(),
            points_initialized: false,
        });
        // A selected-class view is valid for this query only. Caching it by
        // the whole graph key would make a later unrelated query miss aliases.
        if complete_addresses {
            cache.by_inputs = cache.by_inputs.with_inserted(key, paired.clone());
        }
        paired
    }

    fn empty_memory_index(&self, graph: EqualityGraph) -> std::sync::Arc<PairedMemoryIndex> {
        std::sync::Arc::new(PairedMemoryIndex {
            resources: self.storage.clone(),
            indexed_graph: graph.clone(),
            graph,
            addresses: MemoryAddresses::default(),
            points: AddressPoints::default(),
            shapes: shape_points::ShapePoints::default(),
            symbolic: symbolic::RangeSupports::default(),
            points_initialized: true,
        })
    }

    /// Full input registration belongs to publication or normalization, never
    /// a simple lookup. Finish registration before assigning class payloads.
    fn registered_memory_index(&self, graph: EqualityGraph) -> std::sync::Arc<PairedMemoryIndex> {
        let mut symbolic = symbolic::RangeSupports::default();
        for (_, fact) in self.storage.facts.iter() {
            shape_points::ShapePoints::register(fact, &graph);
            if let Some(range) = fact.memory_range() {
                symbolic.register_object(range, &graph);
                symbolic::RangeSupports::register(range, &graph);
            }
        }
        let mut points = AddressPoints::default();
        let mut shapes = shape_points::ShapePoints::default();
        let mut addresses = MemoryAddresses::default();
        for (entry, fact) in self.storage.facts.iter() {
            points.update(*entry, true, fact, &graph);
            shapes.update(*entry, true, fact, &graph);
            symbolic.update(*entry, true, fact, &graph);
            if let Some(range) = fact.memory_range() {
                addresses.update_in_graph(range, fact.is_own(), *entry, true, &graph, fact);
            }
        }
        std::sync::Arc::new(PairedMemoryIndex {
            resources: self.storage.clone(),
            indexed_graph: graph.clone(),
            graph,
            addresses,
            points,
            shapes,
            symbolic,
            points_initialized: true,
        })
    }

    /// Normalization already visits its full resource input. Refresh the
    /// registered root and the published view here, using their existing graph
    /// states. Do not rescan equality history or defer registration to a query.
    pub(super) fn rebuild_paired_memory_entries(&self) {
        let mut cache = self
            .memory_equalities
            .lock()
            .expect("memory equality index");
        let Some(published) = cache.published.clone() else {
            // Even raw interval views can contain IDs renumbered by this
            // replacement. A future cold lookup starts from the new raw index.
            cache.by_inputs = PersistentMap::default();
            return;
        };
        let key = published.graph.input_key();
        let root = cache
            .by_inputs
            .get(&key.root())
            .cloned()
            .expect("published input root");
        // Other views carry obsolete occurrence IDs. Refresh at most these two
        // graph states, rather than every cached branch times the whole input.
        let root = self.registered_memory_index(root.graph.clone());
        let published = if key == key.root() {
            root.clone()
        } else {
            self.registered_memory_index(published.graph.clone())
        };
        cache.by_inputs = PersistentMap::default()
            .with_inserted(key.root(), root)
            .with_inserted(key, published.clone());
        cache.published = Some(published);
    }

    /// Concrete interval coverage supports decisive hits and misses. Exact
    /// whole-cell payloads supply eligible known-equal occurrences; a missing
    /// footprint is unknown when containment, arithmetic or state reasoning
    /// could apply.
    /// Tests of the concrete fragment keep unknown distinct from a miss.
    #[cfg(test)]
    pub(super) fn concrete_read_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<MemoryAccessCandidates> {
        self.concrete_access_entries(pointer, bytes, assumptions, false)
    }

    fn partial_start_entries(
        index: &PairedMemoryIndex,
        pointer: &Pointer,
        bytes: u32,
        owned: bool,
    ) -> Option<MemoryAccessEntries> {
        let graph = &index.graph;
        let class = graph.address_class(pointer)?;
        if index.points_initialized {
            let class = graph.address_class_root(class);
            if let Some(bucket) = index.points.classes.get(&class) {
                let capacities = if owned {
                    &bucket.write_capacities
                } else {
                    &bucket.read_capacities
                };
                let bytes = u64::from(crate::kernel::assumptions::read_candidate_byte_width(bytes));
                if let Some(entries) = capacities.get(&bytes).or_else(|| {
                    capacities
                        .get_greater_than(&bytes)
                        .map(|(_, entries)| entries)
                }) {
                    return Some(MemoryAccessEntries::Exact(entries.clone().owned_values()));
                }
            }
        }
        None
    }

    fn sole_access_supplier(
        index: &PairedMemoryIndex,
        pointer: &Pointer,
        owned: bool,
    ) -> Option<ResourceEntryId> {
        let class = index.graph.address_class(pointer)?;
        if let Some(entry) = index.symbolic.sole_base(class, owned) {
            return Some(entry);
        }
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            for part in [left, right] {
                let part = Pointer {
                    block: pointer.block.clone(),
                    offset: part.as_ref().clone(),
                };
                if let Some(entry) = Self::sole_access_supplier(index, &part, owned) {
                    return Some(entry);
                }
            }
        }
        let root = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let class = index.graph.address_class(&root)?;
        index.symbolic.sole_base(class, owned)
    }

    /// Select a unique supplier in the query's trusted affine block class.
    /// Cardinality is indexed; the caller must still check exact byte coverage.
    fn sole_affine_supplier(
        index: &PairedMemoryIndex,
        pointer: &Pointer,
        owned: bool,
    ) -> Option<ResourceEntryId> {
        let point = index.graph.canonical_pointer(pointer)?;
        let bucket = index.addresses.classes.get(&point.representative)?;
        let suppliers = if owned || bucket.owners.len() == 1 {
            &bucket.owners
        } else {
            &bucket.suppliers
        };
        if suppliers.len() != 1 {
            return None;
        }
        let entry = *suppliers.iter().next().expect("sole supplier");
        index.resources.facts.get(&entry)?.memory_range()?;
        Some(entry)
    }

    /// One indexed read supplier, or a sole retained supplier in the selected
    /// affine class. Unsupported or ambiguous inputs fail closed; queries never
    /// publish input, retry address spellings, or search a resource frame.
    pub(super) fn read_access(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<SelectedMemoryAccess> {
        self.access_entries(pointer, bytes, assumptions, false)?
            .select()
    }

    // Follow only the query's explicit additive prefixes. The relative
    // interval lookup is indexed by each complete base's checked class.
    fn relative_access_entries(
        index: &PairedMemoryIndex,
        pointer: &Pointer,
        bytes: u32,
        owned: bool,
    ) -> Option<MemoryAccessEntries> {
        if !index.points_initialized {
            return None;
        }
        let mut base = pointer.clone();
        let mut displacement = 0_i128;
        let bytes = i128::from(crate::kernel::assumptions::read_candidate_byte_width(bytes));
        loop {
            if let Some(entries) = index.symbolic.relative_byte_entries(
                &base,
                AddressCoordinate(AffineOffset::constant(displacement)),
                AddressCoordinate(AffineOffset::constant(displacement.checked_add(bytes)?)),
                owned,
                &index.graph,
            ) {
                let mut entries = entries.peekable();
                if entries.peek().is_some() {
                    return Some(MemoryAccessEntries::Relative(Box::new(entries)));
                }
            }
            let (prefix, bytes) = match &base.offset {
                PointerOffsetTerm::Add(left, right) => {
                    if let Some(bytes) = right.as_const() {
                        (left.as_ref().clone(), bytes)
                    } else {
                        let bytes = left.as_const()?;
                        (right.as_ref().clone(), bytes)
                    }
                }
                PointerOffsetTerm::Constant(bytes) if *bytes != 0 => {
                    (PointerOffsetTerm::Constant(0), *bytes)
                }
                _ => return None,
            };
            base.offset = prefix;
            displacement = displacement.checked_add(i128::from(bytes))?;
        }
    }

    fn access_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
        owned: bool,
    ) -> Option<MemoryAccessCandidates> {
        // An admitted footprint at this address already supplies coordinates.
        // Resolve a pointer's recorded read only when the ordinary index has
        // no supplier; otherwise its defining history is unrelated to selection.
        let direct = self.pair_memory_equalities_in_graph(
            assumptions.equality_graph.clone(),
            false,
            Some(MemoryQuery::Address(pointer)),
        );
        let direct_entries =
            Self::indexed_access_entries(&direct, pointer, bytes, owned).and_then(|entries| {
                match entries {
                    MemoryAccessEntries::Intervals(mut entries) => entries
                        .next()
                        .map(|first| MemoryAccessEntries::Prefixed(Some(first), entries)),
                    entries => Some(entries),
                }
            });
        if let Some(entries) = direct_entries {
            return Some(
                MemoryAccessCandidates {
                    entries,
                    query: pointer.clone(),
                    index: direct,
                    preferred_owner: None,
                }
                .prefer_owned_supplier(!owned, bytes),
            );
        }
        let index = self.pair_memory_equalities(assumptions, false, Some(pointer));
        // A reference result may capture an interior address without an
        // additive syntax tree. Its checked class retains a producer spelling
        // with that base; use it for indexed supplier selection only.
        let spelling = (!matches!(pointer.offset, PointerOffsetTerm::Add(_, _)))
            .then(|| index.graph.additive_address(pointer))
            .flatten();
        let selected_pointer = spelling.as_ref().unwrap_or(pointer);
        let entries = if let Some(entries) =
            Self::indexed_access_entries(&index, pointer, bytes, owned)
                .or_else(|| Self::partial_start_entries(&index, pointer, bytes, owned))
                .or_else(|| Self::relative_access_entries(&index, selected_pointer, bytes, owned))
        {
            entries
        } else {
            if !index.points_initialized {
                return None;
            }
            // A split suffix may be the unique owner beginning at the exact
            // query even when several pieces share its base. Do not use this
            // lookup for additive prefixes: they need not select that suffix.
            let starting_owner = owned
                .then(|| index.graph.address_class(selected_pointer))
                .flatten()
                .and_then(|class| index.symbolic.sole_owned_start(class));
            let entry = starting_owner
                .or_else(|| Self::sole_access_supplier(&index, selected_pointer, owned))
                .or_else(|| {
                    (!owned)
                        .then(|| Self::sole_access_supplier(&index, selected_pointer, true))
                        .flatten()
                })
                .or_else(|| Self::sole_affine_supplier(&index, selected_pointer, owned))?;
            MemoryAccessEntries::SingleSupplier(Some(entry))
        };
        Some(
            MemoryAccessCandidates {
                entries,
                query: pointer.clone(),
                index,
                preferred_owner: None,
            }
            .prefer_owned_supplier(!owned, bytes),
        )
    }

    /// Owned whole-cell matches or complete affine interval candidates for
    /// writes. Read payloads are unsuitable: a matching view could hide an owner.
    /// Unknown support is refused before testing any candidate.
    #[cfg(test)]
    pub(super) fn concrete_write_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<MemoryAccessCandidates> {
        self.concrete_access_entries(pointer, bytes, assumptions, true)
    }

    /// Whole-scalar consumption requires an unambiguous supplier. Inspecting
    /// the first two indexed entries establishes uniqueness without a bucket scan.
    pub(super) fn unique_write_access(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<SelectedMemoryAccess> {
        let mut candidates = self.access_entries(pointer, bytes, assumptions, true)?;
        let entry = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        Some(SelectedMemoryAccess {
            source: candidates,
            entry,
        })
    }

    /// One write supplier from the shared trusted graph/index checkpoint.
    /// Beside views, a prepared, complete affine block with one memory owner
    /// needs no supplier search even when its bounds or access are symbolic.
    /// Ambiguity or unsupported equality reports unknown before checking; a
    /// selected owner's failed quantity or coverage check is final.
    pub(super) fn write_access(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<SelectedMemoryAccess> {
        self.access_entries(pointer, bytes, assumptions, true)?
            .select()
    }

    #[cfg(test)]
    fn concrete_access_entries(
        &self,
        pointer: &Pointer,
        bytes: u32,
        assumptions: &PureFactContext,
        owned: bool,
    ) -> Option<MemoryAccessCandidates> {
        let index = self.pair_memory_equalities(assumptions, false, Some(pointer));
        let entries = Self::indexed_access_entries(&index, pointer, bytes, owned)?;
        Some(MemoryAccessCandidates {
            entries,
            query: pointer.clone(),
            index,
            preferred_owner: None,
        })
    }

    fn indexed_access_entries(
        index: &PairedMemoryIndex,
        pointer: &Pointer,
        bytes: u32,
        owned: bool,
    ) -> Option<MemoryAccessEntries> {
        let graph = &index.graph;
        let class = graph.address_class(pointer)?;
        if index.points_initialized {
            let class = graph.address_class_root(class);
            let entries = index
                .points
                .classes
                .get(&class)
                .and_then(|bucket| if owned { &bucket.writes } else { &bucket.reads }.get(&bytes))
                .cloned()
                .unwrap_or_default();
            // A graph answer is equality or unknown, not disequality. Scalar
            // arithmetic and state transport can justify an access outside
            // this address closure, so an unbound class is unknown within
            // this fragment. A bound whole-cell class
            // supplies checked address evidence and needs no spelling search.
            // Writes select only positive concrete owners under the same
            // footprint/width eligibility rule; views never enter that payload.
            if !entries.is_empty() {
                return Some(MemoryAccessEntries::Exact(entries.owned_values()));
            }
        }
        // A raw structural root has not registered every occurrence's load
        // origin. Closing just the queried load cannot establish complete
        // supplier coverage, so a load query on it takes positive interval
        // hits only and never a decisive miss. Publication makes this
        // fragment complete; a simple lookup must never register the entire
        // input itself.
        let load_block = match &pointer.block {
            PointerBlock::LoadedPointer(_) => true,
            PointerBlock::Symbolic(variable) => crate::kernel::is_load_variable(variable),
            _ => false,
        };
        let point = graph.canonical_pointer(pointer)?;
        let bucket = index.addresses.classes.get(&point.representative)?;
        let complete = !(load_block && !index.points_initialized)
            && graph.affine_addresses_complete(&point.representative)
            && bucket.read_intervals.len() == bucket.memory_count;
        let start = point.offset.checked_add(&bucket.origin)?;
        let candidate_bytes = crate::kernel::assumptions::read_candidate_byte_width(bytes);
        let end = start.checked_add(&AffineOffset::constant(i128::from(candidate_bytes)))?;
        let intervals = if owned {
            &bucket.write_intervals
        } else {
            &bucket.read_intervals
        };
        let mut entries = intervals.covering(&AddressCoordinate(start), &AddressCoordinate(end));
        if !complete || !point.offset.is_constant() || !bucket.origin.is_constant() {
            // Retained interval hits are positive supplier evidence even if
            // this fragment is incomplete. Only a complete concrete interval
            // index can make an empty lexical result a decisive miss.
            point.offset.to_offset_term()?;
            bucket.origin.to_offset_term()?;
            let first = entries.next()?;
            return Some(MemoryAccessEntries::Prefixed(Some(first), entries));
        }
        Some(MemoryAccessEntries::Intervals(entries))
    }

    /// Retained footprint witnessing one C object. Object identity has its
    /// own typed key: raw address equality between adjacent objects is not
    /// provenance. Lookup never visits other members of an address/block class.
    pub(in crate::kernel) fn memory_object_evidence(
        &self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> Option<&ResourceFact> {
        let object = pointer.object_identity();
        if let Some(entry) = self.storage.index.memory_objects.supplier(&object) {
            crate::instrumentation::record_deterministic_work(1);
            return self.storage.facts.get(&entry);
        }
        // Exact structural evidence is available on raw explicit inputs. A
        // cold miss cannot have graph payloads and must not walk equality
        // history to discover that; publication belongs to its producer.
        self.memory_equalities
            .lock()
            .expect("memory equality index")
            .published
            .as_ref()?;
        let index = self.pair_memory_equalities(assumptions, false, Some(&object));
        let class = index.graph.address_class(&object)?;
        let entry = index.symbolic.object_supplier(class)?;
        crate::instrumentation::record_deterministic_work(1);
        self.storage.facts.get(&entry)
    }

    /// Select only suppliers at the explicit footprint, covering its start,
    /// or starting inside its concrete byte span. Symbolic ambiguity refuses;
    /// no base bucket, spelling enumeration, or ambient normalization is used.
    pub(super) fn memory_fact_candidates(
        &self,
        range: &MemoryRange,
        owned: bool,
        assumptions: &PureFactContext,
    ) -> MemoryFactCandidates {
        // The derived numeric union is confined to this selected query.
        // Coverage and ownership still check the live supplier before use.
        let graph = assumptions.equality_graph.clone();
        if let Some(endpoint) = crate::kernel::memory_provenance::checked_pointer_read_endpoint(
            range.base(),
            assumptions,
        ) {
            graph.add_checked_read_equality(range.base(), &endpoint);
        }
        let index =
            self.pair_memory_equalities_in_graph(graph, false, Some(MemoryQuery::Footprint(range)));
        // A wide range is found by its footprint and addresses; it has no
        // 32-bit element coordinate.
        let bound_coordinates = range
            .int32_bounds()
            .and_then(|(start, _)| memory_candidate_coordinate(range, start));
        MemoryFactCandidates {
            entries: MemoryFactEntries {
                index: index.clone(),
                range: range.clone(),
                owned,
                assumptions: assumptions.clone(),
                bound_coordinates,
            },
            index,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_order_bounds_select_native_memory_suppliers_without_export() {
        use crate::kernel::{
            IntegerTerm, KernelTermExport, KernelTermImport, MachineIntegerType,
            SharedMachineIntegerTerm,
        };
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let lower = MachineTerm::add(
            MachineTerm::Variable(Variable(991421)),
            MachineTerm::Variable(Variable(991422)),
        );
        let cursor = MachineTerm::Variable(Variable(991423));
        let end = MachineTerm::Variable(Variable(991424));
        let observe = |value: &MachineTerm| {
            IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(
                    ty,
                    KernelTermImport::default()
                        .machine_arithmetic(ty, value)
                        .unwrap(),
                )
                .unwrap(),
            )
        };
        for strict in [false, true] {
            let condition = if strict {
                ConditionTerm::integer_less_than(observe(&lower), observe(&cursor))
            } else {
                ConditionTerm::integer_less_equal(observe(&lower), observe(&cursor))
            };
            let facts = PureFactContext::new().assume_condition(condition, true);
            let base = Pointer::symbolic(Variable(991425));
            let start = if strict {
                MachineTerm::add(lower.clone(), 1u32.into())
            } else {
                lower.clone()
            };
            let owned = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                base.clone(),
                start,
                end.clone(),
                4,
            ));
            let resources =
                ResourceContext::new_with_equalities(&facts).unchecked_with_fact(owned.clone());
            resources.synchronize_memory_equalities(&facts);
            let query = MemoryRange::new_with_element_width(
                base,
                cursor.clone(),
                MachineTerm::add(cursor.clone(), 1u32.into()),
                4,
            );
            let exports = KernelTermExport::machine_export_count();
            let without_bound =
                resources.memory_fact_candidates(&query, true, &PureFactContext::new());
            assert!(
                !without_bound.entries.iter().any(|entry| without_bound
                    .index
                    .resources
                    .facts
                    .get(&entry)
                    == Some(&owned))
            );
            let candidates = resources.memory_fact_candidates(&query, true, &facts);
            assert!(
                candidates
                    .entries
                    .iter()
                    .any(|entry| candidates.index.resources.facts.get(&entry) == Some(&owned))
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn kept_field_uses_checked_constant_coordinates_and_full_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(989_810));
        let query = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::add(
                PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(989_811)), 4),
                PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(989_812)), 4),
            ),
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(query.clone(), owner.offset_by_bytes(24)),
            true,
        );
        let assumptions = PureFactContext::new().assume_proposition(equality);
        let range = MemoryRange::new_with_element_width(owner, 0u32.into(), 8u32.into(), 4);
        let resources = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_fact(ResourceFact::own_memory(range));
        let kept = crate::kernel::primitives::CallKeptRanges::new(resources, vec![], None);
        assert!(kept.holds_access(&query, 8, &assumptions));
        assert!(!kept.holds_access(&query, 12, &assumptions));
        assert!(!kept.holds_access(&query, 8, &PureFactContext::new()));
    }

    #[test]
    fn wide_read_aligns_external_buffer_from_symbolic_cursor() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(989_100)), 1),
        };
        let narrow = base.offset_by_elements(MachineTerm::Variable(Variable(989_101)), 1);
        let index = MachineTerm::Variable(Variable(989_102));
        let wide = base.offset_by_typed_elements(index.clone(), 1, true, true);
        let query = Pointer::symbolic(Variable(989_103));
        let aliases = PureFactContext::new()
            .assume_condition(
                ConditionTerm::pointer_equal(query.clone(), narrow.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(narrow, wide.clone()), true);
        let facts = aliases.clone().assume_condition(
            ConditionTerm::uint64_less_than(index.clone(), MachineTerm::uint64_constant(5552)),
            true,
        );
        let facts = facts.assume_condition(
            ConditionTerm::uint64_less_than(
                MachineTerm::uint64_add(index.clone(), MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_constant(5552),
            ),
            true,
        );
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::new_wide(
                base.clone(),
                MachineTerm::uint64_constant(0),
                MachineTerm::uint64_constant(5552),
                1,
            ),
        ));
        resources.synchronize_memory_equalities(&facts);
        let candidates = resources
            .read_access(&query, 1, &facts)
            .expect("buffer supplier remains indexed");
        assert!(
            candidates.source.index.graph.are_equal(&query, &wide),
            "cursor equality remains checked"
        );
        assert_eq!(
            candidates
                .source
                .index
                .graph
                .pointer_at_base_with_wide_index(&query, &base),
            Some(wide),
            "alignment keeps native index"
        );
        assert!(candidates.address().is_some(), "candidate address");
        assert!(resources.permits_memory_read(&query, 1, &facts));
        assert!(resources.permits_memory_read(&query.offset_by_bytes(1), 1, &facts));
        assert!(!resources.permits_memory_read(&query, 2, &facts));
        assert!(!ResourceContext::new().permits_memory_read(&query, 1, &facts));
        let boundary = aliases.assume_condition(
            ConditionTerm::uint64_equal(index, MachineTerm::uint64_constant(5552)),
            true,
        );
        assert!(!resources.permits_memory_read(&query, 1, &boundary));
        assert!(!resources.permits_memory_read(&query.offset_by_bytes(1), 1, &boundary));
    }

    #[test]
    fn native_suffix_view_authorizes_its_first_byte() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        }
        .offset_by_elements(MachineTerm::Variable(Variable(983_710)), 1);
        let whole = MachineTerm::Variable(Variable(983_711));
        let remaining = MachineTerm::Variable(Variable(983_712));
        let available = MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(0),
            whole.clone(),
            1,
        );
        let selected = base.offset_by_typed_elements(
            MachineTerm::uint64_subtract(whole.clone(), remaining.clone()),
            1,
            true,
            true,
        );
        let temporary = Pointer::symbolic(Variable(983_713));
        let required = ResourceFact::view_memory(MemoryRange::new_with_element_width(
            temporary.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
            1,
        ));
        let bounded = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(temporary, selected), true)
            .assume_condition(
                ConditionTerm::uint64_less_equal(whole.clone(), MachineTerm::uint64_constant(5551)),
                true,
            );
        let suffix = bounded.clone().assume_condition(
            ConditionTerm::uint64_less_equal(remaining.clone(), whole.clone()),
            true,
        );
        let facts = suffix.clone().assume_condition(
            ConditionTerm::uint64_less_equal(MachineTerm::uint64_constant(1), remaining.clone()),
            true,
        );
        let held = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(available));
        held.synchronize_memory_equalities(&facts);
        assert!(
            held.satisfies_fact(&required, &facts),
            "a nonempty held suffix authorizes one byte"
        );
        assert!(held.permits_memory_read(required.memory_range().unwrap().base(), 1, &facts));
        assert!(
            !held.satisfies_fact(&required, &suffix),
            "an empty suffix must not authorize a read"
        );
        let low_word = bounded
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    MachineTerm::uint32_from_64(remaining.clone()),
                    MachineTerm::uint32_from_64(whole.clone()),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(MachineTerm::uint64_constant(1), remaining),
                true,
            );
        assert!(
            !held.satisfies_fact(&required, &low_word),
            "truncated bounds are not native coverage"
        );
        let only_viewable = facts.assume_proposition(Proposition::MemoryLoadable {
            memory: Memory::new(),
            base,
            bytes: whole,
            wide: true,
        });
        assert!(
            !ResourceContext::new().satisfies_fact(&required, &only_viewable),
            "range arithmetic cannot mint a view"
        );
    }

    // A partial resource frame leaves a constant-base range covering two
    // fields. A modeled pointer alias must still select an interior field.
    #[test]
    fn modeled_pointer_alias_selects_interior_of_constant_base_owner() {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = Pointer::symbolic(Variable(4000000));
        let model = Pointer::symbolic(Variable(4065536));
        let old_read = Pointer {
            block: parent.block.clone(),
            offset: PointerOffsetTerm::scale_int32(
                MachineTerm::Variable(Variable(1542185793994)),
                4,
            ),
        };
        let cursor = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                MachineTerm::Variable(Variable(2035320285104)),
                4,
            ),
        };
        let parameter = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(100000)), 4),
        };
        let facts = PureFactContext::new()
            .assume_condition(
                ConditionTerm::pointer_equal(parameter.clone(), parent),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(old_read.clone(), model.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), old_read), true)
            .assume_condition(
                ConditionTerm::pointer_equal(cursor.clone(), model.clone()),
                true,
            );
        let range = |base: Pointer, start: u32, end: u32| {
            MemoryRange::new_with_element_width(base, start.into(), end.into(), 4)
        };
        let resources = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(range(parameter.clone(), 0, 2)))
            .unchecked_with_fact(ResourceFact::own_memory(range(parameter, 4, 6)))
            .unchecked_with_fact(ResourceFact::own_memory(range(model.clone(), 2, 6)))
            .unchecked_with_fact(ResourceFact::own_memory(range(model.clone(), 20, 24)))
            .unchecked_with_fact(ResourceFact::view_memory(range(model, 6, 8)));
        resources.synchronize_memory_equalities(&facts);
        let required = ResourceFact::own_memory(range(cursor.clone(), 4, 6));
        let residual = resources
            .clone()
            .without_fact_incrementally(&required, &facts)
            .expect("the selected interior field is owned");
        assert!(residual.satisfies_fact(
            &ResourceFact::own_memory(range(cursor.clone(), 2, 4)),
            &facts
        ));
        assert!(!residual.satisfies_fact(&required, &facts));
        assert!(resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &facts));
        assert!(resources.permits_memory_read(&cursor.offset_by_bytes(24), 8, &facts));
        for (start, end) in [(0, 2), (4, 7), (6, 8)] {
            let unowned = ResourceFact::own_memory(range(cursor.clone(), start, end));
            assert!(
                resources
                    .clone()
                    .without_fact_incrementally(&unowned, &facts)
                    .is_none()
            );
        }
        assert!(
            resources
                .without_fact_incrementally(&required, &PureFactContext::new())
                .is_none()
        );
    }

    #[test]
    fn modeled_pointer_alias_selects_one_of_multiple_owned_fields() {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = Pointer::symbolic(Variable(4000000));
        let model = Pointer::symbolic(Variable(4065536));
        let old_read = Pointer {
            block: parent.block.clone(),
            offset: PointerOffsetTerm::scale_int32(
                MachineTerm::Variable(Variable(1542185793994)),
                4,
            ),
        };
        let cursor = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                MachineTerm::Variable(Variable(2035320285104)),
                4,
            ),
        };
        let parameter = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(100000)), 4),
        };
        let facts = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(parameter, parent), true)
            .assume_condition(
                ConditionTerm::pointer_equal(old_read.clone(), model.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(cursor.clone(), old_read.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), model), true);
        let owner = |offset| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                old_read.offset_by_bytes(offset),
                0u32.into(),
                1u32.into(),
                8,
            ))
        };
        let resources = ResourceContext::new()
            .unchecked_with_fact(owner(8))
            .unchecked_with_fact(owner(0));
        resources.synchronize_memory_equalities(&facts);
        assert!(
            facts
                .equality_graph
                .are_equal(&cursor.offset_by_bytes(8), &old_read.offset_by_bytes(8))
        );
        assert!(resources.permits_memory_read(&cursor.offset_by_bytes(8), 8, &facts));
        assert!(
            !facts
                .equality_graph
                .are_equal(&cursor.offset_by_bytes(8), &old_read.offset_by_bytes(16))
        );
        assert!(!resources.permits_memory_read(&cursor.offset_by_bytes(8), 9, &facts));
        assert!(!resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &facts));
        let missing_alias = PureFactContext::new();
        assert!(!resources.permits_memory_read(&cursor.offset_by_bytes(8), 8, &missing_alias));
    }

    fn view(base: &Pointer, start: u32, end: u32) -> ResourceFact {
        ResourceFact::view_memory(MemoryRange::new_with_element_width(
            base.clone(),
            start.into(),
            end.into(),
            1,
        ))
    }

    #[test]
    fn concrete_read_coverage_tracks_resource_deltas_and_isolates_forks() {
        let base = Pointer::symbolic(Variable(851_000));
        let alias = Pointer::symbolic(Variable(851_001));
        let empty = PureFactContext::new();
        let resources = ResourceContext::new().unchecked_with_fact(view(&base, 0, 8));
        resources.synchronize_memory_equalities(&empty);
        let facts = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        );
        assert!(resources.permits_memory_read(&alias, 8, &facts));
        assert!(!resources.permits_memory_read(&alias, 9, &facts));
        assert!(!resources.permits_memory_read(&alias, 1, &empty));
        let short = view(&base, 2, 4);
        let mixed = resources.clone().unchecked_with_fact(short.clone());
        assert!(mixed.concrete_read_entries(&base, 8, &facts).is_some());
        // A shorter nearest predecessor must not hide the longer view.
        let interior = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        };
        assert!(mixed.permits_memory_read(&interior, 4, &facts));
        let restored = mixed.clone().without_exact_representation(&short).unwrap();
        assert!(restored.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(resources.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(mixed.concrete_read_entries(&alias, 8, &facts).is_some());
        assert!(restored.memory_write_range(&alias, 1, &facts).is_none());
    }

    #[test]
    fn overlapping_views_use_complete_read_intervals() {
        let base = Pointer::symbolic(Variable(851_010));
        let facts = PureFactContext::new();
        let resources = ResourceContext::new()
            .unchecked_with_fact(view(&base, 0, 8))
            .unchecked_with_fact(view(&base, 4, 12));
        let at = |offset| Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        assert!(resources.concrete_read_entries(&at(6), 6, &facts).is_some());
        assert!(resources.permits_memory_read(&at(6), 6, &facts));
        assert!(!resources.permits_memory_read(&at(6), 7, &facts));
        assert!(!resources.permits_memory_read(&at(12), 1, &facts));
    }

    #[test]
    fn write_intervals_preserve_authority_coverage_and_branch_isolation() {
        let base = Pointer::symbolic(Variable(861_000));
        let middle = Pointer::symbolic(Variable(861_001));
        let alias = Pointer::symbolic(Variable(861_002));
        let owned_range =
            MemoryRange::new_with_element_width(base.clone(), 0u32.into(), 32u32.into(), 1);
        let owned = ResourceFact::own_memory(owned_range.clone());
        // An exact-size view must neither grant writes nor hide a longer owner.
        let short = view(&base, 8, 12);
        let resources = ResourceContext::new()
            .unchecked_with_fact(owned.clone())
            .unchecked_with_fact(short.clone());
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let sibling = resources.clone();
        let displaced = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let facts = empty
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(displaced, middle.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(middle, alias.clone()), true);
        assert!(
            resources
                .concrete_write_entries(&alias, 4, &facts)
                .is_some()
        );
        assert_eq!(
            resources.memory_write_range(&alias, 4, &facts),
            Some(&owned_range)
        );
        assert_eq!(
            resources.memory_write_range(&alias, 24, &facts),
            Some(&owned_range)
        );
        assert!(resources.memory_write_range(&alias, 25, &facts).is_none());
        assert!(sibling.memory_write_range(&alias, 4, &empty).is_none());
        let views = resources
            .clone()
            .without_exact_representation(&owned)
            .unwrap();
        assert!(views.permits_memory_read(&alias, 4, &facts));
        assert!(views.memory_write_range(&alias, 4, &facts).is_none());
        let restored = views.unchecked_with_fact(owned);
        assert_eq!(
            restored.memory_write_range(&alias, 24, &facts),
            Some(&owned_range)
        );
    }

    #[test]
    fn pointer_slot_candidates_preserve_the_checked_logical_width_rule() {
        let base = Pointer::symbolic(Variable(851_015));
        let facts = PureFactContext::new();
        let slot = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new(base.clone(), 0u32.into(), 1u32.into()),
        ));
        assert!(slot.permits_memory_read(&base, C_POINTER_BYTE_WIDTH, &facts));
        assert!(!slot.permits_memory_read(&base, 16, &facts));
        assert!(
            slot.memory_write_range(&base, C_POINTER_BYTE_WIDTH, &facts)
                .is_some()
        );
        assert!(slot.memory_write_range(&base, 16, &facts).is_none());
        // Candidate selection is an overapproximation. The logical rule does
        // not authorize a pointer read from a four-byte, byte-indexed view.
        let bytes = ResourceContext::new().unchecked_with_fact(view(&base, 0, 4));
        assert!(!bytes.permits_memory_read(&base, C_POINTER_BYTE_WIDTH, &facts));
        let byte_owner = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(base.clone(), 0u32.into(), 4u32.into(), 1),
        ));
        assert!(
            byte_owner
                .memory_write_range(&base, C_POINTER_BYTE_WIDTH, &facts)
                .is_none()
        );
    }

    #[test]
    fn mixed_extent_reads_find_covering_view_hidden_by_shorter_predecessor() {
        let base = Pointer::symbolic(Variable(851_020));
        let alias = Pointer::symbolic(Variable(851_021));
        let empty = PureFactContext::new();
        let resources = ResourceContext::new()
            .unchecked_with_fact(view(&base, 0, 32))
            .unchecked_with_fact(view(&base, 4, 8));
        resources.synchronize_memory_equalities(&empty);
        let middle = Pointer::symbolic(Variable(851_022));
        let displaced = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let facts = empty
            .assume_condition(
                ConditionTerm::pointer_equal(displaced, middle.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(middle, alias.clone()), true);
        let interior = Pointer {
            block: alias.block,
            offset: PointerOffsetTerm::Constant(4),
        };
        assert!(
            resources
                .concrete_read_entries(&interior, 20, &facts)
                .is_some()
        );
        assert!(resources.permits_memory_read(&interior, 20, &facts));
        assert!(!resources.permits_memory_read(&interior, 21, &facts));
        let without_long = resources
            .clone()
            .without_exact_representation(&view(&base, 0, 32))
            .unwrap();
        assert!(!without_long.permits_memory_read(&interior, 1, &facts));
        assert!(resources.permits_memory_read(&interior, 20, &facts));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/memory_equality_index/tests.rs");
    }
}
