use super::*;
use crate::kernel::assumptions::{wide_index_binary, wide_index_comparison};
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::int32_constant;
use crate::kernel::{CompareRelation, MachineCastSpelling, MachineIntegerType, OverflowOperation};
mod observable;
mod ownership_admission;
pub(crate) use ownership_admission::FlatBodyAdmission;

/// A proof-aware composition query in progress on this thread. Bridging a
/// query's state form to a carrier entry can itself ask whether a
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
    ResourcesSeparate(Resource, Resource),
    RangesSeparate(MemoryRange, MemoryRange),
    PointersSeparate(Address, Address),
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
        MemoryRange::new(
            Address::new("buffer".into(), AddressOffset::constant(0)),
            OldMachineTerm::constant(index as u32),
            OldMachineTerm::constant(index as u32 + 1),
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

pub(super) fn insert_resource_index_entry<K: Ord>(
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
    range: &MemoryRange,
) -> Option<Vec<ResourceMemoryIntervalNode>> {
    let (start, end) = concrete_memory_range_bounds(range)?;
    memory_interval_nodes_for_coordinates(&range.base().base, start, end)
}

pub(in crate::kernel) fn memory_interval_nodes_for_coordinates(
    block: &AddressBase,
    start: i64,
    end: i64,
) -> Option<Vec<ResourceMemoryIntervalNode>> {
    if start < i64::from(i32::MIN) || end > i64::from(i32::MAX) {
        return None;
    }
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
            block: block.clone(),
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
/// than [`AddressBase::proven_distinct`]: one of these blocks stands for an
/// address the caller chose, and the answer here is spent dropping a resource
/// projection, where being coarse only ever drops more. The three predicates
/// below are the evidence language of the resource tracker's footprint arm
/// (`src/kernel/resource_tracker/step_effect.rs`), which is the only decider
/// that reads them.
pub(in crate::kernel) fn memory_block_may_alias(block: &AddressBase) -> bool {
    matches!(
        block,
        AddressBase::ExternalArgument
            | AddressBase::Symbolic(_)
            | AddressBase::FunctionSymbolic(_)
            | AddressBase::Load(_)
            | AddressBase::SliceData(_)
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

/// The root of a memory base: its block and the first symbolic atom of its
/// offset, read left to right through additions and put in canonical form,
/// or `None` when the offset is wholly constant.
///
/// A base is its object's root plus displacements (`p`, `p + 8`,
/// `p + 4*i`): offsets are built by adding a displacement to the base they
/// displace, so the object's own spelling comes first. Two bases with
/// different roots are different symbolic objects as far as their spelling
/// goes; only a fact can relate them (an exact alias, or a recorded
/// equality between the roots' index terms), and
/// [`related_memory_base_roots`] adds the roots such facts select.
pub(in crate::kernel) fn memory_base_root(base: &Address) -> MemoryBaseRoot {
    (base.base.clone(), offset_root_atom(&base.offset))
}

/// The offset half of [`memory_base_root`].
pub(in crate::kernel) fn offset_root_atom(offset: &AddressOffset) -> Option<AddressOffset> {
    let mut pending = vec![offset];
    while let Some(offset) = pending.pop() {
        match offset.view() {
            OffsetView::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            OffsetView::Constant(_) => {}
            OffsetView::Variable(_) => return Some(offset.clone()),
            OffsetView::Int32Scaled { index, byte_width } => {
                if index.operand_view().word32_constant().is_some() {
                    continue;
                }
                return Some(AddressOffset::int32_scaled(
                    crate::kernel::proof::equality_rewrite::canonical_pointer_index(&index)?,
                    byte_width,
                ));
            }
            OffsetView::Int64Scaled {
                index,
                byte_width,
                unsigned,
            } => {
                return Some(AddressOffset::int64_scaled(
                    crate::kernel::proof::equality_rewrite::canonical_pointer_index(&index)?,
                    byte_width,
                    unsigned,
                ));
            }
        }
    }
    None
}

/// The roots a base is related to by facts: its own root, and for a root
/// that scales an index term, the roots that scale each member of that
/// term's recorded-equality class (a member pinned to a constant relates
/// the base to the block's constant-offset bases).
fn related_memory_base_roots(
    base: &Address,
    assumptions: &PureFactContext,
) -> BTreeSet<MemoryBaseRoot> {
    let mut roots = BTreeSet::new();
    extend_related_memory_base_roots(base, assumptions, &mut roots, &mut BTreeSet::new());
    roots
}

/// How a root scales its index term: whether it is the int64 form, its byte
/// width, and whether it is unsigned.
type IndexScale = (bool, i64, bool);

/// Add `base`'s related roots (see [`related_memory_base_roots`]) to
/// `roots`.
///
/// `walked` holds the equality classes already walked into `roots`, each
/// member under its block and scale. A recorded-equality class is an
/// equivalence class (its evidence edges are symmetric), so walking it from
/// any member reaches the same members; a base whose index lies in a walked
/// class relates to exactly the roots that walk added, and is not walked
/// again. That holds when the base's own root is the image of its index,
/// which both sides check: the class leaves its starting term out, and the
/// root stands for it.
fn extend_related_memory_base_roots(
    base: &Address,
    assumptions: &PureFactContext,
    roots: &mut BTreeSet<MemoryBaseRoot>,
    walked: &mut BTreeSet<(AddressBase, IndexScale, SharedMachineIntegerTerm)>,
) {
    let root = memory_base_root(base);
    roots.insert(root.clone());
    let (block, Some(atom)) = root.clone() else {
        return;
    };
    let (value, scale, rescale): (
        SharedMachineIntegerTerm,
        IndexScale,
        &dyn Fn(SharedMachineIntegerTerm) -> AddressOffset,
    ) = match atom.view() {
        OffsetView::Int32Scaled { index, byte_width } => {
            (index, (false, byte_width, false), &move |member| {
                crate::kernel::memory_history::rebuild_scaled_pointer_index(
                    member, byte_width, None,
                )
            })
        }
        OffsetView::Int64Scaled {
            index,
            byte_width,
            unsigned,
        } => (index, (true, byte_width, unsigned), &move |member| {
            crate::kernel::memory_history::rebuild_scaled_pointer_index(
                member,
                byte_width,
                Some(unsigned),
            )
        }),
        _ => return,
    };
    let image = |member: SharedMachineIntegerTerm| {
        memory_base_root(&Address::new(block.clone(), rescale(member)))
    };
    let index = value.operand_view().retain(MachineIntegerType::Int32);
    let root_is_own_image = image(index.clone()) == root;
    if root_is_own_image && walked.contains(&(block.clone(), scale, index.clone())) {
        return;
    }
    for member in assumptions.recorded_equality_class_view(value.operand_view()) {
        crate::instrumentation::record_deterministic_work(1);
        if root_is_own_image {
            walked.insert((block.clone(), scale, member.clone()));
        }
        roots.insert(image(member));
    }
    if root_is_own_image {
        walked.insert((block.clone(), scale, index));
    }
}

/// A constant translation of exactly one unregistered int32 scalar atom.
/// Loads, sums of atoms, and native/wide expressions stay open. In particular
/// a registered load variable is not an independent address parameter.
fn memory_base_variable(base: &Address) -> Option<Variable> {
    let mut variable = None;
    let mut pending = vec![&base.offset];
    while let Some(offset) = pending.pop() {
        match offset.view() {
            OffsetView::Constant(_) => {}
            OffsetView::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            OffsetView::Int32Scaled { index, byte_width } if byte_width > 0 => {
                let candidate = index.operand_view().variable()?;
                if variable.is_some() || crate::kernel::is_load_variable(candidate) {
                    return None;
                }
                variable = Some(*candidate);
            }
            _ => return None,
        }
    }
    variable
}

fn owned_range_base_variable(range: &MemoryRange) -> Option<Variable> {
    range.signed_constant_start()?;
    range.signed_constant_end()?;
    memory_base_variable(range.base())
}

/// Exact byte coordinates relative to the base, for ordered neighbour probes
/// and partition sweeps. Signed narrow bounds and unsigned native bounds both
/// fit in i128 after multiplication by the u32 element width. TrackedResource terms
/// themselves are unchanged; no machine-integer narrowing is involved.
fn constant_relative_byte_endpoints(range: &MemoryRange) -> (Option<i128>, Option<i128>) {
    let (start, end) = match range.wide_bounds() {
        Some((start, end)) => (
            start.uint64_as_const().map(i128::from),
            end.uint64_as_const().map(i128::from),
        ),
        None => (
            range.signed_constant_start().map(i128::from),
            range.signed_constant_end().map(i128::from),
        ),
    };
    let width = i128::from(range.element_width());
    (start.map(|n| n * width), end.map(|n| n * width))
}

/// Key constant ranges by their symbolic base and exact byte coordinates.
/// Pointer construction combines trailing constant translations; peel just
/// that explicit displacement, without traversing offsets or consulting facts.
pub(in crate::kernel) fn constant_memory_coordinates(
    range: &MemoryRange,
) -> Option<(Address, i128, i128)> {
    let (start, end) = constant_relative_byte_endpoints(range);
    let (start, end) = (start?, end?);
    let original = range.base();
    let (offset, displacement) = match original.offset.view() {
        OffsetView::Constant(n) => (AddressOffset::constant(0), i128::from(n)),
        OffsetView::Add(left, right) => match (left.view(), right.view()) {
            (OffsetView::Constant(a), OffsetView::Constant(b)) => {
                (AddressOffset::constant(0), i128::from(a) + i128::from(b))
            }
            (_, OffsetView::Constant(n)) => (left.clone(), i128::from(n)),
            (OffsetView::Constant(n), _) => (right.clone(), i128::from(n)),
            _ => (original.offset.clone(), 0),
        },
        _ => (original.offset.clone(), 0),
    };
    Some((
        original.with_offset(offset),
        start.checked_add(displacement)?,
        end.checked_add(displacement)?,
    ))
}

pub(super) fn remove_resource_index_entry<K: Ord + Clone>(
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

/// One fact's share of `ResourceContextIndex::fact_hash`.
pub(super) fn resource_fact_content_hash(fact: &ResourceFact) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    fact.hash(&mut hasher);
    hasher.finish()
}

fn spatial_memory_fact_key(fact: &ResourceFact) -> Option<ResourceFact> {
    let resource = Resource::Memory(fact.memory_range()?.spatial_key());
    Some(match fact {
        ResourceFact::Own(_, units) => ResourceFact::Own(resource, units.clone()),
        ResourceFact::View(_) => ResourceFact::View(resource),
    })
}

pub(super) fn nominal_ownership_block(block: &AddressBase) -> bool {
    matches!(
        block,
        AddressBase::Heap(_)
            | AddressBase::Temporary(_)
            | AddressBase::Concrete(_)
            | AddressBase::AutomaticLocal { .. }
            | AddressBase::StaticObject { .. }
            | AddressBase::AggregateReturn { .. }
            | AddressBase::ContractResult
            | AddressBase::ContractException
    )
}

impl ResourceContextIndex {
    /// Files or withdraws one identity as able to fail instance validity:
    /// held twice, or held once with other than one owned unit.
    fn refresh_suspect_instance(&mut self, identity: InstanceId) {
        let suspect = self
            .instances
            .get(&identity)
            .is_some_and(|entries| entries.len() >= 2)
            || self.invalid_instance_access.contains_key(&identity);
        let filed = self.suspect_instances.contains_key(&identity);
        if suspect && !filed {
            self.suspect_instances = self.suspect_instances.with_inserted(identity, ());
        } else if !suspect && filed {
            self.suspect_instances = self.suspect_instances.without_key(&identity);
        }
    }

    fn refresh_suspect_mutex_authority(&mut self, identity: Resource) {
        let suspect = self
            .by_resource
            .get(&identity)
            .is_some_and(|entries| entries.len() >= 2)
            || self.invalid_mutex_authority_access.contains_key(&identity);
        if suspect {
            self.suspect_mutex_authorities =
                self.suspect_mutex_authorities.with_inserted(identity, ());
        } else {
            self.suspect_mutex_authorities = self.suspect_mutex_authorities.without_key(&identity);
        }
    }

    fn with_inserted(&self, entry: ResourceEntryId, fact: &ResourceFact) -> Self {
        let mut result = self.clone();
        if fact.allocation().is_some() {
            result.owned_allocation_tokens = result.owned_allocation_tokens.with_value(entry);
        }
        if let Some(key) = heap_anchored_composite_key(fact) {
            let count = result
                .heap_anchored_composite_counts
                .get(&key)
                .copied()
                .unwrap_or(0);
            result.heap_anchored_composite_counts.insert(key, count + 1);
        }
        result.written_normalization.insert(entry, fact);
        if fact.is_own()
            && !fact
                .memory_own_range()
                .is_some_and(|range| super::block_is_never_address_taken_local(&range.base().base))
        {
            result.boundary_frame_revision = std::sync::Arc::new(());
        }

        let registry = super::never_address_taken_locals_key();
        if result
            .boundary_private_registry
            .as_ref()
            .is_none_or(|prior| !std::sync::Arc::ptr_eq(prior, &registry))
        {
            result.boundary_private_registry = Some(registry);
            result.boundary_private_entries = ResourceEntryIds::default();
        }

        let mut new_memory_range = false;
        if fact.memory_range().is_some() && !self.exact.contains_key(fact) {
            result.memory_facts.insert(fact.clone(), ());
        }
        if fact.is_own() && fact.memory_range().is_none() && !self.exact.contains_key(fact) {
            result.owned_non_memory_facts.insert(fact.clone(), ());
        }
        if let Some(range) = fact.memory_own_range() {
            let count = result
                .owned_memory_range_counts
                .get(range)
                .copied()
                .unwrap_or(0);
            result.owned_memory_range_counts = result
                .owned_memory_range_counts
                .with_inserted(range.clone(), count + 1);
            if count == 0 {
                new_memory_range = true;
                result.owned_memory_ranges.insert(range.clone(), ());
            }
        }
        if fact.is_own() {
            if fact.memory_own_range().is_none() {
                result.owned_non_memory_entries = result.owned_non_memory_entries.with_value(entry);
            }
            result.owned_count += 1;
            if let Resource::Composite { arguments, .. } = fact.resource() {
                result.owned_composite_count += 1;
                let count = result.owned_composite_facts.get(fact).copied().unwrap_or(0);
                result.owned_composite_facts.insert(fact.clone(), count + 1);
                for pointer in algebraic_pointer_arguments(arguments) {
                    result.owned_composites_by_pointer_argument = insert_resource_index_entry(
                        &result.owned_composites_by_pointer_argument,
                        pointer.clone(),
                        entry,
                    );
                    result.owned_composites_by_argument_block = insert_resource_index_entry(
                        &result.owned_composites_by_argument_block,
                        pointer.base.clone(),
                        entry,
                    );
                }
            }
        }
        if let ResourceFact::View(Resource::Composite { arguments, .. }) = fact {
            for pointer in algebraic_pointer_arguments(arguments) {
                result.viewed_composites_by_argument_block = insert_resource_index_entry(
                    &result.viewed_composites_by_argument_block,
                    pointer.base.clone(),
                    entry,
                );
            }
        }
        if let Resource::MutexGuard(identity) = fact.resource() {
            result.mutex_authorities = insert_resource_index_entry(
                &result.mutex_authorities,
                (ResourceFamily::MutexGuard, identity.mutex.clone()),
                entry,
            );
        }
        if let Resource::MutexUse(identity) = fact.resource() {
            result.mutex_authorities = insert_resource_index_entry(
                &result.mutex_authorities,
                (ResourceFamily::MutexUse, identity.mutex.clone()),
                entry,
            );
        }
        if let Resource::MutexLive(identity) = fact.resource() {
            result.mutex_authorities = insert_resource_index_entry(
                &result.mutex_authorities,
                (ResourceFamily::MutexLive, identity.mutex.clone()),
                entry,
            );
        }
        if let Resource::Publication(right) = fact.resource() {
            result.mutex_authorities = insert_resource_index_entry(
                &result.mutex_authorities,
                (ResourceFamily::Publication, right.flag.clone()),
                entry,
            );
            if right.observed.is_some() {
                result.observed_publications =
                    insert_resource_index_entry(&result.observed_publications, (), entry);
            }
        }
        if let Resource::ConditionalMutexGuard(carrier) = fact.resource() {
            result.instances =
                insert_resource_index_entry(&result.instances, carrier.identity, entry);
            if !fact.has_valid_exclusive_access() {
                let count = result
                    .invalid_instance_access
                    .get(&carrier.identity)
                    .copied()
                    .unwrap_or(0);
                result.invalid_instance_access = result
                    .invalid_instance_access
                    .with_inserted(carrier.identity, count + 1);
            }
            result.refresh_suspect_instance(carrier.identity);
        }
        if let Resource::Instance(instance) = fact.resource() {
            result.instances =
                insert_resource_index_entry(&result.instances, instance.identity, entry);
            if !fact.has_valid_exclusive_access() {
                let count = result
                    .invalid_instance_access
                    .get(&instance.identity)
                    .copied()
                    .unwrap_or(0);
                result.invalid_instance_access = result
                    .invalid_instance_access
                    .with_inserted(instance.identity, count + 1);
            }
            result.refresh_suspect_instance(instance.identity);
            result.instance_shapes = insert_resource_index_entry(
                &result.instance_shapes,
                (instance.name.clone(), instance.arguments.len()),
                entry,
            );
            if fact.is_own() {
                for pointer in instance_pointer_arguments(instance) {
                    result.owned_instances_by_pointer_argument = insert_resource_index_entry(
                        &result.owned_instances_by_pointer_argument,
                        pointer.clone(),
                        entry,
                    );
                }
            }
        }
        if let Resource::Iterated(iterated) = fact.resource() {
            let [first, second] = iterated.blocks();
            result.iterated_by_block =
                insert_resource_index_entry(&result.iterated_by_block, first.clone(), entry);
            if second != first {
                result.iterated_by_block =
                    insert_resource_index_entry(&result.iterated_by_block, second.clone(), entry);
            }
            if matches!(fact, ResourceFact::Own(_, quantity) if quantity.as_const() == Some(1)) {
                result.owned_iterated_by_clause = insert_resource_index_entry(
                    &result.owned_iterated_by_clause,
                    iterated.without_holes(),
                    entry,
                );
            }
        }
        for block in prepared_argument_resource_blocks(fact) {
            result.prepared_argument_resources = insert_resource_index_entry(
                &result.prepared_argument_resources,
                block.clone(),
                entry,
            );
        }
        let hash = resource_fact_content_hash(fact);
        result.fact_hash = result.fact_hash.wrapping_add(hash);
        result.canonical = result.canonical.with_inserted(fact, hash);
        if let Some(range) = fact.memory_own_range() {
            result.boundary_memory_count += 1;
            if super::block_is_never_address_taken_local(&range.base().base) {
                result.boundary_private_entries = result.boundary_private_entries.with_value(entry);
            }
            result.boundary_non_nominal_count +=
                usize::from(!nominal_ownership_block(&range.base().base));
            let block = &range.base().base;
            result.boundary_non_argument_or_nominal_count += usize::from(
                !nominal_ownership_block(block)
                    && !matches!(
                        block,
                        AddressBase::ExternalArgument | AddressBase::ExternalObject(_)
                    ),
            );
            result.boundary_may_alias_argument_count += usize::from(
                !(nominal_ownership_block(block)
                    && block.proven_distinct(&AddressBase::ExternalArgument)),
            );
            if new_memory_range {
                if self.boundary_memory.identity() == self.canonical.identity()
                    && fact.owned_quantity_term() == Some(&OldMachineTerm::constant(1))
                {
                    result.boundary_memory = result.canonical.clone();
                    result.boundary_memory.prepare_footprint();
                } else {
                    result.boundary_memory = result.boundary_memory.with_memory_range(range);
                }
            }
        }
        result.exact = insert_resource_index_entry(&result.exact, fact.clone(), entry);
        if let Some(key) = spatial_memory_fact_key(fact) {
            result.spatial_memory = insert_resource_index_entry(&result.spatial_memory, key, entry);
        }
        result.by_resource =
            insert_resource_index_entry(&result.by_resource, fact.resource().clone(), entry);
        if let Some(amount) = numeric_population_owned_units(fact) {
            let prior = result
                .numeric_owned_units
                .get(fact.resource())
                .copied()
                .unwrap_or((0, 0));
            result.numeric_owned_units.insert(
                fact.resource().clone(),
                (prior.0 + u128::from(amount), prior.1 + 1),
            );
        }
        if matches!(
            fact.resource(),
            Resource::PopulationAuthority(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
        ) {
            let identity = fact.resource();
            if !fact.has_valid_exclusive_access() {
                let count = result
                    .invalid_mutex_authority_access
                    .get(identity)
                    .copied()
                    .unwrap_or(0);
                result.invalid_mutex_authority_access = result
                    .invalid_mutex_authority_access
                    .with_inserted(identity.clone(), count + 1);
            }
            result.refresh_suspect_mutex_authority(identity.clone());
        }
        if let Some(range) = fact.memory_range() {
            let block = range.base().base.clone();
            let mode = fact.is_own();
            if !matches!(
                block,
                AddressBase::Concrete(_)
                    | AddressBase::StaticObject { .. }
                    | AddressBase::AutomaticLocal { .. }
                    | AddressBase::ReferenceCarrier { .. }
            ) {
                result.nonconcrete_memory_count += 1;
            }
            result.memory_by_block =
                insert_resource_index_entry(&result.memory_by_block, block.clone(), entry);
            result.memory_by_base =
                insert_resource_index_entry(&result.memory_by_base, range.base().clone(), entry);
            result.structural_memory.update(range.base(), entry, true);
            result
                .memory_addresses
                .update(range, fact.is_own(), entry, true, fact);
            result.memory_objects.update(entry, true, fact);
            if mode {
                result.owned_memory_by_base = insert_resource_index_entry(
                    &result.owned_memory_by_base,
                    range.base().clone(),
                    entry,
                );
                if let Some(variable) = owned_range_base_variable(range) {
                    result.owned_memory_by_base_variable = insert_resource_index_entry(
                        &result.owned_memory_by_base_variable,
                        (block.clone(), variable),
                        entry,
                    );
                } else {
                    result.owned_memory_open_bases = insert_resource_index_entry(
                        &result.owned_memory_open_bases,
                        block.clone(),
                        entry,
                    );
                }
                result.owned_memory_by_root = insert_resource_index_entry(
                    &result.owned_memory_by_root,
                    memory_base_root(range.base()),
                    entry,
                );
                if let Some(anchor) = crate::kernel::assumptions::memory_range_anchor(range) {
                    result.owned_memory_by_anchor =
                        insert_resource_index_entry(&result.owned_memory_by_anchor, anchor, entry);
                }
                if result.owned_memory_by_block.is_empty() {
                    result.owned_hidden_memory_by_block = Default::default();
                    result.owned_hidden_memory_generation =
                        Some(super::memory_state::never_address_taken_generation());
                }
                if matches!(
                    block,
                    AddressBase::Concrete(_)
                        | AddressBase::AutomaticLocal { .. }
                        | AddressBase::StaticObject { .. }
                        | AddressBase::AggregateReturn { .. }
                        | AddressBase::ContractResult
                        | AddressBase::ContractException
                        | AddressBase::Heap(_)
                        | AddressBase::Temporary(_)
                ) {
                    result.owned_physical_memory_by_block = insert_resource_index_entry(
                        &result.owned_physical_memory_by_block,
                        block.clone(),
                        entry,
                    );
                }
                result.owned_memory_by_block = insert_resource_index_entry(
                    &result.owned_memory_by_block,
                    block.clone(),
                    entry,
                );
                if block_is_never_address_taken_local(&block) {
                    result.owned_hidden_memory_by_block = insert_resource_index_entry(
                        &result.owned_hidden_memory_by_block,
                        block.clone(),
                        entry,
                    );
                }
                if block.is_local_block() {
                    result.owned_automatic_memory_by_block = insert_resource_index_entry(
                        &result.owned_automatic_memory_by_block,
                        block.clone(),
                        entry,
                    );
                }
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
            if let Some((origin, start, end)) = constant_memory_coordinates(range) {
                if mode && start < end {
                    result
                        .constant_owned_intervals
                        .update(&origin, start, end, entry, true);
                }
                let base = (origin, mode);
                // Empty intervals carry no overlap obligation and must not
                // hide a nonempty predecessor from the neighbour check.
                if start < end {
                    result.concrete_memory = insert_resource_index_entry(
                        &result.concrete_memory,
                        (base.0.clone(), mode, start, end),
                        entry,
                    );
                }
                let count = result
                    .concrete_memory_by_base
                    .get(&base)
                    .copied()
                    .unwrap_or(0)
                    + 1;
                result.concrete_memory_by_base =
                    result.concrete_memory_by_base.with_inserted(base, count);
            }
        } else if let Resource::Composite { name, arguments }
        | Resource::Token { name, arguments } = fact.resource()
        {
            result.exact_shapes = insert_resource_index_entry(
                &result.exact_shapes,
                (fact.family(), name.clone(), arguments.len()),
                entry,
            );
            result.exact_shapes_by_root = insert_resource_index_entry(
                &result.exact_shapes_by_root,
                shape_root_key(fact.family(), name, arguments),
                entry,
            );
        }
        result
    }

    fn without_entry(&self, entry: ResourceEntryId, fact: &ResourceFact) -> Self {
        let mut result = self.clone();
        if fact.allocation().is_some() {
            result.owned_allocation_tokens = result.owned_allocation_tokens.without_value(&entry);
        }
        if let Some(key) = heap_anchored_composite_key(fact) {
            let count = *result
                .heap_anchored_composite_counts
                .get(&key)
                .expect("heap-anchored composite count exists");
            if count == 1 {
                result.heap_anchored_composite_counts.remove(&key);
            } else {
                result.heap_anchored_composite_counts.insert(key, count - 1);
            }
        }
        result.written_normalization.remove(entry, fact);
        if fact.is_own()
            && !fact
                .memory_own_range()
                .is_some_and(|range| super::block_is_never_address_taken_local(&range.base().base))
        {
            result.boundary_frame_revision = std::sync::Arc::new(());
        }

        let registry = super::never_address_taken_locals_key();
        if result
            .boundary_private_registry
            .as_ref()
            .is_none_or(|prior| !std::sync::Arc::ptr_eq(prior, &registry))
        {
            result.boundary_private_registry = Some(registry);
            result.boundary_private_entries = ResourceEntryIds::default();
        }

        let mut last_memory_range = false;
        if fact.memory_range().is_some()
            && self
                .exact
                .get(fact)
                .is_some_and(|entries| entries.len() == 1)
        {
            result.memory_facts.remove(fact);
        }
        if fact.is_own()
            && fact.memory_range().is_none()
            && self
                .exact
                .get(fact)
                .is_some_and(|entries| entries.len() == 1)
        {
            result.owned_non_memory_facts.remove(fact);
        }
        if let Some(range) = fact.memory_own_range() {
            let count = result
                .owned_memory_range_counts
                .get(range)
                .copied()
                .expect("owned range is indexed");
            if count == 1 {
                last_memory_range = true;
                result.owned_memory_range_counts =
                    result.owned_memory_range_counts.without_key(range);
                result.owned_memory_ranges.remove(range);
            } else {
                result.owned_memory_range_counts = result
                    .owned_memory_range_counts
                    .with_inserted(range.clone(), count - 1);
            }
        }
        if fact.is_own() {
            if fact.memory_own_range().is_none() {
                result.owned_non_memory_entries =
                    result.owned_non_memory_entries.without_value(&entry);
            }
            result.owned_count -= 1;
            if let Resource::Composite { arguments, .. } = fact.resource() {
                result.owned_composite_count -= 1;
                let count = result
                    .owned_composite_facts
                    .get(fact)
                    .copied()
                    .expect("owned composite count exists");
                if count == 1 {
                    result.owned_composite_facts.remove(fact);
                } else {
                    result.owned_composite_facts.insert(fact.clone(), count - 1);
                }
                for pointer in algebraic_pointer_arguments(arguments) {
                    result.owned_composites_by_pointer_argument = remove_resource_index_entry(
                        &result.owned_composites_by_pointer_argument,
                        pointer,
                        entry,
                    );
                    result.owned_composites_by_argument_block = remove_resource_index_entry(
                        &result.owned_composites_by_argument_block,
                        &pointer.base,
                        entry,
                    );
                }
            }
        }
        if let ResourceFact::View(Resource::Composite { arguments, .. }) = fact {
            for pointer in algebraic_pointer_arguments(arguments) {
                result.viewed_composites_by_argument_block = remove_resource_index_entry(
                    &result.viewed_composites_by_argument_block,
                    &pointer.base,
                    entry,
                );
            }
        }
        if let Resource::MutexGuard(identity) = fact.resource() {
            result.mutex_authorities = remove_resource_index_entry(
                &result.mutex_authorities,
                &(ResourceFamily::MutexGuard, identity.mutex.clone()),
                entry,
            );
        }
        if let Resource::MutexUse(identity) = fact.resource() {
            result.mutex_authorities = remove_resource_index_entry(
                &result.mutex_authorities,
                &(ResourceFamily::MutexUse, identity.mutex.clone()),
                entry,
            );
        }
        if let Resource::MutexLive(identity) = fact.resource() {
            result.mutex_authorities = remove_resource_index_entry(
                &result.mutex_authorities,
                &(ResourceFamily::MutexLive, identity.mutex.clone()),
                entry,
            );
        }
        if let Resource::Publication(right) = fact.resource() {
            result.mutex_authorities = remove_resource_index_entry(
                &result.mutex_authorities,
                &(ResourceFamily::Publication, right.flag.clone()),
                entry,
            );
            if right.observed.is_some() {
                result.observed_publications =
                    remove_resource_index_entry(&result.observed_publications, &(), entry);
            }
        }
        if let Resource::ConditionalMutexGuard(carrier) = fact.resource() {
            result.instances =
                remove_resource_index_entry(&result.instances, &carrier.identity, entry);
            if !fact.has_valid_exclusive_access() {
                let count = *result
                    .invalid_instance_access
                    .get(&carrier.identity)
                    .expect("indexed invalid access");
                result.invalid_instance_access = if count == 1 {
                    result
                        .invalid_instance_access
                        .without_key(&carrier.identity)
                } else {
                    result
                        .invalid_instance_access
                        .with_inserted(carrier.identity, count - 1)
                };
            }
            result.refresh_suspect_instance(carrier.identity);
        }
        if let Resource::Instance(instance) = fact.resource() {
            result.instances =
                remove_resource_index_entry(&result.instances, &instance.identity, entry);
            if !fact.has_valid_exclusive_access() {
                let count = result
                    .invalid_instance_access
                    .get(&instance.identity)
                    .copied()
                    .expect("invalid instance access count exists");
                result.invalid_instance_access = if count == 1 {
                    result
                        .invalid_instance_access
                        .without_key(&instance.identity)
                } else {
                    result
                        .invalid_instance_access
                        .with_inserted(instance.identity, count - 1)
                };
            }
            result.refresh_suspect_instance(instance.identity);
            result.instance_shapes = remove_resource_index_entry(
                &result.instance_shapes,
                &(instance.name.clone(), instance.arguments.len()),
                entry,
            );
            if fact.is_own() {
                for pointer in instance_pointer_arguments(instance) {
                    result.owned_instances_by_pointer_argument = remove_resource_index_entry(
                        &result.owned_instances_by_pointer_argument,
                        pointer,
                        entry,
                    );
                }
            }
        }
        for block in prepared_argument_resource_blocks(fact) {
            result.prepared_argument_resources =
                remove_resource_index_entry(&result.prepared_argument_resources, block, entry);
        }
        if let Resource::Iterated(iterated) = fact.resource() {
            let [first, second] = iterated.blocks();
            result.iterated_by_block =
                remove_resource_index_entry(&result.iterated_by_block, first, entry);
            if second != first {
                result.iterated_by_block =
                    remove_resource_index_entry(&result.iterated_by_block, second, entry);
            }
            if matches!(fact, ResourceFact::Own(_, quantity) if quantity.as_const() == Some(1)) {
                result.owned_iterated_by_clause = remove_resource_index_entry(
                    &result.owned_iterated_by_clause,
                    &iterated.without_holes(),
                    entry,
                );
            }
        }
        let hash = resource_fact_content_hash(fact);
        result.fact_hash = result.fact_hash.wrapping_sub(hash);
        result.canonical = result.canonical.without_one(fact, hash);
        if let Some(range) = fact.memory_own_range() {
            result.boundary_memory_count -= 1;
            result.boundary_private_entries = result.boundary_private_entries.without_value(&entry);
            result.boundary_non_nominal_count -=
                usize::from(!nominal_ownership_block(&range.base().base));
            let block = &range.base().base;
            result.boundary_non_argument_or_nominal_count -= usize::from(
                !nominal_ownership_block(block)
                    && !matches!(
                        block,
                        AddressBase::ExternalArgument | AddressBase::ExternalObject(_)
                    ),
            );
            result.boundary_may_alias_argument_count -= usize::from(
                !(nominal_ownership_block(block)
                    && block.proven_distinct(&AddressBase::ExternalArgument)),
            );
            if last_memory_range {
                if self.boundary_memory.identity() == self.canonical.identity()
                    && fact.owned_quantity_term() == Some(&OldMachineTerm::constant(1))
                {
                    result.boundary_memory = result.canonical.clone();
                    result.boundary_memory.prepare_footprint();
                } else {
                    result.boundary_memory = result.boundary_memory.without_memory_range(range);
                }
            }
        }
        result.exact = remove_resource_index_entry(&result.exact, fact, entry);
        if let Some(key) = spatial_memory_fact_key(fact) {
            result.spatial_memory =
                remove_resource_index_entry(&result.spatial_memory, &key, entry);
        }
        result.by_resource =
            remove_resource_index_entry(&result.by_resource, fact.resource(), entry);
        if let Some(amount) = numeric_population_owned_units(fact) {
            let prior = result
                .numeric_owned_units
                .get(fact.resource())
                .copied()
                .expect("numeric units indexed");
            let remaining = (
                prior
                    .0
                    .checked_sub(u128::from(amount))
                    .expect("numeric units conserved"),
                prior.1 - 1,
            );
            if remaining.1 == 0 {
                result.numeric_owned_units.remove(fact.resource());
            } else {
                result
                    .numeric_owned_units
                    .insert(fact.resource().clone(), remaining);
            }
        }
        if matches!(
            fact.resource(),
            Resource::PopulationAuthority(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
        ) {
            let identity = fact.resource();
            if !fact.has_valid_exclusive_access() {
                let count = result
                    .invalid_mutex_authority_access
                    .get(identity)
                    .copied()
                    .expect("invalid mutex authority access count exists");
                result.invalid_mutex_authority_access = if count == 1 {
                    result.invalid_mutex_authority_access.without_key(identity)
                } else {
                    result
                        .invalid_mutex_authority_access
                        .with_inserted(identity.clone(), count - 1)
                };
            }
            result.refresh_suspect_mutex_authority(identity.clone());
        }
        if let Some(range) = fact.memory_range() {
            let block = range.base().base.clone();
            let mode = fact.is_own();
            if !matches!(
                block,
                AddressBase::Concrete(_)
                    | AddressBase::StaticObject { .. }
                    | AddressBase::AutomaticLocal { .. }
                    | AddressBase::ReferenceCarrier { .. }
            ) {
                result.nonconcrete_memory_count -= 1;
            }
            result.memory_by_block =
                remove_resource_index_entry(&result.memory_by_block, &block, entry);
            result.memory_by_base =
                remove_resource_index_entry(&result.memory_by_base, range.base(), entry);
            result.structural_memory.update(range.base(), entry, false);
            result
                .memory_addresses
                .update(range, fact.is_own(), entry, false, fact);
            result.memory_objects.update(entry, false, fact);
            if mode {
                result.owned_memory_by_base =
                    remove_resource_index_entry(&result.owned_memory_by_base, range.base(), entry);
                if let Some(variable) = owned_range_base_variable(range) {
                    result.owned_memory_by_base_variable = remove_resource_index_entry(
                        &result.owned_memory_by_base_variable,
                        &(block.clone(), variable),
                        entry,
                    );
                } else {
                    result.owned_memory_open_bases =
                        remove_resource_index_entry(&result.owned_memory_open_bases, &block, entry);
                }
                result.owned_memory_by_root = remove_resource_index_entry(
                    &result.owned_memory_by_root,
                    &memory_base_root(range.base()),
                    entry,
                );
                if let Some(anchor) = crate::kernel::assumptions::memory_range_anchor(range) {
                    result.owned_memory_by_anchor =
                        remove_resource_index_entry(&result.owned_memory_by_anchor, &anchor, entry);
                }
                result.owned_memory_by_block =
                    remove_resource_index_entry(&result.owned_memory_by_block, &block, entry);
                result.owned_hidden_memory_by_block = remove_resource_index_entry(
                    &result.owned_hidden_memory_by_block,
                    &block,
                    entry,
                );
                result.owned_physical_memory_by_block = remove_resource_index_entry(
                    &result.owned_physical_memory_by_block,
                    &block,
                    entry,
                );
                if block.is_local_block() {
                    result.owned_automatic_memory_by_block = remove_resource_index_entry(
                        &result.owned_automatic_memory_by_block,
                        &block,
                        entry,
                    );
                }
                if !result
                    .owned_memory_by_block
                    .get(&block)
                    .is_some_and(|entries| entries.len() >= 2)
                {
                    result.shared_owned_memory_blocks =
                        result.shared_owned_memory_blocks.without_key(&block);
                }
            }
            if let Some((origin, start, end)) = constant_memory_coordinates(range) {
                if mode && start < end {
                    result
                        .constant_owned_intervals
                        .update(&origin, start, end, entry, false);
                }
                let base = (origin, mode);
                if start < end {
                    result.concrete_memory = remove_resource_index_entry(
                        &result.concrete_memory,
                        &(base.0.clone(), mode, start, end),
                        entry,
                    );
                }
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
        } else if let Resource::Composite { name, arguments }
        | Resource::Token { name, arguments } = fact.resource()
        {
            result.exact_shapes = remove_resource_index_entry(
                &result.exact_shapes,
                &(fact.family(), name.clone(), arguments.len()),
                entry,
            );
            result.exact_shapes_by_root = remove_resource_index_entry(
                &result.exact_shapes_by_root,
                &shape_root_key(fact.family(), name, arguments),
                entry,
            );
        }
        result
    }
}

/// Whether one recorded step can have written a projection's stated footprint.
///
/// The per-step rule is the resource tracker's, asked about
/// [`crate::kernel::resource_tracker::TrackedResource::Ranges`] for a footprint the
/// kernel could name and
/// [`crate::kernel::resource_tracker::TrackedResource::AnyMemory`] for one it could
/// not, so a new step kind has one answer for a footprint rather than one per
/// caller. A footprint with no memory in it is never touched and is not asked
/// about at all.
/// `evidence` is the caller's, built once per invalidation rather than per
/// step: the footprint arm reads none of it, and constructing an empty context
/// inside this loop would be work the rule does not need.
fn memory_derivation_affects_footprint(
    derivation: &MemoryDerivation,
    produced: &crate::kernel::SharedMemory,
    footprint: &ResourceMemoryFootprint,
    evidence: &crate::kernel::resource_tracker::step_effect::Evidence<'_>,
) -> bool {
    use crate::kernel::resource_tracker::{TrackedResource, step_effect};
    let resource = match footprint {
        ResourceMemoryFootprint::Exact(ranges) => TrackedResource::Ranges(ranges),
        ResourceMemoryFootprint::Unknown => TrackedResource::AnyMemory,
        ResourceMemoryFootprint::None => return false,
    };
    !matches!(
        step_effect::affects(derivation, produced, resource, evidence),
        step_effect::StepEffect::Separate(step_effect::Separation::Footprint(_))
    )
}

/// The widest scalar access the kernel performs. Signed and unsigned
/// 128-bit cells are sixteen bytes. A caller that cannot name its own access
/// width must stand in this one to bound every byte possibly touched.
pub(in crate::kernel) const MAX_SCALAR_ACCESS_BYTES: i64 = 16;

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
    range: &MemoryRange,
    pointer: &Address,
    bytes: u32,
) -> bool {
    let pointer_base = pointer.with_offset(pointer.offset.clone());
    if range.base().blocks_proven_distinct(&pointer_base) {
        return false;
    }
    // Constant offsets locate bytes only within one block: `q + 8` in one
    // block is `p + 0` in another when `q` is `p - 8`.
    if range.base().base != pointer.base {
        return true;
    }
    let Some((start, end)) = concrete_memory_range_bounds(range) else {
        return true;
    };
    let Some(pointer_offset) = pointer.offset.as_const() else {
        return true;
    };
    // An access whose end is not representable is read as reaching everything,
    // as is a range whose span is not; neither is a bound to subtract from.
    let (Some(_), Some(span)) = (
        pointer_offset.checked_add(i64::from(bytes)),
        end.checked_sub(start),
    ) else {
        return true;
    };
    !byte_intervals_disjoint(pointer_offset, i64::from(bytes), start, span)
}

fn add_memory_interval_candidates(
    index: &PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    subtree: &PersistentMap<ResourceMemoryIntervalNode, ResourceOccurrenceIds>,
    range: &MemoryRange,
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

pub(in crate::kernel) fn memory_ranges_overlap(left: &MemoryRange, right: &MemoryRange) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return false;
    }
    if left.base().base != right.base().base {
        return true;
    }
    let (Some((left_start, left_end)), Some((right_start, right_end))) = (
        concrete_memory_range_bounds(left),
        concrete_memory_range_bounds(right),
    ) else {
        return true;
    };
    left_start < right_end && right_start < left_end
}

pub(crate) fn concrete_memory_range_bounds(range: &MemoryRange) -> Option<(i64, i64)> {
    let base = range.base().offset.as_const()?;
    let start_elements = range.signed_constant_start()?;
    let end_elements = range.signed_constant_end()?;
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

fn memory_footprint_for_fact(fact: &ResourceFact) -> ResourceMemoryFootprint {
    if let Some(range) = fact.memory_range() {
        let mut ranges = vec![range.clone()];
        let mut uncertain = false;
        let mut source_memory_state = None;
        collect_memory_load_ranges(
            &range.base().offset,
            &mut ranges,
            &mut uncertain,
            &mut source_memory_state,
        );
        collect_memory_load_ranges_from_term(
            range.bound_terms().0,
            &mut ranges,
            &mut uncertain,
            &mut source_memory_state,
        );
        collect_memory_load_ranges_from_term(
            range.bound_terms().1,
            &mut ranges,
            &mut uncertain,
            &mut source_memory_state,
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
    if matches!(fact.resource(), Resource::Composite { .. }) {
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
    offset: &AddressOffset,
    ranges: &mut Vec<MemoryRange>,
    uncertain: &mut bool,
    source_memory_state: &mut Option<MemoryStateIdentity>,
) {
    collect_memory_load_work(
        [MemoryLoadFootprintWork::Offset(offset, 0)],
        ranges,
        uncertain,
        source_memory_state,
    );
}

const MAX_MEMORY_LOAD_FOOTPRINT_DEPTH: usize = 64;

enum MemoryLoadFootprintWork<'a> {
    Shared(&'a KernelTerm, usize),
    Offset(&'a AddressOffset, usize),
    /// A scaled index, held by value because an offset view owns it.
    Index(SharedMachineIntegerTerm, usize),
    Term(&'a OldMachineTerm, usize),
}

fn collect_memory_load_ranges_from_term(
    term: &OldMachineTerm,
    ranges: &mut Vec<MemoryRange>,
    uncertain: &mut bool,
    source_memory_state: &mut Option<MemoryStateIdentity>,
) {
    collect_memory_load_work(
        [MemoryLoadFootprintWork::Term(term, 0)],
        ranges,
        uncertain,
        source_memory_state,
    );
}

fn collect_memory_load_work<'a>(
    initial: impl IntoIterator<Item = MemoryLoadFootprintWork<'a>>,
    ranges: &mut Vec<MemoryRange>,
    uncertain: &mut bool,
    source_memory_state: &mut Option<MemoryStateIdentity>,
) {
    collect_memory_load_work_with(
        initial,
        &mut std::collections::HashSet::new(),
        ranges,
        uncertain,
        source_memory_state,
    );
}

/// The footprint walk over `initial`, sharing `shared_seen` with an
/// enclosing walk. A nested walk runs to completion where its item would
/// have been popped, so it visits as the enclosing stack would.
fn collect_memory_load_work_with<'a>(
    initial: impl IntoIterator<Item = MemoryLoadFootprintWork<'a>>,
    shared_seen: &mut std::collections::HashSet<(u64, usize)>,
    ranges: &mut Vec<MemoryRange>,
    uncertain: &mut bool,
    source_memory_state: &mut Option<MemoryStateIdentity>,
) {
    let mut work = initial.into_iter().collect::<Vec<_>>();
    while let Some(item) = work.pop() {
        match item {
            MemoryLoadFootprintWork::Index(index, depth) => {
                // The index's operand borrows from the owned index, so it is
                // walked by a nested walk over the same seen set.
                let operand = match index.shared_operand() {
                    Some(node) => MemoryLoadFootprintWork::Shared(node, depth),
                    None => MemoryLoadFootprintWork::Term(
                        index.retained_written_operand().expect("native index"),
                        depth,
                    ),
                };
                collect_memory_load_work_with(
                    [operand],
                    shared_seen,
                    ranges,
                    uncertain,
                    source_memory_state,
                );
            }
            MemoryLoadFootprintWork::Shared(node, depth) => {
                // Footprints are unions. Repeated DAG occurrences at the same
                // depth add no range or uncertainty; different depths retain
                // the native depth refusal.
                if !shared_seen.insert((node.id(), depth)) {
                    continue;
                }
                crate::instrumentation::record_deterministic_work(1);
                if depth > MAX_MEMORY_LOAD_FOOTPRINT_DEPTH {
                    *uncertain = true;
                    continue;
                }
                if let Some(leaf) = node
                    .machine_conversion_leaf()
                    .or_else(|| node.machine_read_leaf())
                {
                    work.push(MemoryLoadFootprintWork::Term(leaf, depth));
                    continue;
                }
                match node.node() {
                    crate::kernel::KernelTermNode::MachineBinary { arguments, .. } => {
                        for child in arguments {
                            work.push(MemoryLoadFootprintWork::Shared(child, depth + 1));
                        }
                    }
                    crate::kernel::KernelTermNode::MachineUnary { operand, .. }
                    | crate::kernel::KernelTermNode::MachineCast { operand, .. } => {
                        work.push(MemoryLoadFootprintWork::Shared(operand, depth + 1));
                    }
                    crate::kernel::KernelTermNode::MachineLiteral(_)
                    | crate::kernel::KernelTermNode::Variable(_) => {}
                    _ => *uncertain = true,
                }
            }
            MemoryLoadFootprintWork::Offset(offset, depth) => {
                if depth > MAX_MEMORY_LOAD_FOOTPRINT_DEPTH {
                    *uncertain = true;
                    continue;
                }
                match offset.view() {
                    OffsetView::Constant(_) | OffsetView::Variable(_) => {}
                    OffsetView::Add(left, right) => {
                        work.push(MemoryLoadFootprintWork::Offset(left, depth + 1));
                        work.push(MemoryLoadFootprintWork::Offset(right, depth + 1));
                    }
                    OffsetView::Int32Scaled { index, .. }
                    | OffsetView::Int64Scaled { index, .. } => {
                        work.push(MemoryLoadFootprintWork::Index(index, depth + 1));
                    }
                }
            }
            MemoryLoadFootprintWork::Term(term, depth) => {
                if depth > MAX_MEMORY_LOAD_FOOTPRINT_DEPTH {
                    *uncertain = true;
                    continue;
                }
                match term {
                    OldMachineTerm::ThreadHandle(_) => {}
                    OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
                        // The checked source state's cell gives the loaded
                        // scalar's ABI width, and the read is never narrower
                        // than its own kind; absent evidence is ambiguous.
                        let Some(value) = memory.memory().known_value(pointer) else {
                            *uncertain = true;
                            continue;
                        };
                        let width = value.byte_width().max(kind.byte_width());
                        if width == 0 {
                            *uncertain = true;
                            continue;
                        }
                        let retained_state = MemoryStateIdentity::of(memory.memory());
                        if source_memory_state.is_some_and(|previous| previous != retained_state) {
                            *uncertain = true;
                            continue;
                        }
                        *source_memory_state = Some(retained_state);
                        ranges.push(MemoryRange::new_with_element_width(
                            pointer.as_ref().clone(),
                            OldMachineTerm::constant(0),
                            OldMachineTerm::constant(1),
                            width,
                        ));
                        work.push(MemoryLoadFootprintWork::Offset(&pointer.offset, depth + 1));
                    }
                    OldMachineTerm::IntegerAddress(pointer, _) => {
                        work.push(MemoryLoadFootprintWork::Offset(&pointer.offset, depth + 1));
                    }
                    crate::kernel::binary_machine_term!(left, right)
                    | OldMachineTerm::Float32Binary { left, right, .. }
                    | OldMachineTerm::Float64Binary { left, right, .. } => {
                        work.push(MemoryLoadFootprintWork::Term(left, depth + 1));
                        work.push(MemoryLoadFootprintWork::Term(right, depth + 1));
                    }
                    crate::kernel::unary_machine_term!(value) => {
                        work.push(MemoryLoadFootprintWork::Term(value, depth + 1));
                    }
                    OldMachineTerm::Constant { .. } | OldMachineTerm::Variable(_) => {}
                    // These forms can hide load-bearing children behind a
                    // separate semantic object. Until checked read evidence
                    // is exposed for that object, invalidate conservatively.
                    OldMachineTerm::If { .. }
                    | OldMachineTerm::BoolCast { .. }
                    | OldMachineTerm::RangeFold { .. }
                    | OldMachineTerm::PureFunctionApplication { .. }
                    | OldMachineTerm::ClickFunctionApplication { .. }
                    | OldMachineTerm::PureApplicationCount(_)
                    | OldMachineTerm::AlgebraicMatch { .. }
                    | OldMachineTerm::IntegerToMachine { .. } => *uncertain = true,
                }
            }
        }
    }
}

impl MemorySplitOrigins {
    /// One indexed lookup, including after arbitrarily many successive splits.
    pub(crate) fn origin_of(&self, occurrence: ResourceOccurrenceId) -> ResourceOccurrenceId {
        crate::instrumentation::record_deterministic_work(1);
        self.origins.get(&occurrence).copied().unwrap_or(occurrence)
    }
}

impl ResourceContext {
    /// Install transferred guard custody using its exact authority key.
    /// The owning rule has consumed its supplier; this checks exclusivity
    /// before updating the normal resource indexes.
    pub(in crate::kernel) fn insert_transferred_mutex_guard(
        mut self,
        guard: MutexIdentity,
    ) -> Result<Self, ResourceContextValidityError> {
        let fact = ResourceFact::own(Resource::MutexGuard(guard));
        if self.storage.index.by_resource.contains_key(fact.resource()) {
            return Err(ResourceContextValidityError::DuplicateOwnedResourceFact(
                fact,
            ));
        }
        self.insert_fact(fact);
        Ok(self)
    }

    /// Restore one checked loop occurrence, selecting by its nominal identity.
    pub(in crate::kernel) fn insert_transferred_conditional_guard(
        mut self,
        guard: Arc<ConditionalMutexGuard>,
    ) -> Result<Self, ResourceContextValidityError> {
        if self.storage.index.instances.contains_key(&guard.identity) {
            return Err(ResourceContextValidityError::DuplicateOwnedResourceFact(
                ResourceFact::own(Resource::ConditionalMutexGuard(guard)),
            ));
        }
        self.insert_fact(ResourceFact::own(Resource::ConditionalMutexGuard(guard)));
        Ok(self)
    }

    fn exclusive_validity_error(
        &self,
        fact: &ResourceFact,
    ) -> Option<ResourceContextValidityError> {
        if let Resource::PopulationAuthority(_)
        | Resource::MutexGuard(_)
        | Resource::MutexLive(_)
        | Resource::MutexUse(_) = fact.resource()
        {
            if !fact.has_valid_exclusive_access() {
                return Some(ResourceContextValidityError::InvalidExclusiveAccess(
                    fact.clone(),
                ));
            }
            return (self
                .storage
                .index
                .by_resource
                .get(fact.resource())
                .map_or(0, ResourceEntryIds::len)
                != 1)
                .then(|| ResourceContextValidityError::DuplicateOwnedResourceFact(fact.clone()));
        }
        let identity = match fact.resource() {
            Resource::Instance(instance) => instance.identity,
            Resource::ConditionalMutexGuard(carrier) => carrier.identity,
            _ => return None,
        };
        if !fact.has_valid_exclusive_access() {
            return Some(ResourceContextValidityError::InvalidExclusiveAccess(
                fact.clone(),
            ));
        }
        let valid = self
            .storage
            .index
            .instances
            .get(&identity)
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
                ResourceFact::Own(Resource::Instance(instance), quantity)
                    if quantity.as_const() == Some(1) =>
                {
                    Some(instance)
                }
                _ => None,
            })
            .collect()
    }

    /// The owned instances whose held entries differ from `earlier`'s:
    /// every owned instance when there is no earlier context. The index of
    /// instances is persistent, so for contexts derived from one another the
    /// walk visits only the changed identities.
    pub(crate) fn changed_owned_instances<'a>(
        &'a self,
        earlier: Option<&'a Self>,
    ) -> Vec<&'a ResourceInstance> {
        let identities: Vec<InstanceId> = match earlier {
            Some(earlier) => self
                .storage
                .index
                .instances
                .diff(&earlier.storage.index.instances)
                .filter_map(|(identity, now, _)| now.map(|_| *identity))
                .collect(),
            None => self.storage.index.instances.keys().copied().collect(),
        };
        identities
            .into_iter()
            .filter_map(|identity| self.owned_instance(identity))
            .collect()
    }

    pub fn owned_instance(&self, identity: InstanceId) -> Option<&ResourceInstance> {
        let entries = self.storage.index.instances.get(&identity)?;
        if entries.len() != 1 {
            return None;
        }
        let ResourceFact::Own(Resource::Instance(instance), quantity) =
            self.fact(*entries.iter().next()?)
        else {
            return None;
        };
        (quantity.as_const() == Some(1)).then_some(instance)
    }

    /// A structural/unpublished context. Use `new_with_equalities` for a
    /// fresh kernel proof context that will receive selected resource facts.
    /// Do not attach an ambient context from a read-only lookup.
    pub fn new() -> Self {
        Self::default()
    }

    /// A temporary contract-reading view retains every resource and dependency,
    /// but must not publish synthetic argument permissions into an ambient
    /// prepared equality index. Its queries prepare only their selected input.
    pub(crate) fn unpublished_contract_view(&self) -> Self {
        let mut view = self.clone();
        view.memory_equalities = Default::default();
        view.observable_projection = Default::default();
        view
    }

    /// Begin a fresh resource lineage in the current trusted equality graph.
    /// Capturing the empty input is constant work; later inserts maintain its
    /// paired indexes through deltas. This establishes publication only, not
    /// resource validity or authority: callers still check their selected facts.
    pub(crate) fn new_with_equalities(assumptions: &PureFactContext) -> Self {
        let context = Self::new();
        context.synchronize_memory_equalities(assumptions);
        context
    }

    pub(in crate::kernel) fn memory_input_facts(&self) -> &HashedOrdMap<ResourceFact, ()> {
        &self.storage.index.memory_facts
    }

    /// The owned facts of resources other than memory, each once.
    pub(in crate::kernel) fn owned_non_memory_input_facts(
        &self,
    ) -> &HashedOrdMap<ResourceFact, ()> {
        &self.storage.index.owned_non_memory_facts
    }

    pub(in crate::kernel) fn flat_owned_memory_ranges(&self) -> &HashedOrdMap<MemoryRange, ()> {
        &self.storage.index.owned_memory_ranges
    }

    /// Whether two resource states are the exact same persistent value.
    ///
    /// Proof joins use this constant-time identity check to retain a resource
    /// context that was untouched in every arm without enumerating it.
    pub(crate) fn shares_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.storage, &other.storage)
    }

    /// A retained projection preserves custody and witnesses with the
    /// visible resource facts. Compare only their persistent roots.
    pub(in crate::kernel) fn shares_projection_inputs_with(&self, other: &Self) -> bool {
        fn same_root<T>(
            left: &Option<std::sync::Arc<T>>,
            right: &Option<std::sync::Arc<T>>,
        ) -> bool {
            match (left, right) {
                (Some(left), Some(right)) => std::sync::Arc::ptr_eq(left, right),
                (None, None) => true,
                _ => false,
            }
        }
        self.shares_storage_with(other)
            && std::sync::Arc::ptr_eq(&self.borrow_dependencies, &other.borrow_dependencies)
            && self.framed_origins.shares_root_with(&other.framed_origins)
            && same_root(&self.instance_consumptions, &other.instance_consumptions)
            && same_root(&self.structural_witnesses, &other.structural_witnesses)
    }

    /// Direct occurrences of only the selected resource. Cached projections
    /// are not independent units and must not be counted or moved as such.
    pub(in crate::kernel) fn exact_resource_facts(&self, resource: &Resource) -> Vec<ResourceFact> {
        self.storage
            .index
            .by_resource
            .get(resource)
            .into_iter()
            .flat_map(|entries| entries.iter())
            .filter(|entry| {
                !self
                    .storage
                    .support_occurrence_by_projection
                    .contains_key(entry)
            })
            .map(|entry| self.fact(*entry).clone())
            .collect()
    }

    /// The owned memory member that is exactly `range`, by its spatial key:
    /// how a range whose bounds are not constants, such as a whole object
    /// of abstract size, is found as a member of the partition.
    pub(in crate::kernel) fn exact_owned_memory_member(
        &self,
        range: &MemoryRange,
    ) -> Option<(u64, &MemoryRange)> {
        crate::instrumentation::record_deterministic_work(1);
        let key = spatial_memory_fact_key(&ResourceFact::own(Resource::Memory(range.clone())))?;
        let entry = *self.storage.index.spatial_memory.get(&key)?.iter().next()?;
        if self.storage.supported_by.contains_key(&entry)
            || self
                .storage
                .support_occurrence_by_projection
                .contains_key(&entry)
        {
            return None;
        }
        Some((entry, self.fact(entry).memory_own_range()?))
    }

    /// Separation of two explicitly selected, independently held resources.
    /// The valid partition supplies the authority; views alone do not separate.
    /// Inspect one exact occurrence per written representation. Cached body
    /// projections are not independent members of the partition.
    pub(crate) fn proves_exact_partition_separation(
        &self,
        left: &Resource,
        right: &Resource,
    ) -> bool {
        #[cfg(test)]
        let _operation =
            crate::kernel::search::FastOperationScope::enter("exact partition separation");
        if left == right
            || matches!((left, right), (Resource::Memory(a), Resource::Memory(b))
            if a.spatial_key() == b.spatial_key())
        {
            return false;
        }
        let direct = |fact: ResourceFact| {
            let entry = if let Some(key) = spatial_memory_fact_key(&fact) {
                self.storage.index.spatial_memory.get(&key)
            } else {
                self.storage.index.exact.get(&fact)
            };
            entry
                .and_then(|entries| entries.iter().next())
                .is_some_and(|entry| {
                    !self.storage.supported_by.contains_key(entry)
                        && !self
                            .storage
                            .support_occurrence_by_projection
                            .contains_key(entry)
                })
        };
        let left_owned = direct(ResourceFact::own(left.clone()));
        let right_owned = direct(ResourceFact::own(right.clone()));
        (left_owned && (right_owned || direct(ResourceFact::View(right.clone()))))
            || (right_owned && direct(ResourceFact::View(left.clone())))
    }

    /// Whether this state contains the exact named representation.
    /// This does not use proof-aware entailment; representation-sensitive
    /// rewrites need the entry itself, not an entailed cached projection.
    pub(crate) fn contains_exact_representation(&self, fact: &ResourceFact) -> bool {
        self.storage.index.exact.contains_key(fact)
    }

    pub(super) fn history_tail_is(
        current: Option<&std::sync::Arc<ResourceContextChange>>,
        expected: Option<&std::sync::Arc<ResourceContextChange>>,
    ) -> bool {
        match (current, expected) {
            (Some(current), Some(expected)) => std::sync::Arc::ptr_eq(current, expected),
            (None, None) => true,
            _ => false,
        }
    }

    pub(crate) fn changed_facts_since(&self, ancestor: &Self) -> Option<BTreeSet<ResourceFact>> {
        if !std::sync::Arc::ptr_eq(&self.storage.origin, &ancestor.storage.origin) {
            return None;
        }
        let expected = ancestor.storage.history.as_ref();
        let mut current = self.storage.history.as_ref();
        let mut changed = BTreeSet::new();
        while !Self::history_tail_is(current, expected) {
            let change = current?;
            // An unrelated sibling cannot reach this ancestor. Stop at the
            // selected delta's depth instead of walking their shared past.
            if change.depth <= expected.map_or(0, |change| change.depth) {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            changed.insert(change.fact.clone());
            current = change.parent.as_ref();
        }
        Some(changed)
    }

    /// New live memory inputs between two retained sibling or ancestor
    /// checkpoints. Work follows their explicit deltas to the common prefix;
    /// it never walks the shared history or enumerates the source's frame.
    pub(in crate::kernel) fn changed_memory_inputs_from(
        &self,
        previous: &Self,
    ) -> Option<Vec<ResourceFact>> {
        self.changed_inputs_from(previous, |fact| fact.memory_range().is_some())
    }

    /// New live owned members, of memory or not, between two retained
    /// checkpoints, by the same walk as `changed_memory_inputs_from`.
    pub(in crate::kernel) fn changed_owned_inputs_from(
        &self,
        previous: &Self,
    ) -> Option<Vec<ResourceFact>> {
        self.changed_inputs_from(previous, ResourceFact::is_own)
    }

    fn changed_inputs_from(
        &self,
        previous: &Self,
        selected: impl Fn(&ResourceFact) -> bool,
    ) -> Option<Vec<ResourceFact>> {
        if !std::sync::Arc::ptr_eq(&self.storage.origin, &previous.storage.origin) {
            return None;
        }
        let (current, prior) = match (
            &self.storage.observable_projection_source,
            &previous.storage.observable_projection_source,
        ) {
            (Some((key, current)), Some((prior_key, prior)))
                if std::sync::Arc::ptr_eq(key, prior_key) =>
            {
                (current.as_ref(), prior.as_ref())
            }
            (None, None) => (self.storage.as_ref(), previous.storage.as_ref()),
            _ => return None,
        };
        let mut left = current.history.as_ref();
        let mut right = prior.history.as_ref();
        let mut changed = BTreeSet::new();
        while !Self::history_tail_is(left, right) {
            crate::instrumentation::record_deterministic_work(1);
            if left.map_or(0, |change| change.depth) >= right.map_or(0, |change| change.depth) {
                let change = left?;
                if selected(&change.fact) {
                    changed.insert(change.fact.clone());
                }
                left = change.parent.as_ref();
            } else {
                let change = right?;
                if selected(&change.fact) {
                    changed.insert(change.fact.clone());
                }
                right = change.parent.as_ref();
            }
        }
        // History is bookkeeping, not source authority. Only facts actually
        // present in this admitted composition may supply new object evidence.
        Some(
            changed
                .into_iter()
                .filter(|fact| self.storage.index.exact.contains_key(fact))
                .collect(),
        )
    }

    /// Carry the resource delta of a constructed logical exchange onto its
    /// retained execution state. Occurrence identities survive publication;
    /// persistent differences visit only the producer's changed entries.
    pub(in crate::kernel) fn with_constructed_exchange(
        mut self,
        before: &Self,
        after: &Self,
    ) -> Result<Self, &'static str> {
        let changes = before
            .storage
            .entry_by_occurrence
            .diff(&after.storage.entry_by_occurrence)
            .map(|(occurrence, old, new)| (*occurrence, old.copied(), new.copied()))
            .collect::<Vec<_>>();
        // Resolve removals before removing an owner: that removal can also
        // expire several of the selected supported occurrences.
        let mut removals = Vec::new();
        for (occurrence, old, _) in &changes {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(old) = old {
                if let Resource::Instance(instance) = before.fact(*old).resource() {
                    self.record_instance_consumption(
                        instance.identity(),
                        after.instance_consumption(instance.identity()).cloned(),
                    );
                }
                if let Some(entry) = self.storage.entry_by_occurrence.get(occurrence).copied() {
                    removals.push(entry);
                } else if before.fact(*old).is_own() {
                    return Err("return exchange lost a retained owned occurrence");
                }
            }
        }
        for entry in removals {
            if self.storage.facts.contains_key(&entry) {
                self.remove_entry(entry);
            }
        }
        for (occurrence, _, new) in changes {
            crate::instrumentation::record_deterministic_work(1);
            let Some(entry) = new else {
                continue;
            };
            if let Resource::Instance(instance) = after.fact(entry).resource() {
                self.record_instance_consumption(
                    instance.identity(),
                    after.instance_consumption(instance.identity()).cloned(),
                );
            }
            self.insert_fact_with_support_occurrence_and_metadata_at(
                after.fact(entry).clone(),
                after.storage.supported_by.get(&entry).cloned(),
                after
                    .storage
                    .support_occurrence_by_projection
                    .get(&entry)
                    .copied(),
                after
                    .storage
                    .support_metadata_by_projection
                    .get(&occurrence)
                    .cloned(),
                Some(occurrence),
            );
            if let Some(binding) = after.borrow_dependency(occurrence) {
                self = self.with_borrow_dependency(occurrence, binding.clone());
            }
        }
        // Folded expansions retain the state at which their body was
        // constructed. They must travel with the authority, not be rebuilt
        // against the retained C state on the next unfold.
        for (occurrence, _, expansion) in before
            .storage
            .expansions_by_support_occurrence
            .diff(&after.storage.expansions_by_support_occurrence)
        {
            crate::instrumentation::record_deterministic_work(1);
            let Some(entry) = self.storage.entry_by_occurrence.get(occurrence).copied() else {
                continue;
            };
            let support = self.fact(entry).clone();
            self = match expansion {
                Some(expansion) => self.with_cached_supported_expansion_arc(
                    *occurrence,
                    &support,
                    expansion.clone(),
                ),
                None => self.without_cached_supported_expansion_for_occurrence(*occurrence),
            };
        }
        Ok(self)
    }

    /// Exact multiplicity of one representation, for an opt-in proof trace.
    pub(crate) fn exact_count(&self, fact: &ResourceFact) -> usize {
        self.storage
            .index
            .exact
            .get(fact)
            .map_or(0, PersistentSet::len)
    }

    /// Whether this state was obtained by persistent resource mutations
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
                    let supported_by = context.storage.supported_by.get(entry).cloned();
                    // An owned instance is unique by its identity, so the
                    // fact names the supporting occurrence. Its occurrence
                    // id is not compared: a rewrite that makes the instance
                    // and publishes from it allocates a fresh id each time
                    // it is derived.
                    let support = if matches!(
                        supported_by,
                        Some(ResourceFact::Own(Resource::Instance(_), _))
                    ) {
                        None
                    } else {
                        context
                            .storage
                            .support_occurrence_by_projection
                            .get(entry)
                            .copied()
                    };
                    *counts.entry((support, supported_by)).or_insert(0usize) += 1;
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
        let representations = |context: &Self, fact: &ResourceFact| {
            let mut explicit = 0usize;
            let mut supported = BTreeMap::<
                (ResourceFact, ResourceOccurrenceId),
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

    /// Apply a body's direct resource exchange into its enclosing frame.
    /// Only changed keys are visited. Derived projections are not independent
    /// authority: remove affected cached projections and let later reads derive
    /// them again from the surviving supports. Keep direct occurrences so the
    /// exit's checked borrow bindings still name exactly the same authority.
    pub(crate) fn restore_frame_after_exchange(
        &self,
        body: &Self,
        frame: &Self,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let changed = self.changed_facts_since(body)?;
        let mut restored = frame.clone();
        let mut additions = Vec::new();
        for fact in changed {
            crate::instrumentation::record_deterministic_work(1);
            let body_direct = body
                .storage
                .index
                .exact
                .get(&fact)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .filter(|entry| !body.storage.supported_by.contains_key(entry))
                .count();
            let entries = restored
                .storage
                .index
                .exact
                .get(&fact)
                .cloned()
                .unwrap_or_default();
            let mut removed = 0;
            for entry in entries.iter().copied() {
                if !restored.storage.facts.contains_key(&entry) {
                    continue;
                }
                if restored.storage.supported_by.contains_key(&entry) {
                    restored.remove_entry(entry);
                } else if removed < body_direct {
                    restored.remove_entry(entry);
                    removed += 1;
                }
            }
            // A borrowed view may have been supplied only to the body. An
            // owned input, however, must have come from the enclosing frame.
            if fact.is_own() && removed != body_direct {
                return None;
            }
            for entry in self
                .storage
                .index
                .exact
                .get(&fact)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
            {
                if !self.storage.supported_by.contains_key(entry) {
                    additions.push((fact.clone(), self.occurrence(*entry)));
                }
            }
        }
        // Unfolded children carry their selected body root's framing rule.
        // Arbitrary additions still need a boundary with the withheld frame;
        // occurrence identities alone never authorize a new footprint.
        if additions.iter().any(|(_, occurrence)| {
            restored
                .storage
                .entry_by_occurrence
                .contains_key(occurrence)
        }) {
            return None;
        }
        let dependencies = additions
            .iter()
            .filter_map(|(_, occurrence)| {
                self.borrow_dependency(*occurrence)
                    .map(|binding| (*occurrence, binding.clone()))
            })
            .collect::<Vec<_>>();
        for (fact, occurrence) in additions {
            if self
                .framed_origins
                .get(&occurrence)
                .is_some_and(|root| body.owned_fact_for_occurrence(*root).is_some())
            {
                restored = restored
                    .install_established_partition_occurrences(
                        [(fact, Some(occurrence))],
                        assumptions,
                    )
                    .ok()?
                    .0;
            } else {
                restored = match restored.admit_selected_occurrences_without_discovery(
                    [(fact, Some(occurrence))],
                    assumptions,
                ) {
                    ownership_admission::OwnershipAdmission::Admitted { context, .. } => context,
                    _ => return None,
                };
            }
            if let Some(root) = self.framed_origins.get(&occurrence) {
                restored.framed_origins = restored.framed_origins.with_inserted(occurrence, *root);
            }
        }
        for (occurrence, binding) in dependencies {
            restored = restored.with_borrow_dependency(occurrence, binding);
        }
        Some(restored)
    }

    /// Visit an explicitly supplied context at publication or composition.
    /// Supplier lookups must use retained indexes rather than this iterator.
    pub(in crate::kernel) fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &ResourceFact> + ExactSizeIterator {
        self.storage.facts.iter().map(|(_, fact)| fact)
    }

    /// A bounded diagnostic view; never a source of checked resource authority.
    pub(crate) fn diagnostic_facts(
        &self,
        limit: usize,
    ) -> (usize, impl Iterator<Item = &ResourceFact>) {
        (self.storage.facts.len(), self.iter().take(limit))
    }

    fn fact(&self, entry: ResourceEntryId) -> &ResourceFact {
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
        fact: &ResourceFact,
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
    ) -> Option<&ResourceFact> {
        let entry = self.storage.entry_by_occurrence.get(&occurrence)?;
        let fact = self.storage.facts.get(entry)?;
        fact.is_view().then_some(fact)
    }

    /// Retire the exact principal view installed for a checked borrow. General
    /// resource consumption leaves views in place because descriptions are
    /// copyable; closing an escrow instead removes its particular occurrence
    /// before returning the owner. The dependency ties this removal to the
    /// same live binding the borrow recovery just discharged.
    pub(crate) fn without_bound_view_occurrence(
        mut self,
        occurrence: ResourceOccurrenceId,
        binding: &crate::kernel::borrows::BorrowBinding,
    ) -> Option<Self> {
        if !self.view_occurrence_is_principal(occurrence)
            || self.view_fact_at_occurrence(occurrence) != Some(&binding.viewed)
            || self.borrow_dependency(occurrence) != Some(binding)
        {
            return None;
        }
        let entry = *self.storage.entry_by_occurrence.get(&occurrence)?;
        self.remove_entry(entry);
        Some(self)
    }

    /// A release selects one whole view. An equivalent pointer spelling
    /// can name it through the same indexed witness used for reads.
    pub(crate) fn principal_view_for_release(
        &self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceOccurrenceId> {
        crate::instrumentation::record_deterministic_work(1);
        let occurrence = if let Some(entries) = self.storage.index.exact.get(fact) {
            if entries.len() != 1 {
                return None;
            }
            self.occurrence(*entries.iter().next()?)
        } else {
            let occurrence = self.indexed_view_witness(fact, assumptions)?;
            let held = self.view_fact_for_occurrence(occurrence)?;
            if !crate::kernel::resources_directly_match(
                fact.resource(),
                held.resource(),
                assumptions,
            ) {
                return None;
            }
            occurrence
        };
        self.view_occurrence_is_principal(occurrence)
            .then_some(occurrence)
    }

    pub(crate) fn exact_principal_view_occurrences(
        &self,
        fact: &ResourceFact,
    ) -> impl Iterator<Item = ResourceOccurrenceId> + '_ {
        crate::instrumentation::record_deterministic_work(1);
        self.storage
            .principal_views_by_fact
            .get(fact)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.occurrence(*entry))
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

    fn support_cache_key(&self, entry: ResourceEntryId) -> (ResourceFact, usize) {
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

    fn insert_fact(&mut self, fact: ResourceFact) {
        self.insert_fact_with_support(fact, None);
    }

    fn insert_fact_with_support(&mut self, fact: ResourceFact, support: Option<ResourceFact>) {
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
        fact: ResourceFact,
        support: Option<ResourceFact>,
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
        fact: ResourceFact,
        support: Option<ResourceFact>,
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
        fact: ResourceFact,
        support: Option<ResourceFact>,
        support_occurrence: Option<ResourceOccurrenceId>,
        support_metadata: Option<ResourceSupportMetadata>,
        occurrence_override: Option<ResourceOccurrenceId>,
    ) {
        self.insert_fact_with_support_at_entry(
            fact,
            support,
            support_occurrence,
            support_metadata,
            occurrence_override,
            self.storage.next_entry_id,
        );
    }

    fn insert_fact_with_support_at_entry(
        &mut self,
        fact: ResourceFact,
        support: Option<ResourceFact>,
        support_occurrence: Option<ResourceOccurrenceId>,
        support_metadata: Option<ResourceSupportMetadata>,
        occurrence_override: Option<ResourceOccurrenceId>,
        entry: ResourceEntryId,
    ) {
        let previous = self.storage.clone();
        let occurrence = occurrence_override.unwrap_or_else(ResourceOccurrenceId::fresh);
        let next_entry_id = entry
            .checked_add(1)
            .expect("resource entry id space exhausted")
            .max(self.storage.next_entry_id);
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
                    insert_occurrence_index_entry(&index, footprint.base().base.clone(), occurrence)
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
                            || memory_block_may_alias(&range.base().base)
                    }) =>
                {
                    self.storage.symbolic_memory_support.with_value(occurrence)
                }
                _ => self.storage.symbolic_memory_support.clone(),
            },
        );
        let nonmemory_projections_by_fact = if support.is_some() && fact.memory_range().is_none() {
            insert_resource_index_entry(
                &self.storage.nonmemory_projections_by_fact,
                fact.clone(),
                entry,
            )
        } else {
            self.storage.nonmemory_projections_by_fact.clone()
        };
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
            nonmemory_projections_by_fact,
            principal_views_by_fact: if fact.is_view()
                && support.is_none()
                && support_occurrence.is_none()
            {
                insert_resource_index_entry(
                    &self.storage.principal_views_by_fact,
                    fact.clone(),
                    entry,
                )
            } else {
                self.storage.principal_views_by_fact.clone()
            },
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
                depth: self
                    .storage
                    .history
                    .as_ref()
                    .map_or(1, |change| change.depth + 1),
                entry_delta: Some((entry, true)),
                fact,
                parent: self.storage.history.clone(),
            })),
            observable_projection_source: None,
            materialized: std::sync::OnceLock::new(),
        });
        self.advance_observable_insertion(&previous, entry);
        self.advance_published_resource_entries();
    }

    fn remove_entry(&mut self, entry: ResourceEntryId) -> ResourceFact {
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
        // Only an occurrence that carried a borrow dependency changes the
        // dependency state. Minting a new identity for an unchanged map would
        // detach this context from the borrow-binding mirror its state keeps
        // beside it, which is checked by pointer identity.
        if removed_occurrences
            .iter()
            .any(|occurrence| self.borrow_dependencies.map.get(occurrence).is_some())
        {
            let map = removed_occurrences
                .iter()
                .fold(self.borrow_dependencies.map.clone(), |map, occurrence| {
                    map.without_key(occurrence)
                });
            self.borrow_dependencies = self.borrow_dependencies.updated(map, removed_occurrences);
        }
        fact
    }

    fn remove_entry_only(&mut self, entry: ResourceEntryId) -> ResourceFact {
        self.framed_origins = self.framed_origins.without_key(&self.occurrence(entry));
        let previous = self.storage.clone();
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
                    remove_occurrence_index_entry(&index, &footprint.base().base, occurrence)
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
                            || memory_block_may_alias(&range.base().base)
                    }) =>
                {
                    self.storage
                        .symbolic_memory_support
                        .without_value(&occurrence)
                }
                _ => self.storage.symbolic_memory_support.clone(),
            },
        );
        let nonmemory_projections_by_fact = if support.is_some() && fact.memory_range().is_none() {
            remove_resource_index_entry(&self.storage.nonmemory_projections_by_fact, &fact, entry)
        } else {
            self.storage.nonmemory_projections_by_fact.clone()
        };
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.without_key(&entry),
            next_entry_id: self.storage.next_entry_id,
            occurrence_by_entry: self.storage.occurrence_by_entry.without_key(&entry),
            entry_by_occurrence: self.storage.entry_by_occurrence.without_key(&occurrence),
            index: self.storage.index.without_entry(entry, &fact),
            supported_by,
            nonmemory_projections_by_fact,
            principal_views_by_fact: if fact.is_view()
                && support.is_none()
                && support_occurrence.is_none()
            {
                remove_resource_index_entry(&self.storage.principal_views_by_fact, &fact, entry)
            } else {
                self.storage.principal_views_by_fact.clone()
            },
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
                depth: self
                    .storage
                    .history
                    .as_ref()
                    .map_or(1, |change| change.depth + 1),
                entry_delta: Some((entry, false)),
                fact: fact.clone(),
                parent: self.storage.history.clone(),
            })),
            observable_projection_source: None,
            materialized: std::sync::OnceLock::new(),
        });
        self.advance_observable_removal(&previous, entry);
        self.advance_published_resource_entries();
        if fact.is_own() {
            self.rekey_cached_support_entries(&fact);
        }
        fact
    }

    /// Rebuild only the canonical cache keys for one support fact. Removing
    /// an earlier equal authority changes the rank of every later equal
    /// authority; leaving the old `(fact, rank)` entries in place would let a
    /// later insertion inherit stale expansion evidence.
    fn rekey_cached_support_entries(&mut self, fact: &ResourceFact) {
        let previous = self.storage.clone();
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
            nonmemory_projections_by_fact: self.storage.nonmemory_projections_by_fact.clone(),
            principal_views_by_fact: self.storage.principal_views_by_fact.clone(),
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
            observable_projection_source: None,
            materialized: std::sync::OnceLock::new(),
        });
        self.advance_observable_rekey(&previous, fact);
    }

    fn replace_facts(
        &mut self,
        facts: impl IntoIterator<Item = (Option<ResourceOccurrenceId>, ResourceFact)>,
        changed_facts: impl IntoIterator<Item = ResourceFact>,
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
                depth: history.as_ref().map_or(1, |change| change.depth + 1),
                entry_delta: None,
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
            nonmemory_projections_by_fact: PersistentMap::default(),
            principal_views_by_fact: PersistentMap::default(),
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
            observable_projection_source: None,
            materialized: std::sync::OnceLock::new(),
        });
        self.observable_projection = Default::default();
        self.rebuild_paired_memory_entries();
    }

    /// Selects one remaining logical resource for a retiring prepared argument.
    pub(in crate::kernel) fn prepared_argument_resource_name(
        &self,
        block: &AddressBase,
    ) -> Option<&str> {
        crate::instrumentation::record_deterministic_work(1);
        let entries = self.storage.index.prepared_argument_resources.get(block)?;
        let entry = entries.iter().next()?;
        match self.fact(*entry).resource() {
            Resource::Instance(instance) => Some(instance.name()),
            Resource::Composite { name, .. } | Resource::Token { name, .. } => Some(name),
            _ => unreachable!("only logical resources are indexed by prepared argument"),
        }
    }

    /// The owned instances of this context with a C pointer argument equal
    /// to `base`, as their entries and facts, read from the argument index:
    /// one unit to position and one per instance returned, never the
    /// context's other instances.
    pub(in crate::kernel) fn owned_instances_with_pointer_argument<'a>(
        &'a self,
        base: &Address,
    ) -> impl Iterator<Item = (u64, &'a ResourceFact)> + 'a {
        crate::instrumentation::record_deterministic_work(1);
        self.storage
            .index
            .owned_instances_by_pointer_argument
            .get(base)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| {
                crate::instrumentation::record_deterministic_work(1);
                (*entry, self.fact(*entry))
            })
    }

    /// Select a sole folded owner naming this exact pointer argument.
    /// An ambiguous bucket needs separate selection evidence.
    pub(in crate::kernel) fn unique_owned_composite_with_pointer_argument(
        &self,
        pointer: &Address,
    ) -> Option<&ResourceFact> {
        crate::instrumentation::record_deterministic_work(1);
        let entries = self
            .storage
            .index
            .owned_composites_by_pointer_argument
            .get(pointer)?;
        if entries.len() != 1 {
            return None;
        }
        Some(self.fact(*entries.iter().next().expect("one indexed owner")))
    }

    /// Select a sole folded owner with a pointer argument in the block.
    pub(in crate::kernel) fn unique_owned_composite_with_argument_block(
        &self,
        block: &AddressBase,
    ) -> Option<&ResourceFact> {
        crate::instrumentation::record_deterministic_work(1);
        let entries = self
            .storage
            .index
            .owned_composites_by_argument_block
            .get(block)?;
        (entries.len() == 1).then(|| self.fact(*entries.iter().next().expect("one indexed owner")))
    }

    /// Identify a uniform folded frame eligible for projecting retirement by
    /// nominal heap block. The caller must also check the family's body.
    pub(in crate::kernel) fn heap_anchored_retirement_family(&self) -> Option<(&str, ProgramType)> {
        crate::instrumentation::record_deterministic_work(1);
        if self.has_owned_allocation_tokens()
            || !self.storage.expansions_by_support_occurrence.is_empty()
        {
            return None;
        }
        let index = &self.storage.index;
        let mut shapes = index.exact_shapes.iter();
        let ((family, name, arity), entries) = shapes.next()?;
        if *family != ResourceFamily::Composite
            || *arity != 1
            || shapes
                .next()
                .is_some_and(|((family, _, _), _)| *family == ResourceFamily::Composite)
        {
            return None;
        }
        let ((eligible_name, argument_type), count) =
            index.heap_anchored_composite_counts.iter().next()?;
        (eligible_name == name && *count == entries.len())
            .then_some((name.as_str(), *argument_type))
    }

    /// Select at most one held body per consumed block. A block with flat
    /// or iterated custody, or several folded bodies, needs the existing
    /// frame check, even when its other blocks are all heap-anchored.
    pub(in crate::kernel) fn heap_retirement_frontier(
        &self,
        blocks: BTreeSet<&AddressBase>,
    ) -> Option<Self> {
        let index = &self.storage.index;
        let mut frontier = Self::new();
        for block in blocks {
            crate::instrumentation::record_deterministic_work(1);
            if index.memory_by_block.contains_key(block)
                || index.iterated_by_block.contains_key(block)
            {
                return None;
            }
            if let Some(entries) = index.owned_composites_by_argument_block.get(block) {
                if entries.len() != 1 {
                    return None;
                }
                let entry = *entries.iter().next().expect("one folded occurrence");
                frontier = frontier.unchecked_with_fact(self.fact(entry).clone());
            }
        }
        Some(frontier)
    }

    /// The owned folded composites with their multiplicity, as one
    /// content-hashed persistent map.
    pub(in crate::kernel) fn owned_composite_facts(&self) -> &HashedOrdMap<ResourceFact, usize> {
        &self.storage.index.owned_composite_facts
    }

    /// Whether this context holds any owned instance with a C pointer
    /// argument: the constant-time gate before any cell asks the index.
    pub(in crate::kernel) fn has_owned_instances_with_pointer_arguments(&self) -> bool {
        !self
            .storage
            .index
            .owned_instances_by_pointer_argument
            .is_empty()
    }

    /// The facts `ResourceFact::may_refer_to_memory_block` selects for
    /// `block`, drawn from the indexes instead of a scan: the memory facts
    /// based in the block, then the composite facts with a pointer argument
    /// into it. SymbolicMemory in other blocks, tokens and instances are never
    /// visited; a held composite is, since its arguments are not indexed by
    /// block. Charges one work unit per visited fact.
    pub(in crate::kernel) fn facts_that_may_refer_to_memory_block<'a>(
        &'a self,
        block: &AddressBase,
    ) -> impl Iterator<Item = &'a ResourceFact> + use<'a> {
        let composite_block = block.clone();
        let composites = self
            .storage
            .index
            .exact_shapes
            .iter()
            .skip_while(|((family, _, _), _)| *family < ResourceFamily::Composite)
            .take_while(|((family, _, _), _)| *family == ResourceFamily::Composite)
            .flat_map(|(_, entries)| entries.iter())
            .map(|entry| self.fact(*entry))
            .filter(move |fact| fact.may_refer_to_memory_block(&composite_block));
        let iterated = self
            .storage
            .index
            .iterated_by_block
            .get(block)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.fact(*entry));
        self.storage
            .index
            .memory_by_block
            .get(block)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.fact(*entry))
            .chain(composites)
            .chain(iterated)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Whether any explicit fact names this block through the same frontier
    /// used for implicit local composite views.
    pub(in crate::kernel) fn has_fact_referring_to_local_view_block(
        &self,
        block: &AddressBase,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        let index = &self.storage.index;
        index.memory_by_block.contains_key(block)
            || index.owned_composites_by_argument_block.contains_key(block)
            || index
                .viewed_composites_by_argument_block
                .contains_key(block)
            || index.iterated_by_block.contains_key(block)
    }

    /// Positive absence evidence for implicit local-storage borrowing. Any
    /// explicit memory fact in the allocation selects the explicit route,
    /// including partial owners and views. Nonconcrete allocation identities
    /// may alias local storage, including through recorded reads. Cross-block
    /// aliases conservatively
    /// require explicit backing whenever memory resources exist; do not search
    /// those resources to decide whether they cover this particular request.
    pub(in crate::kernel) fn has_no_explicit_memory_for_local_storage(
        &self,
        block: &AddressBase,
        assumptions: &PureFactContext,
    ) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.storage.index.memory_by_block.is_empty()
            || (self.storage.index.nonconcrete_memory_count == 0
                && !assumptions.has_address_base_aliases()
                && !self.storage.index.memory_by_block.contains_key(block))
    }

    /// The memory facts based in `block`, from the block index: the `owns`
    /// and `views` ranges a pointer formed in that block can lie in. SymbolicMemory
    /// in other blocks, composite, iterated, token and instance facts are
    /// never visited. Charges one work unit per fact. For
    /// `ExternalArgument`, the block every pointer parameter shares, this is
    /// every parameter's range.
    pub(in crate::kernel) fn memory_facts_in_block<'a>(
        &'a self,
        block: &AddressBase,
    ) -> impl Iterator<Item = &'a ResourceFact> + use<'a> {
        self.storage
            .index
            .memory_by_block
            .get(block)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.fact(*entry))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Owned memory at exactly one block, without visiting observations or
    /// suppliers based in other blocks. Selection does not infer aliases.
    pub(in crate::kernel) fn owned_memory_facts_in_block<'a>(
        &'a self,
        block: &AddressBase,
    ) -> impl Iterator<Item = &'a ResourceFact> + use<'a> {
        self.storage
            .index
            .owned_memory_by_block
            .get(block)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.fact(*entry))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// The iterated guarded-ownership facts whose element or guard cells lie
    /// in `block`, from the block index. Charges one work unit per fact.
    pub(in crate::kernel) fn iterated_facts_in_block<'a>(
        &'a self,
        block: &AddressBase,
    ) -> impl Iterator<Item = &'a ResourceFact> + use<'a> {
        self.storage
            .index
            .iterated_by_block
            .get(block)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .map(|entry| self.fact(*entry))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Select the unique owned occurrence with these exact clause coordinates.
    pub(in crate::kernel) fn owned_iterated_clause(
        &self,
        template: &IteratedMemory,
    ) -> Result<&ResourceFact, &'static str> {
        crate::instrumentation::record_deterministic_work(1);
        let entries = self
            .storage
            .index
            .owned_iterated_by_clause
            .get(template)
            .ok_or("the selected iterated ownership fact is not held; unfold its resource or select its saved arguments")?;
        if entries.len() != 1 {
            return Err("more than one owned iterated fact has the selected clause");
        }
        Ok(self.fact(*entries.last().expect("a singleton clause has an entry")))
    }

    /// Every iterated guarded-ownership fact held, each once, from the block
    /// index. Charges one work unit per fact visited.
    pub(in crate::kernel) fn iterated_facts(&self) -> Vec<ResourceFact> {
        let mut entries = BTreeSet::new();
        for (_, bucket) in self.storage.index.iterated_by_block.iter() {
            for entry in bucket.iter() {
                crate::instrumentation::record_deterministic_work(1);
                entries.insert(*entry);
            }
        }
        entries
            .into_iter()
            .map(|entry| self.fact(entry).clone())
            .collect()
    }

    /// Whether any iterated guarded-ownership fact is held.
    pub(in crate::kernel) fn has_iterated_facts(&self) -> bool {
        !self.storage.index.iterated_by_block.is_empty()
    }

    /// Necessary-shape candidates for proof-aware direct resource matching.
    /// MemoryState-insensitive matching cannot change an address base, resource
    /// family, composite/token name, or arity, so unrelated facts need not
    /// enter the expensive memory-resolution comparator.
    pub(in crate::kernel) fn direct_match_candidates(
        &self,
        fact: &ResourceFact,
    ) -> impl Iterator<Item = &ResourceFact> {
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
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<&ResourceFact> {
        if let Some(range) = required.memory_range() {
            return self.directly_supporting_memory_fact(required, range, assumptions);
        }
        self.direct_match_candidates_for(required, assumptions)
            .into_iter()
            .find(|available| resource_fact_entails(available, required, assumptions))
    }

    /// Check one indexed supplier and return its held representation. A failed
    /// alignment or entailment check does not enumerate alternative suppliers.
    fn directly_supporting_memory_fact(
        &self,
        required: &ResourceFact,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<&ResourceFact> {
        let candidates = self.memory_fact_candidates(range, required.is_own(), assumptions);
        let entry = candidates.entries.single_supplier()?;
        let aligned = candidates.requirement(entry, required)?;
        let available = self.fact(entry);
        // Geometry nominates a supplier; an empty or negative owner supplies
        // neither owned authority nor its read core.
        if available.is_own() && !available.has_proven_positive_quantity(assumptions) {
            return None;
        }
        resource_fact_entails(available, &aligned, assumptions).then_some(available)
    }

    /// Select token/composite candidates by shape and the first pointer's
    /// closed address class on published inputs. Raw compositions retain the
    /// structural-root view until their producer publishes them. Candidate
    /// selection grants no authority: the caller checks the full arguments.
    pub(in crate::kernel) fn direct_match_candidates_for(
        &self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Vec<&ResourceFact> {
        let (Resource::Composite { name, arguments } | Resource::Token { name, arguments }) =
            fact.resource()
        else {
            return self.direct_match_candidates(fact).collect();
        };
        let Some(pointer) = normalization_root_pointer(arguments) else {
            return self.direct_match_candidates(fact).collect();
        };
        let shape = (fact.family(), name.clone(), arguments.len());
        if let Some(found) = self.class_shape_candidates(fact, assumptions) {
            let mut entries = found
                .iter()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .copied()
                .collect::<BTreeSet<_>>();
            if let Some(unrooted) = self.storage.index.exact_shapes_by_root.get(&(
                shape.0,
                shape.1.clone(),
                shape.2,
                None,
            )) {
                entries.extend(unrooted.iter().copied());
            }
            return entries.into_iter().map(|entry| self.fact(entry)).collect();
        }
        let mut entries = BTreeSet::new();
        let roots = std::iter::once(None).chain(
            related_pointer_roots(pointer, assumptions)
                .into_iter()
                .map(Some),
        );
        for root in roots {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(found) = self.storage.index.exact_shapes_by_root.get(&(
                shape.0,
                shape.1.clone(),
                shape.2,
                root,
            )) {
                entries.extend(found.iter().copied());
            }
        }
        entries.into_iter().map(|entry| self.fact(entry)).collect()
    }

    /// Select a deterministic owned candidate from the pointer index. Multiple
    /// returned sibling shares are legitimate. This lookup grants no authority:
    /// callers must still check the selected borrow, initialization, and type.
    pub(crate) fn mutex_use_candidate_at(&self, pointer: &Address) -> Option<&ResourceFact> {
        let entries = self
            .storage
            .index
            .mutex_authorities
            .get(&(ResourceFamily::MutexUse, pointer.clone()))?;
        let fact = self.fact(*entries.iter().next()?);
        matches!(fact, ResourceFact::Own(_, q) if q.as_const() == Some(1)).then_some(fact)
    }

    #[cfg(test)]
    pub(crate) fn mutex_use_at(&self, pointer: &Address) -> Option<&ResourceFact> {
        let entries = self
            .storage
            .index
            .mutex_authorities
            .get(&(ResourceFamily::MutexUse, pointer.clone()))?;
        if entries.len() != 1 {
            return None;
        }
        let fact = self.fact(*entries.iter().next()?);
        matches!(fact, ResourceFact::Own(_, q) if q.as_const() == Some(1)).then_some(fact)
    }

    pub(crate) fn mutex_live_at(&self, pointer: &Address) -> Option<&ResourceFact> {
        let entries = self
            .storage
            .index
            .mutex_authorities
            .get(&(ResourceFamily::MutexLive, pointer.clone()))?;
        if entries.len() != 1 {
            return None;
        }
        let fact = self.fact(*entries.iter().next()?);
        matches!(fact, ResourceFact::Own(_, q) if q.as_const() == Some(1)).then_some(fact)
    }

    /// The owned publication right of `side` for the flag at `pointer`, found
    /// through the authority index rather than a scan of the context.
    pub(crate) fn publication_right_at(
        &self,
        side: super::PublicationSide,
        pointer: &Address,
    ) -> Option<&ResourceFact> {
        let entries = self
            .storage
            .index
            .mutex_authorities
            .get(&(ResourceFamily::Publication, pointer.clone()))?;
        let mut owned = entries
            .iter()
            .map(|entry| self.fact(*entry))
            .filter(|fact| {
                matches!(fact, ResourceFact::Own(Resource::Publication(right), q)
                if right.side == side && q.as_const() == Some(1))
            });
        let fact = owned.next()?;
        owned.next().is_none().then_some(fact)
    }

    /// The subscriber rights read by an acquire load whose value no C branch
    /// has decided yet, found through their own index.
    pub(crate) fn has_observed_publication_rights(&self) -> bool {
        self.storage
            .index
            .observed_publications
            .get(&())
            .is_some_and(|entries| !entries.is_empty())
    }

    pub(crate) fn observed_publication_rights(&self) -> Vec<ResourceFact> {
        self.storage
            .index
            .observed_publications
            .get(&())
            .map(|entries| {
                entries
                    .iter()
                    .map(|entry| self.fact(*entry).clone())
                    .collect()
            })
            .unwrap_or_default()
    }

    pub(crate) fn mutex_guard_at(&self, pointer: &Address) -> Option<&ResourceFact> {
        let entries = self
            .storage
            .index
            .mutex_authorities
            .get(&(ResourceFamily::MutexGuard, pointer.clone()))?;
        if entries.len() != 1 {
            return None;
        }
        let fact = self.fact(*entries.iter().next()?);
        matches!(fact, ResourceFact::Own(_, q) if q.as_const() == Some(1)).then_some(fact)
    }

    /// Select one actual occurrence, retaining a projection's own identity.
    /// Descent belongs to that witness, not to its equal resource term.
    pub(crate) fn structural_witness_occurrence(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceOccurrenceId> {
        crate::instrumentation::record_deterministic_work(1);
        let owner = required
            .is_view()
            .then(|| ResourceFact::own(required.resource().clone()));
        let exact = self.storage.index.exact.get(required).or_else(|| {
            owner
                .as_ref()
                .and_then(|owned| self.storage.index.exact.get(owned))
        });
        let entry = if let Some(entries) = exact {
            if entries.len() != 1 {
                return None;
            }
            *entries.iter().next()?
        } else {
            let entries = self.class_shape_candidates(required, assumptions)?;
            if entries.len() != 1 {
                return None;
            }
            *entries.iter().next()?
        };
        resource_fact_entails(self.fact(entry), required, assumptions)
            .then(|| self.occurrence(entry))
    }

    pub(crate) fn structural_fact_at_occurrence(
        &self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<&ResourceFact> {
        self.storage
            .entry_by_occurrence
            .get(&occurrence)
            .map(|entry| self.fact(*entry))
    }

    /// Select an exact owned occurrence for a fact-only API. Equal owned
    /// facts are distinct authorities, so callers that need to attach a
    /// projection must reject an ambiguous value-only lookup.
    pub(crate) fn unique_owned_occurrence_for_fact(
        &self,
        required: &ResourceFact,
    ) -> Option<(ResourceOccurrenceId, &ResourceFact)> {
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

    /// Drops the memory views published from one owned occurrence, leaving
    /// the owner and every other observation of it. A loop head uses this
    /// before deriving the owner's read authority again over the head's
    /// memory. One indexed lookup; the work is the owner's own projections.
    pub(crate) fn without_memory_views_supported_by_occurrence(
        mut self,
        support: ResourceOccurrenceId,
    ) -> Self {
        let projections = self
            .storage
            .projections_by_support_occurrence
            .get(&support)
            .cloned()
            .unwrap_or_default();
        for entry in projections.iter().copied() {
            if self
                .storage
                .facts
                .get(&entry)
                .is_some_and(|fact| fact.memory_view_range().is_some())
            {
                self.remove_entry(entry);
            }
        }
        self
    }

    pub(crate) fn owned_occurrences_for_fact(
        &self,
        required: &ResourceFact,
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

    /// Select one actual written occurrence without enumerating equal heads.
    pub(crate) fn first_exact_occurrence(
        &self,
        fact: &ResourceFact,
    ) -> Option<ResourceOccurrenceId> {
        let entry = self.storage.index.exact.get(fact)?.iter().next()?;
        Some(self.occurrence(*entry))
    }

    /// Return every exact occurrence for a representation, including viewed
    /// entries.  TrackedResource rewrites use this only after inserting the exact
    /// child representation, so the caller can attach a dependency to the
    /// returned opaque occurrence rather than guessing by value.
    pub(crate) fn occurrences_for_fact(
        &self,
        required: &ResourceFact,
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
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<(ResourceOccurrenceId, &ResourceFact)> {
        self.directly_supporting_owned_entry_with_separation(required, assumptions, true)
    }

    pub(crate) fn directly_supporting_owned_entry_ignoring_separation(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<(ResourceOccurrenceId, &ResourceFact)> {
        self.directly_supporting_owned_entry_with_separation(required, assumptions, false)
    }

    fn directly_supporting_owned_entry_with_separation(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
        use_separation: bool,
    ) -> Option<(ResourceOccurrenceId, &ResourceFact)> {
        if let Some(range) = required.memory_range() {
            let candidates = self.memory_fact_candidates(range, true, assumptions);
            if let Some(entry) = candidates.entries.single_supplier() {
                let candidate = self.fact(entry);
                if candidate.is_own()
                    && candidate.has_proven_positive_quantity(assumptions)
                    && let Some(aligned) = candidates.requirement(entry, required)
                    && Self::memory_support_entails(
                        candidate,
                        &aligned,
                        assumptions,
                        use_separation,
                    )
                {
                    return Some((self.occurrence(entry), candidate));
                }
                // A nominated owner's failed check is final, not a reason
                // to try another owner or a projection of one.
                return None;
            }
            if required.is_view() && !self.storage.supported_by.is_empty() {
                let projections = self.memory_fact_candidates(range, false, assumptions);
                let entry = projections.entries.single_supplier()?;
                let support_occurrence =
                    *self.storage.support_occurrence_by_projection.get(&entry)?;
                let support = self.owned_fact_for_occurrence(support_occurrence)?;
                if self.storage.supported_by.get(&entry) != Some(support)
                    || !support.has_proven_positive_quantity(assumptions)
                {
                    return None;
                }
                let aligned = projections.requirement(entry, required)?;
                if Self::memory_support_entails(
                    self.fact(entry),
                    &aligned,
                    assumptions,
                    use_separation,
                ) {
                    return Some((support_occurrence, support));
                }
            }
            return None;
        }
        self.direct_nonmemory_support_entry(required, assumptions)
    }

    /// Exact facts nominate one occurrence directly. Otherwise only a
    /// singleton resource/address/shape bucket may nominate an occurrence;
    /// a failed candidate never starts a search through alternative owners.
    fn direct_nonmemory_support_entry(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<(ResourceOccurrenceId, &ResourceFact)> {
        crate::instrumentation::record_deterministic_work(1);
        let singleton = |entries: &ResourceEntryIds| {
            (entries.len() == 1).then(|| *entries.iter().next().expect("singleton entry"))
        };
        let unit_owner = required
            .is_view()
            .then(|| ResourceFact::own(required.resource().clone()));
        let unit_owner_entries = unit_owner
            .as_ref()
            .and_then(|owner| self.storage.index.exact.get(owner));
        let entry = if let Some(entries) = self.storage.nonmemory_projections_by_fact.get(required)
        {
            *entries.iter().next()?
        } else if let Some(entries) = unit_owner_entries {
            // An exact unit owner supplies this exact resource's view.
            *entries.iter().next()?
        } else if let Some(entries) = self.storage.index.exact.get(required) {
            // Equal facts are indexed witnesses. Choosing one retains that
            // occurrence's own support, rather than merging their authority.
            *entries.iter().next()?
        } else if let Some(entries) = self.storage.index.by_resource.get(required.resource()) {
            singleton(entries)?
        } else if let Some(entries) = self.class_shape_candidates(required, assumptions) {
            singleton(&entries)?
        } else {
            singleton(self.direct_match_candidate_positions(required)?)?
        };
        let candidate = self.fact(entry);
        if !resource_fact_entails(candidate, required, assumptions) {
            return None;
        }
        if candidate.is_own() {
            return Some((self.occurrence(entry), candidate));
        }
        let support = self.storage.supported_by.get(&entry)?;
        let occurrence = *self.storage.support_occurrence_by_projection.get(&entry)?;
        (support.is_own() && self.owned_fact_for_occurrence(occurrence) == Some(support))
            .then_some((occurrence, support))
    }

    fn memory_support_entails(
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
        use_separation: bool,
    ) -> bool {
        if !use_separation
            && let (Some(available), Some(required)) = (
                resource_fact_read_core_range(available),
                required.memory_view_range(),
            )
        {
            (!required.typed_carrier
                || assumptions.access_provenance_matches_range(
                    required.access_provenance(),
                    required,
                    &available,
                ))
                && memory_range_covers_by_routes(&available, required, assumptions)
        } else {
            resource_fact_entails(available, required, assumptions)
        }
    }

    pub(crate) fn owned_fact_for_occurrence(
        &self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<&ResourceFact> {
        let entry = self.storage.entry_by_occurrence.get(&occurrence)?;
        let fact = self.storage.facts.get(entry)?;
        fact.is_own().then_some(fact)
    }

    /// The view fact a live occurrence holds, for a caller that already has
    /// the occurrence from an indexed lookup.
    pub(crate) fn view_fact_for_occurrence(
        &self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<&ResourceFact> {
        let entry = self.storage.entry_by_occurrence.get(&occurrence)?;
        let fact = self.storage.facts.get(entry)?;
        fact.is_view().then_some(fact)
    }

    /// An already exposed child may be represented by one live occurrence
    /// or by exact adjacent fragments. Read that partition in place. A
    /// covering owner that extends outside the child is not an exact match.
    pub(in crate::kernel) fn covers_exact_owned_piece(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        if !required.is_own() {
            return false;
        }
        if let Some(range) = required.memory_own_range()
            && (memory_range_is_proven_empty(range, assumptions)
                || required.owned_quantity_term().is_some_and(|quantity| {
                    resource_quantity_resolves_to_zero(quantity, assumptions)
                }))
        {
            return true;
        }
        if let Some((_, available)) = self.directly_supporting_owned_entry(required, assumptions) {
            return match (required.memory_own_range(), available.memory_own_range()) {
                (Some(required), Some(available)) => {
                    memory_range_covers(required, available, assumptions)
                }
                (None, None) => resource_fact_entails(required, available, assumptions),
                _ => false,
            };
        }
        required.owned_quantity() == Some(1)
            && (self
                .exact_owned_fragment_cover(required, assumptions)
                .is_some()
                || required.memory_own_range().is_some_and(|range| {
                    (range.has_symbolic_bounds() || range.wide_bounds().is_some())
                        && self
                            .walk_symbolic_owned_partition(required, assumptions, |_, _| Some(()))
                            .is_some()
                }))
    }

    fn exact_owned_fragment_cover(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<()> {
        if required.owned_quantity()? != 1 {
            return None;
        }
        let range = required.memory_own_range()?;
        let (start, end) = constant_relative_byte_endpoints(range);
        let length = i64::try_from(end?.checked_sub(start?)?).ok()?;
        if length <= 0 {
            return None;
        }
        let start = range.start_pointer();
        let mut cursor = 0i64;
        while cursor < length {
            crate::instrumentation::record_deterministic_work(1);
            let point = start.with_offset(AddressOffset::add(
                start.offset.clone(),
                AddressOffset::constant(cursor),
            ));
            let selected = self.write_access(&point, 1, assumptions)?;
            let owner = self.fact(selected.entry());
            let piece = owner.memory_own_range()?;
            let address = selected.address()?;
            if !owner.has_proven_positive_quantity(assumptions)
                || !assumptions.pointers_known_equal(&address, &piece.start_pointer())
                || (range.typed_carrier
                    && !assumptions.access_provenance_matches_range(
                        range.access_provenance(),
                        range,
                        piece,
                    ))
            {
                return None;
            }
            let (lo, hi) = constant_relative_byte_endpoints(piece);
            let bytes = i64::try_from(hi?.checked_sub(lo?)?).ok()?;
            if bytes <= 0 {
                return None;
            }
            cursor = cursor.checked_add(bytes)?;
        }
        (cursor == length).then_some(())
    }

    /// Reserve a constant-length owned footprint from its live byte fragments. Each
    /// step checks and consumes the actual indexed occurrence; a view, gap,
    /// stale occurrence, or unsupported coordinate proves no ownership. The
    /// returned support retains every supplier rather than inventing a
    /// single owner for the joined range. Work follows the consumed fragments,
    /// with logarithmic queries and edits, not unrelated memory in the block.
    #[cfg(test)]
    pub(crate) fn reserve_owned_memory_fragments(
        self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<(Self, Vec<ResourceOccurrenceId>)> {
        self.reserve_owned_memory_fragments_impl(required, assumptions, None, false)
    }

    /// Speculative reservation returns its origins only on success. The caller
    /// can discard this result without changing its retained origin map.
    pub(crate) fn reserve_owned_memory_fragments_with_origins(
        self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
        origins: &MemorySplitOrigins,
    ) -> Option<(Self, Vec<ResourceOccurrenceId>, MemorySplitOrigins)> {
        let mut next_origins = origins.clone();
        let (next, supports) = self.reserve_owned_memory_fragments_impl(
            required,
            assumptions,
            Some(&mut next_origins),
            false,
        )?;
        Some((next, supports, next_origins))
    }

    /// A whole object of a symbolic layout reserved from its pieces: the
    /// object held with holes and, for each hole, that whole field. By the
    /// layout's rule the field fills its hole and no other field's bytes, so
    /// together they are the object, as `symbolic_object_with_field` joins
    /// them. The pieces are found by their `SymbolicField` keys, one index
    /// lookup per field of the layout.
    fn reserve_symbolic_object_from_pieces(
        mut self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<(Self, Vec<ResourceOccurrenceId>)> {
        let range = required.memory_own_range()?;
        let layout = range.symbolic_object()?;
        if range.has_holes() || required.owned_quantity()? != 1 {
            return None;
        }
        let base = range.base().clone();
        let mut object = None;
        let mut fields = BTreeMap::new();
        for field in 0..layout.field_count() {
            crate::instrumentation::record_deterministic_work(1);
            let key = (
                ResourceNormalizationKey::SymbolicField(base.clone(), layout, field, true),
                true,
            );
            let Some(entries) = self.storage.index.written_normalization.entries.get(&key) else {
                continue;
            };
            for &entry in entries.iter() {
                let fact = self.fact(entry);
                let Some(available) = fact.memory_own_range() else {
                    continue;
                };
                if !fact.is_own() || !fact.has_proven_positive_quantity(assumptions) {
                    continue;
                }
                if available.symbolic_object() == Some(layout)
                    && available.base() == &base
                    && available.holes().contains(&field)
                {
                    object.get_or_insert(entry);
                } else if available.symbolic_field() == Some((base.clone(), layout, field)) {
                    fields.entry(field).or_insert(entry);
                }
            }
        }
        let object = object?;
        let mut joined = self.fact(object).memory_own_range()?.clone();
        let holes = joined.holes().to_vec();
        let mut pieces = vec![object];
        for hole in &holes {
            let field = *fields.get(hole)?;
            joined = symbolic_object_with_field(
                &joined,
                self.fact(field).memory_own_range()?,
                assumptions,
            )?;
            pieces.push(field);
        }
        if holes.is_empty() || !symbolic_object_covers_object(&joined, range) {
            return None;
        }
        let supports = pieces.iter().map(|entry| self.occurrence(*entry)).collect();
        for entry in pieces {
            self.remove_entry(entry);
        }
        Some((self, supports))
    }

    fn reserve_owned_memory_fragments_impl(
        mut self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
        mut origins: Option<&mut MemorySplitOrigins>,
        establish_requested_carrier: bool,
    ) -> Option<(Self, Vec<ResourceOccurrenceId>)> {
        if required.owned_quantity()? != 1 {
            return None;
        }
        if required
            .memory_own_range()
            .is_some_and(|range| range.symbolic_object().is_some())
        {
            return self.reserve_symbolic_object_from_pieces(required, assumptions);
        }
        let range = required.memory_own_range()?;
        let end = match range.wide_bounds() {
            Some((start, end)) => i64::try_from(
                end.uint64_as_const()?
                    .checked_sub(start.uint64_as_const()?)?
                    .checked_mul(u64::from(range.element_width()))?,
            )
            .ok()?,
            None => range
                .signed_constant_end()?
                .checked_sub(range.signed_constant_start()?)?
                .checked_mul(i64::from(range.element_width()))?,
        };
        if end <= 0 {
            return None;
        }
        let start = range.start_pointer();
        let mut cursor = 0i64;
        let mut supports = Vec::new();
        while cursor < end {
            let pointer = start.with_offset(AddressOffset::add(
                start.offset.clone(),
                AddressOffset::constant(cursor),
            ));
            let entries = self.write_access(&pointer, 1, assumptions)?;
            let entry = entries.entry();
            crate::instrumentation::record_deterministic_work(1);
            let candidate = self.fact(entry);
            // An index nominates geometry, not authority. The former candidate
            // iterator filtered quantities; indexed selection must check its
            // chosen supplier before consuming any piece.
            if !candidate.has_proven_positive_quantity(assumptions) {
                return None;
            }
            let available = candidate.memory_own_range()?;
            // A query must establish the requested carrier on every piece.
            // Narrow byte transfers instead retain their suppliers' carriers;
            // native transfers already require matching typed provenances.
            if (establish_requested_carrier || range.wide_bounds().is_some())
                && range.typed_carrier
                && !assumptions.access_provenance_matches_range(
                    range.access_provenance(),
                    range,
                    available,
                )
            {
                return None;
            }
            let base = entries.address()?;
            let (bytes, piece) = if let Some((available_start, available_end)) =
                available.wide_bounds()
            {
                // Keep native suppliers in their original coordinates. Only
                // concrete, aligned pieces are consumed; never narrow a bound.
                let point = MemoryRange::new_with_element_width(
                    base,
                    0u32.into(),
                    1u32.into(),
                    available.element_width(),
                );
                let at = u64::try_from(exact_constant_base_delta(
                    available,
                    &point,
                    Some(assumptions),
                )?)
                .ok()?;
                // After the first piece, compose only exact adjacency; a
                // covering supplier may overlap bytes already consumed.
                if cursor > 0 && at != available_start.uint64_as_const()? {
                    return None;
                }
                let width = u64::from(available.element_width());
                let bytes = available_end
                    .uint64_as_const()?
                    .checked_sub(at)?
                    .checked_mul(width)?
                    .min(u64::try_from(end - cursor).ok()?);
                if bytes == 0 || bytes % width != 0 {
                    return None;
                }
                let piece = ResourceFact::own_memory(
                    MemoryRange::new_wide(
                        available.base().clone(),
                        OldMachineTerm::uint64_constant(at),
                        OldMachineTerm::uint64_constant(at.checked_add(bytes / width)?),
                        available.element_width(),
                    )
                    .with_carrier_of(available),
                );
                (i64::try_from(bytes).ok()?, piece)
            } else {
                let point =
                    MemoryRange::new_with_element_width(base.clone(), 0u32.into(), 1u32.into(), 1);
                let byte_available = byte_normalized_memory_range(available);
                let at = exact_constant_base_delta(&byte_available, &point, Some(assumptions))?;
                if cursor > 0 && at != byte_available.signed_constant_start()? {
                    return None;
                }
                let available_end = byte_available.signed_constant_end()?;
                let bytes = available_end
                    .checked_sub(at)
                    .map(|bytes| bytes.min(end - cursor))
                    .filter(|bytes| *bytes > 0)
                    .and_then(|bytes| u32::try_from(bytes).ok())?;
                let piece = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    base,
                    0u32.into(),
                    bytes.into(),
                    1,
                ));
                (i64::from(bytes), piece)
            };
            if !resource_fact_entails(candidate, &piece, assumptions) {
                return None;
            }
            let support = self.occurrence(entry);
            if !self.consume_fact_from_candidates_with_origins(
                &piece,
                assumptions,
                [entry],
                origins.as_deref_mut(),
            ) {
                return None;
            }
            supports.push(support);
            cursor = cursor.checked_add(bytes)?;
        }
        Some((self, supports))
    }

    /// One indexed observation witness for refusal classification and the
    /// borrow coalescing prepass. This grants no borrow authority and does not
    /// search another candidate if the nominated entry is unsuitable.
    pub(crate) fn has_indexed_view_witness(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        self.indexed_view_witness(required, assumptions).is_some()
    }

    pub(crate) fn indexed_view_witness(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceOccurrenceId> {
        if !required.is_view() || self.storage.index.owned_count == self.storage.facts.len() {
            return None;
        }
        if let Some(entries) = self.storage.index.exact.get(required) {
            return entries
                .owned_values()
                .next()
                .map(|entry| self.occurrence(entry));
        }
        let range = required.memory_view_range()?;
        let candidates = self.memory_fact_candidates(range, false, assumptions);
        let entry = candidates.entries.single_supplier()?;
        let available = self.fact(entry);
        (available.is_view()
            && candidates
                .requirement(entry, required)
                .is_some_and(|aligned| resource_fact_entails(available, &aligned, assumptions)))
        .then(|| self.occurrence(entry))
    }

    /// Resolve an authored input against the checked partition. An exact
    /// principal occurrence wins over other views covering the same bytes.
    /// After normalization a single covering principal may represent several
    /// clauses, in which case they install one borrow for that occurrence.
    pub(crate) fn principal_input_view_occurrence(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceOccurrenceId> {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(entries) = self.storage.index.exact.get(required)
            && entries.len() == 1
            && let Some(entry) = entries.iter().next()
        {
            let occurrence = self.occurrence(*entry);
            if self.view_occurrence_is_principal(occurrence) {
                return Some(occurrence);
            }
        }
        let candidates = self.view_occurrences_for_fact(required, assumptions);
        let mut principals = candidates
            .into_iter()
            .filter(|occurrence| self.view_occurrence_is_principal(*occurrence));
        let occurrence = principals.next()?;
        principals.next().is_none().then_some(occurrence)
    }

    /// Return indexed view occurrences that entail `required`. The caller
    /// resolves each occurrence through an explicit checked-state binding;
    /// this method never searches the borrow ledger or unrelated frame entries.
    pub(crate) fn view_occurrences_for_fact(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Vec<ResourceOccurrenceId> {
        // With no viewed facts there is no possible view occurrence. Avoid
        // resolving the query's pointer history or pairing an ownership-only
        // input with a memory index just to discover this empty result.
        if self.storage.index.owned_count == self.storage.facts.len() {
            return Vec::new();
        }
        if let Some(range) = required.memory_view_range() {
            // Select the same indexed, alias-aligned frontier as memory
            // ownership. A loop cursor can name a subrange through a checked
            // offset equality without sharing the source's pointer spelling.
            let candidates = self.memory_fact_candidates(range, false, assumptions);

            return candidates
                .entries
                .iter()
                .filter_map(|entry| {
                    let candidate = self.fact(entry);
                    if !candidate.is_view() {
                        return None;
                    }
                    let aligned = candidates.requirement(entry, required)?;
                    resource_fact_entails(candidate, &aligned, assumptions)
                        .then_some(self.occurrence(entry))
                })
                .collect();
        }
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
        fact: &ResourceFact,
        support_occurrence: ResourceOccurrenceId,
        support: &ResourceFact,
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
    /// is invalidated. Support decisions therefore use this record instead
    /// of asking whether some owner in the frame happens to satisfy the fact:
    /// an equal owner is not the owner a projection came from, and a view
    /// justified by equality alone would survive that owner's consumption.
    pub(crate) fn exact_projection_support(
        &self,
        fact: &ResourceFact,
    ) -> Option<(ResourceOccurrenceId, &ResourceFact)> {
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

    /// Resolve an already selected diagnostic view to a unique exact occurrence.
    pub(crate) fn exact_diagnostic_view(
        &self,
        view: &ResourceFact,
    ) -> Option<ResourceOccurrenceId> {
        crate::instrumentation::record_deterministic_work(1);
        let entries = self.storage.index.exact.get(view)?;
        (view.is_view() && entries.len() == 1)
            .then(|| self.occurrence(*entries.iter().next().expect("singleton view bucket")))
    }

    /// The live owned support a projected view occurrence was published
    /// from, when `occurrence` is such a projection. A projection carries no
    /// borrow of its own: its authority is the exact owned occurrence it is
    /// indexed under, so a read it covers is a read of that owner's memory.
    /// Answered by the occurrence's own entry, without scanning the frame.
    pub(crate) fn owned_projection_support(
        &self,
        occurrence: ResourceOccurrenceId,
    ) -> Option<(ResourceOccurrenceId, &ResourceFact)> {
        let entry = self.storage.entry_by_occurrence.get(&occurrence)?;
        let support = self.storage.supported_by.get(entry)?;
        let support_occurrence = *self.storage.support_occurrence_by_projection.get(entry)?;
        (support.is_own()
            && self
                .storage
                .entry_by_occurrence
                .get(&support_occurrence)
                .is_some_and(|support_entry| {
                    self.storage.facts.get(support_entry) == Some(support)
                }))
        .then_some((support_occurrence, support))
    }

    /// Validate every projection indexed under one exact support occurrence.
    /// The reverse index bounds this check by the affected support rather than
    /// scanning unrelated resources in the frame.
    pub(crate) fn support_occurrence_is_live(
        &self,
        support_occurrence: ResourceOccurrenceId,
        support: &ResourceFact,
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
    pub(crate) fn invalidate_memory_support(
        mut self,
        before: &SymbolicMemory,
        after: &SymbolicMemory,
    ) -> Self {
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
        let before_node = crate::kernel::intern_memory_ref(before);
        let mut current = crate::kernel::intern_memory_ref(after);
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
            // A history barrier (for example an interface join) has no
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

    /// Drops every iterated guarded-ownership fact whose guard cells a memory
    /// transition may have written outside the store rule.
    ///
    /// A C store reaches here only after `plan_iterated_guard_store` made the
    /// stored index a hole of every fact whose guard cells it names, so a
    /// store is kept exactly when its structural index is a hole. A call's
    /// havoc, a free, or an ended lifetime touching a guard or element block
    /// could change what a fact claims without that rule, so the fact is
    /// dropped: losing ownership is sound, keeping a stale claim is not. A
    /// loop-head havoc is a generalization over the visits the invariants
    /// describe, not a write, so it keeps the fact; the loop rule frames out
    /// a fact its body does not hold (`loops.rs`). The walk visits the
    /// derivation steps between the two states and, per step, only the
    /// facts filed under the written block.
    pub(crate) fn invalidate_iterated_facts(
        self,
        before: &SymbolicMemory,
        after: &SymbolicMemory,
        stores_checked: bool,
    ) -> Self {
        if !self.has_iterated_facts() || before.diagnostic_identity() == after.diagnostic_identity()
        {
            return self;
        }
        // The two states differ only in cells written on the derivation
        // paths from their nearest common ancestor. Interning is first-wins
        // on equal content, so `after` may carry the recorded history of an
        // earlier, content-equal state that never passed through `before`;
        // walking `after` alone would then visit stores that are not this
        // transition's and miss the ones on `before`'s side. Arena ids
        // strictly decrease along a derivation, so stepping whichever side
        // is younger meets the common ancestor. A store that leaves the cell
        // holding the same value in both states changes nothing either
        // side reads.
        let mut before_side = crate::kernel::intern_memory_ref(before);
        let mut after_side = crate::kernel::intern_memory_ref(after);
        let unchanged_cell = |pointer: &Address| {
            matches!(
                (before.cells.get(pointer), after.cells.get(pointer)),
                (Some(left), Some(right)) if left == right
            )
        };
        let mut dropped = Vec::<ResourceFact>::new();
        let facts_in_block = |context: &Self, block: &AddressBase| {
            if memory_block_may_alias(block) {
                context
                    .storage
                    .index
                    .iterated_by_block
                    .iter()
                    .flat_map(|(_, entries)| entries.iter())
                    .map(|entry| context.fact(*entry).clone())
                    .collect::<Vec<_>>()
            } else {
                context
                    .iterated_facts_in_block(block)
                    .cloned()
                    .collect::<Vec<_>>()
            }
        };
        while before_side != after_side {
            crate::instrumentation::record_deterministic_work(1);
            let step_after = after_side.arena_id().1 > before_side.arena_id().1;
            let current = if step_after {
                &after_side
            } else {
                &before_side
            };
            let Some(derivation) = current.derivation() else {
                break;
            };
            // A seeded run is the stores it stands for, each judged as one.
            let seeded = derivation.seeded_stores();
            let stores: Vec<(&Address, &ProgramValue)> = match (&*derivation, &seeded) {
                (MemoryDerivation::Store { pointer, value, .. }, _) => {
                    vec![(pointer, value.native())]
                }
                (MemoryDerivation::CellsSeeded { .. }, Some(stores)) => stores
                    .iter()
                    .map(|(pointer, value)| (pointer, value))
                    .collect(),
                _ => Vec::new(),
            };
            match &*derivation {
                MemoryDerivation::Store { .. } | MemoryDerivation::CellsSeeded { .. }
                    if stores_checked => {}
                MemoryDerivation::Store { .. } | MemoryDerivation::CellsSeeded { .. } => {
                    for (pointer, value) in stores {
                        if unchanged_cell(pointer) {
                            continue;
                        }
                        for fact in facts_in_block(&self, &pointer.base) {
                            let Resource::Iterated(iterated) = fact.resource() else {
                                continue;
                            };
                            let guard = iterated.guard();
                            // A store that did not pass the store rule keeps the
                            // fact only when it provably misses the guard cells.
                            let keeps = pointer.base.proven_distinct(&guard.base.base)
                                || (pointer.base == guard.base.base
                                    && value.byte_width() == guard.cell_width
                                    && pointer
                                        .shared_element_index_from_base_with_width(
                                            &guard.base,
                                            guard.cell_width,
                                        )
                                        .is_some_and(|index| {
                                            iterated.holes().iter().any(|hole| {
                                                hole.operand_view()
                                                    .retain(MachineIntegerType::Int32)
                                                    == index
                                            })
                                        }));
                            if !keeps {
                                dropped.push(fact);
                            }
                        }
                    }
                }
                MemoryDerivation::RepresentationWrite { pointer, .. } => {
                    // There is no corresponding whole-cell store fact to
                    // establish a guarded iteration survived this write.
                    dropped.extend(facts_in_block(&self, &pointer.base));
                }
                MemoryDerivation::CallHavoc { mutable_ranges, .. } => {
                    for range in mutable_ranges {
                        for fact in facts_in_block(&self, &range.base().base) {
                            if let Resource::Iterated(iterated) = fact.resource()
                                && (iterated.guard().base.base == range.base().base
                                    || memory_block_may_alias(&range.base().base))
                            {
                                dropped.push(fact);
                            }
                        }
                    }
                }
                MemoryDerivation::HeapFreed {
                    allocation_base, ..
                }
                | MemoryDerivation::ContractAllocationRetired {
                    allocation_base, ..
                } => dropped.extend(facts_in_block(&self, &allocation_base.base)),
                MemoryDerivation::LocalLifetimeEnded { block, .. } => {
                    dropped.extend(facts_in_block(&self, block));
                }
                MemoryDerivation::BranchJoin { .. }
                | MemoryDerivation::LoopHavoc { .. }
                | MemoryDerivation::BlockDeclared { .. }
                | MemoryDerivation::HeapAllocated { .. }
                | MemoryDerivation::HeapAllocationPending { .. }
                | MemoryDerivation::HeapAllocationFailed { .. }
                | MemoryDerivation::ContractAllocationClaimsChanged { .. }
                | MemoryDerivation::ObjectInitializationRecorded { .. }
                | MemoryDerivation::CellObserved { .. }
                | MemoryDerivation::CellsForgotten { .. } => {}
            }
            let base = derivation.base().clone();
            if step_after {
                after_side = base;
            } else {
                before_side = base;
            }
        }
        let mut context = self;
        for fact in dropped {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(next) = context.clone().without_exact_representation(&fact) {
                context = next;
            }
        }
        context
    }

    fn entries_affected_by_memory_derivation(
        &self,
        derivation: &MemoryDerivation,
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
            MemoryDerivation::BranchJoin { .. } => true,
            MemoryDerivation::Store { pointer, .. }
            | MemoryDerivation::RepresentationWrite { pointer, .. } => {
                memory_block_may_alias(&pointer.base)
            }
            MemoryDerivation::CellsSeeded { run, .. } => memory_block_may_alias(&run.base().base),
            MemoryDerivation::CallHavoc { mutable_ranges, .. }
            | MemoryDerivation::LoopHavoc {
                mutable_ranges: Some(mutable_ranges),
                ..
            } => mutable_ranges
                .iter()
                .any(|range| memory_block_may_alias(&range.base().base)),
            MemoryDerivation::HeapFreed {
                allocation_base, ..
            }
            | MemoryDerivation::ContractAllocationRetired {
                allocation_base, ..
            }
            | MemoryDerivation::HeapAllocationPending {
                allocation_base, ..
            } => memory_block_may_alias(&allocation_base.base),
            MemoryDerivation::LocalLifetimeEnded { block, .. } => memory_block_may_alias(block),
            MemoryDerivation::LoopHavoc {
                mutable_ranges: None,
                ..
            }
            | MemoryDerivation::BlockDeclared { .. }
            | MemoryDerivation::HeapAllocated { .. }
            | MemoryDerivation::HeapAllocationFailed { .. }
            | MemoryDerivation::ContractAllocationClaimsChanged { .. }
            | MemoryDerivation::ObjectInitializationRecorded { .. }
            | MemoryDerivation::CellObserved { .. }
            | MemoryDerivation::CellsForgotten { .. } => false,
        };
        if ambiguous_event {
            for occurrence in self.storage.support_metadata_by_projection.keys() {
                crate::instrumentation::record_deterministic_work(1);
                entries = entries.with_value(*occurrence);
            }
        }
        match derivation {
            MemoryDerivation::Store { .. }
            | MemoryDerivation::RepresentationWrite { .. }
            | MemoryDerivation::CellsSeeded { .. } => {
                let stores = if let Some((pointer, width)) = derivation.single_write() {
                    vec![(pointer.clone(), width)]
                } else {
                    derivation
                        .seeded_stores()
                        .expect("a CellsSeeded edge")
                        .into_iter()
                        .map(|(pointer, value)| (pointer, value.byte_width()))
                        .collect()
                };
                for (pointer, width) in stores {
                    let write = MemoryRange::new_with_element_width(
                        pointer.clone(),
                        OldMachineTerm::constant(0),
                        OldMachineTerm::constant(1),
                        width,
                    );
                    if memory_interval_nodes(&write).is_some() {
                        add_memory_interval_candidates(
                            &self.storage.projections_by_memory_interval,
                            &self.storage.projections_by_memory_interval_subtree,
                            &write,
                            &mut entries,
                        );
                    } else if let Some(bucket) =
                        self.storage.projections_by_memory_block.get(&pointer.base)
                    {
                        for occurrence in bucket.iter() {
                            entries = entries.with_value(*occurrence);
                        }
                    }
                }
            }
            MemoryDerivation::CallHavoc { mutable_ranges, .. }
            | MemoryDerivation::LoopHavoc {
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
                        .get(&range.base().base)
                    {
                        for occurrence in bucket.iter() {
                            entries = entries.with_value(*occurrence);
                        }
                    }
                }
            }
            MemoryDerivation::HeapFreed {
                allocation_base,
                bytes,
                ..
            }
            | MemoryDerivation::ContractAllocationRetired {
                allocation_base,
                bytes,
                ..
            } => {
                if let Some(byte_count) = bytes.as_const() {
                    let freed = MemoryRange::new_with_element_width(
                        allocation_base.clone(),
                        OldMachineTerm::constant(0),
                        OldMachineTerm::constant(byte_count),
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
                    .get(&allocation_base.base)
                {
                    for occurrence in bucket.iter() {
                        entries = entries.with_value(*occurrence);
                    }
                }
            }
            MemoryDerivation::BranchJoin { .. }
            | MemoryDerivation::LoopHavoc {
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
            MemoryDerivation::LocalLifetimeEnded { block, .. } => {
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
            MemoryDerivation::BlockDeclared { .. }
            | MemoryDerivation::HeapAllocated { .. }
            | MemoryDerivation::HeapAllocationPending { .. }
            | MemoryDerivation::HeapAllocationFailed { .. }
            | MemoryDerivation::ContractAllocationClaimsChanged { .. }
            | MemoryDerivation::ObjectInitializationRecorded { .. }
            | MemoryDerivation::CellObserved { .. }
            | MemoryDerivation::CellsForgotten { .. } => {}
        }
        entries
    }

    pub(crate) fn proves_owned_resources_separate(
        &self,
        left: &Resource,
        right: &Resource,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter(
            CompositionQuery::ResourcesSeparate(left.clone(), right.clone()),
        ) else {
            return false;
        };
        // What an owner must entail to be the member a side names. A
        // field-bearing instance is only ever owned whole, so its family
        // has no view form and the question is ownership of that instance.
        let named_member = |side: &Resource| match side {
            Resource::Instance(_) => ResourceFact::own(side.clone()),
            _ => ResourceFact::View(side.clone()),
        };
        let left_view = named_member(left);
        let right_view = named_member(right);
        if let (Resource::Memory(left), Resource::Memory(right)) = (left, right) {
            let left_positions = self.owned_memory_candidates_for_range(left, assumptions);
            let right_positions = self.owned_memory_candidates_for_range(right, assumptions);
            #[cfg(debug_assertions)]
            {
                self.cross_check_owned_candidates(&left.base().base, &left_positions, |range| {
                    resource_fact_entails(
                        &ResourceFact::own_memory(range.clone()),
                        &left_view,
                        assumptions,
                    )
                });
                self.cross_check_owned_candidates(&right.base().base, &right_positions, |range| {
                    resource_fact_entails(
                        &ResourceFact::own_memory(range.clone()),
                        &right_view,
                        assumptions,
                    )
                });
            }
            return left_positions.iter().any(|left_entry| {
                resource_fact_entails(self.fact(*left_entry), &left_view, assumptions)
                    && right_positions.iter().any(|right_entry| {
                        left_entry != right_entry
                            && resource_fact_entails(
                                self.fact(*right_entry),
                                &right_view,
                                assumptions,
                            )
                    })
            });
        }
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

    /// Reads at most two entries from the maintained owned-memory index.
    pub(in crate::kernel) fn has_multiple_owned_memory_members(&self) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.storage
            .index
            .owned_memory_by_block
            .values()
            .flat_map(ResourceEntryIds::iter)
            .take(2)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .count()
            == 2
    }

    /// The owned memory fact of this composition that structurally contains
    /// `range`, as its entry and its own range.
    ///
    /// One block bucket, structural containment only: this cannot re-enter
    /// state or alias reasoning. Two lookups decide the composition law
    /// for a pair without materializing any pair.
    fn owned_memory_member_containing(
        &self,
        range: &MemoryRange,
    ) -> Option<(ResourceEntryId, &MemoryRange)> {
        self.storage
            .index
            .memory_by_block
            .get(&range.base().base)?
            .iter()
            .copied()
            .find_map(|entry| {
                let available = self.fact(entry).memory_own_range()?;
                (crate::kernel::assumptions::memory_range_shallowly_contained(range, available)
                    || symbolic_range_shallowly_contained(range, available))
                .then_some((entry, available))
            })
    }

    /// The owned memory members of this composition whose range base is
    /// exactly `base`, as their entries and ranges.
    ///
    /// Read from the base index: logarithmic in the composition to position,
    /// then the members returned. Unlike a block bucket, the answer does not
    /// grow with the other objects the composition owns in the same block,
    /// which for `ExternalArgument` is every object reached from a parameter.
    pub(in crate::kernel) fn owned_memory_members_with_base<'a>(
        &'a self,
        base: &Address,
    ) -> impl Iterator<Item = (u64, &'a MemoryRange)> + 'a {
        crate::instrumentation::record_deterministic_work(1);
        self.storage
            .index
            .memory_by_base
            .get(base)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter_map(|entry| {
                crate::instrumentation::record_deterministic_work(1);
                self.fact(*entry)
                    .memory_own_range()
                    .map(|range| (*entry, range))
            })
    }

    /// One owned member under a written base, without searching a crowded
    /// bucket. Used by automatic store preservation, which may forget a cell
    /// when selecting its owner would require proof search.
    pub(in crate::kernel) fn unique_owned_memory_member_with_base(
        &self,
        base: &Address,
    ) -> Option<(u64, &MemoryRange)> {
        crate::instrumentation::record_deterministic_work(1);
        let entries = self.storage.index.memory_by_base.get(base)?;
        if entries.len() != 1 {
            return None;
        }
        let entry = *entries.iter().next()?;
        self.fact(entry)
            .memory_own_range()
            .map(|range| (entry, range))
    }

    pub(in crate::kernel) fn unique_owned_memory_fact_with_base(
        &self,
        base: &Address,
    ) -> Option<&ResourceFact> {
        let (entry, _) = self.unique_owned_memory_member_with_base(base)?;
        Some(self.fact(entry))
    }

    /// One unambiguous member under an explicit base. A crowded raw bucket
    /// needs the prepared address index or an explicitly selected resource.
    pub(in crate::kernel) fn unique_memory_member_with_base(
        &self,
        base: &Address,
        include_views: bool,
    ) -> Option<&MemoryRange> {
        crate::instrumentation::record_deterministic_work(1);
        let entries = self.storage.index.memory_by_base.get(base)?;
        if entries.len() != 1 {
            return None;
        }
        let fact = self.fact(*entries.iter().next()?);
        if include_views {
            fact.memory_range()
        } else {
            fact.memory_own_range()
        }
    }

    /// Flat owned members, and optionally views, from the exact base index.
    pub(in crate::kernel) fn memory_members_with_base<'a>(
        &'a self,
        base: &Address,
        include_views: bool,
    ) -> impl Iterator<Item = (u64, &'a MemoryRange)> + 'a {
        crate::instrumentation::record_deterministic_work(1);
        self.storage
            .index
            .memory_by_base
            .get(base)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter_map(move |entry| {
                crate::instrumentation::record_deterministic_work(1);
                let fact = self.fact(*entry);
                let range = if include_views {
                    fact.memory_range()
                } else {
                    fact.memory_own_range()
                };
                range.map(|range| (*entry, range))
            })
    }

    /// The owned memory fact of this composition that structurally contains
    /// `pointer`, as its entry and its own range.
    pub(in crate::kernel) fn owned_memory_member_containing_pointer(
        &self,
        pointer: &Address,
    ) -> Option<(ResourceEntryId, &MemoryRange)> {
        self.storage
            .index
            .memory_by_block
            .get(&pointer.base)?
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
    /// state or alias reasoning.
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
        left: &MemoryRange,
        right: &MemoryRange,
    ) -> bool {
        if string_literal_blocks_may_alias(&left.base().base, &right.base().base) {
            return false;
        }
        let Some((left_position, _)) = self.owned_memory_member_containing(left) else {
            return false;
        };
        let Some(positions) = self.storage.index.memory_by_block.get(&right.base().base) else {
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
        left: &Address,
        right: &Address,
    ) -> bool {
        // Each side in its own block's bucket: two owned members are
        // disjoint whatever blocks their pointers are spelled in, except
        // equal literals, which may share their bytes.
        if string_literal_blocks_may_alias(&left.base, &right.base) {
            return false;
        }
        let containing = |pointer: &Address| {
            self.storage
                .index
                .memory_by_block
                .get(&pointer.base)?
                .iter()
                .copied()
                .find(|entry| {
                    self.fact(*entry).memory_own_range().is_some_and(|range| {
                        crate::kernel::assumptions::pointer_in_memory_range_shallow(pointer, range)
                    })
                })
        };
        containing(left)
            .zip(containing(right))
            .is_some_and(|(left, right)| left != right)
    }

    /// Whether the composition law gives this composition same-block
    /// separations in `block`: the block holds two or more owned ranges, and
    /// they do not all share one concrete base with constant bounds (validity
    /// orders those, and the kernel separates them from their constants
    /// without a premise). Linear in the block's owned ranges.
    fn separates_owned_members_in_block(&self, block: &AddressBase) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        if !self
            .storage
            .index
            .shared_owned_memory_blocks
            .contains_key(block)
        {
            return false;
        }
        let mut owned = self
            .storage
            .index
            .owned_memory_by_block
            .get(block)
            .into_iter()
            .flat_map(ResourceEntryIds::iter)
            .filter_map(|entry| self.fact(*entry).memory_own_range());
        let Some(first) = owned.next() else {
            return false;
        };
        let concrete = |range: &MemoryRange| {
            crate::instrumentation::record_deterministic_work(1);
            range.base() == first.base()
                && range.constant_start().is_some()
                && range.constant_end().is_some()
        };
        !(concrete(first) && owned.all(concrete))
    }

    /// Find one exposed member through address keys, never through ambient
    /// resources. Borrowed members require an occurrence-bound checked borrow;
    /// an owner's ordinary read observation is deliberately ineligible.
    pub(in crate::kernel) fn partition_memory_member_at(
        &self,
        pointer: &Address,
        borrowed: bool,
        accepts: impl Fn(&MemoryRange) -> bool,
    ) -> Option<&MemoryRange> {
        let mut base = pointer.clone();
        loop {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(entries) = self.storage.index.memory_by_base.get(&base) {
                for entry in entries.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    let fact = self.fact(*entry);
                    let range = if borrowed {
                        let Some(binding) = self.borrow_dependency(self.occurrence(*entry)) else {
                            continue;
                        };
                        if binding.viewed != *fact {
                            continue;
                        }
                        fact.memory_view_range()
                    } else {
                        fact.memory_own_range()
                    };
                    if let Some(range) = range.filter(|range| accepts(range)) {
                        return Some(range);
                    }
                }
            }
            let next = match base.offset.view() {
                OffsetView::Add(left, _) => left.clone(),
                OffsetView::Constant(value) if value != 0 => AddressOffset::constant(0),
                // A loaded pointer's displacement is all of its offset: the
                // read itself, at displacement zero, is the object's base.
                OffsetView::Int32Scaled { .. } | OffsetView::Int64Scaled { .. }
                    if matches!(base.base, AddressBase::Load(_) | AddressBase::SliceData(_)) =>
                {
                    AddressOffset::constant(0)
                }
                _ => return None,
            };
            base.set_offset(next);
        }
    }

    /// A checked live borrow and a separately held owner belong to disjoint
    /// custody partitions. The borrow binding follows checked composite
    /// projections; observation alone never manufactures such a binding.
    pub(in crate::kernel) fn proves_borrow_partition_separate(
        &self,
        left: &MemoryRange,
        right: &MemoryRange,
    ) -> bool {
        let holds = |range: &MemoryRange, borrowed| {
            self.partition_memory_member_at(range.base(), borrowed, |member| member == range)
                .is_some()
        };
        (holds(left, false) && holds(right, true)) || (holds(left, true) && holds(right, false))
    }

    /// Two distinct owned members, the first of `left_block` accepted by
    /// `left` and the second of `right_block` accepted by `right`, that the
    /// composition law separates: the on-demand form of the separations a
    /// valid composition supports, asked by the query that needs one.
    ///
    /// The candidates are exactly the pairs the composition used to project
    /// eagerly into every fact context holding it (`N(N-1)/2` of them for
    /// `N` owned ranges of one block): two owned ranges of a block that
    /// [`Self::separates_owned_members_in_block`] admits, not already
    /// structurally separate, and accepted by `admit`. Instead of visiting
    /// the pairs, each owned member is asked at most once whether `left`
    /// accepts it and whether `right` does.
    ///
    /// `left_at` and `right_at` are addresses the two sides are spelled at.
    /// The members filed under their roots (`memory_base_root`), and under
    /// the roots of their same-block exact aliases, are asked first: a
    /// member that holds a side is almost always one of them, and then the
    /// query costs those members, not every owned member of the block
    /// (every object a pointer parameter reaches shares one block, so a
    /// call naming two of them used to ask all the others). Only when that
    /// nominated selection holds no admitted pair, the complete conservative
    /// candidate selection is asked, reusing answers already given.
    ///
    /// The answer is the one the full scan gives. A pair the nominated
    /// selection finds is a pair of the full scan's candidate set meeting
    /// all of its conditions (two distinct owned members of those blocks, `left`
    /// accepting one and `right` the other, not structurally separate,
    /// admitted), so the full scan answers `Some` as well; the witness may
    /// differ, and every caller either reads only that one exists or
    /// rechecks the witness it returns (`AccessInRangeEvidence`). When the
    /// selection finds none, `owned_memory_candidates_at` supplies every
    /// member that could hold either operand; open or related bases keep
    /// the full block. The member predicates do not depend on ask order, so
    /// reusing an answer changes nothing. The nomination itself grants
    /// nothing: it chooses which members are asked first.
    ///
    /// The two members may lie in different blocks: owned members are
    /// disjoint however their pointers are spelled. Each side is then asked
    /// of its own block's candidates, and the same-block gate below does
    /// not apply, since two entries of different blocks are never one.
    pub(in crate::kernel) fn separated_owned_members(
        &self,
        left_block: &AddressBase,
        right_block: &AddressBase,
        left_at: &Address,
        right_at: &Address,
        assumptions: &crate::kernel::PureFactContext,
        mut left: impl FnMut(&MemoryRange) -> bool,
        mut right: impl FnMut(&MemoryRange) -> bool,
        mut admit: impl FnMut(&MemoryRange, &MemoryRange) -> bool,
    ) -> Option<(&MemoryRange, &MemoryRange)> {
        if left_block == right_block && !self.separates_owned_members_in_block(left_block)
            || string_literal_blocks_may_alias(left_block, right_block)
        {
            return None;
        }
        let mut left_answers = BTreeMap::<ResourceEntryId, bool>::new();
        let mut right_answers = BTreeMap::<ResourceEntryId, bool>::new();
        let ask = |answers: &mut BTreeMap<ResourceEntryId, bool>,
                   accepts: &mut dyn FnMut(&MemoryRange) -> bool,
                   entry: ResourceEntryId,
                   range: &MemoryRange| {
            *answers.entry(entry).or_insert_with(|| accepts(range))
        };
        let pair = |lefts: &[(ResourceEntryId, &'_ MemoryRange)],
                    rights: &[(ResourceEntryId, &'_ MemoryRange)],
                    admit: &mut dyn FnMut(&MemoryRange, &MemoryRange) -> bool| {
            for (left_entry, left_range) in lefts {
                for (right_entry, right_range) in rights {
                    if left_entry == right_entry {
                        continue;
                    }
                    crate::instrumentation::record_deterministic_work(1);
                    if resources_structurally_separate(
                        &Resource::Memory((*left_range).clone()),
                        &Resource::Memory((*right_range).clone()),
                    ) {
                        continue;
                    }
                    if admit(left_range, right_range) {
                        return Some((*left_entry, *right_entry));
                    }
                }
            }
            None
        };
        let member = |entry: ResourceEntryId| {
            crate::instrumentation::record_deterministic_work(1);
            self.fact(entry)
                .memory_own_range()
                .map(|range| (entry, range))
        };
        if let (Some(left_nominees), Some(right_nominees)) = (
            self.owned_members_nominated_at(left_block, left_at, assumptions),
            self.owned_members_nominated_at(right_block, right_at, assumptions),
        ) {
            let lefts = left_nominees
                .into_iter()
                .filter_map(member)
                .filter(|(entry, range)| ask(&mut left_answers, &mut left, *entry, range))
                .collect::<Vec<_>>();
            if !lefts.is_empty() {
                let rights = right_nominees
                    .into_iter()
                    .filter_map(member)
                    .filter(|(entry, range)| ask(&mut right_answers, &mut right, *entry, range))
                    .collect::<Vec<_>>();
                if let Some((left_entry, right_entry)) = pair(&lefts, &rights, &mut admit) {
                    return Some((
                        self.fact(left_entry).memory_own_range()?,
                        self.fact(right_entry).memory_own_range()?,
                    ));
                }
            }
        }
        let left_candidates = self.owned_memory_candidates_at(left_block, left_at, assumptions);
        let right_candidates = self.owned_memory_candidates_at(right_block, right_at, assumptions);
        #[cfg(debug_assertions)]
        {
            self.cross_check_owned_candidates(left_block, &left_candidates, &mut left);
            self.cross_check_owned_candidates(right_block, &right_candidates, &mut right);
        }
        let lefts = left_candidates
            .into_iter()
            .filter_map(member)
            .filter(|(entry, range)| ask(&mut left_answers, &mut left, *entry, range))
            .collect::<Vec<_>>();
        if lefts.is_empty() {
            return None;
        }
        let rights = right_candidates
            .into_iter()
            .filter_map(member)
            .filter(|(entry, range)| ask(&mut right_answers, &mut right, *entry, range))
            .collect::<Vec<_>>();
        let (left_entry, right_entry) = pair(&lefts, &rights, &mut admit)?;
        Some((
            self.fact(left_entry).memory_own_range()?,
            self.fact(right_entry).memory_own_range()?,
        ))
    }

    #[cfg(debug_assertions)]
    fn cross_check_owned_candidates(
        &self,
        block: &AddressBase,
        candidates: &BTreeSet<ResourceEntryId>,
        mut accepts: impl FnMut(&MemoryRange) -> bool,
    ) {
        if !crate::instrumentation::separation_candidate_cross_checks_enabled()
            || crate::instrumentation::in_uncharged_debug_check()
        {
            return;
        }
        crate::instrumentation::uncharged_debug_check(|| {
            for (entry, range) in self
                .storage
                .index
                .owned_memory_by_block
                .get(block)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .filter(|entry| !candidates.contains(entry))
                .filter_map(|entry| {
                    self.fact(*entry)
                        .memory_own_range()
                        .map(|range| (*entry, range))
                })
            {
                assert!(
                    !accepts(range),
                    "separation candidate index omitted owned entry {entry:?}: {range:?}"
                );
            }
        });
    }

    /// Complete conservative candidates for containment of `at`.
    ///
    /// A fixed footprint at a single scalar base cannot contain a pointer
    /// at a different independent scalar base: the containment routes need
    /// either a fact relating those scalars, or memory/symbolic arithmetic
    /// in one footprint. The condition adjacency is maintained at fact
    /// insertion. If it names the queried scalar, retain the entire block;
    /// this includes order-derived equalities, constant pinning and
    /// transitive aliases without approximating the solver's equality.
    /// Open query bases also keep the full block. Otherwise the same-scalar
    /// bucket plus the open-footprint bucket is complete. A member in the
    /// latter may resolve a load to the queried parameter or cancel a
    /// symbolic endpoint, and must never be discarded just by its root.
    /// This index selects candidates only; the original containment rule
    /// and composition authority still decide every accepted separation.
    fn owned_memory_candidates_at(
        &self,
        block: &AddressBase,
        at: &Address,
        assumptions: &PureFactContext,
    ) -> BTreeSet<ResourceEntryId> {
        let full_block = || {
            self.storage
                .index
                .owned_memory_by_block
                .get(block)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .copied()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .collect()
        };
        let Some(variable) = memory_base_variable(at) else {
            return full_block();
        };
        // Any scalar condition already makes this candidate set conservative.
        // Read the maintained existence witness, without enumerating its facts.
        if assumptions.has_condition_variable(variable) {
            return full_block();
        }
        let key = AtomicConnectionKey::Variable(variable);
        let (mut facts, _) = assumptions.atomic_facts_connected_to(&key, true);
        // Authority, read permissions, and subobject coverage do not equate
        // scalar addresses. Keep other propositions conservatively, including
        // model equalities whose projections may expose a pointer equality.
        let related = facts.any(|fact| {
            crate::instrumentation::record_deterministic_work(1);
            match fact {
                AtomicConnectedFact::Condition(..) => true,
                AtomicConnectedFact::Proposition(Proposition::Predicate { name, .. })
                    if name.starts_with(crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX) =>
                {
                    false
                }
                AtomicConnectedFact::Proposition(proposition) => !matches!(
                    proposition,
                    Proposition::ResourceComposition(_)
                        | Proposition::MemoryLoadable { .. }
                        | Proposition::MemoryCanStore { .. }
                        | Proposition::MemoryReadDefined { .. }
                        | Proposition::MemoryMutatesOnly { .. }
                ),
            }
        });
        if at.base != *block || related {
            return full_block();
        }
        crate::instrumentation::record_deterministic_work(2);
        self.storage
            .index
            .owned_memory_by_base_variable
            .get(&(block.clone(), variable))
            .into_iter()
            .chain(self.storage.index.owned_memory_open_bases.get(block))
            .flat_map(ResourceEntryIds::iter)
            .copied()
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .collect()
    }

    fn owned_memory_candidates_for_range(
        &self,
        range: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> BTreeSet<ResourceEntryId> {
        if range.signed_constant_start().is_none() || range.signed_constant_end().is_none() {
            return self
                .storage
                .index
                .owned_memory_by_block
                .get(&range.base().base)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .copied()
                .inspect(|_| crate::instrumentation::record_deterministic_work(1))
                .collect();
        }
        self.owned_memory_candidates_at(&range.base().base, &range.start_pointer(), assumptions)
    }

    /// The owned members of `block` filed under the root of `at`
    /// (`memory_base_root`) or under the root of one of its same-block exact
    /// aliases: the members a query at `at` asks first. `None` when `at` is
    /// outside `block` or its root has no symbolic atom, whose bucket would
    /// be every constant-offset base of the block; the caller then asks the
    /// whole block. Charges one unit per root and per nominated member.
    fn owned_members_nominated_at(
        &self,
        block: &AddressBase,
        at: &Address,
        assumptions: &crate::kernel::PureFactContext,
    ) -> Option<BTreeSet<ResourceEntryId>> {
        if &at.base != block {
            return None;
        }
        let mut roots = BTreeSet::new();
        for spelling in std::iter::once(at).chain(assumptions.exact_pointer_aliases(at)) {
            crate::instrumentation::record_deterministic_work(1);
            if &spelling.base != block {
                continue;
            }
            let root = memory_base_root(spelling);
            root.1.as_ref()?;
            roots.insert(root);
        }
        let mut nominees = BTreeSet::new();
        for root in &roots {
            for entry in self
                .storage
                .index
                .owned_memory_by_root
                .get(root)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
            {
                crate::instrumentation::record_deterministic_work(1);
                nominees.insert(*entry);
            }
        }
        Some(nominees)
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
        left: &MemoryRange,
        right: &MemoryRange,
        assumptions: &PureFactContext,
        contains: impl Fn(&MemoryRange, &MemoryRange) -> bool,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter(CompositionQuery::RangesSeparate(
            left.clone(),
            right.clone(),
        )) else {
            return false;
        };
        if string_literal_blocks_may_alias(&left.base().base, &right.base().base) {
            return false;
        }
        let holds = |child: &MemoryRange, entry: ResourceEntryId| {
            self.fact(entry)
                .memory_own_range()
                .is_some_and(|available| contains(child, available))
        };
        // A member can contain the range only if the facts relate their
        // bases: the same spelled root, a root an equality of index terms
        // selects, or an exact pointer alias's root. Those buckets are the
        // candidates. Every pointer parameter shares one block, so scanning
        // the block instead would prove containment against each of them,
        // for every cell a call havoc examines. A member outside them is
        // not found, which only leaves the pair unproven, as before.
        let containing = |child: &MemoryRange| {
            // Prefer the written root. A successful containment proof already
            // selects a member; spelling that address many other ways adds
            // no information needed for this query.
            if let Some(entry) = self
                .storage
                .index
                .owned_memory_by_root
                .get(&memory_base_root(child.base()))
                .and_then(|entries| entries.iter().copied().find(|entry| holds(child, *entry)))
            {
                return Some(entry);
            }
            // Owned members are disjoint whatever blocks they are spelled
            // in, so each side is asked of its own candidates, including
            // the roots of pointers its alias class names in other blocks.
            let roots = related_pointer_roots(child.base(), assumptions);
            if roots.iter().any(|(_, atom)| atom.is_none()) {
                // A wholly constant base has no root to key on; its block
                // bucket is the candidate set.
                return self
                    .storage
                    .index
                    .memory_by_block
                    .get(&child.base().base)?
                    .iter()
                    .copied()
                    .find(|entry| holds(child, *entry));
            }
            roots.iter().find_map(|root| {
                crate::instrumentation::record_deterministic_work(1);
                self.storage
                    .index
                    .owned_memory_by_root
                    .get(root)?
                    .iter()
                    .copied()
                    .find(|entry| holds(child, *entry))
            })
        };
        containing(left)
            .zip(containing(right))
            .is_some_and(|(left_position, right_position)| left_position != right_position)
    }

    /// Returns candidate members for covering `target` that are distinct
    /// from every owned resource containing `other`. The caller checks
    /// interval coverage without enumerating unrelated members or pairs.
    pub(in crate::kernel) fn owned_memory_ranges_separate_from(
        &self,
        target: &MemoryRange,
        other: &MemoryRange,
        assumptions: &PureFactContext,
        contains: impl Fn(&Resource, &Resource) -> bool,
    ) -> Vec<MemoryRange> {
        let other_resource = Resource::Memory(other.clone());
        let candidates = self.owned_memory_candidates_for_range(other, assumptions);
        let excluded = candidates
            .iter()
            .chain(self.storage.index.owned_non_memory_entries.iter())
            .copied()
            .filter(|entry| contains(self.fact(*entry).resource(), &other_resource))
            .collect::<BTreeSet<_>>();
        // No owner in `other`'s own block: its owner can live in a block an
        // exact pointer equality identifies with `other`'s address (a fresh
        // symbolic block equal to a parameter's address, say). Only then
        // walk that equality component, so queries the block answers keep
        // their cost.
        let excluded = if excluded.is_empty() {
            let start = other.start_pointer();
            [other.base(), &start]
                .into_iter()
                .flat_map(|pointer| assumptions.pointer_equality_component(pointer))
                .filter(|(alias, _)| alias.base != other.base().base)
                .flat_map(|(alias, _)| {
                    self.owned_memory_candidates_at(&alias.base, &alias, assumptions)
                })
                .filter(|entry| contains(self.fact(*entry).resource(), &other_resource))
                .collect::<BTreeSet<_>>()
        } else {
            excluded
        };
        if excluded.is_empty() {
            return Vec::new();
        }
        self.owned_memory_candidates_for_range(target, assumptions)
            .into_iter()
            .filter(|entry| !excluded.contains(entry))
            .filter_map(|entry| self.fact(entry).memory_own_range().cloned())
            .collect()
    }

    #[cfg(debug_assertions)]
    pub(in crate::kernel) fn owned_memory_ranges_separate_from_full_scan(
        &self,
        block: &AddressBase,
        other: &Resource,
        contains: impl Fn(&Resource, &Resource) -> bool,
    ) -> Vec<MemoryRange> {
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
                (range.base().base == *block).then(|| range.clone())
            })
            .collect()
    }

    pub(in crate::kernel) fn proves_owned_pointers_separate_by(
        &self,
        left: &Address,
        right: &Address,
        contains: impl Fn(&Address, &MemoryRange) -> bool,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter(
            CompositionQuery::PointersSeparate(left.clone(), right.clone()),
        ) else {
            return false;
        };
        if string_literal_blocks_may_alias(&left.base, &right.base) {
            return false;
        }
        let containing = |pointer: &Address| {
            self.storage
                .index
                .memory_by_block
                .get(&pointer.base)?
                .iter()
                .copied()
                .find(|entry| {
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
        range: &MemoryRange,
        pointer: &Address,
        assumptions: &PureFactContext,
        contains_pointer: impl Fn(&Address, &MemoryRange) -> bool,
    ) -> bool {
        self.proves_owned_range_separate_from_pointer_with(
            range,
            pointer,
            assumptions,
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
        range: &MemoryRange,
        pointer: &Address,
        assumptions: &PureFactContext,
        range_contained: impl Fn(&MemoryRange, &MemoryRange) -> bool,
        contains_pointer: impl Fn(&Address, &MemoryRange) -> bool,
    ) -> bool {
        if string_literal_blocks_may_alias(&range.base().base, &pointer.base) {
            return false;
        }
        // A failed separation query must not ask every other parameter
        // object in the shared block. These conservative containment indexes
        // select the same possible owners as the full scan; the caller's
        // membership predicates still decide which ones hold each operand.
        let range_candidates = self.owned_memory_candidates_for_range(range, assumptions);
        #[cfg(debug_assertions)]
        self.cross_check_owned_candidates(&range.base().base, &range_candidates, |available| {
            range_contained(range, available)
        });
        let range_position = range_candidates.into_iter().find(|entry| {
            self.fact(*entry)
                .memory_own_range()
                .is_some_and(|available| range_contained(range, available))
        });
        let Some(range_position) = range_position else {
            return false;
        };
        let pointer_candidates =
            self.owned_memory_candidates_at(&pointer.base, pointer, assumptions);
        #[cfg(debug_assertions)]
        self.cross_check_owned_candidates(&pointer.base, &pointer_candidates, |available| {
            contains_pointer(pointer, available)
        });
        pointer_candidates.into_iter().any(|entry| {
            entry != range_position
                && self
                    .fact(entry)
                    .memory_own_range()
                    .is_some_and(|available| contains_pointer(pointer, available))
        })
    }

    fn direct_match_candidate_positions(&self, fact: &ResourceFact) -> Option<&ResourceEntryIds> {
        let index = &self.storage.index;
        match OwnedMemberKey::of(fact) {
            None => {
                let Resource::Memory(range) = fact.resource() else {
                    unreachable!("only memory has no member key")
                };
                index.memory_by_block.get(&range.base().base)
            }
            Some(OwnedMemberKey::TrackedResource(resource)) => index.by_resource.get(&resource),
            Some(OwnedMemberKey::Instance(identity)) => index.instances.get(&identity),
            Some(OwnedMemberKey::IteratedBlock(block)) => index.iterated_by_block.get(&block),
            Some(OwnedMemberKey::Shape(family, name, arity)) => {
                index.exact_shapes.get(&(family, name, arity))
            }
            Some(OwnedMemberKey::ShapeRoot(_)) => unreachable!("a bucket key is never a root key"),
        }
    }

    /// Adds a resource fact without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_fact` when validity must be checked. A trusted
    /// producer assembling already selected facts should start with
    /// `new_with_equalities` so these deltas retain graph publication. This
    /// method never publishes an unrelated ambient input.
    pub fn unchecked_with_fact(mut self, fact: ResourceFact) -> Self {
        self.insert_fact(fact);
        self
    }

    /// Adds resource facts without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_facts` when validity must be checked. These
    /// deltas preserve an existing graph attachment; they do not publish an
    /// unrelated ambient input. Start a fresh trusted assembly with
    /// `new_with_equalities`.
    pub fn unchecked_with_facts(mut self, facts: impl IntoIterator<Item = ResourceFact>) -> Self {
        for fact in facts {
            self.insert_fact(fact);
        }
        self
    }

    pub(crate) fn unchecked_with_facts_and_occurrences(
        mut self,
        facts: impl IntoIterator<Item = ResourceFact>,
    ) -> (Self, Vec<(ResourceFact, ResourceOccurrenceId)>) {
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
    #[cfg(test)]
    pub(crate) fn unchecked_with_supported_facts(
        self,
        support: &ResourceFact,
        facts: impl IntoIterator<Item = ResourceFact>,
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
    #[cfg(test)]
    pub(crate) fn unchecked_with_supported_facts_from_entry(
        self,
        support_entry: ResourceEntryId,
        support: &ResourceFact,
        facts: impl IntoIterator<Item = ResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert_eq!(self.fact(support_entry), support);
        let support_occurrence = self.occurrence(support_entry);
        self.unchecked_with_supported_facts_from_occurrence(support_occurrence, support, facts)
    }

    #[cfg(test)]
    pub(crate) fn unchecked_with_supported_facts_from_occurrence(
        mut self,
        support_occurrence: ResourceOccurrenceId,
        support: &ResourceFact,
        facts: impl IntoIterator<Item = ResourceFact>,
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

    /// Adds observation projections while recording the memory state and
    /// exact footprint used to derive each one.  This is the memory-aware
    /// counterpart to the legacy support-only API used by call packaging.
    pub(crate) fn unchecked_with_supported_facts_from_occurrence_with_memory(
        self,
        support_occurrence: ResourceOccurrenceId,
        support: &ResourceFact,
        facts: impl IntoIterator<Item = ResourceFact>,
        memory: &SymbolicMemory,
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
        support: &ResourceFact,
        facts: impl IntoIterator<Item = ResourceFact>,
        memory: &SymbolicMemory,
    ) -> (Self, Vec<(ResourceFact, ResourceOccurrenceId)>) {
        debug_assert!(support.is_own());
        debug_assert!(
            self.storage
                .entry_by_occurrence
                .get(&support_occurrence)
                .is_some_and(|entry| self.fact(*entry) == support)
        );
        let memory_state_identity = MemoryStateIdentity::of(memory);
        let mut inserted = Vec::new();
        for fact in facts {
            debug_assert!(fact.is_view());
            let entry = self.storage.next_entry_id;
            let metadata = ResourceSupportMetadata {
                memory_state_identity,
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
    #[cfg(test)]
    pub(crate) fn with_cached_supported_expansion(
        self,
        support: &ResourceFact,
        expansion: Vec<ResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert!(self.storage.index.exact.contains_key(support));
        let (support_occurrence, _) = self
            .unique_owned_occurrence_for_fact(support)
            .expect("cached expansions require one unambiguous owned support entry");
        self.with_cached_supported_expansion_for_occurrence(support_occurrence, support, expansion)
    }

    pub(crate) fn with_cached_supported_expansion_for_occurrence(
        self,
        support_occurrence: ResourceOccurrenceId,
        support: &ResourceFact,
        expansion: Vec<ResourceFact>,
    ) -> Self {
        debug_assert!(
            self.storage
                .entry_by_occurrence
                .get(&support_occurrence)
                .is_some_and(|entry| self.fact(*entry) == support)
        );
        self.with_cached_supported_expansion_arc(
            support_occurrence,
            support,
            std::sync::Arc::new(expansion),
        )
    }

    fn with_cached_supported_expansion_arc(
        mut self,
        support_occurrence: ResourceOccurrenceId,
        support: &ResourceFact,
        expansion: std::sync::Arc<Vec<ResourceFact>>,
    ) -> Self {
        let previous = self.storage.clone();
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.clone(),
            next_entry_id: self.storage.next_entry_id,
            occurrence_by_entry: self.storage.occurrence_by_entry.clone(),
            entry_by_occurrence: self.storage.entry_by_occurrence.clone(),
            index: self.storage.index.clone(),
            supported_by: self.storage.supported_by.clone(),
            nonmemory_projections_by_fact: self.storage.nonmemory_projections_by_fact.clone(),
            principal_views_by_fact: self.storage.principal_views_by_fact.clone(),
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
                depth: self
                    .storage
                    .history
                    .as_ref()
                    .map_or(1, |change| change.depth + 1),
                entry_delta: None,
                fact: support.clone(),
                parent: self.storage.history.clone(),
            })),
            observable_projection_source: None,
            materialized: std::sync::OnceLock::new(),
        });
        self.advance_observable_expansion(&previous, support_occurrence);
        self.rekey_cached_support_entries(support);
        self
    }
    #[cfg(test)]
    pub(crate) fn cached_supported_expansion(
        &self,
        support: &ResourceFact,
    ) -> Option<&[ResourceFact]> {
        self.cached_expansion_for_fact(support)
            .map(|expansion| expansion.as_slice())
    }

    /// Return every cached expansion attached to an exact support occurrence.
    /// Fact-only lookup is intentionally plural: equal authorities may carry
    /// distinct folded states and silently selecting one would discard the
    /// other authority's evidence.
    pub(crate) fn cached_supported_expansions(
        &self,
        support: &ResourceFact,
    ) -> Vec<(ResourceOccurrenceId, Vec<ResourceFact>)> {
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

    #[cfg(test)]
    fn cached_expansion_for_fact(
        &self,
        support: &ResourceFact,
    ) -> Option<&std::sync::Arc<Vec<ResourceFact>>> {
        self.cached_expansion_with_occurrence_for_fact(support)
            .map(|(_, expansion)| expansion)
    }

    #[cfg(test)]
    fn cached_expansion_with_occurrence_for_fact(
        &self,
        support: &ResourceFact,
    ) -> Option<(ResourceOccurrenceId, &std::sync::Arc<Vec<ResourceFact>>)> {
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
        let previous = self.storage.clone();
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
            nonmemory_projections_by_fact: self.storage.nonmemory_projections_by_fact.clone(),
            principal_views_by_fact: self.storage.principal_views_by_fact.clone(),
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
            observable_projection_source: None,
            materialized: std::sync::OnceLock::new(),
        });
        self.advance_observable_expansion(&previous, occurrence);
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
    /// state equality merely to rediscover a folded resource's already
    /// certified body.
    pub(crate) fn cached_support_exposing_fact(
        &self,
        target: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<&ResourceFact> {
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
        fact: ResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts(std::iter::once(fact), assumptions)
    }

    pub fn try_compose_with_facts(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts_delaying_normalization_with_occurrences(facts, assumptions)
            .map(|(context, inserted)| context.normalized_delta(inserted, assumptions))
    }

    pub(crate) fn try_compose_with_facts_delaying_normalization(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
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
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        // `self` is the retained resource partition. Establish only the new
        // facts' relationship with it; its producer already established the
        // old partition. Raw input validation remains an explicit operation.
        self.try_compose_checked_ownership_and_occurrences(facts, assumptions)
    }

    pub(crate) fn try_compose_with_fact_with_occurrence(
        self,
        fact: ResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Option<ResourceOccurrenceId>), ResourceContextValidityError> {
        let (context, mut inserted) = self
            .try_compose_with_facts_delaying_normalization_with_occurrences(
                std::iter::once(fact.clone()),
                assumptions,
            )?;
        let occurrence = inserted.last().map(|(_, occurrence)| *occurrence);
        let context = context.normalized_delta(std::mem::take(&mut inserted), assumptions);
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
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_checked_ownership_and_occurrences(facts, assumptions)
            .map(|(context, _)| context)
    }

    pub(in crate::kernel) fn receive_published_payload(
        receipt: crate::kernel::publication::PublishedPayloadReceipt,
        assumptions: &PureFactContext,
    ) -> Self {
        let (mut residual, payload) = receipt.into_parts();
        if residual.is_empty() {
            residual.synchronize_memory_equalities(assumptions);
        }
        residual.insert_fact(payload);
        residual.advance_prepared_memory_equalities(assumptions);
        residual
    }

    pub(in crate::kernel) fn restore_call_borrows(
        transfer: crate::kernel::functions::ReturnedCallBorrows,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        #[cfg(test)]
        let _fast =
            crate::kernel::search::FastOperationScope::enter("call entry borrow restoration");
        let (mut frame, outputs) = transfer.into_parts();
        // Entry borrows restore their retained ownership to the same residual
        // frame. Entry already established this memory partition; rediscovering
        // it through aliases would recheck the produced transfer. New produced
        // ownership and raw descriptions use the validating constructor below.
        if frame.storage.facts.is_empty() {
            frame.synchronize_memory_equalities(assumptions);
        }
        let mut inserted = Vec::new();
        for fact in outputs.facts() {
            let entry = frame.storage.next_entry_id;
            frame.insert_fact(fact.clone());
            if let Some(error) = frame.exclusive_validity_error(fact) {
                return Err(error);
            }
            inserted.push((fact.clone(), frame.occurrence(entry)));
        }
        frame.advance_prepared_memory_equalities(assumptions);
        Ok((frame, inserted))
    }

    /// Move one checked consumed cell back to the residual selected at entry.
    /// The private producer establishes fixed contract geometry; no frame or
    /// alias discovery is needed to reconstruct that ownership relationship.
    pub(in crate::kernel) fn return_consumed_cell(
        transfer: crate::kernel::functions::ReturnedConsumedCell,
        assumptions: &PureFactContext,
    ) -> (Self, crate::kernel::functions::ReturnResourceTransfer) {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("consumed cell return");
        let (mut frame, output, source, input) = transfer.into_parts();
        if frame.storage.facts.is_empty() {
            frame.synchronize_memory_equalities(assumptions);
        }
        let entry = frame.storage.next_entry_id;
        frame.insert_fact(output);
        let transfer = crate::kernel::functions::ReturnResourceTransfer {
            source,
            destination: frame.occurrence(entry),
            consumed_input: Some(input),
            fresh_allocation: None,
        };
        frame.advance_prepared_memory_equalities(assumptions);
        (frame, transfer)
    }

    /// Install a partition constructed by executed custody or a verified rule.
    /// The producer retains the call's frame relationship; no overlap or
    /// exclusive-identity discovery is repeated at publication.
    pub(in crate::kernel) fn return_constructed_body(
        transfer: crate::kernel::functions::FramedReturnPartition,
        assumptions: &PureFactContext,
    ) -> (Self, Vec<(ResourceFact, ResourceOccurrenceId)>) {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("constructed body return");
        let (mut frame, outputs) = transfer.into_parts();
        if frame.storage.facts.is_empty() {
            frame.synchronize_memory_equalities(assumptions);
        }
        let mut inserted = Vec::new();
        for fact in outputs.facts() {
            let entry = frame.storage.next_entry_id;
            frame.insert_fact(fact.clone());
            inserted.push((fact.clone(), frame.occurrence(entry)));
        }
        frame.advance_prepared_memory_equalities(assumptions);
        (frame, inserted)
    }

    /// Apply allocator-established separation to one returned owned piece.
    /// Actual output custody remains checked at body exit; freshness removes
    /// only discovery of overlap with the caller's pre-allocation frame.
    pub(in crate::kernel) fn return_fresh_allocation(
        transfer: crate::kernel::functions::ReturnedFreshAllocation,
        assumptions: &PureFactContext,
    ) -> (Self, crate::kernel::functions::ReturnResourceTransfer) {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter("fresh allocation return");
        let (mut frame, output, source, allocation) = transfer.into_parts();
        if frame.storage.facts.is_empty() {
            frame.synchronize_memory_equalities(assumptions);
        }
        let entry = frame.storage.next_entry_id;
        frame.insert_fact(output);
        let transfer = crate::kernel::functions::ReturnResourceTransfer {
            source,
            destination: frame.occurrence(entry),
            consumed_input: None,
            fresh_allocation: Some(allocation),
        };
        frame.advance_prepared_memory_equalities(assumptions);
        (frame, transfer)
    }

    pub(in crate::kernel) fn install_held_composite_body(
        construction: crate::kernel::functions::HeldCompositeBody,
        assumptions: &PureFactContext,
    ) -> (Self, Vec<(ResourceFact, ResourceOccurrenceId)>) {
        let (_source, frame, children) = construction.into_parts();
        let (context, inserted) = frame.unchecked_with_facts_and_occurrences(children);
        context.advance_prepared_memory_equalities(assumptions);
        (context, inserted)
    }

    /// Install the body exposed by removal of one selected held composite.
    /// Its definition supplies the relationship with the retained frame.
    pub(crate) fn install_established_partition(
        self,
        body: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        self.install_established_partition_occurrences(
            body.into_iter().map(|fact| (fact, None)),
            assumptions,
        )
    }

    fn install_established_partition_occurrences(
        mut self,
        body: impl IntoIterator<Item = (ResourceFact, Option<ResourceOccurrenceId>)>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        let mut inserted = Vec::new();
        for (fact, occurrence) in body {
            // Preserve the constructor's direct contradictory-range refusal.
            // Missing geometry is discharged by the selected parent's framed
            // definition, never by searching for unrelated owners.
            if fact.has_proven_positive_quantity(assumptions)
                && let crate::kernel::primitives::memory_equality_index::ConstantOwnedOverlap::Overlap(
                entry,
            ) = self.constant_owned_overlap(&fact, assumptions)
            {
                return Err(
                    ResourceContextValidityError::OverlappingOwnedMemoryResources {
                        left: self
                            .fact(entry)
                            .memory_own_range()
                            .expect("selected owner")
                            .clone(),
                        right: fact.memory_own_range().expect("queried owner").clone(),
                    },
                );
            }
            let entry = self.storage.next_entry_id;
            self.insert_fact_with_support_occurrence_and_metadata_at(
                fact.clone(),
                None,
                None,
                None,
                occurrence,
            );
            if let Some(error) = self.exclusive_validity_error(&fact) {
                return Err(error);
            }
            inserted.push((fact, self.occurrence(entry)));
        }
        self.advance_prepared_memory_equalities(assumptions);
        Ok((self, inserted))
    }

    /// Apply the framed definitional exchange R * F -> body(R) * F.
    /// The instance rewrite constructs this body from the exclusively held
    /// parent after selecting its definition/arm and checking child identities.
    /// This is not admission of arbitrary new ownership: no overlap search
    /// against the retained frame is needed to expose ownership already held.
    pub(in crate::kernel) fn unfold_instance_body(
        self,
        instance: &ResourceInstance,
        body: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Option<Self>, ResourceContextValidityError> {
        #[cfg(test)]
        let _fast =
            crate::kernel::search::FastOperationScope::enter("instance unfold frame replacement");
        let parent = ResourceFact::own(Resource::Instance(instance.clone()));
        let source = self
            .unique_owned_occurrence_for_fact(&parent)
            .map(|(source, _)| source);
        let root = source.map(|source| self.framed_origins.get(&source).copied().unwrap_or(source));
        let Some(mut next) = self.without_exact_representation(&parent) else {
            return Ok(None);
        };
        if next.storage.facts.is_empty() {
            next.synchronize_memory_equalities(assumptions);
        }
        for fact in body {
            let entry = next.storage.next_entry_id;
            next.insert_fact(fact.clone());
            if fact.is_own()
                && let Some(root) = root
            {
                next.framed_origins = next
                    .framed_origins
                    .with_inserted(next.occurrence(entry), root);
            }
            // Retain exact exclusive-identity checks. SymbolicMemory/frame overlap
            // discovery is the revalidation removed by this exchange rule.
            if let Some(error) = next.exclusive_validity_error(&fact) {
                return Err(error);
            }
        }
        next.advance_prepared_memory_equalities(assumptions);
        Ok(Some(next))
    }

    /// Nominate at most four entries when this origin accounts for every
    /// member of the caller's block or root. Empty intervals have no overlap.
    /// Duplicate keys need only the first and last occurrences: after the
    /// caller excludes itself, one representative of the other owners remains.
    pub(super) fn constant_owned_neighbors(
        &self,
        origin: &Address,
        start: i128,
        end: i128,
        members: usize,
    ) -> Option<BTreeSet<ResourceEntryId>> {
        let represented = *self
            .storage
            .index
            .concrete_memory_by_base
            .get(&(origin.clone(), true))?;
        if represented != members {
            return None;
        }
        let mut selected = BTreeSet::new();
        if start >= end {
            return Some(selected);
        }
        let key = (origin.clone(), true, start, end);
        let index = &self.storage.index.concrete_memory;
        if let Some(duplicates) = index.get(&key) {
            if let Some(entry) = duplicates.iter().next() {
                selected.insert(*entry);
            }
            if let Some(entry) = duplicates.iter().next_back() {
                selected.insert(*entry);
            }
        }
        if let Some((neighbor, entries)) = index.get_less_than(&key)
            && neighbor.0 == key.0
            && neighbor.1
            && let Some(entry) = entries.iter().next_back()
        {
            selected.insert(*entry);
        }
        if let Some((neighbor, entries)) = index.get_greater_than(&key)
            && neighbor.0 == key.0
            && neighbor.1
            && let Some(entry) = entries.iter().next()
        {
            selected.insert(*entry);
        }
        Some(selected)
    }

    /// The caller supplies a directly stated equality of the two bases.
    /// Rebase before reading coordinates; a merely related root may have a
    /// nonzero displacement and cannot use this operation. The root count
    /// prevents selection from hiding owners with symbolic coordinates.
    fn constant_owned_neighbors_at_exact_alias(
        &self,
        range: &MemoryRange,
        alias: &Address,
    ) -> Option<BTreeSet<ResourceEntryId>> {
        let rebased = range.with_base(alias.clone());
        let (origin, start, end) = constant_memory_coordinates(&rebased)?;
        let members = self
            .storage
            .index
            .owned_memory_by_root
            .get(&memory_base_root(alias))?
            .len();
        self.constant_owned_neighbors(&origin, start, end, members)
    }

    /// Cached key count proves absence without enumerating pointer aliases.
    /// A key exists exactly when its block has at least one memory owner.
    fn has_owned_memory_outside_block(&self, block: &AddressBase) -> bool {
        let blocks = &self.storage.index.owned_memory_by_block;
        blocks.len() > usize::from(blocks.contains_key(block))
    }

    /// The owned memory entries whose overlap with `range` the facts could
    /// prove, in entry order: the owned ranges of its block at a root related
    /// to its base or to a same-block exact alias of it
    /// ([`related_memory_base_roots`]), the owned ranges whose own base has a
    /// same-block exact alias at such a root, and the owned ranges based
    /// exactly at a cross-block exact alias of its base. A completely indexed
    /// constant-coordinate root at an exact alias instead nominates its
    /// interval neighbors, including constant translations of that alias.
    ///
    /// These are the pairs `memory_ranges_proven_overlapping` can answer
    /// through a relating fact. It rebases through exact aliases and then
    /// asks the endpoints under a structural base delta, and a delta between
    /// two different roots, such as `4*a - 4*b` for two pointer parameters,
    /// is bounded only by a fact that relates the two index terms. Pairs
    /// without one are not visited: validity refuses a *proven* overlap, so
    /// an overlap nothing states needs no work, and the ranges of every
    /// other object in the block (for `ExternalArgument`, every object a
    /// parameter reaches) cost nothing. The work is the keys (this base's
    /// aliases and equality classes) and the entries they select.
    ///
    /// `skip_block` leaves out one block's entries, for a caller that has
    /// already covered that block another way.
    fn owned_validity_candidates(
        &self,
        range: &MemoryRange,
        skip_block: Option<&AddressBase>,
        assumptions: &PureFactContext,
    ) -> BTreeSet<ResourceEntryId> {
        crate::kernel::search::ProofSearch::<ResourceContext>::ownership_validity_candidates(
            self,
            range,
            skip_block,
            assumptions,
        )
    }

    /// Extends a valid context with one already-certified valid resource
    /// group, checking only pairs that cross the group boundary.
    ///
    /// Composite expansion checks its children together before caching the
    /// group. Rechecking child/child pairs when that expansion is later
    /// installed can recursively rediscover state and range separation
    /// through an unrelated call history. Only a conflict with the existing
    /// caller frame is new information at installation time.
    #[cfg(test)]
    pub(crate) fn try_compose_certified_group_into_valid_context_delaying_normalization(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_certified_group_into_valid_context_delaying_normalization_with_occurrences(
            facts,
            assumptions,
        )
        .map(|(context, _)| context)
    }

    #[cfg(test)]
    pub(crate) fn try_compose_certified_group_into_valid_context_delaying_normalization_with_occurrences(
        self,
        facts: impl IntoIterator<Item = ResourceFact>,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<(ResourceFact, ResourceOccurrenceId)>), ResourceContextValidityError>
    {
        if self.storage.facts.is_empty() {
            self.synchronize_memory_equalities(assumptions);
        }
        let frame = self.clone();
        let mut context = self;
        let mut inserted = Vec::new();
        for fact in facts {
            // This group's internal composition is already established. Only
            // its boundary with the captured destination is a new obligation.
            frame.admit_certified_memory_boundary(&fact, assumptions)?;
            let entry = context.storage.next_entry_id;
            context.insert_fact(fact.clone());
            if let Some(error) = context.exclusive_validity_error(&fact) {
                return Err(error);
            }
            inserted.push((fact, context.occurrence(entry)));
        }
        context.advance_prepared_memory_equalities(assumptions);
        Ok((context, inserted))
    }

    pub(super) fn missing_ownership_boundary(
        &self,
        fact: &ResourceFact,
    ) -> Option<Box<Proposition>> {
        let range = fact.memory_own_range()?;
        Some(Box::new(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(range.clone())),
            right: Box::new(self.storage.index.boundary_memory.footprint()),
        }))
    }

    fn admit_certified_memory_boundary(
        &self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Result<(), ResourceContextValidityError> {
        // Absence of retained memory owners establishes this boundary even
        // when the group's certified quantity or bounds are symbolic. Do not
        // ask geometry discovery to prove separation from an empty partition.
        if self.storage.index.owned_memory_by_block.is_empty() {
            return Ok(());
        }
        match self.owned_boundary_overlap(fact, assumptions) {
            crate::kernel::primitives::memory_equality_index::ConstantOwnedOverlap::Clear => {}
            crate::kernel::primitives::memory_equality_index::ConstantOwnedOverlap::Overlap(
                entry,
            ) => {
                return Err(
                    ResourceContextValidityError::OverlappingOwnedMemoryResources {
                        left: self
                            .fact(entry)
                            .memory_own_range()
                            .expect("indexed owner")
                            .clone(),
                        right: fact.memory_own_range().expect("queried owner").clone(),
                    },
                );
            }
            crate::kernel::primitives::memory_equality_index::ConstantOwnedOverlap::Unsupported => {
                return Err(ResourceContextValidityError::UnestablishedOwnedBoundary(
                    self.missing_ownership_boundary(fact)
                        .expect("owned memory boundary"),
                ));
            }
        }
        Ok(())
    }

    pub(in crate::kernel) fn has_owned_facts(&self) -> bool {
        self.storage.index.owned_count != 0
    }

    pub(in crate::kernel) fn ownership_frame_revision(
        &self,
    ) -> (std::sync::Arc<()>, std::sync::Arc<()>) {
        (
            self.storage.index.boundary_frame_revision.clone(),
            super::never_address_taken_locals_key(),
        )
    }

    /// The worker producer retained the current parent partition. Keep its
    /// output occurrences and projections without rechecking that evidence.
    pub(in crate::kernel) fn compose_framed_worker_outputs(
        self,
        outputs: &Self,
        assumptions: &PureFactContext,
        _partition: crate::kernel::threads::FramedWorkerOutputs,
    ) -> Result<Self, ResourceContextValidityError> {
        self.compose_output_partition(outputs, assumptions, true)
    }

    /// Join a constructed output partition with today's frame, preserving
    /// its occurrence identities, dependencies and cached projections. Only
    /// the boundary with that frame needs memory admission.
    pub(crate) fn compose_checked_outputs(
        self,
        outputs: &Self,
        assumptions: &PureFactContext,
    ) -> Result<Self, ResourceContextValidityError> {
        self.compose_output_partition(outputs, assumptions, false)
    }

    fn compose_output_partition(
        mut self,
        outputs: &Self,
        assumptions: &PureFactContext,
        framed: bool,
    ) -> Result<Self, ResourceContextValidityError> {
        if self.storage.facts.is_empty() {
            self.synchronize_memory_equalities(assumptions);
        }
        let frame = self.clone();
        for (entry, fact) in outputs.storage.facts.iter() {
            crate::instrumentation::record_deterministic_work(1);
            if !framed {
                frame.admit_certified_memory_boundary(fact, assumptions)?;
            }
            let occurrence = outputs.occurrence(*entry);
            if self.storage.entry_by_occurrence.contains_key(&occurrence) {
                return Err(ResourceContextValidityError::DuplicateOwnedResourceFact(
                    fact.clone(),
                ));
            }
            if let Resource::Instance(instance) = fact.resource() {
                self.record_instance_consumption(
                    instance.identity(),
                    outputs.instance_consumption(instance.identity()).cloned(),
                );
            }
            self.insert_fact_with_support_occurrence_and_metadata_at(
                fact.clone(),
                outputs.storage.supported_by.get(entry).cloned(),
                outputs
                    .storage
                    .support_occurrence_by_projection
                    .get(entry)
                    .copied(),
                outputs
                    .storage
                    .support_metadata_by_projection
                    .get(&occurrence)
                    .cloned(),
                Some(occurrence),
            );
            if let Some(error) = self.exclusive_validity_error(fact) {
                return Err(error);
            }
            if let Some(binding) = outputs.borrow_dependency(occurrence) {
                self = self.with_borrow_dependency(occurrence, binding.clone());
            }
            if let Some(expansion) = outputs
                .storage
                .expansions_by_support_occurrence
                .get(&occurrence)
            {
                self =
                    self.with_cached_supported_expansion_arc(occurrence, fact, expansion.clone());
            }
        }
        self.advance_prepared_memory_equalities(assumptions);
        Ok(self)
    }

    /// The held facts' combined written-syntax ceiling, cached on the
    /// canonical fact set ([`canonical_fact_set::CanonicalFactSet::syntax_ceiling`]).
    pub(in crate::kernel) fn syntax_ceiling(
        &self,
        fact_ceiling: fn(&ResourceFact) -> canonical_fact_set::SyntaxCeiling,
    ) -> canonical_fact_set::SyntaxCeiling {
        self.storage.index.canonical.syntax_ceiling(fact_ceiling)
    }

    #[cfg(test)]
    pub(in crate::kernel) fn facts_are_materialized(&self) -> bool {
        self.storage.materialized.get().is_some()
    }

    pub(in crate::kernel) fn fact_count(&self) -> usize {
        self.storage.facts.len()
    }

    /// The call preparation producer checked intrinsic storage or an empty
    /// body for this nonexclusive observation. Preserve written-neighbor
    /// normalization of views without running owned admission.
    pub(in crate::kernel) fn insert_prepared_call_view(
        mut self,
        fact: ResourceFact,
        assumptions: &PureFactContext,
    ) -> Self {
        assert!(matches!(
            fact,
            ResourceFact::View(Resource::Memory(_) | Resource::Composite { .. })
        ));
        if self.is_empty() {
            self.synchronize_memory_equalities(assumptions);
        }
        let entry = self.storage.next_entry_id;
        self.insert_fact(fact.clone());
        self.advance_prepared_memory_equalities(assumptions);
        let occurrence = self.occurrence(entry);
        self.normalized_delta(vec![(fact, occurrence)], assumptions)
    }

    pub fn facts(&self) -> &[ResourceFact] {
        self.storage
            .materialized
            .get_or_init(|| self.iter().cloned().collect())
    }

    pub(in crate::kernel) fn has_owned_allocation_tokens(&self) -> bool {
        !self.storage.index.owned_allocation_tokens.is_empty()
    }

    pub(in crate::kernel) fn owned_allocation_tokens(&self) -> impl Iterator<Item = &ResourceFact> {
        self.storage
            .index
            .owned_allocation_tokens
            .iter()
            .map(|entry| self.fact(*entry))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    pub(in crate::kernel) fn has_owned_composites(&self) -> bool {
        self.storage.index.owned_composite_count != 0
    }

    pub(in crate::kernel) fn has_folded_composites(&self) -> bool {
        // This index contains only composites and tokens, with composites first.
        self.storage
            .index
            .exact_shapes
            .keys()
            .next()
            .is_some_and(|(family, _, _)| *family == ResourceFamily::Composite)
    }

    /// Select folded composites without materializing unrelated memory facts.
    pub(crate) fn composite_facts(&self) -> impl Iterator<Item = &ResourceFact> {
        let entries = self
            .storage
            .index
            .exact_shapes
            .iter()
            .skip_while(|((family, _, _), _)| *family < ResourceFamily::Composite)
            .take_while(|((family, _, _), _)| *family == ResourceFamily::Composite)
            .flat_map(|(_, entries)| entries.iter().copied())
            .collect::<BTreeSet<_>>();
        entries
            .into_iter()
            .map(|entry| self.fact(entry))
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }

    /// Whether the context is a partition under `assumptions`, and the first
    /// violation in the canonical order if not.
    ///
    /// The check is decided by indexed entries only. An identity can fail
    /// instance validity only when it is held twice or with invalid access,
    /// and those identities are indexed. Two owned ranges can overlap only
    /// when they share a block, which only blocks holding two or more owned
    /// ranges do, or when an exact pointer equality in `assumptions` joins
    /// their bases across blocks; the second walk is driven from whichever
    /// of the two sides — the context's bases or the equalities — is
    /// smaller. Each walk visits its candidates in the same order the
    /// unindexed scans did, so the reported violation is unchanged. A block
    /// owning one range, or an unaliased base, holds no pair and is never
    /// visited, so a caller's unrelated allocations cost nothing here.
    pub fn validity_error(
        &self,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        self.validity_error_with_separation(assumptions, true)
    }

    fn validity_error_with_separation(
        &self,
        assumptions: &PureFactContext,
        use_separation: bool,
    ) -> Option<ResourceContextValidityError> {
        if let Some((identity, ())) = self.storage.index.suspect_mutex_authorities.iter().next() {
            let entries = self
                .storage
                .index
                .by_resource
                .get(identity)
                .expect("suspect mutex authority is held");
            for entry in entries.iter() {
                if let Some(error) = self.exclusive_validity_error(self.fact(*entry)) {
                    return Some(error);
                }
            }
        }
        for (identity, ()) in self.storage.index.suspect_instances.iter() {
            let entries = self
                .storage
                .index
                .instances
                .get(identity)
                .expect("a suspect instance identity is held");
            for entry in entries.iter() {
                if let Some(error) = self.exclusive_validity_error(self.fact(*entry)) {
                    return Some(error);
                }
            }
        }
        for (block, ()) in self.storage.index.shared_owned_memory_blocks.iter() {
            let entries = self
                .storage
                .index
                .memory_by_block
                .get(block)
                .expect("a block with owned ranges has memory entries");
            let owned_entries = entries
                .iter()
                .filter_map(|entry| {
                    #[cfg(test)]
                    crate::instrumentation::record_deterministic_work(1);
                    let fact = self.fact(*entry);
                    fact.memory_own_range().map(|range| (*entry, range))
                })
                .collect::<Vec<_>>();
            let owned = owned_entries
                .iter()
                .map(|(entry, range)| (self.fact(*entry), *range))
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
            let coordinates = owned
                .iter()
                .map(|(fact, range)| {
                    constant_memory_coordinates(range)
                        .map(|(origin, start, end)| (origin, start, end, *fact))
                })
                .collect::<Option<Vec<_>>>();
            if let Some(coordinates) = coordinates
                && coordinates
                    .first()
                    .is_some_and(|first| coordinates.iter().all(|entry| entry.0 == first.0))
            {
                let mut ordered = coordinates
                    .into_iter()
                    .map(|(_, start, end, fact)| (start, end, fact))
                    .collect::<Vec<_>>();
                ordered.sort_by_key(|(start, end, _)| (*start, *end));
                let mut furthest: Option<(i128, &ResourceFact)> = None;
                for (_, end, fact) in ordered {
                    // A checkpoint, not only a charge: an exhausted run stops
                    // here with no proven overlap, as a limited `decide`
                    // does, and the pending limit fails the run.
                    if crate::instrumentation::deadline_exceeded() {
                        return None;
                    }
                    if let Some((furthest_end, left)) = furthest {
                        if let Some(error) = pair_validity_error_with_separation(
                            left,
                            fact,
                            assumptions,
                            use_separation,
                        ) {
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
            // Otherwise each owned range is compared with the owned ranges
            // a fact could relate it to (`owned_validity_candidates`), in the
            // pair order of a pairwise scan.
            let mut pairs = BTreeSet::new();
            for (right_entry, right_range) in &owned_entries {
                if crate::instrumentation::deadline_exceeded_with_work(0) {
                    return None;
                }
                let right_entry = *right_entry;
                for left_entry in self.owned_validity_candidates(right_range, None, assumptions) {
                    if left_entry >= right_entry {
                        break;
                    }
                    pairs.insert((left_entry, right_entry));
                }
            }
            for (left_entry, right_entry) in pairs {
                if crate::instrumentation::deadline_exceeded() {
                    return None;
                }
                let left = self.fact(left_entry);
                let right = self.fact(right_entry);
                if let Some(error) =
                    pair_validity_error_with_separation(left, right, assumptions, use_separation)
                {
                    return Some(error);
                }
            }
        }

        // The block sweep above covers every same-block pair. Visit the
        // output-sized set of exact-base matches for direct cross-block
        // pointer equalities separately, from the smaller index. Both
        // drivers visit the bases held here that have an exact alias, in
        // pointer order.
        let memory_by_base = &self.storage.index.memory_by_base;
        let aliased = assumptions.exactly_aliased_pointers();
        if aliased.len() < memory_by_base.len() {
            for base in aliased {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(entries) = memory_by_base.get(base)
                    && let Some(error) =
                        self.cross_block_alias_error(base, entries, assumptions, use_separation)
                {
                    return Some(error);
                }
            }
        } else {
            for (base, entries) in memory_by_base.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(error) =
                    self.cross_block_alias_error(base, entries, assumptions, use_separation)
                {
                    return Some(error);
                }
            }
        }
        None
    }

    /// Checks the owned ranges at one exact base against those at each of
    /// its direct cross-block aliases.
    fn cross_block_alias_error(
        &self,
        base: &Address,
        entries: &ResourceEntryIds,
        assumptions: &PureFactContext,
        use_separation: bool,
    ) -> Option<ResourceContextValidityError> {
        for entry in entries.iter().copied() {
            if self.fact(entry).memory_own_range().is_none() {
                continue;
            }
            for alias in assumptions.exact_pointer_aliases(base) {
                if alias.base == base.base {
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
                    if let Some(error) = pair_validity_error_with_separation(
                        left,
                        right,
                        assumptions,
                        use_separation,
                    ) {
                        return Some(error);
                    }
                }
            }
        }
        None
    }

    pub fn is_valid(&self, assumptions: &PureFactContext) -> bool {
        self.validity_error(assumptions).is_none()
    }

    /// Validate an assembled description before exposing its composition.
    /// Held execution/proof partitions use `observable_facts_assuming_valid`;
    /// this raw-input boundary must not recheck a producer's successor.
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
        _assumptions: &PureFactContext,
    ) -> Vec<Proposition> {
        let composition = self.observable_composition();
        if composition.storage.index.owned_count >= 2
            || composition.storage.index.owned_composite_count != 0
            || (composition.storage.index.owned_count == 1
                && !composition.borrow_dependencies.map.is_empty())
        {
            vec![Proposition::ResourceComposition(composition)]
        } else {
            Vec::new()
        }
    }

    pub fn satisfies_fact(&self, fact: &ResourceFact, assumptions: &PureFactContext) -> bool {
        if !fact.has_valid_exclusive_access() {
            return false;
        }
        if self.storage.index.exact.contains_key(fact) {
            return true;
        }
        if fact
            .owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
        {
            return true;
        }
        // Exact ownership of a non-memory resource includes its exact
        // view. The resource-key index already erases access mode and owned
        // quantity, so answer this common core-projection query without
        // entering proof-aware memory/state entailment.
        if fact.is_view()
            && fact.memory_range().is_none()
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
        if let Some(range) = fact.memory_range() {
            if memory_range_is_proven_empty(range, assumptions)
                || fact.owned_quantity_term().is_some_and(|quantity| {
                    resource_quantity_resolves_to_zero(quantity, assumptions)
                })
            {
                return true;
            }
            // Observation selects one held supplier. Do not assemble or
            // normalize a speculative collection of alternative fragments.
            if fact.is_view() {
                return self
                    .directly_supporting_memory_fact(fact, range, assumptions)
                    .is_some();
            }
            // Decide unit ownership by constructing its consumption
            // on a persistent branch. The caller retains every occurrence;
            // indexed selection stops at a gap instead of normalizing candidates.
            if fact.owned_quantity() == Some(1) {
                return self
                    .clone()
                    .consume_unit_owned_memory(fact, assumptions, None, true)
                    .is_some();
            }
            let candidates = self.memory_fact_candidates(range, fact.is_own(), assumptions);
            if candidates.entries.iter().any(|entry| {
                candidates.requirement(entry, fact).is_some_and(|aligned| {
                    resource_fact_entails(self.fact(entry), &aligned, assumptions)
                })
            }) {
                return true;
            }
            return self
                .normalized_memory_suppliers(
                    &candidates.entries.iter().collect::<Vec<_>>(),
                    &candidates,
                    range.base(),
                    assumptions,
                )
                .is_some_and(|joined| {
                    joined.directly_supporting_fact(fact, assumptions).is_some()
                });
        }
        if let Some(required) = numeric_population_owned_units(fact) {
            let (units, entries) = self
                .storage
                .index
                .numeric_owned_units
                .get(fact.resource())
                .copied()
                .unwrap_or((0, 0));
            if units >= u128::from(required) {
                return true;
            }
            // If every possible support is already in this constant tally,
            // failure is exact too. Symbolic quantities and proved aliases
            // keep the existing proof-aware entailment route below.
            if self
                .direct_match_candidate_positions(fact)
                .map_or(0, |candidates| candidates.len())
                == entries
            {
                return false;
            }
        }
        if crate::instrumentation::measure_operation(
            "kernel",
            "resource satisfaction",
            "resource satisfaction: indexed direct entailment",
            || {
                // Only facts whose first pointer is related to the required
                // one can entail it (`direct_match_candidates_for`); every
                // held fact of the shape would make this linear in the
                // objects held.
                self.direct_match_candidates_for(fact, assumptions)
                    .into_iter()
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
        false
    }

    /// Non-consuming observation of an exact subcontext. Multiplicity is
    /// checked through the retained index, including duplicate owned shares.
    pub(crate) fn contains_exact_facts_of(&self, required: &Self) -> bool {
        required.storage.index.exact.iter().all(|(fact, entries)| {
            crate::instrumentation::record_deterministic_work(1);
            self.storage
                .index
                .exact
                .get(fact)
                .is_some_and(|available| available.len() >= entries.len())
        })
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
        fact: &ResourceFact,
    ) -> bool {
        if self.storage.index.exact.contains_key(fact) {
            return true;
        }
        let Some(required) = fact.memory_range() else {
            return false;
        };
        let bytes =
            memory_equality_index::read_span(fact).and_then(|bytes| u32::try_from(bytes).ok());
        let start = required.start_pointer();
        self.structural_memory_entries(required.base(), &start, bytes)
            .any(|entry| {
                let available = self.fact(entry);
                let available = if fact.is_own() {
                    available.memory_own_range().cloned()
                } else {
                    resource_fact_read_core_range(available)
                };
                available.is_some_and(|available| {
                    (!required.typed_carrier
                        || (available.provenance == required.provenance
                            && (required.carrier_known()
                                || available.carrier_owner() == required.carrier_owner())))
                        && memory_range_structurally_covers(&available, required, None)
                            == Some(true)
                })
            })
    }

    pub(in crate::kernel) fn permits_memory_read(
        &self,
        pointer: &Address,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        self.permits_designated_memory_read(pointer, None, byte_width, assumptions)
    }

    pub(in crate::kernel) fn permits_designated_memory_read(
        &self,
        pointer: &Address,
        provenance: Option<(&Address, Option<&Address>)>,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        if self.symbolic_object_holds_field(pointer, provenance, byte_width, assumptions) {
            return true;
        }
        if let Some(entries) = self.read_access(pointer, byte_width, assumptions) {
            let entry = entries.entry();
            crate::instrumentation::record_deterministic_work(1);
            let resource = self.fact(entry);
            let Some(address) = entries.address() else {
                return false;
            };
            if provenance.is_some_and(|provenance| {
                resource.memory_range().is_none_or(|range| {
                    !assumptions
                        .access_provenance_matches_bytes(provenance, pointer, byte_width, range)
                })
            }) {
                return false;
            }
            if memory_resource_fact_permits_read(resource, &address, byte_width, assumptions) {
                return true;
            }
            return false;
        }
        false
    }

    /// Bounds evidence for a position, including the one-past endpoint.
    /// Zero bytes select intervals without claiming a readable element.
    pub(in crate::kernel) fn permits_designated_pointer_position(
        &self,
        pointer: &Address,
        operand: &Address,
        provenance: (&Address, Option<&Address>),
        assumptions: &PureFactContext,
    ) -> bool {
        // A field of a symbolic layout formed from `operand` is inside the
        // whole object held at `operand`, by the layout's rule.
        if crate::kernel::SymbolicLayoutName::field_displacement(&pointer.offset).is_some()
            && let Some(entries) = self.read_access(operand, 0, assumptions)
            && let Some(range) = resource_fact_read_core_range(self.fact(entries.entry()))
            && assumptions.access_provenance_matches_bytes(provenance, operand, 0, &range)
            && pointer_formation_in_range(pointer, operand, &range, assumptions)
        {
            return true;
        }
        let Some(entries) = self.read_access(pointer, 0, assumptions) else {
            return false;
        };
        let entry = entries.entry();
        crate::instrumentation::record_deterministic_work(1);
        let address = entries.address().unwrap_or_else(|| pointer.clone());
        let Some(range) = resource_fact_read_core_range(self.fact(entry)) else {
            return false;
        };
        if !assumptions.access_provenance_matches_bytes(provenance, pointer, 0, &range) {
            return false;
        }
        if pointer_formation_in_range(&address, operand, &range, assumptions)
            || (address != *pointer
                && pointer_formation_in_range(pointer, operand, &range, assumptions))
        {
            return true;
        }
        false
    }

    /// The undecided no-wrap condition that keeps an owned range at the
    /// required wide range's base from standing for it, when the two are
    /// spelled in different element widths: `p[0u64..n]` of 8-byte elements
    /// required from the held byte range `p[0u64..n * 8u64]` needs `n * 8`
    /// not to wrap. The owner is the one indexed supplier coverage selects
    /// for the requirement; `None` when there is none, the widths agree, neither range is
    /// wide, the requirement's provenance does not match the owner's, or
    /// one re-spelling has every product decided (coverage then refused for
    /// another reason). Diagnostic only: it runs after coverage has refused,
    /// with at most two re-spellings and one decision per product.
    pub(in crate::kernel) fn wide_range_respelling_refusal(
        &self,
        required: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<crate::kernel::WideRangeNoWrap> {
        let entry = self
            .memory_fact_candidates(required, true, assumptions)
            .entries
            .single_supplier()?;
        crate::instrumentation::record_deterministic_work(1);
        let held = self.fact(entry).memory_own_range()?;
        if (required.typed_carrier
            && !assumptions.access_provenance_matches_range(
                required.access_provenance(),
                required,
                held,
            ))
            || held.element_width() == required.element_width()
            || (held.wide_bounds().is_none() && required.wide_bounds().is_none())
        {
            return None;
        }
        // Coverage tries the requirement in the owner's width, then the
        // owner in the requirement's. When either re-spelling has every
        // product decided, coverage failed for another reason.
        let mut undecided = None;
        for (source, width) in [
            (required, held.element_width()),
            (held, required.element_width()),
        ] {
            let Some(respelled) = wide_memory_range_respelled(source, width) else {
                continue;
            };
            match respelled.no_wrap.into_iter().find(|(count, factor)| {
                assumptions.decide(&wide_respelling_no_wrap_condition(count, *factor)) != Some(true)
            }) {
                None => return None,
                Some((count, factor)) => {
                    undecided.get_or_insert(crate::kernel::WideRangeNoWrap {
                        range: ResourceFact::own_memory(source.clone()),
                        count,
                        factor,
                    });
                }
            }
        }
        undecided
    }

    /// A bulk read covers physical bytes, even when its width happens
    /// to equal the ABI pointer width. Scalar pointer-cell conventions do
    /// not shorten an array copy's footprint.
    pub(in crate::kernel) fn permits_designated_storage_read(
        &self,
        pointer: &Address,
        provenance: Option<(&Address, Option<&Address>)>,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        if self.symbolic_object_holds_field(pointer, provenance, bytes, assumptions) {
            return true;
        }
        let Some(entries) = self.read_access(pointer, bytes, assumptions) else {
            return false;
        };
        let entry = entries.entry();
        crate::instrumentation::record_deterministic_work(1);
        let Some(address) = entries.address() else {
            return false;
        };
        let Some(range) = self.fact(entry).memory_range() else {
            return false;
        };
        if provenance
            .is_some_and(|d| !assumptions.access_provenance_matches_bytes(d, pointer, bytes, range))
        {
            return false;
        }
        let required = ResourceFact::view_memory(
            MemoryRange::new_with_element_width(address, 0u32.into(), bytes.into(), 1)
                .with_carrier_of(range),
        );
        if resource_fact_entails(self.fact(entry), &required, assumptions) {
            return true;
        }
        false
    }

    /// Whether the `bytes` at `pointer`, a field of a symbolic layout, lie in
    /// the whole object held at that object's start: the owner is found at
    /// the object's address, and the field is inside it by the layout's rule.
    fn symbolic_object_holds_field(
        &self,
        pointer: &Address,
        provenance: Option<(&Address, Option<&Address>)>,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        self.symbolic_object_holding_field(pointer, provenance, bytes, false, assumptions)
            .is_some()
    }

    /// The range of the whole symbolic object, owned for a `write`, that
    /// holds the `bytes` at `pointer`, a field of its layout: found at the
    /// object's start, the field inside it by the layout's rule.
    fn symbolic_object_holding_field(
        &self,
        pointer: &Address,
        provenance: Option<(&Address, Option<&Address>)>,
        bytes: u32,
        write: bool,
        assumptions: &PureFactContext,
    ) -> Option<&MemoryRange> {
        let (rest, layout, field) =
            crate::kernel::SymbolicLayoutName::field_displacement(&pointer.offset)?;
        let object = pointer.with_offset(rest.cloned().unwrap_or(AddressOffset::constant(0)));
        let entries = if write {
            self.write_access(&object, 0, assumptions)
        } else {
            self.read_access(&object, 0, assumptions)
        };
        // An object of abstract size has no byte span for the access index:
        // its one owned member at the object's base, or at an exact alias
        // of it, holds the field.
        let by_member = || -> Option<&MemoryRange> {
            let stored = match &object.base {
                AddressBase::Load(load) => crate::kernel::eval::loaded_pointer_stored_address(
                    load, None,
                )
                .and_then(|stored| {
                    matches!(object.offset.view(), OffsetView::Constant(0)).then_some(stored)
                }),
                _ => None,
            };
            std::iter::once(object.clone())
                .chain(stored)
                .chain(assumptions.exact_pointer_aliases(&object).cloned())
                .find_map(|alias| {
                    crate::instrumentation::record_deterministic_work(1);
                    let (_, range) = self.unique_owned_memory_member_with_base(&alias)?;
                    let field_pointer = alias.offset_by_layout(layout.field_offset(field));
                    symbolic_object_covers_field(
                        range,
                        &MemoryRange::new_with_element_width(
                            field_pointer,
                            0u32.into(),
                            bytes.into(),
                            1,
                        ),
                    )
                    .then_some(range)
                })
        };
        let Some(entries) = entries else {
            return by_member();
        };
        crate::instrumentation::record_deterministic_work(1);
        let fact = self.fact(entries.entry());
        let range = if write {
            fact.memory_own_range()?
        } else {
            fact.memory_range()?
        };
        // The held range is the whole object at `object`, so an access
        // through a pointer whose bounds are that object's matches it even
        // through a byte view of the object.
        let provenance_matches = provenance.is_none_or(|provenance| {
            assumptions.access_provenance_matches_bytes(provenance, &object, 0, range)
                || (assumptions.provenance_equal(provenance.0, &range.provenance)
                    && provenance.1.is_none_or(|owner| *owner == object))
        });
        (provenance_matches
            && symbolic_object_covers_field(
                range,
                &MemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), bytes.into(), 1),
            ))
        .then_some(range)
        .or_else(by_member)
    }

    /// Storage authority uses the same retained occurrence and graph alignment
    /// as resource support. Equality selects the owner; quantity and the entire
    /// byte footprint remain ordinary resource entailment obligations.
    pub(in crate::kernel) fn owns_storage_access(
        &self,
        pointer: &Address,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        self.owned_storage_access(pointer, None, bytes, assumptions)
            .is_some()
    }

    pub(in crate::kernel) fn owns_designated_storage_access(
        &self,
        pointer: &Address,
        provenance: (&Address, Option<&Address>),
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        self.owned_storage_access(pointer, Some(provenance), bytes, assumptions)
            .is_some()
    }

    /// Consumes the owned access [`Self::owns_storage_access`] finds, spelled
    /// at the address of the fact that supplies it.
    pub(in crate::kernel) fn without_owned_storage_access(
        self,
        pointer: &Address,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        let access = self.owned_storage_access(pointer, None, bytes, assumptions)?;
        self.without_fact_delaying_normalization(&access, assumptions)
    }

    fn owned_storage_access(
        &self,
        pointer: &Address,
        provenance: Option<(&Address, Option<&Address>)>,
        bytes: u32,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFact> {
        let entries = self.write_access(pointer, bytes, assumptions)?;
        let entry = entries.entry();
        crate::instrumentation::record_deterministic_work(1);
        if !self.fact(entry).has_proven_positive_quantity(assumptions) {
            return None;
        }
        let address = entries.address()?;
        let range = self.fact(entry).memory_range()?;
        if provenance
            .is_some_and(|d| !assumptions.access_provenance_matches_bytes(d, pointer, bytes, range))
        {
            return None;
        }
        let aligned = ResourceFact::own_memory(
            MemoryRange::new_with_element_width(address, 0u32.into(), bytes.into(), 1)
                .with_carrier_of(range),
        );
        if resource_fact_entails(self.fact(entry), &aligned, assumptions) {
            return Some(aligned);
        }
        None
    }

    /// Whether a held resource grants the whole object `required`, for a
    /// write when `write` and a read otherwise: the owner its first byte
    /// selects covers it, as an access of a value of an abstract type,
    /// `[p, p + sizeof(T))`, needs ([`MemoryRange::access`]).
    pub(in crate::kernel) fn permits_object_access(
        &self,
        required: &MemoryRange,
        write: bool,
        assumptions: &PureFactContext,
    ) -> bool {
        let pointer = required.base();
        let entries = if write {
            self.write_access(pointer, 1, assumptions)
        } else {
            self.read_access(pointer, 1, assumptions)
        };
        // An object of abstract size has no byte span for the interval
        // index; its one owned member at the object's own base holds it.
        let Some(entry) = entries.map(|entries| entries.entry()).or_else(|| {
            self.unique_owned_memory_member_with_base(pointer)
                .map(|(entry, _)| entry)
        }) else {
            return false;
        };
        crate::instrumentation::record_deterministic_work(1);
        let resource = self.fact(entry);
        let held = if write {
            resource.memory_own_range()
        } else {
            resource.memory_range()
        };
        (!write || resource.has_proven_positive_quantity(assumptions))
            && held.is_some_and(|held| memory_range_covers(held, required, assumptions))
    }

    pub(in crate::kernel) fn memory_write_range(
        &self,
        pointer: &Address,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> Option<&MemoryRange> {
        self.designated_memory_write_range(pointer, None, byte_width, assumptions)
    }

    pub(in crate::kernel) fn designated_memory_write_range(
        &self,
        pointer: &Address,
        provenance: Option<(&Address, Option<&Address>)>,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> Option<&MemoryRange> {
        if let Some(range) =
            self.symbolic_object_holding_field(pointer, provenance, byte_width, true, assumptions)
        {
            return Some(range);
        }
        if let Some(entries) = self.write_access(pointer, byte_width, assumptions) {
            let entry = entries.entry();
            crate::instrumentation::record_deterministic_work(1);
            let resource = self.fact(entry);
            let range = resource.memory_own_range()?;
            if provenance.is_some_and(|origin| {
                !assumptions.access_provenance_matches_bytes(origin, pointer, byte_width, range)
            }) {
                return None;
            }
            let address = entries.address()?;
            if memory_resource_fact_permits_write(resource, &address, byte_width, assumptions) {
                return Some(range);
            }
            return None;
        }
        None
    }

    /// The live owner selected by the shared address-class access index.
    /// Keep its occurrence identity so separation can distinguish independent
    /// members from two accesses within one member. Equality selects the
    /// candidate; the physical frame judgment checks its complete byte span.
    pub(in crate::kernel) fn owned_memory_member_covering_access(
        &self,
        pointer: &Address,
        byte_width: u32,
        assumptions: &PureFactContext,
    ) -> Option<(u64, &MemoryRange)> {
        if let Some(entries) = self.write_access(pointer, byte_width, assumptions) {
            let entry = entries.entry();
            crate::instrumentation::record_deterministic_work(1);
            let resource = self.fact(entry);
            let range = resource.memory_own_range()?;
            let address = entries.address()?;
            // Permission lookup uses the historical logical pointer-cell
            // unit when selecting candidates. Separation needs all physical
            // bytes, just as the existing held-range/frame judgment does.
            if resource.has_proven_positive_quantity(assumptions)
                && assumptions.kept_range_holds_access(range, &address, byte_width)
            {
                return Some((entry, range));
            }
            return None;
        }
        None
    }

    /// [`Self::owned_memory_member_covering_access`] for an access of any
    /// extent: a whole object of abstract size has no byte span for the
    /// access index, so its member is the one owned at its address.
    pub(in crate::kernel) fn owned_memory_member_covering_extent(
        &self,
        pointer: &Address,
        extent: crate::kernel::AccessExtent,
        assumptions: &PureFactContext,
    ) -> Option<(u64, &MemoryRange)> {
        let crate::kernel::AccessExtent::Object(_) = extent else {
            return self.owned_memory_member_covering_access(
                pointer,
                extent.bytes().expect("a byte extent"),
                assumptions,
            );
        };
        crate::instrumentation::record_deterministic_work(1);
        let (entry, range) = self.unique_owned_memory_member_with_base(pointer)?;
        (self.fact(entry).has_proven_positive_quantity(assumptions)
            && assumptions.access_held_by_range(pointer, extent, range))
        .then_some((entry, range))
    }

    pub fn without_fact(self, fact: &ResourceFact, assumptions: &PureFactContext) -> Option<Self> {
        self.without_fact_delaying_normalization(fact, assumptions)
            .map(|context| context.normalized(assumptions))
    }

    pub(in crate::kernel) fn without_fact_delaying_normalization(
        mut self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        self.consume_fact_without_normalizing(fact, assumptions)
            .then_some(self)
    }

    /// Consume from retained memory suppliers, composing only selected fragments
    /// when no single supplier suffices. Nonmemory resources use their local
    /// exact/shape indexes. Neither route materializes unrelated holdings;
    /// persistent edits preserve this context's mutation ancestry.
    pub(crate) fn without_fact_incrementally(
        self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        self.without_fact_incrementally_impl(fact, assumptions, None)
    }

    /// Commit split origins together with a successful persistent successor.
    pub(crate) fn without_fact_incrementally_with_origins(
        self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
        origins: &mut MemorySplitOrigins,
    ) -> Option<Self> {
        let mut next_origins = origins.clone();
        let next =
            self.without_fact_incrementally_impl(fact, assumptions, Some(&mut next_origins))?;
        *origins = next_origins;
        Some(next)
    }

    /// Consume one already selected occurrence. The caller supplies its
    /// identity; this operation neither discovers suppliers nor composes
    /// fragments. A failed check never tries a different occurrence.
    pub(crate) fn without_selected_fact_with_origins(
        mut self,
        occurrence: ResourceOccurrenceId,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
        origins: &mut MemorySplitOrigins,
    ) -> Option<Self> {
        if !fact.has_valid_exclusive_access() {
            return None;
        }
        let entry = *self.storage.entry_by_occurrence.get(&occurrence)?;
        let aligned = if let Some(range) = fact.memory_range() {
            self.memory_fact_candidates(range, fact.is_own(), assumptions)
                .requirement(entry, fact)?
        } else {
            fact.clone()
        };
        let mut next_origins = origins.clone();
        if !self.consume_fact_from_candidates_with_origins(
            &aligned,
            assumptions,
            [entry],
            Some(&mut next_origins),
        ) {
            return None;
        }
        *origins = next_origins;
        Some(self)
    }

    fn without_fact_incrementally_impl(
        self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
        mut origins: Option<&mut MemorySplitOrigins>,
    ) -> Option<Self> {
        if !fact.has_valid_exclusive_access() {
            return None;
        }
        let Resource::Memory(range) = fact.resource() else {
            return self.without_fact_from_local_indexes(fact, assumptions);
        };
        if fact
            .owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
            || memory_range_is_proven_empty(range, assumptions)
        {
            return Some(self);
        }
        if fact.is_view() {
            // Observing a view preserves the supplier, including its occurrence
            // and borrow identities. Joining fragments requires explicit proof.
            let supported = self
                .directly_supporting_memory_fact(fact, range, assumptions)
                .is_some();
            return supported.then_some(self);
        }
        if fact.owned_quantity() == Some(1) {
            return self.consume_unit_owned_memory(fact, assumptions, origins, false);
        }
        let candidates = self.memory_fact_candidates(range, fact.is_own(), assumptions);
        let mut selected = self;
        for entry in candidates.entries.iter() {
            if let Some(required) = candidates.requirement(entry, fact)
                && selected.consume_fact_from_candidates_with_origins(
                    &required,
                    assumptions,
                    std::iter::once(entry),
                    origins.as_deref_mut(),
                )
            {
                return Some(selected);
            }
        }
        let mut joined = selected.normalized_memory_suppliers(
            &candidates.entries.iter().collect::<Vec<_>>(),
            &candidates,
            range.base(),
            assumptions,
        )?;
        let support = joined.memory_fact_candidates(range, fact.is_own(), assumptions);
        let mut consumed = false;
        for entry in support.entries.iter() {
            if let Some(required) = support.requirement(entry, fact)
                && joined.consume_fact_from_candidates(
                    &required,
                    assumptions,
                    std::iter::once(entry),
                )
            {
                consumed = true;
                break;
            }
        }
        if !consumed {
            return None;
        }
        for entry in candidates.entries.iter() {
            if selected.storage.facts.contains_key(&entry) {
                selected.remove_entry(entry);
            }
        }
        for residual in joined.iter() {
            selected.insert_fact(residual.clone());
        }
        Some(selected)
    }

    /// Consume an explicit unit-owned footprint through retained supplier identities.
    /// A gap ends the operation; no candidate frontier is collected or retried.
    fn consume_unit_owned_memory(
        mut self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
        mut origins: Option<&mut MemorySplitOrigins>,
        establish_requested_carrier: bool,
    ) -> Option<Self> {
        let range = required.memory_own_range()?;
        let candidates = self.memory_fact_candidates(range, true, assumptions);
        let supplier = candidates.entries.single_supplier();
        if let Some(entry) = supplier
            && self.fact(entry).has_proven_positive_quantity(assumptions)
            && !self
                .fact(entry)
                .memory_own_range()
                .is_some_and(|available| memory_range_definitely_shorter(available, range))
            && let Some(aligned) = candidates.requirement(entry, required)
            && self.consume_fact_from_candidates_with_origins(
                &aligned,
                assumptions,
                [entry],
                origins.as_deref_mut(),
            )
        {
            return Some(self);
        }
        // A constant request can cross a symbolic partition boundary.
        if range.has_symbolic_bounds()
            || supplier.is_some_and(|entry| {
                self.fact(entry)
                    .memory_own_range()
                    .is_some_and(MemoryRange::has_symbolic_bounds)
            })
        {
            return self.consume_symbolic_partition(required, assumptions, origins);
        }
        self.reserve_owned_memory_fragments_impl(
            required,
            assumptions,
            origins,
            establish_requested_carrier,
        )
        .map(|(remaining, _)| remaining)
    }

    /// Compose the selected endpoint chain, without inspecting other starts.
    /// Requests and their intermediate partition points may be symbolic.
    fn consume_symbolic_partition(
        mut self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
        mut origins: Option<&mut MemorySplitOrigins>,
    ) -> Option<Self> {
        let source = self.clone();
        source.walk_symbolic_owned_partition(required, assumptions, |entry, available| {
            self.consume_fact_from_candidates_with_origins(
                available,
                assumptions,
                [entry],
                origins.as_deref_mut(),
            )
            .then_some(())
        })?;
        Some(self)
    }

    /// Follow the indexed endpoint chain on the original partition. The
    /// consumer can remove each selected occurrence or just retain coverage.
    fn walk_symbolic_owned_partition(
        &self,
        required: &ResourceFact,
        assumptions: &PureFactContext,
        mut visit: impl FnMut(ResourceEntryId, &ResourceFact) -> Option<()>,
    ) -> Option<()> {
        let range = required.memory_own_range().expect("unit ownership query");
        let candidates = self.memory_fact_candidates(range, true, assumptions);
        let first = candidates.entries.single_supplier()?;
        let mut next = first;
        let mut visited = BTreeSet::new();
        let mut joined: Option<ResourceFact> = None;
        loop {
            if !visited.insert(next) {
                return None;
            }
            let available = self.fact(next);
            if available.owned_quantity() != Some(1) {
                return None;
            }
            let piece = candidates.supplier_at_base(next, range.base())?;
            // A selected cell such as (p + i)[0..1] must use the request's
            // coordinates before containment and adjacency. This restates one
            // supplied footprint; it never discovers another owner or alias.
            let piece = match piece.memory_own_range() {
                Some(selected)
                    if range.wide_bounds().is_none()
                        && selected.wide_bounds().is_none()
                        && selected.base() != range.base()
                        && constant_range_span(selected).is_some() =>
                {
                    ResourceFact::own_memory(memory_range_rebased(
                        selected,
                        range.base(),
                        assumptions,
                    )?)
                }
                _ => piece,
            };
            let piece_range = piece.memory_own_range()?;
            if range.typed_carrier
                && !assumptions.access_provenance_matches_range(
                    range.access_provenance(),
                    range,
                    piece_range,
                )
            {
                return None;
            }
            let combined = match joined {
                None => piece,
                Some(ref prior) => normalize_resource_fact_pair(prior, &piece, assumptions)?,
            };
            let combined_range = combined.memory_own_range()?;
            // Do not continue a chain outside the footprint the query names.
            if !memory_range_covers(range, combined_range, assumptions) {
                return None;
            }
            visit(next, available)?;
            if resource_fact_entails(&combined, required, assumptions) {
                return Some(());
            }
            let successor = candidates.sole_owned_start(&combined_range.end_pointer())?;
            joined = Some(combined);
            next = successor;
        }
    }

    /// Join only the suppliers selected for the explicit footprint. Borrow-bound
    /// observations keep their original occurrences and cannot be coalesced.
    /// This is proportional to selected input, never the ambient context.
    fn normalized_memory_suppliers(
        &self,
        entries: &[ResourceEntryId],
        candidates: &super::memory_equality_index::MemoryFactCandidates,
        base: &Address,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        if entries.len() < 2
            || entries.iter().any(|entry| {
                self.storage.supported_by.contains_key(entry)
                    || self
                        .borrow_dependencies
                        .map
                        .contains_key(&self.occurrence(*entry))
            })
        {
            return None;
        }
        let mut suppliers = Self::new_with_equalities(assumptions);
        for entry in entries {
            let supplier = candidates
                .supplier_at_base(*entry, base)
                .unwrap_or_else(|| self.fact(*entry).clone());
            // A cell returned at an interior pointer must share the query's
            // coordinates before adjacency indexing. This only rebases the
            // already selected constant-size range; carrier checks remain in
            // the ordinary merge rule.
            let supplier = match &supplier {
                ResourceFact::Own(Resource::Memory(range), quantity) => {
                    memory_range_rebased(range, base, assumptions).map_or_else(
                        || supplier.clone(),
                        |range| ResourceFact::Own(Resource::Memory(range), quantity.clone()),
                    )
                }
                _ => supplier,
            };
            suppliers.insert_fact(supplier);
        }
        Some(suppliers.normalized_with_byte_endpoints(assumptions, true, false))
    }

    fn without_fact_from_local_indexes(
        mut self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        debug_assert!(
            fact.memory_range().is_none(),
            "memory consumption uses retained graph suppliers"
        );
        if !fact.has_valid_exclusive_access() {
            return None;
        }
        if fact
            .owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
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
                if self.storage.facts.contains_key(entry) {
                    self.remove_entry(*entry);
                }
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
                if self.storage.facts.contains_key(entry) {
                    self.remove_entry(*entry);
                }
            }
            for residual in residual {
                self.insert_fact(residual);
            }
            return Some(self);
        }
        None
    }

    /// Rejoins each returned owned memory piece in `seeds` with the owned
    /// pieces that abut it, after a call returned the piece it borrowed.
    ///
    /// Only the piece's neighbours in the constant-range index are candidates
    /// (the same probe the composition check makes), so the work is the
    /// rejoined chain's, not the block's: every parameter object shares the
    /// external argument block. A merged owner's supported projections and
    /// cached expansions are read through the support indexes and restored
    /// while their owner survives; a projection of an owner merged away is
    /// dropped with it, since the merged owner supplies the same view.
    pub(crate) fn rejoined_memory_around(
        mut self,
        seeds: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> Self {
        for seed in seeds {
            if seed.memory_own_range().is_none() {
                continue;
            }
            let Some(mut entry) = self.storage.index.exact.get(seed).and_then(|entries| {
                entries
                    .iter()
                    .copied()
                    .find(|entry| self.storage.supported_by.get(entry).is_none())
            }) else {
                continue;
            };
            while let Some((neighbour, merged)) = self.abutting_owned_memory(entry, assumptions) {
                let mut supported = Vec::new();
                let mut expansions = Vec::new();
                self.collect_removed_support(entry, &mut supported, &mut expansions);
                self.collect_removed_support(neighbour, &mut supported, &mut expansions);
                self.remove_entry(entry);
                if self.storage.facts.contains_key(&neighbour) {
                    self.remove_entry(neighbour);
                }
                entry = self.storage.next_entry_id;
                self.insert_fact(merged);
                self = self
                    .restore_supported_projection_pairs(supported)
                    .restore_cached_support_expansions(expansions);
            }
        }
        self
    }

    /// The owned memory piece next to `entry` in the constant-range index
    /// that the pair rule merges with it, and the merged fact.
    fn abutting_owned_memory(
        &self,
        entry: ResourceEntryId,
        assumptions: &PureFactContext,
    ) -> Option<(ResourceEntryId, ResourceFact)> {
        let fact = self.fact(entry);
        let range = fact.memory_own_range()?;
        let (origin, start, end) = constant_memory_coordinates(range)?;
        let key = (origin, true, start, end);
        let index = &self.storage.index.concrete_memory;
        let before = index
            .get_less_than(&key)
            .filter(|(candidate, _)| candidate.0 == key.0 && candidate.1)
            .and_then(|(_, entries)| entries.iter().next_back().copied());
        let after = index
            .get_greater_than(&key)
            .filter(|(candidate, _)| candidate.0 == key.0 && candidate.1)
            .and_then(|(_, entries)| entries.iter().next().copied());
        [before, after]
            .into_iter()
            .flatten()
            .filter(|candidate| {
                *candidate != entry && self.storage.supported_by.get(candidate).is_none()
            })
            .find_map(|candidate| {
                crate::instrumentation::record_deterministic_work(1);
                normalize_resource_fact_pair(fact, self.fact(candidate), assumptions)
                    .map(|merged| (candidate, merged))
            })
    }

    fn supported_projection_pair(
        &self,
        entry: ResourceEntryId,
        support: &ResourceFact,
    ) -> (
        Option<ResourceOccurrenceId>,
        ResourceFact,
        ResourceFact,
        Option<ResourceSupportMetadata>,
    ) {
        (
            self.storage
                .support_occurrence_by_projection
                .get(&entry)
                .copied(),
            support.clone(),
            self.fact(entry).clone(),
            self.storage
                .support_metadata_by_projection
                .get(&self.occurrence(entry))
                .cloned(),
        )
    }

    /// The supported projections and cached expansion that removing `entry`
    /// drops: its own occurrence's, and those of the projections that cascade
    /// with it (`remove_entry`), found through the support-occurrence index.
    fn collect_removed_support(
        &self,
        entry: ResourceEntryId,
        supported: &mut Vec<(
            Option<ResourceOccurrenceId>,
            ResourceFact,
            ResourceFact,
            Option<ResourceSupportMetadata>,
        )>,
        expansions: &mut Vec<(ResourceOccurrenceId, Vec<ResourceFact>)>,
    ) {
        let mut pending = vec![entry];
        let mut visited = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !visited.insert(current) || !self.storage.facts.contains_key(&current) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let occurrence = self.occurrence(current);
            if let Some(expansion) = self
                .storage
                .expansions_by_support_occurrence
                .get(&occurrence)
            {
                expansions.push((occurrence, expansion.as_ref().clone()));
            }
            let Some(projections) = self
                .storage
                .projections_by_support_occurrence
                .get(&occurrence)
            else {
                continue;
            };
            for projection in projections.iter().copied() {
                if let Some(support) = self.storage.supported_by.get(&projection) {
                    supported.push(self.supported_projection_pair(projection, support));
                }
                pending.push(projection);
            }
        }
    }

    pub(crate) fn without_exact_representation(mut self, fact: &ResourceFact) -> Option<Self> {
        let entry = *self.storage.index.exact.get(fact)?.iter().next()?;
        self.remove_entry(entry);
        Some(self)
    }

    /// Consumes several facts while postponing whole-context normalization
    /// until the end. If a required fact is only available after adjacent
    /// resources are merged, normalize once at that point and retry it.
    pub fn without_facts(
        self,
        facts: &[ResourceFact],
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
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        if !fact.has_valid_exclusive_access() {
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
            if let Resource::Memory(required_range) = fact.resource() {
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
        let merge_candidates = fact.is_own().then(|| candidates.clone());
        if self.consume_fact_from_candidates(fact, assumptions, candidates) {
            return true;
        }
        if let Some(candidates) = merge_candidates
            && self.consume_fact_from_merged_units(fact, assumptions, &candidates)
        {
            return true;
        }
        fact.owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_resolves_to_zero(quantity, assumptions))
    }

    /// Consume a constant owned quantity no single held unit covers from
    /// several plain units of the same resource. A body that took one of two
    /// `slot(pool)` and later produced another holds `slot(pool) x 1` twice;
    /// a context only merges them when it normalizes, which consumption
    /// deliberately does not do first. The units are those the consumption
    /// already selected by key, admitted with the family's own pair rule in
    /// their index order until their constant total covers `fact`. Memory keeps
    /// its own supplier composition, and a unit with a borrow, support,
    /// projection or witness keeps its identity.
    fn consume_fact_from_merged_units(
        &mut self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
        candidates: &[ResourceEntryId],
    ) -> bool {
        if fact.memory_range().is_some() || fact.owned_quantity().is_none() {
            return false;
        }
        let algebra = resource_family_algebra(fact.family());
        // The first selected unit, the running constant total, and the units
        // merged so far. Each further unit is checked against the first with
        // the family's pair rule, so the check stays the size of one unit
        // while the total is kept as a constant.
        let mut first: Option<ResourceFact> = None;
        let mut total = 0_u32;
        let mut used = Vec::new();
        let mut seen = BTreeSet::new();
        for &entry in candidates {
            crate::instrumentation::record_deterministic_work(1);
            let unit = self.fact(entry);
            let Some(quantity) = unit.owned_quantity() else {
                continue;
            };
            if !seen.insert(entry)
                || !self.merged_unit_eligible(entry)
                || !unit.is_own()
                || unit.resource() != fact.resource()
            {
                continue;
            }
            if let Some(first) = &first
                && normalize_resource_fact_pair(first, unit, assumptions).is_none()
            {
                continue;
            }
            let Some(next_total) = total.checked_add(quantity) else {
                return false;
            };
            first.get_or_insert_with(|| unit.clone());
            total = next_total;
            used.push(entry);
            if used.len() < 2 {
                continue;
            }
            let merged = ResourceFact::own_quantity(
                fact.resource().clone(),
                OldMachineTerm::constant(total),
            );
            if let Some(ResourceFactConsumption::Replace(residual)) =
                algebra.consume(&merged, fact, assumptions)
            {
                for entry in &used {
                    let occurrence = self.occurrence(*entry);
                    if self
                        .storage
                        .expansions_by_support_occurrence
                        .contains_key(&occurrence)
                    {
                        *self = self
                            .clone()
                            .without_cached_supported_expansion_for_occurrence(occurrence);
                    }
                    self.remove_entry(*entry);
                }
                for residual in residual {
                    self.insert_fact(residual);
                }
                return true;
            }
        }
        false
    }

    fn consume_fact_from_candidates(
        &mut self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
        candidates: impl IntoIterator<Item = ResourceEntryId>,
    ) -> bool {
        self.consume_fact_from_candidates_with_origins(fact, assumptions, candidates, None)
    }

    fn consume_fact_from_candidates_with_origins(
        &mut self,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
        candidates: impl IntoIterator<Item = ResourceEntryId>,
        mut origins: Option<&mut MemorySplitOrigins>,
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
                if let Some(origins) = origins.as_deref_mut() {
                    origins.origins.remove(&self.occurrence(entry));
                }
                self.remove_entry(entry);
                return true;
            }
            let available = self.fact(entry);
            let Some(consumption) = algebra.consume(available, fact, assumptions) else {
                continue;
            };
            if let ResourceFactConsumption::Replace(residual) = consumption {
                let occurrence = self.occurrence(entry);
                let original = available.memory_own_range().and_then(|_| {
                    origins
                        .as_deref()
                        .map(|origins| origins.origin_of(occurrence))
                });
                if let Some(origins) = origins.as_deref_mut() {
                    origins.origins.remove(&occurrence);
                }
                self.remove_entry(entry);
                for residual in residual {
                    if residual.memory_own_range().is_some()
                        && let Some(original) = original
                        && let Some(origins) = origins.as_deref_mut()
                    {
                        let occurrence = ResourceOccurrenceId::fresh();
                        self.insert_fact_with_support_occurrence_and_metadata_at(
                            residual,
                            None,
                            None,
                            None,
                            Some(occurrence),
                        );
                        origins.origins.insert(occurrence, original);
                    } else {
                        self.insert_fact(residual);
                    }
                }
            }
            return true;
        }
        false
    }

    /// Forget the read authority an owned instance publishes for the cells
    /// its body owns. It is an observation of that instance, derived again
    /// wherever the instance is made, and carries no capability beyond
    /// holding it. Borrow-bound views stay. The work is the supported entries
    /// this context holds.
    pub(in crate::kernel) fn without_owned_instance_read_views(mut self) -> Self {
        if self.storage.supported_by.is_empty() {
            return self;
        }
        let entries = self
            .storage
            .supported_by
            .iter()
            .filter_map(|(entry, support)| {
                crate::instrumentation::record_deterministic_work(1);
                (matches!(support, ResourceFact::Own(Resource::Instance(_), _))
                    && self.fact(*entry).memory_view_range().is_some()
                    && self.borrow_dependency(self.occurrence(*entry)).is_none())
                .then_some(*entry)
            })
            .collect::<Vec<_>>();
        for entry in entries {
            self.remove_entry(entry);
        }
        self
    }

    /// Forget only observations and identity expansions of a memory owner.
    /// Neither carries a capability beyond that same owner. Live borrow-bound
    /// views and nontrivial supported descriptions remain distinct.
    pub(in crate::kernel) fn without_redundant_owned_memory_views(mut self) -> Self {
        let entries = self
            .storage
            .supported_by
            .iter()
            .filter_map(|(entry, support)| {
                crate::instrumentation::record_deterministic_work(1);
                let ResourceFact::View(Resource::Memory(range)) = self.fact(*entry) else {
                    return None;
                };
                let owned = support.memory_own_range()?;
                let occurrence = self.occurrence(*entry);
                (owned == range
                    && support.owned_quantity() == Some(1)
                    && self.borrow_dependency(occurrence).is_none())
                .then_some(*entry)
            })
            .collect::<Vec<_>>();
        for entry in entries {
            self.remove_entry(entry);
        }
        let identity_expansions = self
            .storage
            .expansions_by_support_occurrence
            .iter()
            .filter_map(|(occurrence, expansion)| {
                crate::instrumentation::record_deterministic_work(1);
                let entry = self.storage.entry_by_occurrence.get(occurrence)?;
                let support = self.fact(*entry);
                (support.memory_own_range().is_some()
                    && expansion.as_slice() == std::slice::from_ref(support))
                .then_some(*occurrence)
            })
            .collect::<Vec<_>>();
        for occurrence in identity_expansions {
            self = self.without_cached_supported_expansion_for_occurrence(occurrence);
        }
        self
    }

    /// Coalesce only the written neighbors reached by this insertion. Every
    /// successful iteration consumes one changed occurrence; unrelated facts,
    /// aliases, projections, and borrow dependencies retain their identities.
    pub(in crate::kernel) fn normalized_delta(
        mut self,
        inserted: Vec<(ResourceFact, ResourceOccurrenceId)>,
        assumptions: &PureFactContext,
    ) -> Self {
        for (_, occurrence) in inserted {
            let Some(mut entry) = self.storage.entry_by_occurrence.get(&occurrence).copied() else {
                continue;
            };
            loop {
                let fact = self.fact(entry).clone();
                if !self.delta_normalization_eligible(entry) {
                    break;
                }
                if fact.has_valid_exclusive_access() && fact.owned_quantity() == Some(0) {
                    self.remove_entry(entry);
                    break;
                }
                let mut merge = None;
                for candidate in self.written_normalization_candidates(entry, &fact) {
                    crate::instrumentation::record_deterministic_work(1);
                    if !self.delta_normalization_eligible(candidate)
                        || fact.is_own() && !self.fact(candidate).is_own()
                    {
                        continue;
                    }
                    if let Some(merged) =
                        normalize_resource_fact_pair(self.fact(candidate), &fact, assumptions)
                    {
                        merge = Some((candidate, merged));
                        break;
                    }
                }
                let Some((candidate, merged)) = merge else {
                    break;
                };
                // An absorbed view must not replace its unchanged owner.
                if &merged == self.fact(candidate) {
                    self.remove_entry(entry);
                    break;
                }
                if merged == fact {
                    self.remove_entry(candidate);
                    continue;
                }
                self.remove_entry(entry);
                self.remove_entry(candidate);
                entry = self.storage.next_entry_id;
                self.insert_fact(merged);
            }
        }
        self.advance_prepared_memory_equalities(assumptions);
        self
    }

    fn written_normalization_candidates(
        &self,
        entry: ResourceEntryId,
        fact: &ResourceFact,
    ) -> BTreeSet<ResourceEntryId> {
        let mut candidates: BTreeSet<_> = self
            .storage
            .index
            .written_normalization
            .candidates(entry, fact)
            .into_iter()
            .collect();
        if let Some(entries) = self.storage.index.by_resource.get(fact.resource()) {
            candidates.extend(entries.iter().take(2).copied());
        }
        if let Resource::Composite { name, arguments } | Resource::Token { name, arguments } =
            fact.resource()
            && let Some(entries) =
                self.storage
                    .index
                    .exact_shapes
                    .get(&(fact.family(), name.clone(), arguments.len()))
        {
            candidates.extend(entries.iter().take(2).copied());
        }
        if fact.is_own()
            && let Some(range) = fact.memory_own_range()
            && let Some((origin, start, end)) = constant_memory_coordinates(range)
            && let Some(count) = self
                .storage
                .index
                .concrete_memory_by_base
                .get(&(origin.clone(), true))
            && let Some(neighbors) = self.constant_owned_neighbors(&origin, start, end, *count)
        {
            candidates.extend(neighbors);
        }
        candidates.remove(&entry);
        candidates
    }

    /// A unit [`Self::consume_fact_from_merged_units`] may merge away: what
    /// delta normalization accepts, and also a unit whose only extra is a
    /// cached expansion of its body. That cache is derived again wherever it
    /// is needed and is dropped with the unit.
    fn merged_unit_eligible(&self, entry: ResourceEntryId) -> bool {
        let occurrence = self.occurrence(entry);
        !self.storage.supported_by.contains_key(&entry)
            && !self
                .storage
                .projections_by_support_occurrence
                .contains_key(&occurrence)
            && self.borrow_dependency(occurrence).is_none()
            && !self
                .structural_witnesses
                .as_ref()
                .is_some_and(|witnesses| witnesses.contains(occurrence))
    }

    fn delta_normalization_eligible(&self, entry: ResourceEntryId) -> bool {
        let occurrence = self.occurrence(entry);
        !self.storage.supported_by.contains_key(&entry)
            && !self
                .storage
                .projections_by_support_occurrence
                .contains_key(&occurrence)
            && !self
                .storage
                .expansions_by_support_occurrence
                .contains_key(&occurrence)
            && self.borrow_dependency(occurrence).is_none()
            && !self
                .structural_witnesses
                .as_ref()
                .is_some_and(|witnesses| witnesses.contains(occurrence))
    }

    pub(in crate::kernel) fn normalized(self, assumptions: &PureFactContext) -> Self {
        self.normalized_with_byte_endpoints(assumptions, false, false)
    }

    /// Optional coalescing of one explicit constructed body. Only written
    /// endpoints and exact resources nominate one neighbour per key. Missing
    /// an alias-based merge retains both valid facts; it does not start search.
    pub(in crate::kernel) fn normalized_without_discovery(
        self,
        assumptions: &PureFactContext,
    ) -> Self {
        #[cfg(test)]
        let _fast = crate::kernel::search::FastOperationScope::enter(
            "bounded constructed return normalization",
        );
        self.normalized_with_byte_endpoints(assumptions, false, true)
    }

    // Bytewise regrouping belongs to explicitly selected memory suppliers.
    // Ambient normalization preserves the representation of borrowed clauses.
    fn normalized_with_byte_endpoints(
        mut self,
        assumptions: &PureFactContext,
        byte_endpoints: bool,
        written_only: bool,
    ) -> Self {
        // One retained nonzero fact has no partner to coalesce. Preserve the
        // normalizer's input attachment, but do not discover alias/endpoint
        // candidates for a merge that cannot exist. Zero units still take
        // the ordinary cleanup path below.
        if self.storage.facts.len() <= 1
            && !self.storage.facts.iter().next().is_some_and(|(_, fact)| {
                fact.has_valid_exclusive_access() && fact.owned_quantity() == Some(0)
            })
        {
            self.synchronize_memory_equalities(assumptions);
            return self;
        }
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
            // Each removal above advanced the observable projection; clearing
            // the expansion caches advances it too, so a normalization that
            // restores the same supported pairs below keeps the warm view
            // instead of leaving every later observation to recompute it.
            let previous = self.storage.clone();
            self.clear_cached_support_expansions();
            self.advance_observable_expansions_cleared(&previous);
            return self
                .normalized_with_byte_endpoints(assumptions, byte_endpoints, written_only)
                .restore_supported_projection_pairs(supported)
                .restore_cached_support_expansions(expansions);
        }
        let mut changed_facts = BTreeSet::new();
        let retained = self
            .storage
            .facts
            .iter()
            .filter_map(|(entry, fact)| {
                if fact.has_valid_exclusive_access() && fact.owned_quantity() == Some(0) {
                    changed_facts.insert(fact.clone());
                    None
                } else {
                    Some((Some(self.occurrence(*entry)), fact.clone()))
                }
            })
            .collect::<Vec<_>>();
        #[cfg(test)]
        WHOLE_NORMALIZATION_FACTS.with(|count| count.set(count.get() + retained.len()));
        let mut slots = retained.iter().cloned().map(Some).collect::<Vec<_>>();
        let mut index = ResourceNormalizationIndex {
            byte_endpoints,
            written_only,
            ..Default::default()
        };
        for (position, (_, fact)) in retained.iter().enumerate() {
            index.insert(position, fact);
        }
        // A merged fact is a new authority with no occurrence, so merging a
        // borrow-bound view would silently discard the dependency that
        // authorizes reading it. Under stable-borrow semantics the split
        // representation is the checked one; keep it. The map is empty under
        // legacy semantics, so this costs nothing and changes nothing there.
        let borrow_bound = |occurrence: &Option<ResourceOccurrenceId>| {
            occurrence.is_some_and(|occurrence| {
                self.borrow_dependencies.map.get(&occurrence).is_some()
                    || self
                        .structural_witnesses
                        .as_ref()
                        .is_some_and(|witnesses| witnesses.contains(occurrence))
            })
        };
        let mut i = 0;
        while i < slots.len() {
            let Some((occurrence, fact)) = slots[i].clone() else {
                i += 1;
                continue;
            };
            if borrow_bound(&occurrence) {
                i += 1;
                continue;
            }
            let mut changed = false;
            for j in index.candidates_after(i, &fact, assumptions) {
                crate::instrumentation::record_deterministic_work(1);
                let Some((right_occurrence, right)) = slots[j].as_ref() else {
                    continue;
                };
                if borrow_bound(right_occurrence) {
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
        if !changed_facts.is_empty() {
            self.replace_facts(slots.into_iter().flatten(), changed_facts);
        }
        // Normalization already visits the complete input, so it is an
        // attachment boundary even when no resource representation changed.
        // Delta-only composition must never do this for an ambient context.
        self.synchronize_memory_equalities(assumptions);
        self
    }

    fn supported_projection_pairs(
        &self,
    ) -> Vec<(
        Option<ResourceOccurrenceId>,
        ResourceFact,
        ResourceFact,
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
            ResourceFact,
            ResourceFact,
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

    fn cached_support_expansions(&self) -> Vec<(ResourceOccurrenceId, Vec<ResourceFact>)> {
        self.storage
            .expansions_by_support_occurrence
            .iter()
            .map(|(support_occurrence, expansion)| {
                (*support_occurrence, expansion.as_ref().clone())
            })
            .collect()
    }

    /// Replace the storage root with one holding no cached support
    /// expansions, leaving every fact, entry, occurrence and support index in
    /// place. The caller advances the observable projection.
    fn clear_cached_support_expansions(&mut self) {
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.clone(),
            next_entry_id: self.storage.next_entry_id,
            occurrence_by_entry: self.storage.occurrence_by_entry.clone(),
            entry_by_occurrence: self.storage.entry_by_occurrence.clone(),
            index: self.storage.index.clone(),
            supported_by: self.storage.supported_by.clone(),
            nonmemory_projections_by_fact: self.storage.nonmemory_projections_by_fact.clone(),
            principal_views_by_fact: self.storage.principal_views_by_fact.clone(),
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
            unknown_memory_support: self.storage.unknown_memory_support.clone(),
            symbolic_memory_support: self.storage.symbolic_memory_support.clone(),
            expansions_by_support_occurrence: PersistentMap::default(),
            expansions_by_support_entry: PersistentMap::default(),
            origin: self.storage.origin.clone(),
            history: self.storage.history.clone(),
            observable_projection_source: None,
            materialized: std::sync::OnceLock::new(),
        });
    }

    fn restore_cached_support_expansions(
        mut self,
        expansions: Vec<(ResourceOccurrenceId, Vec<ResourceFact>)>,
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

/// Fixed literals retain the old constant-time key path; only compound
/// endpoints need the memoized syntax fingerprint. Neither variant is evidence.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum WideNormalizationEndpointKey {
    Constant(u64),
    Syntax(u64),
}

fn wide_normalization_endpoint_key(view: MachineOperandView<'_>) -> WideNormalizationEndpointKey {
    match view.uint64_constant() {
        Some(value) => WideNormalizationEndpointKey::Constant(value),
        None => WideNormalizationEndpointKey::Syntax(
            crate::kernel::assumptions::machine_syntax_fingerprint(view),
        ),
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ResourceNormalizationKey {
    Instance(InstanceId),
    TrackedResource(Resource),
    ExactShape(ResourceFamily, String, usize),
    /// A token or composite whose first argument is a pointer into a block
    /// proven distinct from every block but itself and a symbolic one.
    ExactShapeAnchored(ResourceFamily, String, usize, AddressBase),
    /// Every anchored token or composite of one shape, for the unanchored
    /// facts that may still name the same block.
    ExactShapeAnchoredAll(ResourceFamily, String, usize),
    /// A token or composite whose first argument is a pointer into any other
    /// block, keyed by that pointer's [`memory_base_root`]. Every parameter
    /// shares the one argument block, so keying by block alone would pair
    /// each parameter's facts with every other parameter's.
    ExactShapeRooted(ResourceFamily, String, usize, MemoryBaseRoot),
    /// Every rooted token or composite of one shape, for the facts whose
    /// first argument is not such a pointer.
    ExactShapeRootedAll(ResourceFamily, String, usize),
    MemoryStart(MemoryBaseRoot, bool, SharedMachineIntegerTerm),
    MemoryEnd(MemoryBaseRoot, bool, SharedMachineIntegerTerm),
    // Native adjacency retains the exact base and width plus a compact,
    // state-sensitive endpoint fingerprint. These keys only propose pairs;
    // the existing merge rule remains authoritative (including collisions).
    MemoryNativeStart(Address, u32, bool, WideNormalizationEndpointKey),
    MemoryNativeEnd(Address, u32, bool, WideNormalizationEndpointKey),
    MemoryByteStart(MemoryBaseRoot, bool, i64),
    MemoryByteEnd(MemoryBaseRoot, bool, i64),
    /// A field of a symbolic object: the object with that field as a hole,
    /// and the field's own range, meet here to be joined again.
    SymbolicField(Address, crate::kernel::SymbolicLayoutName, u32, bool),
}

/// The [`ResourceNormalizationKey::SymbolicField`] keys of `fact`: one per
/// hole of a symbolic object, or the one of a whole field's range.
fn symbolic_field_keys(fact: &ResourceFact) -> Vec<ResourceNormalizationKey> {
    let Some(range) = fact.memory_range() else {
        return Vec::new();
    };
    if let Some(layout) = range.symbolic_object() {
        return range
            .holes()
            .iter()
            .map(|hole| {
                ResourceNormalizationKey::SymbolicField(
                    range.base().clone(),
                    layout,
                    *hole,
                    fact.is_own(),
                )
            })
            .collect();
    }
    range
        .symbolic_field()
        .map(|(object, layout, field)| {
            ResourceNormalizationKey::SymbolicField(object, layout, field, fact.is_own())
        })
        .into_iter()
        .collect()
}

/// Written normalization candidates are maintained with each resource delta.
/// Querying a key nominates at most two entries (one may be the query itself).
/// A missed or borrow-bound nominee leaves the split representation intact.
#[derive(Clone, Debug, Default)]
pub(super) struct WrittenNormalizationIndex {
    entries: PersistentMap<(ResourceNormalizationKey, bool), ResourceEntryIds>,
}

impl WrittenNormalizationIndex {
    fn keys(fact: &ResourceFact) -> Vec<ResourceNormalizationKey> {
        let Some(range) = fact.memory_range() else {
            return Vec::new();
        };
        // Constant ranges meet through the concrete index, except a field of
        // a symbolic object, whose object is no constant range.
        // Constant ranges meet through the concrete index, except a field of
        // a symbolic object, whose object is no constant range.
        if constant_memory_coordinates(range).is_some() {
            return symbolic_field_keys(fact);
        }
        ResourceNormalizationIndex {
            byte_endpoints: true,
            written_only: true,
            ..Default::default()
        }
        .keys(fact)
        .into_iter()
        .filter(|key| {
            matches!(
                key,
                ResourceNormalizationKey::MemoryStart(..)
                    | ResourceNormalizationKey::MemoryEnd(..)
                    | ResourceNormalizationKey::MemoryNativeStart(..)
                    | ResourceNormalizationKey::MemoryNativeEnd(..)
                    | ResourceNormalizationKey::MemoryByteStart(..)
                    | ResourceNormalizationKey::MemoryByteEnd(..)
                    | ResourceNormalizationKey::SymbolicField(..)
            )
        })
        .collect()
    }

    fn insert(&mut self, entry: ResourceEntryId, fact: &ResourceFact) {
        for key in Self::keys(fact) {
            self.entries = insert_resource_index_entry(&self.entries, (key, fact.is_own()), entry);
        }
    }

    fn remove(&mut self, entry: ResourceEntryId, fact: &ResourceFact) {
        for key in Self::keys(fact) {
            self.entries = remove_resource_index_entry(&self.entries, &(key, fact.is_own()), entry);
        }
    }

    fn candidates(&self, entry: ResourceEntryId, fact: &ResourceFact) -> Vec<ResourceEntryId> {
        let mut candidates = BTreeSet::new();
        for key in Self::keys(fact) {
            use ResourceNormalizationKey::*;
            let complementary = match key {
                MemoryStart(base, own, position) => MemoryEnd(base, own, position),
                MemoryEnd(base, own, position) => MemoryStart(base, own, position),
                MemoryNativeStart(base, width, own, position) => {
                    MemoryNativeEnd(base, width, own, position)
                }
                MemoryNativeEnd(base, width, own, position) => {
                    MemoryNativeStart(base, width, own, position)
                }
                MemoryByteStart(base, own, position) => MemoryByteEnd(base, own, position),
                MemoryByteEnd(base, own, position) => MemoryByteStart(base, own, position),
                key => key,
            };
            for own in [fact.is_own(), !fact.is_own()] {
                // An inserted owner does not consume ambient observations.
                // Inserting a view may still be absorbed by an existing owner.
                if fact.is_own() && !own {
                    continue;
                }
                if let Some(entries) = self.entries.get(&(complementary.clone(), own)) {
                    candidates.extend(
                        entries
                            .iter()
                            .take(2)
                            .copied()
                            .filter(|candidate| *candidate != entry),
                    );
                }
            }
        }
        candidates.into_iter().collect()
    }
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
///
/// A symbolic base keeps element units, counted from its root (the base
/// without its displacement), so a piece a call returns over `x + i` or
/// `x + 1` meets the pieces of `x` it abuts. The key only proposes a pair;
/// [`merge_memory_ranges`] decides it exactly.
fn memory_normalization_position(
    range: &MemoryRange,
    bound: MachineOperandView<'_>,
) -> SharedMachineIntegerTerm {
    let byte_position = || -> Option<SharedMachineIntegerTerm> {
        let base = range.base().offset.as_const()?;
        let elements = crate::kernel::assumptions::signed_index_constant(bound)?;
        let byte = base.checked_add(elements.checked_mul(i64::from(range.element_width()))?)?;
        Some(
            MachineOperandView::Old(&OldMachineTerm::constant(i32::try_from(byte).ok()? as u32))
                .retain(MachineIntegerType::Int32),
        )
    };
    let root_position = || -> Option<SharedMachineIntegerTerm> {
        let (block, atom) = memory_base_root(range.base());
        let root = Address::new(block, atom?);
        if range.base() == &root {
            return None;
        }
        let delta =
            range
                .base()
                .exact_element_delta_from_base(&root, range.element_width(), None)?;
        let constant = i32::try_from(delta.constant).ok()? as u32;
        Some(crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Add,
            crate::kernel::assumptions::index_binary(
                MachineBinaryOp::Add,
                delta.index.operand_view(),
                bound,
            )
            .operand_view(),
            MachineOperandView::Old(&OldMachineTerm::constant(constant)),
        ))
    };
    byte_position()
        .or_else(root_position)
        .unwrap_or_else(|| bound.retain(MachineIntegerType::Int32))
}

/// Constant endpoints also meet in bytes relative to a symbolic object root.
/// Element-unit keys alone cannot pair a returned scalar with bytewise padding.
/// These keys only select candidates; merging still checks exact adjacency.
fn memory_normalization_relative_byte_position(
    range: &MemoryRange,
    bound: MachineOperandView<'_>,
) -> Option<i64> {
    let elements = crate::kernel::assumptions::signed_index_constant(bound)?;
    let displacement = match memory_base_root(range.base()).1 {
        Some(offset) => {
            let root = range.base().with_offset(offset);
            let delta = range.base().exact_element_delta_from_base(&root, 1, None)?;
            delta
                .constant
                .checked_add(crate::kernel::assumptions::signed_index_constant(
                    delta.index.operand_view(),
                )?)?
        }
        None => range.base().offset.as_const()?,
    };
    displacement.checked_add(elements.checked_mul(i64::from(range.element_width()))?)
}

#[derive(Default)]
struct ResourceNormalizationIndex {
    byte_endpoints: bool,
    written_only: bool,
    positions: BTreeMap<ResourceNormalizationKey, BTreeSet<usize>>,
}

impl ResourceNormalizationIndex {
    fn keys(&self, fact: &ResourceFact) -> Vec<ResourceNormalizationKey> {
        let mut keys = vec![ResourceNormalizationKey::TrackedResource(
            fact.resource().clone(),
        )];
        keys.extend(symbolic_field_keys(fact));
        match fact.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
            }
            Resource::Instance(instance) => {
                keys.push(ResourceNormalizationKey::Instance(instance.identity))
            }
            Resource::ConditionalMutexGuard(carrier) => {
                keys.push(ResourceNormalizationKey::Instance(carrier.identity))
            }
            Resource::PopulationAuthority(_)
            | Resource::Iterated(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_) => {}
            Resource::Memory(range) if range.wide_bounds().is_some() => {
                if let Some((base, start, end)) = native_wide_normalization_key(range) {
                    keys.push(ResourceNormalizationKey::MemoryNativeStart(
                        base.clone(),
                        range.element_width(),
                        fact.is_own(),
                        start,
                    ));
                    keys.push(ResourceNormalizationKey::MemoryNativeEnd(
                        base,
                        range.element_width(),
                        fact.is_own(),
                        end,
                    ));
                }
            }
            Resource::Memory(range) => {
                // A window at a 64-bit index from its root, a piece a call
                // handed back, also meets its wide neighbours there, and so
                // does a constant piece at the root itself.
                if let Some((base, start, end)) = native_wide_normalization_key(range) {
                    keys.push(ResourceNormalizationKey::MemoryNativeStart(
                        base.clone(),
                        range.element_width(),
                        fact.is_own(),
                        start,
                    ));
                    keys.push(ResourceNormalizationKey::MemoryNativeEnd(
                        base,
                        range.element_width(),
                        fact.is_own(),
                        end,
                    ));
                }
                if self.byte_endpoints
                    && let Some(start) = memory_normalization_relative_byte_position(
                        range,
                        MachineOperandView::Old(range.start()),
                    )
                {
                    keys.push(ResourceNormalizationKey::MemoryByteStart(
                        memory_base_root(range.base()),
                        fact.is_own(),
                        start,
                    ));
                }
                if self.byte_endpoints
                    && let Some(end) = memory_normalization_relative_byte_position(
                        range,
                        MachineOperandView::Old(range.end()),
                    )
                {
                    keys.push(ResourceNormalizationKey::MemoryByteEnd(
                        memory_base_root(range.base()),
                        fact.is_own(),
                        end,
                    ));
                }
                keys.push(ResourceNormalizationKey::MemoryStart(
                    memory_base_root(range.base()),
                    fact.is_own(),
                    memory_normalization_position(range, MachineOperandView::Old(range.start())),
                ));
                keys.push(ResourceNormalizationKey::MemoryEnd(
                    memory_base_root(range.base()),
                    fact.is_own(),
                    memory_normalization_position(range, MachineOperandView::Old(range.end())),
                ));
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
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
                    None => match normalization_root_pointer(arguments) {
                        Some(pointer) => {
                            keys.push(ResourceNormalizationKey::ExactShapeRooted(
                                shape.0,
                                shape.1.clone(),
                                shape.2,
                                memory_base_root(pointer),
                            ));
                            keys.push(ResourceNormalizationKey::ExactShapeRootedAll(
                                shape.0, shape.1, shape.2,
                            ));
                        }
                        None => keys.push(ResourceNormalizationKey::ExactShape(
                            shape.0, shape.1, shape.2,
                        )),
                    },
                }
            }
        }
        keys
    }

    fn insert(&mut self, position: usize, fact: &ResourceFact) {
        for key in self.keys(fact) {
            self.positions.entry(key).or_default().insert(position);
        }
    }

    fn remove(&mut self, position: usize, fact: &ResourceFact) {
        for key in self.keys(fact) {
            if let Some(positions) = self.positions.get_mut(&key) {
                positions.remove(&position);
            }
        }
    }

    /// The facts after `position` that may normalize with `fact`.
    ///
    /// A memory range meets the ranges whose end is its start and whose start
    /// is its end. Those endpoints are looked up as written and under every
    /// spelling an exact equality premise joins to them, because
    /// [`merge_memory_ranges`] merges two ranges that abut by a proved
    /// equality: `data[0..n]` and `data[m..4]` under `n == m` are one range,
    /// and a lookup by the written spelling alone would never offer them to
    /// each other. The extra lookups cost the endpoint's equality class.
    /// SymbolicMemory keys also include the base root and its recorded aliases: an
    /// endpoint such as zero alone must not pair every external object with
    /// every other object in the same block.
    fn candidates_after(
        &self,
        position: usize,
        fact: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Vec<usize> {
        let mut keys = vec![ResourceNormalizationKey::TrackedResource(
            fact.resource().clone(),
        )];
        keys.extend(symbolic_field_keys(fact));
        match fact.resource() {
            Resource::Memory(range) if self.written_only => {
                if let Some((base, start, end)) = native_wide_normalization_key(range) {
                    keys.push(ResourceNormalizationKey::MemoryNativeEnd(
                        base.clone(),
                        range.element_width(),
                        fact.is_own(),
                        start,
                    ));
                    keys.push(ResourceNormalizationKey::MemoryNativeStart(
                        base,
                        range.element_width(),
                        fact.is_own(),
                        end,
                    ));
                }
                if range.wide_bounds().is_none() {
                    keys.push(ResourceNormalizationKey::MemoryEnd(
                        memory_base_root(range.base()),
                        fact.is_own(),
                        memory_normalization_position(
                            range,
                            MachineOperandView::Old(range.start()),
                        ),
                    ));
                    keys.push(ResourceNormalizationKey::MemoryStart(
                        memory_base_root(range.base()),
                        fact.is_own(),
                        memory_normalization_position(range, MachineOperandView::Old(range.end())),
                    ));
                }
            }
            _ if self.written_only => {}
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
            }
            Resource::Instance(instance) => {
                keys.push(ResourceNormalizationKey::Instance(instance.identity))
            }
            Resource::ConditionalMutexGuard(carrier) => {
                keys.push(ResourceNormalizationKey::Instance(carrier.identity))
            }
            Resource::PopulationAuthority(_)
            | Resource::Iterated(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_) => {}
            Resource::Memory(range) if range.wide_bounds().is_some() => {
                if let Some((base, start, end)) = native_wide_normalization_key(range) {
                    keys.push(ResourceNormalizationKey::MemoryNativeEnd(
                        base.clone(),
                        range.element_width(),
                        fact.is_own(),
                        start,
                    ));
                    keys.push(ResourceNormalizationKey::MemoryNativeStart(
                        base,
                        range.element_width(),
                        fact.is_own(),
                        end,
                    ));
                }
            }
            Resource::Memory(range) => {
                if let Some((base, start, end)) = native_wide_normalization_key(range) {
                    keys.push(ResourceNormalizationKey::MemoryNativeEnd(
                        base.clone(),
                        range.element_width(),
                        fact.is_own(),
                        start,
                    ));
                    keys.push(ResourceNormalizationKey::MemoryNativeStart(
                        base,
                        range.element_width(),
                        fact.is_own(),
                        end,
                    ));
                }
                let roots = related_pointer_roots(range.base(), assumptions);
                let owned = fact.is_own();
                let start_members = assumptions.bitvector_equality_class_view(range.start());
                for start in std::iter::once(MachineOperandView::Old(range.start())).chain(
                    start_members.iter().map(|member| {
                        member
                            .retained_written_operand()
                            .map(MachineOperandView::Old)
                            .unwrap_or_else(|| member.operand_view())
                    }),
                ) {
                    for root in &roots {
                        if self.byte_endpoints
                            && let Some(byte) =
                                memory_normalization_relative_byte_position(range, start)
                        {
                            keys.push(ResourceNormalizationKey::MemoryByteEnd(
                                root.clone(),
                                owned,
                                byte,
                            ));
                        }
                        keys.push(ResourceNormalizationKey::MemoryEnd(
                            root.clone(),
                            owned,
                            memory_normalization_position(range, start),
                        ));
                    }
                }
                let end_members = assumptions.bitvector_equality_class_view(range.end());
                for end in std::iter::once(MachineOperandView::Old(range.end())).chain(
                    end_members.iter().map(|member| {
                        member
                            .retained_written_operand()
                            .map(MachineOperandView::Old)
                            .unwrap_or_else(|| member.operand_view())
                    }),
                ) {
                    for root in &roots {
                        if self.byte_endpoints
                            && let Some(byte) =
                                memory_normalization_relative_byte_position(range, end)
                        {
                            keys.push(ResourceNormalizationKey::MemoryByteStart(
                                root.clone(),
                                owned,
                                byte,
                            ));
                        }
                        keys.push(ResourceNormalizationKey::MemoryStart(
                            root.clone(),
                            owned,
                            memory_normalization_position(range, end),
                        ));
                    }
                }
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                // Two facts of one shape merge only when their arguments are
                // proven equal, and a pointer is never proven equal to one in
                // a block proven distinct from its own. So an anchored fact
                // meets the facts anchored in its own block and the
                // unanchored ones. A fact rooted at another pointer meets the
                // facts rooted where its pointer is related, as memory
                // ranges do, plus the anchored and pointerless ones. A
                // pointerless fact meets every fact of its shape.
                let shape = (fact.family(), name.clone(), arguments.len());
                keys.push(ResourceNormalizationKey::ExactShape(
                    shape.0,
                    shape.1.clone(),
                    shape.2,
                ));
                match normalization_anchor(arguments) {
                    Some(block) => {
                        keys.push(ResourceNormalizationKey::ExactShapeAnchored(
                            shape.0,
                            shape.1.clone(),
                            shape.2,
                            block.clone(),
                        ));
                        keys.push(ResourceNormalizationKey::ExactShapeRootedAll(
                            shape.0, shape.1, shape.2,
                        ));
                    }
                    None => {
                        keys.push(ResourceNormalizationKey::ExactShapeAnchoredAll(
                            shape.0,
                            shape.1.clone(),
                            shape.2,
                        ));
                        match normalization_root_pointer(arguments) {
                            Some(pointer) => {
                                for root in related_pointer_roots(pointer, assumptions) {
                                    keys.push(ResourceNormalizationKey::ExactShapeRooted(
                                        shape.0,
                                        shape.1.clone(),
                                        shape.2,
                                        root,
                                    ));
                                }
                            }
                            None => keys.push(ResourceNormalizationKey::ExactShapeRootedAll(
                                shape.0, shape.1, shape.2,
                            )),
                        }
                    }
                }
            }
        }
        let mut candidates = BTreeSet::new();
        for key in keys {
            if let Some(positions) = self.positions.get(&key) {
                if self.written_only {
                    candidates.extend(positions.range((position + 1)..).next().copied());
                } else {
                    candidates.extend(positions.range((position + 1)..).copied());
                }
            }
        }
        candidates.into_iter().collect()
    }
}

fn prepared_argument_resource_blocks(fact: &ResourceFact) -> impl Iterator<Item = &AddressBase> {
    let arguments = match fact.resource() {
        Resource::Instance(instance) => Some(&instance.arguments),
        Resource::Composite { arguments, .. } | Resource::Token { arguments, .. } => {
            Some(arguments)
        }
        _ => None,
    };
    arguments
        .into_iter()
        .flat_map(algebraic_pointer_arguments)
        .map(|pointer| &pointer.base)
        .filter(|block| block.prepared_argument_binding().is_some())
}

/// The C pointer arguments of an instance, as its index keys them.
fn instance_pointer_arguments(instance: &ResourceInstance) -> impl Iterator<Item = &Address> {
    algebraic_pointer_arguments(&instance.arguments)
}

/// The C pointer arguments among `arguments`, in order.
fn algebraic_pointer_arguments(arguments: &ResourceArguments) -> impl Iterator<Item = &Address> {
    arguments.iter().filter_map(|argument| match argument {
        ResourceFieldValue::Program(ProgramValue::Pointer(pointer)) => Some(pointer.address()),
        _ => None,
    })
}

/// Coalesce an explicit description list without constructing ownership or
/// resource indexes. This is representation only: callers retain the source
/// partition/occurrence evidence, and no ambient context is inspected.
pub(crate) fn coalesce_written_resource_descriptions(
    facts: Vec<ResourceFact>,
    assumptions: &PureFactContext,
) -> Vec<ResourceFact> {
    #[cfg(test)]
    let _fast = crate::kernel::search::FastOperationScope::enter(
        "bounded constructed description normalization",
    );
    let mut index = ResourceNormalizationIndex {
        byte_endpoints: false,
        written_only: true,
        ..Default::default()
    };
    let mut slots = facts
        .into_iter()
        .map(|fact| {
            crate::instrumentation::record_deterministic_work(1);
            // An empty owned range has no footprint to publish, including
            // when a field supplies an endpoint proved equal to the other.
            if fact.has_valid_exclusive_access()
                && (fact.owned_quantity() == Some(0)
                    || fact
                        .memory_own_range()
                        .is_some_and(|range| memory_range_is_proven_empty(range, assumptions)))
            {
                None
            } else {
                Some(fact)
            }
        })
        .collect::<Vec<_>>();
    for (position, fact) in slots.iter().enumerate() {
        if let Some(fact) = fact {
            index.insert(position, fact);
        }
    }
    let mut position = 0;
    while position < slots.len() {
        let Some(left) = slots[position].clone() else {
            position += 1;
            continue;
        };
        let mut changed = false;
        for candidate in index.candidates_after(position, &left, assumptions) {
            crate::instrumentation::record_deterministic_work(1);
            let Some(right) = slots[candidate].as_ref() else {
                continue;
            };
            if let Some(merged) = normalize_resource_fact_pair(&left, right, assumptions) {
                index.remove(position, &left);
                index.remove(candidate, right);
                slots[candidate] = None;
                index.insert(position, &merged);
                slots[position] = Some(merged);
                changed = true;
                break;
            }
        }
        if !changed {
            position += 1;
        }
    }
    slots.into_iter().flatten().collect()
}

/// The block of a token or composite's first argument when that argument is
/// a pointer into a heap or temporary block. `AddressBase::proven_distinct`
/// separates such a block from every block except itself and a symbolic one,
/// with no assumption able to override it, so two facts anchored in
/// different blocks can never have their first arguments proven equal and
/// never normalize together.
fn normalization_anchor(arguments: &ResourceArguments) -> Option<&AddressBase> {
    match arguments.first() {
        Some(ResourceFieldValue::Program(ProgramValue::Pointer(pointer)))
            if matches!(
                pointer.address().base,
                AddressBase::Heap(_) | AddressBase::Temporary(_)
            ) =>
        {
            Some(&pointer.address().base)
        }
        _ => None,
    }
}

fn heap_anchored_composite_key(fact: &ResourceFact) -> Option<(String, ProgramType)> {
    let Resource::Composite { name, arguments } = fact.resource() else {
        return None;
    };
    let [ResourceFieldValue::Program(ProgramValue::Pointer(pointer))] =
        arguments.fixed_values::<1>()?
    else {
        return None;
    };
    (fact.owned_quantity() == Some(1) && matches!(pointer.address().base, AddressBase::Heap(_)))
        .then(|| (name.clone(), pointer.program_type()))
}

/// The `exact_shapes_by_root` key of a token or composite.
fn shape_root_key(
    family: ResourceFamily,
    name: &str,
    arguments: &ResourceArguments,
) -> super::ShapeRootKey {
    (
        family,
        name.to_string(),
        arguments.len(),
        normalization_root_pointer(arguments).map(memory_base_root),
    )
}

/// The bucket a non-memory fact is matched in by
/// `direct_match_candidate_positions`, as a key: two facts one can entail
/// share it, so a context can list compositions under their non-memory
/// owned members (`CompositionMemberIndex`). SymbolicMemory has none; its members
/// are listed by block.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::kernel) enum OwnedMemberKey {
    TrackedResource(Resource),
    Instance(InstanceId),
    IteratedBlock(AddressBase),
    Shape(ResourceFamily, String, usize),
    /// A token or composite's shape and first-pointer root, the narrower
    /// bucket `direct_match_candidates_for` reads.
    ShapeRoot(super::ShapeRootKey),
}

impl OwnedMemberKey {
    pub(in crate::kernel) fn of(fact: &ResourceFact) -> Option<Self> {
        Some(match fact.resource() {
            resource @ (Resource::Footprint(_)
            | Resource::Parameter(_)
            | Resource::Emp
            | Resource::Star(_)) => Self::TrackedResource(resource.clone()),
            Resource::Memory(_) => return None,
            resource @ (Resource::PopulationAuthority(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)) => Self::TrackedResource(resource.clone()),
            Resource::Instance(instance) => Self::Instance(instance.identity),
            Resource::Iterated(iterated) => Self::IteratedBlock(iterated.element_base.base.clone()),
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                Self::Shape(fact.family(), name.clone(), arguments.len())
            }
        })
    }

    /// The keys a composition is listed under for its owned member `fact`:
    /// its bucket and, for a token or composite, its shape and root too.
    pub(in crate::kernel) fn listed(fact: &ResourceFact) -> Vec<Self> {
        let mut keys = Vec::from_iter(Self::of(fact));
        if let Resource::Composite { name, arguments } | Resource::Token { name, arguments } =
            fact.resource()
        {
            keys.push(Self::ShapeRoot(shape_root_key(
                fact.family(),
                name,
                arguments,
            )));
        }
        keys
    }

    /// The narrowest key a composition lists an owned member equal to
    /// `fact` under.
    pub(in crate::kernel) fn exact(fact: &ResourceFact) -> Option<Self> {
        match fact.resource() {
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => Some(
                Self::ShapeRoot(shape_root_key(fact.family(), name, arguments)),
            ),
            _ => Self::of(fact),
        }
    }

    /// The keys under which every owned member that can entail `view` is
    /// listed. A token or composite whose first argument is a pointer reads
    /// the roots `direct_match_candidates_for` reads, and the root-free key
    /// of members whose first argument is not a pointer; other facts read
    /// their bucket.
    pub(in crate::kernel) fn probed(
        view: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Vec<Self> {
        let (Resource::Composite { name, arguments } | Resource::Token { name, arguments }) =
            view.resource()
        else {
            return Vec::from_iter(Self::of(view));
        };
        let Some(pointer) = normalization_root_pointer(arguments) else {
            return Vec::from_iter(Self::of(view));
        };
        std::iter::once(None)
            .chain(
                related_pointer_roots(pointer, assumptions)
                    .into_iter()
                    .map(Some),
            )
            .map(|root| {
                crate::instrumentation::record_deterministic_work(1);
                Self::ShapeRoot((view.family(), name.clone(), arguments.len(), root))
            })
            .collect()
    }
}

/// The first argument of a token or composite when it is a pointer.
fn normalization_root_pointer(arguments: &ResourceArguments) -> Option<&Address> {
    match arguments.first() {
        Some(ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) => {
            Some(pointer.address())
        }
        _ => None,
    }
}

/// The blocks of `pointer`'s related roots and its own: the blocks of the
/// owned members `proves_owned_memory_ranges_separate_by` can find for a
/// range at `pointer`, so the compositions `CompositionMemberIndex` lists
/// under them are the ones that can answer it.
pub(in crate::kernel) fn related_pointer_root_blocks(
    pointer: &Address,
    assumptions: &PureFactContext,
) -> BTreeSet<AddressBase> {
    let mut blocks = BTreeSet::from([pointer.base.clone()]);
    blocks.extend(
        related_pointer_roots(pointer, assumptions)
            .into_iter()
            .map(|(block, _)| block),
    );
    blocks
}

/// The roots a normalization lookup visits for a pointer: its related roots
/// and those of its recorded exact aliases.
fn related_pointer_roots(
    pointer: &Address,
    assumptions: &PureFactContext,
) -> BTreeSet<MemoryBaseRoot> {
    // Aliases of one pointer usually have indexes in one equality class;
    // `walked` lets that class be walked once rather than once per alias.
    let mut roots = BTreeSet::new();
    let mut walked = BTreeSet::new();
    extend_related_memory_base_roots(pointer, assumptions, &mut roots, &mut walked);
    // A loaded pointer's root has no index atom to walk, so equal values
    // spelled in other load blocks are reached through the alias class.
    for alias in assumptions.pointer_alias_class(pointer) {
        extend_related_memory_base_roots(&alias, assumptions, &mut roots, &mut walked);
    }
    for alias in assumptions.exact_pointer_offset_aliases(pointer) {
        extend_related_memory_base_roots(&alias, assumptions, &mut roots, &mut walked);
    }
    roots
}

fn resource_family_algebra(family: ResourceFamily) -> &'static dyn ResourceFamilyAlgebra {
    let algebra: &'static dyn ResourceFamilyAlgebra = match family {
        ResourceFamily::Parameter => {
            panic!("a theorem resource descriptor is not an ownership fact")
        }
        ResourceFamily::Memory => &MEMORY_RESOURCE_ALGEBRA,
        ResourceFamily::PopulationAuthority => &POPULATION_AUTHORITY_RESOURCE_ALGEBRA,
        ResourceFamily::Composite => &COMPOSITE_RESOURCE_ALGEBRA,
        ResourceFamily::Token => &TOKEN_RESOURCE_ALGEBRA,
        ResourceFamily::Instance => &INSTANCE_RESOURCE_ALGEBRA,
        ResourceFamily::MutexGuard => &MUTEX_GUARD_RESOURCE_ALGEBRA,
        ResourceFamily::MutexLive => &MUTEX_LIVE_RESOURCE_ALGEBRA,
        ResourceFamily::MutexUse => &MUTEX_USE_RESOURCE_ALGEBRA,
        ResourceFamily::Iterated => &ITERATED_RESOURCE_ALGEBRA,
        ResourceFamily::Publication => &PUBLICATION_RESOURCE_ALGEBRA,
    };
    debug_assert_eq!(algebra.family(), family);
    algebra
}

pub(super) fn validate_resource_spec(spec: &ResourceSpec) -> Result<(), ResourceSpecError> {
    resource_family_algebra(spec.family()).validate_spec(spec)
}

fn resource_fact_entails(
    available: &ResourceFact,
    required: &ResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    available.family() == required.family()
        && resource_family_algebra(available.family()).entails(available, required, assumptions)
}

fn normalize_resource_fact_pair(
    left: &ResourceFact,
    right: &ResourceFact,
    assumptions: &PureFactContext,
) -> Option<ResourceFact> {
    if left.family() != right.family() {
        return None;
    }
    resource_family_algebra(left.family()).normalize_pair(left, right, assumptions)
}

fn memory_resource_fact_entails(
    available: &ResourceFact,
    required: &ResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    if let (Some(available), Some(required)) = (available.memory_range(), required.memory_range())
        && required.typed_carrier
        && !assumptions.access_provenance_matches_range(
            required.access_provenance(),
            required,
            available,
        )
    {
        return false;
    }
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
    available: &ResourceFact,
    required: &ResourceFact,
    assumptions: &PureFactContext,
) -> Option<ResourceFactConsumption> {
    if let (Some(available), Some(required)) = (available.memory_range(), required.memory_range())
        && required.typed_carrier
        && !assumptions.access_provenance_matches_range(
            required.access_provenance(),
            required,
            available,
        )
    {
        return None;
    }
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
        // escrowed owner and an opened borrow, which only the stable-view
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
                .map(ResourceFact::own_memory)
                .collect(),
        ));
    }
    unreachable!("non-memory resource sent to memory resource consumer")
}

fn exact_resources_proven_equal(
    left: &Resource,
    right: &Resource,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (Resource::Iterated(left), Resource::Iterated(right)) => {
            iterated_memories_proven_equal(left, right, assumptions)
        }
        (Resource::Publication(left), Resource::Publication(right)) => {
            let pointer = |pointer: &Address| -> AlgebraicValue {
                ProgramValue::pointer(pointer.clone()).into()
            };
            left.side == right.side
                && left.observed.is_none()
                && right.observed.is_none()
                && crate::kernel::resource_arguments_proven_equal(
                    &pointer(&left.flag),
                    &pointer(&right.flag),
                    assumptions,
                )
                && left.payload.family() == right.payload.family()
                && left.payload.schema() == right.payload.schema()
                && left.payload.resource_arguments() == right.payload.resource_arguments()
                && left.payload.arguments().len() == right.payload.arguments().len()
                && left
                    .payload
                    .arguments()
                    .iter()
                    .zip(right.payload.arguments())
                    .all(|(a, b)| {
                        crate::kernel::resource_field_values_proven_equal(a, b, assumptions)
                    })
        }
        (Resource::Instance(left), Resource::Instance(right)) => {
            left.identity == right.identity
                && left.name == right.name
                && left.schema == right.schema
                && left.resource_arguments == right.resource_arguments
                && left.arguments.len() == right.arguments.len()
                && left.fields.len() == right.fields.len()
                && left
                    .arguments
                    .iter()
                    .zip(right.arguments.iter())
                    .all(|(a, b)| {
                        crate::kernel::instance_field_values_proven_equal(a, b, assumptions)
                    })
                && left.fields.iter().zip(right.fields.iter()).all(|(a, b)| {
                    crate::kernel::resource_field_values_proven_equal(a, b, assumptions)
                })
        }
        (
            Resource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            Resource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments.iter())
                    .all(|(a, b)| {
                        crate::kernel::instance_field_values_proven_equal(a, b, assumptions)
                    })
        }
        (
            Resource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            Resource::Token {
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
                        crate::kernel::resource_field_values_proven_equal(left, right, assumptions)
                    })
        }
        _ => false,
    }
}

fn exact_resource_fact_entails(
    available: &ResourceFact,
    required: &ResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    match (available, required) {
        (
            ResourceFact::Own(available, available_quantity),
            ResourceFact::Own(required, required_quantity),
        ) => {
            resource_quantity_at_least(
                available_quantity.old_form(),
                required_quantity.old_form(),
                assumptions,
            ) && exact_resources_proven_equal(available, required, assumptions)
        }
        (ResourceFact::Own(available, available_quantity), ResourceFact::View(required)) => {
            resource_quantity_is_positive(available_quantity.old_form(), assumptions)
                && exact_resources_proven_equal(available, required, assumptions)
        }
        (ResourceFact::View(available), ResourceFact::View(required)) => {
            exact_resources_proven_equal(available, required, assumptions)
        }
        _ => false,
    }
}

/// Whether `range` is proved to name no cell: its two endpoints are the same
/// term or proved equal.
pub(in crate::kernel) fn memory_range_is_proven_empty(
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if let Some((start, end)) = range.wide_bounds() {
        return start == end
            || assumptions.decide(&OldConditionTerm::uint64_equal(start.clone(), end.clone()))
                == Some(true);
    }
    assumptions.int32_values_known_equal(range.start(), range.end())
}

/// Compare the two quantity operands as written, including literal pairs.
pub(in crate::kernel) fn quantity_comparison_holds(
    assumptions: &PureFactContext,
    format: MachineIntegerType,
    relation: CompareRelation,
    left: &OldMachineTerm,
    right: &OldMachineTerm,
) -> bool {
    let mut import = KernelTermImport::for_exact_field_inputs();
    let operands = [left, right].map(|operand| import.machine(format, operand));
    let root = KernelTerm::boolean_comparison_raw(format, relation, operands);
    quantity_condition_holds(
        assumptions,
        StoredConditionTerm::from_root(root).expect("quantity comparison"),
    )
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
    condition: StoredConditionTerm,
) -> bool {
    assumptions.proves_exact(&Proposition::condition_is(condition.clone(), true))
        || assumptions.decide(condition.old_form()) == Some(true)
}

fn resource_quantity_at_least(
    available: &OldMachineTerm,
    required: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    available == required
        || quantity_comparison_holds(
            assumptions,
            MachineIntegerType::Int32,
            CompareRelation::GreaterEqual,
            available,
            required,
        )
}

/// Whether a constant owned quantity is positive, as the signed number it is.
///
/// An owned quantity is an `int32`, and `resource_quantity_at_least` beside it
/// asks the `int32` `>=` comparison, so reading this one through
/// `OldMachineTerm::as_const` made the two arms disagree about one number:
/// `-1` was the largest quantity there is. `a98a05e4` is the same confusion at
/// the surface `fold`, and this is the kernel's own copy of it — the one that
/// decides whether an owned population exposes a viewed description of itself.
fn constant_quantity_is_positive(quantity: &OldMachineTerm) -> bool {
    signed_bitvector_constant(quantity).is_some_and(|value| value > 0)
}

pub(super) fn resource_quantity_is_positive(
    quantity: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    constant_quantity_is_positive(quantity)
        || quantity_comparison_holds(
            assumptions,
            MachineIntegerType::Int32,
            CompareRelation::GreaterThan,
            quantity,
            &OldMachineTerm::constant(0),
        )
}

/// The total of two population quantities, as the natural number a count is.
///
/// A population count is a mathematical natural number. The kernel holds one
/// in an `int32` term, and [`OldMachineTerm::add`] is modular, so
/// `2000000000 + 2000000000` is `-294967296`: four billion units reading as a
/// negative population. Every quantity rule beneath this one is signed —
/// [`resource_quantity_at_least`], [`constant_quantity_is_positive`],
/// [`resource_quantity_is_positive`] — so a wrapped total is not an
/// imprecision, it is a different and smaller number. Two `produces k of
/// tok(o)` clauses at `k == 2000000000` composed to `k + k` this way, and
/// `ensures count(tok(o)) < 0` verified on the result.
///
/// A total may be formed only when it is exact. Constants and recombining a
/// split need no extra premise. Other sums require the no-overflow condition
/// in the supplied context, checked by indexed lookup and atomic arithmetic.
/// Declining a merge leaves its two resource facts intact.
pub(in crate::kernel) fn population_quantity_sum(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> Option<OldMachineTerm> {
    if let (Some(left_value), Some(right_value)) = (
        signed_bitvector_constant(left),
        signed_bitvector_constant(right),
    ) {
        let total = left_value + right_value;
        return u32::try_from(total)
            .ok()
            .filter(|_| total <= i64::from(i32::MAX))
            .map(OldMachineTerm::constant);
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
    if let binary_term!(Int32, Subtract, total, taken) = right
        && taken.as_ref() == left
    {
        return Some(total.as_ref().clone());
    }
    if let binary_term!(Int32, Subtract, total, taken) = left
        && taken.as_ref() == right
    {
        return Some(total.as_ref().clone());
    }
    // An explicitly held guard can be read with borrowed operands. During
    // premise capture, let the proof query select and record its source.
    if !crate::kernel::assumptions::implicit_consulted_premises_capturing()
        && assumptions.condition_facts.written_overflow_value(
            MachineIntegerType::Int32,
            OverflowOperation::Add,
            left,
            right,
        ) == Some(false)
    {
        return Some(OldMachineTerm::add(left.clone(), right.clone()));
    }
    let no_overflow = OldConditionTerm::Overflows {
        format: MachineIntegerType::Int32,
        op: OverflowOperation::Add,
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    };
    (assumptions.proves_exact(&Proposition::condition_is(no_overflow.clone(), false))
        || assumptions.decide(&no_overflow) == Some(false))
    .then(|| OldMachineTerm::add(left.clone(), right.clone()))
}

/// Only families with ordinary unit quantities participate. A memory share,
/// an acquisition, or an authority cannot be added into a population unit.
fn numeric_population_owned_units(fact: &ResourceFact) -> Option<u32> {
    let ResourceFact::Own(resource, quantity) = fact else {
        return None;
    };
    if !matches!(
        resource,
        Resource::Composite { .. } | Resource::Token { .. }
    ) {
        return None;
    }
    quantity
        .as_const()
        .filter(|q| *q > 0 && *q <= i32::MAX as u32)
}

fn resource_quantity_is_zero(quantity: &OldMachineTerm, assumptions: &PureFactContext) -> bool {
    quantity.as_const() == Some(0)
        || assumptions.proves_exact(&Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(quantity.clone()),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            true,
        ))
}

fn resource_quantity_resolves_to_zero(
    quantity: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    resource_quantity_is_zero(quantity, assumptions)
        || crate::kernel::reasoning::int32_values_proven_equal_for_memory_resolution(
            quantity,
            &OldMachineTerm::constant(0),
            assumptions,
        )
}

#[cfg(test)]
mod zero_quantity_graph_tests {
    use super::*;

    fn var(id: u64) -> OldMachineTerm {
        OldMachineTerm::Variable(Variable(id))
    }

    fn required(quantity: OldMachineTerm) -> ResourceFact {
        ResourceFact::own_quantity(
            Resource::Composite {
                name: "zero-quantity".into(),
                arguments: Vec::new().into(),
            },
            quantity,
        )
    }

    #[test]
    fn separately_retained_units_entail_their_exact_quantity() {
        let assumptions = PureFactContext::new();
        let one = required(OldMachineTerm::constant(1));
        let two = required(OldMachineTerm::constant(2));
        let three = required(OldMachineTerm::constant(3));
        let context = ResourceContext::new().unchecked_with_facts([one.clone(), one.clone()]);
        assert!(context.satisfies_fact(&two, &assumptions));
        assert!(!context.satisfies_fact(&three, &assumptions));
        let after = context.clone().without_exact_representation(&one).unwrap();
        assert!(!after.satisfies_fact(&two, &assumptions));
        assert!(
            context
                .without_fact_incrementally(&two, &assumptions)
                .unwrap()
                .is_empty()
        );
        let views = ResourceContext::new()
            .unchecked_with_facts([ResourceFact::View(one.resource().clone()), one.clone()]);
        assert!(!views.satisfies_fact(&two, &assumptions));
        let large = required(OldMachineTerm::constant(2_000_000_000));
        let oversized = ResourceContext::new().unchecked_with_facts([large.clone(), large]);
        assert!(oversized.satisfies_fact(&two, &assumptions));
        assert!(oversized.satisfies_fact(
            &required(OldMachineTerm::constant(i32::MAX as u32)),
            &assumptions,
        ));
    }

    #[test]
    fn separately_retained_units_are_consumed_together_without_normalizing() {
        let assumptions = PureFactContext::new();
        let one = required(OldMachineTerm::constant(1));
        let two = required(OldMachineTerm::constant(2));
        let three = required(OldMachineTerm::constant(3));
        let pair = ResourceContext::new().unchecked_with_facts([one.clone(), one.clone()]);
        assert!(
            pair.clone()
                .without_fact_delaying_normalization(&two, &assumptions)
                .unwrap()
                .is_empty()
        );
        assert!(
            pair.clone()
                .without_fact_delaying_normalization(&three, &assumptions)
                .is_none()
        );
        // The merged unit keeps its residual.
        let left = ResourceContext::new()
            .unchecked_with_facts([one.clone(), one.clone(), one.clone()])
            .without_fact_delaying_normalization(&two, &assumptions)
            .unwrap();
        assert!(left.satisfies_fact(&one, &assumptions));
        assert!(!left.satisfies_fact(&two, &assumptions));
        // A view of the resource is not a unit of it.
        let viewed = ResourceContext::new()
            .unchecked_with_facts([ResourceFact::View(one.resource().clone()), one.clone()]);
        assert!(
            viewed
                .without_fact_delaying_normalization(&two, &assumptions)
                .is_none()
        );
    }

    #[test]
    fn zero_ownership_uses_graph_with_state_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let before =
            crate::kernel::intern_memory(SymbolicMemory::new().with_block("zero-quantity", 8));
        let pointer =
            |index| Address::new("zero-quantity".into(), AddressOffset::scale_int32(index, 4));
        let load = |memory: &SharedMemory, index| {
            OldMachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &pointer(index),
                crate::kernel::LoadKind::Int32,
                4,
                memory,
            ))
        };
        let (a, b) = (var(90_101), var(90_102));
        let after = crate::kernel::intern_memory(before.memory().clone().store(
            pointer(b.clone()),
            ProgramValue::Int32(OldMachineTerm::constant(9)),
        ));
        let sum = |value| OldMachineTerm::add(value, OldMachineTerm::constant(1));
        let source = required(sum(load(&before, a.clone())));
        let later = required(sum(load(&after, b.clone())));
        let address_premise = OldConditionTerm::equal(a, b.clone());
        let zero_premise =
            OldConditionTerm::equal(sum(load(&before, b)), OldMachineTerm::constant(0));
        let parent = PureFactContext::new();
        let address_only = parent
            .clone()
            .assume_condition(address_premise.clone(), true);
        let branch = address_only
            .clone()
            .assume_condition(zero_premise.clone(), true);
        let empty = ResourceContext::new();
        let _scope = branch.enter_id_scope();

        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(empty.satisfies_fact(&source, &branch));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!empty.satisfies_fact(&later, &branch));
        assert!(!empty.satisfies_fact(&source, &address_only));
        let zero_only = parent.assume_condition(zero_premise, true);
        assert!(!empty.satisfies_fact(&source, &zero_only));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/primitives/resource_algebra/zero_quantity_graph_tests.rs"
        );
    }
}

fn consume_exact_resource_fact(
    available: &ResourceFact,
    required: &ResourceFact,
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
        let ResourceFact::Own(available, available_quantity) = available else {
            unreachable!("owned exact requirement entailed by a viewed fact")
        };
        let ResourceFact::Own(_, required_quantity) = required else {
            unreachable!("checked above")
        };
        let residual = OldMachineTerm::subtract(
            available_quantity.old_form().clone(),
            required_quantity.old_form().clone(),
        );
        let residual_is_zero = residual.as_const() == Some(0)
            || quantity_comparison_holds(
                assumptions,
                MachineIntegerType::Int32,
                CompareRelation::Equal,
                &residual,
                &OldMachineTerm::constant(0),
            );
        ResourceFactConsumption::Replace(if residual_is_zero {
            Vec::new()
        } else {
            vec![ResourceFact::own_quantity(available.clone(), residual)]
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
/// A **bound** view — one whose occurrence carries a live `borrow_dependency` —
/// must never be absorbed: the merged fact is a new authority with no
/// occurrence, so the dependency that authorizes reading it would vanish and
/// the borrow would disappear with it. `ResourceContext::normalized` is the
/// only caller, and its `borrow_bound` guard skips both sides of every pair
/// whose occurrence has a live dependency, and detaches supported projections
/// before normalizing at all. That guard, not this function, is what makes
/// the merge safe: `normalize_pair` sees two bare facts and cannot tell a
/// bound description from an unbound one.
fn combine_exact_resource_facts(
    left: &ResourceFact,
    right: &ResourceFact,
    assumptions: &PureFactContext,
) -> Option<ResourceFact> {
    match (left, right) {
        (ResourceFact::Own(left, quantity), ResourceFact::View(right))
        | (ResourceFact::View(right), ResourceFact::Own(left, quantity))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(ResourceFact::Own(left.clone(), quantity.clone()))
        }
        (ResourceFact::View(left), ResourceFact::View(right))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(ResourceFact::View(left.clone()))
        }
        _ => None,
    }
}

/// The owner-observation rule (docs/internals/stable-views.md).
///
/// An owner may read what it owns and inspect its composite without issuing a
/// stable borrow to itself, so a positive owned fact exposes a viewed
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
/// * the escrow record in `crate::kernel::borrows`, which names the viewed
///   description a checked lend transition hands the callee.
///
/// It never answers a *call's* `views` requirement on its own. Meeting one
/// escrows the owner and opens a borrow, and only the stable-view planner does
/// that; a call transfer never routes a view requirement into consumption.
/// The projection is not authority the callee could carry: it is read off
/// ownership that stays where it is, so nothing survives the observing
/// context.
fn owner_observation_core(resource: &ResourceFact) -> Option<ResourceFact> {
    match resource {
        ResourceFact::Own(resource, quantity)
            if constant_quantity_is_positive(quantity.old_form()) =>
        {
            Some(ResourceFact::View(resource.clone()))
        }
        ResourceFact::Own(_, _) => None,
        ResourceFact::View(resource) => Some(ResourceFact::View(resource.clone())),
    }
}

/// Separation cases whose proof depends only on the resource constructors,
/// not on ambient facts or the composition that happened to contain them.
pub(in crate::kernel) fn resources_structurally_separate(
    left: &Resource,
    right: &Resource,
) -> bool {
    match (left, right) {
        (Resource::Memory(left), Resource::Memory(right)) => {
            left.base().blocks_proven_distinct(right.base())
                || left.base() == right.base()
                    && matches!(
                        (
                            left.signed_constant_start(),
                            left.signed_constant_end(),
                            right.signed_constant_start(),
                            right.signed_constant_end(),
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
pub(super) fn string_literal_blocks_may_alias(left: &AddressBase, right: &AddressBase) -> bool {
    if left == right {
        return false;
    }
    matches!(
        (left, right),
        (
            AddressBase::StringLiteral { bytes: left, .. },
            AddressBase::StringLiteral { bytes: right, .. }
        ) if left == right
    )
}

fn pair_validity_error_with_separation(
    left: &ResourceFact,
    right: &ResourceFact,
    assumptions: &PureFactContext,
    use_separation: bool,
) -> Option<ResourceContextValidityError> {
    if !use_separation
        && let (Some(left_range), Some(right_range)) =
            (left.memory_own_range(), right.memory_own_range())
    {
        if string_literal_blocks_may_alias(&left_range.base().base, &right_range.base().base) {
            return None;
        }
        return memory_ranges_proven_overlapping_ignoring_separation(
            left_range,
            right_range,
            assumptions,
        )
        .then(
            || ResourceContextValidityError::OverlappingOwnedMemoryResources {
                left: left_range.clone(),
                right: right_range.clone(),
            },
        );
    }
    resource_family_algebra(left.family()).pair_validity_error(left, right, assumptions)
}

impl ResourceFamilyAlgebra for MemoryResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Memory
    }

    /// Two owners of overlapping bytes are a partition violation. An owner
    /// overlapping a *view* is decided by the view's binding, which this
    /// check cannot see (the owner-observation rule in docs/internals/stable-views.md).
    ///
    /// A **bound** view — one carrying a live `borrow_dependency` — beside a
    /// usable owner of the same bytes is invalid: lending escrows the owner
    /// out of the caller residual, so the two cannot coexist. That is
    /// enforced where the binding is visible, not here: the planner refuses
    /// an `owns` requirement inside a lent range (its exclusive reservations
    /// are taken before any view is planned, and the composite lend checks
    /// the frontier beside the original entry partition). The ledger refuses
    /// writes and retirement through a lent range.
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
        left: &ResourceFact,
        right: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        let (Some(left), Some(right)) = (left.memory_own_range(), right.memory_own_range()) else {
            return None;
        };
        if string_literal_blocks_may_alias(&left.base().base, &right.base().base) {
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
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        memory_resource_fact_entails(available, required, assumptions)
    }

    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        consume_memory_resource_fact(available, required, assumptions)
    }

    fn normalize_pair(
        &self,
        left: &ResourceFact,
        right: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFact> {
        combine_memory_resource_facts(left, right, assumptions)
    }

    fn core(&self, fact: &ResourceFact) -> Option<ResourceFact> {
        owner_observation_core(fact)
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
                _left: &ResourceFact,
                _right: &ResourceFact,
                _assumptions: &PureFactContext,
            ) -> Option<ResourceContextValidityError> {
                None
            }

            fn entails(
                &self,
                available: &ResourceFact,
                required: &ResourceFact,
                assumptions: &PureFactContext,
            ) -> bool {
                exact_resource_fact_entails(available, required, assumptions)
            }

            fn consume(
                &self,
                available: &ResourceFact,
                required: &ResourceFact,
                assumptions: &PureFactContext,
            ) -> Option<ResourceFactConsumption> {
                consume_exact_resource_fact(available, required, assumptions)
            }

            fn normalize_pair(
                &self,
                left: &ResourceFact,
                right: &ResourceFact,
                assumptions: &PureFactContext,
            ) -> Option<ResourceFact> {
                match (left, right) {
                    (
                        ResourceFact::Own(left, left_quantity),
                        ResourceFact::Own(right, right_quantity),
                    ) if exact_resources_proven_equal(left, right, assumptions) => {
                        // A merge that cannot state the total exactly is
                        // declined rather than wrapped: leaving both facts
                        // in the state costs precision, and a wrapped
                        // quantity is a count that is not the population's.
                        Some(ResourceFact::Own(
                            left.clone(),
                            Box::new(
                                population_quantity_sum(
                                    left_quantity.old_form(),
                                    right_quantity.old_form(),
                                    assumptions,
                                )?
                                .into(),
                            ),
                        ))
                    }
                    _ => combine_exact_resource_facts(left, right, assumptions),
                }
            }

            fn core(&self, fact: &ResourceFact) -> Option<ResourceFact> {
                owner_observation_core(fact)
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
        left: &ResourceFact,
        right: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        match (left.resource(), right.resource()) {
            (Resource::Instance(a), Resource::Instance(b)) if a.identity == b.identity => Some(
                ResourceContextValidityError::DuplicateOwnedResourceFact(right.clone()),
            ),
            _ => None,
        }
    }
    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        matches!((available,required),(ResourceFact::Own(_,a),ResourceFact::Own(_,b)) if a.as_const()==Some(1) && b.as_const()==Some(1))
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions)
            .then(|| ResourceFactConsumption::Replace(vec![]))
    }
    fn normalize_pair(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceFact> {
        None
    }
    fn core(&self, _: &ResourceFact) -> Option<ResourceFact> {
        None
    }
}

impl ResourceFamilyAlgebra for PopulationAuthorityResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::PopulationAuthority
    }
    fn pair_validity_error(
        &self,
        left: &ResourceFact,
        right: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        match (left.resource(), right.resource()) {
            (Resource::PopulationAuthority(a), Resource::PopulationAuthority(b)) if a == b => Some(
                ResourceContextValidityError::DuplicateOwnedResourceFact(right.clone()),
            ),
            _ => None,
        }
    }
    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        matches!((available,required),(ResourceFact::Own(_,a),ResourceFact::Own(_,b)) if a.as_const()==Some(1) && b.as_const()==Some(1))
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions)
            .then(|| ResourceFactConsumption::Replace(vec![]))
    }
    fn normalize_pair(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceFact> {
        None
    }
    fn core(&self, _: &ResourceFact) -> Option<ResourceFact> {
        None
    }
}

impl ResourceFamilyAlgebra for MutexGuardResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::MutexGuard
    }
    fn pair_validity_error(
        &self,
        left: &ResourceFact,
        right: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        match (left.resource(), right.resource()) {
            (Resource::ConditionalMutexGuard(a), Resource::ConditionalMutexGuard(b))
                if a.identity == b.identity =>
            {
                Some(ResourceContextValidityError::DuplicateOwnedResourceFact(
                    right.clone(),
                ))
            }
            (Resource::MutexGuard(a), Resource::MutexGuard(b)) if a == b => Some(
                ResourceContextValidityError::DuplicateOwnedResourceFact(right.clone()),
            ),
            _ => None,
        }
    }
    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        matches!((available,required),(ResourceFact::Own(_,a),ResourceFact::Own(_,b)) if a.as_const()==Some(1) && b.as_const()==Some(1))
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions)
            .then(|| ResourceFactConsumption::Replace(vec![]))
    }
    fn normalize_pair(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceFact> {
        None
    }
    fn core(&self, _: &ResourceFact) -> Option<ResourceFact> {
        None
    }
}

/// A publication right is unique: initialization mints one of each side and
/// nothing duplicates it, so two for the same flag and side are a conflict.
impl ResourceFamilyAlgebra for PublicationResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Publication
    }
    fn pair_validity_error(
        &self,
        left: &ResourceFact,
        right: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        match (left.resource(), right.resource()) {
            (Resource::Publication(a), Resource::Publication(b))
                if a.side == b.side && a.flag == b.flag =>
            {
                Some(ResourceContextValidityError::DuplicateOwnedResourceFact(
                    right.clone(),
                ))
            }
            _ => None,
        }
    }
    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        matches!((available,required),(ResourceFact::Own(_,a),ResourceFact::Own(_,b)) if a.as_const()==Some(1) && b.as_const()==Some(1))
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions)
            .then(|| ResourceFactConsumption::Replace(vec![]))
    }
    fn normalize_pair(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceFact> {
        None
    }
    fn core(&self, _: &ResourceFact) -> Option<ResourceFact> {
        None
    }
}

impl ResourceFamilyAlgebra for MutexLiveResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::MutexLive
    }
    fn pair_validity_error(
        &self,
        left: &ResourceFact,
        right: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        match (left.resource(), right.resource()) {
            (Resource::MutexLive(a), Resource::MutexLive(b)) if a == b => Some(
                ResourceContextValidityError::DuplicateOwnedResourceFact(right.clone()),
            ),
            _ => None,
        }
    }
    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        matches!((available,required),(ResourceFact::Own(_,a),ResourceFact::Own(_,b)) if a.as_const()==Some(1) && b.as_const()==Some(1))
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions)
            .then(|| ResourceFactConsumption::Replace(vec![]))
    }
    fn normalize_pair(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceFact> {
        None
    }
    fn core(&self, _: &ResourceFact) -> Option<ResourceFact> {
        None
    }
}

impl ResourceFamilyAlgebra for MutexUseResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::MutexUse
    }
    fn pair_validity_error(
        &self,
        left: &ResourceFact,
        right: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        match (left.resource(), right.resource()) {
            (Resource::MutexUse(a), Resource::MutexUse(b)) if a == b => Some(
                ResourceContextValidityError::DuplicateOwnedResourceFact(right.clone()),
            ),
            _ => None,
        }
    }
    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        matches!((available,required),(ResourceFact::Own(_,a),ResourceFact::Own(_,b)) if a.as_const()==Some(1) && b.as_const()==Some(1))
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions)
            .then(|| ResourceFactConsumption::Replace(vec![]))
    }
    fn normalize_pair(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceFact> {
        None
    }
    fn core(&self, _: &ResourceFact) -> Option<ResourceFact> {
        None
    }
}

impl ResourceFamilyAlgebra for IteratedResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Iterated
    }
    fn pair_validity_error(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        None
    }
    fn entails(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> bool {
        let unit = |quantity: &StoredMachineTerm| quantity.as_const() == Some(1);
        let shape = match (available, required) {
            (ResourceFact::Own(_, available), ResourceFact::Own(_, required)) => {
                unit(available) && unit(required)
            }
            (ResourceFact::Own(_, available), ResourceFact::View(_)) => unit(available),
            (ResourceFact::View(_), ResourceFact::View(_)) => true,
            (ResourceFact::View(_), ResourceFact::Own(..)) => false,
        };
        shape
            && exact_resources_proven_equal(available.resource(), required.resource(), assumptions)
    }
    fn consume(
        &self,
        available: &ResourceFact,
        required: &ResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption> {
        self.entails(available, required, assumptions).then(|| {
            if required.is_view() {
                ResourceFactConsumption::Preserve
            } else {
                ResourceFactConsumption::Replace(vec![])
            }
        })
    }
    fn normalize_pair(
        &self,
        _: &ResourceFact,
        _: &ResourceFact,
        _: &PureFactContext,
    ) -> Option<ResourceFact> {
        None
    }
    fn core(&self, _: &ResourceFact) -> Option<ResourceFact> {
        None
    }
}

/// Whether two iterated facts denote the same holding: every structural
/// parameter equal, and every pointer and term equal or proved equal. Holes
/// are compared in order; the checked operations keep them in the order
/// they were opened.
pub(in crate::kernel) fn iterated_memories_proven_equal(
    left: &IteratedMemory,
    right: &IteratedMemory,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    let term_equal = |a: &OldMachineTerm, b: &OldMachineTerm| {
        a == b
            || assumptions.decide(&OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(a.clone()),
                right: Box::new(b.clone()),
            }) == Some(true)
    };
    let address_equal = |a: &Address, b: &Address| {
        crate::kernel::prelude::pointers_proven_equal_for_memory_resolution(a, b, assumptions)
    };
    left.element_width == right.element_width
        && left.stride == right.stride
        && left.start_offset == right.start_offset
        && left.end_offset == right.end_offset
        && left.guard.cell_type == right.guard.cell_type
        && left.guard.cell_width == right.guard.cell_width
        && left.guard.holds_when_equal == right.guard.holds_when_equal
        && left.holes.len() == right.holes.len()
        && address_equal(&left.element_base, &right.element_base)
        && address_equal(&left.guard.base, &right.guard.base)
        && term_equal(left.lower.old_form(), right.lower.old_form())
        && term_equal(left.upper.old_form(), right.upper.old_form())
        && term_equal(left.guard.value.old_form(), right.guard.value.old_form())
        && left
            .holes
            .iter()
            .zip(right.holes.iter())
            .all(|(a, b)| term_equal(a.old_form(), b.old_form()))
}

pub(super) fn resource_fact_read_core_range(resource: &ResourceFact) -> Option<MemoryRange> {
    match resource.core()? {
        ResourceFact::View(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
        ) => None,
        ResourceFact::View(Resource::Memory(range)) => Some(range),
        ResourceFact::View(
            Resource::Composite { .. }
            | Resource::Token { .. }
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_),
        )
        | ResourceFact::Own(..) => None,
    }
}

fn memory_resource_fact_permits_read(
    resource: &ResourceFact,
    pointer: &Address,
    byte_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    resource_fact_read_core_range(resource).is_some_and(|range| {
        if range.wide_bounds().is_some() {
            return assumptions.pointer_access_in_wide_range(pointer, byte_width, &range);
        }
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
    resource: &ResourceFact,
    pointer: &Address,
    byte_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    match resource {
        ResourceFact::Own(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
            _,
        ) => false,
        ResourceFact::Own(Resource::Memory(range), quantity) if range.wide_bounds().is_some() => {
            resource_quantity_is_positive(quantity.old_form(), assumptions)
                && assumptions.pointer_access_in_wide_range(pointer, byte_width, range)
        }
        ResourceFact::Own(Resource::Memory(range), quantity) => {
            resource_quantity_is_positive(quantity.old_form(), assumptions)
                && assumptions.pointer_access_in_range(
                    pointer,
                    byte_width,
                    range.base(),
                    range.start(),
                    range.end(),
                    range.element_width(),
                )
        }
        ResourceFact::Own(
            Resource::Composite { .. }
            | Resource::Token { .. }
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_),
            _,
        )
        | ResourceFact::View(_) => false,
    }
}

#[cfg(test)]
#[test]
fn owned_cell_access_uses_transitive_graph_address_equality() {
    let pointer = |id| Address::symbolic(Variable(id));
    let (a, b, c, d) = (
        pointer(91_100),
        pointer(91_101),
        pointer(91_102),
        pointer(91_103),
    );
    let owner = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
        MemoryRange::new_with_element_width(a.clone(), 0u32.into(), 1u32.into(), 4),
    ));
    let facts = PureFactContext::new()
        .assume_condition(OldConditionTerm::address_equal(a.clone(), b.clone()), true)
        .assume_condition(OldConditionTerm::address_equal(c.clone(), d.clone()), true);
    assert!(!owner.permits_memory_read(&d, 4, &facts));
    let connected = facts
        .clone()
        .assume_condition(OldConditionTerm::address_equal(b, c), true);
    assert!(connected.pointers_known_equal(&a, &d));
    assert!(owner.permits_memory_read(&d, 4, &connected));
    assert!(owner.memory_write_range(&d, 4, &connected).is_some());
    assert!(!owner.permits_memory_read(&d, 12, &connected));
    assert!(!owner.permits_memory_read(&d, 4, &facts));
}

/// Range endpoints compare like ordinary terms, and additionally two loads
/// of one pointer are equal when the pointed-to cell is provably unchanged
/// between their states — a range written through metadata loads then
/// survives writes to unrelated cells.
fn range_endpoint_terms_equal(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    range_endpoint_views_equal(
        MachineOperandView::Old(left),
        MachineOperandView::Old(right),
        assumptions,
    )
}

fn range_endpoint_views_equal(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    fn walk(
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        assumptions: &PureFactContext,
        memo: &mut BTreeMap<(SharedMachineIntegerTerm, SharedMachineIntegerTerm), bool>,
    ) -> bool {
        let key = (
            left.retain(MachineIntegerType::Int32),
            right.retain(MachineIntegerType::Int32),
        );
        if key.0 == key.1 {
            return true;
        }
        if let Some(answer) = memo.get(&key) {
            return *answer;
        }
        let bridged = match (left.read(), right.read()) {
            (Some((_, lp, lk)), Some((_, rp, rk))) if lp == rp && lk == rk => {
                let a = left.read_source().expect("selected read");
                let b = right.read_source().expect("selected read");
                crate::kernel::explicit_atomic_equality_from_memory_derivations(&a, &b, assumptions)
            }
            _ => false,
        };
        let structural = bridged
            || match (left.binary(), right.binary()) {
                (
                    Some((MachineIntegerType::Int32, lo, [la, lb])),
                    Some((MachineIntegerType::Int32, ro, [ra, rb])),
                ) if lo == ro
                    && matches!(
                        lo,
                        MachineBinaryOp::Add
                            | MachineBinaryOp::Subtract
                            | MachineBinaryOp::Multiply
                    ) =>
                {
                    walk(la, ra, assumptions, memo) && walk(lb, rb, assumptions, memo)
                }
                _ => false,
            };
        let answer = structural
            || crate::kernel::reasoning::int32_operand_values_equal_for_memory_resolution(
                left,
                right,
                assumptions,
            );
        memo.insert(key, answer);
        answer
    }
    walk(left, right, assumptions, &mut BTreeMap::new())
}

/// Pointer bases compare with the same load bridging as range endpoints:
/// two forms of one loaded base pointer are equal when the loaded cell
/// is provably unchanged between their states.
fn pointer_bases_equal_with_load_bridging(
    left: &Address,
    right: &Address,
    assumptions: &PureFactContext,
) -> bool {
    left.base == right.base
        && pointer_offsets_equal_with_load_bridging(&left.offset, &right.offset, assumptions)
}

fn pointer_offsets_equal_with_load_bridging(
    left: &AddressOffset,
    right: &AddressOffset,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left.view(), right.view()) {
        (OffsetView::Add(left_a, left_b), OffsetView::Add(right_a, right_b)) => {
            pointer_offsets_equal_with_load_bridging(left_a, right_a, assumptions)
                && pointer_offsets_equal_with_load_bridging(left_b, right_b, assumptions)
        }
        (
            OffsetView::Int32Scaled {
                index: left_value,
                byte_width: left_width,
            },
            OffsetView::Int32Scaled {
                index: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && range_endpoint_views_equal(
                    left_value.operand_view(),
                    right_value.operand_view(),
                    assumptions,
                )
        }
        _ => false,
    }
}

/// A range as its physical byte footprint: width 1, based at its first byte.
///
/// This is the shared spelling-independent form of a memory footprint (D6).
/// [`MemoryRange::byte_footprint`] already derives the pointer and the byte
/// length, and `protected_range_proven_overlapping` in the borrow oracle asks
/// its question in exactly these terms; this helper keeps the memory family's
/// relations on that one normalization rather than inventing a second.
// Coverage, splitting and overlap all dispatch wide ranges before normalization.
fn byte_normalized_memory_range(range: &MemoryRange) -> MemoryRange {
    let (base, bytes) = range.byte_footprint();
    MemoryRange::new_with_element_width(base, OldMachineTerm::constant(0), bytes, 1)
        .with_carrier_of(range)
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
fn memory_range_in_element_width(range: &MemoryRange, width: u32) -> Option<MemoryRange> {
    if range.element_width() == width {
        return Some(range.clone());
    }
    let source_width = i64::from(range.element_width());
    let target_width = i64::from(width);
    let start = range.signed_constant_start()?.checked_mul(source_width)?;
    let end = range.signed_constant_end()?.checked_mul(source_width)?;
    if start % target_width != 0 || end % target_width != 0 {
        return None;
    }
    let start = i32::try_from(start / target_width).ok()?;
    let end = i32::try_from(end / target_width).ok()?;
    Some(
        MemoryRange::new_with_element_width(
            range.base().clone(),
            OldMachineTerm::constant(start as u32),
            OldMachineTerm::constant(end as u32),
            width,
        )
        .with_carrier_of(range),
    )
}

/// A wide range re-spelled in another element width, before its no-wrap
/// conditions are decided: the respelled range and, for each symbolic
/// endpoint `x` that was or became a product `x * m`, the pair `(x, m)`.
pub(in crate::kernel) struct WideRangeRespelling {
    pub(in crate::kernel) range: MemoryRange,
    pub(in crate::kernel) no_wrap: Vec<(OldMachineTerm, u64)>,
}

/// The structural re-spelling of a wide range in `width`-byte elements.
///
/// A wide range's endpoints are unsigned 64-bit element indices, so
/// `p[0u64..n]` of 8-byte elements and `p[0u64..n * 8u64]` of bytes name the
/// same footprint exactly when the `uint64` product `n * 8` does not wrap.
/// Narrowing the width multiplies each endpoint by `m = from / to`; widening
/// it reads an endpoint that is a `uint64` product `x * m` (either order) or a
/// constant multiple of `m` as `x`. Each symbolic product is returned with its
/// no-wrap condition `x <= UINT64_MAX / m`; a constant is folded only when it
/// does not overflow. `None` for a narrow range, widths that do not divide,
/// or an endpoint with no such reading. A wide range has no 32-bit byte count,
/// so this is the only width conversion wide ranges have.
pub(in crate::kernel) fn wide_memory_range_respelled(
    range: &MemoryRange,
    width: u32,
) -> Option<WideRangeRespelling> {
    let (start, end) = range.wide_bounds()?;
    let from = u64::from(range.element_width());
    let to = u64::from(width);
    if from == 0 || to == 0 {
        return None;
    }
    let mut no_wrap = Vec::new();
    let mut convert = |endpoint: &OldMachineTerm| -> Option<OldMachineTerm> {
        if from == to {
            return Some(endpoint.clone());
        }
        if from.is_multiple_of(to) {
            let factor = from / to;
            if let Some(value) = endpoint.uint64_as_const() {
                return value
                    .checked_mul(factor)
                    .map(OldMachineTerm::uint64_constant);
            }
            no_wrap.push((endpoint.clone(), factor));
            return Some(OldMachineTerm::uint64_multiply(
                endpoint.clone(),
                OldMachineTerm::uint64_constant(factor),
            ));
        }
        if !to.is_multiple_of(from) {
            return None;
        }
        let factor = to / from;
        if let Some(value) = endpoint.uint64_as_const() {
            return value
                .is_multiple_of(factor)
                .then(|| OldMachineTerm::uint64_constant(value / factor));
        }
        let binary_term!(UInt64, Multiply, left, right) = endpoint else {
            return None;
        };
        let count = match (left.uint64_as_const(), right.uint64_as_const()) {
            (_, Some(constant)) if constant == factor => left.as_ref(),
            (Some(constant), _) if constant == factor => right.as_ref(),
            _ => return None,
        };
        no_wrap.push((count.clone(), factor));
        Some(count.clone())
    };
    let start = convert(start)?;
    let end = convert(end)?;
    Some(WideRangeRespelling {
        range: MemoryRange::new_wide(range.base().clone(), start, end, width)
            .with_carrier_of(range),
        no_wrap,
    })
}

/// The no-wrap condition `count <= UINT64_MAX / factor` of one re-spelled
/// endpoint.
pub(in crate::kernel) fn wide_respelling_no_wrap_condition(
    count: &OldMachineTerm,
    factor: u64,
) -> OldConditionTerm {
    OldConditionTerm::uint64_less_equal(
        count.clone(),
        OldMachineTerm::uint64_constant(u64::MAX / factor),
    )
}

/// [`wide_memory_range_respelled`] once each of its no-wrap conditions is
/// decided: then every product is the mathematical value and the two ranges
/// name the same bytes, so either may stand for the other in coverage and
/// subtraction. One decision per symbolic endpoint; nothing is scanned.
fn wide_memory_range_in_element_width(
    range: &MemoryRange,
    width: u32,
    assumptions: &PureFactContext,
) -> Option<MemoryRange> {
    let respelled = wide_memory_range_respelled(range, width)?;
    respelled
        .no_wrap
        .iter()
        .all(|(count, factor)| {
            assumptions.decide(&wide_respelling_no_wrap_condition(count, *factor)) == Some(true)
        })
        .then_some(respelled.range)
}

/// Bounds geometry shared by held ranges and opaque-domain coverage facts.
/// This constructs no read authority and includes the one-past position.
pub(in crate::kernel) fn pointer_formation_in_range(
    pointer: &Address,
    operand: &Address,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A field of a symbolic layout lies inside its object, by the layout's
    // rule found by lookup: `p + offsetof(L, f)` formed from `p` is in the
    // object `[p, p + sizeof(L))`.
    if let Some((rest, layout, _)) =
        crate::kernel::SymbolicLayoutName::field_displacement(&pointer.offset)
        && pointer.base == operand.base
        && rest.map_or(operand.offset.as_const() == Some(0), |rest| {
            *rest == operand.offset
        })
        && range.base() == operand
        && range.element_width() == 1
        && range.wide_bounds().is_some_and(|(start, end)| {
            start.uint64_as_const() == Some(0) && *end == layout.size_term()
        })
    {
        return true;
    }
    let width = range.element_width();
    let nonempty = match range.wide_bounds() {
        Some((start, end)) => OldConditionTerm::uint64_less_than(start.clone(), end.clone()),
        None => OldConditionTerm::signed_less_than(range.start().clone(), range.end().clone()),
    };
    // Re-spell only checked nonnegative endpoints. This does not
    // truncate a native index or a native range into 32 bits.
    let wide = shared_wide_range_bounds(range, assumptions);
    let narrow = if range.wide_bounds().is_none() {
        Some(range.clone())
    } else {
        range.wide_bounds().and_then(|(start, end)| {
            let (start, end) = start.uint64_as_const().zip(end.uint64_as_const())?;
            (start <= end && end <= i32::MAX as u64 / u64::from(width)).then(|| {
                MemoryRange::new_with_element_width(
                    range.base().clone(),
                    OldMachineTerm::constant(start as u32),
                    OldMachineTerm::constant(end as u32),
                    width,
                )
            })
        })
    };
    let wide_window = |base: &Address, start: u64, end: u64| {
        wide.as_ref().is_some_and(|(first, limit)| {
            if assumptions.decide(&wide_index_comparison(
                CompareRelation::LessEqual,
                limit.operand_view(),
                MachineOperandView::Old(&OldMachineTerm::uint64_constant(
                    i64::MAX as u64 / u64::from(width),
                )),
            )) != Some(true)
            {
                return false;
            }
            let start = OldMachineTerm::uint64_constant(start);
            let end = OldMachineTerm::uint64_constant(end);
            let bounds = [first.operand_view(), limit.operand_view()];
            if range.base() == base
                || pointers_proven_equal_for_memory_resolution(range.base(), base, assumptions)
            {
                wide_bounds_cover(
                    bounds,
                    [
                        MachineOperandView::Old(&start),
                        MachineOperandView::Old(&end),
                    ],
                    assumptions,
                )
            } else {
                wide_memory_range_covers_window(
                    range.base(),
                    width,
                    bounds,
                    &MemoryRange::new_wide(base.clone(), start, end, width),
                    assumptions,
                )
            }
        })
    };
    let narrow_contains = |position: &Address, bytes| {
        narrow
            .as_ref()
            .is_some_and(|range| assumptions.pointer_access_in_held_range(position, bytes, range))
    };
    let contains = |position: &Address| {
        narrow_contains(position, 0)
            || narrow_contains(position, 1)
            || wide_window(position, 0, 0)
            // An element or field address of a struct array, over its count.
            || assumptions.position_in_wide_struct_array(position, range)
            || position
                .offset_from_base(operand)
                .and_then(|offset| offset.as_const())
                .filter(|bytes| *bytes >= 0)
                .is_some_and(|bytes| {
                    let elements = (bytes / i64::from(width)) as u64;
                    let last = elements + u64::from(bytes % i64::from(width) != 0);
                    wide_window(operand, elements, last)
                })
    };
    // An empty range can justify only the same contained position.
    contains(pointer)
        && (contains(operand)
            || assumptions.decide(&nonempty) == Some(true)
            || narrow_contains(pointer, 1)
            || narrow_contains(pointer, width)
            || wide_window(pointer, 0, 1))
}

pub(in crate::kernel) fn memory_range_covers(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if available.has_holes() || required.has_holes() {
        return symbolic_object_covers_field(available, required)
            || symbolic_object_covers_object(available, required);
    }
    symbolic_object_covers_field(available, required)
        || memory_range_covers_by_routes(available, required, assumptions)
}

/// Whether `available` holds every byte of `required`, both the object of
/// one symbolic layout at one base: `required` takes out every field
/// `available` does.
fn symbolic_object_covers_object(available: &MemoryRange, required: &MemoryRange) -> bool {
    available.base() == required.base()
        && available.symbolic_object().is_some()
        && available.symbolic_object() == required.symbolic_object()
        && available
            .holes()
            .iter()
            .all(|hole| required.holes().contains(hole))
}

/// Whether two ranges share no byte by the symbolic layout rules alone: two
/// whole fields of one object, or a field and the object with that field
/// as a hole.
pub(in crate::kernel) fn symbolic_ranges_disjoint(left: &MemoryRange, right: &MemoryRange) -> bool {
    let hole_of = |object: &MemoryRange, field: &MemoryRange| {
        object.symbolic_object().is_some_and(|layout| {
            field
                .symbolic_field()
                .is_some_and(|(base, field_layout, index)| {
                    field_layout == layout
                        && base == *object.base()
                        && object.holes().contains(&index)
                })
        })
    };
    if let (
        Some((left_object, left_layout, left_field)),
        Some((right_object, right_layout, right_field)),
    ) = (left.symbolic_field(), right.symbolic_field())
    {
        return left_layout == right_layout
            && left_object == right_object
            && left_field != right_field;
    }
    hole_of(left, right) || hole_of(right, left)
}

/// Whether `range` lies in `available` by the symbolic layout rules alone,
/// with no arithmetic: the same object, holes allowing, or one whole field
/// of it.
fn symbolic_range_shallowly_contained(range: &MemoryRange, available: &MemoryRange) -> bool {
    symbolic_object_covers_object(available, range)
        || symbolic_object_covers_field(available, range)
}

/// `object` with the field `field` names taken out: the residue of handing
/// out one whole field of a symbolic object, by the layout's rule that the
/// field lies inside the object and no other field shares its bytes.
fn symbolic_object_without_field(object: &MemoryRange, field: &MemoryRange) -> Option<MemoryRange> {
    let layout = object.symbolic_object()?;
    let (base, field_layout, field_index) = field.symbolic_field()?;
    if field_layout != layout
        || base != *object.base()
        || field.has_holes()
        || object.holes().contains(&field_index)
    {
        return None;
    }
    let mut holes = object.holes().to_vec();
    holes.push(field_index);
    holes.sort_unstable();
    Some(object.clone().with_holes(holes))
}

/// `object` with the field `field` names given back: the inverse of
/// [`symbolic_object_without_field`].
fn symbolic_object_with_field(
    object: &MemoryRange,
    field: &MemoryRange,
    assumptions: &PureFactContext,
) -> Option<MemoryRange> {
    let layout = object.symbolic_object()?;
    let (base, field_layout, field_index) = field.symbolic_field()?;
    if field_layout != layout
        || base != *object.base()
        || field.has_holes()
        || !object.holes().contains(&field_index)
        || !assumptions.provenance_equal(&object.provenance, &field.provenance)
    {
        return None;
    }
    let holes = object
        .holes()
        .iter()
        .copied()
        .filter(|hole| *hole != field_index)
        .collect();
    Some(object.clone().with_holes(holes))
}

/// Whether `available` is the whole object of a symbolic layout,
/// `[p, p + sizeof(L))`, and `required` lies in one of its fields: at
/// `p + offsetof(L, f)`, reaching no further than `f`. Fields lie inside
/// their object by the layout's rule, decided by lookup.
pub(in crate::kernel) fn symbolic_object_covers_field(
    available: &MemoryRange,
    required: &MemoryRange,
) -> bool {
    let field = crate::kernel::SymbolicLayoutName::field_displacement(&required.base().offset)
        .map(|(_, layout, field)| (layout, field));
    if required.has_holes() {
        return false;
    }
    // The required bytes from the field's start: a count, or the whole
    // object of an abstract type.
    let extent = match required.wide_bounds() {
        Some((start, end)) if start.uint64_as_const() == Some(0) => match end.uint64_as_const() {
            Some(count) => u32::try_from(count)
                .ok()
                .and_then(|count| count.checked_mul(required.element_width()))
                .map(crate::kernel::AccessExtent::Bytes),
            None => field
                .filter(|_| required.element_width() == 1)
                .map(|(layout, field)| layout.field_extent(field))
                .filter(|extent| extent.term() == *end),
        },
        Some(_) => None,
        None => (required.constant_start() == Some(0))
            .then(|| required.constant_end())
            .flatten()
            .and_then(|count| count.checked_mul(required.element_width()))
            .map(crate::kernel::AccessExtent::Bytes),
    };
    extent.is_some_and(|extent| {
        symbolic_object_holds_field_access(available, required.base(), extent)
    })
}

/// Whether `available` is the whole object of a symbolic layout,
/// `[p, p + sizeof(L))`, and an access of `extent` at `pointer` lies in one of
/// its fields that is not a hole: `pointer` is `p + offsetof(L, f)` and the
/// access reaches no further than `f`. Decided by lookup on the two terms.
pub(in crate::kernel) fn symbolic_object_holds_field_access(
    available: &MemoryRange,
    pointer: &Address,
    extent: crate::kernel::AccessExtent,
) -> bool {
    let object = available.base();
    let Some((rest, layout, field)) =
        crate::kernel::SymbolicLayoutName::field_displacement(&pointer.offset)
    else {
        // An access in the fixed prefix lies inside the object too.
        return available.element_width() == 1
            && pointer.base == object.base
            && available.wide_bounds().is_some_and(|(start, end)| {
                start.uint64_as_const() == Some(0)
                    && crate::kernel::SymbolicLayoutName::of_term(end).is_some_and(
                        |(layout, field)| {
                            field.is_none()
                                && crate::kernel::SymbolicLayoutName::constant_displacement(
                                    Some(&object.offset),
                                    &pointer.offset,
                                )
                                .is_some_and(|offset| {
                                    layout.within_prefix(offset, extent)
                                        && !available.holes().iter().any(|hole| {
                                            layout.fixed_field_meets(
                                                *hole,
                                                offset,
                                                extent.bytes().unwrap_or(0),
                                            )
                                        })
                                })
                        },
                    )
            });
    };
    !available.holes().contains(&field)
        && pointer.base == object.base
        && rest.map_or(object.offset.as_const() == Some(0), |rest| {
            *rest == object.offset
        })
        && available.element_width() == 1
        && available.wide_bounds().is_some_and(|(start, end)| {
            start.uint64_as_const() == Some(0) && *end == layout.size_term()
        })
        && layout.within_field(field, extent)
}

/// A field-sized footprint lies in one whole element of an unscaled range.
/// Keep the exact byte displacement separate from the element index: a
/// modular byte product cannot justify containment in a symbolic range.
pub(in crate::kernel) fn memory_range_covers_interior_element(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A range with holes holds only its other fields, by the field rules.
    if available.has_holes() {
        return false;
    }
    if available.constant_start() != Some(0) {
        return false;
    }
    fn split_constant(offset: &AddressOffset) -> Option<(AddressOffset, i64)> {
        match offset.view() {
            OffsetView::Constant(value) => Some((AddressOffset::constant(0), value)),
            OffsetView::Add(left, right) => {
                let (left, a) = split_constant(left)?;
                let (right, b) = split_constant(right)?;
                Some((AddressOffset::add(left, right), a.checked_add(b)?))
            }
            _ => Some((offset.clone(), 0)),
        }
    }
    let Some((start, count)) = constant_range_span(required) else {
        return false;
    };
    if count <= 0 {
        return false;
    }
    let Some(offset) = required.base().offset_from_base(available.base()) else {
        return false;
    };
    let Some((symbolic, constant)) = split_constant(&offset) else {
        return false;
    };
    let width = i64::from(available.element_width());
    let Some(first_byte) = start
        .checked_mul(i64::from(required.element_width()))
        .and_then(|start| start.checked_add(constant))
    else {
        return false;
    };
    let Some(bytes) = count.checked_mul(i64::from(required.element_width())) else {
        return false;
    };
    // This route only covers a footprint wholly within one owned object.
    if width == 0
        || first_byte
            .rem_euclid(width)
            .checked_add(bytes)
            .is_none_or(|end| end > width)
    {
        return false;
    }
    let Some(mut delta) = crate::kernel::reasoning::path_facts::exact_element_delta_from_offset(
        &symbolic,
        available.element_width(),
    ) else {
        return false;
    };
    let Some(constant) = delta.constant.checked_add(first_byte.div_euclid(width)) else {
        return false;
    };
    delta.constant = constant;
    let Some(index) = delta.as_index_term() else {
        return false;
    };
    if let Some(index) = index
        .operand_view()
        .word32_constant()
        .map(|index| index as i32)
        && index >= 0
        && let Some(next) = index.checked_add(1)
        && assumptions.exact_condition_value(&OldConditionTerm::signed_less_equal(
            OldMachineTerm::constant(next as u32),
            available.end().clone(),
        )) == Some(true)
    {
        return true;
    }
    crate::kernel::assumptions::bitvector_index_in_range_shallow_views(
        index.operand_view(),
        MachineOperandView::Old(available.start()),
        MachineOperandView::Old(available.end()),
        assumptions,
    )
}

/// A constant-length footprint inside one struct of a wide struct array
/// (`p[0u64..m]` of `k`-byte structs, or the byte block `p[0u64..m * k]`):
/// the field rule of [`PureFactContext::field_access_in_wide_struct_array`],
/// which places the footprint's first byte over the struct count instead of
/// comparing bytes with the wrapping product `m * k`.
fn memory_range_covers_struct_array_field(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if required.wide_bounds().is_some() || available.wide_bounds().is_none() {
        return false;
    }
    let Some(bytes) = constant_range_span(required)
        .and_then(|(_, count)| count.checked_mul(i64::from(required.element_width())))
        .and_then(|bytes| u32::try_from(bytes).ok())
        .filter(|bytes| *bytes > 0)
    else {
        return false;
    };
    let (start, _) = required.byte_footprint();
    assumptions.field_access_in_wide_struct_array(&start, bytes, available)
}

/// Whether `available` holds every byte of `required`, by the indexed and
/// structural routes below. A stated separation never vetoes a coverage
/// they prove: one range covering a nonempty other and being disjoint from it
/// are contradictory facts, under which either answer is sound, so asking
/// would only walk the separation facts for nothing.
fn memory_range_covers_by_routes(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A range with holes holds only its other fields, by the field rules.
    if available.has_holes() {
        return false;
    }
    if available.element_width() != required.element_width() {
        if memory_range_covers_interior_element(available, required, assumptions)
            || memory_range_covers_struct_array_field(available, required, assumptions)
        {
            return true;
        }
        // A footprint is bytes and the element width is only how the bytes
        // are spelled (D6), so a mismatch is rewritten into one coordinate
        // system instead of refusing. Neither rewrite adds or drops a byte,
        // so both are sound; the re-spelling is tried first because it keeps
        // the bases and endpoints the equal-width paths reason about.
        if required.wide_bounds().is_none()
            && memory_range_in_element_width(required, available.element_width()).is_some_and(
                |required| memory_range_covers_by_routes(available, &required, assumptions),
            )
        {
            return true;
        }
        // A wide range has no 32-bit byte count to renormalize to. Two wide
        // ranges of different widths are rewritten into one width when the
        // products that relate them are decided not to wrap; the requirement
        // is rewritten first, keeping the owner's coordinates, then the
        // owner. At most two attempts, each one re-spelling.
        if available.wide_bounds().is_some() || required.wide_bounds().is_some() {
            if wide_memory_range_in_element_width(required, available.element_width(), assumptions)
                .is_some_and(|required| {
                    memory_range_covers_by_routes(available, &required, assumptions)
                })
            {
                return true;
            }
            return wide_memory_range_in_element_width(
                available,
                required.element_width(),
                assumptions,
            )
            .is_some_and(|available| {
                memory_range_covers_by_routes(&available, required, assumptions)
            });
        }
        return memory_range_covers_by_routes(
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
    memory_range_covered_by_some_route(available, required, assumptions)
}

/// Interpret a signed endpoint as a native coordinate only when its complete
/// value survives truncation. Addition commutes modulo 2^32; the native upper
/// bound below rules out both truncation and crossing the signed high bit.
pub(in crate::kernel) fn checked_shared_native_range_endpoint(
    term: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> Option<SharedMachineIntegerTerm> {
    fn base(term: MachineOperandView<'_>) -> Option<MachineOperandView<'_>> {
        if term.variable().is_some() {
            Some(term)
        } else if let Some((MachineCastSpelling::UInt32From64, _, _, value)) = term.cast() {
            Some(value)
        } else {
            None
        }
    }
    let literal = |value| {
        let root = KernelTerm::retained_native_machine_operand(
            MachineIntegerType::UInt64,
            &OldMachineTerm::uint64_constant(value),
        );
        MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64)
    };
    let small = |value: MachineOperandView<'_>| {
        value
            .word32_constant()
            .filter(|value| *value <= i32::MAX as u32)
    };
    if let Some(value) = small(term) {
        return Some(literal(u64::from(value)));
    }
    let wide = if let Some(value) = base(term) {
        value.retain(MachineIntegerType::UInt64)
    } else if let Some((MachineIntegerType::Int32, MachineBinaryOp::Add, [left, right])) =
        term.binary()
    {
        let (value, constant) = if let Some(constant) = small(right) {
            (base(left)?, constant)
        } else if matches!(left.literal(), Some(int32_constant!(_))) {
            (base(right)?, small(left)?)
        } else {
            return None;
        };
        if assumptions.decide(&wide_index_comparison(
            CompareRelation::LessEqual,
            value,
            MachineOperandView::Old(&OldMachineTerm::uint64_constant(
                i32::MAX as u64 - u64::from(constant),
            )),
        )) != Some(true)
        {
            return None;
        }
        wide_index_binary(
            MachineBinaryOp::Add,
            value,
            literal(u64::from(constant)).operand_view(),
        )
    } else {
        return None;
    };
    (assumptions.decide(&wide_index_comparison(
        CompareRelation::LessEqual,
        wide.operand_view(),
        literal(i32::MAX as u64).operand_view(),
    )) == Some(true))
    .then_some(wide)
}

/// Coverage where either range is wide, for two equal-width ranges at one
/// base. Each range's bounds are read as unsigned 64-bit values: a wide
/// range's are its own, and an `Int32` range's are taken only when both
/// are checked to retain their complete nonnegative values. The
/// required range is covered when `available.start <= required.start` and
/// `required.end <= available.end` are decided as 64-bit comparisons. Any
/// other pairing is not covered.
pub(in crate::kernel) fn wide_memory_range_covers(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // A range with holes holds only its other fields, by the field rules.
    if available.has_holes() {
        return false;
    }
    if available.element_width() != required.element_width() {
        return false;
    }
    if !(available.base() == required.base()
        || pointers_proven_equal_for_memory_resolution(
            available.base(),
            required.base(),
            assumptions,
        ))
    {
        let Some((start, end)) = available.wide_bounds() else {
            return false;
        };
        return wide_memory_range_covers_window(
            available.base(),
            available.element_width(),
            [MachineOperandView::Old(start), MachineOperandView::Old(end)],
            required,
            assumptions,
        );
    }
    let (Some((available_start, available_end)), Some((required_start, required_end))) = (
        shared_wide_range_bounds(available, assumptions),
        shared_wide_range_bounds(required, assumptions),
    ) else {
        return false;
    };
    wide_bounds_cover(
        [available_start.operand_view(), available_end.operand_view()],
        [required_start.operand_view(), required_end.operand_view()],
        assumptions,
    )
}

fn wide_bounds_cover(
    available: [MachineOperandView<'_>; 2],
    required: [MachineOperandView<'_>; 2],
    assumptions: &PureFactContext,
) -> bool {
    let holds = |lower: MachineOperandView<'_>, upper: MachineOperandView<'_>| {
        lower.retain(MachineIntegerType::UInt64) == upper.retain(MachineIntegerType::UInt64)
            || assumptions.decide(&wide_index_comparison(
                CompareRelation::LessEqual,
                lower,
                upper,
            )) == Some(true)
    };
    holds(available[0], required[0]) && holds(required[1], available[1])
}

/// Coverage of a window at another base, with native uint64 bounds or
/// nonnegative constant int32 bounds. Translated endpoints use subtraction
/// guards to avoid wrapping. A suffix `(whole - count)[0..count]` additionally
/// transports a checked observer value to the available endpoint.
fn wide_memory_range_covers_window(
    available_base: &Address,
    available_width: u32,
    available_bounds: [MachineOperandView<'_>; 2],
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    let (first, last) = match required.wide_bounds() {
        Some((first, last)) => (first.clone(), last.clone()),
        None => {
            let (Some(first), Some(last)) = (
                required
                    .signed_constant_start()
                    .and_then(|value| u64::try_from(value).ok()),
                required
                    .signed_constant_end()
                    .and_then(|value| u64::try_from(value).ok()),
            ) else {
                return false;
            };
            (
                OldMachineTerm::uint64_constant(first),
                OldMachineTerm::uint64_constant(last),
            )
        }
    };
    let holds = |lower: MachineOperandView<'_>, upper: MachineOperandView<'_>| {
        lower.retain(MachineIntegerType::UInt64) == upper.retain(MachineIntegerType::UInt64)
            || assumptions.decide(&wide_index_comparison(
                CompareRelation::LessEqual,
                lower,
                upper,
            )) == Some(true)
    };
    let [start_view, end_view] = available_bounds;
    let first_view = MachineOperandView::Old(&first);
    let last_view = MachineOperandView::Old(&last);
    // Native translated windows require a non-wrapping byte span. Keep
    // the existing constant-int32 window path unchanged.
    if required.wide_bounds().is_some()
        && !holds(
            end_view,
            MachineOperandView::Old(&OldMachineTerm::uint64_constant(
                i64::MAX as u64 / u64::from(available_width),
            )),
        )
    {
        return false;
    }
    if !holds(first_view, last_view) {
        return false;
    }
    let mut selected = required.base().clone();
    if let Some(offset) = crate::kernel::equality_graph::AffineOffset::of(&selected.offset)
        .and_then(|offset| offset.to_offset_term())
    {
        selected.set_offset(offset);
    }
    if !pointers_proven_equal_for_memory_resolution(&selected, required.base(), assumptions) {
        return false;
    }
    let aligned = assumptions
        .pointer_at_known_base_with_wide_index(&selected, available_base)
        .unwrap_or_else(|| selected.clone());
    let covers_index = |index: SharedMachineIntegerTerm| {
        let index = index.operand_view();
        if let Some((MachineIntegerType::UInt64, MachineBinaryOp::Subtract, [whole, taken])) =
            index.binary()
            && (assumptions.decide(&wide_index_comparison(
                CompareRelation::Equal,
                last_view,
                taken,
            )) == Some(true)
                || holds(last_view, taken))
            && assumptions.uint64_values_equal_for_range_resolution_views(end_view, whole)
            && holds(taken, end_view)
        {
            // The full-width underflow guard keeps the requested suffix in bounds.
            return start_view.uint64_constant() == Some(0) || holds(start_view, index);
        }
        if let Some((MachineIntegerType::UInt64, MachineBinaryOp::Subtract, [whole, skipped])) =
            last_view.binary()
            && first_view.uint64_constant() == Some(0)
            && assumptions.uint64_values_equal_for_range_resolution_views(index, skipped)
            && assumptions.uint64_values_equal_for_range_resolution_views(end_view, whole)
            && holds(index, end_view)
        {
            return start_view.uint64_constant() == Some(0) || holds(start_view, index);
        }
        (start_view.uint64_constant() == Some(0) || holds(start_view, index))
            && ((holds(index, end_view)
                && holds(
                    last_view,
                    wide_index_binary(MachineBinaryOp::Subtract, end_view, index).operand_view(),
                ))
                || (holds(last_view, end_view)
                    && holds(
                        index,
                        wide_index_binary(MachineBinaryOp::Subtract, end_view, last_view)
                            .operand_view(),
                    )))
    };
    // The supplied address can already carry the complete native coordinate.
    // Use it before alignment can choose another spelling of the same address.
    if assumptions
        .shared_wide_element_index_of_access(&selected, available_base, available_width)
        .is_some_and(&covers_index)
    {
        return true;
    }
    // Only aliases explicitly indexed for this selected address are candidates.
    // Each candidate still owes exact address equality and the complete native
    // span; equality proposes a spelling, never memory authority.
    std::iter::once(aligned)
        .chain(assumptions.exact_pointer_aliases(&selected).cloned())
        .chain(assumptions.exact_pointer_offset_aliases(&selected))
        .any(|candidate| {
            crate::instrumentation::record_deterministic_work(1);
            if !pointers_proven_equal_for_memory_resolution(&candidate, &selected, assumptions) {
                return false;
            }
            assumptions
                .shared_wide_element_index_of_access(&candidate, available_base, available_width)
                .is_some_and(&covers_index)
        })
}

/// Whether two ranges, at least one of them wide, are proven to overlap.
/// Constant same-base ranges compare exact byte coordinates. Otherwise they
/// must have one base and one element width, and `a.start <
/// b.end`, `b.start < a.end` and each range's `start < end` are decided as
/// unsigned 64-bit comparisons. An `Int32` range takes part through
/// nonnegative constant bounds only. Anything undecided is not proven.
pub(in crate::kernel) fn wide_memory_ranges_proven_overlapping(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    // The neighbour index orders complete byte intervals, including mixed
    // element widths. Compare those exact intervals before symbolic rules.
    if left.base() == right.base()
        && let (Some(a), Some(b), Some(c), Some(d)) = (
            constant_relative_byte_endpoints(left).0,
            constant_relative_byte_endpoints(left).1,
            constant_relative_byte_endpoints(right).0,
            constant_relative_byte_endpoints(right).1,
        )
    {
        return a < b && c < d && a < d && c < b;
    }
    if left.element_width() != right.element_width()
        || !(left.base() == right.base()
            || pointers_proven_equal_for_memory_resolution(left.base(), right.base(), assumptions))
    {
        return false;
    }
    let bounds = |range: &MemoryRange| match range.wide_bounds() {
        Some((start, end)) => Some((start.clone(), end.clone())),
        None => {
            let start = u64::try_from(range.signed_constant_start()?).ok()?;
            let end = u64::try_from(range.signed_constant_end()?).ok()?;
            Some((
                OldMachineTerm::uint64_constant(start),
                OldMachineTerm::uint64_constant(end),
            ))
        }
    };
    let (Some((left_start, left_end)), Some((right_start, right_end))) =
        (bounds(left), bounds(right))
    else {
        return false;
    };
    let below = |lower: &OldMachineTerm, upper: &OldMachineTerm| {
        assumptions.decide(&OldConditionTerm::uint64_less_than(
            lower.clone(),
            upper.clone(),
        )) == Some(true)
    };
    below(&left_start, &left_end)
        && below(&right_start, &right_end)
        && below(&left_start, &right_end)
        && below(&right_start, &left_end)
}

/// The positive coverage routes of [`memory_range_covers`], for two
/// equal-width ranges that are not syntactically equal and not in provably
/// distinct blocks. The caller applies the explicit-separation veto.
fn memory_range_covered_by_some_route(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if available.wide_bounds().is_some() || required.wide_bounds().is_some() {
        return wide_memory_range_covers(available, required, assumptions);
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

fn memory_resource_fact_range(fact: &ResourceFact) -> Option<&MemoryRange> {
    match fact {
        ResourceFact::Own(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
            _,
        )
        | ResourceFact::View(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
        ) => None,
        ResourceFact::Own(Resource::Memory(range), _)
        | ResourceFact::View(Resource::Memory(range)) => Some(range),
        ResourceFact::Own(
            Resource::Composite { .. }
            | Resource::Token { .. }
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_),
            _,
        )
        | ResourceFact::View(
            Resource::Composite { .. }
            | Resource::Token { .. }
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_),
        ) => None,
    }
}

/// A structurally known shorter footprint cannot supply the whole request,
/// regardless of pointer spelling. Do not ask pointer/order reasoning to
/// rediscover this refusal before composing selected adjacent pieces.
fn memory_range_definitely_shorter(available: &MemoryRange, required: &MemoryRange) -> bool {
    let bytes = |range: &MemoryRange| -> Option<u64> {
        let (start, end) = range.int32_bounds()?;
        let count = OldMachineTerm::subtract(end.clone(), start.clone()).as_const()?;
        // Only use a representable nonnegative signed element count.
        (count <= i32::MAX as u32).then_some(u64::from(count) * u64::from(range.element_width()))
    };
    matches!((bytes(available), bytes(required)), (Some(a), Some(r)) if a < r)
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
fn constant_range_span(range: &MemoryRange) -> Option<(i64, i64)> {
    let start = range.constant_start()? as i32;
    let end = range.constant_end()? as i32;
    Some((i64::from(start), i64::from(end.wrapping_sub(start))))
}

/// Whether `required`, whose first element sits `delta` elements from
/// `available`'s base, lies inside `available`.
///
/// Every input is an exact `i64`, so this is interval containment and owes no
/// premise of its own: the caller's obligation is to have obtained `delta`
/// exactly. A reversed range is refused rather than answered, because neither
/// side of this test means what it reads as when a count runs backwards.
fn constant_spans_contain(available: (i64, i64), delta: i64, required: (i64, i64)) -> Option<bool> {
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
/// `Address::element_index_from_base_with_width` answers with one modular
/// term, which names the delta only modulo `2^32`; a containment conclusion
/// reads the delta as a number, so it takes
/// [`Address::exact_element_delta_from_base`] instead. That keeps the constant
/// part in `i64` beside at most one symbolic index, and the index's *signed*
/// value is part of the delta — which is why `exact_signed_constant` may be
/// asked for it, and may not be asked for a residue.
fn exact_constant_base_delta(
    available: &MemoryRange,
    required: &MemoryRange,
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
    crate::kernel::assumptions::exact_signed_constant_view(
        delta.index.operand_view(),
        assumptions?,
    )?
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
/// to build both relative endpoints with the modular `OldMachineTerm::add`
/// and compare them as an order, so a base `i32::MIN` elements below the owner
/// carried `q[-1..0]` back into it.
///
/// Answering `None` rather than `Some(false)` where the arithmetic no longer
/// settles it matters: `Some` is a short-circuit, and the routes below this one
/// are the exact ones.
fn memory_range_structurally_covers(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: Option<&PureFactContext>,
) -> Option<bool> {
    // A range with holes holds only its other fields, by the field rules.
    if available.has_holes() {
        return None;
    }
    if available.element_width() != required.element_width() {
        return None;
    }
    let delta = if required.base() == available.base() {
        0
    } else {
        exact_constant_base_delta(available, required, assumptions)?
    };
    constant_spans_contain(
        constant_range_span(available)?,
        delta,
        constant_range_span(required)?,
    )
}

fn memory_ranges_structurally_disjoint(left: &MemoryRange, right: &MemoryRange) -> bool {
    if left.base().blocks_proven_distinct(right.base()) || symbolic_ranges_disjoint(left, right) {
        return true;
    }
    // A wide range has no constant bounds to compare structurally.
    if left.element_width() != right.element_width()
        || left.wide_bounds().is_some()
        || right.wide_bounds().is_some()
    {
        return false;
    }
    let Some(base_delta) = right
        .base()
        .shared_element_index_from_base_with_width(left.base(), left.element_width())
    else {
        return false;
    };
    let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
        left.constant_start().map(|value| value as i32),
        left.constant_end().map(|value| value as i32),
        crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Old(right.start()),
        )
        .operand_view()
        .word32_constant()
        .map(|value| value as i32),
        crate::kernel::assumptions::index_binary(
            MachineBinaryOp::Add,
            base_delta.operand_view(),
            MachineOperandView::Old(right.end()),
        )
        .operand_view()
        .word32_constant()
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
/// `p[0..3]`) the way
/// [`crate::kernel::assumptions::memory_range_contained_for_memory_resolution`]
/// already reads them; anything else has to be decided from the context, as
/// `p[0..n]` is under `0 <= n`.
fn consumed_range_is_well_formed(
    start: MachineOperandView<'_>,
    end: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    // An affine constant difference is the true one only modulo 2^32, so
    // `difference >= 0` is not "runs forward": a difference of 2^32 is a range
    // of zero elements, and one of -2^32 is too. The residue is the count, and
    // reading it as a forward span needs it inside the signed range a count
    // may occupy; anything else falls through to the decision procedure rather
    // than answering from arithmetic that wrapped.
    if let Some(difference) =
        crate::kernel::assumptions::affine_bitvector_difference_constant_views(end, start)
        && (0..=i64::from(i32::MAX)).contains(&difference)
    {
        return true;
    }
    assumptions.decide(&crate::kernel::assumptions::index_comparison(
        CompareRelation::LessEqual,
        start,
        end,
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
    delta: MachineOperandView<'_>,
    endpoint: MachineOperandView<'_>,
    assumptions: &PureFactContext,
) -> bool {
    if delta.word32_constant() == Some(0) || endpoint.word32_constant() == Some(0) {
        return true;
    }
    if let (Some(a), Some(b)) = (delta.word32_constant(), endpoint.word32_constant()) {
        return i32::try_from(i64::from(a as i32) + i64::from(b as i32)).is_ok();
    }
    let query = crate::kernel::machine_integer::definedness::OverflowQueryView::from_operands(
        MachineIntegerType::Int32,
        crate::kernel::machine_integer::Operation::Add,
        [delta, endpoint],
    )
    .expect("int32 addition");
    assumptions.decide_overflow_query(&query) == Some(false)
}

/// The wide lookup key of an `Int32` range: its [`wide_normalization_form`],
/// or, for a range at its own root with nonnegative constant bounds, those
/// bounds as unsigned 64-bit values. A constant piece a composite body
/// splits off the front of a wide owned range, `p[0..1]` beside
/// `p[1..n + 1]`, then meets its wide neighbour. Like the form itself, this
/// only proposes a pair; [`merge_memory_ranges`] checks the merge.
fn native_wide_normalization_key(
    range: &MemoryRange,
) -> Option<(
    Address,
    WideNormalizationEndpointKey,
    WideNormalizationEndpointKey,
)> {
    let shifted = matches!(range.base().offset.view(), OffsetView::Add(_, last)
        if matches!(last.view(), OffsetView::Int64Scaled { byte_width, unsigned: true, .. }
            if byte_width == i64::from(range.element_width())));
    if !shifted {
        if let Some((start, end)) = range.wide_bounds() {
            return Some((
                range.base().clone(),
                wide_normalization_endpoint_key(MachineOperandView::Old(start)),
                wide_normalization_endpoint_key(MachineOperandView::Old(end)),
            ));
        }
        let constant = |bound: &OldMachineTerm| {
            let value = bound.as_const()?;
            (value as i32 >= 0).then_some(WideNormalizationEndpointKey::Constant(u64::from(value)))
        };
        return Some((
            range.base().clone(),
            constant(range.start())?,
            constant(range.end())?,
        ));
    }
    let (base, start, end) = wide_normalization_form(range)?;
    Some((
        base,
        wide_normalization_endpoint_key(start.operand_view()),
        wide_normalization_endpoint_key(end.operand_view()),
    ))
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
/// The wide normalization spelling of a range: its base with any trailing
/// unsigned 64-bit element index moved into the bounds, `(x + i)[s..e]` as
/// `x[i + s..i + e]`, with the sums formed as [`shared_rebased_wide_bounds`] forms
/// them so two pieces that abut meet at one term. An `Int32` range takes
/// part only at such a base and with nonnegative constant bounds. The form is
/// a lookup key; the merge it proposes is checked by [`merge_memory_ranges`].
pub(super) fn wide_normalization_form(
    range: &MemoryRange,
) -> Option<(Address, SharedMachineIntegerTerm, SharedMachineIntegerTerm)> {
    let width = i64::from(range.element_width());
    let (root, index) = match range.base().offset.view() {
        OffsetView::Add(rest, last) => match last.view() {
            OffsetView::Int64Scaled {
                index,
                byte_width,
                unsigned: true,
            } if byte_width == width => (range.base().with_offset(rest.clone()), Some(index)),
            _ => (range.base().clone(), None),
        },
        _ => (range.base().clone(), None),
    };
    let (start, end) = match range.wide_bounds() {
        Some((start, end)) => (
            SharedMachineIntegerTerm::index(MachineIntegerType::UInt64, start.clone()),
            SharedMachineIntegerTerm::index(MachineIntegerType::UInt64, end.clone()),
        ),
        None => {
            index.as_ref()?;
            let constant = |bound: &OldMachineTerm| {
                let value = bound.as_const()?;
                (value as i32 >= 0).then(|| {
                    SharedMachineIntegerTerm::index(
                        MachineIntegerType::UInt64,
                        OldMachineTerm::uint64_constant(u64::from(value)),
                    )
                })
            };
            (constant(range.start())?, constant(range.end())?)
        }
    };
    let Some(index) = index else {
        return Some((root, start, end));
    };
    let shifted = |bound: SharedMachineIntegerTerm| {
        if bound.operand_view().uint64_constant() == Some(0) {
            index.clone()
        } else {
            wide_index_binary(
                MachineBinaryOp::Add,
                index.operand_view(),
                bound.operand_view(),
            )
        }
    };
    Some((root, shifted(start), shifted(end)))
}

/// A range's bounds as retained unsigned 64-bit values. Signed endpoints
/// participate only when their complete values fit in `0..=INT_MAX`.
pub(in crate::kernel) fn shared_wide_range_bounds(
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> Option<(SharedMachineIntegerTerm, SharedMachineIntegerTerm)> {
    let retain = |value: &OldMachineTerm| {
        let view = MachineOperandView::Old(value);
        if view.literal().is_some() || view.variable().is_some() {
            let root =
                KernelTerm::retained_native_machine_operand(MachineIntegerType::UInt64, value);
            MachineOperandView::Shared(&root).retain(MachineIntegerType::UInt64)
        } else {
            view.retain(MachineIntegerType::UInt64)
        }
    };
    match range.wide_bounds() {
        Some((start, end)) => Some((retain(start), retain(end))),
        None => Some((
            checked_shared_native_range_endpoint(
                MachineOperandView::Old(range.start()),
                assumptions,
            )?,
            checked_shared_native_range_endpoint(
                MachineOperandView::Old(range.end()),
                assumptions,
            )?,
        )),
    }
}

/// Rebase only the coordinates: `(base + i)[s..e]` becomes `[i+s..i+e]`.
/// Held wide ranges bound each summand by `i64::MAX / width`, so the
/// additions do not wrap. No temporary native range is constructed for a check.
fn shared_rebased_wide_bounds(
    range: &MemoryRange,
    base: &Address,
    assumptions: &PureFactContext,
) -> Option<(SharedMachineIntegerTerm, SharedMachineIntegerTerm)> {
    let index = assumptions.shared_wide_element_index_of_access(
        range.base(),
        base,
        range.element_width(),
    )?;
    let (start, end) = shared_wide_range_bounds(range, assumptions)?;
    let shifted = |bound: SharedMachineIntegerTerm| {
        if bound.operand_view().uint64_constant() == Some(0) {
            index.clone()
        } else if index.operand_view().uint64_constant() == Some(0) {
            bound
        } else {
            wide_index_binary(
                MachineBinaryOp::Add,
                index.operand_view(),
                bound.operand_view(),
            )
        }
    };
    Some((shifted(start), shifted(end)))
}

/// MemoryRange still owns native endpoints. Convert only a final output;
/// neither range checks nor coordinate reconstruction call this adapter.
fn wide_endpoint_output(endpoint: SharedMachineIntegerTerm) -> OldMachineTerm {
    endpoint
        .operand_view()
        .literal()
        .unwrap_or_else(|| endpoint.structural_value().clone())
}

pub(in crate::kernel) fn split_memory_range(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> Option<Vec<MemoryRange>> {
    // One whole field out of a symbolic object leaves the object with a
    // hole: its fields' order is not known, so no byte interval is.
    if let Some(residue) = symbolic_object_without_field(available, required) {
        return Some(vec![residue]);
    }
    if available.has_holes() || required.has_holes() {
        return (available == required).then(Vec::new);
    }
    if available.wide_bounds().is_some() || required.wide_bounds().is_some() {
        if available.element_width() != required.element_width() {
            // As coverage does: rewrite the requirement into the owner's
            // width, keeping the residues in the owner's coordinates, else
            // the owner into the requirement's. Both need their products
            // decided not to wrap, so no byte is added or dropped.
            return wide_memory_range_in_element_width(
                required,
                available.element_width(),
                assumptions,
            )
            .and_then(|required| split_memory_range(available, &required, assumptions))
            .or_else(|| {
                let available = wide_memory_range_in_element_width(
                    available,
                    required.element_width(),
                    assumptions,
                )?;
                split_memory_range(&available, required, assumptions)
            });
        }
        let (start, end) = shared_wide_range_bounds(available, assumptions)?;
        // A window at another spelling of the base, `(bytes + index)[0..4]`
        // inside `bytes[0..length]`, is restated at the available base. Its
        // coverage is what bounds `index + 4` by the available end.
        let same_base = pointers_proven_equal_for_memory_resolution(
            available.base(),
            required.base(),
            assumptions,
        );
        let (first, last) = if same_base {
            shared_wide_range_bounds(required, assumptions)?
        } else {
            if !memory_range_covers(available, required, assumptions) {
                return None;
            }
            shared_rebased_wide_bounds(required, available.base(), assumptions)?
        };
        let holds = |lower: &SharedMachineIntegerTerm, upper: &SharedMachineIntegerTerm| {
            lower == upper
                || assumptions.decide(&wide_index_comparison(
                    CompareRelation::LessEqual,
                    lower.operand_view(),
                    upper.operand_view(),
                )) == Some(true)
        };
        // Coverage of a rebased window already placed it inside the available
        // range; its sums need not be decided again.
        if same_base && (!holds(&start, &first) || !holds(&first, &last) || !holds(&last, &end)) {
            return None;
        }
        let equal = |left: &SharedMachineIntegerTerm, right: &SharedMachineIntegerTerm| {
            left == right
                || assumptions.decide(&wide_index_comparison(
                    CompareRelation::Equal,
                    left.operand_view(),
                    right.operand_view(),
                )) == Some(true)
        };
        let mut residues = Vec::new();
        if !equal(&start, &first) {
            residues.push(
                MemoryRange::new_wide(
                    available.base().clone(),
                    wide_endpoint_output(start),
                    wide_endpoint_output(first),
                    available.element_width(),
                )
                .with_carrier_of(available),
            );
        }
        if !equal(&last, &end) {
            residues.push(
                MemoryRange::new_wide(
                    available.base().clone(),
                    wide_endpoint_output(last),
                    wide_endpoint_output(end),
                    available.element_width(),
                )
                .with_carrier_of(available),
            );
        }
        return Some(residues);
    }
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
    // equivalent load from a later memory state; retaining it would create
    // a symbolic zero-length residue when the required range exhausts the
    // beginning of `available`.
    let available_start_pointer = available.start_pointer();
    let base_delta = if pointers_proven_equal_for_memory_resolution(
        required.base(),
        &available_start_pointer,
        assumptions,
    ) {
        Some(MachineOperandView::Old(available.start()).retain(MachineIntegerType::Int32))
    } else {
        required
            .base()
            .shared_element_index_from_base_with_width(available.base(), available.element_width())
            .or_else(|| {
                pointer_bases_equal_with_load_bridging(
                    required.base(),
                    available.base(),
                    assumptions,
                )
                .then(|| {
                    MachineOperandView::Old(&OldMachineTerm::constant(0))
                        .retain(MachineIntegerType::Int32)
                })
            })
    }?;
    let required_start = crate::kernel::assumptions::index_binary(
        MachineBinaryOp::Add,
        base_delta.operand_view(),
        MachineOperandView::Old(required.start()),
    );
    let required_end = crate::kernel::assumptions::index_binary(
        MachineBinaryOp::Add,
        base_delta.operand_view(),
        MachineOperandView::Old(required.end()),
    );
    let keeps_prefix = assumptions.decide(&crate::kernel::assumptions::index_comparison(
        CompareRelation::Equal,
        MachineOperandView::Old(available.start()),
        required_start.operand_view(),
    )) != Some(true)
        && !range_endpoint_views_equal(
            MachineOperandView::Old(available.start()),
            required_start.operand_view(),
            assumptions,
        );
    let keeps_suffix = assumptions.decide(&crate::kernel::assumptions::index_comparison(
        CompareRelation::Equal,
        required_end.operand_view(),
        MachineOperandView::Old(available.end()),
    )) != Some(true)
        && !range_endpoint_views_equal(
            required_end.operand_view(),
            MachineOperandView::Old(available.end()),
            assumptions,
        );
    // A join that becomes a residue's own bound has to be the sum and not its
    // residue; see `exact_shifted_endpoint`. A join that bounds no residue is
    // never read as a position — it has just been shown equal to an endpoint
    // the owner already carried — so it owes nothing.
    if keeps_prefix
        && !exact_shifted_endpoint(
            base_delta.operand_view(),
            MachineOperandView::Old(required.start()),
            assumptions,
        )
    {
        return None;
    }
    if keeps_suffix
        && !exact_shifted_endpoint(
            base_delta.operand_view(),
            MachineOperandView::Old(required.end()),
            assumptions,
        )
    {
        return None;
    }
    if keeps_prefix
        && keeps_suffix
        && !consumed_range_is_well_formed(
            required_start.operand_view(),
            required_end.operand_view(),
            assumptions,
        )
    {
        return None;
    }
    let mut residues = Vec::new();
    if keeps_prefix {
        residues.push(available.with_bounds(
            available.base().clone(),
            available.start().clone(),
            required_start.structural_value().clone(),
        ));
    }
    if keeps_suffix {
        residues.push(available.with_bounds(
            available.base().clone(),
            required_end.structural_value().clone(),
            available.end().clone(),
        ));
    }
    Some(residues)
}

pub(crate) fn memory_ranges_proven_overlapping(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    memory_ranges_proven_overlapping_with_separation(left, right, assumptions, true)
}

pub(crate) fn memory_ranges_proven_overlapping_ignoring_separation(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    memory_ranges_proven_overlapping_with_separation(left, right, assumptions, false)
}

/// Entry checks the written ownership/view partition before it can use that
/// partition as separation evidence. Align the two selected ranges using
/// the checked pointer graph, including a retained additive address when a
/// pointer names an interior address. Either endpoint can carry the spine.
pub(in crate::kernel) fn contract_entry_memory_overlap(
    owned: &MemoryRange,
    viewed: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    #[cfg(test)]
    let _fast = crate::kernel::search::FastOperationScope::enter("contract entry view overlap");
    let wide = owned.wide_bounds().is_some() || viewed.wide_bounds().is_some();
    let overlap = |left: &MemoryRange, right: &MemoryRange| {
        super::super::borrows::protected_ranges_constant_overlap(left, right).unwrap_or_else(|| {
            // Wide range comparison can consult memory-resolution separation
            // while matching bases. Entry needs a common base established
            // by the pointer graph alone, or exact byte geometry.
            if wide && left.base() != right.base() {
                return constant_memory_overlap(left, right) == Some(true);
            }
            memory_ranges_proven_overlapping_ignoring_separation(left, right, assumptions)
        })
    };
    let compare = |left: &MemoryRange, right: &MemoryRange| {
        [(left, right), (right, left)]
            .into_iter()
            .any(|(left, right)| {
                overlap(left, right)
                    || assumptions
                        .equality_graph
                        .pointer_at_base(right.base(), left.base())
                        .is_some_and(|aligned| {
                            aligned != *right.base() && overlap(left, &right.with_base(aligned))
                        })
            })
    };
    if wide
        || (constant_memory_coordinates(owned).is_some()
            && constant_memory_coordinates(viewed).is_some())
    {
        return compare(owned, viewed);
    }
    // The byte form keeps the selected start address available to the index
    // when a symbolic range's bounds are written in different element units.
    compare(
        &byte_normalized_memory_range(owned),
        &byte_normalized_memory_range(viewed),
    )
}

/// Exact geometry in a shared coordinate system. None means the bases or
/// bounds need other reasoning, not that the ranges are disjoint.
pub(in crate::kernel) fn constant_memory_overlap(
    left: &MemoryRange,
    right: &MemoryRange,
) -> Option<bool> {
    let (left_origin, a, b) = constant_memory_coordinates(left)?;
    let (right_origin, c, d) = constant_memory_coordinates(right)?;
    (left_origin == right_origin).then_some(a < b && c < d && a < d && c < b)
}

fn memory_ranges_proven_overlapping_with_separation(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
    use_separation: bool,
) -> bool {
    // A symbolic object with holes overlaps only its remaining fields, which
    // no rule here decides; it is never proven to overlap.
    if left.has_holes() || right.has_holes() {
        return false;
    }
    #[cfg(test)]
    let _fast = crate::kernel::search::FastOperationScope::enter("selected ownership overlap");
    if memory_ranges_proven_overlapping_without_aliases(left, right, assumptions, use_separation) {
        return true;
    }
    // Query recorded equalities even between structurally distinct blocks:
    // contradictory supplied aliases must still expose duplicate ownership.
    // Two nonempty constant byte spans sharing their first address overlap,
    // even when a recorded equality translates one base (p == q + 8).
    // Query the selected endpoints, never spellings in either alias class.
    let nonempty = |range: &MemoryRange| {
        let (start, end) = constant_relative_byte_endpoints(range);
        start.zip(end).is_some_and(|(start, end)| start < end)
    };
    if nonempty(left)
        && nonempty(right)
        && assumptions.pointers_known_equal(&left.start_pointer(), &right.start_pointer())
        && (!use_separation
            || !assumptions
                .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    left, right,
                ))
    {
        return true;
    }
    // A recorded equality supplies one common coordinate system. Query its
    // maintained graph directly; never enumerate either base's alias class.
    left.base() != right.base()
        && assumptions.pointers_known_equal(left.base(), right.base())
        && memory_ranges_proven_overlapping_without_aliases(
            left,
            &right.with_base(left.base().clone()),
            assumptions,
            use_separation,
        )
}

fn memory_ranges_proven_overlapping_without_aliases(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
    use_separation: bool,
) -> bool {
    // Empty constant intervals own no bytes. This must agree with the
    // neighbour index, which omits them so they cannot hide an overlap.
    let empty = |range: &MemoryRange| {
        let (start, end) = constant_relative_byte_endpoints(range);
        start.zip(end).is_some_and(|(start, end)| start >= end)
    };
    if empty(left) || empty(right) {
        return false;
    }
    if left.base().blocks_proven_distinct(right.base()) {
        return false;
    }
    if let Some(overlap) = constant_memory_overlap(left, right) {
        return overlap
            && (!use_separation
                || !assumptions
                    .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                        left, right,
                    ));
    }
    if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
        return wide_memory_ranges_proven_overlapping(left, right, assumptions)
            && (!use_separation
                || !assumptions
                    .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                        left, right,
                    ));
    }
    // Footprints are bytes (D6): two spellings of overlapping bytes at
    // different element widths overlap, so the memory family's validity check
    // refuses two owners of them. Rewrite both sides to width-1 footprints
    // before deciding, exactly as the borrow oracle does
    // (`protected_range_proven_overlapping`).
    if left.element_width() != right.element_width() {
        let left = byte_normalized_memory_range(left);
        let right = byte_normalized_memory_range(right);
        return memory_ranges_proven_overlapping_without_aliases(
            &left,
            &right,
            assumptions,
            use_separation,
        );
    }
    let Some(base_delta) = right
        .base()
        .shared_element_index_from_base_with_width(left.base(), left.element_width())
    else {
        return false;
    };
    let right_start = crate::kernel::assumptions::index_binary(
        MachineBinaryOp::Add,
        base_delta.operand_view(),
        MachineOperandView::Old(right.start()),
    );
    let right_end = crate::kernel::assumptions::index_binary(
        MachineBinaryOp::Add,
        base_delta.operand_view(),
        MachineOperandView::Old(right.end()),
    );

    // An explicit separation only vetoes an overlap the endpoints prove, and
    // a valid composition proves none: ask it last, so the ordinary answer
    // (no proven overlap) never pays for the separation search.
    assumptions.decide(&crate::kernel::assumptions::index_comparison(
        CompareRelation::LessThan,
        MachineOperandView::Old(left.start()),
        right_end.operand_view(),
    )) == Some(true)
        && assumptions.decide(&crate::kernel::assumptions::index_comparison(
            CompareRelation::LessThan,
            right_start.operand_view(),
            MachineOperandView::Old(left.end()),
        )) == Some(true)
        && (!use_separation
            || !assumptions
                .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    left, right,
                ))
}

/// The same containment as [`memory_range_structurally_covers`], for a base
/// delta the facts pin rather than the offsets alone.
///
/// An element index is signed: `Address::offset_by_elements` sign-extends it
/// before scaling, so element `-1` of `p` is the element below `p`. This read
/// both endpoints of both ranges through `as_const`, which answers `u32`, so a
/// `-1` start arrived as `4294967295` and `p[-1..0]` — the element *before*
/// the range — passed `available_start <= required_start` against every owner
/// whose own end cleared `0`. A caller owning `p[0..1]` could hand `p[-1..0]`
/// to a callee and have it written.
fn memory_range_covers_with_exact_index(
    available: &MemoryRange,
    required: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    let Some(delta) = exact_constant_base_delta(available, required, Some(assumptions)) else {
        return false;
    };
    let (Some(available), Some(required)) = (
        constant_range_span(available),
        constant_range_span(required),
    ) else {
        return false;
    };
    constant_spans_contain(available, delta, required) == Some(true)
}

impl Resource {
    pub fn family(&self) -> ResourceFamily {
        match self {
            Self::Footprint(_) | Self::Parameter(_) | Self::Emp | Self::Star(_) => {
                ResourceFamily::Parameter
            }
            Self::Memory(_) => ResourceFamily::Memory,
            Self::PopulationAuthority(_) => ResourceFamily::PopulationAuthority,
            Self::Composite { .. } => ResourceFamily::Composite,
            Self::Token { .. } => ResourceFamily::Token,
            Self::Instance(_) => ResourceFamily::Instance,

            Self::ConditionalMutexGuard(_) | Self::MutexGuard(_) => ResourceFamily::MutexGuard,
            Self::MutexLive(_) => ResourceFamily::MutexLive,
            Self::MutexUse(_) => ResourceFamily::MutexUse,
            Self::Iterated(_) => ResourceFamily::Iterated,
            Self::Publication(_) => ResourceFamily::Publication,
        }
    }
}

impl ResourceFact {
    /// The fact's access and resource name in a diagnostic, as `owns
    /// pair(...)` or `views memory`.
    pub(crate) fn diagnostic_summary(&self) -> String {
        let access = if self.is_own() { "owns" } else { "views" };
        match self.resource() {
            Resource::Composite { .. } | Resource::Token { .. } | Resource::Instance(_) => {
                format!("{access} {}(...)", self.resource().diagnostic_name())
            }
            resource => format!("{access} {}", resource.diagnostic_name()),
        }
    }

    fn has_valid_exclusive_access(&self) -> bool {
        !matches!(
            self.resource(),
            Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
        ) || matches!(self, Self::Own(_, quantity) if quantity.as_const() == Some(1))
    }

    pub const ALLOCATION_RESOURCE_NAME: &'static str = "allocation";

    pub fn own_memory(range: MemoryRange) -> Self {
        Self::own(Resource::Memory(range))
    }

    pub fn view_memory(range: MemoryRange) -> Self {
        Self::View(Resource::Memory(range))
    }

    pub fn own_composite(name: String, arguments: Vec<ProgramValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::Program).collect();
        Self::own(Resource::Composite { name, arguments })
    }

    pub fn view_composite(name: String, arguments: Vec<ProgramValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::Program).collect();
        Self::View(Resource::Composite { name, arguments })
    }

    pub fn own_token(name: String, arguments: Vec<ProgramValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::Program).collect();
        Self::own(Resource::Token { name, arguments })
    }

    pub fn own(resource: Resource) -> Self {
        Self::Own(resource, Box::new(OldMachineTerm::constant(1).into()))
    }

    pub fn own_quantity(resource: Resource, quantity: OldMachineTerm) -> Self {
        Self::own_quantity_stored(resource, quantity.into())
    }

    pub(crate) fn own_quantity_stored(resource: Resource, quantity: StoredMachineTerm) -> Self {
        Self::Own(resource, Box::new(quantity))
    }

    pub(crate) fn has_proven_zero_quantity(&self, assumptions: &PureFactContext) -> bool {
        self.has_valid_exclusive_access()
            && self
                .owned_quantity_term()
                .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
    }

    pub(crate) fn has_proven_positive_quantity(&self, assumptions: &PureFactContext) -> bool {
        self.has_valid_exclusive_access()
            && self
                .owned_quantity_term()
                .is_some_and(|quantity| resource_quantity_is_positive(quantity, assumptions))
    }

    /// `allocation(base, bytes)` with a 32-bit byte count.
    pub fn own_allocation(base: Address, bytes: impl Into<OldMachineTerm>) -> Self {
        Self::own_heap_allocation(base, &AllocationSize::int32(bytes))
    }

    /// `allocation(base, bytes)` with the byte count in the size's format.
    pub(in crate::kernel) fn own_heap_allocation(base: Address, size: &AllocationSize) -> Self {
        Self::own_designated_allocation(Pointer::new(base, ProgramType::Int32Pointer), size)
    }

    pub(in crate::kernel) fn own_designated_allocation(
        base: Pointer,
        size: &AllocationSize,
    ) -> Self {
        Self::own(Resource::Token {
            name: Self::ALLOCATION_RESOURCE_NAME.to_string(),
            arguments: ResourceArguments::from_stored([
                StoredResourceField::Input(AlgebraicValue::Program(ProgramValue::Pointer(
                    base.with_type(ProgramType::Int32Pointer),
                ))),
                match size.bytes.value() {
                    crate::kernel::ExecutionValue::Native(value) => {
                        StoredResourceField::Input(AlgebraicValue::Program(value.clone()))
                    }
                    value => StoredResourceField::from_program(value.clone()),
                },
            ]),
        })
    }

    /// Allocation identity supplies bounds, independently of read authority.
    pub(in crate::kernel) fn allocation_bounds_fact(
        &self,
        assumptions: &PureFactContext,
    ) -> Option<Proposition> {
        if !self.has_proven_positive_quantity(assumptions) {
            return None;
        }
        // The coverage range has the token's size kind.
        let (base, bytes) = self.allocation_arguments()?;
        let range = match bytes {
            ProgramValue::Int32(bytes) => {
                MemoryRange::from_pointer_value(base, 0u32.into(), bytes.clone(), 1)
            }
            ProgramValue::UInt64(bytes) => MemoryRange::from_pointer_value_wide(
                base,
                OldMachineTerm::uint64_constant(0),
                bytes.clone(),
                1,
            ),
            _ => return None,
        };
        base.opaque_coverage_fact(&range)
    }

    /// The base and byte term of an owned `allocation` token of either
    /// size kind; [`Self::allocation_size`] also gives the kind.
    pub fn allocation(&self) -> Option<(&Address, &OldMachineTerm)> {
        self.allocation_value()
            .map(|(base, bytes)| (base.address(), bytes))
    }

    pub(in crate::kernel) fn allocation_value(&self) -> Option<(&Pointer, &OldMachineTerm)> {
        let (base, bytes) = self.allocation_arguments()?;
        let (ProgramValue::Int32(bytes) | ProgramValue::UInt64(bytes)) = bytes else {
            return None;
        };
        Some((base, bytes))
    }

    /// The base and tagged size of an owned `allocation` token.
    pub(in crate::kernel) fn allocation_size(&self) -> Option<(&Pointer, AllocationSize)> {
        let Self::Own(Resource::Token { name, arguments }, _) = self else {
            return None;
        };
        if name != Self::ALLOCATION_RESOURCE_NAME || arguments.len() != 2 {
            return None;
        }
        let ResourceFieldValue::Program(ProgramValue::Pointer(base)) = arguments.get(0)? else {
            return None;
        };
        Some((
            base,
            AllocationSize::from_value(arguments.program_value(1)?)?,
        ))
    }

    fn allocation_arguments(&self) -> Option<(&Pointer, &ProgramValue)> {
        let Self::Own(Resource::Token { name, arguments }, _) = self else {
            return None;
        };
        if name != Self::ALLOCATION_RESOURCE_NAME {
            return None;
        }
        let Some(
            [
                ResourceFieldValue::Program(ProgramValue::Pointer(base)),
                ResourceFieldValue::Program(bytes),
            ],
        ) = arguments.fixed_values::<2>()
        else {
            return None;
        };
        Some((base, bytes))
    }

    pub(in crate::kernel) fn may_refer_to_memory_block(&self, block: &AddressBase) -> bool {
        match self.resource() {
        Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => true,
            Resource::Memory(range) => &range.base().base == block,
            Resource::Composite { arguments, .. } => arguments.iter().any(
                |argument| matches!(argument, crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer)) if &pointer.base == block),
            ),
            Resource::Iterated(iterated) => iterated.blocks().contains(&block),
            Resource::Token { .. } | Resource::PopulationAuthority(_)
            | Resource::Instance(_) | Resource::ConditionalMutexGuard(_) | Resource::MutexGuard(_) | Resource::MutexLive(_) | Resource::MutexUse(_) | Resource::Publication(_) => false,
        }
    }

    pub(in crate::kernel) fn is_proven_separate_from_allocation(
        &self,
        base: &Address,
        bytes: &AllocationSize,
        assumptions: &PureFactContext,
    ) -> bool {
        self.is_proven_separate_from_allocation_with_element_width(base, bytes, 4, assumptions)
    }

    pub(in crate::kernel) fn is_proven_separate_from_allocation_with_element_width(
        &self,
        base: &Address,
        bytes: &AllocationSize,
        element_width: u32,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(element_count) = bytes.element_count(element_width) else {
            return false;
        };
        let allocation_memory =
            Resource::Memory(bytes.range(base.clone(), element_count, element_width));
        // Exact fact lookup, then the retained atomic separation checker.
        // The general prover added nothing here but its logical fallbacks
        // (context inconsistency, singleton substitution), which are proof
        // search rather than resource theory.
        let right = self.resource().clone();
        assumptions.proves_exact(&Proposition::ResourceSeparate {
            left: Box::new(allocation_memory.clone()),
            right: Box::new(right.clone()),
        }) || assumptions.proves_resource_separate(&allocation_memory, &right)
    }

    pub fn view_token(name: String, arguments: Vec<ProgramValue>) -> Self {
        let arguments = arguments.into_iter().map(AlgebraicValue::Program).collect();
        Self::View(Resource::Token { name, arguments })
    }

    pub fn resource(&self) -> &Resource {
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

    /// This fact's owner observation, per `owner_observation_core`: a viewed
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
        if matches!(
            self.resource(),
            Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
        ) {
            return None;
        }
        match self {
            Self::Own(resource, quantity)
                if resource_quantity_is_positive(quantity.old_form(), assumptions) =>
            {
                Some(Self::View(resource.clone()))
            }
            Self::Own(_, _) => None,
            Self::View(resource) => Some(Self::View(resource.clone())),
        }
    }

    pub fn memory_own_range(&self) -> Option<&MemoryRange> {
        match self {
            Self::Own(
                Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
                _,
            ) => None,
            Self::Own(Resource::Memory(range), _) => Some(range),
            Self::Own(
                Resource::Composite { .. }
                | Resource::Token { .. }
                | Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::Iterated(_),
                _,
            )
            | Self::View(_) => None,
        }
    }

    pub fn memory_view_range(&self) -> Option<&MemoryRange> {
        match self {
            Self::View(
                Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
            ) => None,
            Self::View(Resource::Memory(range)) => Some(range),
            Self::View(
                Resource::Composite { .. }
                | Resource::Token { .. }
                | Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::Iterated(_),
            )
            | Self::Own(..) => None,
        }
    }

    pub fn memory_range(&self) -> Option<&MemoryRange> {
        match self {
            Self::Own(
                Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
                _,
            )
            | Self::View(
                Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
            ) => None,
            Self::Own(Resource::Memory(range), _) | Self::View(Resource::Memory(range)) => {
                Some(range)
            }
            Self::Own(
                Resource::Composite { .. }
                | Resource::Token { .. }
                | Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::Iterated(_),
                _,
            )
            | Self::View(
                Resource::Composite { .. }
                | Resource::Token { .. }
                | Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::Iterated(_),
            ) => None,
        }
    }

    pub fn owned_resource(&self) -> Option<&Resource> {
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

    pub fn owned_quantity_term(&self) -> Option<&OldMachineTerm> {
        match self {
            Self::Own(_, quantity) => Some(quantity.old_form()),
            Self::View(_) => None,
        }
    }
}

/// SymbolicMemory-family normalization. The first two arms absorb an entailed fact
/// into the entailing one, which includes an owner swallowing a viewed
/// description of bytes it already covers.
///
/// That case is the owner-observation rule again: the view is a description
/// of ownership this context holds, and dropping a description changes no
/// live access share (the owner-observation rule and law 4 in docs/internals/stable-views.md). It is sound only because a
/// *bound* view never reaches here — `ResourceContext::normalized` skips any
/// entry with a live `borrow_dependency` and detaches supported projections
/// first. See [`combine_exact_resource_facts`] for the full argument; the
/// same guard covers both families.
fn combine_memory_resource_facts(
    left: &ResourceFact,
    right: &ResourceFact,
    assumptions: &PureFactContext,
) -> Option<ResourceFact> {
    // A field given back to the symbolic object holding it as a hole: the
    // two are disjoint, and joined they are the object again.
    match (left, right) {
        (ResourceFact::View(Resource::Memory(l)), ResourceFact::View(Resource::Memory(r))) => {
            if let Some(joined) = symbolic_object_with_field(l, r, assumptions)
                .or_else(|| symbolic_object_with_field(r, l, assumptions))
            {
                return Some(ResourceFact::view_memory(joined));
            }
        }
        (ResourceFact::Own(Resource::Memory(l), _), ResourceFact::Own(Resource::Memory(r), _)) => {
            if let Some(joined) = symbolic_object_with_field(l, r, assumptions)
                .or_else(|| symbolic_object_with_field(r, l, assumptions))
            {
                return Some(ResourceFact::own_memory(joined));
            }
        }
        _ => {}
    }
    if let (Some(left_range), Some(right_range)) = (
        memory_resource_fact_range(left),
        memory_resource_fact_range(right),
    ) && memory_ranges_structurally_disjoint(left_range, right_range)
    {
        return None;
    }
    // The normalization index selects adjacent endpoints. Join that pair
    // directly before trying either direction of containment, whose alias
    // reasoning can revisit the full history of a loaded base.
    match (left, right) {
        (
            ResourceFact::View(Resource::Memory(left)),
            ResourceFact::View(Resource::Memory(right)),
        ) => {
            if let Some(merged) = merge_memory_ranges(left, right, assumptions) {
                return Some(ResourceFact::view_memory(merged));
            }
        }
        (
            ResourceFact::Own(Resource::Memory(left), _),
            ResourceFact::Own(Resource::Memory(right), _),
        ) => {
            if let Some(merged) = merge_memory_ranges(left, right, assumptions) {
                return Some(ResourceFact::own_memory(merged));
            }
        }
        _ => {}
    }
    match (left, right) {
        _ if memory_resource_fact_entails(left, right, assumptions) => Some(left.clone()),
        _ if memory_resource_fact_entails(right, left, assumptions) => Some(right.clone()),
        (
            ResourceFact::View(Resource::Memory(left)),
            ResourceFact::View(Resource::Memory(right)),
        ) => merge_memory_ranges(left, right, assumptions).map(ResourceFact::view_memory),
        (
            ResourceFact::Own(Resource::Memory(left), _),
            ResourceFact::Own(Resource::Memory(right), _),
        ) => merge_memory_ranges(left, right, assumptions).map(ResourceFact::own_memory),
        _ => None,
    }
}

/// Joins two abutting ranges named through one provenance.
fn merge_memory_ranges(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> Option<MemoryRange> {
    // A field given back to the symbolic object it was taken from.
    if let Some(merged) = symbolic_object_with_field(left, right, assumptions)
        .or_else(|| symbolic_object_with_field(right, left, assumptions))
    {
        return Some(merged);
    }
    if left.has_holes() || right.has_holes() {
        return None;
    }
    if !assumptions.provenance_equal(&left.provenance, &right.provenance)
        || !match (left.carrier_owner(), right.carrier_owner()) {
            (None, None) => true,
            (Some(a), Some(b)) => assumptions.bounds_owners_equal(a, b),
            _ => false,
        }
    {
        return None;
    }
    merge_abutting_memory_ranges(left, right, assumptions)
}

fn merge_abutting_memory_ranges(
    left: &MemoryRange,
    right: &MemoryRange,
    assumptions: &PureFactContext,
) -> Option<MemoryRange> {
    if left.wide_bounds().is_some() || right.wide_bounds().is_some() {
        if left.element_width() != right.element_width() {
            return None;
        }
        // A piece at another spelling of the base, a window a call returned,
        // is restated at the left piece's base before the endpoints meet.
        let (base, (first, middle), (next, last)) = if left.base() == right.base() {
            (
                left.base(),
                shared_wide_range_bounds(left, assumptions)?,
                shared_wide_range_bounds(right, assumptions)?,
            )
        } else if let Some(right_bounds) =
            shared_rebased_wide_bounds(right, left.base(), assumptions)
        {
            (
                left.base(),
                shared_wide_range_bounds(left, assumptions)?,
                right_bounds,
            )
        } else {
            (
                right.base(),
                shared_rebased_wide_bounds(left, right.base(), assumptions)?,
                shared_wide_range_bounds(right, assumptions)?,
            )
        };
        let equal = |a: &SharedMachineIntegerTerm, b: &SharedMachineIntegerTerm| {
            a == b
                || assumptions.decide(&wide_index_comparison(
                    CompareRelation::Equal,
                    a.operand_view(),
                    b.operand_view(),
                )) == Some(true)
        };
        let output = |start, end| {
            MemoryRange::new_wide(
                base.clone(),
                wide_endpoint_output(start),
                wide_endpoint_output(end),
                left.element_width(),
            )
            .with_carrier_of(left)
        };
        if equal(&middle, &next) {
            return Some(output(first, last));
        }
        if equal(&last, &first) {
            return Some(output(next, middle));
        }
        return None;
    }
    if left.element_width() != right.element_width() {
        // Bytes that abut still abut under either spelling, so a bytewise
        // split's residue rejoins the owner it came from instead of leaving
        // the context permanently fragmented across two widths.
        if let Some(right) = memory_range_in_element_width(right, left.element_width()) {
            return merge_abutting_memory_ranges(left, &right, assumptions);
        }
        let left = memory_range_in_element_width(left, right.element_width())?;
        return merge_abutting_memory_ranges(&left, right, assumptions);
    }
    if left.base() != right.base() {
        // Pieces over two spellings of one block, such as the residue of
        // `owns x[0..4]` and the `owns (x + i)[0..1]` a call returns, meet
        // over whichever base the other can be restated on exactly.
        if let Some(right) = memory_range_rebased(right, left.base(), assumptions) {
            return merge_abutting_memory_ranges(left, &right, assumptions);
        }
        let left = memory_range_rebased(left, right.base(), assumptions)?;
        return merge_abutting_memory_ranges(&left, right, assumptions);
    }
    if left.end() == right.start()
        || bitvector_terms_proven_equal(left.end(), right.start(), assumptions)
    {
        return Some(
            MemoryRange::new_with_element_width(
                left.base().clone(),
                left.start().clone(),
                right.end().clone(),
                left.element_width(),
            )
            .with_carrier_of(left),
        );
    }
    if right.end() == left.start()
        || bitvector_terms_proven_equal(right.end(), left.start(), assumptions)
    {
        return Some(
            MemoryRange::new_with_element_width(
                left.base().clone(),
                right.start().clone(),
                left.end().clone(),
                left.element_width(),
            )
            .with_carrier_of(left),
        );
    }
    None
}

/// `range` restated over `base`, naming exactly the same elements.
///
/// Only a range with constant bounds is restated, and only onto a base it
/// sits an exact number of elements from
/// ([`crate::kernel::reasoning::ExactElementDelta`]). A range's
/// first element is the signed value of its start and its length the
/// wrapping difference of its bounds, so the restated start must be exact: a
/// constant that fits `int32`, or the delta's symbolic index itself with no
/// constant beside it, since `i + k` is `sext(i) + k` only while it does not
/// wrap. The restated end is the start plus the same length, which the
/// wrapping difference preserves.
fn memory_range_rebased(
    range: &MemoryRange,
    base: &Address,
    assumptions: &PureFactContext,
) -> Option<MemoryRange> {
    let (start, count) = constant_range_span(range)?;
    let delta = range.base().exact_element_delta_from_base(
        base,
        range.element_width(),
        Some(assumptions),
    )?;
    let offset = delta.constant.checked_add(start)?;
    let start = if delta.is_constant() {
        OldMachineTerm::constant(i32::try_from(offset).ok()? as u32)
    } else if offset == 0 {
        delta.index.structural_value().clone()
    } else {
        return None;
    };
    let end = OldMachineTerm::add(
        start.clone(),
        OldMachineTerm::constant(i32::try_from(count).ok()? as u32),
    );
    Some(
        MemoryRange::new_with_element_width(base.clone(), start, end, range.element_width())
            .with_carrier_of(range),
    )
}

fn bitvector_terms_proven_equal(
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || assumptions.decide(&OldConditionTerm::equal(left.clone(), right.clone())) == Some(true)
}

#[cfg(test)]
mod support_removal_tests {
    use super::*;

    #[test]
    fn frame_exchange_refuses_duplicate_authority_and_unrelated_histories() {
        let assumptions = PureFactContext::new();
        let authority = ResourceFact::own_memory(MemoryRange::new(
            Address::new("frame".into(), AddressOffset::constant(0)),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(4),
        ));
        let body = ResourceContext::new();
        let frame = body.clone().unchecked_with_fact(authority.clone());
        let exit = body.clone().unchecked_with_fact(authority.clone());
        assert!(
            exit.restore_frame_after_exchange(&body, &frame, &assumptions)
                .is_none()
        );
        let unrelated = ResourceContext::new().unchecked_with_fact(authority);
        assert!(
            unrelated
                .restore_frame_after_exchange(&body, &frame, &assumptions)
                .is_none()
        );
    }

    #[test]
    fn frame_exchange_uses_selected_unfold_custody_but_refuses_unclassified_additions() {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let range = |id| {
            ResourceFact::own_memory(MemoryRange::new(
                Address::symbolic(Variable(id)),
                0u32.into(),
                4u32.into(),
            ))
        };
        let instance = ResourceInstance::new(
            InstanceId::from_variable(Variable(8_779_101)),
            "body".into(),
            vec![].into(),
            ResourceFieldSchema::new(vec![(
                "tag".into(),
                ResourceFieldType::Program(ProgramType::Int32),
            )])
            .unwrap(),
            vec![ProgramValue::Int32(OldMachineTerm::constant(7)).into()].into(),
        )
        .unwrap();
        let parent = ResourceFact::own(Resource::Instance(instance.clone()));
        let child = range(8_779_102);
        let held = range(8_779_103);
        let body = ResourceContext::new().unchecked_with_fact(parent.clone());
        let frame = body.clone().unchecked_with_fact(held.clone());
        let exit = body
            .clone()
            .unfold_instance_body(&instance, [child.clone()], &facts)
            .unwrap()
            .unwrap();
        let occurrence = exit.unique_owned_occurrence_for_fact(&child).unwrap().0;
        let restored = exit
            .restore_frame_after_exchange(&body, &frame, &facts)
            .unwrap();
        assert_eq!(restored.owned_fact_for_occurrence(occurrence), Some(&child));
        assert!(restored.contains_exact_representation(&held));
        let unclassified = body
            .clone()
            .without_exact_representation(&parent)
            .unwrap()
            .unchecked_with_fact(child.clone());
        assert!(
            unclassified
                .restore_frame_after_exchange(&body, &frame, &facts)
                .is_none()
        );
        let replaced = exit
            .without_exact_representation(&child)
            .unwrap()
            .unchecked_with_fact(child);
        assert!(
            replaced
                .restore_frame_after_exchange(&body, &frame, &facts)
                .is_none(),
            "a removed child's custody must not authorize a later description"
        );
    }

    #[test]
    fn frame_exchange_does_not_turn_derived_projections_into_authority() {
        let assumptions = PureFactContext::new();
        let owner = ResourceFact::own_composite("owner".into(), Vec::new());
        let projection = ResourceFact::view_token("projection".into(), Vec::new());
        let body = ResourceContext::new().unchecked_with_fact(owner.clone());
        let exit = body
            .clone()
            .unchecked_with_supported_facts(&owner, vec![projection.clone()]);
        let restored = exit
            .restore_frame_after_exchange(&body, &body, &assumptions)
            .unwrap();
        assert!(restored.contains_exact_representation(&owner));
        assert!(!restored.contains_exact_representation(&projection));
    }

    #[test]
    fn selected_range_join_uses_graph_endpoint_decision_without_fact_path_fallback() {
        let (a, b) = (Variable(90_010), Variable(90_011));
        let endpoint = |variable| {
            OldMachineTerm::add(
                OldMachineTerm::Variable(variable),
                OldMachineTerm::constant(1),
            )
        };
        let base = Address::symbolic(Variable(90_012));
        let left = MemoryRange::new(base.clone(), OldMachineTerm::constant(0), endpoint(a));
        let right = MemoryRange::new(base.clone(), endpoint(b), OldMachineTerm::constant(16));
        let premise =
            OldConditionTerm::equal(OldMachineTerm::Variable(a), OldMachineTerm::Variable(b));
        let parent = PureFactContext::new();
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert_eq!(
            merge_memory_ranges(&left, &right, &branch),
            Some(MemoryRange::new(
                base,
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(16),
            )),
        );
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(merge_memory_ranges(&left, &right, &parent).is_none());
    }

    #[test]
    fn concrete_interval_rejects_exclusive_end_outside_shared_coordinate_space() {
        let range = MemoryRange::new(
            Address::new("boundary".into(), AddressOffset::constant(1)),
            OldMachineTerm::constant((i32::MAX - 1) as u32),
            OldMachineTerm::constant(i32::MAX as u32),
        );
        assert_eq!(concrete_memory_range_bounds(&range), None);
    }

    #[test]
    fn memory_load_footprints_use_checked_state_widths() {
        let short_pointer = Address::new("typed-loads".into(), AddressOffset::constant(0));
        let wide_pointer = Address::new("typed-loads".into(), AddressOffset::constant(8));
        let memory = SymbolicMemory::new()
            .with_block("typed-loads", 24)
            .store(short_pointer.clone(), int16(0))
            .store(
                wide_pointer.clone(),
                ProgramValue::Float64(OldMachineTerm::uint64_constant(0)),
            );
        let short_load = OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
            Box::new(short_pointer.clone()),
            crate::kernel::LoadKind::Int16,
        );
        let wide_load = OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
            Box::new(wide_pointer.clone()),
            crate::kernel::LoadKind::Float64,
        );
        let fact = ResourceFact::view_memory(MemoryRange::new(
            Address::new("result".into(), AddressOffset::constant(0)),
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
    fn memory_load_footprints_reject_mixed_source_states() {
        let pointer = Address::new("mixed-loads".into(), AddressOffset::constant(0));
        let first = SymbolicMemory::new()
            .with_block("mixed-loads", 8)
            .store(pointer.clone(), int16(0));
        let second = first.clone().store(pointer.clone(), int16(1));
        let first_load = OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&first))),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let second_load = OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&second))),
            Box::new(pointer),
            crate::kernel::LoadKind::Int32,
        );
        let fact = ResourceFact::view_memory(MemoryRange::new(
            Address::new("mixed-result".into(), AddressOffset::constant(0)),
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
        let pointer = Address::new("deep-load".into(), AddressOffset::constant(0));
        let memory = SymbolicMemory::new()
            .with_block("deep-load", 8)
            .store(pointer.clone(), int16(0));
        let load = OldMachineTerm::read_named(
            ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
            Box::new(pointer),
            crate::kernel::LoadKind::Int32,
        );
        let mut nested = load;
        for _ in 0..(MAX_MEMORY_LOAD_FOOTPRINT_DEPTH + 8) {
            nested = binary_node!(
                Int32,
                Add,
                Box::new(nested),
                Box::new(OldMachineTerm::constant(0))
            );
        }
        let fact = ResourceFact::view_memory(MemoryRange::new(
            Address::new("deep-result".into(), AddressOffset::constant(0)),
            OldMachineTerm::constant(0),
            nested,
        ));
        assert_eq!(
            memory_footprint_for_fact(&fact),
            ResourceMemoryFootprint::Unknown
        );
    }

    #[test]
    fn removing_support_cascades_through_nested_projection_chain() {
        let parent = ResourceFact::own_composite("parent".into(), Vec::new());
        let child = ResourceFact::view_token("child".into(), Vec::new());
        let grandchild = ResourceFact::view_token("grandchild".into(), Vec::new());
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
        let left = ResourceFact::view_token("left".into(), Vec::new());
        let right = ResourceFact::view_token("right".into(), Vec::new());
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

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/primitives/resource_algebra/support_removal_tests.rs");
    }
}

#[cfg(test)]
#[test]
fn symbolic_struct_coverage_uses_exact_element_indices() {
    let base = Address::symbolic(Variable(99_300));
    let i = OldMachineTerm::Variable(Variable(99_301));
    let n = OldMachineTerm::Variable(Variable(99_302));
    let owned = MemoryRange::new_with_element_width(base.clone(), 0u32.into(), n.clone(), 16);
    let required = |pointer: Address, bytes| {
        MemoryRange::new_with_element_width(pointer, 0u32.into(), bytes, 1)
    };
    let lower = PureFactContext::new().assume_condition(
        OldConditionTerm::signed_less_equal(0u32.into(), i.clone()),
        true,
    );
    let inside = lower.clone().assume_condition(
        OldConditionTerm::signed_less_than(i.clone(), n.clone()),
        true,
    );
    let at_i = base.offset_by_elements(i.clone(), 16);
    assert!(memory_range_covers(
        &owned,
        &required(at_i.offset_by_bytes(8), 8u32.into()),
        &inside
    ));
    assert!(memory_range_covers(
        &owned,
        &required(at_i.clone(), 4u32.into()),
        &inside
    ));
    assert!(!memory_range_covers(
        &owned,
        &required(at_i.offset_by_bytes(12), 8u32.into()),
        &inside
    ));
    let inclusive = lower.assume_condition(
        OldConditionTerm::signed_less_equal(i.clone(), n.clone()),
        true,
    );
    assert!(!memory_range_covers(
        &owned,
        &required(at_i.offset_by_bytes(8), 8u32.into()),
        &inclusive
    ));
    let upper_only = PureFactContext::new()
        .assume_condition(OldConditionTerm::signed_less_than(i, n.clone()), true);
    assert!(!memory_range_covers(
        &owned,
        &required(at_i.offset_by_bytes(8), 8u32.into()),
        &upper_only
    ));
    let first = PureFactContext::new()
        .assume_condition(OldConditionTerm::signed_less_equal(1u32.into(), n), true);
    assert!(memory_range_covers(
        &owned,
        &required(base.offset_by_bytes(8), 8u32.into()),
        &first
    ));
    let negative = base.offset_by_elements(OldMachineTerm::constant(u32::MAX), 16);
    assert!(!memory_range_covers(
        &owned,
        &required(negative.offset_by_bytes(8), 8u32.into()),
        &first
    ));
    // A displacement of 2^32 elements must never wrap back into element zero.
    let distant = base.with_offset(AddressOffset::add(
        base.offset.clone(),
        AddressOffset::constant((1i64 << 32) * 16 + 8),
    ));
    assert!(!memory_range_covers(
        &owned,
        &required(distant, 8u32.into()),
        &first
    ));
}

#[cfg(test)]
#[test]
fn exact_principal_input_view_ignores_covering_views() {
    let _session = crate::kernel::VerificationSession::enter();
    let assumptions = PureFactContext::new();
    let pointer = Address::new("local:input-view".into(), AddressOffset::constant(0));
    let required =
        ResourceFact::view_memory(MemoryRange::new(pointer.clone(), 0u32.into(), 1u32.into()));
    for count in [0u32, 16, 64, 256] {
        let mut facts = ResourceContext::new().unchecked_with_fact(required.clone());
        let exact = facts.indexed_view_witness(&required, &assumptions).unwrap();
        for end in 2..count + 2 {
            facts = facts.unchecked_with_fact(ResourceFact::view_memory(MemoryRange::new(
                pointer.clone(),
                0u32.into(),
                end.into(),
            )));
        }
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.principal_input_view_occurrence(&required, &assumptions)
        });
        assert_eq!(selected, Some(exact));
        assert_eq!(work, 1, "covering views: {count}");
    }
}

#[cfg(test)]
#[test]
fn absent_view_queries_ignore_owned_frames_and_track_view_lifecycle() {
    let _session = crate::kernel::VerificationSession::enter();
    let assumptions = PureFactContext::new();
    let pointer = Address::new("local:selected-view".into(), AddressOffset::constant(0));
    let required = ResourceFact::view_memory(MemoryRange::new(pointer, 0u32.into(), 1u32.into()));
    for size in [0, 16, 64, 256] {
        let mut owned = ResourceContext::new();
        for index in 0..size {
            owned = owned.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                Address::new(
                    format!("local:unrelated-view-owner-{index}").into(),
                    AddressOffset::constant(0),
                ),
                0u32.into(),
                1u32.into(),
            )));
        }
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            owned.view_occurrences_for_fact(&required, &assumptions)
        });
        assert!(found.is_empty());
        assert_eq!(
            work, 0,
            "ownership-only input must not resolve memory: size={size}"
        );
        let view_entry = owned.storage.next_entry_id;
        let mut with_view = owned.clone().unchecked_with_fact(required.clone());
        let occurrence = with_view.occurrence(view_entry);
        assert_eq!(
            with_view.view_occurrences_for_fact(&required, &assumptions),
            vec![occurrence],
        );
        assert!(
            owned
                .view_occurrences_for_fact(&required, &assumptions)
                .is_empty()
        );
        assert_eq!(with_view.remove_entry(view_entry), required);
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_view.view_occurrences_for_fact(&required, &assumptions)
        });
        assert!(found.is_empty());
        assert_eq!(
            work, 0,
            "removing the last view restores empty lookup: size={size}"
        );
    }
}

#[cfg(test)]
mod related_pointer_root_tests {
    use super::*;

    fn external(index: u64) -> Address {
        Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::scaled_int32_node(
                OldMachineTerm::Variable(Variable(986_400 + index)),
                4,
            ),
        )
    }

    /// `count` pointers each stated equal to one base, as `requires q == b`
    /// states them.
    fn aliases_of_base(count: u64) -> (Address, PureFactContext) {
        let base = external(0);
        let assumptions = (1..=count).fold(PureFactContext::new(), |assumptions, index| {
            assumptions.assume_condition(
                OldConditionTerm::address_equal(external(index), base.clone()),
                true,
            )
        });
        (base, assumptions)
    }

    /// The roots as each alias computes them on its own, the reference the
    /// shared walk must reproduce.
    fn roots_alias_by_alias(
        pointer: &Address,
        assumptions: &PureFactContext,
    ) -> BTreeSet<MemoryBaseRoot> {
        let mut roots = related_memory_base_roots(pointer, assumptions);
        for alias in assumptions.exact_pointer_aliases(pointer) {
            roots.extend(related_memory_base_roots(alias, assumptions));
        }
        for alias in assumptions.exact_pointer_offset_aliases(pointer) {
            roots.extend(related_memory_base_roots(&alias, assumptions));
        }
        roots
    }

    #[test]
    fn aliases_in_one_class_relate_the_same_roots_as_alias_by_alias() {
        let _session = crate::kernel::VerificationSession::enter();
        for count in [1, 3, 17] {
            let (base, assumptions) = aliases_of_base(count);
            let roots = related_pointer_roots(&base, &assumptions);
            assert_eq!(roots, roots_alias_by_alias(&base, &assumptions));
            assert_eq!(roots.len(), count as usize + 1);
            // Asking from an alias reaches the same class.
            let alias = external(count);
            assert_eq!(
                related_pointer_roots(&alias, &assumptions),
                roots_alias_by_alias(&alias, &assumptions)
            );
        }
    }

    /// One pointer with N recorded aliases, all in one equality class, used
    /// to cost N walks of that N-member class.
    #[test]
    fn related_roots_of_aliased_pointers_walk_their_class_once() {
        let _session = crate::kernel::VerificationSession::enter();
        let work_at = |count: u64| {
            let (base, assumptions) = aliases_of_base(count);
            let (roots, work) = crate::instrumentation::measure_deterministic_work(|| {
                related_pointer_roots(&base, &assumptions)
            });
            assert_eq!(roots.len(), count as usize + 1);
            work
        };
        let small = work_at(16);
        let large = work_at(128);
        assert!(
            large <= 10 * small,
            "related roots of 128 aliases cost {large} work units against {small} for 16"
        );
    }
}

#[cfg(test)]
thread_local! {
    /// Facts visited by whole-context normalization, for the scaling
    /// regression that keeps a plain `unfold` from renormalizing every
    /// held resource.
    static WHOLE_NORMALIZATION_FACTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn take_whole_normalization_facts() -> usize {
    WHOLE_NORMALIZATION_FACTS.with(|count| count.replace(0))
}

#[cfg(test)]
mod read_definition_index_tests;

mod legacy_search;

#[cfg(test)]
mod shared_wide_bound_tests {
    use super::*;
    use crate::kernel::{KernelTermExport, KernelType, VerificationSession};

    #[test]
    fn mixed_endpoint_coverage_needs_the_complete_bound_without_export() {
        let _session = VerificationSession::enter();
        let base = Address::new("shared_wide_bound".into(), AddressOffset::constant(0));
        let length = OldMachineTerm::Variable(Variable(1018501));
        let low = OldMachineTerm::uint32_from_64(length.clone());
        let narrow = MemoryRange::new_with_element_width(
            base.clone(),
            OldMachineTerm::constant(0),
            OldMachineTerm::add(low.clone(), OldMachineTerm::constant(1)),
            1,
        );
        let wide = MemoryRange::new_wide(
            base.clone(),
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_add(length.clone(), OldMachineTerm::uint64_constant(1)),
            1,
        );
        let empty = PureFactContext::new();
        let complete = empty.clone().assume_condition(
            OldConditionTerm::uint64_less_equal(
                length.clone(),
                OldMachineTerm::uint64_constant(i32::MAX as u64 - 1),
            ),
            true,
        );
        let truncated = empty.clone().assume_condition(
            OldConditionTerm::unsigned_less_equal(
                low,
                OldMachineTerm::constant(i32::MAX as u32 - 1),
            ),
            true,
        );
        let exports = KernelTermExport::machine_export_count();
        assert!(wide_memory_range_covers(&narrow, &wide, &complete));
        assert!(wide_memory_range_covers(&wide, &narrow, &complete));
        assert!(!wide_memory_range_covers(&narrow, &wide, &empty));
        assert!(!wide_memory_range_covers(&narrow, &wide, &truncated));
        assert_eq!(KernelTermExport::machine_export_count(), exports);

        let pointer = base.with_offset(AddressOffset::scale_int64(length, 1, true));
        let exports = KernelTermExport::machine_export_count();
        assert!(pointer_formation_in_range(
            &pointer, &base, &wide, &complete
        ));
        assert!(!pointer_formation_in_range(&pointer, &base, &wide, &empty));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn wide_split_and_merge_keep_full_width_output_endpoints() {
        let _session = VerificationSession::enter();
        let base = Address::new("wide_bound_outputs".into(), AddressOffset::constant(0));
        let big = 1u64 << 40;
        let range = |start, end| {
            MemoryRange::new_wide(
                base.clone(),
                OldMachineTerm::uint64_constant(start),
                OldMachineTerm::uint64_constant(end),
                1,
            )
        };
        let facts = PureFactContext::new();
        let whole = range(0, big + 3);
        let taken = range(big, big + 1);
        let residues = split_memory_range(&whole, &taken, &facts).unwrap();
        assert_eq!(residues, vec![range(0, big), range(big + 1, big + 3)]);
        let prefix = merge_abutting_memory_ranges(&residues[0], &taken, &facts).unwrap();
        assert_eq!(
            merge_abutting_memory_ranges(&prefix, &residues[1], &facts),
            Some(whole)
        );
        assert!(merge_abutting_memory_ranges(&residues[0], &residues[1], &facts).is_none());
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/primitives/resource_algebra/shared_wide_bounds.rs");
        include!(
            "../../scaling_tests/kernel/primitives/resource_algebra/coverage_separation_tests.rs"
        );
    }
}

#[cfg(test)]
mod constructed_normalization_tests {
    use super::*;

    #[test]
    fn written_normalization_keeps_both_facts_when_a_merge_needs_an_alias() {
        let pointer = Address::symbolic(Variable(8_853_001));
        let alias = Address::symbolic(Variable(8_853_002));
        let facts = PureFactContext::new().assume_condition(
            OldConditionTerm::address_equal(pointer.clone(), alias.clone()),
            true,
        );
        let pieces = [
            ResourceFact::View(Resource::Memory(MemoryRange::new(
                pointer,
                0u32.into(),
                1u32.into(),
            ))),
            ResourceFact::View(Resource::Memory(MemoryRange::new(
                alias,
                1u32.into(),
                2u32.into(),
            ))),
        ];
        let normalized = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_facts(pieces.clone())
            .normalized_without_discovery(&facts);
        assert_eq!(normalized.facts().len(), 2);
        for piece in pieces {
            assert!(normalized.contains_exact_representation(&piece));
        }
    }

    mod scaling_tests {
        use super::*;
        include!(
            "../../scaling_tests/kernel/primitives/resource_algebra/constructed_normalization.rs"
        );
    }
}
