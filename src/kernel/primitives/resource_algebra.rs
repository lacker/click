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

fn memory_interval_nodes(range: &CMemoryRange) -> Option<Vec<ResourceMemoryIntervalNode>> {
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

fn memory_interval_ancestors(node: &ResourceMemoryIntervalNode) -> Vec<ResourceMemoryIntervalNode> {
    (node.level..=32)
        .map(|level| ResourceMemoryIntervalNode {
            block: node.block.clone(),
            level,
            start: (u64::from(node.start) >> level << level) as u32,
        })
        .collect()
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
            if mode {
                result.owned_memory_by_block = insert_resource_index_entry(
                    &result.owned_memory_by_block,
                    block.clone(),
                    entry,
                );
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
            if let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const()) {
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
            if mode {
                result.owned_memory_by_block =
                    remove_resource_index_entry(&result.owned_memory_by_block, &block, entry);
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
            if let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const()) {
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

fn memory_derivation_affects_footprint(
    derivation: &CMemoryDerivation,
    footprint: &ResourceMemoryFootprint,
) -> bool {
    let ResourceMemoryFootprint::Exact(ranges) = footprint else {
        return matches!(footprint, ResourceMemoryFootprint::Unknown)
            && !matches!(
                derivation,
                CMemoryDerivation::BlockDeclared { .. }
                    | CMemoryDerivation::HeapAllocated { .. }
                    | CMemoryDerivation::HeapAllocationPending { .. }
                    | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
                    | CMemoryDerivation::CellsForgotten { .. }
            );
    };
    match derivation {
        CMemoryDerivation::Store { pointer, value, .. } => ranges
            .iter()
            .any(|range| memory_range_overlaps_pointer(range, pointer, value.byte_width())),
        CMemoryDerivation::CallHavoc { mutable_ranges, .. }
        | CMemoryDerivation::LoopHavoc {
            mutable_ranges: Some(mutable_ranges),
            ..
        } => ranges.iter().any(|footprint| {
            mutable_ranges
                .iter()
                .any(|written| memory_ranges_overlap(footprint, written))
        }),
        CMemoryDerivation::HeapFreed {
            allocation_base,
            bytes,
            ..
        } => ranges.iter().any(|range| {
            memory_range_overlaps_pointer(
                range,
                allocation_base,
                bytes.as_const().unwrap_or(u32::MAX),
            )
        }),
        CMemoryDerivation::LocalLifetimeEnded { block, .. } => {
            ranges.iter().any(|range| range.base().block == *block)
        }
        CMemoryDerivation::LoopHavoc {
            mutable_ranges: None,
            ..
        } => true,
        CMemoryDerivation::BlockDeclared { .. }
        | CMemoryDerivation::HeapAllocated { .. }
        | CMemoryDerivation::HeapAllocationPending { .. }
        | CMemoryDerivation::ContractAllocationClaimsChanged { .. }
        | CMemoryDerivation::CellsForgotten { .. } => false,
    }
}

fn memory_range_overlaps_pointer(range: &CMemoryRange, pointer: &Pointer, bytes: u32) -> bool {
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
    let Some(pointer_end) = pointer_offset.checked_add(i64::from(bytes)) else {
        return true;
    };
    pointer_offset < end && pointer_end > start
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
        for ancestor in memory_interval_ancestors(&query) {
            if let Some(bucket) = index.get(&ancestor) {
                for occurrence in bucket.iter() {
                    *occurrences = occurrences.with_value(*occurrence);
                }
            }
        }
        if let Some(bucket) = subtree.get(&query) {
            for occurrence in bucket.iter() {
                *occurrences = occurrences.with_value(*occurrence);
            }
        }
    }
}

fn memory_ranges_overlap(left: &CMemoryRange, right: &CMemoryRange) -> bool {
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

fn concrete_memory_range_bounds(range: &CMemoryRange) -> Option<(i64, i64)> {
    let base = range.base().offset.as_const()?;
    let start = signed_bitvector_constant(range.start())?;
    let end = signed_bitvector_constant(range.end())?;
    let width = i64::from(range.element_width());
    Some((
        base.checked_add(start.checked_mul(width)?)?,
        base.checked_add(end.checked_mul(width)?)?,
    ))
}

fn memory_footprint_for_fact(fact: &CResourceFact) -> ResourceMemoryFootprint {
    if let Some(range) = fact.memory_range() {
        return ResourceMemoryFootprint::Exact(std::sync::Arc::from(vec![range.clone()]));
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

    fn changed_facts_since(&self, ancestor: &Self) -> Option<BTreeSet<CResourceFact>> {
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
                (usize, Option<ResourceSupportMetadata>),
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
                        .or_insert((0, metadata.clone()));
                    if slot.1 != metadata {
                        // Equal projections with different dependency
                        // topology cannot be safely joined under one record.
                        slot.1 = None;
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
                .filter_map(|(support, (left_count, left_metadata))| {
                    right_supported
                        .get(&support)
                        .filter(|(_, right_metadata)| {
                            left_metadata.as_ref().map(|metadata| &metadata.footprint)
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
                        memory_interval_nodes(range).is_none() || range.base().has_symbolic_block()
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
        let projections = self
            .storage
            .projections_by_support_occurrence
            .get(&self.occurrence(entry))
            .cloned()
            .unwrap_or_default();
        for projection in projections.iter().copied() {
            crate::instrumentation::record_deterministic_work(1);
            self.remove_entry_only(projection);
        }
        self.remove_entry_only(entry)
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
                    if ranges
                        .iter()
                        .any(|range| memory_interval_nodes(range).is_none()) =>
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

    fn memory_block_facts(&self, block: &PointerBlock) -> impl Iterator<Item = &CResourceFact> {
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

    /// Finds the owned authority that directly supports a requirement. A
    /// supported projection records an owned fact (never another projection)
    /// as its support, so this is deliberately one indexed hop rather than a
    /// recursive search through caller-controlled metadata.
    pub(crate) fn directly_supporting_owned_entry(
        &self,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<(ResourceOccurrenceId, &CResourceFact)> {
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
                if memory_derivation_affects_footprint(&derivation, &metadata.footprint)
                    && let Some(entry) = self.storage.entry_by_occurrence.get(occurrence)
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
            CMemoryDerivation::Store { pointer, .. } => pointer.has_symbolic_block(),
            CMemoryDerivation::CallHavoc { mutable_ranges, .. }
            | CMemoryDerivation::LoopHavoc {
                mutable_ranges: Some(mutable_ranges),
                ..
            } => mutable_ranges
                .iter()
                .any(|range| range.base().has_symbolic_block()),
            CMemoryDerivation::HeapFreed {
                allocation_base, ..
            }
            | CMemoryDerivation::HeapAllocationPending {
                allocation_base, ..
            } => allocation_base.has_symbolic_block(),
            CMemoryDerivation::LocalLifetimeEnded { .. }
            | CMemoryDerivation::LoopHavoc {
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
                    entries = entries.with_value(*occurrence);
                }
            }
            CMemoryDerivation::LocalLifetimeEnded { block, .. } => {
                if let Some(bucket) = self.storage.projections_by_memory_block.get(block) {
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

    /// Non-recursive projection for memory-resolution fast paths. It uses
    /// only block indexing and structural containment, so it cannot re-enter
    /// snapshot or alias reasoning.
    pub(in crate::kernel) fn proves_owned_memory_ranges_separate_shallow(
        &self,
        left: &CMemoryRange,
        right: &CMemoryRange,
    ) -> bool {
        if left.base().block != right.base().block {
            return false;
        }
        let Some(positions) = self.storage.index.memory_by_block.get(&left.base().block) else {
            return false;
        };
        let left_position = positions.iter().copied().find(|entry| {
            self.fact(*entry)
                .memory_own_range()
                .is_some_and(|available| {
                    crate::kernel::assumptions::memory_range_shallowly_contained(left, available)
                })
        });
        let Some(left_position) = left_position else {
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
    pub(in crate::kernel) fn same_block_separation_candidates(
        &self,
    ) -> Vec<(Proposition, CMemoryRange, CMemoryRange)> {
        let mut by_block = BTreeMap::<PointerBlock, Vec<&CMemoryRange>>::new();
        for fact in self.iter() {
            let Some(range) = fact.memory_own_range() else {
                continue;
            };
            crate::instrumentation::record_deterministic_work(1);
            by_block
                .entry(range.base().block.clone())
                .or_default()
                .push(range);
        }
        let mut entries = Vec::new();
        for owned in by_block.values() {
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
        mut self,
        support_occurrence: ResourceOccurrenceId,
        support: &CResourceFact,
        facts: impl IntoIterator<Item = CResourceFact>,
        memory: &CMemory,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert!(
            self.storage
                .entry_by_occurrence
                .get(&support_occurrence)
                .is_some_and(|entry| self.fact(*entry) == support)
        );
        let memory_snapshot = CMemorySnapshotIdentity::of(memory);
        let facts = facts.into_iter().collect::<Vec<_>>();
        for fact in facts {
            debug_assert!(fact.is_view());
            let metadata = ResourceSupportMetadata {
                memory_snapshot,
                footprint: memory_footprint_for_fact(&fact),
            };
            self.insert_fact_with_support_occurrence_and_metadata(
                fact,
                Some(support.clone()),
                Some(support_occurrence),
                Some(metadata),
            );
        }
        self
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
        let occurrence =
            occurrence.filter(|occurrence| context.owned_occurrence_matches(*occurrence, &fact));
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
            let same_base_concrete = right_range
                .start()
                .as_const()
                .zip(right_range.end().as_const())
                .and_then(|(start, end)| {
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
        let facts = facts.into_iter().collect::<Vec<_>>();
        for fact in &facts {
            self.clone()
                .try_compose_into_valid_context_delaying_normalization(
                    std::iter::once(fact.clone()),
                    assumptions,
                )?;
        }
        Ok(self.unchecked_with_facts(facts))
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
            let one_concrete_base = owned.first().map(|(_, range)| range.base()).filter(|base| {
                owned.iter().all(|(_, range)| {
                    range.base() == *base
                        && range.start().as_const().is_some()
                        && range.end().as_const().is_some()
                })
            });
            if one_concrete_base.is_some() {
                let mut ordered = owned;
                ordered.sort_by_key(|(_, range)| {
                    (
                        range.start().as_const().unwrap(),
                        range.end().as_const().unwrap(),
                    )
                });
                let mut furthest: Option<(&CResourceFact, &CMemoryRange)> = None;
                for (fact, range) in ordered {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some((left, left_range)) = furthest {
                        if let Some(error) = resource_family_algebra(left.family())
                            .pair_validity_error(left, fact, assumptions)
                        {
                            return Some(error);
                        }
                        if range.end().as_const().unwrap() > left_range.end().as_const().unwrap() {
                            furthest = Some((fact, range));
                        }
                    } else {
                        furthest = Some((fact, range));
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
                    memory_range_structurally_covers(&available, required) == Some(true)
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
        let resolved = crate::kernel::reasoning::resolve_minted_load_pointer(pointer, assumptions);
        let resolved =
            crate::kernel::reasoning::resolve_symbolic_pointer_alias(&resolved, assumptions);
        let pointer = &resolved;
        if self.permits_memory_read_structurally(pointer, byte_width, assumptions) {
            return true;
        }
        self.memory_block_facts(&pointer.block).any(|resource| {
            memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
        })
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
        // matches owned ranges still written through loads.
        let resolved = crate::kernel::reasoning::resolve_minted_load_pointer(pointer, assumptions);
        let pointer = &resolved;
        for resource in self.memory_block_facts(&pointer.block) {
            let CResourceFact::Own(CResource::Memory(range), _) = resource else {
                continue;
            };
            if pointer_has_structural_range_base(pointer, range.base())
                && memory_resource_fact_permits_write(resource, pointer, byte_width, assumptions)
            {
                return Some(range);
            }
        }
        self.iter().find_map(|resource| {
            memory_resource_fact_permits_write(resource, pointer, byte_width, assumptions)
                .then(|| resource.memory_own_range())
                .flatten()
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
        let mut i = 0;
        while i < slots.len() {
            let Some((_, fact)) = slots[i].clone() else {
                i += 1;
                continue;
            };
            let mut changed = false;
            for j in index.candidates_after(i, &fact) {
                crate::instrumentation::record_deterministic_work(1);
                let Some((_, right)) = slots[j].as_ref() else {
                    continue;
                };
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
    MemoryStart(PointerBlock, bool, Bitvector32Term),
    MemoryEnd(PointerBlock, bool, Bitvector32Term),
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
                    range.start().clone(),
                ));
                keys.push(ResourceNormalizationKey::MemoryEnd(
                    range.base().block.clone(),
                    fact.is_own(),
                    range.end().clone(),
                ));
            }
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                keys.push(ResourceNormalizationKey::ExactShape(
                    fact.family(),
                    name.clone(),
                    arguments.len(),
                ));
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
                    range.start().clone(),
                ));
                keys.push(ResourceNormalizationKey::MemoryStart(
                    range.base().block.clone(),
                    fact.is_own(),
                    range.end().clone(),
                ));
            }
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                keys.push(ResourceNormalizationKey::ExactShape(
                    fact.family(),
                    name.clone(),
                    arguments.len(),
                ));
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
            memory_range_covers_for_read(&available, required, assumptions)
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
        return resource_fact_read_core_range(available)
            .is_some_and(|available| {
                memory_range_covers_for_read(&available, required, assumptions)
            })
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

fn resource_quantity_is_positive(
    quantity: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    quantity.as_const().is_some_and(|value| value > 0)
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
        )
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

fn access_mode_core(resource: &CResourceFact) -> Option<CResourceFact> {
    match resource {
        CResourceFact::Own(resource, quantity)
            if quantity.as_const().is_some_and(|value| value > 0) =>
        {
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

impl ResourceFamilyAlgebra for MemoryResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Memory
    }

    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError> {
        let (Some(left), Some(right)) = (left.memory_own_range(), right.memory_own_range()) else {
            return None;
        };
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
        access_mode_core(fact)
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
                        Some(CResourceFact::Own(
                            left.clone(),
                            Box::new(Bitvector32Term::add(
                                left_quantity.as_ref().clone(),
                                right_quantity.as_ref().clone(),
                            )),
                        ))
                    }
                    _ => combine_exact_resource_facts(left, right, assumptions),
                }
            }

            fn core(&self, fact: &CResourceFact) -> Option<CResourceFact> {
                access_mode_core(fact)
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

pub(in crate::kernel) fn memory_range_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if available.element_width() != required.element_width() {
        return false;
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
    if let Some(covers) = memory_range_structurally_covers(available, required) {
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

/// Read access is typed at the leaf being inspected, but an enclosing owned
/// object may use a different logical range width. For example, `object(p)`
/// is int32-indexed while an embedded `uint8` field is byte-indexed. Views
/// may use the enclosing object's physical byte footprint; ownership
/// consumption deliberately stays on [`memory_range_covers`] so residual
/// ownership never changes coordinate systems implicitly.
fn memory_range_covers_for_read(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if available.element_width() == required.element_width() {
        return memory_range_covers(available, required, assumptions);
    }

    let (available_base, available_bytes) = available.byte_footprint();
    let (required_base, required_bytes) = required.byte_footprint();
    let available = CMemoryRange::new_with_element_width(
        available_base,
        Bitvector32Term::Constant(0),
        available_bytes,
        1,
    );
    let required = CMemoryRange::new_with_element_width(
        required_base,
        Bitvector32Term::Constant(0),
        required_bytes,
        1,
    );
    memory_range_covers(&available, &required, assumptions)
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

fn memory_range_structurally_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
) -> Option<bool> {
    if available.element_width() != required.element_width() {
        return None;
    }
    let base_delta = if required.base() == available.base() {
        Bitvector32Term::Constant(0)
    } else {
        required
            .base()
            .element_index_from_base_with_width(available.base(), available.element_width())?
    };
    let available_start = available.start().as_const()? as i32;
    let available_end = available.end().as_const()? as i32;
    let required_start =
        Bitvector32Term::add(base_delta.clone(), required.start().clone()).as_const()? as i32;
    let required_end = Bitvector32Term::add(base_delta, required.end().clone()).as_const()? as i32;
    Some(available_start <= required_start && required_end <= available_end)
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
    if let Some(difference) =
        crate::kernel::assumptions::affine_bitvector_difference_constant(end, start)
    {
        return difference >= 0;
    }
    assumptions.decide(&ConditionTerm::signed_less_equal(
        start.clone(),
        end.clone(),
    )) == Some(true)
}

fn split_memory_range(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<Vec<CMemoryRange>> {
    if available.element_width() != required.element_width() {
        return None;
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
    let required_end = Bitvector32Term::add(base_delta, required.end().clone());
    let keeps_prefix =
        !bitvector_terms_proven_equal(available.start(), &required_start, assumptions)
            && !range_endpoint_terms_equal(available.start(), &required_start, assumptions);
    let keeps_suffix = !bitvector_terms_proven_equal(&required_end, available.end(), assumptions)
        && !range_endpoint_terms_equal(&required_end, available.end(), assumptions);
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

fn memory_ranges_proven_overlapping(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return false;
    }
    if left.element_width() != right.element_width() {
        return false;
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

fn memory_range_covers_with_exact_index(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    let index = required
        .base()
        .element_index_from_base_with_width(available.base(), available.element_width());
    let Some(base_delta) = index
        .and_then(|index| crate::kernel::assumptions::exact_signed_constant(&index, assumptions))
    else {
        return false;
    };
    let (Some(available_start), Some(available_end), Some(required_start), Some(required_end)) = (
        available.start().as_const().map(|value| value as i64),
        available.end().as_const().map(|value| value as i64),
        required.start().as_const().map(|value| value as i64),
        required.end().as_const().map(|value| value as i64),
    ) else {
        return false;
    };
    let Some(required_start) = base_delta.checked_add(required_start) else {
        return false;
    };
    let Some(required_end) = base_delta.checked_add(required_end) else {
        return false;
    };
    available_start <= required_start && required_end <= available_end
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

    pub fn core(&self) -> Option<Self> {
        resource_family_algebra(self.family()).core(self)
    }

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
    if left.base() != right.base() || left.element_width() != right.element_width() {
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
