use super::*;

thread_local! {
    static RESOURCE_COMPOSITION_QUERY_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Proof-aware composition queries may nest: bridging a query's snapshot
/// form to a carrier entry can itself ask whether a pointer survived a
/// call havoc, which is served by the same composition. A binary lock would
/// force those inner queries to fail where the former materialized pairs
/// answered them, so nesting is allowed to a small fixed depth; the
/// memory-resolution fuel still bounds total work.
const RESOURCE_COMPOSITION_QUERY_DEPTH_LIMIT: usize = 3;

struct ResourceCompositionQueryGuard;

impl ResourceCompositionQueryGuard {
    fn enter() -> Option<Self> {
        RESOURCE_COMPOSITION_QUERY_DEPTH.with(|depth| {
            if depth.get() >= RESOURCE_COMPOSITION_QUERY_DEPTH_LIMIT {
                return None;
            }
            depth.set(depth.get() + 1);
            Some(Self)
        })
    }
}

impl Drop for ResourceCompositionQueryGuard {
    fn drop(&mut self) {
        RESOURCE_COMPOSITION_QUERY_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
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

impl ResourceContext {
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
            let mut explicit = 0;
            let mut supported = BTreeMap::<CResourceFact, usize>::new();
            for entry in context
                .storage
                .index
                .exact
                .get(fact)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
            {
                if let Some(support) = context.storage.supported_by.get(entry) {
                    *supported.entry(support.clone()).or_default() += 1;
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
                .filter_map(|(support, left_count)| {
                    right_supported
                        .get(&support)
                        .map(|right_count| (support, left_count.min(*right_count)))
                })
                .collect::<Vec<_>>();
            let expansion = left
                .storage
                .expansions_by_support
                .get(fact)
                .filter(|left_expansion| {
                    right.storage.expansions_by_support.get(fact) == Some(*left_expansion)
                })
                .map(|expansion| expansion.as_ref().clone());
            common_representations.push((
                fact.clone(),
                left_explicit.min(right_explicit),
                supported,
                expansion,
            ));
        }

        let mut common = left.clone();
        for fact in &changed {
            let entries = common
                .storage
                .index
                .exact
                .get(fact)
                .cloned()
                .unwrap_or_default();
            for entry in entries.iter().copied() {
                if common.storage.facts.contains_key(&entry) {
                    common.remove_entry(entry);
                }
            }
        }
        for (fact, explicit, _, _) in &common_representations {
            for _ in 0..*explicit {
                common.insert_fact(fact.clone());
            }
        }
        for (fact, _, supported, _) in &common_representations {
            for (support, count) in supported {
                if !common.storage.index.exact.contains_key(support) {
                    continue;
                }
                for _ in 0..*count {
                    common.insert_fact_with_support(fact.clone(), Some(support.clone()));
                }
            }
        }
        for (support, _, _, expansion) in common_representations {
            if let Some(expansion) = expansion
                && common.storage.index.exact.contains_key(&support)
            {
                common = common.with_cached_supported_expansion(&support, expansion);
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

    fn insert_fact(&mut self, fact: CResourceFact) {
        self.insert_fact_with_support(fact, None);
    }

    fn insert_fact_with_support(&mut self, fact: CResourceFact, support: Option<CResourceFact>) {
        let entry = self.storage.next_entry_id;
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
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.with_inserted(entry, fact.clone()),
            next_entry_id,
            index: self.storage.index.with_inserted(entry, &fact),
            supported_by,
            projections_by_support,
            expansions_by_support: self.storage.expansions_by_support.clone(),
            origin: self.storage.origin.clone(),
            history: Some(std::sync::Arc::new(ResourceContextChange {
                fact,
                parent: self.storage.history.clone(),
            })),
            materialized: std::sync::OnceLock::new(),
        });
    }

    fn remove_entry(&mut self, entry: ResourceEntryId) -> CResourceFact {
        let fact = self.fact(entry).clone();
        let projections = self
            .storage
            .projections_by_support
            .get(&fact)
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
        let projections_by_support = support.as_ref().map_or_else(
            || self.storage.projections_by_support.clone(),
            |support| {
                remove_resource_index_entry(&self.storage.projections_by_support, support, entry)
            },
        );
        let expansions_by_support = self.storage.expansions_by_support.without_key(&fact);
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.without_key(&entry),
            next_entry_id: self.storage.next_entry_id,
            index: self.storage.index.without_entry(entry, &fact),
            supported_by,
            projections_by_support,
            expansions_by_support,
            origin: self.storage.origin.clone(),
            history: Some(std::sync::Arc::new(ResourceContextChange {
                fact: fact.clone(),
                parent: self.storage.history.clone(),
            })),
            materialized: std::sync::OnceLock::new(),
        });
        fact
    }

    fn replace_facts(
        &mut self,
        facts: impl IntoIterator<Item = CResourceFact>,
        changed_facts: impl IntoIterator<Item = CResourceFact>,
    ) {
        let mut replacement_facts = PersistentMap::default();
        let mut replacement_index = ResourceContextIndex::default();
        let mut next_entry_id = 0_u64;
        for fact in facts {
            replacement_facts = replacement_facts.with_inserted(next_entry_id, fact.clone());
            replacement_index = replacement_index.with_inserted(next_entry_id, &fact);
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
            index: replacement_index,
            supported_by: PersistentMap::default(),
            projections_by_support: PersistentMap::default(),
            expansions_by_support: PersistentMap::default(),
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

    pub(crate) fn proves_owned_resources_separate(
        &self,
        left: &CResource,
        right: &CResource,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter() else {
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
        let Some(_guard) = ResourceCompositionQueryGuard::enter() else {
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

    pub(in crate::kernel) fn proves_owned_pointers_separate_by(
        &self,
        left: &Pointer,
        right: &Pointer,
        contains: impl Fn(&Pointer, &CMemoryRange) -> bool,
    ) -> bool {
        let Some(_guard) = ResourceCompositionQueryGuard::enter() else {
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
    pub(crate) fn unchecked_with_supported_facts(
        mut self,
        support: &CResourceFact,
        facts: impl IntoIterator<Item = CResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert!(self.storage.index.exact.contains_key(support));
        for fact in facts {
            debug_assert!(fact.is_view());
            self.insert_fact_with_support(fact, Some(support.clone()));
        }
        self
    }

    pub(crate) fn with_cached_supported_expansion(
        mut self,
        support: &CResourceFact,
        expansion: Vec<CResourceFact>,
    ) -> Self {
        debug_assert!(support.is_own());
        debug_assert!(self.storage.index.exact.contains_key(support));
        self.storage = std::sync::Arc::new(ResourceContextStorage {
            facts: self.storage.facts.clone(),
            next_entry_id: self.storage.next_entry_id,
            index: self.storage.index.clone(),
            supported_by: self.storage.supported_by.clone(),
            projections_by_support: self.storage.projections_by_support.clone(),
            expansions_by_support: self
                .storage
                .expansions_by_support
                .with_inserted(support.clone(), std::sync::Arc::new(expansion)),
            origin: self.storage.origin.clone(),
            history: Some(std::sync::Arc::new(ResourceContextChange {
                fact: support.clone(),
                parent: self.storage.history.clone(),
            })),
            materialized: std::sync::OnceLock::new(),
        });
        self
    }

    pub(crate) fn cached_supported_expansion(
        &self,
        support: &CResourceFact,
    ) -> Option<&[CResourceFact]> {
        self.storage
            .expansions_by_support
            .get(support)
            .map(|expansion| expansion.as_slice())
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
            .filter_map(|entry| self.storage.supported_by.get(entry))
            .find(|support| {
                self.storage
                    .expansions_by_support
                    .get(*support)
                    .is_some_and(|expansion| expansion.iter().any(|fact| fact == target))
            })
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
        let context = self.unchecked_with_facts(facts);
        if let Some(error) = context.validity_error(assumptions) {
            return Err(error);
        }
        Ok(context)
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
                self.insert_fact(fact);
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
        if !self.storage.supported_by.is_empty() || !self.storage.expansions_by_support.is_empty() {
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
                index: self.storage.index.clone(),
                supported_by: self.storage.supported_by.clone(),
                projections_by_support: self.storage.projections_by_support.clone(),
                expansions_by_support: PersistentMap::default(),
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
            .iter()
            .filter_map(|fact| {
                if fact
                    .owned_quantity_term()
                    .is_some_and(|quantity| quantity.as_const() == Some(0))
                {
                    changed_facts.insert(fact.clone());
                    None
                } else {
                    Some(fact.clone())
                }
            })
            .collect::<Vec<_>>();
        let mut slots = retained.iter().cloned().map(Some).collect::<Vec<_>>();
        let mut index = ResourceNormalizationIndex::default();
        for (position, fact) in retained.iter().enumerate() {
            index.insert(position, fact);
        }
        let mut i = 0;
        while i < slots.len() {
            let Some(fact) = slots[i].clone() else {
                i += 1;
                continue;
            };
            let mut changed = false;
            for j in index.candidates_after(i, &fact) {
                crate::instrumentation::record_deterministic_work(1);
                let Some(right) = slots[j].as_ref() else {
                    continue;
                };
                if let Some(merged) = normalize_resource_fact_pair(&fact, right, assumptions) {
                    changed_facts.insert(fact.clone());
                    changed_facts.insert(right.clone());
                    changed_facts.insert(merged.clone());
                    index.remove(i, &fact);
                    index.remove(j, right);
                    slots[j] = None;
                    slots[i] = Some(merged.clone());
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

    fn supported_projection_pairs(&self) -> Vec<(CResourceFact, CResourceFact)> {
        self.storage
            .supported_by
            .iter()
            .map(|(entry, support)| (support.clone(), self.fact(*entry).clone()))
            .collect()
    }

    fn restore_supported_projection_pairs(
        mut self,
        supported: Vec<(CResourceFact, CResourceFact)>,
    ) -> Self {
        for (support, projection) in supported {
            if !self.storage.index.exact.contains_key(&support) {
                continue;
            }
            let already_present = self
                .storage
                .projections_by_support
                .get(&support)
                .into_iter()
                .flat_map(ResourceEntryIds::iter)
                .any(|entry| self.fact(*entry) == &projection);
            if !already_present {
                self.insert_fact_with_support(projection, Some(support));
            }
        }
        self
    }

    fn cached_support_expansions(&self) -> Vec<(CResourceFact, Vec<CResourceFact>)> {
        self.storage
            .expansions_by_support
            .iter()
            .map(|(support, expansion)| (support.clone(), expansion.as_ref().clone()))
            .collect()
    }

    fn restore_cached_support_expansions(
        mut self,
        expansions: Vec<(CResourceFact, Vec<CResourceFact>)>,
    ) -> Self {
        for (support, expansion) in expansions {
            if self.storage.index.exact.contains_key(&support) {
                self = self.with_cached_supported_expansion(&support, expansion);
            }
        }
        self
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ResourceNormalizationKey {
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
    };
    debug_assert_eq!(algebra.family(), family);
    algebra
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
                    .zip(right_arguments)
                    .all(|(left, right)| {
                        c_values_proven_equal_for_memory_resolution(left, right, assumptions)
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

fn resource_quantity_at_least(
    available: &Bitvector32Term,
    required: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    available == required
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(available.clone()),
                Box::new(required.clone()),
            ),
            true,
        ))
}

fn resource_quantity_is_positive(
    quantity: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    quantity.as_const().is_some_and(|value| value > 0)
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ))
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
        let residual_is_zero = assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(residual.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ));
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

fn resource_fact_read_core_range(resource: &CResourceFact) -> Option<CMemoryRange> {
    match resource.core()? {
        CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::View(CResource::Composite { .. } | CResource::Token { .. })
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
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
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
        // The load-unchanged check re-enters separation reasoning, which can
        // re-enter range comparison; guard against unbounded mutual
        // recursion rather than relying on structural depth.
        thread_local! {
            static ENDPOINT_BRIDGE_ACTIVE: std::cell::Cell<bool> =
                const { std::cell::Cell::new(false) };
        }
        if let (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) = (left, right)
            && left_pointer == right_pointer
        {
            if ENDPOINT_BRIDGE_ACTIVE.with(std::cell::Cell::get) {
                crate::kernel::assumptions::note_search_truncation();
                return false;
            }
            ENDPOINT_BRIDGE_ACTIVE.with(|active| active.set(true));
            let bridged = crate::kernel::api::c_memory_load_is_unchanged(
                left_memory,
                right_memory,
                left_pointer,
                assumptions,
            ) || crate::kernel::api::c_memory_load_is_unchanged(
                right_memory,
                left_memory,
                left_pointer,
                assumptions,
            );
            ENDPOINT_BRIDGE_ACTIVE.with(|active| active.set(false));
            return bridged;
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

fn memory_resource_fact_range(fact: &CResourceFact) -> Option<&CMemoryRange> {
    match fact {
        CResourceFact::Own(CResource::Memory(range), _)
        | CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
        | CResourceFact::View(CResource::Composite { .. } | CResource::Token { .. }) => None,
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
    let mut residues = Vec::new();
    if !bitvector_terms_proven_equal(available.start(), &required_start, assumptions)
        && !range_endpoint_terms_equal(available.start(), &required_start, assumptions)
    {
        residues.push(available.with_bounds(
            available.base().clone(),
            available.start().clone(),
            required_start.clone(),
        ));
    }
    if !bitvector_terms_proven_equal(&required_end, available.end(), assumptions)
        && !range_endpoint_terms_equal(&required_end, available.end(), assumptions)
    {
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

impl CResource {
    pub fn family(&self) -> ResourceFamily {
        match self {
            Self::Memory(_) => ResourceFamily::Memory,
            Self::Composite { .. } => ResourceFamily::Composite,
            Self::Token { .. } => ResourceFamily::Token,
        }
    }
}

impl CResourceFact {
    pub const ALLOCATION_RESOURCE_NAME: &'static str = "allocation";

    pub fn own_memory(range: CMemoryRange) -> Self {
        Self::own(CResource::Memory(range))
    }

    pub fn view_memory(range: CMemoryRange) -> Self {
        Self::View(CResource::Memory(range))
    }

    pub fn own_composite(name: String, arguments: Vec<CValue>) -> Self {
        Self::own(CResource::Composite { name, arguments })
    }

    pub fn view_composite(name: String, arguments: Vec<CValue>) -> Self {
        Self::View(CResource::Composite { name, arguments })
    }

    pub fn own_token(name: String, arguments: Vec<CValue>) -> Self {
        Self::own(CResource::Token { name, arguments })
    }

    pub fn own(resource: CResource) -> Self {
        Self::Own(resource, Box::new(Bitvector32Term::Constant(1)))
    }

    pub fn own_quantity(resource: CResource, quantity: Bitvector32Term) -> Self {
        Self::Own(resource, Box::new(quantity))
    }

    pub(crate) fn has_proven_zero_quantity(&self, assumptions: &PureFactContext) -> bool {
        self.owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_zero(quantity, assumptions))
    }

    pub(crate) fn has_proven_positive_quantity(&self, assumptions: &PureFactContext) -> bool {
        self.owned_quantity_term()
            .is_some_and(|quantity| resource_quantity_is_positive(quantity, assumptions))
    }

    pub fn own_allocation(base: Pointer, bytes: impl Into<Bitvector32Term>) -> Self {
        let bytes = bytes.into();
        Self::own_token(
            Self::ALLOCATION_RESOURCE_NAME.to_string(),
            vec![CValue::Pointer(base), int32(bytes)],
        )
    }

    pub fn allocation(&self) -> Option<(&Pointer, &Bitvector32Term)> {
        let Self::Own(CResource::Token { name, arguments }, _) = self else {
            return None;
        };
        if name != Self::ALLOCATION_RESOURCE_NAME {
            return None;
        }
        let [CValue::Pointer(base), CValue::Int32(bytes)] = arguments.as_slice() else {
            return None;
        };
        Some((base, bytes))
    }

    pub(in crate::kernel) fn may_refer_to_memory_block(&self, block: &PointerBlock) -> bool {
        match self.resource() {
            CResource::Memory(range) => &range.base().block == block,
            CResource::Composite { arguments, .. } => arguments.iter().any(
                |argument| matches!(argument, CValue::Pointer(pointer) if &pointer.block == block),
            ),
            CResource::Token { .. } => false,
        }
    }

    pub(in crate::kernel) fn is_proven_separate_from_allocation(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> bool {
        let Some(element_count) = crate::kernel::reasoning::int32_element_count_from_bytes(bytes)
        else {
            return false;
        };
        let allocation_memory = CResource::Memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            element_count,
        ));
        assumptions.proves(&Proposition::CResourceSeparate {
            left: allocation_memory,
            right: self.resource().clone(),
        })
    }

    pub fn view_token(name: String, arguments: Vec<CValue>) -> Self {
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
        match self {
            Self::Own(resource, quantity)
                if quantity.as_const().is_some_and(|value| value > 0)
                    || assumptions.proves(&Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedGreaterThan(
                            Box::new(quantity.as_ref().clone()),
                            Box::new(Bitvector32Term::Constant(0)),
                        ),
                        true,
                    )) =>
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
            Self::Own(CResource::Composite { .. } | CResource::Token { .. }, _) | Self::View(_) => {
                None
            }
        }
    }

    pub fn memory_view_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::View(CResource::Memory(range)) => Some(range),
            Self::View(CResource::Composite { .. } | CResource::Token { .. }) | Self::Own(..) => {
                None
            }
        }
    }

    pub fn memory_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range), _) | Self::View(CResource::Memory(range)) => {
                Some(range)
            }
            Self::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
            | Self::View(CResource::Composite { .. } | CResource::Token { .. }) => None,
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
