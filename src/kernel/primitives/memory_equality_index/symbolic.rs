//! Bounded symbolic supplier selection inside the trusted kernel.
//! Footprint congruence selects occurrences, never authority or arithmetic.
use super::super::resource_algebra::{
    memory_range_covers, resource_fact_read_core_range, resource_quantity_is_positive,
};
use super::*;

#[derive(Clone, Default)]
struct Suppliers {
    classes: PersistentMap<u64, ResourceEntryIds>,
    entries: PersistentMap<ResourceEntryId, u64>,
}
impl Suppliers {
    fn merge(&mut self, moved: u64, kept: u64) {
        let Some(mut smaller) = self.classes.get(&moved).cloned() else {
            return;
        };
        let mut larger = self.classes.get(&kept).cloned().unwrap_or_default();
        self.classes.remove(&moved);
        if larger.len() < smaller.len() {
            std::mem::swap(&mut larger, &mut smaller);
        }
        for entry in smaller.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger = larger.with_value(*entry);
        }
        self.classes.insert(kept, larger);
    }
    fn update(&mut self, entry: ResourceEntryId, insert: bool, class: u64, graph: &EqualityGraph) {
        let class = if insert {
            self.entries.insert(entry, class);
            class
        } else {
            let Some(class) = self.entries.get(&entry).copied() else {
                return;
            };
            self.entries.remove(&entry);
            graph.address_class_root(class)
        };
        let entries = self.classes.get(&class).cloned().unwrap_or_default();
        let entries = if insert {
            entries.with_value(entry)
        } else {
            entries.without_value(&entry)
        };
        if entries.is_empty() {
            self.classes.remove(&class);
        } else {
            self.classes.insert(class, entries);
        }
    }
    fn sole(&self, class: u64) -> Option<ResourceEntryId> {
        let entries = self.classes.get(&class)?;
        // This is a cardinality check, not a symbolic range search. Never
        // iterate an ambiguous bucket, including buckets of exact footprints.
        (entries.len() == 1).then(|| *entries.iter().next().expect("sole supplier"))
    }
}

/// Constant byte spans relative to a complete address class. Affine block
/// coordinates alone cannot represent every checked whole-pointer alias.
#[derive(Clone, Default)]
struct RelativeIntervals {
    classes: PersistentMap<u64, ReadIntervals>,
    entries: PersistentMap<ResourceEntryId, (u64, AddressCoordinate)>,
}
impl RelativeIntervals {
    fn update(
        &mut self,
        entry: ResourceEntryId,
        insert: bool,
        class: u64,
        start: AddressCoordinate,
        end: AddressCoordinate,
        graph: &EqualityGraph,
    ) {
        let (class, start) = if insert {
            self.entries.insert(entry, (class, start.clone()));
            (class, start)
        } else {
            let Some((class, start)) = self.entries.get(&entry).cloned() else {
                return;
            };
            self.entries.remove(&entry);
            (graph.address_class_root(class), start)
        };
        let mut intervals = self.classes.get(&class).cloned().unwrap_or_default();
        if insert {
            intervals.insert(start, end, entry);
        } else {
            intervals.remove(start, entry);
        }
        if intervals.len() == 0 {
            self.classes.remove(&class);
        } else {
            self.classes.insert(class, intervals);
        }
    }
    fn merge(&mut self, moved: u64, kept: u64) {
        let Some(mut smaller) = self.classes.get(&moved).cloned() else {
            return;
        };
        let mut larger = self.classes.get(&kept).cloned().unwrap_or_default();
        self.classes.remove(&moved);
        if larger.len() < smaller.len() {
            std::mem::swap(&mut larger, &mut smaller);
        }
        for (start, end, entry) in smaller.iter() {
            crate::instrumentation::record_deterministic_work(1);
            larger.insert(start.clone(), end.clone(), entry);
        }
        self.classes.insert(kept, larger);
    }
}

/// Structural keys retain exact object evidence before graph publication.
/// Updates charge one admitted resource delta; a cold lookup never attaches
/// the input or enumerates facts to discover its object footprint.
#[derive(Clone, Debug, Default)]
pub(in crate::kernel::primitives) struct ObjectSuppliers {
    nonempty: PersistentMap<Pointer, ResourceEntryIds>,
    symbolic: PersistentMap<Pointer, ResourceEntryIds>,
}
impl ObjectSuppliers {
    pub(in crate::kernel::primitives) fn update(
        &mut self,
        entry: ResourceEntryId,
        insert: bool,
        fact: &CResourceFact,
    ) {
        let Some(range) = fact.memory_range() else {
            return;
        };
        let suppliers = if read_extent(fact).is_some() {
            &mut self.nonempty
        } else if RangeSupports::symbolic(range)
            && fact
                .owned_quantity_term()
                .and_then(Bitvector32Term::as_const)
                != Some(0)
        {
            &mut self.symbolic
        } else {
            return;
        };
        let object = range.base().object_identity();
        let entries = suppliers.get(&object).cloned().unwrap_or_default();
        let entries = if insert {
            entries.with_value(entry)
        } else {
            entries.without_value(&entry)
        };
        if entries.is_empty() {
            suppliers.remove(&object);
        } else {
            suppliers.insert(object, entries);
        }
    }
    pub(in crate::kernel::primitives) fn supplier(
        &self,
        object: &Pointer,
    ) -> Option<ResourceEntryId> {
        self.nonempty
            .get(object)
            .and_then(|entries| entries.iter().next().copied())
            .or_else(|| {
                let entries = self.symbolic.get(object)?;
                (entries.len() == 1).then(|| *entries.iter().next().expect("sole object witness"))
            })
    }
}

#[derive(Clone, Default)]
pub(super) struct RangeSupports {
    owned_relative: RelativeIntervals,
    viewed_relative: RelativeIntervals,
    footprints: Suppliers,
    owned_footprints: Suppliers,
    bases: Suppliers,
    owned_bases: Suppliers,
    read_starts: Suppliers,
    // Split owned ranges can share a base while having distinct symbolic starts.
    // Selection at that exact start still leaves quantity and coverage to the checker.
    owned_starts: Suppliers,
    nonempty_objects: Suppliers,
    symbolic_objects: Suppliers,
    object_classes: PersistentMap<Pointer, u64>,
}
impl RangeSupports {
    pub(super) fn register(range: &CMemoryRange, graph: &EqualityGraph) {
        graph.address_class(range.base());
        graph.address_class(&range.start_pointer());
        if Self::symbolic(range) {
            graph.footprint_class(range);
        }
    }
    pub(super) fn register_object(&mut self, range: &CMemoryRange, graph: &EqualityGraph) {
        let object = range.base().object_identity();
        if !self.object_classes.contains_key(&object)
            && let Some(class) = graph.address_class(&object)
        {
            self.object_classes.insert(object, class);
        }
    }
    fn symbolic(range: &CMemoryRange) -> bool {
        range.has_symbolic_bounds()
    }
    pub(super) fn update(
        &mut self,
        entry: ResourceEntryId,
        insert: bool,
        fact: &CResourceFact,
        graph: &EqualityGraph,
    ) {
        let Some(range) = fact.memory_range() else {
            return;
        };
        if let Some(class) = self
            .object_classes
            .get(&range.base().object_identity())
            .copied()
        {
            let class = graph.address_class_root(class);
            if read_extent(fact).is_some() {
                self.nonempty_objects.update(entry, insert, class, graph);
            } else if Self::symbolic(range)
                && fact
                    .owned_quantity_term()
                    .and_then(Bitvector32Term::as_const)
                    != Some(0)
            {
                self.symbolic_objects.update(entry, insert, class, graph);
            }
        }
        if let Some(class) = graph.address_class(range.base()) {
            self.bases.update(entry, insert, class, graph);
            if let Some((start, end)) = Self::constant_span(range) {
                let intervals = if fact.is_own() {
                    &mut self.owned_relative
                } else {
                    &mut self.viewed_relative
                };
                intervals.update(entry, insert, class, start, end, graph);
            }
            if fact.is_own() {
                self.owned_bases.update(entry, insert, class, graph);
            }
        }
        if Self::symbolic(range) {
            let start = range.start_pointer();
            if let Some(class) = graph.address_class(&start) {
                self.read_starts.update(entry, insert, class, graph);
                if fact.is_own() {
                    self.owned_starts.update(entry, insert, class, graph);
                }
            }
        }
        if Self::symbolic(range)
            && let Some(class) = graph.footprint_class(range)
        {
            self.footprints.update(entry, insert, class, graph);
            if fact.is_own() {
                self.owned_footprints.update(entry, insert, class, graph);
            }
        }
    }
    fn constant_span(range: &CMemoryRange) -> Option<(AddressCoordinate, AddressCoordinate)> {
        let start = i128::from(range.signed_constant_start()?) * i128::from(range.element_width());
        let end = i128::from(range.signed_constant_end()?) * i128::from(range.element_width());
        (start < end).then(|| {
            (
                AddressCoordinate(AffineOffset::constant(start)),
                AddressCoordinate(AffineOffset::constant(end)),
            )
        })
    }
    pub(super) fn relative_entries(
        &self,
        range: &CMemoryRange,
        owned: bool,
        graph: &EqualityGraph,
    ) -> Option<Box<dyn Iterator<Item = ResourceEntryId>>> {
        let (start, end) = Self::constant_span(range)?;
        self.relative_byte_entries(range.base(), start, end, owned, graph)
    }
    pub(super) fn relative_byte_entries(
        &self,
        base: &Pointer,
        start: AddressCoordinate,
        end: AddressCoordinate,
        owned: bool,
        graph: &EqualityGraph,
    ) -> Option<Box<dyn Iterator<Item = ResourceEntryId>>> {
        let class = graph.address_class(base)?;
        let mut streams = Vec::new();
        if let Some(intervals) = self.owned_relative.classes.get(&class) {
            streams.push(intervals.covering(&start, &end));
        }
        if !owned && let Some(intervals) = self.viewed_relative.classes.get(&class) {
            streams.push(intervals.covering(&start, &end));
        }
        (!streams.is_empty()).then(|| {
            Box::new(streams.into_iter().flatten()) as Box<dyn Iterator<Item = ResourceEntryId>>
        })
    }
    pub(super) fn footprint_entries(&self, class: u64, owned: bool) -> Option<ResourceEntryIds> {
        let suppliers = if owned {
            &self.owned_footprints
        } else {
            &self.footprints
        };
        suppliers.classes.get(&class).cloned()
    }
    pub(super) fn sole_owned_start(&self, class: u64) -> Option<ResourceEntryId> {
        self.owned_starts.sole(class)
    }
    pub(super) fn sole_base(&self, class: u64, owned: bool) -> Option<ResourceEntryId> {
        if owned {
            self.owned_bases.sole(class)
        } else {
            self.read_starts
                .sole(class)
                .or_else(|| self.bases.sole(class))
        }
    }
    pub(super) fn object_supplier(&self, class: u64) -> Option<ResourceEntryId> {
        // Known nonempty footprints need no candidate search. Unknown symbolic
        // footprints are eligible only when uniquely selected; the consumer
        // proves nonemptiness and object identity from the retained source.
        self.nonempty_objects
            .classes
            .get(&class)
            .and_then(|entries| entries.iter().next().copied())
            .or_else(|| self.symbolic_objects.sole(class))
    }
    pub(super) fn merge(&mut self, moved: u64, kept: u64) {
        self.owned_relative.merge(moved, kept);
        self.viewed_relative.merge(moved, kept);
        self.nonempty_objects.merge(moved, kept);
        self.symbolic_objects.merge(moved, kept);
        self.read_starts.merge(moved, kept);
        self.owned_starts.merge(moved, kept);
        self.bases.merge(moved, kept);
        self.owned_bases.merge(moved, kept);
        self.footprints.merge(moved, kept);
        self.owned_footprints.merge(moved, kept);
    }
}

impl ResourceContext {
    /// Select at most one live supplier, then apply the ordinary read-core
    /// coverage rule. `None` means selection is unknown, not permission denied.
    /// A failed check of a selected supplier is final. Incomparable symbolic
    /// partitions require a checked footprint or a retained occurrence witness.
    /// Witnesses are context-local authority handles, not arbitrary graph IDs.
    pub(in crate::kernel) fn symbolic_range_read_supported(
        &self,
        required: &CMemoryRange,
        assumptions: &PureFactContext,
        supplier: Option<ResourceOccurrenceId>,
    ) -> Option<bool> {
        self.symbolic_range_support(required, assumptions, supplier, false)
    }

    fn symbolic_range_support(
        &self,
        required: &CMemoryRange,
        assumptions: &PureFactContext,
        supplier: Option<ResourceOccurrenceId>,
        owned: bool,
    ) -> Option<bool> {
        let paired = self.pair_memory_equalities_in_graph(
            assumptions.equality_graph.clone(),
            false,
            Some(MemoryQuery::Footprint(required)),
        );
        if !paired.points_initialized {
            return None;
        }
        let footprint = paired.graph.footprint_class(required)?;
        let base = paired.graph.address_class(required.base())?;
        let entry = if let Some(supplier) = supplier {
            *paired.resources.entry_by_occurrence.get(&supplier)?
        } else {
            let footprints = if owned {
                &paired.symbolic.owned_footprints
            } else {
                &paired.symbolic.footprints
            };
            footprints.sole(footprint).or_else(|| {
                let entries = &paired.points.classes.get(&base)?.entries;
                (entries.len() == 1).then(|| *entries.iter().next().expect("sole start supplier"))
            })?
        };
        let fact = paired.resources.facts.get(&entry)?;
        if owned
            && !fact
                .owned_quantity_term()
                .is_some_and(|quantity| resource_quantity_is_positive(quantity, assumptions))
        {
            return Some(false);
        }
        let available = if owned {
            fact.memory_own_range().cloned()
        } else {
            resource_fact_read_core_range(fact)
        };
        let Some(available) = available else {
            return Some(false);
        };
        // Loadability names bytes, while the selected supplier names elements.
        // Invert its explicit scaling before checking bounds, just as clause
        // lowering formed it. This is a conversion of one selected footprint,
        // not another supplier search or an inferred permission premise.
        let element_required = (required.element_width() == 1
            && required.constant_start() == Some(0))
        .then(|| {
            crate::kernel::reasoning::element_count_from_bytes(
                required.end(),
                available.element_width(),
            )
        })
        .flatten()
        .map(|end| {
            CMemoryRange::new_with_element_width(
                required.base().clone(),
                0u32.into(),
                end,
                available.element_width(),
            )
        });
        let required = element_required.as_ref().unwrap_or(required);
        let aligned = if paired.graph.are_equal(required.base(), available.base()) {
            required.with_base(available.base().clone())
        } else {
            let Some(base) = paired
                .graph
                .pointer_in_block(required.base(), &available.base().block)
            else {
                return Some(false);
            };
            required.with_base(base)
        };
        Some(memory_range_covers(&available, &aligned, assumptions))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn range(base: &Pointer, start: Bitvector32Term, end: Bitvector32Term) -> CMemoryRange {
        CMemoryRange::new_with_element_width(base.clone(), start, end, 1)
    }

    #[test]
    fn symbolic_support_selects_exact_footprints_and_checks_selected_bounds() {
        let base = Pointer::symbolic(Variable(910_000));
        let alias = Pointer::symbolic(Variable(910_001));
        let n = Bitvector32Term::Variable(Variable(910_002));
        let k = Bitvector32Term::Variable(Variable(910_003));
        let empty = PureFactContext::new();
        let facts = empty
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(base.clone(), alias.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), k.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_than(k.clone(), n.clone()), true);
        let held = CResourceFact::view_memory(range(&base, 0u32.into(), n.clone()));
        let resources =
            ResourceContext::new_with_equalities(&empty).unchecked_with_fact(held.clone());
        let exact = range(&alias, 0u32.into(), n.clone());
        let indexed = range(&alias, k.clone(), Bitvector32Term::add(k, 1u32.into()));
        assert_eq!(
            resources.symbolic_range_read_supported(&exact, &facts, None),
            Some(true)
        );
        assert_eq!(
            resources.symbolic_range_read_supported(&indexed, &facts, None),
            Some(true)
        );
        assert_eq!(
            resources.symbolic_range_read_supported(&exact, &empty, None),
            None
        );
        let outside = range(
            &alias,
            n.clone(),
            Bitvector32Term::add(n.clone(), 1u32.into()),
        );
        assert_eq!(
            resources.symbolic_range_read_supported(&outside, &facts, None),
            Some(false)
        );
        // Distinct symbolic spans cannot be ordered by a hidden candidate scan.
        let other = CResourceFact::view_memory(range(
            &base,
            0u32.into(),
            Bitvector32Term::add(n, 8u32.into()),
        ));
        let split = resources.clone().unchecked_with_fact(other);
        assert_eq!(
            split.symbolic_range_read_supported(&exact, &facts, None),
            Some(true)
        );
        assert_eq!(
            split.symbolic_range_read_supported(&indexed, &facts, None),
            None
        );
        let supplier = resources.occurrences_for_fact(&held)[0];
        assert_eq!(
            split.symbolic_range_read_supported(&indexed, &facts, Some(supplier)),
            Some(true)
        );
        let removed = split
            .without_exact_representation_for_occurrence(supplier)
            .unwrap();
        assert_eq!(
            removed.symbolic_range_read_supported(&indexed, &facts, Some(supplier)),
            None
        );
        assert_eq!(
            resources.symbolic_range_read_supported(&indexed, &facts, Some(supplier)),
            Some(true)
        );
    }
    #[test]
    fn symbolic_footprint_selection_does_not_scan_same_base_ranges() {
        let base = Pointer::symbolic(Variable(920_000));
        let alias = Pointer::symbolic(Variable(920_001));
        let n = Bitvector32Term::Variable(Variable(920_002));
        let empty = PureFactContext::new();
        let facts = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        );
        let mut samples = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let held = CResourceFact::view_memory(range(&base, 0u32.into(), n.clone()));
            let mut resources =
                ResourceContext::new_with_equalities(&empty).unchecked_with_fact(held.clone());
            for i in 0..size {
                let end = Bitvector32Term::Variable(Variable(921_000 + i));
                resources = resources.unchecked_with_fact(CResourceFact::view_memory(range(
                    &base,
                    0u32.into(),
                    end,
                )));
            }
            // Apply the explicit equality delta before measuring steady queries.
            resources.synchronize_memory_equalities(&facts);
            let required = range(&alias, 0u32.into(), n.clone());
            let supplier = resources.occurrences_for_fact(&held)[0];
            let (((), work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    assert_eq!(
                        resources.symbolic_range_read_supported(&required, &facts, None),
                        Some(true)
                    );
                    let uncertain = range(
                        &alias,
                        0u32.into(),
                        Bitvector32Term::Variable(Variable(950_000)),
                    );
                    assert_eq!(
                        resources.symbolic_range_read_supported(&uncertain, &facts, None),
                        None
                    );
                    assert_eq!(
                        resources.symbolic_range_read_supported(&required, &facts, Some(supplier)),
                        Some(true)
                    );
                })
            });
            samples.push((size, work, persistent));
        }
        assert!(
            samples
                .iter()
                .all(|(_, work, _)| *work <= samples[0].1 * 2 + 64),
            "supplier search: {samples:?}"
        );
        assert!(
            samples
                .iter()
                .all(|(_, _, work)| *work <= samples[0].2 * 4 + 512),
            "deep/linear index lookup: {samples:?}"
        );
    }

    #[test]
    fn symbolic_byte_read_consumer_refuses_ambiguous_suppliers_without_search() {
        let base = Pointer::symbolic(Variable(960_000));
        let alias = Pointer::symbolic(Variable(960_001));
        let n = Bitvector32Term::Variable(Variable(960_002));
        let m = Bitvector32Term::Variable(Variable(960_003));
        let empty = PureFactContext::new();
        let facts = empty
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(base.clone(), alias.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), m.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_equal(m.clone(), n.clone()), true);
        let mut samples = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let held = CResourceFact::view_memory(range(&base, 0u32.into(), n.clone()));
            let mut resources =
                ResourceContext::new_with_equalities(&empty).unchecked_with_fact(held);
            for i in 0..size {
                resources = resources.unchecked_with_fact(CResourceFact::view_memory(range(
                    &base,
                    0u32.into(),
                    Bitvector32Term::Variable(Variable(961_000 + i)),
                )));
            }
            resources.synchronize_memory_equalities(&facts);
            let (((), work), persistent) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    assert!(crate::kernel::resource_context_has_symbolic_range_read(
                        &resources, &alias, &n, &facts,
                    ));
                    // m <= n can validate a selected supplier, but cannot choose
                    // one by testing every range in an ambiguous start bucket.
                    assert!(!crate::kernel::resource_context_has_symbolic_range_read(
                        &resources, &alias, &m, &facts,
                    ));
                })
            });
            samples.push((size, work, persistent));
        }
        assert!(
            samples
                .iter()
                .all(|(_, work, _)| *work <= samples[0].1 * 2 + 64),
            "symbolic byte consumer searched suppliers: {samples:?}"
        );
        assert!(
            samples
                .iter()
                .all(|(_, _, work)| *work <= samples[0].2 * 4 + 512),
            "symbolic byte consumer scanned persistent inputs: {samples:?}"
        );
    }

    #[test]
    fn symbolic_byte_read_consumer_preserves_width_bounds_and_authority() {
        let base = Pointer::symbolic(Variable(962_000));
        let alias = Pointer::symbolic(Variable(962_001));
        let n = Bitvector32Term::Variable(Variable(962_002));
        let k = Bitvector32Term::Variable(Variable(962_003));
        let empty = PureFactContext::new();
        let equal = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        );
        let bounded = equal
            .clone()
            .assume_condition(
                ConditionTerm::signed_less_equal(0u32.into(), k.clone()),
                true,
            )
            .assume_condition(ConditionTerm::signed_less_equal(k.clone(), n.clone()), true);
        for width in [1, 2, 4, 8] {
            let range =
                CMemoryRange::new_with_element_width(base.clone(), 0u32.into(), n.clone(), width);
            let bytes = crate::kernel::memory_range_byte_count(0u32.into(), n.clone(), width);
            let smaller = crate::kernel::memory_range_byte_count(0u32.into(), k.clone(), width);
            for held in [
                CResourceFact::view_memory(range.clone()),
                CResourceFact::own_memory(range.clone()),
            ] {
                let resources =
                    ResourceContext::new_with_equalities(&empty).unchecked_with_fact(held);
                assert!(
                    crate::kernel::resource_context_has_symbolic_range_read(
                        &resources, &alias, &bytes, &equal,
                    ),
                    "exact byte footprint at width {width}"
                );
                assert!(
                    !crate::kernel::resource_context_has_symbolic_range_read(
                        &resources, &alias, &bytes, &empty,
                    ),
                    "sibling without alias evidence"
                );
                assert!(
                    crate::kernel::resource_context_has_symbolic_range_read(
                        &resources, &alias, &smaller, &bounded,
                    ),
                    "selected supplier's bounds at width {width}"
                );
                assert!(
                    !crate::kernel::resource_context_has_symbolic_range_read(
                        &resources, &alias, &smaller, &equal,
                    ),
                    "missing bounds at width {width}"
                );
            }
            let zero = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
                CResourceFact::Own(CResource::Memory(range), Box::new(0u32.into())),
            );
            assert!(
                !crate::kernel::resource_context_has_symbolic_range_read(
                    &zero, &alias, &bytes, &equal,
                ),
                "zero quantity is not read authority"
            );
        }
    }

    #[test]
    fn symbolic_supplier_access_modes_remain_separate() {
        let base = Pointer::symbolic(Variable(930_000));
        let n = Bitvector32Term::Variable(Variable(930_001));
        let facts = PureFactContext::new();
        let required = range(&base, 0u32.into(), n);
        let view = CResourceFact::view_memory(required.clone());
        let owner = CResourceFact::own_memory(required.clone());
        let resources =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(view.clone());
        let view_id = resources.occurrences_for_fact(&view)[0];
        assert_eq!(
            resources.symbolic_range_support(&required, &facts, None, true),
            Some(false)
        );
        assert_eq!(
            resources.symbolic_range_support(&required, &facts, Some(view_id), true),
            Some(false)
        );
        let zero = CResourceFact::Own(owner.resource().clone(), Box::new(0u32.into()));
        let zeros = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(zero.clone());
        let zero_id = zeros.occurrences_for_fact(&zero)[0];
        assert_eq!(
            zeros.symbolic_range_support(&required, &facts, Some(zero_id), true),
            Some(false)
        );
        assert_eq!(
            zeros.symbolic_range_read_supported(&required, &facts, Some(zero_id)),
            Some(false)
        );
        let wrong = Pointer::symbolic(Variable(930_002));
        assert_eq!(
            resources.symbolic_range_read_supported(
                &range(&wrong, 0u32.into(), 1u32.into()),
                &facts,
                Some(view_id)
            ),
            Some(false)
        );
        let resources = resources.unchecked_with_fact(owner);
        assert_eq!(
            resources.symbolic_range_support(&required, &facts, None, true),
            Some(true)
        );
    }
    #[test]
    fn symbolic_footprints_follow_endpoint_equalities_and_snapshot_origins() {
        let slot = Pointer::symbolic(Variable(940_000));
        let alias = Pointer::symbolic(Variable(940_001));
        let n = Bitvector32Term::Variable(Variable(940_002));
        let m = Bitvector32Term::Variable(Variable(940_003));
        let snapshot = crate::kernel::intern_c_memory(CMemory::new());
        let loaded = Pointer::loaded_value(&snapshot, &slot);
        let loaded_alias = Pointer::loaded_value(&snapshot, &alias);
        let empty = PureFactContext::new();
        let equal_base = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(slot.clone(), alias.clone()),
            true,
        );
        let facts = equal_base
            .clone()
            .assume_condition(ConditionTerm::equal(n.clone(), m.clone()), true);
        let held = CResourceFact::view_memory(range(&loaded, 0u32.into(), n.clone()));
        let other = CResourceFact::view_memory(range(
            &loaded,
            0u32.into(),
            Bitvector32Term::Variable(Variable(940_004)),
        ));
        let resources = ResourceContext::new_with_equalities(&empty)
            .unchecked_with_fact(held)
            .unchecked_with_fact(other);
        let required = range(&loaded_alias, 0u32.into(), m);
        assert_eq!(
            resources.symbolic_range_read_supported(&required, &equal_base, None),
            None
        );
        assert_eq!(
            resources.symbolic_range_read_supported(&required, &facts, None),
            Some(true)
        );
        assert_eq!(
            resources.symbolic_range_read_supported(&required, &empty, None),
            None
        );
        let later = crate::kernel::intern_c_memory(CMemory::new().with_block("later", 8));
        let required = range(&Pointer::loaded_value(&later, &alias), 0u32.into(), n);
        assert_eq!(
            resources.symbolic_range_read_supported(&required, &facts, None),
            None
        );
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Aligning an alias to its supplier must preserve native endpoints.
    #[test]
    fn wide_symbolic_supplier_alignment_keeps_native_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(985_200));
        let alias = Pointer::symbolic(Variable(985_201));
        let wide = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::Variable(Variable(985_202)),
            1,
        );
        let facts = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(base, alias.clone()), true);
        let held = CResourceFact::view_memory(wide.clone());
        let resources = ResourceContext::new().unchecked_with_fact(held.clone());
        // Register the resource input at publication, before bounded queries.
        resources.pair_memory_equalities(&facts, true, None);
        let supplier = resources.occurrences_for_fact(&held)[0];
        assert_eq!(
            resources.symbolic_range_read_supported(&wide.with_base(alias), &facts, Some(supplier)),
            Some(true)
        );
    }
}
