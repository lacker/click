//! Value-origin equality. Address congruence must never enter this index.
use super::PointerValue;
use crate::persistent::{PersistentMap, PersistentSet};

/// Persistent union by size. Insertion touches two root paths; a branch
/// forks a persistent clone.
#[derive(Clone, Debug)]
pub(super) struct ValueClasses<K: Ord> {
    parents: PersistentMap<K, K>,
    sizes: PersistentMap<K, usize>,
    edges: PersistentMap<K, PersistentSet<K>>,
    /// Reverse admission order, independent of state content hashes.
    ordered_edges: PersistentMap<K, PersistentMap<u64, K>>,
    next_edge: u64,
    representative: PersistentMap<K, K>,
}

impl<K: Ord> Default for ValueClasses<K> {
    fn default() -> Self {
        Self {
            parents: Default::default(),
            sizes: Default::default(),
            edges: Default::default(),
            ordered_edges: Default::default(),
            next_edge: 0,
            representative: Default::default(),
        }
    }
}
impl<K: Ord + Clone> ValueClasses<K> {
    fn root(&self, value: &K) -> K {
        let mut root = value;
        while let Some(parent) = self.parents.get(root) {
            crate::instrumentation::record_deterministic_work(1);
            root = parent;
        }
        root.clone()
    }
    pub(super) fn equal(&self, left: &K, right: &K) -> bool {
        left == right || self.root(left) == self.root(right)
    }
    pub(super) fn representative(&self, value: &K) -> K {
        self.representative
            .get(&self.root(value))
            .unwrap_or(value)
            .clone()
    }
    /// One stated source for a checked read comparison. An ambiguous neighbor
    /// bucket requires an explicit premise, not a spelling search.
    pub(super) fn unique_direct_alias(&self, value: &K) -> Option<&K> {
        let _checking =
            crate::instrumentation::CheckingWorkScope::new("select provenance alias", 1);
        let neighbors = self.ordered_edges.get(value)?;
        if neighbors.len() != 1 {
            return None;
        }
        neighbors.values().next()
    }
    #[cfg(test)]
    pub(super) fn direct_aliases(&self, value: &K) -> impl Iterator<Item = &K> {
        self.ordered_edges
            .get(value)
            .into_iter()
            .flat_map(|neighbors| neighbors.iter().rev().map(|(_, key)| key))
    }
    fn join(&mut self, left: &K, right: &K, prefer: impl Fn(&K, &K) -> K) {
        let mut left = self.root(left);
        let mut right = self.root(right);
        if left == right {
            return;
        }
        let mut a = self.sizes.get(&left).copied().unwrap_or(1);
        let mut b = self.sizes.get(&right).copied().unwrap_or(1);
        if a < b {
            std::mem::swap(&mut left, &mut right);
            std::mem::swap(&mut a, &mut b);
        }
        let value = prefer(&self.representative(&left), &self.representative(&right));
        self.parents = self.parents.with_inserted(right.clone(), left.clone());
        self.sizes = self
            .sizes
            .without_key(&right)
            .with_inserted(left.clone(), a + b);
        self.representative = self
            .representative
            .without_key(&right)
            .with_inserted(left, value);
    }
    pub(super) fn insert(&mut self, left: &K, right: &K, prefer: impl Fn(&K, &K) -> K) {
        if left == right {
            return;
        }
        for (a, b) in [(left, right), (right, left)] {
            let neighbors = self.edges.get(a).cloned().unwrap_or_default();
            if neighbors.contains(b) {
                continue;
            }
            let ordinal = self.next_edge;
            self.next_edge = self
                .next_edge
                .checked_add(1)
                .expect("pointer alias ordinals exhausted");
            let ordered = self.ordered_edges.get(a).cloned().unwrap_or_default();
            self.ordered_edges = self
                .ordered_edges
                .with_inserted(a.clone(), ordered.with_inserted(ordinal, b.clone()));
            self.edges = self
                .edges
                .with_inserted(a.clone(), neighbors.with_value(b.clone()));
        }
        self.join(left, right, prefer);
    }
}

pub(super) fn prefer_pointer(left: &PointerValue, right: &PointerValue) -> PointerValue {
    // A contract supplies the designation of an opaque incoming value. Its
    // explicit subobject boundary takes precedence over an unknown extent.
    if !left.extent_is_known() && right.extent_is_known()
        || matches!(right.pointer().block, super::PointerBlock::Function(_))
            && !matches!(left.pointer().block, super::PointerBlock::Function(_))
    {
        // A complete-value class can expose a concrete callback target even
        // when both the structural read and the target have known root bounds.
        right.clone()
    } else {
        left.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::*;

    #[test]
    fn origin_aliases_follow_admission_not_value_order() {
        let mut graph = super::ValueClasses::default();
        let prefer = |a: &i32, _: &i32| *a;
        graph.insert(&100, &900, prefer);
        graph.insert(&100, &1, prefer);
        let sibling = graph.clone();
        graph.insert(&100, &500, prefer);
        graph.insert(&100, &900, prefer);
        let aliases = |graph: &super::ValueClasses<i32>| {
            graph.direct_aliases(&100).copied().collect::<Vec<_>>()
        };
        assert_eq!(aliases(&graph), [500, 1, 900]);
        assert_eq!(aliases(&sibling), [1, 900]);
        assert!(graph.equal(&100, &900));
        assert!(graph.equal(&100, &500));
        assert!(!sibling.equal(&100, &500));
    }

    fn value(id: u64) -> PointerValue {
        PointerValue::new(Pointer::symbolic(Variable(id)), ProgramType::Int32Pointer)
    }
    fn equality(a: &PointerValue, b: &PointerValue) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(a.clone()), Box::new(b.clone())),
            true,
        )
    }
    #[test]
    fn only_true_full_pointer_equalities_supply_numeric_index_equalities() {
        let a = MachineTerm::Variable(Variable(809_998));
        let b = MachineTerm::Variable(Variable(809_999));
        let pointer = |index| {
            PointerValue::new(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(index, 4),
                },
                ProgramType::Int32Pointer,
            )
        };
        let equality = ConditionTerm::PointerValueEqual(
            Box::new(pointer(a.clone())),
            Box::new(pointer(b.clone())),
        );
        let context = PureFactContext::new().assume_condition(equality.clone(), true);
        assert!(context.int32_values_known_equal(&a, &b));
        let unequal = PureFactContext::new().assume_condition(equality, false);
        assert!(!unequal.int32_values_known_equal(&a, &b));
    }

    #[test]
    fn a_proven_null_address_denotes_the_unique_null_value() {
        let pointer = value(810_000);
        let null = PointerValue::new(Pointer::null(), ProgramType::Int32Pointer);
        let empty = PureFactContext::new();
        assert!(!empty.pointer_designations_match(&pointer, &null));
        let context = empty.assume_condition(
            ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null()),
            true,
        );
        assert!(context.pointer_designations_match(&pointer, &null));
        assert!(crate::kernel::resource_arguments_proven_equal(
            &ProgramValue::Pointer(pointer).into(),
            &ProgramValue::Pointer(null).into(),
            &context,
        ));
    }

    #[test]
    fn address_equality_preserves_memory_aliasing_without_granting_designation() {
        let a = value(810_001);
        let b = value(810_002);
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone()),
            true,
        );
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::from_pointer_value(&b, 0u32.into(), 1u32.into(), 4),
        ));
        assert!(context.pointers_known_equal(a.pointer(), b.pointer()));
        assert!(resources.permits_memory_read(a.pointer(), 4, &context));
        assert!(!resources.permits_designated_memory_read(
            a.pointer(),
            Some(a.access_designation()),
            4,
            &context
        ));
        assert!(
            resources
                .designated_memory_write_range(
                    a.pointer(),
                    Some(a.access_designation()),
                    4,
                    &context
                )
                .is_none()
        );
        let linked = context.clone().assume_proposition(equality(&a, &b));
        assert!(resources.permits_designated_memory_read(
            a.pointer(),
            Some(a.access_designation()),
            4,
            &linked
        ));
        assert!(
            resources
                .designated_memory_write_range(
                    a.pointer(),
                    Some(a.access_designation()),
                    4,
                    &linked
                )
                .is_some()
        );
    }
    #[test]
    fn equality_of_widened_views_does_not_widen_the_original_input() {
        let input = value(815_001);
        let parent = value(815_002);
        let byte_view = input.clone().with_root_extent();
        let parent_view = parent.clone().with_root_extent();
        let context = PureFactContext::new().assume_proposition(equality(&byte_view, &parent_view));
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::from_pointer_value(&parent, 0u32.into(), 2u32.into(), 4),
        ));
        assert!(context.designations_equal(input.designation(), parent.designation()));
        assert!(!resources.permits_designated_memory_read(
            input.pointer(),
            Some(input.access_designation()),
            4,
            &context
        ));
        assert!(resources.permits_designated_memory_read(
            byte_view.pointer(),
            Some(byte_view.access_designation()),
            4,
            &context
        ));
        let split = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::from_pointer_value(
                &input,
                0u32.into(),
                1u32.into(),
                4,
            )))
            .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::from_pointer_value(
                &parent,
                1u32.into(),
                2u32.into(),
                4,
            )))
            .normalized(&context);
        let sibling = input.pointer().offset_by_bytes(4);
        assert!(!split.permits_designated_memory_read(
            &sibling,
            Some(input.access_designation()),
            4,
            &context
        ));
        let selected = byte_view.with_extent(Some(SubobjectExtent {
            start: input.pointer().clone(),
            width: 4u32.into(),
        }));
        let selected_resources =
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::from_pointer_value(&selected, 0u32.into(), 1u32.into(), 4),
            ));
        assert!(!selected_resources.permits_designated_memory_read(
            input.pointer(),
            Some(input.access_designation()),
            4,
            &context
        ));
    }

    #[test]
    fn origin_support_handles_cycles_and_reverse_edges() {
        let a = value(820_001);
        let b = value(820_002);
        let c = value(820_003);
        let ab = equality(&a, &b);
        let ba = equality(&b, &a);
        let bc = equality(&b, &c);
        let context = PureFactContext::new()
            .assume_proposition(ab)
            .assume_proposition(ba)
            .assume_proposition(bc.clone());
        assert!(context.designations_equal(a.designation(), c.designation()));
        let bc_only = PureFactContext::new().assume_proposition(bc);
        assert!(!bc_only.designations_equal(a.designation(), c.designation()));
        assert!(bc_only.designations_equal(b.designation(), c.designation()));
    }
    #[test]
    fn a_narrowed_read_does_not_narrow_its_enclosing_pointer() {
        let parent = value(824_001);
        let member = parent.clone().with_extent(Some(SubobjectExtent {
            start: parent.pointer().clone(),
            width: 4u32.into(),
        }));
        let retained_state = crate::kernel::intern_memory(Memory::new());
        let cell = Pointer::symbolic(Variable(824_002));
        let read_address = Pointer::symbolic(Variable(824_003));
        let read = PointerValue::from_read(
            read_address,
            ProgramType::Int32Pointer,
            &retained_state,
            &cell,
        );
        let context = PureFactContext::new().assume_proposition(equality(&read, &member));
        assert!(context.pointer_value_at_entry(&read).extent().is_some());
        assert!(context.pointer_value_at_entry(&parent).extent().is_none());
        assert!(!context.contains_known(&equality(&parent, &member)));
        assert!(!context.pointer_designations_match(&parent, &read));
    }

    #[test]
    fn equal_storage_addresses_preserve_a_complete_pointer_reads_designation() {
        let a = value(825_001);
        let b = value(825_002);
        let retained_state = crate::kernel::intern_memory(Memory::new());
        let x = PointerValue::from_read(
            Pointer::symbolic(Variable(825_003)),
            ProgramType::Int32Pointer,
            &retained_state,
            a.pointer(),
        );
        let y = PointerValue::from_read(
            Pointer::symbolic(Variable(825_004)),
            ProgramType::Int32Pointer,
            &retained_state,
            b.pointer(),
        );
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone()),
            true,
        );
        assert!(!context.designations_equal(a.designation(), b.designation()));
        assert!(context.designations_equal(x.designation(), y.designation()));
    }

    #[test]
    fn pointer_value_equality_combines_with_a_scalar_offset_equality() {
        let a = value(830_001);
        let b = value(830_002);
        let offset = MachineTerm::Variable(Variable(830_003));
        let facts = [
            equality(&a, &b),
            Proposition::ConditionIs(ConditionTerm::equal(offset.clone(), 0u32.into()), true),
        ];
        let context = facts.iter().fold(PureFactContext::new(), |c, f| {
            c.assume_proposition(f.clone())
        });
        let displaced = a.clone().with_address(
            a.pointer()
                .offset_by_typed_elements(offset, 4, false, false),
        );
        let goal = equality(&displaced, &b);
        assert!(context.pointer_designations_match(&displaced, &b));
        assert!(context.pointers_known_equal(displaced.pointer(), b.pointer()));
        assert!(context.contains_known(&goal));
        let proof_facts = crate::kernel::proof::ProofFacts::from_ordered(&facts);
        assert!(
            crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                &goal,
                &[],
                &proof_facts
            )
            .is_ok()
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../scaling_tests/kernel/pointer_designations/tests.rs");
}
