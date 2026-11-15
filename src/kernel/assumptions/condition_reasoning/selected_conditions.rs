use super::*;
use crate::kernel::MachineOperandView as V;
use crate::kernel::binary_node;
use crate::kernel::cast_term;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{bits32_constant, constant_u32};

/// Only these operand families are compared up to memory resolution.
/// Every other condition is matched by its exact fact identity. The index
/// and the matcher share this classification so an exact-only refusal cannot
/// silently omit a family that the matcher knows how to relate.
enum MemoryMatchOperands<'a> {
    Words(
        MachineIntegerType,
        CompareRelation,
        &'a MachineTerm,
        &'a MachineTerm,
    ),
    Offsets(&'a PointerOffsetTerm, &'a PointerOffsetTerm),
    Exact,
}

fn memory_match_operands(condition: &ConditionTerm) -> MemoryMatchOperands<'_> {
    match condition {
        ConditionTerm::Compare {
            format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
            relation,
            left,
            right,
        } => MemoryMatchOperands::Words(*format, *relation, left, right),
        ConditionTerm::PointerOffsetEqual(left, right) => MemoryMatchOperands::Offsets(left, right),
        _ => MemoryMatchOperands::Exact,
    }
}

impl PureFactContext {
    pub(in crate::kernel) fn has_matching_condition_fact_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.indexed_matching_condition_fact_for_memory_resolution(condition, value)
            .unwrap_or(false)
    }

    /// Look for a memory-equivalent fact using the supported indexed routes.
    /// `None` means the query falls outside those routes, not that its
    /// negation holds. The caller deliberately declines instead of searching
    /// the whole ambient context. Explicit proof steps can establish the
    /// required spelling before a call.
    ///
    /// Exact identities and syntactic symmetries use direct lookups. Compound
    /// queries check a singleton under their canonical key. Atomic truth uses
    /// the maintained equality graph. A missing key declines; it never scans
    /// the family's open facts. Every candidate still passes the memory matcher's checks.
    fn indexed_matching_condition_fact_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> Option<bool> {
        // One comparison of two scalar atoms is fixed explicit input. Its
        // checked cost stays distinct from the search that may invoke it.
        // Compound terms and offsets need their own input-size measure.
        let scalar_atom = |term: &MachineTerm| match term {
            bits32_constant!(_) => true,
            MachineTerm::Variable(variable) => {
                crate::kernel::eval::registered_load_for_variable(variable).is_none()
            }
            _ => false,
        };
        let _checking = matches!(memory_match_operands(condition),
            MemoryMatchOperands::Words(_, _, left, right) if scalar_atom(left) && scalar_atom(right))
            .then(|| crate::instrumentation::CheckingWorkScope::new("match atomic memory condition", 1));
        // An exact hit needs no operand reasoning, even for loads and sums.
        // For exact-only kinds a miss is conclusive too: no other condition
        // can match under `condition_matches_after_memory_resolution`.
        crate::instrumentation::record_deterministic_work(1);
        let exact = self.condition_facts.get(condition) == Some(&value);
        if exact || matches!(memory_match_operands(condition), MemoryMatchOperands::Exact) {
            return Some(exact);
        }
        // The matcher also accepts a fixed number of syntactic symmetries.
        // Probe those exact keys before resolving operands or scanning facts.
        let lookup = |candidate: ConditionTerm| {
            crate::instrumentation::record_deterministic_work(1);
            self.condition_facts.get(&candidate) == Some(&value)
        };
        let symmetric = match memory_match_operands(condition) {
            MemoryMatchOperands::Words(format, relation, left, right) => {
                use CompareRelation::*;
                let reversed = match relation {
                    Equal => Equal,
                    LessThan => GreaterThan,
                    LessEqual => GreaterEqual,
                    GreaterThan => LessThan,
                    GreaterEqual => LessEqual,
                };
                // Condition identity already ignores signedness for 32-bit
                // equality; order comparisons retain their exact carrier.
                ConditionTerm::Compare {
                    format,
                    relation: reversed,
                    left: Box::new(right.clone()),
                    right: Box::new(left.clone()),
                }
            }
            MemoryMatchOperands::Offsets(left, right) => {
                ConditionTerm::PointerOffsetEqual(Box::new(right.clone()), Box::new(left.clone()))
            }
            MemoryMatchOperands::Exact => unreachable!("exact-only kinds returned above"),
        };
        if lookup(symmetric.clone()) {
            return Some(true);
        }
        // Predicate truth is maintained with the equality classes. Asking
        // that index does not enumerate the operands' alternative spellings.
        let atom_order = matches!(memory_match_operands(condition),
            MemoryMatchOperands::Words(_, relation, left, right)
                if relation != CompareRelation::Equal && scalar_atom(left) && scalar_atom(right));
        if atom_order
            && (self.equality_graph.knows_condition(condition, value)
                || self.equality_graph.knows_condition(&symmetric, value))
        {
            return Some(true);
        }
        let key = crate::kernel::assumptions::condition_match_key(condition)?;
        crate::instrumentation::record_deterministic_work(1);
        // A shape bucket is not an explicit premise list. Only its unique
        // source can be checked implicitly; an ambiguous bucket needs a
        // selected premise. Keep the memory matcher's state checks.
        Some(
            self.condition_facts_by_sides
                .get(&key)
                .is_some_and(|facts| {
                    facts.len() == 1
                        && facts.iter().any(|(fact, fact_value)| {
                            crate::instrumentation::record_deterministic_work(1);
                            *fact_value == value
                                && self.condition_matches_after_memory_resolution(fact, condition)
                        })
                }),
        )
    }

    pub(in crate::kernel) fn has_anchored_bitvector_equality_fact_for_memory_resolution(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        let target = ConditionTerm::equal(left.clone(), right.clone());
        if self.exact_condition_value(&target) == Some(true) {
            return true;
        }
        [left, right].into_iter().any(|endpoint| {
            self.checked_scalar_facts
                .singleton_equality(endpoint)
                .is_some_and(|fact| self.condition_matches_after_memory_resolution(fact, &target))
        })
    }

    fn condition_matches_after_memory_resolution(
        &self,
        fact: &ConditionTerm,
        target: &ConditionTerm,
    ) -> bool {
        if fact == target {
            return true;
        }
        use MemoryMatchOperands::{Exact, Offsets, Words};
        match (memory_match_operands(fact), memory_match_operands(target)) {
            (
                Words(_, CompareRelation::Equal, fl, fr),
                Words(_, CompareRelation::Equal, tl, tr),
            ) => {
                bitvector_terms_proven_equal_for_memory_resolution(fl, tl, self)
                    && bitvector_terms_proven_equal_for_memory_resolution(fr, tr, self)
                    || bitvector_terms_proven_equal_for_memory_resolution(fl, tr, self)
                        && bitvector_terms_proven_equal_for_memory_resolution(fr, tl, self)
            }
            (Offsets(fl, fr), Offsets(tl, tr)) => {
                pointer_offsets_proven_equal_for_memory_resolution(fl, tl, self)
                    && pointer_offsets_proven_equal_for_memory_resolution(fr, tr, self)
                    || pointer_offsets_proven_equal_for_memory_resolution(fl, tr, self)
                        && pointer_offsets_proven_equal_for_memory_resolution(fr, tl, self)
            }
            (Words(ff, frel, fl, fr), Words(tf, trel, tl, tr)) if ff == tf => {
                if frel == trel {
                    bitvector_terms_proven_equal_for_memory_resolution(fl, tl, self)
                        && bitvector_terms_proven_equal_for_memory_resolution(fr, tr, self)
                } else if matches!(
                    (frel, trel),
                    (CompareRelation::LessThan, CompareRelation::GreaterThan)
                        | (CompareRelation::GreaterThan, CompareRelation::LessThan)
                        | (CompareRelation::LessEqual, CompareRelation::GreaterEqual)
                        | (CompareRelation::GreaterEqual, CompareRelation::LessEqual)
                ) {
                    bitvector_terms_proven_equal_for_memory_resolution(fl, tr, self)
                        && bitvector_terms_proven_equal_for_memory_resolution(fr, tl, self)
                } else {
                    false
                }
            }
            (Exact, _) | (_, Exact) => false,
            _ => false,
        }
    }

    /// The unique constant this term resolves to through established equality
    /// facts, if any. Does not search other states for a constant.
    pub(in crate::kernel) fn known_signed_constant_after_normalization(
        &self,
        term: &MachineTerm,
    ) -> Option<i64> {
        self.signed_constant_after_equality_normalization(term)
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!(
        "../../../scaling_tests/kernel/assumptions/condition_reasoning/selected_conditions.rs"
    );
}

#[cfg(test)]
mod memory_condition_match_tests {
    use super::*;

    fn comparison(
        format: MachineIntegerType,
        relation: CompareRelation,
        left: u64,
        right: u64,
    ) -> ConditionTerm {
        ConditionTerm::Compare {
            format,
            relation,
            left: Box::new(MachineTerm::Variable(Variable(left))),
            right: Box::new(MachineTerm::Variable(Variable(right))),
        }
    }

    #[test]
    fn memory_condition_matching_keeps_reversed_orders_and_carriers() {
        use CompareRelation::*;
        use MachineIntegerType::*;
        let _session = crate::kernel::VerificationSession::enter();
        for format in [Int32, UInt32] {
            for (relation, reversed) in [
                (LessThan, GreaterThan),
                (LessEqual, GreaterEqual),
                (GreaterThan, LessThan),
                (GreaterEqual, LessEqual),
            ] {
                let context = PureFactContext::new()
                    .assume_condition(comparison(Int32, Equal, 960_000, 960_002), true)
                    .assume_condition(comparison(Int32, Equal, 960_001, 960_003), true)
                    .assume_condition(comparison(format, relation, 960_000, 960_001), true);
                assert!(context.has_matching_condition_fact_for_memory_resolution(
                    &comparison(format, reversed, 960_003, 960_002),
                    true
                ));
                let other_format = if format == Int32 { UInt32 } else { Int32 };
                assert!(!context.has_matching_condition_fact_for_memory_resolution(
                    &comparison(other_format, reversed, 960_003, 960_002),
                    true
                ));
            }
        }
        let words = PureFactContext::new()
            .assume_condition(comparison(Int32, Equal, 960_004, 960_005), true);
        assert!(words.has_matching_condition_fact_for_memory_resolution(
            &comparison(UInt32, Equal, 960_005, 960_004),
            true
        ));
        let offsets = ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::Variable(Variable(960_006)),
            PointerOffsetTerm::Variable(Variable(960_007)),
        );
        let reversed = ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::Variable(Variable(960_007)),
            PointerOffsetTerm::Variable(Variable(960_006)),
        );
        assert!(
            PureFactContext::new()
                .assume_condition(offsets, true)
                .has_matching_condition_fact_for_memory_resolution(&reversed, true)
        );
    }

    #[test]
    fn unsigned_atom_memory_conditions_use_indexed_word_identities() {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| MachineTerm::Variable(Variable(id));
        let sum = MachineTerm::add(var(996_000), var(996_001));
        let base = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(var(996_001), 0u32.into()), true);
        let goal = ConditionTerm::unsigned_less_than(var(996_000), var(996_002));
        for value in [false, true] {
            let source = ConditionTerm::unsigned_less_than(sum.clone(), var(996_002));
            let held = base.clone().assume_condition(source.clone(), value);
            assert_eq!(
                held.indexed_matching_condition_fact_for_memory_resolution(&goal, value),
                Some(true)
            );
            assert!(held.has_matching_condition_fact_for_memory_resolution(&goal, value));
            // Without the zero-addend equality, the predicate cannot transfer.
            let no_zero = PureFactContext::new().assume_condition(source.clone(), value);
            assert!(!no_zero.has_matching_condition_fact_for_memory_resolution(&goal, value));
            assert!(!held.has_matching_condition_fact_for_memory_resolution(&goal, !value));
            let named = held.clone().assume_condition(goal.clone(), value);
            assert!(named.has_matching_condition_fact_for_memory_resolution(&goal, value));
            assert!(!base.has_matching_condition_fact_for_memory_resolution(&goal, value));
            let signed = base.clone().assume_condition(
                ConditionTerm::signed_less_than(sum.clone(), var(996_002)),
                value,
            );
            assert!(!signed.has_matching_condition_fact_for_memory_resolution(&goal, value));
        }
    }

    #[test]
    fn compound_memory_condition_candidates_preserve_states() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = Memory::new();
        let pointer = Pointer::symbolic(Variable(999_000));
        let load = |memory: &Memory| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        let raw = load(&memory);
        let named =
            MachineTerm::Variable(crate::kernel::eval::load_variable_for_term(&raw).unwrap().0);
        let changed = memory
            .clone()
            .store(pointer.clone(), ProgramValue::Int32(9u32.into()));
        let condition = |kind, term| {
            let left = MachineTerm::add(term, 1u32.into());
            let right = MachineTerm::Variable(Variable(999_001));
            match kind {
                0 => ConditionTerm::signed_less_than(left, right),
                1 => ConditionTerm::unsigned_less_than(left, right),
                _ => ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(left, 4),
                    PointerOffsetTerm::scale_int32(right, 4),
                ),
            }
        };
        for kind in 0..3 {
            let source = condition(kind, named.clone());
            let goal = condition(kind, raw.clone());
            for value in [false, true] {
                let held = PureFactContext::new().assume_condition(source.clone(), value);
                assert_eq!(
                    held.indexed_matching_condition_fact_for_memory_resolution(&goal, value),
                    Some(true)
                );
                assert!(held.has_matching_condition_fact_for_memory_resolution(&goal, value));
                assert!(!held.has_matching_condition_fact_for_memory_resolution(&goal, !value));
                assert!(!held.has_matching_condition_fact_for_memory_resolution(
                    &condition(kind, load(&changed)),
                    value
                ));
            }
        }
    }

    #[test]
    fn compound_memory_condition_miss_requires_the_explicit_spelling() {
        let _session = crate::kernel::VerificationSession::enter();
        let var = |id| MachineTerm::Variable(Variable(id));
        let condition = |kind, id| {
            let left = MachineTerm::add(var(id), 1u32.into());
            let right = var(999_012);
            match kind {
                0 => ConditionTerm::signed_less_than(left, right),
                1 => ConditionTerm::unsigned_less_than(left, right),
                _ => ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(left, 4),
                    PointerOffsetTerm::scale_int32(right, 4),
                ),
            }
        };
        for kind in 0..3 {
            let source = condition(kind, 999_010);
            let goal = condition(kind, 999_011);
            for value in [false, true] {
                let facts = PureFactContext::new()
                    .assume_condition(ConditionTerm::equal(var(999_010), var(999_011)), true)
                    .assume_condition(source.clone(), value);
                // The old ambient scan found this equivalent spelling. The
                // fast path deliberately declines; selected-premise reasoning
                // can still establish it before the call needs the exact fact.
                assert!(facts.condition_matches_after_memory_resolution(&source, &goal));
                assert!(
                    facts
                        .selected_for_test()
                        .proves_condition_from_selected_facts(&goal, value)
                );
                assert!(!facts.has_matching_condition_fact_for_memory_resolution(&goal, value));
                let explicit = facts.assume_condition(goal.clone(), value);
                assert!(explicit.has_matching_condition_fact_for_memory_resolution(&goal, value));
                assert!(!explicit.has_matching_condition_fact_for_memory_resolution(&goal, !value));
            }
        }
    }

    #[test]
    fn exact_memory_condition_matching_respects_truth() {
        let _session = crate::kernel::VerificationSession::enter();
        let goal = comparison(
            MachineIntegerType::UInt64,
            CompareRelation::LessThan,
            960_010,
            960_011,
        );
        let parent = PureFactContext::new().assume_condition(goal.clone(), true);
        assert!(parent.has_matching_condition_fact_for_memory_resolution(&goal, true));
        assert!(!parent.has_matching_condition_fact_for_memory_resolution(&goal, false));
        let child = PureFactContext::new().assume_condition(goal.clone(), false);
        assert!(child.has_matching_condition_fact_for_memory_resolution(&goal, false));
        assert!(!child.has_matching_condition_fact_for_memory_resolution(&goal, true));
        let reversed = comparison(
            MachineIntegerType::UInt64,
            CompareRelation::GreaterThan,
            960_011,
            960_010,
        );
        assert!(
            !parent.has_matching_condition_fact_for_memory_resolution(&reversed, true),
            "this matcher only transports 32-bit comparisons and offsets; wider conditions need exact identity"
        );
    }
}

impl SelectedFacts<'_> {
    pub(crate) fn decide_selected_condition(&self, condition: &ConditionTerm) -> Option<bool> {
        if let Some(value) = self.known_condition_value(condition) {
            return Some(value);
        }
        if let Some(value) = self
            .decide_small_uint64_index_order(condition)
            .or_else(|| self.decide_indexed_greater_equal(condition))
            .or_else(|| self.decide_masked_order(condition))
            .or_else(|| self.decide_widened_sum_bound(condition))
        {
            return Some(value);
        }
        if let Some(value) = self.decide_exact_signed_constant_order(condition) {
            return Some(value);
        }

        if matches!(condition, ConditionTerm::PointerValueEqual(..)) {
            return self.decide(condition);
        }
        match condition {
            ConditionTerm::AlgebraicEqual(left, right) => {
                self.decide_algebraic_equality(left, right)
            }
            ConditionTerm::Constant(value) => Some(*value),
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right) if self.pointers_known_equal(left, right) => {
                Some(true)
            }
            ConditionTerm::PointerEqual(left, right) if left.blocks_proven_distinct(right) => {
                Some(false)
            }
            ConditionTerm::PointerEqual(left, right) if left.block == right.block => self
                .decide_selected_condition(&ConditionTerm::pointer_offset_equal(
                    left.offset.clone(),
                    right.offset.clone(),
                )),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } if ConditionTerm::address_equality_as_pointer_equality(left, right).is_some() => {
                ConditionTerm::address_equality_as_pointer_equality(left, right)
                    .and_then(|condition| self.decide_selected_condition(&condition))
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: _,
                right: _,
            } if condition.as_pointer_alignment().is_some() => {
                let (pointer, alignment) = condition.as_pointer_alignment()?;
                self.decide_pointer_alignment(pointer, alignment)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            } => {
                if self.uint64_values_known_equal(left, right) {
                    return Some(true);
                }
                match (
                    self.wide_constant_from_equalities(left),
                    self.wide_constant_from_equalities(right),
                ) {
                    (Some(left), Some(right)) => Some(left == right),
                    _ => self.decide_uint64_equality_extras(left, right),
                }
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                if self.equality_graph.are_offsets_equal(left, right)
                    || pointer_offsets_proven_equal_for_memory_resolution(left, right, self)
                {
                    Some(true)
                } else {
                    match (left.as_ref().as_const(), right.as_ref().as_const()) {
                        (Some(left), Some(right)) => Some(left == right),
                        _ => None,
                    }
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } => {
                let narrowed_constant = |term: &MachineTerm| match term {
                    cast_term!(UInt32From64, wide) => self
                        .wide_constant_from_equalities(wide)
                        .map(|bits| bits as u32),
                    bits32_constant!(bits) => Some(constant_u32(*bits)),
                    _ => None,
                };
                if let (Some(left), Some(right)) =
                    (narrowed_constant(left), narrowed_constant(right))
                {
                    return Some(left == right);
                }
                if bitvector_terms_proven_equal_for_memory_resolution(left, right, self)
                    || self.proves_condition_from_selected_facts(condition, true)
                {
                    Some(true)
                } else if bitvector_same_base_nonzero_const_offset(left, right) {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if self.selected_increment_preserves_order(left, right) => Some(true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if left.as_ref().add_const_base(1).is_some_and(|base| {
                self.exact_condition_value(&ConditionTerm::signed_less_than(
                    base,
                    right.as_ref().clone(),
                )) == Some(true)
            }) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if self.exact_condition_value(&ConditionTerm::signed_less_than(
                left.as_ref().clone(),
                binary_node!(
                    Int32,
                    Add,
                    Box::new(right.as_ref().clone()),
                    Box::new(MachineTerm::constant(1)),
                ),
            )) == Some(true)
                && self.has_exact_bitvector_inequality_after_cancellation(left, right) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if self
                .selected_positive_offset_is_proven_above(V::Legacy(left), V::Legacy(right)) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } if right.as_ref() == &MachineTerm::constant(0)
                && left.as_ref().subtract_one_base().is_some_and(|base| {
                    self.exact_condition_value(&ConditionTerm::signed_greater_than(
                        base,
                        MachineTerm::constant(0),
                    )) == Some(true)
                }) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } if left.as_ref() == &MachineTerm::constant(0)
                && right.as_ref().subtract_one_base().is_some_and(|base| {
                    self.exact_condition_value(&ConditionTerm::signed_greater_than(
                        base,
                        MachineTerm::constant(0),
                    )) == Some(true)
                }) =>
            {
                Some(true)
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } if left.as_ref().subtract_one_base().is_some_and(|base| {
                &base == right.as_ref()
                    && self.exact_condition_value(&ConditionTerm::signed_greater_than(
                        base,
                        MachineTerm::constant(0),
                    )) == Some(true)
            }) =>
            {
                Some(true)
            }
            _ => {
                if self.proves_condition_from_selected_facts(condition, true) {
                    return Some(true);
                }
                if self.proves_condition_from_selected_facts(condition, false) {
                    return Some(false);
                }
                // This stronger normalization is tactic-local. Keep its atomic
                // checks structural: calling the general condition solver here
                // can recurse through fact transport and memory alias solving.
                if let Some((left, right, strict)) = retained_order_fact(condition, true)
                    && self.has_selected_order_path(
                        left.operand_view(),
                        right.operand_view(),
                        strict,
                    )
                {
                    return Some(true);
                }
                if let Some((left, right, strict)) = retained_order_fact(condition, false)
                    && self.has_selected_order_path(
                        left.operand_view(),
                        right.operand_view(),
                        strict,
                    )
                {
                    return Some(false);
                }
                if order_view_at_format(condition, true, MachineIntegerType::Int32).is_some() {
                    PureFactContext::decide_intrinsically(condition)
                } else {
                    self.decide(condition)
                }
            }
        }
    }

    fn selected_increment_preserves_order(
        &self,
        incremented_lower: &MachineTerm,
        incremented_value: &MachineTerm,
    ) -> bool {
        let order_facts = self.condition_order_facts();
        order_facts.iter().any(|(lower, value, strict)| {
            if *strict
                || !self.selected_successor_matches(lower.operand_view(), incremented_lower)
                || !self.selected_successor_matches(value.operand_view(), incremented_value)
            {
                return false;
            }
            order_facts
                .iter()
                .any(|(strict_value, _, strict)| *strict && strict_value == value)
        })
    }

    fn selected_successor_matches(&self, lower: V<'_>, incremented: &MachineTerm) -> bool {
        if let V::Legacy(lower) = lower {
            return MachineTerm::add(lower.clone(), MachineTerm::constant(1)) == *incremented;
        }
        let V::Shared(lower) = lower else {
            unreachable!()
        };
        let one = crate::kernel::KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(1));
        let sum = crate::kernel::KernelTerm::machine_binary_shared(
            MachineIntegerType::Int32,
            crate::kernel::MachineBinaryOp::Add,
            [lower.clone(), one],
        );
        let sum = self.equality_graph.checking_word32_root(&sum, |_| None);
        use super::super::checked_scalar_facts::ScalarOperandKey as Key;
        Key::for_format(MachineIntegerType::Int32, V::Shared(&sum))
            == Key::for_format(MachineIntegerType::Int32, V::Legacy(incremented))
    }

    fn has_exact_bitvector_inequality_after_cancellation(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        self.exact_condition_value(&ConditionTerm::equal(left.clone(), right.clone()))
            == Some(false)
            || self
                .condition_facts
                .scan_explicit_input()
                .any(|(condition, value)| {
                    if *value {
                        return false;
                    }
                    let ConditionTerm::Compare {
                        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        left: fact_left,
                        right: fact_right,
                    } = condition
                    else {
                        return false;
                    };
                    let Some((fact_left, fact_right)) =
                        bitvector_equality_after_additive_cancellation(fact_left, fact_right)
                    else {
                        return false;
                    };
                    (&fact_left == left && &fact_right == right)
                        || (&fact_left == right && &fact_right == left)
                })
    }

    fn decide_selected_condition_without_propositions(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        if let Some(value) = self.known_condition_value(condition) {
            return Some(value);
        }
        if let Some(value) = self
            .decide_small_uint64_index_order(condition)
            .or_else(|| self.decide_indexed_greater_equal(condition))
            .or_else(|| self.decide_masked_order(condition))
            .or_else(|| self.decide_widened_sum_bound(condition))
        {
            return Some(value);
        }
        if let Some(value) = self.decide_exact_signed_constant_order(condition) {
            return Some(value);
        }
        if let ConditionTerm::Constant(value) = condition {
            return Some(*value);
        }
        if let ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } = condition
            && self.exact_condition_value(&ConditionTerm::signed_less_than(
                left.as_ref().clone(),
                binary_node!(
                    Int32,
                    Add,
                    Box::new(right.as_ref().clone()),
                    Box::new(MachineTerm::constant(1)),
                ),
            )) == Some(true)
            && self.has_exact_bitvector_inequality_after_cancellation(left, right)
        {
            return Some(true);
        }
        if let Some((left, right, strict)) = retained_order_fact(condition, true)
            && self.has_selected_order_path(left.operand_view(), right.operand_view(), strict)
        {
            return Some(true);
        }
        if let Some((left, right, strict)) = retained_order_fact(condition, false)
            && self.has_selected_order_path(left.operand_view(), right.operand_view(), strict)
        {
            return Some(false);
        }
        PureFactContext::decide_intrinsically(condition)
    }

    fn proves_condition_from_selected_facts(&self, condition: &ConditionTerm, value: bool) -> bool {
        let Some(_proof) = SelectedFactReasoningGuard::enter(condition, value) else {
            return false;
        };
        // A slow-part scan: only `solve` reaches this, and a certificate
        // runs it again over the step's retained premises alone.
        self.condition_facts
            .scan_explicit_input()
            .any(|(fact, fact_value)| {
                *fact_value == value
                    && self.condition_matches_after_memory_resolution(fact, condition)
            })
            || self.prop_facts.scan_explicit_input().any(|proposition| {
                self.selected_proposition_proves_condition(proposition, condition, value)
            })
    }

    fn selected_proposition_proves_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        match proposition {
            Proposition::ConditionIs(fact, fact_value) => {
                *fact_value == value
                    && self.condition_matches_after_memory_resolution(fact, condition)
            }
            Proposition::And(left, right) => {
                self.selected_proposition_proves_condition(left, condition, value)
                    || self.selected_proposition_proves_condition(right, condition, value)
            }
            Proposition::Implies(left, right) => {
                // Reject implications whose conclusion cannot establish the
                // target before proving their (potentially expensive)
                // antecedent against the whole context.
                self.selected_proposition_proves_condition(right, condition, value)
                    && self.proves_selected_proposition(left)
            }
            Proposition::ForAll { body, .. } => {
                self.selected_proposition_proves_condition(body, condition, value)
                    || self
                        .forall_instantiations_for_condition(proposition, condition)
                        .iter()
                        .any(|instance| {
                            self.selected_proposition_proves_condition(instance, condition, value)
                        })
            }
            _ => false,
        }
    }

    fn proves_selected_proposition(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide_selected_condition_without_propositions(condition) == Some(*value)
            }
            Proposition::And(left, right) => {
                self.proves_selected_proposition(left) && self.proves_selected_proposition(right)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide_selected_condition_without_propositions(condition) == Some(!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            _ => self.proves_exact(proposition),
        }
    }

    fn has_selected_order_path(&self, left: V<'_>, right: V<'_>, require_strict: bool) -> bool {
        let mut order_facts = self.condition_order_facts().as_ref().clone();
        self.collect_quantified_order_facts_for_condition(
            &crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::LessThan,
                [left, right],
            ),
            &mut order_facts,
        );
        let mut stack = vec![(retain_order_operand(left), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            if let Some(connection_strict) =
                self.selected_order_path_connection(current.operand_view(), right)
                && (!require_strict || strict_so_far || connection_strict)
            {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in order_facts.iter() {
                if let Some(connection_strict) = self.selected_order_path_connection(
                    current.operand_view(),
                    edge_left.operand_view(),
                ) {
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || connection_strict || *edge_strict,
                    ));
                }
            }
        }
        false
    }

    fn selected_positive_offset_is_proven_above(&self, base: V<'_>, term: V<'_>) -> bool {
        let Some((term_base, addend)) = term.int32_add_const_parts() else {
            return false;
        };
        if !self.selected_bitvector_terms_equal(term_base, base)
            || nonnegative_int32_value(addend).is_none_or(|value| value <= 0)
        {
            return false;
        }
        // A selected strict upper bound makes the existing +1 rule safe.
        addend == 1
            && self
                .condition_facts
                .scan_explicit_input()
                .any(|(condition, value)| {
                    *value
                        && order_view_at_format(condition, true, MachineIntegerType::Int32)
                            .is_some_and(|view| {
                                view.relation == crate::kernel::machine_integer::Relation::Less
                                    && self.selected_bitvector_terms_equal(
                                        view.operands[0].operand_view(),
                                        base,
                                    )
                            })
                })
    }

    fn selected_order_path_connection(&self, left: V<'_>, right: V<'_>) -> Option<bool> {
        if self.selected_bitvector_terms_equal(left, right) {
            return Some(false);
        }
        if self.selected_positive_offset_is_proven_above(left, right) {
            return Some(true);
        }
        let left = self.known_signed_constant_after_normalization_view(left)?;
        let right = self.known_signed_constant_after_normalization_view(right)?;
        (left <= right).then_some(left < right)
    }

    fn selected_bitvector_terms_equal(&self, left: V<'_>, right: V<'_>) -> bool {
        if self.bitvector_terms_equal_for_transport_views(left, right) {
            return true;
        }
        self.condition_facts
            .scan_explicit_input()
            .any(|(condition, value)| {
                if !*value {
                    return false;
                }
                let Some(view) =
                    crate::kernel::machine_integer::comparison::structural_native_comparison_view(
                        condition, true,
                    )
                    .filter(|view| {
                        matches!(
                            view.format,
                            MachineIntegerType::Int32 | MachineIntegerType::UInt32
                        ) && view.relation == crate::kernel::machine_integer::Relation::Equal
                    })
                else {
                    return false;
                };
                let [a, b] = view.operands.each_ref().map(|p| p.operand_view());
                self.bitvector_terms_equal_for_transport_views(left, a)
                    && self.bitvector_terms_equal_for_transport_views(right, b)
                    || self.bitvector_terms_equal_for_transport_views(left, b)
                        && self.bitvector_terms_equal_for_transport_views(right, a)
            })
    }
}

#[cfg(test)]
mod checking_attribution_tests {
    use super::*;
    use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};

    #[test]
    fn atomic_condition_check_and_search_exhaustion_have_distinct_reports() {
        for expensive_check in [true, false] {
            let _session = crate::kernel::VerificationSession::enter();
            instrumentation::with_tactic_work_limits(
                TacticWorkLimits {
                    simple: if expensive_check { 1 } else { 10 },
                    smart: 20,
                    control: 20,
                },
                || {
                    instrumentation::collect(|| {
                        let tactic = TacticEvent {
                            source_tactic_path: None,
                            claim: "condition_budget".into(),
                            tactic_index: 0,
                            tactic_name: "solve".into(),
                            class: "smart".into(),
                            statement_index: 3,
                            source_index: 4,
                        };
                        instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                        let context = PureFactContext::new();
                        let query = ConditionTerm::signed_less_than(
                            MachineTerm::Variable(Variable(945_000)),
                            MachineTerm::Variable(Variable(945_001)),
                        );
                        let (_, work) = instrumentation::measure_deterministic_work(|| {
                            for _ in 0..if expensive_check { 1 } else { 8 } {
                                assert!(
                                    !context.has_matching_condition_fact_for_memory_resolution(
                                        &query, true
                                    )
                                );
                            }
                        });
                        let message = instrumentation::deadline_context();
                        if expensive_check {
                            assert_eq!(work, 3);
                            assert!(
                                message.contains("match atomic memory condition")
                                    && message.contains("engine performance defect"),
                                "{message}"
                            );
                            assert!(
                                message.contains("solve") && message.contains("source tactic 4"),
                                "{message}"
                            );
                        } else {
                            assert_eq!(work, 24);
                            assert!(message.contains("smart search is heuristic"), "{message}");
                            assert!(!message.contains("engine performance defect"), "{message}");
                        }
                        instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                    });
                },
            );
        }
    }
}

#[cfg(test)]
mod retained_order_tests {
    use super::*;
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};

    fn root(id: u64) -> KernelTerm {
        let x = KernelTerm::variable(
            KernelType::Program(MachineIntegerType::Int32.program_type()),
            Variable(id),
        );
        KernelTerm::machine_binary_shared(
            MachineIntegerType::Int32,
            MachineBinaryOp::Multiply,
            [x.clone(), x],
        )
    }
    fn bound(a: &KernelTerm, b: &KernelTerm, strict: bool) -> ConditionTerm {
        condition_for_operand_views(
            MachineIntegerType::Int32,
            if strict {
                CompareRelation::LessThan
            } else {
                CompareRelation::LessEqual
            },
            [V::Shared(a), V::Shared(b)],
        )
    }
    #[test]
    fn selected_shared_paths_preserve_strictness_and_branch_scope_without_export() {
        let _session = crate::kernel::VerificationSession::enter();
        let [a, b, c] = [root(993501), root(993502), root(993503)];
        let exports = KernelTermExport::machine_export_count();
        let parent = PureFactContext::new().assume_condition(bound(&a, &b, true), true);
        let child = parent.clone().assume_condition(bound(&b, &c, false), true);
        assert!(child.selected_for_test().has_selected_order_path(
            V::Shared(&a),
            V::Shared(&c),
            true
        ));
        assert!(!child.selected_for_test().has_selected_order_path(
            V::Shared(&c),
            V::Shared(&a),
            false
        ));
        assert!(!parent.selected_for_test().has_selected_order_path(
            V::Shared(&a),
            V::Shared(&c),
            false
        ));
        let weak = PureFactContext::new()
            .assume_condition(bound(&a, &b, false), true)
            .assume_condition(bound(&b, &c, false), true);
        assert!(weak.selected_for_test().has_selected_order_path(
            V::Shared(&a),
            V::Shared(&c),
            false
        ));
        assert!(!weak.selected_for_test().has_selected_order_path(
            V::Shared(&a),
            V::Shared(&c),
            true
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn derived_shared_bounds_require_the_selected_guard() {
        let _session = crate::kernel::VerificationSession::enter();
        let [a, b] = [root(993511), root(993512)];
        let guard = ConditionTerm::equal(
            MachineTerm::Variable(Variable(993513)),
            MachineTerm::constant(7),
        );
        let source = Proposition::Implies(
            Box::new(Proposition::ConditionIs(guard.clone(), true)),
            Box::new(Proposition::ConditionIs(bound(&a, &b, true), true)),
        );
        let empty = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let mut facts = Vec::new();
        empty.collect_derived_order_facts_from_proposition(&source, &mut facts);
        assert!(facts.is_empty());
        let allowed = empty.clone().assume_condition(guard, true);
        allowed.collect_derived_order_facts_from_proposition(&source, &mut facts);
        assert_eq!(facts.len(), 1);
        assert_eq!(
            facts[0],
            retained_order_fact(&bound(&a, &b, true), true).unwrap()
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
    #[test]
    fn finite_quantified_shared_bounds_keep_the_instantiated_operands() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let [a, b] = [root(993541), root(993542)];
        let k = Variable(993543);
        let binder = KernelTerm::variable(KernelType::Program(ty.program_type()), k);
        let body = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [a.clone(), binder]);
        let guard = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    MachineTerm::constant(0),
                    MachineTerm::Variable(k),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(MachineTerm::Variable(k), MachineTerm::constant(2)),
                true,
            )),
        );
        let source = Proposition::ForAll {
            name: Default::default(),
            var: k,
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::Implies(
                Box::new(guard),
                Box::new(Proposition::ConditionIs(bound(&body, &b, false), true)),
            )),
        };
        let context = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        let mut facts = Vec::new();
        context.collect_finite_forall_order_facts(&source, &mut facts);
        assert_eq!(facts.len(), 2);
        for (index, (left, right, strict)) in facts.iter().enumerate() {
            let value = crate::kernel::KernelTermImport::default()
                .machine(ty, &MachineTerm::constant(index as u32));
            let expected =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [a.clone(), value]);
            assert!(!strict);
            assert!(context.bitvector_terms_equal_for_transport_views(
                left.operand_view(),
                V::Shared(&expected)
            ));
            assert!(
                context
                    .bitvector_terms_equal_for_transport_views(right.operand_view(), V::Shared(&b))
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
