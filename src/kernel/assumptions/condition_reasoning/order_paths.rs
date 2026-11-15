use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{MachineCastSpelling, MachineTerm};
use crate::kernel::{bits32_constant, constant_u32};
use crate::kernel::{constant_u64, uint64_constant};

impl PureFactContext {
    #[cfg(test)]
    /// Whether one recorded strict order fact separates `left` from `right`
    /// directly (`left < right` or `right < left`, under either term or its
    /// canonical alias). This is an indexed lookup only — no derivation, no
    /// fuel — so an assumption-free walk such as memory-derivation naming can
    /// refute an offset equality from a recorded bound without reasoning.
    pub(in crate::kernel) fn direct_strict_order_recorded(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> bool {
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let key = |view| Key::for_format(MachineIntegerType::Int32, view);
        let left_key = key(MachineOperandView::Legacy(left));
        let right_key = key(MachineOperandView::Legacy(right));
        let separated = |endpoint: &MachineTerm| {
            self.signed_order_bounds
                .get(endpoint)
                .is_some_and(|bounds| {
                    bounds.operand_keys().any(|(lower, upper, strict, _)| {
                        strict
                            && ((key(lower) == left_key && key(upper) == right_key)
                                || (key(lower) == right_key && key(upper) == left_key))
                    })
                })
        };
        separated(left)
            || separated(right)
            || separated(&crate::kernel::eval::canonical_term(left))
            || separated(&crate::kernel::eval::canonical_term(right))
    }

    pub(in crate::kernel) fn decide_from_order_facts(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        if let Some(result) = self.decide_from_variable_chain(condition) {
            return Some(result);
        }
        if let Some(value) = self.decide_unsigned_small_bound(condition) {
            return Some(value);
        }
        if let Some(value) = self.decide_from_order_rules(condition) {
            return Some(value);
        }
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let view = comparison_view(condition, true)?;
        if view.format != MachineIntegerType::Int32 {
            return None;
        }
        let strict = match view.relation {
            Relation::Less => true,
            Relation::LessEqual => false,
            _ => return None,
        };
        let [lower, upper] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        self.decide_successor_order_views(lower, upper, strict)
    }

    fn decide_successor_order_views(
        &self,
        lower: MachineOperandView<'_>,
        upper: MachineOperandView<'_>,
        strict: bool,
    ) -> Option<bool> {
        let format = MachineIntegerType::Int32;
        if !strict
            && let Some(base) = lower.int32_add_const_base(1)
            && self.decide_written_operand_comparison(
                format,
                CompareRelation::LessThan,
                base,
                upper,
            ) == Some(true)
        {
            return Some(true);
        }
        if let Some(constant) = lower.word32_constant()
            && let Some(base) = upper.int32_add_const_base(1)
            && let Some(reduced) = (if strict {
                Some(constant as i32)
            } else {
                (constant as i32).checked_sub(1)
            })
        {
            let reduced = MachineTerm::constant(reduced as u32);
            let maximum = MachineTerm::constant(i32::MAX as u32);
            if self.decide_written_operand_comparison(
                format,
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(&reduced),
                base,
            ) == Some(true)
                && self.decide_written_operand_comparison(
                    format,
                    CompareRelation::LessThan,
                    base,
                    MachineOperandView::Legacy(&maximum),
                ) == Some(true)
            {
                return Some(true);
            }
        }
        // The unsigned bridge accepts only a plain variable and a literal.
        // Materialize these fixed-size atoms, never an arithmetic operand.
        let atom = |view: MachineOperandView<'_>| {
            view.literal()
                .or_else(|| view.variable().copied().map(MachineTerm::Variable))
        };
        let (Some(lower), Some(upper)) = (atom(lower), atom(upper)) else {
            return None;
        };
        self.signed_bound_from_unsigned_order(&lower, &upper, strict)
            .then_some(true)
    }

    /// Whether a signed bound between a plain variable `t` and a constant
    /// follows from a `uint32` order chain on `t`, which the difference graph
    /// composes in its unsigned domain (`t <u n`, `n <=u 4` gives `t <u 4`):
    ///
    /// * `c <= t` for `c <= 0` (or `c < t` for `c < 0`) holds when
    ///   `t <=u INT_MAX`: the sign bit of `t` is clear, so `0 <= t`.
    /// * `t <= c` for `c >= 0` (or `t < c` for `c > 0`) holds when
    ///   `t <=u c` (or `t <u c`): `t` lies in `0..=c` (or `0..c`), where the
    ///   unsigned and signed readings agree.
    ///
    /// The chain is walked over unsigned facts alone: a chain mixing
    /// `t <u n` with a signed `n < 4` does not compose here. A wrapped bound
    /// (`t <u n - 1u` with `n` possibly zero) is a different value from `n`.
    /// One difference-graph query from `t`
    /// ([`Self::difference_graph_proves`]).
    fn signed_bound_from_unsigned_order(
        &self,
        lower: &MachineTerm,
        upper: &MachineTerm,
        strict: bool,
    ) -> bool {
        let (term, target, walk_strict) = match (
            signed_bitvector_constant(lower),
            signed_bitvector_constant(upper),
        ) {
            (Some(bound), None) if (if strict { bound < 0 } else { bound <= 0 }) => {
                (upper, i32::MAX as u32, false)
            }
            (None, Some(bound)) if (if strict { bound > 0 } else { bound >= 0 }) => {
                (lower, bound as u32, strict)
            }
            _ => return false,
        };
        if !matches!(term, MachineTerm::Variable(variable)
            if !crate::kernel::eval::is_load_variable(variable))
        {
            return false;
        }
        // A walk needs an unsigned upper bound on `t`. Asked by key first,
        // so a signed question about a variable no unsigned bound names
        // costs one lookup, not the filing of the fact set the walk reads.
        let has_unsigned_bound = self
            .uint32_order_bounds
            .get(&crate::kernel::eval::canonical_term(term))
            .is_some_and(|bounds| bounds.operand_keys().any(|(_, _, _, below)| below));
        let target = MachineTerm::constant(target);
        has_unsigned_bound
            && self.difference_graph_proves(&if walk_strict {
                ConditionTerm::unsigned_less_than(term.clone(), target)
            } else {
                ConditionTerm::unsigned_less_equal(term.clone(), target)
            })
    }

    /// The existing word-equality rules over selected operand handles. Opaque
    /// native operands keep their explicit legacy rules; shared arithmetic is
    /// inspected through views and never materialized for a query.
    fn decide_word_equality_views(
        &self,
        format: MachineIntegerType,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<bool> {
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        use crate::kernel::machine_integer::Relation;
        use crate::kernel::machine_integer::comparison::{ComparisonOperand, NativeComparisonView};
        use MachineOperandView as V;
        if let (V::Legacy(a), V::Legacy(b)) = (left, right) {
            return self.decide_from_order_rules(&ConditionTerm::machine_compare(
                format,
                CompareRelation::Equal,
                a.clone(),
                b.clone(),
            ));
        }
        let written = [left, right];
        let normalized = [left, right].map(|operand| match operand {
            V::Shared(root) => Some(self.equality_graph.checking_word32_root(root, |child| {
                self.indexed_exact_int32_constant_view(V::Shared(child))
                    .map(|(value, _)| value as u32)
            })),
            V::Legacy(_) => None,
        });
        let [left, right] = std::array::from_fn(|i| {
            normalized[i]
                .as_ref()
                .map(V::Shared)
                .unwrap_or([left, right][i])
        });
        let same = |a: V<'_>, b: V<'_>| Key::for_format(format, a) == Key::for_format(format, b);
        if same(left, right) || self.word_addends_equal_views(left, right) {
            return Some(true);
        }
        let view = NativeComparisonView {
            format,
            relation: Relation::Equal,
            operands: [left, right]
                .map(|operand| ComparisonOperand::Observation(operand.retain(format))),
        };
        if let Some(cancelled) = view.cancelled_equality() {
            let (condition, truth) = cancelled.retained_condition();
            return self.decide(&condition).map(|value| value == truth);
        }
        if let Some(equal) = self.exact_signed_intervals_equal_views(left, right) {
            return Some(equal);
        }
        let held = |relation, a, b, truth| {
            self.has_written_operand_comparison(MachineIntegerType::Int32, relation, a, b, truth)
        };
        if held(CompareRelation::Equal, left, right, true)
            || held(CompareRelation::Equal, right, left, true)
            // Retain the native dispatcher's checked memory-equality rule.
            // Shared syntax lends only selected read leaves, never an exported
            // arithmetic tree or a fact-dependent lowering result.
            || left.read_source().zip(right.read_source()).is_some_and(|(left, right)| {
                self.memory_loads_proven_equal(&left, &right)
            })
            || (held(CompareRelation::LessEqual, left, right, true)
                && held(CompareRelation::GreaterEqual, left, right, true))
            || (held(CompareRelation::LessEqual, written[0], written[1], true)
                && held(CompareRelation::GreaterEqual, written[0], written[1], true))
            || self.order_facts_force_equal_views(written[0], written[1])
            || self.range_facts_force_equal_views(written[0], written[1])
            || self.scaled_word_comparison_known(format, written, true)
        {
            return Some(true);
        }
        let offset_apart = |a: V<'_>, b: V<'_>| {
            a.int32_add_const_parts().is_some_and(|(base, offset)| {
                (same(base, b) && offset != 0)
                    || b.int32_add_const_parts()
                        .is_some_and(|(other, other_offset)| {
                            same(base, other) && offset != other_offset
                        })
            })
        };
        if held(CompareRelation::Equal, left, right, false)
            || held(CompareRelation::Equal, right, left, false)
            || offset_apart(left, right)
            || offset_apart(right, left)
            || self.scaled_word_comparison_known(format, written, false)
        {
            return Some(false);
        }
        if self.decide_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessThan,
            left,
            right,
        ) == Some(true)
            || self.decide_written_operand_comparison(
                MachineIntegerType::Int32,
                CompareRelation::GreaterThan,
                left,
                right,
            ) == Some(true)
        {
            return Some(false);
        }
        self.difference_graph
            .built()
            .and_then(|graph| graph.decide_word_equality_views(written[0], written[1]))
    }

    fn scaled_word_comparison_known(
        &self,
        format: MachineIntegerType,
        operands: [MachineOperandView<'_>; 2],
        truth: bool,
    ) -> bool {
        self.observation_comparisons
            .scaled_source(format, operands, truth)
            .is_some_and(|source| {
                record_implicit_reasoning_provenance(self, source);
                true
            })
    }

    /// Match the selected sums as multisets of word classes. No ambient facts
    /// are enumerated; registration reuses the graph's retained shared nodes.
    fn word_addends_equal_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> bool {
        use crate::kernel::MachineBinaryOp as Op;
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        use MachineOperandView as V;
        let sum_format = |v: V<'_>| {
            v.binary()
                .and_then(|(ty, op, _)| (ty.format().bits() == 32 && op == Op::Add).then_some(ty))
        };
        let format = match (sum_format(left), sum_format(right)) {
            (Some(a), Some(b)) if a != b => return false,
            (Some(a), _) | (_, Some(a)) => a,
            _ => return false,
        };
        // Aligned syntax needs only its selected leaf correspondences. Reuse
        // the shared DAG walk, but check each leaf against this context's
        // existing addend authority; never cache a fact-dependent verdict in
        // the syntax correspondence table. Permuted sums still use classes
        // below, without restoring the native all-pairs search.
        if operands_equal_with_load_atoms(format, left, right, &|left, right| {
            self.bitvector_addend_terms_proven_equal(left, right)
        }) {
            return true;
        }
        let (a, ac) = retained_additive_parts(left, format);
        let (b, bc) = retained_additive_parts(right, format);
        if ac != bc {
            return false;
        }
        let a: Vec<_> = a
            .into_iter()
            .map(|(v, n)| (Key::for_format(format, v), n))
            .collect();
        let b: Vec<_> = b
            .into_iter()
            .map(|(v, n)| (Key::for_format(format, v), n))
            .collect();
        for (key, _) in a.iter().chain(&b) {
            self.equality_graph
                .scalar_normalization_class_view(key.operand_view());
        }
        let signature = |terms: Vec<(Key, num_bigint::BigUint)>| {
            let mut keys =
                std::collections::BTreeMap::<Result<u64, Key>, num_bigint::BigUint>::new();
            for (key, count) in terms {
                let class = self
                    .equality_graph
                    .scalar_normalization_class_view(key.operand_view())
                    .map(|(root, _)| Ok(root))
                    .unwrap_or(Err(key));
                *keys.entry(class).or_default() += count;
            }
            keys
        };
        signature(a) == signature(b)
    }

    fn decide_from_order_rules(&self, condition: &ConditionTerm) -> Option<bool> {
        match condition {
            ConditionTerm::PointerEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerEqual(left, right) => {
                if self.pointers_known_equal(left, right) {
                    Some(true)
                } else if left.block == right.block {
                    self.decide_from_order_rules(&ConditionTerm::pointer_offset_equal(
                        left.offset.clone(),
                        right.offset.clone(),
                    ))
                } else {
                    left.blocks_proven_distinct(right).then_some(false)
                }
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
                if let Some(pointer_condition) =
                    ConditionTerm::address_equality_as_pointer_equality(left, right)
                {
                    return self.decide(&pointer_condition);
                }
                if let Some((pointer, alignment)) = condition.as_pointer_alignment() {
                    return self.decide_pointer_alignment(pointer, alignment);
                }
                self.decide_uint64_equality_extras(left, right)
            }
            ConditionTerm::PointerOffsetEqual(left, right) if left == right => Some(true),
            ConditionTerm::PointerOffsetEqual(left, right) => {
                if pointer_offsets_proven_equal_for_memory_resolution(left, right, self) {
                    return Some(true);
                }
                match (left.as_ref().as_const(), right.as_ref().as_const()) {
                    (Some(left), Some(right)) => Some(left == right),
                    _ => {
                        // Addends both offsets share cancel exactly over the
                        // integers, so only the remainders are compared; a
                        // shared symbolic base offset then no longer blocks
                        // an exact decision about the indices.
                        let (left, right) = cancel_common_offset_addends(left, right);
                        if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
                            return Some(left == right);
                        }
                        let (left, right) = (&left, &right);
                        // One scaled index against a constant is exactly a
                        // question about the index: `x * 8 + 4 == 12` is
                        // `x == 1`, at any stride.
                        if let Some((index, element)) =
                            single_scaled_index_equal_to_constant(left, right)
                                .or_else(|| single_scaled_index_equal_to_constant(right, left))
                        {
                            return self.decide(&crate::kernel::machine_integer::comparison::condition_for_operand_views(
                                MachineIntegerType::Int32, CompareRelation::Equal,
                                [index.operand_view(), MachineOperandView::Legacy(&MachineTerm::constant(element as u32))],
                            ));
                        }
                        let left_index =
                            crate::kernel::reasoning::shared_element_index_from_offset(left, 4);
                        let right_index =
                            crate::kernel::reasoning::shared_element_index_from_offset(right, 4);
                        match (left_index, right_index) {
                            (Some(left_index), Some(right_index)) => exact_or_unequal(
                                self.decide(&crate::kernel::machine_integer::comparison::condition_for_operand_views(
                                    MachineIntegerType::Int32, CompareRelation::Equal,
                                    [left_index.operand_view(), right_index.operand_view()],
                                )),
                                self.rebuilt_offset_is_exact(left, 4, false)
                                    && self.rebuilt_offset_is_exact(right, 4, false),
                            ),
                            _ => {
                                let left_bytes = crate::kernel::reasoning::shared_byte_offset_from_pointer_offset(left);
                                let right_bytes = crate::kernel::reasoning::shared_byte_offset_from_pointer_offset(right);
                                match (left_bytes, right_bytes) {
                                    (Some(left_bytes), Some(right_bytes)) => exact_or_unequal(
                                        self.decide(&crate::kernel::machine_integer::comparison::condition_for_operand_views(
                                    MachineIntegerType::Int32, CompareRelation::Equal,
                                    [left_bytes.operand_view(), right_bytes.operand_view()],
                                )),
                                        self.rebuilt_offset_is_exact(left, 4, true)
                                            && self.rebuilt_offset_is_exact(right, 4, true),
                                    ),
                                    _ => None,
                                }
                            }
                        }
                    }
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            } if left == right => Some(true),
            ConditionTerm::Compare {
                format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                relation: CompareRelation::Equal,
                left,
                right,
            } => {
                let left = left.as_ref().clone();
                let right = right.as_ref().clone();
                if self.bitvector_add_terms_proven_equal(&left, &right)
                    || self.count_fold_split_terms_proven_equal(&left, &right)
                    || self.range_fold_terms_alpha_equivalent(&left, &right)
                {
                    return Some(true);
                }

                if let Some((left, right)) =
                    bitvector_equality_after_additive_cancellation(&left, &right)
                {
                    return self.decide(&ConditionTerm::machine_compare(
                        *format,
                        CompareRelation::Equal,
                        left,
                        right,
                    ));
                }

                if let Some(equal) = self.exact_signed_intervals_equal(&left, &right) {
                    return Some(equal);
                }

                if self.has_condition_fact(ConditionTerm::equal(left.clone(), right.clone()), true)
                    || self
                        .has_condition_fact(ConditionTerm::equal(right.clone(), left.clone()), true)
                    || self.memory_loads_proven_equal(&left, &right)
                    || self.has_condition_fact(
                        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                        true,
                    ) && self.has_condition_fact(
                        ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                        ),
                        true,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                        ),
                        true,
                    )
                    || self.order_facts_force_equal(&left, &right)
                    || self.range_facts_force_equal(&left, &right)
                {
                    Some(true)
                } else if self
                    .has_condition_fact(ConditionTerm::equal(left.clone(), right.clone()), false)
                    || self.has_condition_fact(
                        ConditionTerm::equal(right.clone(), left.clone()),
                        false,
                    )
                    || bitvector_same_base_nonzero_const_offset(&left, &right)
                {
                    Some(false)
                } else if (self.has_condition_fact(
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                ) && self.has_condition_fact(
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    false,
                )) || (self.has_condition_fact(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                ) && self.has_condition_fact(
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    false,
                )) {
                    Some(true)
                } else if self.decide(&ConditionTerm::signed_less_than(
                    left.clone(),
                    right.clone(),
                )) == Some(true)
                    || self.decide(&ConditionTerm::signed_greater_than(
                        left.clone(),
                        right.clone(),
                    )) == Some(true)
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                        ),
                        false,
                    )
                    || self.has_condition_fact(
                        ConditionTerm::pointer_offset_equal(
                            PointerOffsetTerm::scale_int32(right.clone(), 4),
                            PointerOffsetTerm::scale_int32(left.clone(), 4),
                        ),
                        false,
                    )
                {
                    Some(false)
                } else {
                    None
                }
            }
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation:
                    relation @ (crate::kernel::CompareRelation::LessThan
                    | crate::kernel::CompareRelation::LessEqual
                    | crate::kernel::CompareRelation::GreaterThan
                    | crate::kernel::CompareRelation::GreaterEqual),
                ..
            } if *relation != CompareRelation::Equal => self.decide_unsigned32_order(condition),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } => self.decide_signed_order_views(
                CompareRelation::LessThan,
                MachineOperandView::Legacy(left),
                MachineOperandView::Legacy(right),
            ),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } => self.decide_signed_order_views(
                CompareRelation::LessEqual,
                MachineOperandView::Legacy(left),
                MachineOperandView::Legacy(right),
            ),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            } => self.decide_signed_order_views(
                CompareRelation::GreaterThan,
                MachineOperandView::Legacy(left),
                MachineOperandView::Legacy(right),
            ),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => self.decide_signed_order_views(
                CompareRelation::GreaterEqual,
                MachineOperandView::Legacy(left),
                MachineOperandView::Legacy(right),
            ),
            _ => {
                use crate::kernel::machine_integer::{
                    Relation, comparison::native_comparison_view,
                };
                let view = native_comparison_view(condition, true)?;
                if matches!(
                    view.format,
                    MachineIntegerType::Int32 | MachineIntegerType::UInt32
                ) && matches!(view.relation, Relation::Equal | Relation::NotEqual)
                {
                    if view.relation == Relation::NotEqual {
                        let (positive, _) = view.retained_condition();
                        return self.decide(&positive).map(|value| !value);
                    }
                    let [left, right] = view
                        .operands
                        .each_ref()
                        .map(|operand| operand.operand_view());
                    return self
                        .decide_word_equality_views(view.format, left, right)
                        .map(|value| value == (view.relation == Relation::Equal));
                }
                let relation = match view.relation {
                    Relation::Less => CompareRelation::LessThan,
                    Relation::LessEqual => CompareRelation::LessEqual,
                    _ => return None,
                };
                let [left, right] = view
                    .operands
                    .each_ref()
                    .map(|operand| operand.operand_view());
                match view.format {
                    MachineIntegerType::Int32 => {
                        self.decide_signed_order_views(relation, left, right)
                    }
                    MachineIntegerType::UInt32 => self.decide_unsigned32_order_views(
                        left,
                        right,
                        relation == CompareRelation::LessThan,
                    ),
                    _ => None,
                }
            }
        }
    }

    /// The signed order rules in their original order, over retained roots.
    pub(super) fn decide_signed_order_views(
        &self,
        relation: CompareRelation,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
    ) -> Option<bool> {
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let same = match (left, right) {
            (MachineOperandView::Legacy(left), MachineOperandView::Legacy(right)) => left == right,
            _ => {
                Key::for_format(MachineIntegerType::Int32, left)
                    == Key::for_format(MachineIntegerType::Int32, right)
                    || self.equality_graph.are_integer_equal(
                        &IntegerTerm::Machine(left.retain(MachineIntegerType::Int32)),
                        &IntegerTerm::Machine(right.retain(MachineIntegerType::Int32)),
                    )
            }
        };
        if same {
            return match relation {
                CompareRelation::LessThan | CompareRelation::GreaterThan => Some(false),
                CompareRelation::LessEqual | CompareRelation::GreaterEqual => Some(true),
                CompareRelation::Equal => None,
            };
        }
        match relation {
            CompareRelation::LessThan => {
                if let Some(result) = self.decide_signed_comparison_from_equal_constants_views(
                    left,
                    right,
                    |left, right| left < right,
                ) {
                    return Some(result);
                }
                if right.literal() == Some(signed_int_min_term())
                    || left.literal() == Some(signed_int_max_term())
                {
                    return Some(false);
                }
                if self.subtract_same_const_order_fact_views(left, right, true)
                    || self.difference_graph_proves_order_views(left, right, true)
                    || (self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessEqual, left, right, true) && self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::Equal, left, right, false))
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::GreaterThan, right, left, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::GreaterEqual, left, right, false)
                    || self.has_upper_bound_below_views(left, right)
                    || self.has_successor_upper_bound_below_views(left, right)
                    || self.has_add_const_upper_bound_below_views(left, right)
                    || self.has_lower_bound_above_views(right, left)
                    || self.has_add_const_lower_bound_above_views(right, left)
                    || self.constant_offset_is_proven(left, right, false, true)
                    || self.constant_offset_is_proven(right, left, true, true)
                    // Consulted last: every earlier rule keeps its cost.
                    || self.has_subtract_const_upper_bound_views(left, right, true)
                    || self.has_subtract_const_lower_bound_views(right, left, true)
                {
                    Some(true)
                } else if self.has_written_operand_comparison(
                    MachineIntegerType::Int32,
                    CompareRelation::GreaterEqual,
                    left,
                    right,
                    true,
                ) || self.has_written_operand_comparison(
                    MachineIntegerType::Int32,
                    CompareRelation::LessEqual,
                    right,
                    left,
                    true,
                ) || self.difference_graph_proves_order_views(right, left, true)
                    || self.order_facts_force_equal_views(left, right)
                {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval_views(left, right, true)
                }
            }
            CompareRelation::LessEqual => {
                if let Some(result) = self.decide_signed_comparison_from_equal_constants_views(
                    left,
                    right,
                    |left, right| left <= right,
                ) {
                    return Some(result);
                }
                if left.literal() == Some(signed_int_min_term())
                    || right.literal() == Some(signed_int_max_term())
                {
                    return Some(true);
                }
                if self.difference_graph_proves_order_views(left, right, false)
                    || left.int32_add_const_base(1).is_some_and(|base| {
                        self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessThan, base, right, true)
                    })
                    || right.int32_subtract_const_parts().filter(|(_, n)| *n == 1).map(|(base, _)| base).is_some_and(|base| {
                        let zero_literal = MachineTerm::constant(0);
                        let zero = MachineOperandView::Legacy(&zero_literal);
                        left.literal() == Some(MachineTerm::constant(0))
                            && (self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::GreaterThan, base, zero, true) || self.has_lower_bound_above_views(base, zero))
                    })
                    || self.has_add_const_upper_bound_at_or_below_views(left, right)
                    || self.is_bounded_by_base_before_nonnegative_offset_views(left, right)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessThan, left, right, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::GreaterEqual, right, left, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::GreaterThan, right, left, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::GreaterThan, left, right, false)
                    || self.has_lower_bound_at_or_above_views(right, left)
                    || self.has_add_const_lower_bound_at_or_above_views(right, left)
                    || self.constant_offset_is_proven(left, right, false, false)
                    || self.order_facts_force_equal_views(left, right)
                    // Consulted last: every earlier rule keeps its cost.
                    || self.has_subtract_const_upper_bound_views(left, right, false)
                    || self.has_subtract_const_lower_bound_views(right, left, false)
                {
                    Some(true)
                } else if self.has_written_operand_comparison(
                    MachineIntegerType::Int32,
                    CompareRelation::GreaterThan,
                    left,
                    right,
                    true,
                ) {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval_views(left, right, false)
                }
            }
            CompareRelation::GreaterThan => {
                if let Some(result) = self.decide_signed_comparison_from_equal_constants_views(
                    left,
                    right,
                    |left, right| left > right,
                ) {
                    return Some(result);
                }
                if right.literal() == Some(signed_int_max_term())
                    || left.literal() == Some(signed_int_min_term())
                {
                    return Some(false);
                }
                if self.difference_graph_proves_order_views(right, left, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessThan, right, left, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessEqual, left, right, false)
                    || self.has_lower_bound_above_views(left, right)
                    || self.has_add_const_lower_bound_above_views(left, right)
                    // The mirrors of the `<` rules for a successor and for
                    // the int32 maximum, so `x + 1 > x` and `INT32_MAX > x`
                    // are decided as `x < x + 1` and `x < INT32_MAX` are.
                    || self.constant_offset_is_proven(right, left, false, true)
                    || left.literal() == Some(signed_int_max_term())
                        && self.decide_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessThan, right, left) == Some(true)
                {
                    Some(true)
                } else if self.has_written_operand_comparison(
                    MachineIntegerType::Int32,
                    CompareRelation::LessEqual,
                    left,
                    right,
                    true,
                ) || self.has_written_operand_comparison(
                    MachineIntegerType::Int32,
                    CompareRelation::GreaterEqual,
                    right,
                    left,
                    true,
                ) || self.order_facts_force_equal_views(left, right)
                {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval_views(right, left, true)
                }
            }
            CompareRelation::GreaterEqual => {
                if let Some(result) = self.decide_signed_comparison_from_equal_constants_views(
                    left,
                    right,
                    |left, right| left >= right,
                ) {
                    return Some(result);
                }
                if right.literal() == Some(signed_int_min_term())
                    || left.literal() == Some(signed_int_max_term())
                {
                    return Some(true);
                }
                if self.difference_graph_proves_order_views(right, left, false)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::GreaterThan, left, right, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessEqual, right, left, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessThan, right, left, true)
                    || self.has_written_operand_comparison(MachineIntegerType::Int32, CompareRelation::LessThan, left, right, false)
                    || self.has_lower_bound_at_or_above_views(left, right)
                    || self.has_add_const_lower_bound_at_or_above_views(left, right)
                    // The mirror of the `<=` successor rule, so `x + 1 >= x`
                    // is decided as `x <= x + 1` is.
                    || self.constant_offset_is_proven(right, left, false, false)
                    || self.order_facts_force_equal_views(left, right)
                {
                    Some(true)
                } else if self.has_written_operand_comparison(
                    MachineIntegerType::Int32,
                    CompareRelation::LessThan,
                    left,
                    right,
                    true,
                ) {
                    Some(false)
                } else {
                    self.decide_signed_order_from_conditional_interval_views(right, left, false)
                }
            }
            CompareRelation::Equal => None,
        }
    }

    /// The order rules of a `uint32` order: equal operands, constants an
    /// equality pins, the extremes `0` and `UINT32_MAX`, the difference
    /// graph's unsigned domain, the fact itself in any of its spellings, and
    /// one recorded bound of either operand ([`Self::has_unsigned32_bound_between_views`]).
    /// Each is tried for the order and for its converse, which refutes it.
    fn decide_unsigned32_order(&self, condition: &ConditionTerm) -> Option<bool> {
        let (lower, upper, strict) = held_order_at(MachineIntegerType::UInt32, condition, true)?;
        self.decide_unsigned32_order_views(
            MachineOperandView::Legacy(lower),
            MachineOperandView::Legacy(upper),
            strict,
        )
    }

    fn decide_unsigned32_order_views(
        &self,
        lower: MachineOperandView<'_>,
        upper: MachineOperandView<'_>,
        strict: bool,
    ) -> Option<bool> {
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let format = MachineIntegerType::UInt32;
        let same = match (lower, upper) {
            (MachineOperandView::Legacy(lower), MachineOperandView::Legacy(upper)) => {
                lower == upper
            }
            _ => {
                Key::for_format(format, lower) == Key::for_format(format, upper)
                    || self.equality_graph.are_integer_equal(
                        &IntegerTerm::Machine(lower.retain(format)),
                        &IntegerTerm::Machine(upper.retain(format)),
                    )
            }
        };
        if same {
            return Some(!strict);
        }
        if let (Some(lower), Some(upper)) = (
            self.signed_constant_known_equal_view(lower),
            self.signed_constant_known_equal_view(upper),
        ) {
            let (lower, upper) = (lower as u32, upper as u32);
            return Some(if strict {
                lower < upper
            } else {
                lower <= upper
            });
        }
        let holds = |lower: MachineOperandView<'_>, upper: MachineOperandView<'_>, strict: bool| {
            let (low, high) = (lower.word32_constant(), upper.word32_constant());
            if !strict && (low == Some(0) || high == Some(u32::MAX)) {
                return true;
            }
            if strict && (high == Some(0) || low == Some(u32::MAX)) {
                return false;
            }
            let order = crate::kernel::machine_integer::comparison::condition_for_operand_views(
                format,
                if strict {
                    CompareRelation::LessThan
                } else {
                    CompareRelation::LessEqual
                },
                [lower, upper],
            );
            self.difference_graph_proves(&order)
                || self.stated_unsigned_order_view(&order)
                || (strict
                    && self.has_written_operand_comparison(
                        format,
                        CompareRelation::LessEqual,
                        lower,
                        upper,
                        true,
                    )
                    && self.has_written_operand_comparison(
                        MachineIntegerType::Int32,
                        CompareRelation::Equal,
                        lower,
                        upper,
                        false,
                    ))
                || self.has_unsigned32_bound_between_views(lower, upper, strict)
        };
        if holds(lower, upper, strict) {
            Some(true)
        } else if holds(upper, lower, !strict) {
            Some(false)
        } else {
            None
        }
    }

    /// Exact stated orders only; retain the native route's four written forms.
    fn stated_unsigned_order_view(&self, order: &ConditionTerm) -> bool {
        if matches!(order, ConditionTerm::Compare { .. }) {
            return crate::kernel::proof::fact_reasoning::order_claim_forms(
                &Proposition::ConditionIs(order.clone(), true),
            )
            .iter()
            .any(|form| {
                matches!(form, Proposition::ConditionIs(condition, value)
                if self.condition_facts.get(condition) == Some(value))
            });
        }
        if let Some(source) = self.observation_comparisons.source(order, true) {
            record_implicit_reasoning_provenance(self, source);
            true
        } else {
            false
        }
    }

    /// Query equality already known to the trusted graph. This performs no
    /// arithmetic proof search, alias-component walk, or resource check.
    /// `false` means unknown, not unequal. Memory consumers must retain their
    /// structural-distinctness and separation checks around this query.
    pub(in crate::kernel) fn pointers_known_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        self.equality_graph.are_equal(left, right)
    }

    /// Whether two addresses are one, by spelling or by the equality graph
    /// of this context: one indexed class lookup, no search. Diagnostics use
    /// it to name two reads of one address that are spelled differently,
    /// such as the byte offset `(char *)q + i * 4` and the element `q[i]`.
    pub(crate) fn addresses_known_equal(&self, left: &Pointer, right: &Pointer) -> bool {
        left == right || self.pointers_known_equal(left, right)
    }

    /// True when some exact order fact strictly bounds `term` above
    /// (`term < y` for any `y`). A strict signed bound pins
    /// `term < INT_MAX`, which is what discharges `term + 1` overflow
    /// is checked from exact facts alone.
    pub(in crate::kernel) fn has_exact_strict_upper_bound(&self, term: &MachineTerm) -> bool {
        self.has_exact_strict_upper_bound_view(MachineOperandView::Legacy(term))
    }

    pub(in crate::kernel) fn has_exact_strict_upper_bound_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> bool {
        self.checked_order_bounds.strict_upper_view(term).is_some()
    }

    /// Whether the difference graph of these facts proves `left < right`
    /// (or `left <= right` when `require_strict` is false). This is the one
    /// order engine the condition decision and memory resolution read: it is
    /// maintained per fact and answers each query within `EDGE_LIMIT` edges,
    /// so it reads no collection that grows with the facts. A longer order
    /// chain is left undecided; a proof states an intermediate step.
    pub(in crate::kernel) fn difference_graph_proves_order(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
        require_strict: bool,
    ) -> bool {
        self.difference_graph_proves_order_views(
            MachineOperandView::Legacy(left),
            MachineOperandView::Legacy(right),
            require_strict,
        )
    }

    pub(in crate::kernel) fn difference_graph_proves_order_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        require_strict: bool,
    ) -> bool {
        self.difference_graph_proves(
            &crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                if require_strict {
                    CompareRelation::LessThan
                } else {
                    CompareRelation::LessEqual
                },
                [left, right],
            ),
        )
    }

    /// Whether the difference graph of these facts proves `condition`
    /// ([`Self::difference_graph_proves_order`]), at any format it orders.
    pub(in crate::kernel) fn difference_graph_proves(&self, condition: &ConditionTerm) -> bool {
        let graph = self.difference_graph.graph(|| {
            self.condition_facts
                .scan_for_upkeep()
                .map(|(condition, value)| (condition, *value))
                .collect()
        });
        if !matches!(condition, ConditionTerm::Compare { .. })
            && let Some(view) =
                crate::kernel::machine_integer::comparison::native_comparison_view(condition, true)
        {
            return graph.decide_shared_order(&view) == Some(true);
        }
        graph.decide(condition) == Some(true)
    }

    #[cfg(test)]
    pub(in crate::kernel) fn reset_exact_order_evidence_visits() {
        EXACT_ORDER_EVIDENCE_VISITS.with(|visits| visits.set(0));
    }

    #[cfg(test)]
    pub(in crate::kernel) fn exact_order_evidence_visits() -> usize {
        EXACT_ORDER_EVIDENCE_VISITS.with(std::cell::Cell::get)
    }

    /// Retain the exact signed-order edges selected by a deterministic path
    /// decision. This deliberately accepts only syntactic edge joins (plus a
    /// context-free constant tail): equality, memory-DAG, quantified, and
    /// derived-edge joins need their own typed evidence before they may be
    /// exported as certificate provenance.
    #[cfg(test)]
    pub(in crate::kernel) fn exact_signed_order_path_evidence(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
        require_strict: bool,
    ) -> Option<Vec<SignedOrderDerivationStep>> {
        self.exact_signed_order_source_path(
            MachineOperandView::Legacy(left),
            MachineOperandView::Legacy(right),
            require_strict,
        )?
        .into_iter()
        .map(|step| {
            // Boxed reference used by native path-parity tests only.
            let Proposition::ConditionIs(condition, value) = &step.premise else {
                return None;
            };
            let (lower, upper, strict) = condition_as_order_fact(condition, *value)?;
            Some(SignedOrderDerivationStep::from_views(
                MachineOperandView::Legacy(&lower),
                MachineOperandView::Legacy(&upper),
                strict,
                step.premise,
            ))
        })
        .collect()
    }

    pub(in crate::kernel) fn exact_signed_order_source_path(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        require_strict: bool,
    ) -> Option<Vec<OrderDerivationStep>> {
        use super::super::checked_scalar_facts::ScalarOperandKey as Key;
        use crate::kernel::machine_integer::Relation;
        use MachineOperandView as V;
        let format = MachineIntegerType::Int32;
        let key = |v: MachineOperandView<'_>| Key::for_format(format, v);
        let constant = |v: V<'_>| v.word32_constant().map(|n| i64::from(n as i32));
        let connection = |a: V<'_>, b: V<'_>| {
            constant(a)
                .zip(constant(b))
                .and_then(|(a, b)| (a <= b).then_some(a < b))
        };
        let bridging = crate::kernel::api::extended_dag_bridging_active();
        let terms_match = |a: V<'_>, b: V<'_>| {
            key(a) == key(b)
                || (bridging
                    && a.read_source().zip(b.read_source()).is_some_and(|(a, b)| {
                        crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                            &a, &b, self,
                        )
                    }))
        };
        let edges_from = |current: V<'_>| {
            let index = &self.order_facts_by_lower;
            let mut conditions = index.written_from_view(current).collect::<BTreeSet<_>>();
            if let Some(c) = constant(current) {
                conditions.extend(index.constant_at_least(c));
            }
            if bridging && let Some((_, pointer, kind)) = current.read() {
                conditions.extend(index.loads_of(pointer, kind));
            }
            conditions
                .into_iter()
                .rev()
                .filter_map(|condition| {
                    #[cfg(test)]
                    EXACT_ORDER_EVIDENCE_VISITS.with(|visits| visits.set(visits.get() + 1));
                    let value = *self.condition_facts.get(condition)?;
                    let view = order_view_at_format(condition, value, format)?;
                    Some((
                        key(view.operands[0].operand_view()),
                        key(view.operands[1].operand_view()),
                        view.relation == Relation::Less,
                        OrderDerivationStep {
                            premise: Proposition::ConditionIs(condition.clone(), value),
                        },
                    ))
                })
                .collect::<Vec<_>>()
        };
        let mut stack = vec![(key(left), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let current = current.operand_view();
            let tail = connection(current, right);
            if (terms_match(current, right) || tail.is_some())
                && (!require_strict || strict_so_far || tail == Some(true))
                && !path.is_empty()
            {
                return Some(path);
            }
            for (lower, upper, strict, edge) in edges_from(current) {
                let link = connection(current, lower.operand_view());
                if !terms_match(current, lower.operand_view()) && link.is_none() {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(edge);
                stack.push((
                    upper,
                    strict_so_far || strict || link == Some(true),
                    extended,
                ));
            }
        }
        None
    }

    /// The exact order facts at `format`, one of [`WIDE_ORDER_FORMATS`], that
    /// chain `left` up to `right`. Each step keeps the proposition the context holds, as
    /// [`Self::exact_signed_order_path_evidence`] does for `int32`. The chain
    /// meets `right` at the same canonical term; a constant connection is
    /// left to other rules, since `solve` writes no lemma for it.
    pub(in crate::kernel) fn exact_wide_order_path_evidence(
        &self,
        left: crate::kernel::MachineOperandView<'_>,
        right: crate::kernel::MachineOperandView<'_>,
        require_strict: bool,
        format: MachineIntegerType,
    ) -> Option<Vec<OrderDerivationStep>> {
        use super::super::checked_scalar_facts::ScalarOperandKey as Key;
        use crate::kernel::machine_integer::Relation;
        let canonical = |term: crate::kernel::MachineOperandView<'_>| Key::canonical(format, term);
        // Read only the edges indexed at this endpoint, in the same reverse
        // source order as the native walk. Canonical load identities still
        // connect a written load and its registered variable.
        let edges_from = |current: &Key| {
            self.order_facts_by_lower
                .wide_from(format, current)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .rev()
                .filter_map(|condition| {
                    let value = *self.condition_facts.get(condition)?;
                    let view = order_view_at_format(condition, value, format)?;
                    debug_assert_eq!(canonical(view.operands[0].operand_view()), *current);
                    Some((
                        canonical(view.operands[1].operand_view()),
                        view.relation == Relation::Less,
                        OrderDerivationStep {
                            premise: Proposition::ConditionIs(condition.clone(), value),
                        },
                    ))
                })
                .collect::<Vec<_>>()
        };
        let target = canonical(right);
        let mut stack = vec![(canonical(left), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            if current == target && (!require_strict || strict_so_far) && !path.is_empty() {
                return Some(path);
            }
            for (upper, strict, edge) in edges_from(&current) {
                let mut extended = path.clone();
                extended.push(edge);
                stack.push((upper, strict_so_far || strict, extended));
            }
        }
        None
    }

    /// Whether written signed-order facts chain from `left` to `right`,
    /// strictly when `require_strict`.
    ///
    /// A non-constant node's edges are read from the endpoint index
    /// (`signed_order_bounds`), which files every written order fact under
    /// its lower endpoint, so a walk costs the edges it follows rather than
    /// every order fact at every node. The two matches no endpoint key
    /// spells read `OrderFactsByLower`: a constant node connects to any edge
    /// whose lower end is a constant at least as large, one range read, and
    /// with extended bridging a load connects to its forms at other
    /// states, filed under its pointer and kind.
    pub(in crate::kernel) fn has_exact_order_path(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
        require_strict: bool,
    ) -> bool {
        self.has_exact_order_path_views(
            MachineOperandView::Legacy(left),
            MachineOperandView::Legacy(right),
            require_strict,
        )
    }

    pub(in crate::kernel) fn has_exact_order_path_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        require_strict: bool,
    ) -> bool {
        use crate::kernel::MachineOperandView as V;
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let format = MachineIntegerType::Int32;
        let bridging = crate::kernel::api::extended_dag_bridging_active();
        let terms_match = |current: V<'_>, other: V<'_>| {
            Key::for_format(format, current) == Key::for_format(format, other)
                || (bridging
                    && current.read_source().zip(other.read_source()).is_some_and(
                        |(current, other)| {
                            crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                                &current, &other, self,
                            )
                        },
                    ))
        };
        let constant = |operand: V<'_>| {
            operand
                .word32_constant()
                .map(|value| i64::from(value as i32))
        };
        let connection = |current: V<'_>, other: V<'_>| {
            constant(current)
                .zip(constant(other))
                .and_then(|(current, other)| (current <= other).then_some(current < other))
        };
        let mut stack = vec![(Key::for_format(format, left), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let current = current.operand_view();
            let constant_connection = connection(current, right);
            if (terms_match(current, right) || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
            {
                return true;
            }
            let bridged_load = bridging && current.read().is_some();
            if bridged_load || constant(current).is_some() {
                let index = &self.order_facts_by_lower;
                let candidates = match (current.read(), constant(current)) {
                    (_, Some(constant)) => index.constant_at_least(constant).collect::<Vec<_>>(),
                    (Some((_, pointer, kind)), None) => index.loads_of(pointer, kind).collect(),
                    _ => Vec::new(),
                };
                for condition in candidates {
                    let Some(view) = self
                        .condition_facts
                        .get(condition)
                        .and_then(|value| comparison_view(condition, *value))
                        .filter(|view| {
                            view.format == format
                                && matches!(view.relation, Relation::Less | Relation::LessEqual)
                        })
                    else {
                        continue;
                    };
                    let [edge_left, edge_right] = view
                        .operands
                        .each_ref()
                        .map(|operand| operand.operand_view());
                    let constant_connection = connection(current, edge_left);
                    if terms_match(current, edge_left) || constant_connection.is_some() {
                        stack.push((
                            Key::for_format(format, edge_right),
                            strict_so_far
                                || view.relation == Relation::Less
                                || constant_connection == Some(true),
                        ));
                    }
                }
                continue;
            }
            let Some(bounds) = self.signed_order_bounds.get_operand(current) else {
                continue;
            };
            for (lower, upper, edge_strict, outgoing) in bounds.operand_keys() {
                crate::instrumentation::record_deterministic_work(1);
                // Canonical aliases are indexed, but an exact walk still
                // requires the written endpoint to match.
                if outgoing && Key::for_format(format, lower) == Key::for_format(format, current) {
                    stack.push((Key::for_format(format, upper), strict_so_far || edge_strict));
                }
            }
        }
        false
    }

    pub(in crate::kernel) fn proves_order_condition_for_memory_resolution(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        use crate::kernel::machine_integer::{
            Relation,
            comparison::{comparison_view, condition_for_operand_views},
        };
        use MachineOperandView as V;
        if crate::kernel::assumptions::reasoning_interrupted() {
            return false;
        }
        if value && self.decide_from_variable_chain(condition) == Some(true) {
            return true;
        }
        let Some(view) = comparison_view(condition, value) else {
            return false;
        };
        let strict = match view.relation {
            Relation::Less => true,
            Relation::LessEqual => false,
            _ => return false,
        };
        let [left, right] = view.operands.each_ref().map(|v| v.operand_view());
        let written_constant = |v: V<'_>| v.literal().and_then(|v| v.as_const());
        let order = |left, right, strict| {
            condition_for_operand_views(
                MachineIntegerType::Int32,
                if strict {
                    CompareRelation::LessThan
                } else {
                    CompareRelation::LessEqual
                },
                [left, right],
            )
        };
        // An unsigned upper bound below the sign bit is the signed pair
        // 0 <= term and term <= bound, at the same written word reading.
        if value && view.format == MachineIntegerType::UInt32 && written_constant(left).is_none() {
            let Some(bound) = written_constant(right)
                .and_then(|bound| {
                    if strict {
                        bound.checked_sub(1)
                    } else {
                        Some(bound)
                    }
                })
                .filter(|bound| *bound <= i32::MAX as u32)
            else {
                return false;
            };
            let left = match left.cast() {
                Some((MachineCastSpelling::Generic, source, destination, operand))
                    if crate::kernel::is_sign_cast32(source, destination) =>
                {
                    operand
                }
                _ => left,
            };
            let zero = MachineTerm::constant(0);
            let bound = MachineTerm::constant(bound);
            return self.proves_order_condition_for_memory_resolution(
                &order(V::Legacy(&zero), left, false),
                true,
            ) && self.proves_order_condition_for_memory_resolution(
                &order(left, V::Legacy(&bound), false),
                true,
            );
        }
        if view.format != MachineIntegerType::Int32 {
            return false;
        }
        let maximum = MachineTerm::constant(i32::MAX as u32);
        let minimum = MachineTerm::constant(i32::MIN as u32);
        if !strict
            && (right.literal().as_ref() == Some(&maximum)
                || left.literal().as_ref() == Some(&minimum))
        {
            return true;
        }
        // Use the common checking simplifier; it retains shared operands and
        // consults the ordinary equality/constant indexes for these endpoints.
        let native = [left, right].map(|view| match view {
            V::Legacy(term) => Some(self.simplify_bitvector_under_assumptions(term)),
            V::Shared(_) => None,
        });
        let shared = [left, right].map(|view| match view {
            V::Shared(root) => Some(self.checking_word32_shared_root(root)),
            V::Legacy(_) => None,
        });
        let [lower, upper] = std::array::from_fn(|i| {
            native[i].as_ref().map(V::Legacy).unwrap_or_else(|| {
                V::Shared(shared[i].as_ref().expect("one operand representation"))
            })
        });
        if self.difference_graph_proves_order_views(lower, upper, strict) {
            return true;
        }
        // The successor rules keep the written endpoints and run after the
        // graph query, just as the ordinary condition checker does.
        if !strict
            && let Some(base) = left.int32_add_const_base(1)
            && self.proves_order_condition_for_memory_resolution(&order(base, right, true), true)
        {
            return true;
        }
        let Some((constant, base)) = written_constant(left).zip(right.int32_add_const_base(1))
        else {
            return false;
        };
        let Some(reduced) = (if strict {
            Some(constant as i32)
        } else {
            (constant as i32).checked_sub(1)
        }) else {
            return false;
        };
        let reduced = MachineTerm::constant(reduced as u32);
        self.proves_order_condition_for_memory_resolution(
            &order(V::Legacy(&reduced), base, false),
            true,
        ) && self.proves_order_condition_for_memory_resolution(
            &order(base, V::Legacy(&maximum), true),
            true,
        )
    }
}

/// Splits both offsets into their addends and removes every addend they
/// share (one occurrence per match). Offsets are exact i64 sums of their
/// addends, so `C + L == C + R` holds exactly if and only if `L == R`.
pub(in crate::kernel) fn cancel_common_offset_addends(
    left: &crate::kernel::PointerOffsetTerm,
    right: &crate::kernel::PointerOffsetTerm,
) -> (
    crate::kernel::PointerOffsetTerm,
    crate::kernel::PointerOffsetTerm,
) {
    use crate::kernel::PointerOffsetTerm;
    fn addends(offset: &PointerOffsetTerm, out: &mut Vec<PointerOffsetTerm>) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                addends(left, out);
                addends(right, out);
            }
            other => out.push(other.clone()),
        }
    }
    fn rebuild(addends: Vec<PointerOffsetTerm>) -> PointerOffsetTerm {
        addends
            .into_iter()
            .reduce(|sum, addend| PointerOffsetTerm::Add(Box::new(sum), Box::new(addend)))
            .unwrap_or(PointerOffsetTerm::Constant(0))
    }
    let mut left_addends = Vec::new();
    addends(left, &mut left_addends);
    let mut right_addends = Vec::new();
    addends(right, &mut right_addends);
    crate::instrumentation::record_deterministic_work(left_addends.len() + right_addends.len());
    // A multiset count: each addend is hashed once, and an addend shared
    // `k` times cancels `k` times, so the work is linear in the addends.
    let mut right_counts = std::collections::HashMap::<&PointerOffsetTerm, usize>::new();
    for addend in &right_addends {
        *right_counts.entry(addend).or_default() += 1;
    }
    let mut cancelled = std::collections::HashMap::<&PointerOffsetTerm, usize>::new();
    let mut left_rest = Vec::new();
    for addend in &left_addends {
        match right_counts.get_mut(addend) {
            Some(count) if *count > 0 => {
                *count -= 1;
                *cancelled.entry(addend).or_default() += 1;
            }
            _ => left_rest.push(addend.clone()),
        }
    }
    let mut right_rest = Vec::new();
    for addend in &right_addends {
        match cancelled.get_mut(addend) {
            Some(count) if *count > 0 => *count -= 1,
            _ => right_rest.push(addend.clone()),
        }
    }
    (rebuild(left_rest), rebuild(right_rest))
}

/// The largest alignment a fact may state; probes above it are pointless.
const MAX_PROBED_ALIGNMENT: u64 = 4096;

impl PureFactContext {
    /// Decides `aligned(pointer, alignment)` from the pointer's formation: a
    /// heap block base is allocator-aligned, and any other base needs a
    /// recorded alignment fact (from address-of or a contract). A constant
    /// byte displacement from such a base is then decided exactly. Anything
    /// else stays undecided; alignment is never inferred from a pointee type.
    pub(in crate::kernel) fn decide_pointer_alignment(
        &self,
        pointer: &Pointer,
        alignment: u64,
    ) -> Option<bool> {
        self.pointer_alignment_decision(pointer, alignment)
            .map(|(aligned, _)| aligned)
    }

    /// The decision together with the exact base fact it used, so a
    /// derivation can retain that premise for its check.
    pub(in crate::kernel) fn pointer_alignment_decision(
        &self,
        pointer: &Pointer,
        alignment: u64,
    ) -> Option<(bool, Option<Proposition>)> {
        self.pointer_formation_alignment_decision(pointer, alignment, true)
            .or_else(|| {
                // One checked concrete formation, not an alias-member search.
                // Equality is trusted kernel evidence; the formation rule still
                // proves the alignment and retains any explicit base premise.
                let storage = self.equality_graph.storage_address(pointer);
                (storage != *pointer)
                    .then(|| self.pointer_formation_alignment_decision(&storage, alignment, true))
                    .flatten()
            })
    }

    /// The existing single-premise alignment certificate encodes formation
    /// arithmetic, not address-class equality. Do not cite a class witness as
    /// though that restricted certificate also carried its equality support.
    pub(in crate::kernel) fn pointer_alignment_certificate_decision(
        &self,
        pointer: &Pointer,
        alignment: u64,
    ) -> Option<(bool, Option<Proposition>)> {
        self.pointer_formation_alignment_decision(pointer, alignment, false)
    }

    fn pointer_formation_alignment_decision(
        &self,
        pointer: &Pointer,
        alignment: u64,
        allow_class_witness: bool,
    ) -> Option<(bool, Option<Proposition>)> {
        if !alignment.is_power_of_two() {
            return None;
        }
        // The null pointer's address is zero, which every alignment divides.
        let null_fact = ConditionTerm::pointer_equal(pointer.clone(), Pointer::null());
        if self.decide(&null_fact) == Some(true) {
            return Some((true, Some(Proposition::ConditionIs(null_fact, true))));
        }
        let (base, displacement) = split_constant_displacement(&pointer.offset);
        let intrinsic_block_alignment = match &pointer.block {
            PointerBlock::Heap(_) => Some(crate::kernel::primitives::HEAP_ALLOCATION_ALIGNMENT),
            // A file-scope or static object's block is placed by the
            // compiler at its type's alignment, recorded when the block was
            // created.
            block => crate::kernel::primitives::registered_block_alignment(block),
        };
        let premise = if base.as_const() == Some(0)
            && intrinsic_block_alignment.is_some_and(|intrinsic| alignment <= intrinsic)
        {
            None
        } else {
            // A displacement that is a scaled index whose scale the alignment
            // divides (an element step of a struct pointer, say) cannot
            // change the residue, so the fact may be recorded on the pointer
            // without it.
            let reduced = drop_aligned_scaled_addends(&base, alignment);
            let candidates = std::iter::once(base.clone())
                .chain(reduced.filter(|reduced| *reduced != base))
                .collect::<Vec<_>>();
            let mut found = None;
            'candidates: for candidate in candidates {
                let base_pointer = Pointer {
                    block: pointer.block.clone(),
                    offset: candidate,
                };
                let mut probe = alignment;
                while probe <= MAX_PROBED_ALIGNMENT {
                    let premise_at = |pointer: &Pointer, alignment| {
                        self.equality_graph
                            .admitted
                            .pointer_alignment_facts
                            .get(&(pointer.clone(), alignment))
                            .and_then(|sources| sources.iter().next())
                            .cloned()
                            .or_else(|| {
                                let fact =
                                    ConditionTerm::pointer_aligned(pointer.clone(), alignment);
                                (self.exact_condition_value(&fact) == Some(true)).then_some(fact)
                            })
                    };
                    if let Some(fact) = premise_at(&base_pointer, probe) {
                        found = Some(Proposition::ConditionIs(fact, true));
                        break 'candidates;
                    }
                    let witness = allow_class_witness
                        .then(|| self.equality_graph.alignment_witness(&base_pointer))
                        .flatten()
                        .filter(|(known, _)| probe <= *known)
                        .and_then(|(known, source)| premise_at(&source, known));
                    if let Some(fact) = witness {
                        found = Some(Proposition::ConditionIs(fact, true));
                        break 'candidates;
                    }
                    probe *= 2;
                }
            }
            Some(found?)
        };
        Some((displacement.rem_euclid(alignment as i64) == 0, premise))
    }
}

impl PureFactContext {
    /// Equalities the address and tag structure decides beyond the plain
    /// address rules: two tagged addresses, a tagged address against zero,
    /// a masked tag against a value, and a masked term against zero.
    pub(in crate::kernel) fn decide_uint64_equality_extras(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
    ) -> Option<bool> {
        let mut used = crate::kernel::eval::pointer_tags::UsedFacts::new();
        self.decide_uint64_equality_extras_citing(left, right, &mut used)
    }

    /// Retain a written 64-bit equality through evidence selection and replay.
    pub(in crate::kernel) fn decide_pointer_comparison_citing(
        &self,
        condition: &ConditionTerm,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        let view =
            crate::kernel::machine_integer::comparison::structural_comparison_view(condition)?;
        if view.format.format().bits() != 64 || view.relation != CompareRelation::Equal {
            return None;
        }
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let decided = if let (Some(left), Some(right)) = (left.read_source(), right.read_source()) {
            self.decide_pointer_word_equality_citing(&left, &right, used)
        } else {
            self.decide_uint64_equality_extras_views(left, right, used)
        }?;
        Some(decided != view.negated)
    }

    /// The complete pointer-word decision for a 64-bit equality, citing the
    /// exact facts used: the address rule, the alignment rule, and the tag
    /// extras, in that order.
    pub(in crate::kernel) fn decide_pointer_word_equality_citing(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        if let Some(pointer_condition) =
            ConditionTerm::address_equality_as_pointer_equality(left, right)
        {
            return self.decide_citing(&pointer_condition, used);
        }
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        };
        if let Some((pointer, alignment)) = condition.as_pointer_alignment() {
            let (aligned, premise) =
                self.pointer_alignment_certificate_decision(pointer, alignment)?;
            if let Some(premise) = premise {
                used.premises.push(premise);
            }
            return Some(aligned);
        }
        self.decide_uint64_equality_extras_citing(left, right, used)
    }

    fn decide_uint64_equality_extras_citing(
        &self,
        left: &MachineTerm,
        right: &MachineTerm,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        self.decide_uint64_equality_extras_views(
            MachineOperandView::Legacy(left),
            MachineOperandView::Legacy(right),
            used,
        )
    }

    pub(in crate::kernel) fn decide_uint64_equality_extras_views(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        use crate::kernel::eval::pointer_tags::{
            masked_tag_value, tag_bound, tagged_address_form_view,
        };
        let left_form = tagged_address_form_view(left, self, used);
        let right_form = tagged_address_form_view(right, self, used);
        let left_is_form = left_form.is_some();
        let equal = |left, right| {
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::UInt64,
                CompareRelation::Equal,
                [left, right],
            )
        };
        match (left_form, right_form) {
            (Some(left), Some(right)) => {
                if crate::kernel::eval::pointer_tags::same_tag_syntax(&left.tag, &right.tag) {
                    return self.decide_citing(
                        &ConditionTerm::pointer_equal(left.pointer, right.pointer),
                        used,
                    );
                }
                if left.pointer == right.pointer {
                    return self.decide_citing(
                        &equal(left.tag.operand_view(), right.tag.operand_view()),
                        used,
                    );
                }
                let (Some(left_tag), Some(right_tag)) = (
                    tag_bound(left.tag.operand_view()),
                    tag_bound(right.tag.operand_view()),
                ) else {
                    return None;
                };
                let alignment = left_tag
                    .max(right_tag)
                    .checked_add(1)?
                    .checked_next_power_of_two()?;
                let tags_differ = self.decide_citing(
                    &equal(left.tag.operand_view(), right.tag.operand_view()),
                    used,
                ) == Some(false);
                let distinct = tags_differ
                    || self.decide_citing(
                        &ConditionTerm::pointer_equal(left.pointer.clone(), right.pointer.clone()),
                        used,
                    ) == Some(false);
                let both_aligned = self.decide_citing(
                    &ConditionTerm::pointer_aligned(left.pointer, alignment),
                    used,
                ) == Some(true)
                    && self.decide_citing(
                        &ConditionTerm::pointer_aligned(right.pointer, alignment),
                        used,
                    ) == Some(true);
                // Different low tags have different residues modulo alignment.
                // Otherwise, distinct aligned bases differ by at least that
                // alignment, so smaller tags cannot make the words coincide.
                (distinct && both_aligned).then_some(false)
            }
            (Some(form), None) | (None, Some(form)) => {
                let other = if left_is_form { right } else { left };
                if other.uint64_constant() != Some(0) {
                    return None;
                }
                let tag = tag_bound(form.tag.operand_view())?;
                let alignment = tag.checked_add(1)?.checked_next_power_of_two()?;
                let nonnull = self.decide_citing(
                    &ConditionTerm::pointer_equal(form.pointer.clone(), Pointer::null()),
                    used,
                ) == Some(false);
                let aligned = self.decide_citing(
                    &ConditionTerm::pointer_aligned(form.pointer, alignment),
                    used,
                ) == Some(true);
                // A non-null base aligned to `alignment` is at least
                // `alignment`, so adding a smaller tag cannot reach zero.
                (nonnull && aligned).then_some(false)
            }
            (None, None) => {
                if let Some(tag) = masked_tag_value(left, self, used) {
                    return self.decide_citing(&equal(tag.operand_view(), right), used);
                }
                if let Some(tag) = masked_tag_value(right, self, used) {
                    return self.decide_citing(&equal(left, tag.operand_view()), used);
                }
                self.decide_masked_zero(left, right, used)
            }
        }
    }

    /// The Integer observation of a wide equality, with its original
    /// polarity. Native pointer-word queries keep their existing rule order.
    pub(in crate::kernel) fn decide_shared_mask_zero(
        &self,
        condition: &ConditionTerm,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::{Relation, comparison::native_comparison_view};
        let view = native_comparison_view(condition, true)?;
        if view.format.format().bits() != 64
            || !matches!(view.relation, Relation::Equal | Relation::NotEqual)
        {
            return None;
        }
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        self.decide_masked_zero(left, right, used)
            .map(|value| value == (view.relation == Relation::Equal))
    }

    /// `(x & m) == 0` holds when `x` is below the lowest set bit of `m`.
    pub(in crate::kernel) fn decide_masked_zero(
        &self,
        left: MachineOperandView<'_>,
        right: MachineOperandView<'_>,
        used: &mut crate::kernel::eval::pointer_tags::UsedFacts,
    ) -> Option<bool> {
        let masked = if right.uint64_constant() == Some(0) {
            left
        } else if left.uint64_constant() == Some(0) {
            right
        } else {
            return None;
        };
        let (MachineIntegerType::UInt64, MachineBinaryOp::BitwiseAnd, [first, second]) =
            masked.binary()?
        else {
            return None;
        };
        let (value, mask) = match (first.uint64_constant(), second.uint64_constant()) {
            (None, Some(mask)) => (first, mask),
            (Some(mask), None) => (second, mask),
            _ => return None,
        };
        if mask == 0 {
            return Some(true);
        }
        let bound = MachineTerm::uint64_constant(1u64.checked_shl(mask.trailing_zeros())?);
        let guard = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            MachineIntegerType::UInt64,
            CompareRelation::LessThan,
            [value, MachineOperandView::Legacy(&bound)],
        );
        (self.decide_citing(&guard, used) == Some(true)).then_some(true)
    }
}

/// Separates the constant byte addends of an offset from its symbolic part,
/// rebuilding the symbolic part with the canonical constructor so it matches
/// the shape a recorded fact about the base pointer has.
/// The offset without its scaled-index addends whose byte scale `alignment`
/// divides; `None` when there is no such addend.
fn drop_aligned_scaled_addends(
    offset: &crate::kernel::PointerOffsetTerm,
    alignment: u64,
) -> Option<crate::kernel::PointerOffsetTerm> {
    use crate::kernel::PointerOffsetTerm;
    fn addends(offset: &PointerOffsetTerm, out: &mut Vec<PointerOffsetTerm>) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                addends(left, out);
                addends(right, out);
            }
            other => out.push(other.clone()),
        }
    }
    let mut parts = Vec::new();
    addends(offset, &mut parts);
    let alignment = i64::try_from(alignment).ok()?;
    // A struct pointer steps by `(uint8 *)p + i * sizeof(struct)`, so the
    // scale may sit inside the index as a constant factor.
    fn constant_factor(term: crate::kernel::MachineOperandView<'_>) -> Option<i64> {
        let (MachineIntegerType::Int32, crate::kernel::MachineBinaryOp::Multiply, [left, right]) =
            term.binary()?
        else {
            return None;
        };
        left.word32_constant()
            .or_else(|| right.word32_constant())
            .map(|constant| i64::from(constant as i32))
    }
    let divisible = |part: &PointerOffsetTerm| match part {
        PointerOffsetTerm::Int32Scaled { value, byte_width }
        | PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } => {
            let scale = constant_factor(value.operand_view())
                .and_then(|factor| factor.checked_mul(*byte_width))
                .unwrap_or(*byte_width);
            scale != 0 && scale % alignment == 0
        }
        _ => false,
    };
    if !parts.iter().any(&divisible) {
        return None;
    }
    Some(
        parts
            .into_iter()
            .filter(|part| !divisible(part))
            .reduce(PointerOffsetTerm::add)
            .unwrap_or(PointerOffsetTerm::Constant(0)),
    )
}

fn split_constant_displacement(
    offset: &crate::kernel::PointerOffsetTerm,
) -> (crate::kernel::PointerOffsetTerm, i64) {
    use crate::kernel::PointerOffsetTerm;
    fn addends(offset: &PointerOffsetTerm, out: &mut Vec<PointerOffsetTerm>) {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                addends(left, out);
                addends(right, out);
            }
            other => out.push(other.clone()),
        }
    }
    let mut parts = Vec::new();
    addends(offset, &mut parts);
    let mut displacement = 0i64;
    let mut symbolic = Vec::new();
    for part in parts {
        match part.as_const() {
            Some(constant) => displacement = displacement.wrapping_add(constant),
            None => symbolic.push(part),
        }
    }
    let base = symbolic
        .into_iter()
        .reduce(PointerOffsetTerm::add)
        .unwrap_or(PointerOffsetTerm::Constant(0));
    (base, displacement)
}

/// The operand, inclusive bound, and source strictness of a `uint32` upper
/// bound `x <=u c` (or `x <u c + 1`) held with `value`, in either
/// orientation or polarity, whose bound `c` lies below the sign bit.
///
/// Such a bound means exactly `0 <= x` and `x <= c` in signed arithmetic: a
/// word no larger than `c < 2^31` as unsigned has a clear sign bit, and for a
/// clear sign bit the two readings agree. That is the form order facts are
/// written in, so the condition checker decides it by deciding those two, and
/// a context that assumes it files those two beside it
/// (`PureFactContext::assume_condition`), so every reader of signed order
/// facts sees the range an unsigned test established. The returned operand
/// is `x`'s bits read through one σ (`MachineTerm::sign_cast32_bits`):
/// the signed reading of `σ(y) <=u c` is a range of `y` itself, never a
/// signed comparison of the `uint32` term `σ(y)`. The recognizer is a
/// constant-size match on the condition's own shape.
pub(in crate::kernel) fn unsigned_upper_bound_below_sign_bit(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&MachineTerm, u32, bool)> {
    let (left, right, strict) = held_order_at(MachineIntegerType::UInt32, condition, value)?;
    if left.as_const().is_some() {
        return None;
    }
    let bound = right.as_const()?;
    let bound = if strict { bound.checked_sub(1)? } else { bound };
    (bound <= i32::MAX as u32).then_some((left.sign_cast32_bits(), bound, strict))
}

/// The operand, inclusive bound, and source strictness of a sixty-four-bit
/// unsigned upper bound `x <=u c` (or `x <u c + 1`) held with `value`, in
/// either orientation or polarity, whose bound `c` lies below `2^31`.
///
/// Such a bound pins `x` below the sign bit of its low word: `x` is exactly
/// its truncation `(uint32)x`, which as a signed word lies in `0..=c`. A
/// context that assumes the bound files that range on the truncation beside
/// it (`PureFactContext::assume_condition`), the sixty-four-bit counterpart
/// of [`unsigned_upper_bound_below_sign_bit`]. Constant-size match.
pub(in crate::kernel) fn uint64_upper_bound_below_sign_bit(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&MachineTerm, u32, bool)> {
    let (left, right, strict) = match (condition, value) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            },
            false,
        ) => (a, b, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            },
            false,
        ) => (a, b, true),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: a,
                right: b,
            },
            false,
        ) => (b, a, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: a,
                right: b,
            },
            true,
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: a,
                right: b,
            },
            false,
        ) => (b, a, true),
        _ => return None,
    };
    if left.uint64_as_const().is_some() {
        return None;
    }
    let bound = right.uint64_as_const()?;
    let bound = if strict { bound.checked_sub(1)? } else { bound };
    (bound <= i32::MAX as u64).then_some((left.as_ref(), bound as u32, strict))
}

impl PureFactContext {
    /// Decides `term <=u bound` for `bound < 2^31` as the signed pair
    /// `0 <= term` and `term <= bound`; see
    /// [`unsigned_upper_bound_below_sign_bit`]. True only when both are
    /// decided true, false as soon as either is decided false.
    fn decide_unsigned_small_bound(&self, condition: &ConditionTerm) -> Option<bool> {
        if matches!(condition, ConditionTerm::Compare { format, .. } if *format != MachineIntegerType::UInt32)
        {
            return None;
        }
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let view = comparison_view(condition, true)?;
        if view.format != MachineIntegerType::UInt32 {
            return None;
        }
        let strict = match view.relation {
            Relation::Less => true,
            Relation::LessEqual => false,
            _ => return None,
        };
        let [mut term, bound] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        if term.word32_constant().is_some() {
            return None;
        }
        let bound = bound.word32_constant()?;
        let bound = if strict { bound.checked_sub(1)? } else { bound };
        if bound > i32::MAX as u32 {
            return None;
        }
        if let Some((MachineCastSpelling::Generic, source, destination, bits)) = term.cast()
            && crate::kernel::is_sign_cast32(source, destination)
        {
            term = bits;
        }
        let zero = MachineTerm::constant(0);
        let maximum = MachineTerm::constant(bound);
        let nonnegative = self.decide_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            MachineOperandView::Legacy(&zero),
            term,
        );
        if nonnegative == Some(false) {
            return Some(false);
        }
        let below = self.decide_written_operand_comparison(
            MachineIntegerType::Int32,
            CompareRelation::LessEqual,
            term,
            MachineOperandView::Legacy(&maximum),
        );
        match (nonnegative, below) {
            (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        }
    }
}

/// A wrapped comparison of rebuilt terms can refute offset equality (equal
/// offsets have equal residues) but can affirm it only when both rebuilt
/// terms are exact; otherwise the equality stays undecided.
fn exact_or_unequal(decided: Option<bool>, exact: bool) -> Option<bool> {
    match decided {
        Some(true) if !exact => None,
        other => other,
    }
}

impl PureFactContext {
    /// [`Self::rebuilt_offset_is_exact`] on the four-byte element path. The
    /// path-fact recorder needs this for negative offset premises; memory
    /// resolution uses the width-specific form for positive index equality.
    pub(in crate::kernel) fn element_index_rebuild_is_exact(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
    ) -> bool {
        self.element_index_rebuild_is_exact_for_width(offset, 4)
    }

    /// Whether the offset's index at this element width is exact rather than
    /// merely its 32-bit residue.
    pub(in crate::kernel) fn element_index_rebuild_is_exact_for_width(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
        element_width: u32,
    ) -> bool {
        self.rebuilt_offset_is_exact(offset, element_width, false)
    }

    /// Whether the index or byte term the offset rebuilders produce for
    /// `offset` denotes the exact offset rather than a wrapped 32-bit value.
    /// `PointerOffsetTerm` semantics are exact i64, so equal rebuilt terms
    /// imply equal offsets only when every rebuilt addition (and, on the byte
    /// path, every scaling by a width) is proved not to overflow under the
    /// current facts. Constants and single index terms are always exact.
    fn rebuilt_offset_operation_is_exact(
        &self,
        operation: crate::kernel::machine_integer::Operation,
        operands: [MachineOperandView<'_>; 2],
    ) -> bool {
        crate::kernel::machine_integer::definedness::OverflowQueryView::from_operands(
            MachineIntegerType::Int32,
            operation,
            operands,
        )
        .is_some_and(|query| self.decide_overflow_query(&query) == Some(false))
    }

    fn rebuilt_offset_is_exact(
        &self,
        offset: &crate::kernel::PointerOffsetTerm,
        element_width: u32,
        byte_path: bool,
    ) -> bool {
        use crate::kernel::PointerOffsetTerm;
        let rebuild = |offset: &PointerOffsetTerm| {
            if byte_path {
                crate::kernel::reasoning::shared_byte_offset_from_pointer_offset(offset)
            } else {
                crate::kernel::reasoning::shared_element_index_from_offset(offset, element_width)
            }
        };
        match offset {
            PointerOffsetTerm::Constant(_) => true,
            // Full-width constants or checked unsigned bounds make the
            // element projection exact. The byte projection below still
            // requires a constant whose scaled byte displacement fits.
            PointerOffsetTerm::Int64Scaled { byte_width, .. } => {
                if !byte_path && *byte_width != i64::from(element_width) {
                    return false;
                }
                if byte_path && *byte_width == 0 {
                    return true;
                }
                if !byte_path {
                    return crate::kernel::reasoning::shared_element_index_from_offset_with_facts(
                        offset,
                        element_width,
                        self,
                    )
                    .is_some();
                }
                // An `Int64Scaled` scales its *sixty-four-bit* value, and the
                // byte rebuilder scales it with the thirty-two-bit
                // `Multiply`. So the thirty-two-bit overflow question is the
                // wrong question to ask about this term: it is answered from
                // the low word, and the term's own value is not that word. A
                // value whose low word is `0xFFFFFFFF` passes it — `-1 * 8`
                // does not overflow an `int32` — while the offset it really
                // names, for an unsigned index, is `8 * 4294967295`, and the
                // rebuilt `-8` then reads as the element *below* the base.
                //
                // What settles it is what `bbe71eba` found settles the
                // element side: a fact pinning the value to a number, with
                // the scaled product then required to occupy an `int32`,
                // which is all the rebuilt term can hold. Arithmetic alone
                // cannot, and saying so is the refusal. The fact has to be a
                // sixty-four-bit one: a thirty-two-bit fact names the low
                // word and leaves the rest, which is the shape that made
                // `0xFFFFFFFF` look like a clean `-1`.
                crate::kernel::assumptions::exact_wide_scaled_offset_constant(offset, self)
                    .is_some_and(|bytes| i32::try_from(bytes).is_ok())
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                if !byte_path || *byte_width <= 1 {
                    return true;
                }
                let Ok(width) = u32::try_from(*byte_width) else {
                    return false;
                };
                self.rebuilt_offset_operation_is_exact(
                    crate::kernel::machine_integer::Operation::Multiply,
                    [
                        value.operand_view(),
                        MachineOperandView::Legacy(&MachineTerm::constant(width)),
                    ],
                )
            }
            PointerOffsetTerm::Add(left, right)
                if left.as_ref() == &PointerOffsetTerm::Constant(0) =>
            {
                self.rebuilt_offset_is_exact(right, element_width, byte_path)
            }
            PointerOffsetTerm::Add(left, right)
                if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
            {
                self.rebuilt_offset_is_exact(left, element_width, byte_path)
            }
            PointerOffsetTerm::Add(left, right) => {
                if !(self.rebuilt_offset_is_exact(left, element_width, byte_path)
                    && self.rebuilt_offset_is_exact(right, element_width, byte_path))
                {
                    return false;
                }
                match (rebuild(left), rebuild(right)) {
                    (Some(left), Some(right)) => self.rebuilt_offset_operation_is_exact(
                        crate::kernel::machine_integer::Operation::Add,
                        [left.operand_view(), right.operand_view()],
                    ),
                    _ => false,
                }
            }
            PointerOffsetTerm::Variable(_) => false,
        }
    }
}

#[cfg(test)]
thread_local! {
    static EXACT_ORDER_EVIDENCE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// An order fact at `format`, held with `value`, as the references
/// `(lower, upper, strict)` for `lower < upper` (strict) or `lower <=
/// upper`: `>` and `>=` swap their operands, and a false order is the
/// reversed order with the opposite strictness. Constant-size match.
pub(in crate::kernel) fn held_order_at(
    format: MachineIntegerType,
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&MachineTerm, &MachineTerm, bool)> {
    let ConditionTerm::Compare {
        format: condition_format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if *condition_format != format {
        return None;
    }
    let (lower_first, strict) = match relation {
        CompareRelation::LessThan => (true, true),
        CompareRelation::LessEqual => (true, false),
        CompareRelation::GreaterThan => (false, true),
        CompareRelation::GreaterEqual => (false, false),
        CompareRelation::Equal => return None,
    };
    let (lower, upper) = if lower_first {
        (left.as_ref(), right.as_ref())
    } else {
        (right.as_ref(), left.as_ref())
    };
    Some(if value {
        (lower, upper, strict)
    } else {
        (upper, lower, !strict)
    })
}

/// The formats whose order facts the format-indexed order walk
/// ([`PureFactContext::exact_wide_order_path_evidence`]) follows: the 64-bit
/// orders and the `uint32` order. The `int32` order has its own walk
/// ([`PureFactContext::exact_signed_order_path_evidence`]).
pub(in crate::kernel) const WIDE_ORDER_FORMATS: [MachineIntegerType; 3] = [
    MachineIntegerType::UInt64,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt32,
];

/// An order fact at `format`, retaining its written operand views.
pub(in crate::kernel) fn order_view_at_format(
    condition: &ConditionTerm,
    value: bool,
    format: MachineIntegerType,
) -> Option<crate::kernel::machine_integer::comparison::NativeComparisonView<'_>> {
    let view = super::super::retained_order_bounds::order_view(condition, value)?;
    (view.format == format).then_some(view)
}

impl PureFactContext {
    /// Check the full unsigned value's range through its own bound index.
    /// This proves that taking its low word preserves its nonnegative signed
    /// value; a bound on the low word alone supplies no evidence here.
    pub(in crate::kernel) fn uint64_index_fits_int32(&self, term: &MachineTerm) -> bool {
        self.uint64_index_fits_int32_view(MachineOperandView::Legacy(term))
    }

    pub(in crate::kernel) fn uint64_index_fits_int32_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> bool {
        let limit = MachineTerm::uint64_constant(i32::MAX as u64);
        let guard = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            MachineIntegerType::UInt64,
            CompareRelation::LessEqual,
            [term, MachineOperandView::Legacy(&limit)],
        );
        // A maintained bound keyed by this exact value also handles exact
        // widening. Do not invoke the general decision fallbacks here: this
        // query is part of every checked range projection.
        guard.reflexive_value() == Some(true)
            || self.exact_condition_value(&guard) == Some(true)
            || self
                .difference_graph
                .built()
                .and_then(|graph| graph.decide(&guard))
                == Some(true)
    }

    /// The signed counterpart: the full signed value lies in `0..=INT_MAX`,
    /// by 64-bit signed order facts on the value itself, so its low word is
    /// the value.
    pub(in crate::kernel) fn int64_index_fits_int32_view(
        &self,
        term: MachineOperandView<'_>,
    ) -> bool {
        let zero = MachineTerm::int64_constant(0);
        let limit = MachineTerm::int64_constant(i32::MAX as i64);
        [
            [MachineOperandView::Legacy(&zero), term],
            [term, MachineOperandView::Legacy(&limit)],
        ]
        .into_iter()
        .all(|operands| {
            self.decide(
                &crate::kernel::machine_integer::comparison::condition_for_operand_views(
                    MachineIntegerType::Int64,
                    CompareRelation::LessEqual,
                    operands,
                ),
            ) == Some(true)
        })
    }

    /// An unsigned 64-bit comparison of signed values read as unsigned,
    /// `(uint64)i < (uint64)n`, or of one beside a constant at most
    /// `i64::MAX`: the bound a `long` range bound or index is given
    /// ([`crate::kernel::wide_range_bounds`]). When each signed value is
    /// decided nonnegative the two orders agree, so the signed comparison
    /// answers. Anything else is left to the other rules.
    pub(super) fn decide_unsigned_order_of_nonnegative_signed(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        use crate::kernel::MachineCastSpelling as Cast;
        use crate::kernel::machine_integer::{
            Relation,
            comparison::{ComparisonOperand, comparison_view},
        };
        let view = comparison_view(condition, true)?;
        if view.format != MachineIntegerType::UInt64
            || !matches!(view.relation, Relation::Less | Relation::LessEqual)
        {
            return None;
        }
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let reinterpreted = |term: MachineOperandView<'_>| {
            matches!(term.cast(), Some((Cast::UInt64FromInt64, _, _, _)))
        };
        if !reinterpreted(left) && !reinterpreted(right) {
            return None;
        }
        let as_signed = |term: MachineOperandView<'_>| -> Option<ComparisonOperand<'static>> {
            if let Some((Cast::UInt64FromInt64, _, _, value)) = term.cast() {
                let zero = MachineTerm::int64_constant(0);
                let nonnegative = self.decide_operand_comparison(
                    MachineIntegerType::Int64,
                    Relation::LessEqual,
                    MachineOperandView::Legacy(&zero),
                    value,
                ) == Some(true);
                return nonnegative.then(|| match value {
                    MachineOperandView::Shared(_) => {
                        ComparisonOperand::Observation(value.retain(MachineIntegerType::Int64))
                    }
                    MachineOperandView::Legacy(value) => ComparisonOperand::Constant(value.clone()),
                });
            }
            let constant = i64::try_from(term.uint64_constant()?).ok()?;
            Some(ComparisonOperand::Constant(MachineTerm::int64_constant(
                constant,
            )))
        };
        let left = as_signed(left)?;
        let right = as_signed(right)?;
        self.decide_operand_comparison(
            MachineIntegerType::Int64,
            view.relation,
            left.operand_view(),
            right.operand_view(),
        )
    }

    /// Strengthen a constant bound using only the queried nonconstant endpoint's
    /// index. Never walk a shared constant's incident edges or unrelated facts.
    pub(super) fn decide_uint64_constant_order_bounds(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        self.decide_uint64_constant_order_bounds_inner(condition, false)
    }

    fn decide_uint64_constant_order_bounds_inner(
        &self,
        condition: &ConditionTerm,
        literal_only: bool,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let view = comparison_view(condition, true)?;
        let negated = view.relation == Relation::NotEqual;
        let mut operator = match (view.format, view.relation) {
            (MachineIntegerType::UInt64, Relation::Less) => 0,
            (MachineIntegerType::UInt64, Relation::LessEqual) => 1,
            (
                MachineIntegerType::Int64 | MachineIntegerType::UInt64,
                Relation::Equal | Relation::NotEqual,
            ) => 4,
            _ => return None,
        };
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let (term, limit) = if let Some(limit) = right.uint64_constant() {
            (left, limit)
        } else {
            let limit = left.uint64_constant()?;
            operator = match operator {
                0 => 2,
                1 => 3,
                2 => 0,
                3 => 1,
                _ => 4,
            };
            (right, limit)
        };
        let bounds = self.uint64_order_bounds.get_operand(term)?;
        for (_, other, strict, upper, source) in bounds.sourced_operands() {
            crate::instrumentation::record_deterministic_work(1);
            let bound = if literal_only {
                other.uint64_constant()
            } else {
                self.wide_constant_from_equalities_view(other)
            };
            let Some(bound) = bound else {
                continue;
            };
            let bound = if strict {
                if upper {
                    bound.checked_sub(1)
                } else {
                    bound.checked_add(1)
                }
            } else {
                Some(bound)
            };
            let Some(bound) = bound else {
                continue;
            };
            let answer = match (operator, upper) {
                (0, true) if bound < limit => Some(true),
                (1, true) if bound <= limit => Some(true),
                (2, true) if bound <= limit => Some(false),
                (3, true) if bound < limit => Some(false),
                (0, false) if bound >= limit => Some(false),
                (1, false) if bound > limit => Some(false),
                (2, false) if bound > limit => Some(true),
                (3, false) if bound >= limit => Some(true),
                (4, true) if bound < limit => Some(false),
                (4, false) if bound > limit => Some(false),
                _ => None,
            };
            let Some(answer) = answer else {
                continue;
            };
            record_implicit_reasoning_provenance(self, source);
            return Some(answer != negated);
        }
        None
    }

    /// Follow only upper edges in the operand's indexed uint64 order graph.
    /// Each node is visited once; unrelated facts are never read.
    fn uint64_small_upper_bound_view(&self, term: MachineOperandView<'_>) -> Option<u64> {
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let format = MachineIntegerType::UInt64;
        let mut stack = vec![Key::canonical(format, term)];
        let mut seen = BTreeSet::new();
        let mut best = None;
        while let Some(term) = stack.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if let Some(value) = self.wide_constant_from_equalities_view(term.operand_view()) {
                best = Some(best.map_or(value, |old: u64| old.min(value)));
                continue;
            }
            if let Some(edges) = self.uint64_order_bounds.get_operand(term.operand_view()) {
                for (_, upper, strict, forward) in edges.operand_keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    if !forward {
                        continue;
                    }
                    if let Some(value) = self.wide_constant_from_equalities_view(upper) {
                        if let Some(value) = if strict {
                            value.checked_sub(1)
                        } else {
                            Some(value)
                        } {
                            best = Some(best.map_or(value, |old: u64| old.min(value)));
                        }
                    } else {
                        stack.push(Key::canonical(format, upper));
                    }
                }
            }
        }
        best
    }

    /// Whether held 64-bit order facts chain from `lower` up to `upper`,
    /// and whether some chain does so strictly: `Some(true)` for a strict
    /// chain, `Some(false)` for a chain of `<=` only, `None` for no chain.
    ///
    /// One walk over the queried kind's direction-split edges, from `lower`
    /// along upper edges, or from `upper` along lower edges when `lower` is
    /// a literal. Each term is visited at most twice, once reached strictly
    /// and once not, and only the edges leaving a visited term in the
    /// walk's direction are read. A
    /// literal is an end of a chain and never a step in one: its edges name
    /// every term bounded by it, related to the question or not. Terms join
    /// by their canonical spelling; a visited term and the far end that
    /// both have a constant value join by comparing the values, as the kind
    /// compares them.
    fn wide_order_chain_views(
        &self,
        lower: MachineOperandView<'_>,
        upper: MachineOperandView<'_>,
        unsigned: bool,
    ) -> Option<bool> {
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let format = if unsigned {
            MachineIntegerType::UInt64
        } else {
            MachineIntegerType::Int64
        };
        let literal = |term: &Key| {
            term.operand_view().uint64_constant().is_some()
                || term.operand_view().int64_constant().is_some()
        };
        let lower = Key::canonical(format, lower);
        let upper = Key::canonical(format, upper);
        let upward = !literal(&lower);
        let (start, goal) = if upward {
            (lower, upper)
        } else {
            (upper, lower)
        };
        // Only the edges leaving a term in the walk's direction are read.
        let index = &self.wide_order_edges[usize::from(!unsigned)][usize::from(!upward)];
        let goal_constant = self.wide_constant_from_equalities_view(goal.operand_view());
        // How a visited value and the goal's value order along the walk.
        let toward_goal = |value: u64, goal: u64| {
            let (below, above) = if upward { (value, goal) } else { (goal, value) };
            if unsigned {
                below.cmp(&above)
            } else {
                (below as i64).cmp(&(above as i64))
            }
        };
        let mut stack = vec![(start, false)];
        let mut seen = BTreeSet::new();
        let mut chained = None;
        while let Some((term, strict_so_far)) = stack.pop() {
            if !seen.insert((term.clone(), strict_so_far)) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let joined = if term == goal {
                Some(strict_so_far)
            } else {
                self.wide_constant_from_equalities_view(term.operand_view())
                    .zip(goal_constant)
                    .and_then(|(value, goal)| match toward_goal(value, goal) {
                        std::cmp::Ordering::Less => Some(true),
                        std::cmp::Ordering::Equal => Some(strict_so_far),
                        std::cmp::Ordering::Greater => None,
                    })
            };
            match joined {
                Some(true) => return Some(true),
                Some(false) => chained = Some(false),
                None => {}
            }
            if literal(&term) {
                continue;
            }
            let Some(edges) = index.get_operand(term.operand_view()) else {
                continue;
            };
            for (other, strict) in edges.operand_keys() {
                crate::instrumentation::record_deterministic_work(1);
                let format = if unsigned {
                    MachineIntegerType::UInt64
                } else {
                    MachineIntegerType::Int64
                };
                stack.push((Key::canonical(format, other), strict_so_far || strict));
            }
        }
        chained
    }

    /// Decide a 64-bit order comparison from a chain of held order facts of
    /// its own kind, signed or unsigned: transitivity, a constant bound
    /// reached through a chain, and `a <= b` with `a != b`. The reversed
    /// chain refutes: `b <= a` refutes `a < b`, and `b < a` refutes `a <= b`.
    pub(super) fn decide_wide_order_chain(&self, condition: &ConditionTerm) -> Option<bool> {
        use crate::kernel::MachineOperandView as V;
        use crate::kernel::machine_integer::{
            Relation,
            comparison::{ComparisonOperand, NativeComparisonView},
        };
        let view = super::super::retained_order_bounds::order_view(condition, true)?;
        let format = view.format;
        let unsigned = match format {
            MachineIntegerType::UInt64 => true,
            MachineIntegerType::Int64 => false,
            _ => return None,
        };
        let [lower, upper] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let strict = view.relation == Relation::Less;
        let equal = |a: V<'_>, b: V<'_>| match (a, b) {
            (V::Legacy(a), V::Legacy(b)) => ConditionTerm::int64_equal(a.clone(), b.clone()),
            _ => NativeComparisonView {
                format,
                relation: Relation::Equal,
                operands: [a, b]
                    .map(|operand| ComparisonOperand::Observation(operand.retain(format))),
            }
            .integer_condition(),
        };
        let zero = MachineTerm::uint64_constant(0);
        if unsigned
            && matches!(
                (lower.uint64_constant(), strict),
                (Some(0), true) | (Some(1), false)
            )
            && [
                equal(upper, V::Legacy(&zero)),
                equal(V::Legacy(&zero), upper),
            ]
            .iter()
            .any(|zero| self.exact_condition_value(zero) == Some(false))
        {
            return Some(true);
        }
        match self.wide_order_chain_views(lower, upper, unsigned) {
            Some(true) => return Some(true),
            Some(false) if !strict => return Some(true),
            Some(false) => {
                if self.exact_condition_value(&equal(lower, upper)) == Some(false)
                    || self.exact_condition_value(&equal(upper, lower)) == Some(false)
                {
                    return Some(true);
                }
            }
            None => {}
        }
        match self.wide_order_chain_views(upper, lower, unsigned) {
            Some(true) => Some(false),
            Some(false) if strict => Some(false),
            _ => None,
        }
    }

    /// Within the signed word's nonnegative range, truncation preserves
    /// uint64 order exactly. The range checks are required on both operands.
    pub(super) fn decide_small_uint64_index_order(
        &self,
        condition: &ConditionTerm,
    ) -> Option<bool> {
        let wide_order = super::super::retained_order_bounds::order_view(condition, true)
            .filter(|view| view.format == MachineIntegerType::UInt64);
        if let Some(view) = &wide_order {
            use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
            let [left, right] = view
                .operands
                .each_ref()
                .map(|operand| Key::canonical(MachineIntegerType::UInt64, operand.operand_view()));
            let strict = view.relation == crate::kernel::machine_integer::Relation::Less;
            if let Some(bounds) = self.uint64_order_bounds.get_operand(left.operand_view()) {
                for (_, other, held_strict, forward) in bounds.operand_keys() {
                    crate::instrumentation::record_deterministic_work(1);
                    if Key::canonical(MachineIntegerType::UInt64, other) != right {
                        continue;
                    }
                    if forward && (!strict || held_strict) {
                        return Some(true);
                    }
                    if !forward && (strict || held_strict) {
                        return Some(false);
                    }
                }
            }
        }
        if let Some(guard) = condition
            .uint64_successor_guard()
            .or_else(|| condition.uint64_subtraction_guard())
            .or_else(|| condition.uint64_remainder_bound_guard())
            && self.decide(&guard) == Some(true)
        {
            return Some(true);
        }
        if let Some(guards) = condition
            .uint64_subtraction_upper_bound_guards()
            .or_else(|| condition.uint64_partial_restoration_upper_bound_guards())
            && guards.iter().all(|guard| self.decide(guard) == Some(true))
        {
            return Some(true);
        }
        if let Some(view) = &wide_order
            && view.relation == crate::kernel::machine_integer::Relation::LessEqual
            && !matches!(
                condition,
                ConditionTerm::Compare {
                    relation: CompareRelation::GreaterEqual,
                    ..
                }
            )
        {
            let limit = view.operands[1].operand_view().uint64_constant()?;
            if self.uint64_small_upper_bound_view(view.operands[0].operand_view())? <= limit {
                return Some(true);
            }
            return None;
        }
        if let Some(guards) = condition.nonnegative_division_bound_guards()
            && guards.iter().all(|guard| self.decide(guard) == Some(true))
        {
            return Some(true);
        }
        use crate::kernel::machine_integer::comparison::{
            comparison_view, condition_for_operand_views,
        };
        use crate::kernel::{
            KernelTerm, KernelTermImport, MachineBinaryOp, MachineCastSpelling,
            SharedMachineIntegerTerm,
        };
        let view = comparison_view(condition, true)?;
        if view.format != MachineIntegerType::Int32 {
            return None;
        }
        let strict = match view.relation {
            crate::kernel::machine_integer::Relation::Less => true,
            crate::kernel::machine_integer::Relation::LessEqual => false,
            _ => return None,
        };
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        fn small(operand: MachineOperandView<'_>) -> Option<u64> {
            match operand.literal()? {
                bits32_constant!(value) if constant_u32(value) <= i32::MAX as u32 => {
                    Some(u64::from(constant_u32(value)))
                }
                _ => None,
            }
        }
        fn low_word(operand: MachineOperandView<'_>) -> Option<MachineOperandView<'_>> {
            match operand.cast()? {
                (MachineCastSpelling::UInt32From64, _, _, value) => Some(value),
                _ => None,
            }
        }
        // Truncation commutes with addition modulo 2^32. Retain the wide
        // root and append only the selected literal, preserving the native
        // query constructor's literal and subtraction-cancellation rules.
        fn truncated(
            operand: MachineOperandView<'_>,
            unsigned: bool,
        ) -> Option<SharedMachineIntegerTerm> {
            let format = if unsigned {
                MachineIntegerType::UInt64
            } else {
                MachineIntegerType::Int64
            };
            if let Some(value) = low_word(operand) {
                return Some(value.retain(format));
            }
            let (MachineIntegerType::Int32, MachineBinaryOp::Add, [a, b]) = operand.binary()?
            else {
                return None;
            };
            let (value, constant) = if let Some(value) = low_word(a) {
                (value, small(b)?)
            } else {
                (low_word(b)?, small(a)?)
            };
            let literal = if unsigned {
                MachineTerm::uint64_constant(constant)
            } else {
                MachineTerm::int64_constant(constant as i64)
            };
            let native = |value| {
                if unsigned {
                    MachineTerm::uint64_add(value, literal.clone())
                } else {
                    MachineTerm::int64_add(value, literal.clone())
                }
            };
            if let MachineOperandView::Legacy(value) = value {
                return Some(SharedMachineIntegerTerm::intern(
                    format,
                    native(value.clone()),
                ));
            }
            if let Some(value) = value.literal() {
                return Some(SharedMachineIntegerTerm::intern(format, native(value)));
            }
            if unsigned {
                if constant == 0 {
                    return Some(value.retain(format));
                }
                if let Some((MachineIntegerType::UInt64, MachineBinaryOp::Subtract, [inner, taken])) =
                    value.binary()
                    && matches!(taken.literal(), Some(uint64_constant!(taken)) if constant_u64(taken) == constant)
                {
                    return Some(inner.retain(format));
                }
            }
            let MachineOperandView::Shared(root) = value else {
                unreachable!()
            };
            SharedMachineIntegerTerm::from_shared(
                format,
                KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [
                        root.with_machine_observation_type(format),
                        KernelTermImport::default().machine(format, &literal),
                    ],
                ),
            )
        }
        if truncated(left, true).is_none() && truncated(right, true).is_none() {
            return None;
        }
        let wide = |operand, unsigned| {
            truncated(operand, unsigned).or_else(|| {
                small(operand).map(|value| {
                    let (format, value) = if unsigned {
                        (
                            MachineIntegerType::UInt64,
                            MachineTerm::uint64_constant(value),
                        )
                    } else {
                        (
                            MachineIntegerType::Int64,
                            MachineTerm::int64_constant(value as i64),
                        )
                    };
                    SharedMachineIntegerTerm::intern(format, value)
                })
            })
        };
        let relation = if strict {
            CompareRelation::LessThan
        } else {
            CompareRelation::LessEqual
        };
        let a = wide(left, true)?;
        let b = wide(right, true)?;
        let unsigned_small = |term: &SharedMachineIntegerTerm| {
            self.uint64_small_upper_bound_view(term.operand_view())
                .is_some_and(|bound| bound <= i32::MAX as u64)
        };
        if unsigned_small(&a) && unsigned_small(&b) {
            if a.operand_view().uint64_constant() == Some(0) && !strict {
                return Some(true);
            }
            return self.decide(&condition_for_operand_views(
                MachineIntegerType::UInt64,
                relation,
                [a.operand_view(), b.operand_view()],
            ));
        }
        let a = wide(left, false)?;
        let b = wide(right, false)?;
        let signed_small = |term: &SharedMachineIntegerTerm| {
            self.wide_order_chain_views(
                MachineOperandView::Legacy(&MachineTerm::int64_constant(0)),
                term.operand_view(),
                false,
            )
            .is_some()
                && self
                    .wide_order_chain_views(
                        term.operand_view(),
                        MachineOperandView::Legacy(&MachineTerm::int64_constant(i32::MAX as i64)),
                        false,
                    )
                    .is_some()
        };
        if !signed_small(&a) || !signed_small(&b) {
            return None;
        }
        self.decide(&condition_for_operand_views(
            MachineIntegerType::Int64,
            relation,
            [a.operand_view(), b.operand_view()],
        ))
    }
}

#[cfg(test)]
mod slice_index_tests {
    use super::*;

    #[test]
    fn low_word_index_transport_keeps_the_literal_addend_restriction() {
        use crate::kernel::{KernelTermExport, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        let n = MachineTerm::Variable(Variable(998191));
        let wide = MachineTerm::uint64_add(n.clone(), MachineTerm::uint64_constant(2));
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_less_equal(wide, MachineTerm::uint64_constant(20)),
            true,
        );
        let add = |a, b| MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: crate::kernel::MachineBinaryOp::Add,
            left: Box::new(a),
            right: Box::new(b),
        };
        let low = add(
            MachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(n)),
            add(MachineTerm::constant(1), MachineTerm::constant(1)),
        );
        let native = ConditionTerm::signed_less_than(low.clone(), MachineTerm::constant(22));
        assert_eq!(context.decide_small_uint64_index_order(&native), None);
        let operand = SharedMachineIntegerTerm::from_shared(
            MachineIntegerType::Int32,
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, &low)
                .unwrap(),
        )
        .unwrap();
        let shared = ConditionTerm::integer_less_than(
            IntegerTerm::Machine(operand),
            IntegerTerm::constant(22.into()),
        );
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(context.decide_small_uint64_index_order(&shared), None);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_low_word_index_order_keeps_range_guards_without_export() {
        use crate::kernel::{KernelTermExport, SharedMachineIntegerTerm};
        for format in [MachineIntegerType::UInt64, MachineIntegerType::Int64] {
            for bounded in [false, true] {
                for offset in [0, 1] {
                    for limit in [19, 22] {
                        let _session = crate::kernel::VerificationSession::enter();
                        let constant = |value| {
                            if format == MachineIntegerType::UInt64 {
                                MachineTerm::uint64_constant(value as u64)
                            } else {
                                MachineTerm::int64_constant(value)
                            }
                        };
                        let add = |a, b| {
                            if format == MachineIntegerType::UInt64 {
                                MachineTerm::uint64_add(a, b)
                            } else {
                                MachineTerm::int64_add(a, b)
                            }
                        };
                        let n = add(
                            MachineTerm::Variable(Variable(998181)),
                            MachineTerm::Variable(Variable(998182)),
                        );
                        let wide = if offset == 0 {
                            n.clone()
                        } else {
                            add(n.clone(), constant(offset as i64))
                        };
                        let context = if bounded {
                            PureFactContext::new()
                                .assume_condition(
                                    ConditionTerm::machine_compare(
                                        format,
                                        CompareRelation::LessEqual,
                                        wide.clone(),
                                        constant(20),
                                    ),
                                    true,
                                )
                                .assume_condition(
                                    ConditionTerm::machine_compare(
                                        format,
                                        CompareRelation::LessEqual,
                                        constant(20),
                                        wide,
                                    ),
                                    true,
                                )
                        } else {
                            PureFactContext::new()
                        };
                        let low = MachineTerm::legacy_cast(
                            MachineCastSpelling::UInt32From64,
                            Box::new(n),
                        );
                        let low = if offset == 0 {
                            low
                        } else {
                            MachineTerm::add(low, MachineTerm::constant(offset))
                        };
                        let native = ConditionTerm::signed_less_than(
                            low.clone(),
                            MachineTerm::constant(limit),
                        );
                        let expected = context.decide_small_uint64_index_order(&native);
                        assert_eq!(
                            expected,
                            bounded.then_some(limit == 22),
                            "{format:?}, offset={offset}, limit={limit}"
                        );
                        let operand = SharedMachineIntegerTerm::from_shared(
                            MachineIntegerType::Int32,
                            crate::kernel::KernelTermImport::default()
                                .machine_arithmetic(MachineIntegerType::Int32, &low)
                                .unwrap(),
                        )
                        .unwrap();
                        let shared = ConditionTerm::integer_less_than(
                            IntegerTerm::Machine(operand.clone()),
                            IntegerTerm::constant(limit.into()),
                        );
                        let exports = KernelTermExport::machine_export_count();
                        // Native source admission may already retain this exact written operand.
                        let boxed_before = operand.has_boxed_operand();
                        assert_eq!(context.decide_small_uint64_index_order(&shared), expected);
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(operand.has_boxed_operand(), boxed_before);
                    }
                }
            }
        }
    }

    #[test]
    fn shared_wide_order_consumers_keep_endpoints_and_negative_answers() {
        use crate::kernel::{KernelTerm, KernelType, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            let make = |id| {
                let variable =
                    KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
                SharedMachineIntegerTerm::from_shared(
                    ty,
                    KernelTerm::machine_binary_shared(
                        ty,
                        crate::kernel::MachineBinaryOp::Add,
                        [variable.clone(), variable],
                    ),
                )
                .unwrap()
            };
            let a = make(994671);
            let b = make(994672);
            let c = make(994673);
            let observe = |term: &SharedMachineIntegerTerm| IntegerTerm::Machine(term.clone());
            let facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::integer_less_than(observe(&a), observe(&b)),
                    true,
                )
                .assume_condition(
                    ConditionTerm::integer_less_equal(observe(&b), observe(&c)),
                    true,
                );
            assert_eq!(
                facts.decide_wide_order_chain(&ConditionTerm::integer_less_than(
                    observe(&a),
                    observe(&c)
                )),
                Some(true)
            );
            assert_eq!(
                facts.decide_wide_order_chain(&ConditionTerm::integer_less_equal(
                    observe(&c),
                    observe(&a)
                )),
                Some(false)
            );
            assert_eq!(
                facts.decide_wide_order_chain(&ConditionTerm::integer_less_than(
                    observe(&b),
                    observe(&c)
                )),
                None
            );
            assert!(!a.has_boxed_operand());
            assert!(!b.has_boxed_operand());
            assert!(!c.has_boxed_operand());
            let ranged = facts.assume_condition(
                ConditionTerm::integer_less_equal(observe(&c), IntegerTerm::constant(10.into())),
                true,
            );
            if ty == MachineIntegerType::UInt64 {
                assert_eq!(
                    ranged.uint64_small_upper_bound_view(a.operand_view()),
                    Some(10)
                );
                assert_eq!(
                    ranged.decide_uint64_constant_order_bounds(&ConditionTerm::integer_less_than(
                        observe(&c),
                        IntegerTerm::constant(11.into())
                    )),
                    Some(true)
                );
                assert_eq!(
                    ranged.decide_uint64_constant_order_bounds(
                        &ConditionTerm::integer_greater_than(
                            observe(&c),
                            IntegerTerm::constant(11.into())
                        )
                    ),
                    Some(false)
                );
            } else {
                assert_eq!(
                    ranged.int64_interval_view(c.operand_view()),
                    Some((i64::MIN, 10))
                );
            }
            assert!(!a.has_boxed_operand());
            assert!(!c.has_boxed_operand());
        }
    }

    #[test]
    fn wide_order_chains_decide_by_kind_and_refute_by_the_reversed_chain() {
        let v = |n: u64| MachineTerm::Variable(Variable(997000 + n));
        let (a, b, c, d) = (v(0), v(1), v(2), v(3));
        type Order = fn(MachineTerm, MachineTerm) -> ConditionTerm;
        let kinds: [(Order, Order); 2] = [
            (
                ConditionTerm::uint64_less_than,
                ConditionTerm::uint64_less_equal,
            ),
            (
                ConditionTerm::int64_signed_less_than,
                ConditionTerm::int64_signed_less_equal,
            ),
        ];
        for (index, (lt, le)) in kinds.iter().enumerate() {
            let facts = PureFactContext::new()
                .assume_condition(lt(a.clone(), b.clone()), true)
                .assume_condition(le(b.clone(), c.clone()), true)
                .assume_condition(le(c.clone(), d.clone()), true);
            assert_eq!(facts.decide(&lt(a.clone(), d.clone())), Some(true));
            assert_eq!(facts.decide(&le(a.clone(), d.clone())), Some(true));
            assert_eq!(facts.decide(&le(b.clone(), d.clone())), Some(true));
            // `b <= c <= d` has no strict step.
            assert_eq!(facts.decide(&lt(b.clone(), d.clone())), None);
            // The reversed chain refutes.
            assert_eq!(facts.decide(&lt(d.clone(), a.clone())), Some(false));
            assert_eq!(facts.decide(&le(d.clone(), a.clone())), Some(false));
            assert_eq!(facts.decide(&lt(d.clone(), b.clone())), Some(false));
            assert_eq!(facts.decide(&le(d.clone(), b.clone())), None);
            // A chain of one kind says nothing about the other.
            let (other_lt, other_le) = kinds[1 - index];
            assert_eq!(facts.decide(&other_lt(a.clone(), d.clone())), None);
            assert_eq!(facts.decide(&other_le(a.clone(), d.clone())), None);
            // `<=` with a held disequality is strict.
            let distinct = PureFactContext::new()
                .assume_condition(le(a.clone(), b.clone()), true)
                .assume_condition(ConditionTerm::int64_equal(a.clone(), b.clone()), false);
            assert_eq!(distinct.decide(&lt(a.clone(), b.clone())), Some(true));
            let unrelated = PureFactContext::new()
                .assume_condition(lt(a.clone(), b.clone()), true)
                .assume_condition(lt(c.clone(), d.clone()), true);
            assert_eq!(unrelated.decide(&lt(a.clone(), d.clone())), None);
        }
    }

    #[test]
    fn wide_order_chains_reach_constants_as_their_kind_compares_them() {
        let a = MachineTerm::Variable(Variable(997100));
        let b = MachineTerm::Variable(Variable(997101));
        let u = MachineTerm::uint64_constant;
        let unsigned = PureFactContext::new()
            .assume_condition(ConditionTerm::uint64_less_than(a.clone(), b.clone()), true)
            .assume_condition(ConditionTerm::uint64_less_equal(b.clone(), u(10)), true)
            .assume_condition(ConditionTerm::uint64_less_equal(u(5), a.clone()), true);
        let lt = ConditionTerm::uint64_less_than;
        let le = ConditionTerm::uint64_less_equal;
        assert_eq!(unsigned.decide(&lt(a.clone(), u(10))), Some(true));
        // `a < b <= 10` entails `a <= 9`, which the difference graph reads.
        assert_eq!(unsigned.decide(&le(a.clone(), u(9))), Some(true));
        assert_eq!(unsigned.decide(&lt(a.clone(), u(u64::MAX))), Some(true));
        assert_eq!(unsigned.decide(&lt(u(5), b.clone())), Some(true));
        assert_eq!(unsigned.decide(&lt(u(4), a.clone())), Some(true));
        assert_eq!(unsigned.decide(&lt(u(5), a.clone())), None);
        assert_eq!(unsigned.decide(&lt(b.clone(), u(5))), Some(false));
        // An unsigned bound above the signed range is not a signed bound:
        // `a <=u 2^63` allows `a` to be negative as an int64.
        let high = 1u64 << 63;
        let wide = PureFactContext::new()
            .assume_condition(le(a.clone(), b.clone()), true)
            .assume_condition(le(b.clone(), u(high)), true);
        assert_eq!(wide.decide(&le(a.clone(), u(high))), Some(true));
        assert_eq!(
            wide.decide(&ConditionTerm::int64_signed_less_equal(a.clone(), u(high))),
            None
        );
        assert_eq!(
            wide.decide(&ConditionTerm::int64_signed_less_equal(u(0), a.clone())),
            None
        );
        // A signed chain compares its constants as signed values.
        let minus_one = u(u64::MAX);
        let signed = PureFactContext::new()
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(a.clone(), b.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::int64_signed_less_equal(b.clone(), minus_one.clone()),
                true,
            );
        assert_eq!(
            signed.decide(&ConditionTerm::int64_signed_less_than(a.clone(), u(0))),
            Some(true)
        );
        assert_eq!(signed.decide(&lt(a.clone(), u(0))), Some(false));
    }

    #[test]
    fn uint64_constant_lower_bound_survives_checked_narrowing() {
        let value = MachineTerm::Variable(Variable(991003));
        let context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::uint64_less_than(MachineTerm::uint64_constant(0), value.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(
                    value.clone(),
                    MachineTerm::uint64_constant(i32::MAX as u64),
                ),
                true,
            );
        let goal = ConditionTerm::signed_less_than(
            MachineTerm::constant(0),
            MachineTerm::uint32_from_64(value),
        );
        assert_eq!(
            context.selected_for_test().decide_selected_condition(&goal),
            Some(true)
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/order_paths/slice_index_tests.rs"
        );
    }
}

#[cfg(test)]
mod annotated_alignment_premise_tests {
    use super::*;

    #[test]
    fn alignment_certificates_cite_the_exact_annotated_premise() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(996_210));
        // Address annotations share identity. Keep the written stronger
        // premise for exact citation, independently of a weaker alignment
        // premise.
        let source = ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::uint64_bitwise_and(
                MachineTerm::object_pointer_address(
                    pointer.clone(),
                    Some(CAccessClass::Scalar(CScalarClass::Int)),
                ),
                MachineTerm::uint64_constant(7),
            )),
            right: Box::new(MachineTerm::uint64_constant(0)),
        };
        assert_eq!(source, ConditionTerm::pointer_aligned(pointer.clone(), 8));
        let bare = ConditionTerm::pointer_aligned(pointer.clone(), 4);
        let context = PureFactContext::new().assume_condition(source.clone(), true);
        assert_eq!(
            context.pointer_alignment_certificate_decision(&pointer, 4),
            Some((true, Some(Proposition::ConditionIs(source.clone(), true))))
        );
        let weaker = PureFactContext::new().assume_condition(bare.clone(), true);
        assert_eq!(
            weaker.pointer_alignment_certificate_decision(&pointer, 4),
            Some((true, Some(Proposition::ConditionIs(bare, true))))
        );
    }
}

#[cfg(test)]
mod exact_order_path_tests {
    use super::*;

    fn var(index: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(986_500 + index))
    }

    /// The walk as it was before the endpoint index: every node scans every
    /// order fact. The indexed walk must answer exactly as this does.
    fn scanned_order_path(
        context: &PureFactContext,
        left: &MachineTerm,
        right: &MachineTerm,
        require_strict: bool,
    ) -> bool {
        let order_facts: Vec<_> = context
            .selected_for_test()
            .condition_order_facts()
            .iter()
            .map(|(a, b, strict)| {
                (
                    a.operand_view()
                        .retain(MachineIntegerType::Int32)
                        .value()
                        .clone(),
                    b.operand_view()
                        .retain(MachineIntegerType::Int32)
                        .value()
                        .clone(),
                    *strict,
                )
            })
            .collect();
        let mut stack = vec![(left.clone(), false)];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (&current == right || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
            {
                return true;
            }
            for (edge_left, edge_right, edge_strict) in order_facts.iter() {
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(edge_left))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if &current == edge_left || constant_connection.is_some() {
                    stack.push((
                        edge_right.clone(),
                        strict_so_far || *edge_strict || constant_connection == Some(true),
                    ));
                }
            }
        }
        false
    }

    struct Terms(u64);
    impl Terms {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            self.0 >> 33
        }
        fn term(&mut self) -> MachineTerm {
            match self.next() % 5 {
                0 => MachineTerm::constant((self.next() % 5) as u32),
                1 => MachineTerm::add(var(self.next() % 6), MachineTerm::constant(1)),
                // A sum whose canonical form differs from its spelling, so
                // its facts are also filed under an alias key.
                2 => MachineTerm::add(MachineTerm::constant(1), var(self.next() % 6)),
                _ => var(self.next() % 6),
            }
        }
    }

    #[test]
    fn indexed_walk_agrees_with_scanning_every_order_fact() {
        let _session = crate::kernel::VerificationSession::enter();
        for seed in 0..30u64 {
            let mut terms = Terms(seed + 1);
            let mut context = PureFactContext::new();
            for _ in 0..14 {
                let (left, right) = (Box::new(terms.term()), Box::new(terms.term()));
                let condition = match terms.next() % 4 {
                    0 => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left,
                        right,
                    },
                    1 => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left,
                        right,
                    },
                    2 => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left,
                        right,
                    },
                    _ => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left,
                        right,
                    },
                };
                context = context.assume_condition(condition, !terms.next().is_multiple_of(3));
            }
            for _ in 0..40 {
                let (left, right) = (terms.term(), terms.term());
                let strict = terms.next().is_multiple_of(2);
                assert_eq!(
                    context.has_exact_order_path(&left, &right, strict),
                    scanned_order_path(&context, &left, &right, strict),
                    "seed {seed}: {left:?} to {right:?}, strict {strict}"
                );
            }
        }
    }

    /// The evidence walk as it was before `OrderFactsByLower`: every node
    /// visits every order fact, in reverse fact order.
    fn scanned_order_path_evidence(
        context: &PureFactContext,
        left: &MachineTerm,
        right: &MachineTerm,
        require_strict: bool,
    ) -> Option<Vec<SignedOrderDerivationStep>> {
        let order_facts = context
            .condition_facts
            .iter()
            .filter_map(|(condition, value)| {
                condition_as_order_fact(condition, *value).map(|(lower, upper, strict)| {
                    SignedOrderDerivationStep::from_views(
                        MachineOperandView::Legacy(&lower),
                        MachineOperandView::Legacy(&upper),
                        strict,
                        Proposition::ConditionIs(condition.clone(), *value),
                    )
                })
            })
            .collect::<Vec<_>>();
        let mut stack = vec![(left.clone(), false, Vec::new())];
        let mut seen = BTreeSet::new();
        while let Some((current, strict_so_far, path)) = stack.pop() {
            if !seen.insert((current.clone(), strict_so_far)) {
                continue;
            }
            let constant_connection = signed_bitvector_constant(&current)
                .zip(signed_bitvector_constant(right))
                .and_then(|(current, right)| (current <= right).then_some(current < right));
            if (&current == right || constant_connection.is_some())
                && (!require_strict || strict_so_far || constant_connection == Some(true))
                && !path.is_empty()
            {
                return Some(path);
            }
            for edge in order_facts.iter().rev() {
                let constant_connection = signed_bitvector_constant(&current)
                    .zip(signed_bitvector_constant(edge.lower()))
                    .and_then(|(current, edge_left)| {
                        (current <= edge_left).then_some(current < edge_left)
                    });
                if &current != edge.lower() && constant_connection.is_none() {
                    continue;
                }
                let mut extended = path.clone();
                extended.push(edge.clone());
                stack.push((
                    edge.upper().clone(),
                    strict_so_far || edge.strict || constant_connection == Some(true),
                    extended,
                ));
            }
        }
        None
    }

    /// The indexed evidence walk returns the very path the full scan did,
    /// not only an answer of the same truth.
    #[test]
    fn indexed_evidence_walk_finds_the_scanned_path() {
        let _session = crate::kernel::VerificationSession::enter();
        for seed in 0..30u64 {
            let mut terms = Terms(seed + 101);
            let mut context = PureFactContext::new();
            for _ in 0..14 {
                let (left, right) = (Box::new(terms.term()), Box::new(terms.term()));
                let condition = match terms.next() % 4 {
                    0 => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::LessThan,
                        left,
                        right,
                    },
                    1 => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::LessEqual,
                        left,
                        right,
                    },
                    2 => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::GreaterThan,
                        left,
                        right,
                    },
                    _ => ConditionTerm::Compare {
                        format: crate::kernel::MachineIntegerType::Int32,
                        relation: crate::kernel::CompareRelation::GreaterEqual,
                        left,
                        right,
                    },
                };
                context = context.assume_condition(condition, !terms.next().is_multiple_of(3));
            }
            for _ in 0..40 {
                let (left, right) = (terms.term(), terms.term());
                let strict = terms.next().is_multiple_of(2);
                let indexed = context
                    .exact_signed_order_path_evidence(&left, &right, strict)
                    .map(|path| {
                        path.into_iter()
                            .map(|step| step.premise)
                            .collect::<Vec<_>>()
                    });
                let scanned =
                    scanned_order_path_evidence(&context, &left, &right, strict).map(|path| {
                        path.into_iter()
                            .map(|step| step.premise)
                            .collect::<Vec<_>>()
                    });
                assert_eq!(
                    indexed, scanned,
                    "seed {seed}: {left:?} to {right:?}, strict {strict}"
                );
            }
        }
    }

    /// A walk from a constant reads the order facts from a constant at
    /// least as large, not every order fact. Both walks once collected every
    /// order fact, so their work grew with unrelated bounds.
    #[test]
    fn constant_order_walks_ignore_unrelated_order_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut samples = Vec::new();
        for size in [16u64, 64, 256] {
            let mut context = PureFactContext::new()
                .assume_condition(ConditionTerm::signed_less_than(5u32.into(), var(0)), true);
            for index in 0..size {
                context = context.assume_condition(
                    ConditionTerm::signed_less_than(var(10 + 2 * index), var(11 + 2 * index)),
                    true,
                );
            }
            let (found, walk) = crate::instrumentation::measure_deterministic_work(|| {
                context.has_exact_order_path(&3u32.into(), &var(0), true)
            });
            assert!(found);
            let (evidence, evidence_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    context.exact_signed_order_path_evidence(&3u32.into(), &var(0), true)
                });
            assert!(evidence.is_some());
            samples.push((walk, evidence_work));
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "unrelated order facts changed a constant walk's work: {samples:?}"
        );
    }

    /// An order chain of fixed length beside many unrelated order facts:
    /// the walk follows the chain's edges only.
    #[test]
    fn exact_order_path_ignores_unrelated_order_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let work_beside = |unrelated: u64| {
            let mut context = PureFactContext::new();
            for index in 0..8 {
                context = context.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(var(index)),
                        right: Box::new(var(index + 1)),
                    },
                    true,
                );
            }
            for index in 0..unrelated {
                context = context.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(var(1_000 + 2 * index)),
                        right: Box::new(var(1_001 + 2 * index)),
                    },
                    true,
                );
            }
            let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.has_exact_order_path(&var(0), &var(8), true)
            });
            assert!(found);
            work
        };
        let small = work_beside(16);
        let large = work_beside(1_024);
        // The walk charges the nodes and edges it visits.
        assert!(small > 0);
        assert_eq!(
            large, small,
            "the walk cost {large} beside 1,024 facts and {small} beside 16"
        );
    }
}

#[cfg(test)]
mod memory_order_view_tests {
    use super::*;
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelTermExport, KernelTermImport, KernelType, MachineBinaryOp,
        SharedMachineIntegerTerm,
    };

    fn observed_condition(condition: &ConditionTerm) -> ConditionTerm {
        let ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } = condition
        else {
            unreachable!()
        };
        let observe = |value: &MachineTerm| {
            IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(
                    *format,
                    KernelTermImport::default()
                        .machine_arithmetic(*format, value)
                        .unwrap(),
                )
                .unwrap(),
            )
        };
        let (left, right) = (observe(left), observe(right));
        match relation {
            CompareRelation::LessThan => ConditionTerm::integer_less_than(left, right),
            CompareRelation::LessEqual => ConditionTerm::integer_less_equal(left, right),
            CompareRelation::GreaterThan => ConditionTerm::integer_greater_than(left, right),
            CompareRelation::GreaterEqual => ConditionTerm::integer_greater_equal(left, right),
            CompareRelation::Equal => ConditionTerm::integer_equal(left, right),
        }
    }

    #[test]
    fn memory_order_views_keep_extremes_successors_and_unsigned_domains() {
        let x = MachineTerm::Variable(Variable(993201));
        let y = MachineTerm::Variable(Variable(993202));
        let sum = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(x.clone()),
            right: Box::new(1u32.into()),
        };
        let square = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Multiply,
            left: Box::new(x.clone()),
            right: Box::new(x.clone()),
        };
        let le = ConditionTerm::signed_less_equal;
        let lt = ConditionTerm::signed_less_than;
        let zero = MachineTerm::constant(0);
        let maximum = MachineTerm::constant(i32::MAX as u32);
        let lower = le(zero.clone(), x.clone());
        let upper = lt(x.clone(), maximum.clone());
        let below_y = lt(x.clone(), y.clone());
        let wide = MachineTerm::Variable(Variable(993203));
        let narrowed = MachineTerm::uint32_from_64(wide.clone());
        let cases = [
            (
                vec![ConditionTerm::equal(x.clone(), 2u32.into())],
                le(square.clone(), 4u32.into()),
                true,
                true,
            ),
            (
                vec![ConditionTerm::equal(x.clone(), 2u32.into())],
                le(square.clone(), 3u32.into()),
                true,
                false,
            ),
            (
                vec![ConditionTerm::uint64_equal(
                    wide,
                    MachineTerm::uint64_constant(0x1_0000_0007),
                )],
                le(narrowed, 7u32.into()),
                true,
                true,
            ),
            (vec![], le(sum.clone(), y.clone()), true, false),
            (
                vec![below_y.clone()],
                le(sum.clone(), y.clone()),
                true,
                true,
            ),
            (
                vec![below_y.clone()],
                lt(sum.clone(), y.clone()),
                true,
                false,
            ),
            (
                vec![below_y],
                ConditionTerm::signed_greater_than(sum.clone(), y),
                false,
                true,
            ),
            (
                vec![lower.clone(), upper.clone()],
                lt(zero.clone(), sum.clone()),
                true,
                true,
            ),
            (
                vec![lower.clone()],
                lt(zero.clone(), sum.clone()),
                true,
                false,
            ),
            (
                vec![lower.clone(), upper],
                le(1u32.into(), sum.clone()),
                true,
                true,
            ),
            (
                vec![],
                le(MachineTerm::constant(i32::MIN as u32), square.clone()),
                true,
                true,
            ),
            (vec![], le(square, maximum), true, true),
            (
                vec![lower, le(x.clone(), 15u32.into())],
                ConditionTerm::unsigned_less_equal(sum.clone(), 17u32.into()),
                true,
                true,
            ),
            (
                vec![le(x, 15u32.into())],
                ConditionTerm::unsigned_less_equal(sum.clone(), 17u32.into()),
                true,
                false,
            ),
            (
                vec![],
                ConditionTerm::unsigned_less_than(sum, zero),
                true,
                false,
            ),
        ];
        for (premises, native, truth, expected) in cases {
            let _session = crate::kernel::VerificationSession::enter();
            let facts = premises
                .into_iter()
                .fold(PureFactContext::new(), |facts, premise| {
                    facts.assume_condition(premise, true)
                });
            let shared = observed_condition(&native);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                facts.proves_order_condition_for_memory_resolution(&shared, truth),
                expected,
                "shared {native:?}, polarity {truth}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                facts.proves_order_condition_for_memory_resolution(&native, truth),
                expected,
                "native {native:?}, polarity {truth}"
            );
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        use super::*;
        include!(
            "../../../scaling_tests/kernel/assumptions/condition_reasoning/memory_order_views.rs"
        );
    }
}

#[cfg(test)]
mod shared_read_equality_rule_tests {
    use super::*;

    #[test]
    fn shared_word_equality_retains_selected_memory_frame_authority() {
        use crate::kernel::MachineOperandView as V;
        let _session = crate::kernel::VerificationSession::enter();
        // A real recorded store whose disjointness needs the selected index
        // fact (the reversed-history regression uses this same edge shape).
        let read_index = MachineTerm::Variable(Variable(995_781));
        let write_index = MachineTerm::Variable(Variable(995_782));
        let base = Pointer {
            block: "selected-word".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pointer = base.offset_by_elements(read_index.clone(), 4);
        let written = base.offset_by_elements(write_index.clone(), 4);
        crate::kernel::eval::declare_load_access_width(&pointer, 4);
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_than(read_index, write_index),
            true,
        );
        let before = Memory::new().with_block("selected-word", 64);
        let after = before.clone().store_with_context(
            written,
            ProgramValue::Int32(MachineTerm::constant(9)),
            &context,
        );
        let read = |memory: Memory, at: &Pointer| {
            let memory = crate::kernel::intern_memory(memory);
            MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                at,
                LoadKind::Int32,
                4,
            ))
        };
        let left = read(before.clone(), &pointer);
        let right = read(after.clone(), &pointer);
        let unrelated = Pointer {
            block: "different-word".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let wrong_address = read(after.clone(), &unrelated);
        let wrong_state = read(
            after.clone().store(
                pointer.clone(),
                ProgramValue::Int32(MachineTerm::constant(31)),
            ),
            &pointer,
        );
        assert!(
            !context.int32_values_known_equal(&left, &right),
            "graph alone has no frame authority"
        );
        assert!(context.memory_loads_proven_equal(&left, &right));
        let shared = |term: &MachineTerm| {
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, term)
                .unwrap()
        };
        let left_shared = shared(&left);
        for (candidate, expected) in [
            (&right, Some(true)),
            (&wrong_address, None),
            (&wrong_state, None),
        ] {
            let candidate_shared = shared(candidate);
            for operands in [
                [V::Legacy(&left), V::Legacy(candidate)],
                [V::Shared(&left_shared), V::Shared(&candidate_shared)],
                [V::Legacy(&left), V::Shared(&candidate_shared)],
                [V::Shared(&left_shared), V::Legacy(candidate)],
            ] {
                assert_eq!(
                    context.decide_word_equality_views(
                        MachineIntegerType::Int32,
                        operands[0],
                        operands[1]
                    ),
                    expected
                );
                assert_eq!(
                    context.bitvector_terms_equal_for_transport_views(operands[0], operands[1]),
                    expected == Some(true)
                );
            }
            let extra = MachineTerm::Variable(Variable(995_783));
            let left_sum = MachineTerm::add(left.clone(), extra.clone());
            let right_sum = MachineTerm::add(candidate.clone(), extra);
            let left_shared = shared(&left_sum);
            let right_shared = shared(&right_sum);
            for operands in [
                [V::Legacy(&left_sum), V::Legacy(&right_sum)],
                [V::Shared(&left_shared), V::Shared(&right_shared)],
                [V::Legacy(&left_sum), V::Shared(&right_shared)],
                [V::Shared(&left_shared), V::Legacy(&right_sum)],
            ] {
                assert_eq!(
                    context.decide_word_equality_views(
                        MachineIntegerType::Int32,
                        operands[0],
                        operands[1]
                    ),
                    expected,
                    "sum decision must preserve the selected read's memory authority",
                );
                assert_eq!(
                    context.bitvector_terms_equal_for_transport_views(operands[0], operands[1]),
                    expected == Some(true)
                );
            }
        }
        assert!(!PureFactContext::new().memory_loads_proven_equal(&left, &right));
    }
}

#[cfg(test)]
mod shared_read_order_bridge_tests {
    use super::*;

    #[test]
    fn shared_order_read_index_and_paths_retain_selected_dag_bridge() {
        use crate::kernel::MachineOperandView as V;
        let _session = crate::kernel::VerificationSession::enter();
        let read_index = MachineTerm::Variable(Variable(995_801));
        let write_index = MachineTerm::Variable(Variable(995_802));
        let base = Pointer {
            block: "order-read-bridge".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let pointer = base.offset_by_elements(read_index.clone(), 4);
        let write = base.offset_by_elements(write_index.clone(), 4);
        crate::kernel::eval::declare_load_access_width(&pointer, 4);
        let separation = ConditionTerm::signed_less_than(read_index, write_index);
        let separated = PureFactContext::new().assume_condition(separation, true);
        let before = Memory::new().with_block("order-read-bridge", 64);
        let after = before.clone().store_with_context(
            write,
            ProgramValue::Int32(MachineTerm::constant(9)),
            &separated,
        );
        let read = |memory| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory),
                Box::new(pointer.clone()),
                LoadKind::Int32,
            )
        };
        let before = read(before);
        let after = read(after);
        let import = |term: &MachineTerm| {
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, term)
                .unwrap()
        };
        let before_shared = import(&before);
        let after_shared = import(&after);
        let upper = MachineTerm::constant(20);
        let upper_shared = import(&upper);
        let premise = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            MachineIntegerType::Int32,
            CompareRelation::LessThan,
            [V::Shared(&before_shared), V::Legacy(&upper)],
        );
        let context = separated.clone().assume_condition(premise.clone(), true);
        assert!(
            context
                .order_facts_by_lower
                .loads_of(&pointer, LoadKind::Int32)
                .any(|source| source == &premise)
        );
        assert!(
            !separated
                .order_facts_by_lower
                .loads_of(&pointer, LoadKind::Int32)
                .any(|source| source == &premise)
        );
        for left in [V::Legacy(&after), V::Shared(&after_shared)] {
            for right in [V::Legacy(&upper), V::Shared(&upper_shared)] {
                assert!(!context.has_exact_order_path_views(left, right, true));
                crate::kernel::api::with_extended_dag_bridging(|| {
                    assert!(
                        crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                            &before, &after, &context
                        )
                    );
                    assert!(context.has_exact_order_path_views(left, right, true));
                    let path = context
                        .exact_signed_order_source_path(left, right, true)
                        .expect("selected frame bridge");
                    assert!(path.iter().any(
                        |step| step.premise == Proposition::ConditionIs(premise.clone(), true)
                    ));
                    assert!(!separated.has_exact_order_path_views(left, right, true));
                    let no_frame = PureFactContext::new().assume_condition(premise.clone(), true);
                    assert!(!no_frame.has_exact_order_path_views(left, right, true));
                });
            }
        }
    }
}

#[cfg(test)]
mod shared_byte_rebuild_tests {
    use super::*;
    use crate::kernel::{KernelTermExport, SharedMachineIntegerTerm};

    #[test]
    fn byte_rebuild_uses_shared_overflow_query_without_losing_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1018220));
        let index = SharedMachineIntegerTerm::index(
            MachineIntegerType::Int32,
            MachineTerm::add(x, MachineTerm::constant(1)),
        );
        let limit = MachineTerm::constant(i32::MAX as u32 / 8);
        let zero = MachineTerm::constant(0);
        let bound = |left, right| {
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::Int32,
                CompareRelation::LessEqual,
                [left, right],
            )
        };
        let upper = bound(index.operand_view(), MachineOperandView::Legacy(&limit));
        let lower = bound(MachineOperandView::Legacy(&zero), index.operand_view());
        let empty = PureFactContext::new();
        let lower_only = empty.clone().assume_condition(lower, true);
        let bounded = lower_only.clone().assume_condition(upper, true);
        let offset = PointerOffsetTerm::Int32Scaled {
            value: index,
            byte_width: 8,
        };
        let exports = KernelTermExport::machine_export_count();
        assert!(bounded.rebuilt_offset_is_exact(&offset, 4, true));
        assert!(!empty.rebuilt_offset_is_exact(&offset, 4, true));
        assert!(!lower_only.rebuilt_offset_is_exact(&offset, 4, true));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
